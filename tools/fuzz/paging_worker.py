#!/usr/bin/env python3
"""认证后的单个 samples v1 输入 → 既有重放链 → 三方结果。

只读导入 DIFFTEST_XIANGSHAN_DIR；本入口不实现分页解码或窄规则。
外层 Executor 负责批量、超时与取消，本入口负责清理 run_probe 的独立进程组。
"""
import argparse
import contextlib
import ctypes
import json
import os
from pathlib import Path
import signal
import subprocess
import sys

DEFAULT_DIFFTEST = '/data1/baiyifan/workplace/isla-runner/.worktree/replay-p0/difftest-xiangshan'
DEFAULT_DECODER = '/data1/baiyifan/workplace/isla-runner/.worktree/isla-enumerate/agents/path_merge_call_support/pt_decode'


def finish_result(case, result, trace, log, fuzz):
    """保留原始桶；三方判断与窄规则使用既有实现。"""
    merged = dict(result, sample_id=case['sample']['sample_id'], isla_cause=case['expected']['cause'],
                  xs_cause=None, nemu_cause=None, isla_consistent_side='unobserved',
                  mismatch=dict(filtered=False, known_rule=None, group_key=None))
    merged['prestate_context'] = case['prestate_context']
    if result['bucket'] in {'timeout', 'limit', 'framework-abort', 'other-failure'}:
        return merged
    observation = fuzz.observe_run(case, result, trace, log)
    merged.update(observation=observation, **observation)
    merged['agree'] = result['agree'] and observation['isla_consistent_side'] == 'both'
    if not merged['agree']:
        table = fuzz.MismatchTable(fuzz.KNOWN_MISMATCH_RULES)
        merged['mismatch'] = table.record(case, observation, result.get('id', str(merged['sample_id'])))
    return merged


@contextlib.contextmanager
def managed_children():
    """跟踪既有接口创建的子进程；取消时结束 emu 会话并回收 NEMU。"""
    children = []
    original = subprocess.Popen
    libc = ctypes.CDLL(None, use_errno=True)
    assert libc.prctl(36, 1, 0, 0, 0) == 0  # PR_SET_CHILD_SUBREAPER

    class ManagedPopen(original):
        def __init__(self, *args, **kwargs):
            # 子进程创建与登记必须是一个不可被取消打断的步骤。
            mask = signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGTERM, signal.SIGINT})
            original_setup = kwargs.get('preexec_fn')
            def child_setup():
                signal.pthread_sigmask(signal.SIG_SETMASK, mask)
                if original_setup is not None:
                    original_setup()
            kwargs['preexec_fn'] = child_setup
            try:
                super().__init__(*args, **kwargs)
                children.append((self, kwargs.get('start_new_session', False)))
            finally:
                signal.pthread_sigmask(signal.SIG_SETMASK, mask)

    def cancelled(signum, frame):
        raise InterruptedError(f'收到取消信号 {signum}')

    previous = {sig: signal.signal(sig, cancelled) for sig in (signal.SIGTERM, signal.SIGINT)}
    subprocess.Popen = ManagedPopen
    try:
        yield
    finally:
        subprocess.Popen = original
        for sig in previous:
            signal.signal(sig, signal.SIG_IGN)
        for child, session in children:
            try:
                if session:
                    os.killpg(child.pid, signal.SIGKILL)
                elif child.poll() is None:
                    child.kill()
            except ProcessLookupError:
                pass  # 子进程已被既有 run_probe 回收。
        for child, session in children:
            child.wait()
        while True:
            try:
                os.waitpid(-1, 0)
            except ChildProcessError:
                break
        for sig, handler in previous.items():
            signal.signal(sig, handler)


def run(args):
    sys.path.insert(0, os.environ.get('DIFFTEST_XIANGSHAN_DIR', DEFAULT_DIFFTEST))
    import paging_replay as replay
    import paging_fuzz as fuzz
    profile = json.loads(args.profile.read_text())
    lock = json.loads(args.lock.read_text())
    # 只核对平台描述和锁的语义关联；不把 isarch 二进制身份作为认证门槛。
    replay.verify_platform_lock(profile, lock, {})
    files = json.loads(args.files.read_text())
    decoder, provenance = replay.load_decoder(os.environ.get('PT_DECODE_DIR', DEFAULT_DECODER),
                                             standard_paging=profile['isa'].get('standard_paging', False))
    samples = [json.loads(line) for line in args.input.read_text().splitlines()]
    if args.sample_id is not None:
        samples = [sample for sample in samples if sample['sample_id'] == args.sample_id]
    assert len(samples) == 1, '入口必须恰好收到一个认证后的样本'
    sample = samples[0]
    assert sample['schema_version'] == 1 and sample['post_registers'] and sample['result'] is not None
    case = replay.platform_case(sample, decoder, profile, lock['platform_gen_sha256'])
    case['source'] = dict(path=str(args.input.resolve()), sample_id=sample['sample_id'],
                          certification='调用方已通过当前 Isla 认证档', lock_schema_version=lock['schema_version'])
    case['pt_decode'] = provenance
    args.output.mkdir(parents=True, exist_ok=True)
    with managed_children():
        built = replay.build_case(case, args.output, args.compiler)
        os.environ.update(XIANGSHAN_DIFF_SO=str(Path(files['nemu']).resolve()),
                          PAYLOAD_PC=hex(built['symbols']['payload_ins']),
                          EXIT_LOW=hex(built['symbols']['good_trap_ins']),
                          EXIT_HIGH=hex(built['symbols']['fail_memory_trap']))
        result = replay.run_probe(built, files['emu'], args.observer, timeout=args.timeout)
        trace_path = args.output / 'native-nemu-trace.jsonl'
        trace = [json.loads(line) for line in trace_path.read_text().splitlines()] if trace_path.exists() else []
        merged = finish_result(built, result, trace, Path(result['log']).read_text(errors='replace'), fuzz)
    merged.update(source=case['source'], phase='execute', lock_schema_version=lock['schema_version'])
    (args.output / 'result.json').write_text(json.dumps(merged, ensure_ascii=False, indent=2) + '\n')
    return merged


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('input', 'profile', 'lock', 'files', 'observer', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--sample-id', type=int)
    parser.add_argument('--timeout', type=float, default=120)
    parser.add_argument('--compiler', default='riscv64-unknown-elf-gcc')
    args = parser.parse_args()
    assert 0 < args.timeout <= 600
    try:
        if (args.output.parent / 'CANCEL').exists():
            # 启动器所在进程环境可能已退出；只通知持有本输出目录的 Rust 父进程。
            parent = os.getppid()
            command = Path(f'/proc/{parent}/cmdline').read_bytes().split(b'\0')
            index = command.index(b'--fuzz-output')
            assert Path(os.fsdecode(command[index+1])).resolve() == args.output.parent.parent.resolve()
            os.kill(parent, signal.SIGTERM)
            raise InterruptedError('本 campaign 已请求取消')
        run(args)
    except BaseException as error:
        # 写取证记录后继续抛错，不把内部错误变成正常重放结果。
        args.output.mkdir(parents=True, exist_ok=True)
        result = dict(sample_id=args.sample_id, bucket='worker-error', reason=f'{type(error).__name__}: {error}',
                      agree=False, isla_cause=None, xs_cause=None, nemu_cause=None,
                      isla_consistent_side='unobserved', phase='worker', elf_sha256=None,
                      mismatch=dict(filtered=False, known_rule=None, group_key=None))
        (args.output / 'result.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
        raise


if __name__ == '__main__':
    main()
