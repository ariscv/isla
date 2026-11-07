#!/usr/bin/env bash
# 在本工作树重用只读 Python 算子；不调用硬件、不计算来源哈希、不改 Python 文件。
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
exec python3 - "$@" <<'PY'
import concurrent.futures
import copy
import fcntl
import importlib.util
import json
import os
from pathlib import Path
import random
import signal
import subprocess
import sys
import threading
import time

root = Path.cwd()
if 'FUZZ_STEP3_OUTPUT' not in os.environ:
    raise RuntimeError('必须显式设置 FUZZ_STEP3_OUTPUT，选择本工作树内的独立绝对输出目录')
base = Path(os.environ['FUZZ_STEP3_OUTPUT'])
assert base.is_absolute()
inputs_base = root / 'output/fuzz-step3/python-inputs'
slots = root / 'output/fuzz-step3/process-slots'
slots.mkdir(parents=True,exist_ok=True)
for name in ('tmp','cache'):
    (base/name).mkdir(parents=True,exist_ok=True)
source = root.parent / 'replay-p0'
action = sys.argv[1] if len(sys.argv) > 1 else 'run'
values = (1, 42, 2026)
scenes = ('sv39-store', 'sv39-load')
cancelled = threading.Event()
children = {}
children_lock = threading.RLock()

def stop(signum, frame):
    cancelled.set()
    with children_lock:
        for process in children.values():
            if process.poll() is None:
                os.killpg(process.pid,signal.SIGTERM)
    print('已取消驱动，正在结束本驱动的子进程',flush=True)

signal.signal(signal.SIGINT,stop)
signal.signal(signal.SIGTERM,stop)

def write(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')

def generate(scene, number):
    directory = inputs_base / scene / str(number)
    if (directory / 'generation.json').exists():
        return directory
    directory.mkdir(parents=True, exist_ok=False)
    sys.path.insert(0, str(source / 'difftest-xiangshan'))
    import paging_fuzz as fuzz
    import paging_replay as replay
    # 只装载已存在的解码接口，直接沿用标准分页适配；避免 load_decoder 的来源哈希。
    path = root / 'agents/path_merge_call_support/pt_decode/pt_decode.py'
    spec = importlib.util.spec_from_file_location('step3_pt_decode', path)
    decoder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(decoder)
    decoder.classify_pte = lambda value, level, config: replay.classify_standard_pte(decoder, value, level, config)
    corpus = [json.loads(line) for line in (source / 'output/ecfg4b' / scene / 'samples.jsonl').read_text().splitlines()]
    profile = json.loads((source / 'output/ecfg4b/profile.json').read_text())
    rng = random.Random(number)
    parents = copy.copy(corpus)
    rng.shuffle(parents)
    inputs, records, rejected = [], [], []
    def identity(sample):
        return json.dumps({key: sample[key] for key in ('pre_registers', 'pre_memory', 'isa_state')}, sort_keys=True)
    seen = {identity(s) for s in corpus}
    attempts = 0
    started = time.monotonic()
    while len(inputs) < 2000:
        assert attempts < 40000
        parent = parents[attempts % len(parents)]
        operator = fuzz.OPERATORS[attempts % 3]
        attempts += 1
        try:
            sample, decoded, change = fuzz.mutate(parent, operator, rng, decoder, profile, len(inputs))
        except fuzz.MutationRejected as error:
            rejected.append(dict(stage='platform', reason=str(error)))
            continue
        key = identity(sample)
        if key in seen:
            rejected.append(dict(stage='duplicate'))
            continue
        seen.add(key)
        inputs.append(sample)
        change['sample_id'] = sample['sample_id']
        records.append(change)
    (directory / 'inputs.jsonl').write_text(''.join(json.dumps(s, sort_keys=True) + '\n' for s in inputs))
    write(directory / 'mutations.json', records)
    write(directory / 'generation.json', dict(scene=scene, random_seed=number, count=len(inputs), attempts=attempts, rejected=rejected, seconds=time.monotonic()-started))
    return directory

def run_in_slot(task, slot):
    if cancelled.is_set():
        raise RuntimeError('驱动已取消，不再启动任务')
    kind, scene, number = task
    directory = base / kind / scene / str(number)
    directory.mkdir(parents=True, exist_ok=False)
    argv = json.loads((root / 'output/fuzz-step2/replay' / scene / 'done.json').read_text())['command']
    argv[0] = os.environ.get('FUZZ_STEP3_BINARY',str(root / 'target/release/isarch'))
    data = inputs_base / scene / str(number)
    argv[argv.index('--fuzz-mutations')+1] = str(data / 'mutations.json')
    argv[argv.index('--fuzz-output')+1] = str(directory / 'fuzz')
    argv += ['--fuzz-inputs', str(data / 'inputs.jsonl'), '--fuzz-seed', str(number)]
    if kind != 'baseline':
        argv[argv.index('--fuzz-mode')+1] = 'campaign'
        argv += ['--fuzz-budget', '2000', '--fuzz-control-percent', '5']
        if kind != 'performance':
            argv += ['--fuzz-certify-all']
    assert argv[argv.index('-T')+1] == '32'
    environment = os.environ.copy()
    environment.pop('LD_PRELOAD', None)
    environment.update(TMPDIR=str(base/'tmp'), XDG_CACHE_HOME=str(base/'cache'), PYTHONDONTWRITEBYTECODE='1')
    started = time.monotonic()
    with (directory/'stdout.log').open('w') as out, (directory/'stderr.log').open('w') as err:
        with children_lock:
            if cancelled.is_set():
                raise RuntimeError('驱动已取消，不再启动任务')
            process = subprocess.Popen(argv, cwd=directory, env=environment, stdout=out, stderr=err, start_new_session=True,pass_fds=(slot.fileno(),))
            children[process.pid] = process
        try:
            write(directory/'running.json',dict(command=argv,pid=process.pid,slot=slot.name,started=time.time()))
            while True:
                if cancelled.is_set():
                    raise RuntimeError('驱动已取消')
                try:
                    returncode = process.wait(timeout=30)
                    break
                except subprocess.TimeoutExpired:
                    last_output = (directory/'stderr.log').stat().st_mtime
                    if time.time()-last_output > 2400:
                        raise TimeoutError('连续 40 分钟没有日志进展，停止本批次')
        except BaseException:
            if process.poll() is None:
                os.killpg(process.pid,signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL)
                process.wait()
            raise
        finally:
            with children_lock:
                del children[process.pid]
    write(directory/'done.json', dict(command=argv, cwd=str(directory), returncode=returncode, seconds=time.monotonic()-started))
    assert returncode in (0,1), (kind,scene,number,returncode)
    assert (directory/'fuzz/timing.json').exists(), (kind,scene,number)
    print(kind,scene,number,'完成',round(time.monotonic()-started,3),flush=True)

def run(task):
    # 锁由父子进程共同持有；驱动意外退出也不会提前释放仍在运行的占位。
    while not cancelled.is_set():
        for index in range(4):
            slot = (slots/str(index)).open('a+')
            try:
                fcntl.flock(slot,fcntl.LOCK_EX|fcntl.LOCK_NB)
            except BlockingIOError:
                slot.close()
                continue
            try:
                return run_in_slot(task,slot)
            finally:
                fcntl.flock(slot,fcntl.LOCK_UN)
                slot.close()
        cancelled.wait(0.25)
    raise RuntimeError('驱动已取消，不再启动任务')

if action in ('run','all'):
    for scene in scenes:
        for number in values:
            generate(scene,number)
    tasks = [(kind,scene,number) for number in values for scene in scenes for kind in ('guided','baseline')]
    if action == 'all':
        tasks += [('repeat',scene,1) for scene in scenes]
        tasks += [('performance',scene,1) for scene in scenes]
elif action == 'repeat':
    tasks = [('repeat',scene,1) for scene in scenes]
elif action == 'performance':
    tasks = [('performance',scene,1) for scene in scenes]
else:
    raise ValueError('操作必须是 run、repeat、performance 或 all')
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    list(pool.map(run,tasks))
PY
