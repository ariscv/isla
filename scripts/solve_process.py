#!/usr/bin/python3
"""仅监督一条 solve timeout 的专属进程组；手动停止必须显式验证 PID 归属。

用于现有 isarch 线程程序及未主动 setsid/setpgid 逃逸的同组子进程。
不追踪主动创建新 session/进程组的命令，也不提供跨任务的进程管理。
"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

SYSTEM_PYTHON = Path('/usr/bin/python3')


def process_stat(pid):
    fields = Path(f'/proc/{pid}/stat').read_text().rsplit(') ', 1)[1].split()
    return {'state': fields[0], 'pgid': int(fields[2]), 'start': int(fields[19])}


def group_live(pgid):
    # leader 尚未 reap，PGID 不可能被其他任务复用；只观察这一组是否仍有活进程。
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit():
            continue
        try:
            info = process_stat(int(entry.name))
        except (FileNotFoundError, ProcessLookupError):
            continue
        if info['pgid'] == pgid and info['state'] != 'Z':
            return True
    return False


def run(args):
    command = args.command
    if command[:1] == ['--']:
        command = command[1:]
    if not command or Path(command[0]).name != 'timeout':
        raise RuntimeError('run 必须接收原 timeout 命令')
    if '/' in args.clause or not args.clause or args.cleanup_grace <= 0:
        raise RuntimeError('clause 或 cleanup-grace 非法')
    received = []

    def interrupted(number, frame):
        received.append(number)

    signal.signal(signal.SIGINT, interrupted)
    signal.signal(signal.SIGTERM, interrupted)
    child = subprocess.Popen(command, start_new_session=True)
    pgid = child.pid
    started = time.monotonic()
    stop_deadline = None
    escalated = False
    while True:
        state = os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
        if state is not None:
            break
        if received and stop_deadline is None:
            # 由原 timeout 先执行 TERM/kill-after；信号重复不重置截止时间。
            os.kill(child.pid, signal.SIGTERM)
            stop_deadline = time.monotonic() + args.cleanup_grace
        if stop_deadline is not None and time.monotonic() >= stop_deadline and not escalated:
            os.killpg(pgid, signal.SIGKILL)
            escalated = True
        time.sleep(.02)
    # timeout 可能先退出而留下忽略 TERM 的孙进程；保留 zombie leader 锁住PGID再清理。
    leftovers = group_live(pgid)
    if leftovers:
        os.killpg(pgid, signal.SIGTERM)
        deadline = stop_deadline if stop_deadline is not None else time.monotonic() + args.cleanup_grace
        while group_live(pgid) and time.monotonic() < deadline:
            time.sleep(.02)
        if group_live(pgid):
            os.killpg(pgid, signal.SIGKILL)
            escalated = True
        deadline = time.monotonic() + 5
        while group_live(pgid):
            if time.monotonic() >= deadline:
                raise RuntimeError('本任务进程组在 SIGKILL 后仍未结束')
            time.sleep(.02)
    child_code = child.wait()
    shell_code = child_code if child_code >= 0 else 128 - child_code
    result = 128 + received[0] if received else shell_code
    report = {'clause': args.clause, 'cwd': str(Path.cwd()), 'supervisor_pid': os.getpid(),
              'timeout_pid': child.pid, 'process_group': pgid, 'command': command,
              'supervisor_signals': received,
              'child_wait': {'exit_code': child_code if child_code >= 0 else None,
                             'signal': -child_code if child_code < 0 else None},
              'waitid_code': state.si_code, 'waitid_status': state.si_status,
              'return_code': result, 'remaining_group_cleanup': leftovers,
              'sent_sigkill': escalated, 'elapsed_seconds': time.monotonic() - started}
    output = Path('output')
    (output / 'process').mkdir(parents=True, exist_ok=True)
    (output / 'process' / f'{args.clause}-{os.getpid()}.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    category = 'intime' if result == 0 else 'timeout' if result == 124 else 'failed'
    message = f'{args.clause} {category}' + (f' ({result})' if category == 'failed' else '') + '\n'
    fd = os.open(output / f'status.{category}.log', os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o666)
    try:
        os.write(fd, message.encode())
    finally:
        os.close(fd)
    return result


def stop(args):
    if not args.pid or args.pid <= 1:
        raise RuntimeError('必须指定有效的 SOLVE_PID；拒绝全局清理')
    if not hasattr(os, 'pidfd_open'):
        raise RuntimeError('系统 Python 缺少 os.pidfd_open；拒绝发送信号')
    if not hasattr(signal, 'pidfd_send_signal'):
        raise RuntimeError('系统 Python 缺少 signal.pidfd_send_signal；拒绝发送信号')
    # pidfd 在身份检查前打开；即使 PID 后续退出/复用，也不会给新进程发信号。
    fd = os.pidfd_open(args.pid)
    try:
        before = process_stat(args.pid)
        cwd = Path(f'/proc/{args.pid}/cwd').resolve(strict=True)
        argv = Path(f'/proc/{args.pid}/cmdline').read_bytes().split(b'\0')
        argv = [os.fsdecode(x) for x in argv if x]
        if cwd != Path.cwd().resolve() or len(argv) < 4 or argv[2] != 'run':
            raise RuntimeError('PID 不属于本 cwd 的 solve 监督命令')
        script = Path(argv[1])
        if not script.is_absolute():
            script = cwd / script
        if script.resolve() != Path(__file__).resolve() or Path(f'/proc/{args.pid}/exe').resolve() != SYSTEM_PYTHON.resolve():
            raise RuntimeError('PID 的可执行文件或监督脚本身份不匹配')
        if '--' not in argv or Path(argv[argv.index('--') + 1]).name != 'timeout':
            raise RuntimeError('PID 未监督 timeout 命令')
        after = process_stat(args.pid)
        if (before['start'], before['pgid']) != (after['start'], after['pgid']):
            raise RuntimeError('PID 身份在核验期间发生变化')
        signal.pidfd_send_signal(fd, signal.SIGTERM)
    finally:
        os.close(fd)
    print(f'已向本 cwd 的 solve 监督进程 {args.pid} 发送 TERM')
    return 0


def main():
    # 直接 `python3 scripts/solve_process.py` 会绕过 shebang；两种入口统一到受信解释器。
    if Path(sys.executable).resolve() != SYSTEM_PYTHON.resolve():
        try:
            os.execv(str(SYSTEM_PYTHON), [str(SYSTEM_PYTHON), str(Path(__file__).resolve()), *sys.argv[1:]])
        except OSError as error:
            print(f'solve 进程清理失败：无法启动系统 Python：{error}', file=sys.stderr)
            return 1
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    runner = sub.add_parser('run')
    runner.add_argument('--clause', required=True)
    runner.add_argument('--cleanup-grace', type=float, default=10)
    runner.add_argument('command', nargs=argparse.REMAINDER)
    killer = sub.add_parser('kill')
    killer.add_argument('--pid', type=int)
    args = parser.parse_args()
    try:
        return run(args) if args.action == 'run' else stop(args)
    except Exception as error:
        print(f'solve 进程清理失败：{error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
