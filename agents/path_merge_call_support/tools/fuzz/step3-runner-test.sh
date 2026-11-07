#!/usr/bin/env bash
# 只启动休眠的假程序，检查跨驱动上限、取消清理及父进程意外退出后的锁位。
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
exec python3 - <<'PY'
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import time

root=Path.cwd()
script=root/'agents/path_merge_call_support/tools/fuzz/step3-experiments.sh'
assert 'FUZZ_STEP3_BINARY' in script.read_text(),'测试需要显式假程序入口，禁止误启动实际求解'
base=root/'output/fuzz-step3/runner-test'
base.mkdir(exist_ok=False)
fake=base/'fake-isarch.sh'
fake.write_text('''#!/usr/bin/env bash
set -eu
while [ "$#" -gt 0 ]; do
    if [ "$1" = --fuzz-output ]; then destination="$2"; shift 2; else shift; fi
done
mkdir "$destination"
trap 'rm -f "$destination/alive"; exit 0' TERM INT
touch "$destination/alive"
while true; do sleep 1; done
''')
fake.chmod(0o755)
drivers=[]
logs=[]
def start(name):
    directory=base/name
    log=(base/(name+'.log')).open('w');logs.append(log)
    env=os.environ.copy();env.update(FUZZ_STEP3_OUTPUT=str(directory),FUZZ_STEP3_BINARY=str(fake))
    process=subprocess.Popen(['bash',str(script),'run'],cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
    drivers.append(process)
    return process
def wait_until(predicate):
    limit=time.monotonic()+30
    while not predicate():
        assert time.monotonic()<limit,'进程控制测试超时'
        time.sleep(.05)
def live():
    return list(base.glob('*/**/alive'))
def records():
    return [json.loads(p.read_text()) for p in base.glob('*/**/running.json')]
try:
    first=start('one');second=start('two')
    wait_until(lambda:len(live())==4)
    for i in range(20):
        assert len(live())<=4
        time.sleep(.05)
    first.send_signal(signal.SIGINT);second.send_signal(signal.SIGINT)
    for process in (first,second):
        assert process.wait(timeout=15)!=0
    wait_until(lambda:not live())
    for directory in (base/'one',base/'two'):
        assert len(list(directory.glob('**/running.json')))<=4,'取消后不得再启动队列任务'
    third=start('killed')
    wait_until(lambda:len(live())==4)
    active=[json.loads(p.read_text()) for p in (base/'killed').glob('**/running.json')]
    assert len(active)==4
    third.kill();third.wait(timeout=5)
    held=0
    for i in range(4):
        with (root/'output/fuzz-step3/process-slots'/str(i)).open('a+') as slot:
            try:
                fcntl.flock(slot,fcntl.LOCK_EX|fcntl.LOCK_NB)
            except BlockingIOError:
                held+=1
            else:
                fcntl.flock(slot,fcntl.LOCK_UN)
    assert held==4,'父进程被强制结束后，子进程必须继续持有锁位'
    for row in active:
        os.killpg(row['pid'],signal.SIGTERM)
    wait_until(lambda:not live())
    for row in active:
        try:
            os.kill(row['pid'],0)
        except ProcessLookupError:
            continue
        # 已退出且待收取的进程也不会占用锁位。
        assert Path('/proc').joinpath(str(row['pid']),'stat').read_text().rsplit(') ',1)[1].startswith('Z')
    for i in range(4):
        with (root/'output/fuzz-step3/process-slots'/str(i)).open('a+') as slot:
            fcntl.flock(slot,fcntl.LOCK_EX|fcntl.LOCK_NB)
            fcntl.flock(slot,fcntl.LOCK_UN)
    (base/'result.json').write_text(json.dumps(dict(cross_driver_limit=4,cancel_reaped=True,no_queued_start_after_cancel=True,child_retains_slot_after_parent_kill=True,slots_released=True),indent=2)+'\n')
    print('跨驱动上限、取消清理、意外退出锁位：通过')
finally:
    for process in drivers:
        if process.poll() is None:
            process.terminate()
            process.wait(timeout=15)
    for row in records():
        try:
            os.killpg(row['pid'],signal.SIGTERM)
        except ProcessLookupError:
            continue
    for log in logs:
        log.close()
PY
