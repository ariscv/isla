"""用 RV64D 的编码及寄存器接口，只替换 execute 正文，测试停止、缓存及样本读回。"""
import argparse
import json
import os
import shutil
import re
import signal
import subprocess
import time
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
for field in ("binary", "ir", "config", "out"):
    p.add_argument(field, type=lambda s: Path(s).resolve())
p.add_argument("mode", choices=("timeout", "term", "int", "queued", "replace", "zero"))
a = p.parse_args()
a.out.mkdir(parents=True)
(a.out / "output").mkdir()
slow = a.mode != "zero"
body = """fn zexecute(zmergez3var) {
  zvalue : %bv64;
  zvalue = zget_X_bits(0b00001);
  jump @eq(zvalue, 0x0000000000000000) goto 5;
  return = zRETIRE_SUCCESS;
  end;
  {end};
}""".replace("{end}", "goto 5" if slow else "goto 3")
if a.mode == "queued":
    # 单线程先交付 x1=0，再探索 x1=1。到限时两个自环分别在途和排队。
    body = """fn zexecute(zmergez3var) {
  zvalue : %bv64;
  zvalue = zget_X_bits(0b00001);
  jump @eq(zvalue, 0x0000000000000000) goto 6;
  jump @eq(zvalue, 0x0000000000000001) goto 5;
  goto 4;
  goto 5;
  return = zRETIRE_SUCCESS;
  end;
}"""
ir, replaced = re.subn(r"(?ms)^fn zexecute\(.*?^\}", body, a.ir.read_text())
assert replaced == 1
(a.out / "fixture.ir").write_text(ir)
config = a.config.read_text()
command = [str(a.binary), "-A", "fixture.ir", "-C", "config.toml", "-T", "1" if a.mode == "queued" else "2",
           "--no-path-merging", "--tastic", "default", "solve-state", "--clause=MRET"]

if a.mode == "replace":
    # 运行中重新构建同名工具，发布器仍需读取实际运行的二进制记录来源。
    executable = a.out / "isarch"
    shutil.copyfile(a.binary, executable)
    executable.chmod(0o755)
    command[0] = str(executable)

def run(label, args, expected=0, send=None):
    logfile = a.out / (label + ".log")
    with logfile.open("w") as log:
        child = subprocess.Popen(command + args, cwd=a.out, stdout=log, stderr=subprocess.STDOUT)
        try:
            if send:
                deadline = time.monotonic() + 20
                while child.poll() is None and time.monotonic() < deadline:
                    if "[PATH_CACHE_TERMINAL]" in logfile.read_text():
                        if a.mode == "replace":
                            os.unlink(command[0])
                        child.send_signal(send)
                        break
                    time.sleep(0.025)
            rc = child.wait(timeout=100)
            assert rc == expected, (label, rc, expected, logfile)
        finally:
            if child.poll() is None:
                child.kill()
            child.wait()

def capture(label, extra, expected, send=None):
    run(label, ["--path-cache-only", "--path-cache-format", "bin", "--path-cache-write", label, *extra], expected, send)
    return json.loads((a.out / label / "manifest.json").read_text())

(a.out / "config.toml").write_text(config)
if not slow:
    default = capture("default", [], 0)
    (a.out / "config.toml").write_text(config + '\n[run_control]\nprogram_timeout = "1ms"\n')
    zero = capture("zero", ["--program-timeout", "0"], 0)
    for key in ("completeness", "errors", "path_signatures", "normal_paths", "execution_error_paths", "model_exception_paths"):
        assert default[key] == zero[key], key
    assert zero["completeness"] == "complete" and zero["normal_paths"] == 2
else:
    send = {"term": signal.SIGTERM, "int": signal.SIGINT, "replace": signal.SIGTERM}.get(a.mode)
    if a.mode in ("timeout", "queued"):
        (a.out / "config.toml").write_text(config + '\n[run_control]\nprogram_timeout = "6s"\n')
    options = ["--merge-diagnostics", "summary"] if a.mode == "int" else []
    manifest = capture("partial", options, 124, send)
    assert manifest["completeness"] == "partial" and manifest["normal_paths"] == 1
    assert manifest["execution_error_paths"] == 0 and manifest["errors"]["errors"] == 0
    stopped = 2 if a.mode == "queued" else 1
    assert manifest["errors"]["unfinished-paths"] == stopped
    assert manifest["category_counts"]["ProgramStop"] == stopped
    assert manifest["stop_reason"] == {"int": "SIGINT", "term": "SIGTERM", "replace": "SIGTERM", "timeout": "program-timeout", "queued": "program-timeout"}[a.mode]
    command[0] = str(a.binary)
    read = ["--path-cache-read", "partial", "--path-cache-encoding", "bin", "--path-cache-recompute-facts"]
    (a.out / "config.toml").write_text(config + """
[execution_limits.path_merge.enumeration]
outputs = [{ format = "v1_jsonl", path = "samples.jsonl" }]
""")
    run("export", read)
    (a.out / "config.toml").write_text(config)
    run("check", read + ["--check-samples", "samples.jsonl", "--check-samples-limit", "1", "--check-samples-report", "check.json"])
    report = json.loads((a.out / "check.json").read_text())
    assert report["sample_total"] == 1 and report["samples"][0]["consistent_paths"] == 1
    assert not report["inconsistent"] and not report["unaccepted_sample_ids"]
    if a.mode == "timeout":
        # 在首条路径完成前到限，直接收尾，不把空队列交给常驻 judge。
        run("early-resident", ["--program-timeout", "1ms", "--judge-resident", "samples.jsonl",
                               "--judge-resident-out", "resident.jsonl"], 124)
print(a.mode, "PASS")
