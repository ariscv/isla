#!/usr/bin/env python3
"""只读复制 F16 输入，批量导出原始路径约束；不展开类内位组合。"""

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source", type=Path, required=True, help="F16 output/f16 目录"
    )
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--detail", action="store_true", help="导出全部守卫定义")
    parser.add_argument("--binary", type=Path, help="额外核对 fff25fa 已冻结二进制")
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(exist_ok=True)
    inputs = out / "inputs"
    inputs.mkdir(exist_ok=True)
    source = args.source.resolve()
    metadata = json.loads((source / "environment.json").read_text())
    if args.binary:
        old = next(path for path in metadata["sha256"] if Path(path).name == "isarch")
        del metadata["sha256"][old]
        metadata["sha256"][str(args.binary.resolve())] = (
            "610df5395219d4202a0dc347d05104737f521562d85dd47a70fbe25d8d31a3db"
        )
    frozen = {}
    for src, expected in metadata["sha256"].items():
        dst = inputs / Path(src).name
        if not dst.exists():
            shutil.copyfile(src, dst)
            dst.chmod(Path(src).stat().st_mode)
        actual = hashlib.sha256(dst.read_bytes()).hexdigest()
        assert actual == expected, (src, actual, expected)
        frozen[dst.name] = actual
    for directory in ["tmp", "cache"]:
        (out / directory).mkdir(exist_ok=True)
    if not (out / "observe.so").exists():
        shutil.copyfile(out.parent / "observe.so", out / "observe.so")
    symbols = subprocess.check_output(
        ["nm", "-n", "-C", str(inputs / "isarch")], text=True
    ).splitlines()
    target = "isla_lib::executor::merge_record::merge_enumeration::parallel::enumerate"
    indices = [
        i for i, line in enumerate(symbols) if line.split(maxsplit=2)[-1] == target
    ]
    assert len(indices) == 1
    index = indices[0]
    begin = int(symbols[index].split()[0], 16)
    end = next(
        int(line.split()[0], 16)
        for line in symbols[index + 1 :]
        if int(line.split()[0], 16) > begin
    )
    (out / "inputs.json").write_text(json.dumps(frozen, indent=2) + "\n")

    def run(scene):
        folder = out / scene
        folder.mkdir()
        shutil.copyfile(
            source / "predict" / scene / "prediction.json",
            folder / "f16-prediction.json",
        )
        (folder / "smt").mkdir()
        limits = folder / "limits.toml"
        limits.write_text("""[execution_limits]
strict=false
[execution_limits.merge_enumeration]
enabled=true
mode="count"
class_cap=1
path_cap=9223372036854775807
sample_stride=1
enumeration_threads=4
""")
        command = json.loads((source / "glue" / scene / "command.json").read_text())[
            "command"
        ]
        command[0] = str(inputs / "isarch")
        for flag, value in [
            ("-A", inputs / "rv64d.ir"),
            ("-C", inputs / "config-xs.toml"),
            ("--execution-limits-config", limits),
            ("--timeout", "1770"),
        ]:
            command[command.index(flag) + 1] = str(value)
        env = os.environ.copy()
        for key in list(env):
            if key.startswith("ISLA_"):
                del env[key]
        env.update(
            TMPDIR=str(out / "tmp"),
            XDG_CACHE_HOME=str(out / "cache"),
            PYTHONDONTWRITEBYTECODE="1",
            LD_PRELOAD=str(out / "observe.so"),
            LD_LIBRARY_PATH="/home/baiyifan/.local/opt/z3-official-1fd1d3613/lib",
            ISLA_ENUM_GLUE=str(folder / "reports"),
            EXACT_DUMP=str(folder / "smt"),
            EXACT_ENUM_BEGIN=hex(begin),
            EXACT_ENUM_END=hex(end),
        )
        if args.detail:
            env["ISLA_ENUM_GLUE_DETAIL"] = ",".join(
                p.stem[5:]
                for p in (source / "glue" / scene / "reports").glob("glue-*.json")
            )
        start = time.monotonic()
        (folder / "command.json").write_text(
            json.dumps(
                dict(
                    command=command,
                    environment={
                        key: env[key]
                        for key in [
                            "LD_PRELOAD",
                            "LD_LIBRARY_PATH",
                            "ISLA_ENUM_GLUE",
                            "EXACT_DUMP",
                            "EXACT_ENUM_BEGIN",
                            "EXACT_ENUM_END",
                            "ISLA_ENUM_GLUE_DETAIL",
                        ]
                        if key in env
                    },
                ),
                indent=2,
            )
        )
        with (
            (folder / "stderr.txt").open("w") as err,
            (folder / "stdout.txt").open("w") as stdout,
        ):
            result = subprocess.run(
                command, cwd=folder, env=env, stderr=err, stdout=stdout, timeout=1800
            )
        status = dict(
            exit=result.returncode,
            seconds=time.monotonic() - start,
            dumps=len(list((folder / "smt").glob("*.smt2"))),
        )
        (folder / "exit.json").write_text(json.dumps(status, indent=2) + "\n")
        print(scene, status, flush=True)
        assert result.returncode == 0

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(run, ["sv39-load", "sv39-store", "sv48-load", "sv48-store"]))


if __name__ == "__main__":
    main()
