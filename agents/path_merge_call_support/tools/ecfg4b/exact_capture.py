#!/usr/bin/env python3
"""只读使用 ecfg4b 输入，重新导出四场景路径约束与守卫定义。"""

import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    args = parser.parse_args()
    source = args.source.resolve()
    out = args.out.resolve()
    out.mkdir(exist_ok=False)
    binary = args.binary.resolve(strict=True)
    assert binary == (source / "bin/isarch").resolve(strict=True)
    ir = (source / "rv64d.ir").resolve(strict=True)
    for directory in ["tmp", "cache"]:
        (out / directory).mkdir()
    inputs = dict(
        binary=str(binary),
        ir=str(ir),
        config=str(source / "config-xs.toml"),
        limits=str(source / "count.toml"),
        sail_model="d79d8b32",
        isla="ae1a3355",
        identity_basis="ecfg4b 指定输入路径；未重新计算哈希",
    )
    (out / "inputs.json").write_text(
        json.dumps(inputs, ensure_ascii=False, indent=2) + "\n"
    )
    symbols = subprocess.check_output(
        ["nm", "-n", "-C", str(binary)], text=True
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

    def run(scene):
        folder = out / scene
        folder.mkdir()
        (folder / "smt").mkdir()
        expected = {}
        for line in (source / scene / "samples.jsonl").open():
            sample = json.loads(line)
            signature = str(sample["path_signature"])
            expected[signature] = expected.get(signature, 0) + 1
        (folder / "expected-paths.json").write_text(
            json.dumps(expected, indent=2) + "\n"
        )
        command = json.loads((source / scene / "done.json").read_text())["command"]
        command[0] = str(binary)
        for flag, value in [
            ("-A", ir),
            ("-C", source / "config-xs.toml"),
            ("--execution-limits-config", source / "count.toml"),
            ("-T", "32"),
            ("--timeout", "890"),
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
            LD_PRELOAD=str(out.parent / "observe.so"),
            LD_LIBRARY_PATH="/home/baiyifan/.local/opt/z3-official-1fd1d3613/lib",
            ISLA_ENUM_GLUE=str(folder / "reports"),
            EXACT_DUMP=str(folder / "smt"),
            EXACT_ENUM_BEGIN=hex(begin),
            EXACT_ENUM_END=hex(end),
            ISLA_ENUM_GLUE_DETAIL=",".join(expected),
            ISLA_STATS="1",
        )
        (folder / "command.json").write_text(
            json.dumps(
                dict(
                    command=command,
                    cwd=str(folder),
                    environment={
                        key: env[key]
                        for key in env
                        if key.startswith(("ISLA_", "EXACT_"))
                        or key
                        in ["TMPDIR", "XDG_CACHE_HOME", "LD_PRELOAD", "LD_LIBRARY_PATH"]
                    },
                ),
                indent=2,
            )
            + "\n"
        )
        start = time.monotonic()
        with (
            (folder / "stderr.txt").open("w") as err,
            (folder / "stdout.txt").open("w") as stdout,
        ):
            result = subprocess.run(
                command, cwd=folder, env=env, stderr=err, stdout=stdout, timeout=900
            )
        status = dict(
            exit=result.returncode,
            seconds=time.monotonic() - start,
            dumps=len(list((folder / "smt").glob("*.smt2"))),
        )
        (folder / "exit.json").write_text(json.dumps(status, indent=2) + "\n")
        print(scene, status, flush=True)
        summary = json.loads(next((folder / "output").glob("rv64_*.json")).read_text())[
            "summary"
        ]
        (folder / "raw-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        assert result.returncode in [0, 1], status
        for key in [
            "execution-timeouts",
            "smt-timeouts",
            "unfinished-paths",
            "model-query-timeouts",
            "pending-batches",
        ]:
            assert summary[key] == 0, (scene, key, summary)
        reports = {
            str(r["path_signature"]): r["class_count"]
            for p in (folder / "reports").glob("glue-*.json")
            for r in [json.loads(p.read_text())]
        }
        assert reports == expected, (scene, reports, expected)
        assert {p.stem[5:] for p in (folder / "smt").glob("path-*.smt2")} == set(
            expected
        )

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(run, ["sv39-load", "sv39-store", "sv48-load", "sv48-store"]))


if __name__ == "__main__":
    main()
