#!/usr/bin/env python3
"""Isla JSON 到 XiangShan DiffTest 的最小 RVV 批处理链路。"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


ROOT = Path(__file__).resolve().parent
DEFAULT_SOURCE = ROOT.parent / "isla" / "output" / "rv64_zVVTYPE.json"
DEFAULT_OUT = ROOT / "work"
ENCODING_RE = re.compile(r"(?:32|64)'h([0-9a-fA-F_]+)$")
BITS_RE = re.compile(r"(\d+)'h([0-9a-fA-F_]+)$")
VECTOR_RE = re.compile(r"^vr([0-9]|[12][0-9]|3[01])$")
GPR_RE = re.compile(r"^x([0-9]|[12][0-9]|3[01])$")
V_CONTEXT_REGISTERS = {"vl", "vstart", "vtype", "vcsr"}
VSTART_CSR = 0x008
VXSAT_CSR = 0x009
VXRM_CSR = 0x00A
PMPCFG0_CSR = 0x3A0
PMPADDR0_CSR = 0x3B0
T0 = 5
T1 = 6
TRAP_RET_VAL_RE = re.compile(r"^(Illegal_Instruction|Memory_Exception)")
RESULTS_NDJSON = "results.ndjson"


def expects_trap(entry: dict) -> bool:
    """Isla 预期该条目 payload 触发 trap（非法指令或访存异常）。"""
    return bool(TRAP_RET_VAL_RE.match(str(entry.get("ret_val", ""))))


def read_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict) or not isinstance(value.get("gen"), list):
        raise ValueError(f"{path} 不是 Isla gen JSON")
    return value


def source_entries(
    paths: list[Path], count: int, drop_vector_state: bool, ret_val_regex: str | None
) -> list[dict]:
    pattern = re.compile(ret_val_regex) if ret_val_regex else None
    entries: list[dict] = []
    for path in paths:
        for entry in read_json(path)["gen"]:
            instruction = entry.get("test-ins")
            encoding = entry.get("test-ins-encdec")
            arch = entry.get("arch", {})
            if not isinstance(instruction, str) or not isinstance(encoding, str):
                continue
            if arch.get("xlen") not in (64, "64"):
                continue
            if pattern is not None and not pattern.search(str(entry.get("ret_val", ""))):
                continue
            selected = copy.deepcopy(entry)
            selected["source_file"] = path.name
            if drop_vector_state:
                state = selected.get("isa-state", {})
                if isinstance(state, dict):
                    for name in list(state):
                        if VECTOR_RE.fullmatch(name):
                            del state[name]
            entries.append(selected)
            if count and len(entries) == count:
                return entries
    if not entries:
        raise ValueError("输入 JSON 中没有可用的 RV64 指令")
    return entries


def prepare(args: argparse.Namespace) -> None:
    sources = args.source or [str(DEFAULT_SOURCE)]
    entries = source_entries(
        [Path(p).resolve() for p in sources],
        args.count,
        args.drop_vreg_state,
        args.ret_val_regex,
    )
    output = Path(args.output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    metadata = {
        "purpose": "从现有 Isla V JSON 选取的 XiangShan RVV 小样本",
        "source_json": [str(Path(p).resolve()) for p in sources],
        "vlen_bits": args.vlen_bits,
        "vector_state": "reset-zero" if args.drop_vreg_state else "from-isla-json",
        "selection_count": len(entries),
    }
    if args.ret_val_regex:
        metadata["ret_val_regex"] = args.ret_val_regex
    payload = {"metadata": metadata, "gen": entries}
    output.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"已写入 {output}（{len(entries)} 条）")


def parse_encoding(value: str) -> int:
    match = ENCODING_RE.fullmatch(value.strip())
    if match is None:
        raise ValueError(f"不支持的 test-ins-encdec: {value!r}")
    return int(match.group(1).replace("_", ""), 16)


def parse_bits(value: str, name: str, maximum_width: int = 64) -> int:
    match = BITS_RE.fullmatch(value.strip())
    if match is None:
        raise ValueError(f"{name} 不是无掩码十六进制位向量: {value!r}")
    width = int(match.group(1))
    if width < 1 or width > maximum_width:
        raise ValueError(f"{name} 位宽为 {width}，要求在 1..{maximum_width} 内")
    value = int(match.group(2).replace("_", ""), 16)
    if value >= 1 << width:
        raise ValueError(f"{name} 的值超出声明位宽")
    return value


def parse_vector(value: str, vlen_bits: int) -> tuple[int, int]:
    try:
        width_text, digits = value.split("'h", 1)
        width = int(width_text)
    except (ValueError, AttributeError) as exc:
        raise ValueError(f"无效向量寄存器值: {value!r}") from exc
    if width != vlen_bits:
        raise ValueError(
            f"JSON 向量状态为 {width} bit，但目标 XiangShan VLEN 为 {vlen_bits} bit；"
            "拒绝截断或补零以避免错误的 DiffTest 结论"
        )
    return int(digits.replace("_", ""), 16), width // 64


def encode_vsetvli(rd: int, rs1: int, vtypei: int) -> int:
    if not 0 <= vtypei < 1 << 11:
        raise ValueError(f"vsetvli 的 vtypei 超出 11 位: 0x{vtypei:x}")
    return (vtypei << 20) | (rs1 << 15) | (0b111 << 12) | (rd << 7) | 0x57


def encode_csrw(csr: int, rs1: int) -> int:
    return (csr << 20) | (rs1 << 15) | (0b001 << 12) | 0x73


def encode_vl1re8(vd: int, rs1: int) -> int:
    return (1 << 25) | (0b01000 << 20) | (rs1 << 15) | (vd << 7) | 0x07


def vtype_is_illegal(vtype: int, vlen_bits: int) -> bool:
    if vtype >> 63:
        return True
    if vtype & ~0xFF:
        return True
    vsew = (vtype >> 3) & 0b111
    vlmul = vtype & 0b111
    if vsew > 3 or vlmul == 0b100:
        return True
    sew = 1 << (vsew + 3)
    lmul_power = vlmul if vlmul < 4 else vlmul - 8
    return vlen_bits * (1 << max(lmul_power, 0)) < sew * (1 << max(-lmul_power, 0))


def vtype_vlmax(vtype: int, vlen_bits: int) -> int:
    if vtype_is_illegal(vtype, vlen_bits):
        raise ValueError(f"非法 vtype 0x{vtype:x} 没有可重建的 VLMAX")
    vsew = (vtype >> 3) & 0b111
    vlmul = vtype & 0b111
    sew = 1 << (vsew + 3)
    lmul_power = vlmul if vlmul < 4 else vlmul - 8
    numerator = vlen_bits * (1 << max(lmul_power, 0))
    denominator = sew * (1 << max(-lmul_power, 0))
    if numerator % denominator:
        raise ValueError(
            f"VLEN={vlen_bits}、vtype=0x{vtype:x} 得到非整数 VLMAX，无法重建硬件上下文"
        )
    return numerator // denominator


def vector_context_setup(state: dict, vlen_bits: int) -> tuple[list[str], list[str]]:
    context_registers = V_CONTEXT_REGISTERS.intersection(state)
    if not context_registers:
        return [], []
    if "vtype" not in state:
        raise ValueError("存在 V 扩展上下文，但 isa-state 缺少 vtype")

    vtype = parse_bits(str(state["vtype"]), "vtype")
    illegal_vtype = vtype_is_illegal(vtype, vlen_bits)
    if "vl" in state:
        vl = parse_bits(str(state["vl"]), "vl")
    elif illegal_vtype:
        vl = 0
    else:
        raise ValueError("合法 vtype 的 V 上下文必须显式提供 vl")
    if illegal_vtype and vl != 0:
        raise ValueError("非法 vtype 的硬件上下文必须具有 vl=0")
    if not illegal_vtype:
        vlmax = vtype_vlmax(vtype, vlen_bits)
        if vl > vlmax:
            raise ValueError(
                f"vl={vl} 超出 vtype=0x{vtype:x} 在 VLEN={vlen_bits} 下的 VLMAX={vlmax}；"
                "VSETVL 会静默截断，拒绝生成语义不一致的测试"
            )

    vtypei = 0x400 if illegal_vtype else vtype
    vsetvli_comment = (
        "vsetvli zero, t1, 0x400 (建立 VILL)"
        if illegal_vtype
        else f"vsetvli zero, t1, 0x{vtypei:x}"
    )
    before_loads = [
        f"    li t1, {vl}",
        f"    .4byte 0x{encode_vsetvli(0, T1, vtypei):08x} # {vsetvli_comment}",
    ]
    after_loads: list[str] = []
    if "vstart" in state:
        vstart = parse_bits(str(state["vstart"]), "vstart")
        after_loads.extend([
            f"    li t0, {vstart}",
            f"    .4byte 0x{encode_csrw(VSTART_CSR, T0):08x} # csrw vstart, t0",
        ])
    if "vcsr" in state:
        vcsr = parse_bits(str(state["vcsr"]), "vcsr", maximum_width=3)
        after_loads.extend([
            f"    li t0, {(vcsr >> 1) & 0b11}",
            f"    .4byte 0x{encode_csrw(VXRM_CSR, T0):08x} # csrw vxrm, t0",
            f"    li t0, {vcsr & 1}",
            f"    .4byte 0x{encode_csrw(VXSAT_CSR, T0):08x} # csrw vxsat, t0",
        ])
    return before_loads, after_loads


def vector_setup(state: dict, vlen_bits: int) -> tuple[list[str], list[str]]:
    registers = sorted((key for key in state if VECTOR_RE.fullmatch(key)), key=lambda key: int(key[2:]))
    if not registers:
        return [], []
    words: list[str] = []
    loads: list[str] = ["    la t0, vector_initial_state"]
    for index, name in enumerate(registers):
        value, word_count = parse_vector(str(state[name]), vlen_bits)
        if index == 0:
            expected_words = word_count
        elif word_count != expected_words:
            raise ValueError("同一 JSON 中存在不同宽度的向量寄存器")
        register = int(name[2:])
        loads.append(f"    .4byte 0x{encode_vl1re8(register, T0):08x} # vl1re8.v v{register}, (t0)")
        loads.append(f"    addi t0, t0, {word_count * 8}")
        for word in range(word_count):
            words.append(f"    .dword 0x{(value >> (64 * word)) & ((1 << 64) - 1):016x}")
    return loads, words


def scalar_setup(state: dict) -> list[str]:
    registers = sorted(
        (key for key in state if GPR_RE.fullmatch(key)), key=lambda key: int(key[1:])
    )
    loads: list[str] = []
    for name in registers:
        register = int(name[1:])
        value = parse_bits(str(state[name]), name)
        if register == 0:
            if value != 0:
                raise ValueError("x0 必须为零")
            continue
        loads.append(f"    li {name}, 0x{value:x}")
    return loads


def privilege_setup(state: dict) -> list[str]:
    privilege = state.get("cur_privilege", "Machine")
    if privilege == "Machine":
        return ["payload:"]
    mpp = {"User": 0, "Supervisor": 1}.get(privilege)
    if mpp is None:
        raise ValueError(f"不支持的 cur_privilege: {privilege!r}")
    return [
        "    li t0, -1",
        f"    .4byte 0x{encode_csrw(PMPADDR0_CSR, T0):08x} # csrw pmpaddr0, t0",
        "    li t0, 0x1f",
        f"    .4byte 0x{encode_csrw(PMPCFG0_CSR, T0):08x} # csrw pmpcfg0, t0",
        "    la t0, payload",
        "    csrw mepc, t0",
        "    csrr t0, mstatus",
        "    li t1, -6145",
        "    and t0, t0, t1",
        f"    li t1, {mpp << 11}",
        "    or t0, t0, t1",
        "    csrw mstatus, t0",
        "    mret",
        "payload:",
    ]


def make_assembly(entry: dict, vlen_bits: int) -> str:
    instruction = str(entry["test-ins"])
    encoding = parse_encoding(str(entry["test-ins-encdec"]))
    state = entry.get("isa-state", {})
    if not isinstance(state, dict):
        raise ValueError("isa-state 必须是对象")
    context_before_loads, context_after_loads = vector_context_setup(state, vlen_bits)
    loads, words = vector_setup(state, vlen_bits)
    scalar_loads = scalar_setup(state)
    expect_trap = expects_trap(entry)
    init = [
        "    csrr t0, mstatus",
        "    li t1, 0x600",
        "    or t0, t0, t1",
        "    csrw mstatus, t0",
        "    # 清零 medeleg：emu 默认 medeleg=0x1444 会把 U-mode 非法指令委托到 stvec=0",
        "    csrw medeleg, x0",
        "    # 任何 trap 进入 M-mode trap_handler，由 mepc 是否等于 payload 区分 trap 位置",
        "    la t0, trap_handler",
        "    csrw mtvec, t0",
    ] + context_before_loads + loads + context_after_loads + privilege_setup(state) + scalar_loads
    if expect_trap:
        payload_tail = [
            "    # Isla 预期该指令 trap：payload 未 trap 时，哨兵全零非法指令必然触发，",
            "    # handler 以 mepc!=payload_ins 挂起暴露",
            "    .4byte 0x00000000",
        ]
        trap_handler = [
            "trap_handler:",
            "    csrr t0, mepc",
            "    la t1, payload_ins",
            "    bne t0, t1, 2f",
            "    # payload_ins 处 trap，与 Isla 预期一致",
            "    # XiangShan DiffTest STATE_GOODTRAP custom instruction.",
            "    .4byte 0x0000006b",
            "2:  j 2b",
        ]
    else:
        payload_tail = [
            "    # XiangShan DiffTest STATE_GOODTRAP custom instruction.",
            "    .4byte 0x0000006b",
        ]
        trap_handler = [
            "trap_handler:",
            "    # 不预期 trap：任何 trap 在此挂起，由超时判定失败",
            "2:  j 2b",
        ]
    data = "\n".join(words) if words else "    .dword 0"
    return "\n".join([
        ".option norvc", ".section .text.init", ".globl _start", "_start:",
        *init,
        "payload_ins:",
        f"    # Isla: {instruction}", f"    .4byte 0x{encoding:08x}",
        *payload_tail,
        "1:  j 1b",
        *trap_handler,
        ".section .data", ".align 3",
        "vector_initial_state:", data, "",
    ])


LINKER = """OUTPUT_ARCH(\"riscv\")
ENTRY(_start)
SECTIONS {
  . = 0x80000000;
  .text.init : { KEEP(*(.text.init)) }
  . = ALIGN(0x1000); .text : { *(.text .text.*) }
  . = ALIGN(0x1000); .data : { *(.data .data.* .sdata .sdata.*) }
  .bss (NOLOAD) : { *(.bss .bss.* COMMON) }
  /DISCARD/ : { *(.comment) *(.note*) *(.riscv.attributes) }
}
"""


def compile_case(index: int, entry: dict, output: Path, linker: Path, compiler: str, vlen_bits: int) -> dict:
    case_dir = output / f"case-{index:03d}"
    case_dir.mkdir(exist_ok=True)
    assembly = case_dir / "program.S"
    elf = case_dir / "program.elf"
    assembly.write_text(make_assembly(entry, vlen_bits), encoding="utf-8")
    command = [compiler, "-nostdlib", "-nostartfiles", "-static", "-fno-pic", "-march=rv64gc", "-mabi=lp64d", "-Wl,-T," + str(linker), "-Wl,-e,_start", "-o", str(elf), str(assembly)]
    subprocess.run(command, check=True)
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    case = {
        "id": case_dir.name,
        "instruction": entry["test-ins"],
        "encoding": entry["test-ins-encdec"],
        "isa-state": entry.get("isa-state", {}),
        "ret_val": entry.get("ret_val"),
        "expect_trap": expects_trap(entry),
        "source_file": entry.get("source_file"),
        "elf": str(elf),
        "sha256": digest,
    }
    (case_dir / "case.json").write_text(json.dumps(case, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return case


def build(args: argparse.Namespace) -> None:
    source = read_json(Path(args.input).resolve())
    metadata = source.get("metadata", {})
    source_vlen = metadata.get("vlen_bits")
    if source_vlen is not None and source_vlen != args.vlen_bits:
        raise ValueError(f"样本声明 VLEN={source_vlen}，但构建参数是 {args.vlen_bits}")
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    linker = output / "xiangshan.ld"
    linker.write_text(LINKER, encoding="utf-8")
    if args.jobs < 1:
        raise ValueError("--jobs 必须至少为 1")
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        manifest = list(
            executor.map(
                lambda pair: compile_case(pair[0], pair[1], output, linker, args.compiler, args.vlen_bits),
                enumerate(source["gen"]),
            )
        )
    (output / "manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"已生成 {len(manifest)} 个 ELF：{output}")


def timeout_partial_output(exc: subprocess.TimeoutExpired) -> str:
    partial = exc.stdout or ""
    if isinstance(partial, bytes):
        partial = partial.decode(errors="replace")
    return partial


def run_case(case: dict, emulator: Path, diff_so: Path, timeout: int) -> dict:
    started = time.monotonic()
    command = [str(emulator), "-i", case["elf"], "--diff", str(diff_so)]
    log = Path(case["elf"]).parent / "difftest.log"
    try:
        completed = subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            # 新版 emu 把 HIT GOOD TRAP 输出到 stderr,必须合并才能正确判定
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        output = timeout_partial_output(exc)
        try:
            traced = subprocess.run(
                command + ["--dump-commit-trace"],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=timeout,
            )
            output = traced.stdout
        except subprocess.TimeoutExpired as trace_exc:
            trace_partial = timeout_partial_output(trace_exc)
            if trace_partial:
                output = trace_partial
        log.write_text(
            f"DiffTest execution timeout after {timeout}s\n{output}",
            encoding="utf-8",
        )
        return {
            **case,
            "returncode": None,
            "category": "failure",
            "log": str(log),
            "elapsed": round(time.monotonic() - started, 3),
        }
    category = (
        "success"
        if completed.returncode == 0 and "HIT GOOD TRAP" in completed.stdout
        else "failure"
    )
    # ABORT/非零退出的第一跑 stdout 已含 different-at/ABORT/REF dump，直接作为日志；
    # 只有 timeout 才重跑 --dump-commit-trace 定位停止点
    log.write_text(
        "HIT GOOD TRAP\n" if category == "success" else completed.stdout,
        encoding="utf-8",
    )
    return {
        **case,
        "returncode": completed.returncode,
        "category": category,
        "log": str(log),
        "elapsed": round(time.monotonic() - started, 3),
    }


def load_recorded_results(ndjson: Path) -> list[dict]:
    """读取已有 results.ndjson，返回完整记录列表；半行（进程中断残留）打印警告后跳过。"""
    results: list[dict] = []
    if not ndjson.is_file():
        return results
    for line in ndjson.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            print(f"警告：{ndjson} 存在不完整行，已跳过: {line[:80]!r}", file=sys.stderr)
            continue
        results.append(record)
    return results


def run(args: argparse.Namespace) -> None:
    cases_dir = Path(args.cases).resolve()
    cases = json.loads((cases_dir / "manifest.json").read_text(encoding="utf-8"))
    emulator, diff_so = Path(args.emulator), Path(args.diff_so)
    if not emulator.is_file() or not diff_so.is_file():
        raise ValueError("XIANGSHAN_EMU 或 XIANGSHAN_DIFF_SO 不存在")
    if args.jobs < 1:
        raise ValueError("--jobs 必须至少为 1")
    ndjson_path = cases_dir / RESULTS_NDJSON
    results = load_recorded_results(ndjson_path)
    completed_ids = {record["id"] for record in results}
    pending = [case for case in cases if case["id"] not in completed_ids]
    print(f"共 {len(cases)} 条；已完成 {len(completed_ids)} 条；本次运行 {len(pending)} 条")
    needs_separator = (
        ndjson_path.is_file()
        and ndjson_path.stat().st_size > 0
        and ndjson_path.read_bytes()[-1:] != b"\n"
    )
    with ndjson_path.open("a", encoding="utf-8") as stream:
        if needs_separator:
            # 上次中断残留的半行没有换行结尾，先隔断，避免新记录拼接成损坏行
            stream.write("\n")
        done = len(completed_ids)
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = [
                executor.submit(run_case, case, emulator, diff_so, args.timeout)
                for case in pending
            ]
            for future in as_completed(futures):
                result = future.result()
                stream.write(json.dumps(result, ensure_ascii=False) + "\n")
                stream.flush()
                results.append(result)
                done += 1
                print(f"[{done}/{len(cases)}] {result['id']} {result['category']} ({result['elapsed']}s)")
    results_path = cases_dir / "results.json"
    results_path.write_text(json.dumps(results, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    failures = sum(item["category"] != "success" for item in results)
    print(f"DiffTest 完成：{len(results) - failures}/{len(results)} success；{results_path}")
    if failures:
        raise SystemExit(1)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    prepare_parser = commands.add_parser("prepare-json")
    prepare_parser.add_argument("--source", action="append")
    prepare_parser.add_argument("--count", type=int, default=0, help="保留前 N 条；0 表示保留全部")
    prepare_parser.add_argument("--vlen-bits", type=int, default=128)
    prepare_parser.add_argument(
        "--drop-vreg-state",
        action="store_true",
        help="丢弃与目标 VLEN 不兼容的 Isla vreg 初始状态，使用硬件复位零值",
    )
    prepare_parser.add_argument("--output", default=str(DEFAULT_OUT / "isla-vvtype.json"))
    prepare_parser.add_argument(
        "--ret-val-regex",
        default=None,
        help="仅保留 ret_val 匹配该正则的条目；缺省保留全部",
    )
    build_parser = commands.add_parser("build")
    build_parser.add_argument("--input", default=str(DEFAULT_OUT / "isla-vvtype.json"))
    build_parser.add_argument("--output", default=str(DEFAULT_OUT / "elf"))
    build_parser.add_argument("--vlen-bits", type=int, default=128)
    build_parser.add_argument("--compiler", default="riscv64-unknown-elf-gcc")
    build_parser.add_argument("--jobs", type=int, default=1, help="并行编译的进程数")
    run_parser = commands.add_parser("run")
    run_parser.add_argument("--cases", default=str(DEFAULT_OUT / "elf"))
    run_parser.add_argument("--emulator", required=True)
    run_parser.add_argument("--diff-so", required=True)
    run_parser.add_argument("--timeout", type=int, default=120)
    run_parser.add_argument("--jobs", type=int, default=1, help="并行运行的 DiffTest 数量")
    args = parser.parse_args()
    {"prepare-json": prepare, "build": build, "run": run}[args.command](args)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        print(f"错误: {exc}", file=sys.stderr)
        raise SystemExit(2)
