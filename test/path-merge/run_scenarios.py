#!/usr/bin/env python3
"""用 property 的完成路径核对 path merge 场景。"""

import argparse
import itertools
import json
import re
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PROPERTY = HERE.parent / "property"
MODES = ("off", "recursive", "flat")
NAME = re.compile(r"[A-Za-z_]\w*\Z", re.ASCII)
SCALAR = r"(?:true|false|#[bx][0-9a-fA-F]+)"
TERM = re.compile(rf"{SCALAR}|[A-Za-z_][\w!]*", re.ASCII)
DEFAULTS = {
    "expect_paths_unmerged": 2,
    "expect_paths_merged": 1,
    "modes": list(MODES),
    "status": "ready",
    "title": "",
    "intent": "",
    "reason": "",
    "must_merge": "",
    "must_not_merge": "",
    "inputs": {},
    "registers": [],
    "observe": "out_value",
    "ordered_events": False,
    "ordered_memory_events": True,
    "register_reads": {},
    "sequential_ram": False,
    "reverse_region_ready": False,
    "assertion_failures": [],
    "initialized_registers": [],
    "merge_concrete_values": None,
}


class CheckError(Exception):
    """配置、执行或语义错误。"""


def require(condition, detail):
    if not condition:
        raise CheckError(detail)


def read_scene(path):
    source = path.read_text(encoding="utf-8")
    header = re.match(r"\A// --- TOML\n((?://[^\n]*\n)*)// ---\n", source)
    require(header, "需要 // --- TOML 元数据块")
    metadata = tomllib.loads("\n".join(line[2:].removeprefix(" ") for line in header[1].splitlines()))
    require(not (metadata.keys() - DEFAULTS.keys() - {"id", "group"}), "存在未知元数据字段")
    scene = {**DEFAULTS, "id": path.stem, "group": path.stem[0], **metadata}
    require(re.fullmatch(r"[A-H][1-9]\d*-[a-z0-9]+(?:-[a-z0-9]+)*", path.stem), "场景文件名无效")
    require(scene["id"] == path.stem and scene["group"] == path.stem[0], "id、group 须与文件名一致")
    for key in ("title", "intent", "reason", "must_merge", "must_not_merge"):
        require(isinstance(scene[key], str), f"{key} 须是字符串")
    scene["title"] = scene["title"].strip() or path.stem
    scene["intent"] = scene["intent"].strip() or f"核对{scene['title']}的完成路径与观测值。"
    require(scene["status"] in ("ready", "xfail", "todo"), "status 须为 ready、xfail 或 todo")
    require(scene["status"] == "ready" or scene["reason"].strip(), "xfail 和 todo 须说明 reason")
    require(isinstance(scene["modes"], list) and len(scene["modes"]) == len(MODES)
            and all(mode in scene["modes"] for mode in MODES), "modes 必须包含 off、recursive、flat 各一次")
    for key in ("expect_paths_unmerged", "expect_paths_merged"):
        require(type(scene[key]) is int and scene[key] >= 0, f"{key} 须是非负整数")
    for key in ("ordered_events", "ordered_memory_events", "sequential_ram", "reverse_region_ready"):
        require(type(scene[key]) is bool, f"{key} 须是布尔值")
    reads = scene["register_reads"]
    require(isinstance(reads, dict) and all(NAME.fullmatch(name) and type(count) is int and count >= 0
                                            for name, count in reads.items()),
            "register_reads 须是寄存器名到非负读取次数的表")
    merge_concrete = scene["merge_concrete_values"]
    require(merge_concrete is None or type(merge_concrete) is bool, "merge_concrete_values 须是布尔值")
    inputs = scene["inputs"]
    require(isinstance(inputs, dict) and all(NAME.fullmatch(name) and type(width) is int and width > 0
                                             for name, width in inputs.items()), "inputs 须是寄存器名到正位宽的表")
    registers = scene["registers"]
    require(isinstance(registers, list) and all(isinstance(name, str) and NAME.fullmatch(name) for name in registers),
            "registers 须是观测寄存器名列表")
    observe = scene["observe"]
    require(isinstance(observe, str) and NAME.fullmatch(observe), "observe 须是返回值观测寄存器名")
    initialized = scene["initialized_registers"]
    require(isinstance(initialized, list) and all(isinstance(name, str) and NAME.fullmatch(name) for name in initialized),
            "initialized_registers 须为寄存器名列表")
    errors = scene["assertion_failures"]
    require(isinstance(errors, list) and all(isinstance(row, list) and len(row) == len(inputs)
                and all(type(n) is int and 0 <= n < 1 << w for n, w in zip(row, inputs.values())) for row in errors),
            "assertion_failures 必须列出断言失败对应的完整输入")
    names = [*inputs, observe, *registers]
    require(len(names) == len(set(names)), "inputs、observe、registers 的寄存器名须各不相同")
    scene["source"] = source[header.end():]
    return scene


def run(command, seconds, *, cwd=None, script=None):
    try:
        return subprocess.run(command, input=script, capture_output=True, text=True, cwd=cwd,
                              timeout=seconds, check=False)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise CheckError(f"{Path(command[0]).name} 执行失败（外限 {seconds}s）\n{error}") from error


def replay(guard, commands, seconds):
    result = run(["z3", "-in", "-smt2"], seconds, script=f"{guard}\n{commands}\n")
    require(result.returncode == 0 and not result.stderr and "(error" not in result.stdout,
            f"Z3 重放失败\n{result.stdout}{result.stderr}")
    return result.stdout.strip()


def smt_and(terms):
    return f"(and {' '.join(terms)})" if terms else "true"


def query(condition, after=""):
    return f"(push 1)\n(assert {condition})\n(check-sat)\n{after}\n(pop 1)\n"


def register_term(registers, name):
    require(name in registers, f"完成路径缺少已初始化的观测寄存器 {name}")
    return registers[name]


def model_values(guard, requests, seconds):
    script = "".join(query(cond, f"(get-value ({' '.join(terms)}))") for cond, terms in requests)
    raw = replay(guard, script, seconds)
    models = re.split(r"(?m)^sat\s*\n", raw)
    require(models[0] == "" and len(models) == len(requests) + 1, f"Z3 观测结果异常\n{raw}")
    for (_, terms), model in zip(requests, models[1:]):
        pattern = r"\(\s*" + rf"\((?:{TERM.pattern})\s+({SCALAR})\)\s*" * len(terms) + r"\)"
        match = re.fullmatch(pattern, model.strip())
        require(match, f"Z3 观测值须为布尔值或位向量\n{model}")
        yield match.groups()


def path_outcomes(path, scene, domain, seconds):
    inputs = scene["inputs"]
    terminal = path.get("terminal")
    names = [] if terminal else [scene["observe"], *scene["registers"]]
    registers = path["register_values"]
    input_terms = [register_term(registers, name) for name in inputs]
    state_terms = [path["return_value"], *(register_term(registers, name) for name in names)]
    for name in scene["initialized_registers"]:
        state_terms.append(register_term(path["register_initialized"], name))
        names.append(f"initialized({name})")
    require(all(TERM.fullmatch(term) for term in input_terms + state_terms),
            "场景观测须为可重放的布尔值或位向量，请在 Sail 中投影复合值")
    guard = path["guard_smtlib"]
    conditions = [
        smt_and([f"(= {term} (_ bv{value} {width}))"
                 for term, value, width in zip(input_terms, values, inputs.values())])
        for values in domain
    ]
    replies = replay(guard, "".join(query(cond) for cond in conditions), seconds).splitlines()
    require(len(replies) == len(domain) and set(replies) <= {"sat", "unsat"}, f"Z3 守卫结果异常 {replies}")
    reachable = [(values, cond) for values, cond, reply in zip(domain, conditions, replies) if reply == "sat"]
    require(reachable, "导出的可满足路径在观测输入域中没有对应取值")

    memory = path["memory_events"]
    reads = [event for event in path["register_reads"] if event["register"] in scene["register_reads"]]
    events = memory + reads
    predicates = path["memory_event_guards"]
    require(len(predicates) == len(memory), "访存事件与逐事件守卫数量不符")
    predicates = predicates + [event["guard_smtlib"] for event in reads]
    guard_terms = []
    for index, predicate in enumerate(predicates):
        if predicate in ("true", "false"):
            guard_terms.append(predicate)
        else:
            alias = f"isla_observed_event_guard_{index}"
            guard += f"\n(define-fun {alias} () Bool {predicate})"
            guard_terms.append(alias)
    requests = [(cond, guard_terms) for _, cond in reachable]
    enabled = model_values(guard, requests, seconds) if events else itertools.repeat(())
    projections = []
    requests = []
    for (_, cond), evaluated in zip(reachable, enabled):
        require(set(evaluated) <= {"true", "false"}, "事件条件须为布尔值")
        active_memory, active_reads = [], []
        terms = state_terms.copy()
        for index, (event, active) in enumerate(zip(events, evaluated)):
            if active == "true":
                fields = {key: value for key, value in event.items() if key != "guard_smtlib"}
                if index < len(memory):
                    require(fields["kind"] is not None, "场景的访存 kind 须为具体值")
                    active_memory.append(fields)
                    keys = ("address", "data", "tag")
                else:
                    active_reads.append(fields)
                    keys = ("data",)
                terms.extend(fields[key] for key in keys if fields[key] is not None)
        require(all(TERM.fullmatch(term) for term in terms),
                "生效事件的观测值须为可重放的布尔值或位向量")
        guard_equalities = [f"(= {term} {value})" for term, value in zip(guard_terms, evaluated)]
        projections.append((active_memory, active_reads, guard_equalities))
        requests.append((smt_and([cond, *guard_equalities]), terms))

    # 只取生效事件的值，再证明事件是否生效及其观测值都由输入唯一决定。
    mismatches = []
    outcomes = {}
    for ((values, cond), (_, terms), (active_memory, active_reads, equalities), observed) in zip(
            reachable, requests, projections, model_values(guard, requests, seconds)):
        equalities.extend(f"(= {term} {value})" for term, value in zip(terms, observed))
        mismatches.append(f"(and {cond} (not {smt_and(equalities)}))")
        accesses = iter(observed[len(state_terms):])
        for event in active_memory:
            event["address"] = next(accesses)
            event["data"] = next(accesses)
            if event["tag"] is not None:
                event["tag"] = next(accesses)
        for event in active_reads:
            event["data"] = next(accesses)
        if not scene["ordered_memory_events"]:
            active_memory.sort(key=lambda event: json.dumps(event, sort_keys=True))
        if not scene["ordered_events"]:
            active_reads.sort(key=lambda event: (event["register"], event["accessors"], event["data"]))
        outcomes[values] = {"值": dict(zip(["prop", *names], observed)), "访存": active_memory, "ReadReg": active_reads}
        if terminal is not None:
            outcomes[values]["终态"] = terminal
    result = replay(guard, f"(assert (or {' '.join(mismatches)}))\n(check-sat)", seconds)
    require(result == "unsat", f"观测或事件生效条件无法证明唯一（{result}）。把自由选择或访存读值登记为输入")
    for values, outcome in outcomes.items():
        for name, count in scene["register_reads"].items():
            actual = sum(event["register"] == name for event in outcome["ReadReg"])
            require(actual == count, f"输入 {values} 的 ReadReg({name}) 期望 {count} 次，实际 {actual} 次")
    return outcomes


def summarize_paths(paths, scene, seconds):
    inputs = scene["inputs"]
    domain = list(itertools.product(*(range(1 << width) for width in inputs.values())))
    outcomes, partition = {}, []
    for path in paths:
        values = path_outcomes(path, scene, domain, seconds)
        if path.get("terminal") is None:
            partition.append(tuple(sorted(values)))
        for key, value in values.items():
            require(key not in outcomes or (not path.get("terminal") and outcomes[key] == value),
                    f"同一输入 {key} 有不同结果或重复错误终态")
            outcomes[key] = value
    failures = [key for key, value in outcomes.items() if value.get("终态") == "assertion_failure"]
    require(sorted(failures) == sorted(map(tuple, scene["assertion_failures"])), f"断言错误输入与预期不一致 {failures}")
    return outcomes, sorted(partition)


def semantic_difference(baseline, other):
    for inputs in sorted(baseline.keys() | other.keys()):
        if baseline.get(inputs) != other.get(inputs):
            return f"输入 {inputs} 的语义不同\n关闭合并 {baseline.get(inputs)}\n开启合并 {other.get(inputs)}"
    return None


@dataclass
class ModeResult:
    count: int | None = None
    status: str = "FAIL"
    observations: tuple | None = None
    errors: list = field(default_factory=list)
    assertions: list = field(default_factory=list)


def run_mode(scene, shape, mode, binary, directory, seconds, *, reverse=False):
    result = ModeResult()
    output_name = f"{mode}-reverse" if reverse else mode
    target = directory / f"{output_name}.paths.json"
    target.unlink(missing_ok=True)
    config = directory / f"{mode}.toml"
    enabled = mode != "off"
    expected = scene["expect_paths_merged" if enabled else "expect_paths_unmerged"]
    strategy = mode if enabled else "recursive"
    ordered = str(scene["ordered_events"]).lower()
    settings = (f"includes = [{json.dumps(str(ROOT / 'configs/plain.toml'))}]\n"
                "[execution_limits.path_merge]\n"
                f"enabled = {str(enabled).lower()}\nstrategy = {json.dumps(strategy)}\n"
                f"ordered_events = {ordered}\n")
    merge_concrete = scene["merge_concrete_values"]
    if merge_concrete is not None:
        settings += f"merge_concrete_values = {str(merge_concrete).lower()}\n"
    config.write_text(settings, encoding="utf-8")
    try:
        process = run([str(binary), "-A", str(directory / "model.ir"), "-C", str(config), "-p", "prop", "-T", "2",
                       "--expect-paths", str(expected), "--dump-paths", str(target), "--scenario-observations",
                       *(["--sequential-ram"] if scene["sequential_ram"] else []),
                       *(["--observe-assertion-failures"] if scene["assertion_failures"] else []),
                       *(["--reverse-region-ready"] if reverse else [])],
                      seconds, cwd=directory)
        log = directory / f"{output_name}.log"
        log.write_text(process.stdout + process.stderr, encoding="utf-8")
        require(process.returncode in (0, 2) and "ok" in process.stdout.splitlines(),
                f"property 执行或性质失败（退出 {process.returncode}），见 {log}")
        paths = json.loads(target.read_text(encoding="utf-8"))
        result.count = sum(path.get("terminal") is None for path in paths)
        failures = [path for path in paths if path.get("terminal") is not None]
        require(all(path["terminal"] == "assertion_failure" for path in failures), "未知场景错误终态")
        if result.count != expected:
            result.assertions.append(f"期望 {expected} 条完成路径，实际 {result.count} 条")
        require(process.returncode == (2 if result.count != expected else 0), "property 退出码与路径计数不符")
        result.observations = summarize_paths(paths, scene, seconds)
        if enabled and shape.is_file():
            checked = run(["ruby", str(PROPERTY / "include/check_paths.rb"), str(target), str(shape)], seconds)
            (directory / f"{output_name}.shape.log").write_text(checked.stdout + checked.stderr, encoding="utf-8")
            require(checked.returncode in (0, 2), f"形状检查器失败\n{checked.stdout}{checked.stderr}")
            if checked.returncode == 2:
                result.assertions.append(checked.stderr.strip())
    except (CheckError, OSError, ValueError, KeyError, TypeError) as error:
        result.errors.append(str(error))
    return result


def run_scene(scene, source, binary, plugin, directory, seconds):
    results = {mode: ModeResult() for mode in MODES}
    if scene["status"] == "todo":
        for result in results.values():
            result.status = "TODO"
        return results
    directory.mkdir(parents=True, exist_ok=True)
    try:
        compile_result = run(["sail", "-plugin", str(plugin), "-isla", str(source),
                              str(PROPERTY / "include/config.sail"), "-o", "model"], seconds, cwd=directory)
        log = directory / "sail.log"
        log.write_text(compile_result.stdout + compile_result.stderr, encoding="utf-8")
        require(compile_result.returncode == 0, f"Sail 编译失败，见 {log}")
    except (CheckError, OSError) as error:
        for result in results.values():
            result.errors.append(str(error))
        return results

    shape = source.with_suffix(".shape")
    results = {mode: run_mode(scene, shape, mode, binary, directory, seconds) for mode in MODES}
    off, recursive, flat = (results[mode] for mode in MODES)
    if scene["reverse_region_ready"]:
        for mode in ("recursive", "flat"):
            forward = results[mode]
            reverse = run_mode(scene, shape, mode, binary, directory, seconds, reverse=True)
            forward.errors.extend(reverse.errors)
            forward.assertions.extend(reverse.assertions)
            if forward.observations != reverse.observations:
                forward.errors.append("同一 IR 的正序和逆序观测或守卫分组不同")
    for merged in (recursive, flat):
        if merged.observations is not None and off.observations is not None:
            difference = semantic_difference(off.observations[0], merged.observations[0])
            if difference:
                merged.errors.append(difference)
        elif not merged.errors:
            merged.errors.append("无法与关闭合并的基线比较")
    if recursive.observations is not None and flat.observations is not None:
        if recursive.observations != flat.observations:
            for merged in (recursive, flat):
                merged.errors.append("平铺与递归的观测结果或守卫分组不一致")

    for mode, result in results.items():
        if result.errors:
            result.status = "FAIL"
        elif mode != "off" and scene["status"] == "xfail":
            result.status = "XFAIL" if result.assertions else "XPASS"
        else:
            result.status = "FAIL" if result.assertions else "PASS"
    return results


def summary(records):
    rows = ["| 场景 | 位向量 | off | recursive | flat |",
            "| --- | --- | --- | --- | --- |"]
    for scene, width, results in records:
        cells = []
        for result in results.values():
            count = "" if result.count is None else f"（{result.count} 条）"
            cells.append(result.status + count)
        rows.append("| " + " | ".join([scene["id"], width, *cells]) + " |")
    return "\n".join(rows)


def details(records):
    shown_todos = set()
    for scene, width, results in records:
        if scene["status"] == "todo" and scene["id"] not in shown_todos:
            shown_todos.add(scene["id"])
            yield f"{scene['id']} / TODO\n{scene['reason']}"
        for mode, result in results.items():
            if result.errors or result.assertions or result.status == "XPASS":
                suffix = "\n请移除已通过的 xfail 标记" if result.status == "XPASS" else ""
                messages = "\n".join([*result.errors, *result.assertions])
                if result.status == "XFAIL":
                    messages += f"\n{scene['reason']}"
                yield f"{scene['id']} / {width} / {mode} / {result.status}\n{messages}{suffix}".rstrip()


def write_report(path, scenes, table, diagnostics):
    sections = ["# Path merge 场景运行", "", table]
    if diagnostics:
        sections += ["", "## 运行说明", "", "```text", "\n\n".join(diagnostics), "```"]
    for scene, source in scenes:
        sections += ["", f"## {scene['id']} · {scene['title']}", "", scene["intent"]]
        if scene["status"] != "todo":
            sections += ["", f"期望完成路径数为 off {scene['expect_paths_unmerged']}，"
                         f"recursive 和 flat 各 {scene['expect_paths_merged']}。"]
        for key, label in [("must_merge", "必须合并"), ("must_not_merge", "须保留独立路径"), ("reason", "原因")]:
            if scene[key]:
                sections += ["", f"**{label}**　{scene[key]}"]
        sections += ["", "```sail", scene["source"].rstrip(), "```"]
        shape = source.with_suffix(".shape")
        if shape.is_file():
            sections += ["", "**期望守卫形状**", "", "```smtlib", shape.read_text(encoding="utf-8").rstrip(), "```"]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(sections) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--path-merge-filter", default=".", help="场景编号正则")
    parser.add_argument("--property-bin-dir", type=Path, default=ROOT / "target/debug")
    parser.add_argument("--plugin", type=Path, default=ROOT / "isla-sail/plugin.cmxs")
    parser.add_argument("--scenarios-dir", type=Path, default=HERE / "scenarios")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "output/path-merge-scenarios")
    parser.add_argument("--markdown", type=Path, help="写出含 Sail 源码的 Markdown")
    parser.add_argument("--bitvector", choices=("64", "129", "both"), default="64")
    parser.add_argument("--timeout", type=int, default=30, help="每条外部命令的墙钟外限，单位秒")
    args = parser.parse_args()
    try:
        selector = re.compile(args.path_merge_filter)
        require(args.timeout > 0, "--timeout 必须为正数")
        scenes = []
        for source in sorted(args.scenarios_dir.resolve().glob("*.sail")):
            if selector.search(source.stem):
                try:
                    scenes.append((read_scene(source), source))
                except (CheckError, ValueError, OSError) as error:
                    raise CheckError(f"{source.name} 的元数据无效\n{error}") from error
        require(scenes, "没有匹配的场景")
        widths = ("64", "129") if args.bitvector == "both" else (args.bitvector,)
        records = []
        for width in widths:
            binary = args.property_bin_dir.resolve() / ("isla-property" if width == "64" else "isla-property129")
            if any(scene["status"] != "todo" for scene, _ in scenes):
                require(binary.is_file(), f"找不到 property 程序 {binary}")
                require(args.plugin.is_file(), f"找不到 Sail 插件 {args.plugin}")
            for scene, source in scenes:
                directory = args.output_dir.resolve() / scene["id"] / f"B{width}"
                results = run_scene(scene, source, binary, args.plugin.resolve(), directory, args.timeout)
                records.append((scene, f"B{width}", results))
        table = summary(records)
        diagnostics = list(details(records))
        print(table)
        if diagnostics:
            print("\n" + "\n\n".join(diagnostics))
        if args.markdown:
            write_report(args.markdown, scenes, table, diagnostics)
        return int(any(result.status in ("FAIL", "XPASS") for _, _, results in records for result in results.values()))
    except (CheckError, OSError, re.error) as error:
        print(error, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
