"""提取最后快照，或将静态测量 JSON 渲染为中文报告；不启动执行器。"""
import argparse
import collections
import json
from pathlib import Path


DIRECTORY = Path(__file__).resolve().parent
CLAUSES = "FVFMATYPE FVFMTYPE FVFTYPE FVVMATYPE FVVMTYPE FVVTYPE FWFTYPE FWVFMATYPE FWVVMATYPE FWVVTYPE".split()
TAGS = ["ARM_UNSUPPORTED_SNAPSHOT", "FORK_STATS_SNAPSHOT", "MERGE_STATS_SNAPSHOT"]


def extract(source_root):
    clauses = []
    configurations = set()
    for clause in CLAUSES:
        if clause in {"FWVVMATYPE", "FWVVTYPE"}:
            log = source_root / "pathmerge-cache-all-20261110" / "runs" / clause / "isarch.log"
        else:
            log = source_root / "pathmerge-all-20261110/isla/agents/pathmerge_all_clauses_20261110/runs" / clause / "isarch.log"
        snapshots = {}
        with log.open() as lines:
            for line in lines:
                for tag in TAGS:
                    marker = f"[{tag}] "
                    if marker in line:
                        snapshots[tag] = json.loads(line.split(marker, 1)[1])
        assert set(snapshots) == set(TAGS), clause
        arguments = json.loads((log.parent / "command.json").read_text())["argv"]
        config = arguments[arguments.index("-C") + 1]
        configurations.add(Path(config).read_text())
        groups = {}
        for row in snapshots[TAGS[0]]["top"]:
            key = row["function"], row["branch_pc"]
            group = groups.setdefault(key, dict(function=key[0], branch_pc=key[1], count=0, observed_rejections=[]))
            group["count"] += row["count"]
            group["observed_rejections"].append(row)
        missing = snapshots[TAGS[0]]["total"] - sum(group["count"] for group in groups.values())
        assert missing >= 0
        clauses.append(dict(clause=clause, log=str(log), config=config, snapshots=snapshots,
                            missing_weight=missing, branches=list(groups.values())))
    assert len(configurations) == 1, "各 clause 的加载期配置必须相同"
    (DIRECTORY / "snapshots.json").write_text(json.dumps(clauses, ensure_ascii=False, indent=2) + "\n")


def table(lines, headers, rows):
    lines.extend(["| " + " | ".join(headers) + " |", "| " + " | ".join(["---"] * len(headers)) + " |"])
    lines.extend("| " + " | ".join(map(str, row)) + " |" for row in rows)
    lines.append("")


def report():
    clauses = json.loads((DIRECTORY / "m0.json").read_text())
    baseline = json.loads((DIRECTORY / "m0-baseline.json").read_text())
    assert [clause["clause"] for clause in clauses] == CLAUSES
    total = collections.Counter()
    rows = []
    for clause, previous in zip(clauses, baseline):
        assert [(b["function"], b["branch_pc"], b["baseline"]) for b in clause["branches"]] == [
            (b["function"], b["branch_pc"], b["baseline"]) for b in previous["branches"]]
        weights = clause["weights"]
        new = clause["new_preflight_weights"]
        row = [clause["snapshots"][TAGS[0]]["total"], weights.get("现状已无环", 0),
               weights.get("M1 后无环", 0), weights.get("HasBackEdge", 0), weights.get("NoJoin", 0),
               sum(v for k, v in weights.items() if k.startswith("ExitsRegion")), weights.get("NotJump", 0),
               new.get("可通过", 0), sum(new.values()) - new.get("可通过", 0), clause["missing_weight"]]
        assert sum(row[1:7]) + row[-1] == row[0], clause["clause"]
        assert row[2] == row[7] + row[8]
        rows.append([clause["clause"], *row])
        total.update(dict(enumerate(row)))
    rows.append(["合计", *[total[i] for i in range(10)]])
    lines = ["# 循环内分叉合并 M0 静态测量", "",
             "使用用户指定的只读 IR 和日志；只取每类最后一条快照，按入口 `function + branch_pc` 聚合拒绝次数。"
             "IR 先经 `assertions_to_jumps`，再经正式加载期 `insert_monomorphize`、`insert_primops`；"
             "使用旧运行的相同配置，不初始化架构、不执行 IR。FVFTYPE 的 execute pc28821、pc29115 均为 Jump，"
             "源码起始行分别是 983、1002。现状阶段在 M1 前单独运行，补测逐入口核对现状结果未变。", "",
             "## 加权分类", ""]
    table(lines, ["clause", "拒绝权重", "现状已无环", "M1 后新增无环", "M1 后仍有环", "NoJoin", "ExitsRegion",
                  "非 Jump", "新增无环预检过", "新增无环预检拒", "遗漏权重"], rows)
    lines += ["## 全部 M1 无环区域的预检", ""]
    table(lines, ["clause", "可通过", "callee_state_write", "其他拒绝"], [
        [c["clause"], c["preflight_weights"].get("可通过", 0), c["preflight_weights"].get("callee_state_write", 0),
         sum(v for k, v in c["preflight_weights"].items() if k not in {"可通过", "callee_state_write"})] for c in clauses])
    lines += ["## callee_state_write 细分", ""]
    evidence = collections.Counter()
    for clause in clauses:
        for branch in clause["branches"]:
            if branch.get("preflight") == "callee_state_write":
                first = branch["preflight_rejections"][0]
                assert not first["indirect_write"], "间接写入须单独说明，不能伪报全局名"
                evidence[clause["clause"], first["callee"], first["rejected_function"], first["written_global"]] += branch["count"]
    table(lines, ["clause", "区域直接调用", "实际写入函数", "被写全局", "拒绝权重"], [
        [*key, weight] for key, weight in sorted(evidence.items())])
    lines += ["## FVFTYPE 位置抽查", ""]
    fvftype = next(c for c in clauses if c["clause"] == "FVFTYPE")
    table(lines, ["入口 pc", "权重", "现状汇合点或拒绝", "M1 汇合点或拒绝", "预检"], [
        [b["branch_pc"], b["count"], b.get("baseline_join", b["baseline"]), b.get("m1_join", b["category"]),
         b.get("preflight", "未进入预检")] for b in fvftype["branches"] if b["branch_pc"] in {28821, 29115, 29081, 28721, 51364}])
    lines += ["快照权重是硬超时前的观测次数，不代表独立静态位置数或动态合并成功数。"
              "预检逐节点复用 `instruction_effect` 和 `function_effect_summaries`，表中细分采用首个拒绝证据，每个入口权重只计一次；"
              "JSON 还保留区域内全部静态拒绝证据、直接被调函数和写入位置。静态可通过不保证运行时状态兼容。"
              "M1 之后区域死臂不经过普通执行的 `assertion_filtered_paths` 计数，接受设计稿约定的统计口径变化。", "",
              "## 复现", "", "在本工作树根目录执行；所有输出与临时文件留在本工作树。", "", "```sh",
              "python3 agents/loop_region_merge/measure.py extract",
              "mkdir -p agents/loop_region_merge/tmp",
              'TMPDIR="$PWD/agents/loop_region_merge/tmp"' + ' ' + chr(92),
              'ISLA_REGIONS_IR=/data1/baiyifan/workplace/isla-runner/.worktree/pathmerge-all-20261110/isla/rv64d.ir' + ' ' + chr(92),
              'ISLA_M0_INPUT="$PWD/agents/loop_region_merge/m0-baseline.json"' + ' ' + chr(92),
              'ISLA_M0_OUTPUT="$PWD/agents/loop_region_merge/m0.json"' + ' ' + chr(92),
              "cargo test -p isla-lib regions_loop_merge_real_ir_measurement -- --ignored --nocapture",
              "python3 agents/loop_region_merge/measure.py report", "```", "",
              "首次只测现状时，输入改为 `snapshots.json`、输出改为 `m0-baseline.json`，并设置 `ISLA_M0_BASELINE_ONLY=1`。", ""]
    m2_path = DIRECTORY / "m2.json"
    if m2_path.exists():
        m2 = json.loads(m2_path.read_text())
        lines += ["## M2 后预检", "",
                  "沿用上面的同一 IR、配置、快照、入口和权重；仅打开 `region_global_state` 后重新计算静态效应摘要。"
                  "区域分类保持不变。以下数字是静态可通过权重，不代表动态合并成功数。", ""]
        reasons = sorted({reason for c in m2 for reason in c["preflight_weights"] if reason != "可通过"})
        rows = []
        totals = collections.Counter()
        for old, new in zip(clauses, m2):
            assert old["clause"] == new["clause"]
            assert old["weights"] == new["weights"]
            assert [(b["function"], b["branch_pc"], b["count"]) for b in old["branches"]] == [
                (b["function"], b["branch_pc"], b["count"]) for b in new["branches"]]
            before = old["preflight_weights"].get("可通过", 0)
            after = new["preflight_weights"].get("可通过", 0)
            rejected = sum(new["preflight_weights"].values()) - after
            row = [before, after, after - before, rejected,
                   *[new["preflight_weights"].get(reason, 0) for reason in reasons]]
            totals.update(dict(enumerate(row)))
            rows.append([new["clause"], *row])
        rows.append(["合计", *[totals[i] for i in range(4 + len(reasons))]])
        table(lines, ["clause", "M1 可通过", "M2 可通过", "新增可通过", "仍被拒", *reasons], rows)
        evidence = collections.Counter()
        for clause in m2:
            for branch in clause["branches"]:
                if branch.get("preflight") not in {None, "可通过"}:
                    first = branch["preflight_rejections"][0]
                    evidence[clause["clause"], first["reason"], first["rejected_function"],
                             first["target_pc"], first["operation"]] += branch["count"]
        lines += ["### 仍被拒的原因细分", ""]
        table(lines, ["clause", "原因", "证据函数", "pc", "原语", "权重"], [
            [*key, weight] for key, weight in sorted(evidence.items())])
        lines += ["本次仍被拒的首个证据均为 `execute` 中的 `vector_update`。"
                  "其现有效应分类为 `WritesState`，属于设计要求保持拒绝的其他写效应原语，本次不放宽。", ""]
        lines += ["M2 保留地址写、其他写效应原语和内存写的拒绝。"
                  "未实现的外部函数仍按原规则在实际到达时拒绝，不计入静态拒绝；"
                  "relaxed 寄存器、历史写入和访问顺序冲突也需运行时判定。", "",
                  "复现 M2：沿用上述测量命令，额外设置 `ISLA_M0_GLOBAL_STATE=1`，"
                  "并将 `ISLA_M0_OUTPUT` 改为 `$PWD/agents/loop_region_merge/m2.json`，随后运行 `measure.py report`。", ""]
    (DIRECTORY / "m0.md").write_text("\n".join(lines))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["extract", "report"])
    parser.add_argument("--source-root", type=Path, default=DIRECTORY.parents[2])
    arguments = parser.parse_args()
    if arguments.operation == "extract":
        extract(arguments.source_root)
    else:
        report()
