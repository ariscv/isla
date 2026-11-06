"""汇总 count 模式的分区计数快照；可行解计数为下界，完成后才声称精确。"""
import json


class CountMeasurement:
    def __init__(self):
        self.paths = {}

    def observe(self, entry):
        signature = str(entry["path_signature"])
        phase = entry["phase"]
        if phase == "started":
            assert signature not in self.paths, "同一完成路径不得重复开始测量"
            self.paths[signature] = dict(partitions=entry["partitions"], progress={}, final=None)
            return
        path = self.paths[signature]
        assert path["final"] is None, "已完成路径不得继续更新"
        if phase in ("progress", "partition_complete"):
            partition = entry["partition_id"]
            assert 0 <= partition < path["partitions"]
            previous = path["progress"].get(partition)
            if previous is not None:
                assert entry["counted_paths"] >= previous["counted_paths"], "分区解数不得倒退"
                assert entry["counted_classes"] >= previous["counted_classes"], "分区类数不得倒退"
            path["progress"][partition] = entry.copy()
        else:
            assert phase == "complete"
            assert not entry["path_truncated"] and entry["truncated_classes"] == 0, "受限计数不能声称全部展开"
            assert entry["counted_paths"] >= sum(row["counted_paths"] for row in path["progress"].values())
            path["final"] = entry.copy()

    def report(self):
        rows = []
        for signature, path in self.paths.items():
            final = path["final"]
            rows.append(dict(path_signature=signature, complete=final is not None,
                             counted_classes=final["counted_classes"] if final else
                             sum(row["counted_classes"] for row in path["progress"].values()),
                             lower_bound=final["counted_paths"] if final else
                             sum(row["counted_paths"] for row in path["progress"].values())))
        completed = sum(row["complete"] for row in rows)
        return dict(lower_bound=sum(row["lower_bound"] for row in rows), started_paths=len(rows),
                    completed_paths=completed, complete=bool(rows) and completed == len(rows), paths=rows)


def read_measurement(path):
    measurement = CountMeasurement()
    with open(path) as source:
        for line in source:
            if not line.endswith("\n"):
                break
            if line.startswith("[MERGE_ENUMERATION_MEASURE] "):
                measurement.observe(json.loads(line.split(" ", 1)[1]))
    return measurement.report()
