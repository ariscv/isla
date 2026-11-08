#!/usr/bin/env python3
"""复用既有分页覆盖的字段桶；类身份由 Rust 的实际判定结果补入。"""
import json
import os
from pathlib import Path
import sys

sys.path.insert(0, os.environ.get('DIFFTEST_XIANGSHAN_DIR',
    '/data1/baiyifan/workplace/isla-runner/.worktree/replay-p0/difftest-xiangshan'))
import paging_fuzz as fuzz
import paging_replay as replay


def extract(sample, decoder):
    coverage = fuzz.Coverage()
    coverage.observe(decoder.decode_sample(sample, decoder.Config(False, False, False)))
    buckets = sorted({json.dumps([level, field, value], separators=(',', ':'))
                      for shape, level, field, value in coverage.keys})
    # 沿用 PTE 字段位宽；PPN 的九个区域来自既有 ppn_bucket。
    widths = dict(RSW=4, RSW_60t59b=4, PBMT=4, reserved=32, PPN=9)
    potential = sum(widths.get(field, 2) for level, field in
                    {(level, field) for shape, level, field, value in coverage.keys})
    return dict(buckets=buckets, potential=potential)


def main():
    decoder, provenance = replay.load_decoder(os.environ.get('PT_DECODE_DIR',
        '/data1/baiyifan/workplace/isla-runner/.worktree/isla-enumerate/agents/path_merge_call_support/pt_decode'),
        standard_paging=True)
    samples = [json.loads(line) for line in Path(sys.argv[1]).read_text().splitlines()]
    features = [extract(sample, decoder) for sample in samples]
    Path(sys.argv[2]).write_text(json.dumps(features, ensure_ascii=False, separators=(',', ':')) + '\n')


if __name__ == '__main__':
    main()
