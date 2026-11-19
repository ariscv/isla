#!/usr/bin/env bash
set -euo pipefail

root=$1
data=$2
z3_root=$3
scripts=$(cd "$(dirname "$0")" && pwd)
run=(bash "$scripts/run.sh" "$root" "$data" "$z3_root")
# 短档先原版，长档先还原版。每次只跑一个探针。
"${run[@]}" probe original LOAD 120
"${run[@]}" probe reverted LOAD 120
"${run[@]}" probe original STORE 120
"${run[@]}" probe reverted STORE 120
"${run[@]}" probe reverted LOAD 300
"${run[@]}" probe original LOAD 300
"${run[@]}" probe reverted STORE 300
"${run[@]}" probe original STORE 300
