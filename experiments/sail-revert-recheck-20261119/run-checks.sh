#!/usr/bin/env bash
set -euo pipefail

root=$1
data=$2
z3_root=$3
scripts=$(cd "$(dirname "$0")" && pwd)
for clause in LOAD STORE AMO VVTYPE VLSEGTYPE; do
    for variant in original reverted; do
        bash "$scripts/run.sh" "$root" "$data" "$z3_root" check "$variant" "$clause"
    done
done
