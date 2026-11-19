#!/usr/bin/env bash
set -euo pipefail

root=$1
data=$2
z3_root=$3
isla=$(cd "$(dirname "$0")/../.." && pwd)
commit=$4
variant=$5
out="$data/$variant"
historical="$root/agents/fuzz_strategy_20261112/exp/fullsym-timeout/iter/raw/sail-revert-20261118"
mkdir -p "$out/model-source" "$out"
git -C "$root/sail-riscv" archive "$commit" | tar -x -C "$out/model-source"
cp "$historical/rv64d_v128_e64.json" "$out/model.json"

export PATH="$z3_root/bin:$PATH"
export OCAMLPATH="$(opam var lib)"
(cd "$isla/isla-sail" && dune build --build-dir "$data/dune" --release sail_plugin_isla.cmxs) > "$data/build-plugin.log" 2>&1
plugin="$data/dune/default/sail_plugin_isla.cmxs"
cd "$out/model-source/model"
args=(sail -plugin "$plugin" -isla -D SYMBOLIC --strict-var --strict-bitvector --strict-exponentials
      --require-version 0.20.1 --memo-z3-path "$out/sail_smt_cache" --all-modules)
for fn in encdec_compressed_forwards encdec_compressed_forwards_matches encdec_compressed_backwards encdec_compressed_backwards_matches get_F set_F set_V riscv_f16ToI16 riscv_f16ToUi16 riscv_f32ToI16 riscv_f32ToUi16; do
    args+=(--isla-preserve "$fn")
done
args+=(--isla-output-dir "$out" -o rv64d --config "$out/model.json" riscv.sail_project)
{
    printf 'Sail-RISC-V %s\n' "$commit"
    git -C "$isla" rev-parse HEAD
    sail --version
    z3 --version
    dune --version
    printf 'cwd=%s\n' "$PWD"
    printf '%q ' "${args[@]}"
    printf '\n'
    sha256sum "$plugin" "$out/model.json"
} > "$out/provenance.txt"
"${args[@]}" > "$out/generation.log" 2>&1
test -s "$out/rv64d.ir"
sha256sum "$out/rv64d.ir" >> "$out/provenance.txt"
