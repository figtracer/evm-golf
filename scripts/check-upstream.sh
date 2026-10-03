#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
bash scripts/setup-upstream.sh --check

# Test the real CLI and kernel path, keeping every generated artifact outside git.
work="$(mktemp -d "${TMPDIR:-/tmp}/evm-golf-region.XXXXXX")"
printf '%s\n' 60200201905f808061123456 > "$work/original.hex"
printf '%s\n' 60051b01905f808061123456 > "$work/candidate.hex"
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/original.hex" --candidate "$work/candidate.hex" \
  --entry-pc 0 --out "$work/accepted"; then
  cat "$work/accepted"/*.log 2>/dev/null || true
  echo "Failed certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/accepted/result.json" <<'PY'
import json
import sys

with open(sys.argv[1]) as handle:
    report = json.load(handle)
assert report["entry_pc"] == 0 and report["exit_pc"] == 11
assert report["pushed_destination"] == 0x1234
assert report["source_gas_minimum"] == 25
assert report["gas_surplus_increase"] == 2
assert report["maximum_tail_length"] == 1018
assert "whole-contract equivalence" in report["unproved"]
PY
printf '%s\n' 60061b01905f808061123456 > "$work/wrong.hex"
if cargo run --locked -- certify-runtime-region \
  --original "$work/original.hex" --candidate "$work/wrong.hex" \
  --entry-pc 0 --out "$work/rejected"; then
  echo 'Incorrect candidate was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/rejected/result.json" ]]
echo "Upstream region checks passed. Local evidence: $work"
