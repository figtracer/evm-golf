#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked
# Avoid competing Lean processes consuming each other's wall-clock budgets.
cargo test --locked -- --ignored --test-threads=1
