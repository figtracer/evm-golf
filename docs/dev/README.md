# Developer documentation

## Layout

| Path | Responsibility |
| --- | --- |
| `src/main.rs` | CLI: `inspect`, `optimize`, `verify`, plus hidden developer commands |
| `src/runtime/project.rs` | Project manifests, proposals documents and the three workflows |
| `src/runtime.rs` | Acceptance gate: rewrite selection, proof, replay, evidence |
| `src/runtime/layout.rs` | Fixed-layout analysis and built-in rewrite families |
| `src/runtime/search.rs` | Bounded search rounds and retry of failed batches |
| `src/runtime/proposal_search.rs` | Bounded discovery of stack and literal windows |
| `src/runtime/window_proposal.rs` | Symbolic window checker and generated window proofs |
| `src/runtime/artifact.rs` | Full-image Lean certificates (layout and batch) |
| `src/runtime/scenario.rs`, `calls.rs`, `precompile.rs` | Account fixtures and guarded revm replay |
| `src/runtime/region*` | Developer region certificates against upstream semantics |
| `src/runtime/whole.rs` | Developer whole-program certificates against upstream semantics |
| `src/proof.rs`, `src/proof/upstream.rs` | Pinned Lean runners and axiom audit |
| `lean/` | Model, stack, composition, layout, window and jump threading proofs |
| `lean/Gas.lean` | Local gas costs and metered execution of pure proposal windows |
| `lean/upstream/` | Upstream interpreter region and whole-program lemmas, templates |
| `examples/quickstart/` | Minimal runnable project |
| `tests/` | CLI, replay and proof regression tests |

## Checks

Install Rust (2024 edition) and run `bash scripts/setup-lean.sh` for the pinned
Lean 4.34.0 in `.tools/lean`, or set `LEAN` to an existing 4.34.0 binary. Then:

```sh
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked
cargo test --locked -- --ignored --test-threads=1
```

`bash scripts/check.sh` runs all four. Tests marked `ignore` need Lean; a plain
`cargo test` does not exercise the proof path. CI runs the same checks on Ubuntu.

The region checker has its own toolchain: `bash scripts/setup-upstream.sh`, then
`bash scripts/check-upstream.sh` and, after `setup-upstream.sh --checked-scanner`,
`bash scripts/check-checked-scanner.sh`. See [regions.md](regions.md). Its CLI
commands, `certify-runtime-region` and `certify-runtime-whole`, and the replay-only
`check-runtime` are hidden from `--help`.

## Rules for changes

- New rewrite families need a generated Lean certificate checked by the
  acceptance gate, plus guarded replay. Never relax the 60-second proof budget
  or the foundational-axiom audit.
- Validate representative full contracts when changing certificate generation;
  proof time on 24 KB images is the main performance risk.
- Keep generated proofs, corpora, benchmarks and reports out of the repository.
- The tool is unreleased; the CLI may change, but update README.md, AGENTS.md and
  docs/cli.md together.
