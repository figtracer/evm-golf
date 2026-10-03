# Getting started

## Requirements

- Rust and Cargo. The project uses Rust 2024 and has been tested with Rust 1.98.0.
- Lean **4.34.0**, pinned in [lean-toolchain](../lean-toolchain).
- `curl`, `tar`, and `zstd` for the local Lean installer.

Dependencies are resolved through Cargo.lock. Keep `--locked` when building or
running the tool.

## Build from source

```sh
git clone https://github.com/figtracer/evm-golf.git
cd evm-golf
bash scripts/setup-lean.sh
cargo build --locked
```

The setup script downloads an official Lean release into `.tools/lean`. It
supports macOS and Linux on x86-64 and ARM64 and leaves the global Lean setup
unchanged. Local validation uses macOS ARM64; GitHub Actions exercises the installer
and full Rust/Lean suite on Ubuntu x86-64. macOS x86-64 and Linux ARM64 have not
been validated by this project.

To use an existing installation, set `LEAN` to a Lean 4.34.0 executable. The
checker first uses `LEAN`, then the checkout-local binary, then `lean` on PATH.

The optional [internal-region checker](regions.md) has its own pinned Lean 4.22
setup. It does not replace this toolchain or the expression verifier.

## First optimization

Run commands from the repository root:

```sh
cargo run --locked -- optimize '(+ (* x 2) (- y y))' --out runs/first
```

The optimizer selects `(+ x x)`, using `DUP1` to reuse the loaded word. Lean verifies
its equivalence in the supported model, then revm checks the emitted runtime and
gas on the concrete test inputs.

| Artifact | Contents |
| --- | --- |
| `Proof.lean` | Successful proof of the generated statements |
| `Proof.log` | Lean output and theorem axiom dependencies |
| `Proof.<strategy>.lean/log` | Each attempted proof strategy and its diagnostics |
| `result.json` | Expressions, bytecode, gas and byte counts |

Output directories must be new. A failed run can leave diagnostic artifacts but
has no accepted `result.json`. Use another directory when retrying.

Recheck the saved proof:

```sh
.tools/lean/bin/lean runs/first/Proof.lean
```

## Explore

```sh
cargo run --locked -- --help
cargo run --locked -- challenges
cargo run --locked -- demo --out runs/demo-1
```

Continue with the [command reference](cli.md) and
[verification model](verification.md).
