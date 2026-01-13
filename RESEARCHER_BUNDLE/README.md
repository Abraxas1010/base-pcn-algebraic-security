# Base PCN Algebraic Security — Researcher Bundle

This is a self-contained Lean 4 project for independently verifying the formalization.

## Quick Start

```bash
# Install Lean via elan if not already installed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build the project
lake update
lake build -- -DwarningAsError=true

# Run demos
lake exe base_pcn_demo
lake exe base_pcn_evm_demo
```

## Verification

```bash
./scripts/verify_build.sh
```

## Structure

- `HeytingLean/` — Lean source files
- `lakefile.lean` — Build configuration
- `lean-toolchain` — Lean version specification
- `scripts/` — Verification scripts

See the main README in the parent directory for full documentation.
