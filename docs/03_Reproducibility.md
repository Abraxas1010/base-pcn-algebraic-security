# Reproducibility Guide

This document provides instructions for independently verifying the formalization.

## Environment Setup

### 1. Install elan (Lean Version Manager)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile  # or restart terminal
```

### 2. Verify Installation

```bash
elan --version
# Expected: elan 3.x.x

lean --version
# Expected: Lean (version 4.14.0, ...)
```

## Verification Steps

### Quick Verification

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_build.sh
```

This script:
1. Checks for `sorry`/`admit` in source files
2. Updates Lake dependencies
3. Builds with `-DwarningAsError=true`

### Manual Verification

```bash
cd RESEARCHER_BUNDLE

# Update dependencies (downloads Mathlib cache)
lake update

# Build with warnings as errors
lake build -- -DwarningAsError=true

# Check for sorry/admit (should return nothing)
grep -rn --include='*.lean' -E '\bsorry\b|\badmit\b' HeytingLean/

# Run demos
lake exe base_pcn_demo
lake exe base_pcn_evm_demo
```

### Expected Demo Output

```
Extracted Address-graph edges.card = 3
cap(1,2) = 10
cap(2,3) = 5
cap(3,1) = 8
toy wealth: A=12, B=5, C=6
wgBool(toy wealth) = true
paymentFeasibleBool A→B a=2 = true
after splice(1,2,newCap=12): cap(1,2) = 12
parallel channels demo: edges.card=1
capMax(1,2) = 10
capSum(1,2) = 17
```

## Dependency Versions

| Component | Version | Source |
|-----------|---------|--------|
| Lean | 4.14.0 | `lean-toolchain` |
| Mathlib | v4.14.0 | `lakefile.lean` |
| Lake | (bundled) | — |

## Troubleshooting

### "lake: command not found"

Ensure elan is in your PATH:
```bash
export PATH="$HOME/.elan/bin:$PATH"
```

### Slow build

First build downloads ~300MB of Mathlib cache. Subsequent builds are faster.

### Memory issues

Mathlib compilation can require 8GB+ RAM. Close other applications or use:
```bash
lake build -j1  # Single-threaded build
```

## Verification Checklist

- [ ] `lean --version` shows 4.14.0
- [ ] `lake update` completes without error
- [ ] `lake build -- -DwarningAsError=true` succeeds
- [ ] `grep sorry` finds no matches
- [ ] `grep admit` finds no matches
- [ ] `lake exe base_pcn_demo` runs successfully
- [ ] `lake exe base_pcn_evm_demo` runs successfully

## Axiom Verification

To verify no unexpected axioms are used:

```lean
#print axioms HeytingLean.Blockchain.PaymentChannels.Cuts.mem_WG_iff_forall_cutIntervalHolds
```

Expected output:
```
'HeytingLean.Blockchain.PaymentChannels.Cuts.mem_WG_iff_forall_cutIntervalHolds'
  depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

These are Lean's standard axioms, not custom additions.
