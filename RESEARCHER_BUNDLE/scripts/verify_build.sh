#!/bin/bash
# verify_build.sh — Reproducible verification script for Base PCN Algebraic Security

set -e

echo "=== Base PCN Algebraic Security Verification ==="
echo ""

# Check Lean version
echo "Lean version:"
lean --version || { echo "ERROR: lean not found. Install via elan."; exit 1; }
echo ""

# Check Lake version
echo "Lake version:"
lake --version || { echo "ERROR: lake not found."; exit 1; }
echo ""

# Check for sorry/admit
echo "Checking for sorry/admit..."
if grep -rn --include='*.lean' -E '\bsorry\b|\badmit\b' HeytingLean/ 2>/dev/null; then
    echo "ERROR: Found sorry/admit in source files!"
    exit 1
else
    echo "No sorry/admit found."
fi
echo ""

# Update dependencies
echo "Updating lake dependencies..."
lake update
echo ""

# Build with strict flags
echo "Building with warnings as errors..."
lake build -- -DwarningAsError=true

if [ $? -eq 0 ]; then
    echo ""
    echo "Build completed successfully."
else
    echo ""
    echo "ERROR: Build failed!"
    exit 1
fi
echo ""

# Run demos
echo "Running base_pcn_demo..."
lake exe base_pcn_demo --help
echo ""

echo "Running base_pcn_evm_demo..."
lake exe base_pcn_evm_demo
echo ""

echo "=== VERIFICATION PASSED ==="
echo "All modules compile without sorry/admit."
echo "Demos run successfully."
