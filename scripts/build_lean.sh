#!/bin/bash
#
# build_lean.sh - Build Lean 4 proofs
#
# PODS 2026 Submission - Anonymous
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_DIR="$(dirname "$SCRIPT_DIR")/lean"

cd "$LEAN_DIR"

echo "Building Lean 4 proofs..."
echo "Directory: $LEAN_DIR"
echo ""

# Check for Lean
if ! command -v lean &> /dev/null; then
    echo "Error: Lean not found. Install via:"
    echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    exit 1
fi

echo "Lean version: $(lean --version)"
echo ""

# Fetch cache if available
echo "Fetching Mathlib cache..."
lake exe cache get || echo "Cache not available (building from source)"
echo ""

# Build
echo "Building..."
lake build "$@"

echo ""
echo "Build complete!"

# Report on axiomatizations
echo ""
echo "Axiomatization check:"
grep -r "sorry" *.lean | head -10 || echo "No axiomatizations found"
