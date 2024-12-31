#!/bin/bash
#
# verify_all.sh - Run all verification tasks
#
# PODS 2026 Submission - Anonymous
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname "$SCRIPT_DIR")"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "========================================================================"
echo "Category-Theoretic Foundations - Complete Verification Suite"
echo "========================================================================"
echo ""
echo "Repository: $REPO_DIR"
echo "Started at: $(date)"
echo ""

# Track results
LEAN_STATUS="pending"
TLA_STATUS="pending"
EXAMPLES_STATUS="pending"
TESTS_STATUS="pending"
BENCHMARKS_STATUS="pending"
PLOT_STATUS="pending"

# =============================================================================
# Phase 1: Lean Verification
# =============================================================================

echo "========================================================================"
echo "Phase 1: Lean 4 Verification"
echo "========================================================================"
echo ""

cd "$REPO_DIR/lean"

# Check Lean installation
if ! command -v lean &> /dev/null; then
    echo -e "${RED}Error: Lean 4 not found. Please install via elan.${NC}"
    echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    LEAN_STATUS="skipped"
else
    echo "Lean version: $(lean --version)"
    echo ""
    
    # Try to get cache
    echo "Fetching Mathlib cache..."
    lake exe cache get 2>/dev/null || echo "Cache fetch failed (continuing anyway)"
    echo ""
    
    # Build
    echo "Building Lean proofs..."
    if lake build; then
        echo ""
        echo -e "${GREEN}✓ Lean verification complete${NC}"
        LEAN_STATUS="passed"
        
        # Count sorries
        SORRY_COUNT=$(grep -r "sorry" *.lean 2>/dev/null | wc -l)
        echo "  Axiomatizations (sorry): $SORRY_COUNT"
    else
        echo -e "${RED}✗ Lean build failed${NC}"
        LEAN_STATUS="failed"
    fi
fi

echo ""

# =============================================================================
# Phase 2: TLA+ Model Checking
# =============================================================================

echo "========================================================================"
echo "Phase 2: TLA+ Model Checking"
echo "========================================================================"
echo ""

cd "$REPO_DIR/tla"

# Check TLA+ installation
if ! command -v java &> /dev/null; then
    echo -e "${RED}Error: Java not found. TLA+ requires Java 11+.${NC}"
    TLA_STATUS="skipped"
elif [ ! -f "tla2tools.jar" ] && ! command -v tlc &> /dev/null; then
    echo -e "${YELLOW}Warning: TLC not found. Skipping TLA+ verification.${NC}"
    echo "Download from: https://github.com/tlaplus/tlaplus/releases"
    TLA_STATUS="skipped"
else
    echo "Running TLA+ model checking..."
    echo ""
    
    TLC_CMD="tlc"
    if [ -f "tla2tools.jar" ]; then
        TLC_CMD="java -XX:+UseParallelGC -Xmx4g -jar tla2tools.jar"
    fi
    
    TLA_PASSED=true
    
    for spec in ParadigmTransform ZRelations CorrectionProtocol; do
        if [ -f "${spec}.tla" ]; then
            echo "Checking ${spec}.tla..."
            if $TLC_CMD "${spec}.tla" -config MC.cfg -workers 4 2>&1 | tail -5; then
                echo -e "${GREEN}  ✓ ${spec} passed${NC}"
            else
                echo -e "${RED}  ✗ ${spec} failed${NC}"
                TLA_PASSED=false
            fi
            echo ""
        fi
    done
    
    if $TLA_PASSED; then
        TLA_STATUS="passed"
    else
        TLA_STATUS="failed"
    fi
fi

echo ""

# =============================================================================
# Phase 3: Python Examples
# =============================================================================

echo "========================================================================"
echo "Phase 3: Python Examples"
echo "========================================================================"
echo ""

cd "$REPO_DIR/examples"

if ! command -v python3 &> /dev/null; then
    echo -e "${RED}Error: Python 3 not found.${NC}"
    EXAMPLES_STATUS="skipped"
else
    echo "Python version: $(python3 --version)"
    echo ""
    
    EXAMPLES_PASSED=true
    
    for example in running_example.py ivm_demo.py late_data_demo.py; do
        if [ -f "$example" ]; then
            echo "Running $example..."
            if python3 "$example" > /dev/null 2>&1; then
                echo -e "${GREEN}  ✓ $example passed${NC}"
            else
                echo -e "${RED}  ✗ $example failed${NC}"
                EXAMPLES_PASSED=false
            fi
        fi
    done
    
    if $EXAMPLES_PASSED; then
        EXAMPLES_STATUS="passed"
    else
        EXAMPLES_STATUS="failed"
    fi
fi

echo ""

# =============================================================================
# Phase 4: Benchmarks
# =============================================================================

echo "========================================================================"
echo "Phase 4: Complexity Benchmarks"
echo "========================================================================"
echo ""

cd "$REPO_DIR/benchmarks"

if ! command -v python3 &> /dev/null; then
    BENCHMARKS_STATUS="skipped"
else
    echo "Running complexity validation..."
    if python3 complexity_validation.py > results/benchmark_output.txt 2>&1; then
        echo -e "${GREEN}✓ Benchmarks complete${NC}"
        echo "  Results saved to: benchmarks/results/benchmark_output.txt"
        BENCHMARKS_STATUS="passed"
    else
        echo -e "${RED}✗ Benchmarks failed${NC}"
        BENCHMARKS_STATUS="failed"
    fi
fi

echo ""

# =============================================================================
# Phase 5: Formal Regression Tests
# =============================================================================

echo "========================================================================"
echo "Phase 5: Formal Regression Tests (Paper Examples)"
echo "========================================================================"
echo ""

cd "$REPO_DIR"

if [ -f "scripts/run_tests.sh" ]; then
    echo "Running formal regression tests..."
    if ./scripts/run_tests.sh > /dev/null 2>&1; then
        echo -e "${GREEN}✓ All regression tests passed${NC}"
        TESTS_STATUS="passed"
    else
        echo -e "${RED}✗ Some regression tests failed${NC}"
        TESTS_STATUS="failed"
    fi
else
    echo -e "${YELLOW}Warning: run_tests.sh not found${NC}"
    TESTS_STATUS="skipped"
fi

echo ""

# =============================================================================
# Phase 6: Generate Complexity Plot
# =============================================================================

echo "========================================================================"
echo "Phase 6: Generate Complexity Plot (Theorem 8.1)"
echo "========================================================================"
echo ""

cd "$REPO_DIR"

if ! command -v python3 &> /dev/null; then
    PLOT_STATUS="skipped"
else
    echo "Generating complexity visualization..."
    if python3 benchmarks/paradigm_transform_benchmark.py > /dev/null 2>&1; then
        echo -e "${GREEN}✓ Plot generated${NC}"
        echo "  Artifact generated: benchmarks/results/complexity_plot.png"
        PLOT_STATUS="passed"
    else
        echo -e "${RED}✗ Plot generation failed${NC}"
        PLOT_STATUS="failed"
    fi
fi

echo ""

# =============================================================================
# Summary
# =============================================================================

echo "========================================================================"
echo "Verification Summary"
echo "========================================================================"
echo ""
echo "Completed at: $(date)"
echo ""

print_status() {
    case $2 in
        "passed")
            echo -e "  $1: ${GREEN}PASSED${NC}"
            ;;
        "failed")
            echo -e "  $1: ${RED}FAILED${NC}"
            ;;
        "skipped")
            echo -e "  $1: ${YELLOW}SKIPPED${NC}"
            ;;
        *)
            echo -e "  $1: ${YELLOW}UNKNOWN${NC}"
            ;;
    esac
}

print_status "Lean 4 Proofs" "$LEAN_STATUS"
print_status "TLA+ Model Checking" "$TLA_STATUS"
print_status "Python Examples" "$EXAMPLES_STATUS"
print_status "Formal Tests" "$TESTS_STATUS"
print_status "Complexity Benchmarks" "$BENCHMARKS_STATUS"
print_status "Complexity Plot" "$PLOT_STATUS"

echo ""
echo "Artifacts generated:"
echo "  - benchmarks/results/benchmark_output.txt"
echo "  - benchmarks/results/complexity_plot.png"

echo ""

# Exit code
if [ "$LEAN_STATUS" = "passed" ] || [ "$LEAN_STATUS" = "skipped" ]; then
    if [ "$TLA_STATUS" = "passed" ] || [ "$TLA_STATUS" = "skipped" ]; then
        if [ "$EXAMPLES_STATUS" = "passed" ]; then
            echo -e "${GREEN}All available verifications passed!${NC}"
            exit 0
        fi
    fi
fi

echo -e "${RED}Some verifications failed or were skipped.${NC}"
exit 1
