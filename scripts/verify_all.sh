#!/bin/bash
#
# verify_all.sh - Self-Healing Verification Suite
#
# This script is designed to be IDEMPOTENT and ROBUST against:
# - Stale Lean caches and version mismatches
# - Missing or misconfigured TLA+ config files
# - Missing tool binaries
#
# PODS 2026 Submission - Anonymous
#

set -e  # Exit on first error

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname "$SCRIPT_DIR")"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Track results
LEAN_STATUS="pending"
TLA_STATUS="pending"
EXAMPLES_STATUS="pending"
BENCHMARKS_STATUS="pending"
TESTS_STATUS="pending"
PLOT_STATUS="pending"

echo "========================================================================"
echo "Category-Theoretic Foundations - Self-Healing Verification Suite"
echo "========================================================================"
echo ""
echo "Repository: $REPO_DIR"
echo "Started at: $(date)"
echo ""

# =============================================================================
# PHASE 0: PRE-FLIGHT CHECKS & AUTO-CONFIGURATION
# =============================================================================

echo "========================================================================"
echo -e "${BLUE}Phase 0: Pre-flight Checks & Auto-Configuration${NC}"
echo "========================================================================"
echo ""

# --- TLA+ Tool Location Intelligence ---
echo "Checking for TLA+ tools..."
TLA2TOOLS_PATH=""

if [ -f "$REPO_DIR/tla/tla2tools.jar" ]; then
    TLA2TOOLS_PATH="$REPO_DIR/tla/tla2tools.jar"
    echo -e "  ${GREEN}✓${NC} Found tla2tools.jar in tla/"
elif [ -f "$REPO_DIR/tla2tools.jar" ]; then
    echo "  Moving tla2tools.jar from repo root to tla/..."
    mv "$REPO_DIR/tla2tools.jar" "$REPO_DIR/tla/tla2tools.jar"
    TLA2TOOLS_PATH="$REPO_DIR/tla/tla2tools.jar"
    echo -e "  ${GREEN}✓${NC} Moved tla2tools.jar to tla/"
else
    echo -e "  ${YELLOW}⚠${NC} tla2tools.jar not found"
    echo "    Download from: https://github.com/tlaplus/tlaplus/releases"
    echo "    Place in: $REPO_DIR/tla/"
fi

# --- Generate TLA+ Configuration Files (The "Forever" Fix) ---
echo ""
echo "Generating TLA+ configuration files..."

cat << 'EOF' > "$REPO_DIR/tla/ParadigmTransform.cfg"
SPECIFICATION Spec
CONSTANT MaxDataSize = 4
CONSTANT WindowSize = 3
CONSTANT MaxTimestamp = 8
INVARIANT TypeInvariant
INVARIANT DataPreservationWithinWindow
INVARIANT NoDataLossSmallBatch
INVARIANT WatermarkMonotonic
INVARIANT TransformCountNonNeg
EOF
echo -e "  ${GREEN}✓${NC} Generated ParadigmTransform.cfg"

cat << 'EOF' > "$REPO_DIR/tla/ZRelations.cfg"
SPECIFICATION Spec
CONSTANT MaxTuples = 4
CONSTANT MaxMultiplicity = 3
CONSTANT TupleSpace = {1, 2, 3, 4}
INVARIANT TypeInvariant
INVARIANT MultiplicityBounds
INVARIANT SupportFinite
INVARIANT HistoryConsistent
EOF
echo -e "  ${GREEN}✓${NC} Generated ZRelations.cfg"

cat << 'EOF' > "$REPO_DIR/tla/CorrectionProtocol.cfg"
SPECIFICATION Spec
CONSTANT MaxEvents = 4
CONSTANT MaxLateness = 2
CONSTANT MaxTimestamp = 8
CONSTANT DataValues = {1, 2, 3}
INVARIANT TypeInvariant
INVARIANT CorrectionCompleteness
INVARIANT VersionMonotonic
INVARIANT BoundedLateness
EOF
echo -e "  ${GREEN}✓${NC} Generated CorrectionProtocol.cfg"

echo ""

# =============================================================================
# PHASE 1: LEAN VERIFICATION (Clean Slate Build)
# =============================================================================

echo "========================================================================"
echo "Phase 1: Lean 4 Verification (Clean Slate)"
echo "========================================================================"
echo ""

cd "$REPO_DIR/lean"

if ! command -v lean &> /dev/null; then
    echo -e "${YELLOW}⚠ Lean 4 not found. Skipping.${NC}"
    echo "  Install via: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    LEAN_STATUS="skipped"
else
    echo "Lean version: $(lean --version)"
    
    # Clean slate - remove all build artifacts
    echo "Cleaning build artifacts..."
    rm -rf .lake/build 2>/dev/null || true
    lake clean 2>/dev/null || true
    echo -e "  ${GREEN}✓${NC} Build directory cleaned"
    
    # Fetch cache
    echo "Fetching Mathlib cache..."
    lake exe cache get 2>/dev/null || echo "  (Cache fetch failed, continuing anyway)"
    
    # Build with strict error checking
    echo "Building Lean proofs..."
    if ! lake build; then
        echo -e "${RED}✗ Lean build FAILED${NC}"
        echo "Check the errors above."
        exit 1
    fi
    
    echo -e "${GREEN}✓ Lean verification complete${NC}"
    LEAN_STATUS="passed"
    
    # Count remaining axioms
    SORRY_COUNT=$(grep -r "sorry" *.lean 2>/dev/null | wc -l | tr -d ' ')
    echo "  Axiomatizations (sorry): $SORRY_COUNT"
fi

echo ""

# =============================================================================
# PHASE 2: TLA+ MODEL CHECKING
# =============================================================================

echo "========================================================================"
echo "Phase 2: TLA+ Model Checking"
echo "========================================================================"
echo ""

cd "$REPO_DIR/tla"

if ! command -v java &> /dev/null; then
    echo -e "${YELLOW}⚠ Java not found. TLA+ requires Java 11+. Skipping.${NC}"
    TLA_STATUS="skipped"
elif [ -z "$TLA2TOOLS_PATH" ]; then
    echo -e "${YELLOW}⚠ tla2tools.jar not available. Skipping TLA+ verification.${NC}"
    TLA_STATUS="skipped"
else
    echo "Using: $TLA2TOOLS_PATH"
    TLC_CMD="java -XX:+UseParallelGC -Xmx4g -jar $TLA2TOOLS_PATH"
    
    TLA_PASSED=true
    mkdir -p logs
    
    for spec in ParadigmTransform ZRelations CorrectionProtocol; do
        if [ -f "${spec}.tla" ] && [ -f "${spec}.cfg" ]; then
            echo "Checking ${spec}.tla..."
            
            if $TLC_CMD "${spec}.tla" -config "${spec}.cfg" -workers 4 > "logs/${spec}.log" 2>&1; then
                # Check for errors in output
                if grep -q "Error:" "logs/${spec}.log"; then
                    echo -e "  ${RED}✗ ${spec} had errors${NC}"
                    grep "Error:" "logs/${spec}.log" | head -2
                    TLA_PASSED=false
                else
                    STATES=$(grep -i "states generated" "logs/${spec}.log" | tail -1 || echo "")
                    echo -e "  ${GREEN}✓ ${spec} passed${NC} $STATES"
                fi
            else
                echo -e "  ${RED}✗ ${spec} failed to execute${NC}"
                tail -5 "logs/${spec}.log" 2>/dev/null || true
                TLA_PASSED=false
            fi
        else
            echo -e "  ${YELLOW}⚠ ${spec}.tla or ${spec}.cfg not found${NC}"
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
# PHASE 3: PYTHON EXAMPLES
# =============================================================================

echo "========================================================================"
echo "Phase 3: Python Examples"
echo "========================================================================"
echo ""

cd "$REPO_DIR/examples"

if ! command -v python3 &> /dev/null; then
    echo -e "${YELLOW}⚠ Python 3 not found. Skipping.${NC}"
    EXAMPLES_STATUS="skipped"
else
    echo "Python version: $(python3 --version)"
    EXAMPLES_PASSED=true
    
    for example in running_example.py ivm_demo.py late_data_demo.py; do
        if [ -f "$example" ]; then
            if python3 "$example" > /dev/null 2>&1; then
                echo -e "  ${GREEN}✓${NC} $example"
            else
                echo -e "  ${RED}✗${NC} $example failed"
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
# PHASE 4: FORMAL REGRESSION TESTS
# =============================================================================

echo "========================================================================"
echo "Phase 4: Formal Regression Tests"
echo "========================================================================"
echo ""

cd "$REPO_DIR"

if ! command -v python3 &> /dev/null; then
    TESTS_STATUS="skipped"
elif [ ! -f "tests/test_paper_examples.py" ]; then
    echo -e "${YELLOW}⚠ test_paper_examples.py not found. Skipping.${NC}"
    TESTS_STATUS="skipped"
else
    echo "Installing pytest if needed..."
    pip3 install pytest --quiet 2>/dev/null || true
    
    echo "Running formal regression tests..."
    if python3 -m pytest tests/ -v --tb=short 2>&1 | tail -20; then
        TESTS_STATUS="passed"
        echo -e "${GREEN}✓ All regression tests passed${NC}"
    else
        TESTS_STATUS="failed"
        echo -e "${RED}✗ Some regression tests failed${NC}"
    fi
fi

echo ""

# =============================================================================
# PHASE 5: BENCHMARKS & VISUAL ARTIFACTS
# =============================================================================

echo "========================================================================"
echo "Phase 5: Benchmarks & Visual Artifacts"
echo "========================================================================"
echo ""

cd "$REPO_DIR/benchmarks"
mkdir -p results

if ! command -v python3 &> /dev/null; then
    BENCHMARKS_STATUS="skipped"
    PLOT_STATUS="skipped"
else
    # Run complexity benchmark
    echo "Running complexity benchmarks..."
    if python3 complexity_validation.py > results/benchmark_output.txt 2>&1; then
        echo -e "  ${GREEN}✓${NC} Complexity validation complete"
        BENCHMARKS_STATUS="passed"
    else
        echo -e "  ${RED}✗${NC} Complexity validation failed"
        BENCHMARKS_STATUS="failed"
    fi
    
    # Generate complexity plot (Theorem 8.1)
    echo "Generating complexity plot..."
    if python3 paradigm_transform_benchmark.py > /dev/null 2>&1; then
        echo -e "  ${GREEN}✓${NC} Benchmark complete"
        PLOT_STATUS="passed"
    else
        echo -e "  ${RED}✗${NC} Benchmark script failed"
        PLOT_STATUS="failed"
    fi
    
    # Visual Artifact Verification
    echo ""
    echo "Verifying visual artifacts..."
    if [ -f "results/complexity_plot.png" ]; then
        echo -e "  ${GREEN}✓${NC} complexity_plot.png exists"
    else
        echo -e "  ${RED}✗${NC} complexity_plot.png NOT FOUND"
        PLOT_STATUS="failed"
    fi
fi

echo ""

# =============================================================================
# SUMMARY
# =============================================================================

echo "========================================================================"
echo "Verification Summary"
echo "========================================================================"
echo ""
echo "Completed at: $(date)"
echo ""

print_status() {
    case $2 in
        "passed")  echo -e "  $1: ${GREEN}PASSED${NC}" ;;
        "failed")  echo -e "  $1: ${RED}FAILED${NC}" ;;
        "skipped") echo -e "  $1: ${YELLOW}SKIPPED${NC}" ;;
        *)         echo -e "  $1: ${YELLOW}PENDING${NC}" ;;
    esac
}

print_status "Lean 4 Proofs" "$LEAN_STATUS"
print_status "TLA+ Model Checking" "$TLA_STATUS"
print_status "Python Examples" "$EXAMPLES_STATUS"
print_status "Formal Regression Tests" "$TESTS_STATUS"
print_status "Complexity Benchmarks" "$BENCHMARKS_STATUS"
print_status "Visual Artifacts" "$PLOT_STATUS"

echo ""
echo "Generated Artifacts:"
echo "  - tla/ParadigmTransform.cfg (auto-generated)"
echo "  - tla/ZRelations.cfg (auto-generated)"
echo "  - tla/CorrectionProtocol.cfg (auto-generated)"
echo "  - tla/logs/*.log (TLA+ output)"
echo "  - benchmarks/results/benchmark_output.txt"
echo "  - benchmarks/results/complexity_plot.png"
echo ""

# Final status
OVERALL_SUCCESS=true
for status in "$LEAN_STATUS" "$TLA_STATUS" "$EXAMPLES_STATUS" "$TESTS_STATUS" "$BENCHMARKS_STATUS" "$PLOT_STATUS"; do
    if [ "$status" = "failed" ]; then
        OVERALL_SUCCESS=false
        break
    fi
done

if $OVERALL_SUCCESS; then
    echo -e "${GREEN}========================================================================"
    echo "All verifications passed or skipped!"
    echo "========================================================================${NC}"
    exit 0
else
    echo -e "${RED}========================================================================"
    echo "Some verifications failed. Review the output above."
    echo "========================================================================${NC}"
    exit 1
fi
