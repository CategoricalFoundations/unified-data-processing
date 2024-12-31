#!/bin/bash
#
# run_tla.sh - Run TLA+ model checking
#
# PODS 2026 Submission - Anonymous
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TLA_DIR="$(dirname "$SCRIPT_DIR")/tla"

cd "$TLA_DIR"

echo "Running TLA+ model checking..."
echo "Directory: $TLA_DIR"
echo ""

# Determine TLC command
TLC_CMD=""
if command -v tlc &> /dev/null; then
    TLC_CMD="tlc"
elif [ -f "tla2tools.jar" ]; then
    TLC_CMD="java -XX:+UseParallelGC -Xmx8g -jar tla2tools.jar"
else
    echo "Error: TLC not found."
    echo "Either:"
    echo "  1. Install TLA+ Toolbox and ensure 'tlc' is in PATH"
    echo "  2. Download tla2tools.jar to this directory"
    exit 1
fi

echo "Using: $TLC_CMD"
echo ""

# Parse arguments
PARALLEL=false
SPEC=""

while [[ $# -gt 0 ]]; do
    case $1 in
        --parallel)
            PARALLEL=true
            shift
            ;;
        *)
            SPEC="$1"
            shift
            ;;
    esac
done

# Run specifications
run_spec() {
    local spec=$1
    # Derive config file from spec name (e.g., ParadigmTransform.tla -> ParadigmTransform.cfg)
    local cfg_file="${spec%.tla}.cfg"
    
    echo "========================================"
    echo "Checking: $spec with $cfg_file"
    echo "========================================"
    
    if [ -f "$cfg_file" ]; then
        $TLC_CMD "$spec" -config "$cfg_file" -workers 4
    else
        echo "Warning: $cfg_file not found, falling back to MC.cfg"
        $TLC_CMD "$spec" -config MC.cfg -workers 4
    fi
    
    echo ""
}

if [ -n "$SPEC" ]; then
    # Run single specification
    run_spec "$SPEC"
else
    # Run all specifications
    SPECS=(ParadigmTransform.tla ZRelations.tla CorrectionProtocol.tla)
    
    if $PARALLEL; then
        echo "Running specifications in parallel..."
        for spec in "${SPECS[@]}"; do
            run_spec "$spec" &
        done
        wait
    else
        echo "Running specifications sequentially..."
        for spec in "${SPECS[@]}"; do
            run_spec "$spec"
        done
    fi
fi

echo "Model checking complete!"
