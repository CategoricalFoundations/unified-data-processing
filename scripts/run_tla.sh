#!/bin/bash
#
# run_tla.sh - Run TLA+ model checking with JSON summary output
#
# PODS 2026 Submission - Anonymous
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TLA_DIR="$(dirname "$SCRIPT_DIR")/tla"
OUTPUT_JSON="$TLA_DIR/verification_summary.json"

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

# Initialize JSON summary
init_json() {
    cat > "$OUTPUT_JSON" << 'EOF'
{
  "verification_run": {
    "timestamp": "TIMESTAMP_PLACEHOLDER",
    "tlc_version": "TLC_VERSION_PLACEHOLDER"
  },
  "specifications": []
}
EOF
    # Replace timestamp
    local timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    if [[ "$OSTYPE" == "darwin"* ]]; then
        sed -i '' "s/TIMESTAMP_PLACEHOLDER/$timestamp/" "$OUTPUT_JSON"
    else
        sed -i "s/TIMESTAMP_PLACEHOLDER/$timestamp/" "$OUTPUT_JSON"
    fi
}

# Parse TLC output and extract statistics
parse_tlc_output() {
    local output="$1"
    local spec_name="$2"
    
    # Extract distinct states
    local distinct_states=$(echo "$output" | grep -oE '[0-9,]+ distinct states found' | grep -oE '[0-9,]+' | head -1 | tr -d ',')
    if [ -z "$distinct_states" ]; then
        distinct_states="0"
    fi
    
    # Check for errors
    local no_error="false"
    if echo "$output" | grep -qE "(No error|Model checking completed|0 errors)"; then
        no_error="true"
    fi
    if echo "$output" | grep -qE "(Error:|Invariant .* is violated|Deadlock)"; then
        no_error="false"
    fi
    
    # Extract total states
    local total_states=$(echo "$output" | grep -oE '[0-9,]+ states generated' | grep -oE '[0-9,]+' | head -1 | tr -d ',')
    if [ -z "$total_states" ]; then
        total_states="0"
    fi
    
    # Extract depth
    local depth=$(echo "$output" | grep -oE 'depth [0-9]+|Depth = [0-9]+' | grep -oE '[0-9]+' | head -1)
    if [ -z "$depth" ]; then
        depth="0"
    fi
    
    echo "{\"spec\": \"$spec_name\", \"distinct_states\": $distinct_states, \"total_states\": $total_states, \"depth\": $depth, \"no_error_found\": $no_error}"
}

# Add result to JSON summary
add_to_json() {
    local result="$1"
    local temp_file=$(mktemp)
    
    # Use jq if available, otherwise use sed
    if command -v jq &> /dev/null; then
        jq ".specifications += [$result]" "$OUTPUT_JSON" > "$temp_file" && mv "$temp_file" "$OUTPUT_JSON"
    else
        # Fallback: simple sed-based append
        if [[ "$OSTYPE" == "darwin"* ]]; then
            sed -i '' "s/\"specifications\": \[/\"specifications\": [$result,/" "$OUTPUT_JSON"
            sed -i '' 's/,]/]/' "$OUTPUT_JSON"
        else
            sed -i "s/\"specifications\": \[/\"specifications\": [$result,/" "$OUTPUT_JSON"
            sed -i 's/,]/]/' "$OUTPUT_JSON"
        fi
    fi
}

# Run specifications
run_spec() {
    local spec=$1
    local cfg_file="${spec%.tla}.cfg"
    
    echo "========================================"
    echo "Checking: $spec with $cfg_file"
    echo "========================================"
    
    local output=""
    local exit_code=0
    
    if [ -f "$cfg_file" ]; then
        output=$($TLC_CMD "$spec" -config "$cfg_file" -workers 4 2>&1) || exit_code=$?
    else
        echo "Warning: $cfg_file not found, falling back to MC.cfg"
        output=$($TLC_CMD "$spec" -config MC.cfg -workers 4 2>&1) || exit_code=$?
    fi
    
    echo "$output"
    echo ""
    
    # Parse and add to JSON
    local result=$(parse_tlc_output "$output" "$spec")
    add_to_json "$result"
    
    return $exit_code
}

# Generate final summary
generate_summary() {
    echo ""
    echo "========================================"
    echo "VERIFICATION SUMMARY"
    echo "========================================"
    
    if command -v jq &> /dev/null; then
        local total_specs=$(jq '.specifications | length' "$OUTPUT_JSON")
        local passed=$(jq '[.specifications[] | select(.no_error_found == true)] | length' "$OUTPUT_JSON")
        local total_states=$(jq '[.specifications[].distinct_states] | add' "$OUTPUT_JSON")
        
        echo "Specifications checked: $total_specs"
        echo "Passed: $passed / $total_specs"
        echo "Total distinct states: $total_states"
    else
        echo "Results saved to: $OUTPUT_JSON"
    fi
    
    echo ""
    echo "JSON summary: $OUTPUT_JSON"
    cat "$OUTPUT_JSON"
}

# Initialize JSON output
init_json

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
            run_spec "$spec" || true  # Continue on error to collect all results
        done
    fi
fi

generate_summary

echo ""
echo "Model checking complete!"
