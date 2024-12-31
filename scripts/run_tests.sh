#!/bin/bash
#
# run_tests.sh - Run pytest test suite for paper examples
#
# This script installs pytest if needed and runs the formal regression tests
# that verify the exact values claimed in the paper.
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

echo "========================================"
echo "PODS 2026 Artifact - Test Suite"
echo "========================================"
echo ""

cd "$REPO_DIR"

# Check Python is available
if ! command -v python3 &> /dev/null; then
    echo -e "${RED}Error: Python 3 not found${NC}"
    echo "Please install Python 3.10 or later"
    exit 1
fi

echo "Python version: $(python3 --version)"
echo ""

# Install pytest if not available
echo "Checking pytest installation..."
if ! python3 -c "import pytest" 2>/dev/null; then
    echo "Installing pytest..."
    pip3 install pytest --quiet
    echo -e "${GREEN}pytest installed${NC}"
else
    echo -e "${GREEN}pytest already installed${NC}"
fi
echo ""

# Run tests
echo "========================================"
echo "Running Paper Example Tests"
echo "========================================"
echo ""

# Run with verbose output
if python3 -m pytest tests/ -v --tb=short; then
    echo ""
    echo -e "${GREEN}========================================"
    echo "All tests passed!"
    echo "========================================${NC}"
    exit 0
else
    echo ""
    echo -e "${RED}========================================"
    echo "Some tests failed!"
    echo "========================================${NC}"
    exit 1
fi
