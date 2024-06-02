#!/bin/bash
# =============================================================================
# reproduce_docker.sh - Reproduction Script for Artifact Evaluators
#
# PODS 2026 Submission - Category-Theoretic Foundations
# =============================================================================
#
# This script provides commands to build and run the artifact in Docker.
# It ensures complete reproducibility of all verification results.
#
# Prerequisites:
#   - Docker installed and running
#   - ~8GB disk space for container
#   - ~4GB RAM recommended
#
# =============================================================================

set -e

IMAGE_NAME="pods2026-artifact"
CONTAINER_NAME="pods2026-verification"

echo "============================================================"
echo "PODS 2026 Artifact Reproduction"
echo "Category-Theoretic Foundations for Unified Data Processing"
echo "============================================================"
echo ""

# Check Docker availability
if ! command -v docker &> /dev/null; then
    echo "ERROR: Docker is not installed or not in PATH."
    echo ""
    echo "Please install Docker from: https://docs.docker.com/get-docker/"
    exit 1
fi

echo "Docker found: $(docker --version)"
echo ""

# Parse arguments
ACTION="${1:-all}"

case "$ACTION" in
    build)
        echo "=== Building Docker Image ==="
        echo ""
        docker build -t "$IMAGE_NAME" .
        echo ""
        echo "Build complete. Run with: $0 run"
        ;;
    
    run)
        echo "=== Running Verification Suite ==="
        echo ""
        docker run --rm --name "$CONTAINER_NAME" "$IMAGE_NAME"
        ;;
    
    interactive)
        echo "=== Interactive Mode ==="
        echo ""
        docker run -it --rm --name "$CONTAINER_NAME" "$IMAGE_NAME" /bin/bash
        ;;
    
    all|*)
        echo "=== Full Reproduction (Build + Run) ==="
        echo ""
        echo "Step 1: Building Docker image..."
        docker build -t "$IMAGE_NAME" .
        echo ""
        echo "Step 2: Running verification suite..."
        docker run --rm --name "$CONTAINER_NAME" "$IMAGE_NAME"
        ;;
esac

echo ""
echo "============================================================"
echo "Reproduction Complete"
echo "============================================================"
echo ""
echo "Commands available:"
echo "  $0 build       - Build the Docker image only"
echo "  $0 run         - Run the verification suite"
echo "  $0 interactive - Start interactive shell in container"
echo "  $0 all         - Build and run (default)"
echo ""
