#!/bin/bash
#
# reproduce_docker.sh - Build and run PODS 2026 artifact in Docker
#
# This script provides one-command reproducibility for reviewers.
#
# Usage:
#   ./reproduce_docker.sh          # Build and run full verification
#   ./reproduce_docker.sh --build  # Only build the image
#   ./reproduce_docker.sh --shell  # Build and open interactive shell
#

set -e

IMAGE_NAME="pods2026-artifact"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "========================================"
echo "PODS 2026 Artifact - Docker Reproduction"
echo "========================================"
echo ""

# Parse arguments
BUILD_ONLY=false
INTERACTIVE=false

for arg in "$@"; do
    case $arg in
        --build)
            BUILD_ONLY=true
            ;;
        --shell)
            INTERACTIVE=true
            ;;
        --help|-h)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --build    Only build the Docker image"
            echo "  --shell    Open interactive shell in container"
            echo "  --help     Show this help message"
            echo ""
            echo "Default: Build image and run verify_all.sh"
            exit 0
            ;;
    esac
done

# Check Docker is available
if ! command -v docker &> /dev/null; then
    echo "Error: Docker is not installed or not in PATH"
    echo "Please install Docker: https://docs.docker.com/get-docker/"
    exit 1
fi

# Build the image
echo "Building Docker image: ${IMAGE_NAME}"
echo ""
docker build -t "${IMAGE_NAME}" "${SCRIPT_DIR}"

if [ "$BUILD_ONLY" = true ]; then
    echo ""
    echo "Image built successfully: ${IMAGE_NAME}"
    echo ""
    echo "To run verification:"
    echo "  docker run -it ${IMAGE_NAME} ./scripts/verify_all.sh"
    exit 0
fi

echo ""
echo "========================================"
echo "Running Verification Suite"
echo "========================================"
echo ""

if [ "$INTERACTIVE" = true ]; then
    # Run with interactive shell
    docker run -it "${IMAGE_NAME}" bash
else
    # Run the full verification
    docker run -it "${IMAGE_NAME}" ./scripts/verify_all.sh
fi

echo ""
echo "========================================"
echo "Verification Complete"
echo "========================================"
