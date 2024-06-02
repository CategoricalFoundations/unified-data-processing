# =============================================================================
# Dockerfile for PODS 2026 Artifact Evaluation
# Category-Theoretic Foundations for Unified Data Processing
# =============================================================================
#
# This Dockerfile creates a reproducible environment for artifact evaluation.
# It includes:
# - Python 3.11 with all dependencies
# - Lean 4.3.0 with Mathlib
# - Java runtime for TLA+ model checking
#
# Build: docker build -t pods2026-artifact .
# Run:   docker run --rm pods2026-artifact
#
# =============================================================================

FROM python:3.11-slim

LABEL maintainer="artifact.eval@acm.org"
LABEL description="PODS 2026 Artifact - Category-Theoretic Foundations"
LABEL version="1.0"

# Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    curl \
    wget \
    default-jre \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# Install Lean (elan) - Lean 4.3.0
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:4.3.0
ENV PATH="/root/.elan/bin:$PATH"

# Set working directory
WORKDIR /app

# Copy project files
COPY . /app

# Make scripts executable
RUN chmod +x scripts/*.sh

# Install Python dependencies
RUN pip install --no-cache-dir -r requirements.txt

# Download TLA+ tools
RUN wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -O tla/tla2tools.jar || echo "TLA+ tools download skipped"

# Pre-build Lean proofs to save time for reviewer
RUN cd lean && lake build || echo "Lean pre-build skipped (will build on first run)"

# Default command: run full verification suite
CMD ["./scripts/verify_all.sh"]
