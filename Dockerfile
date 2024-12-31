# Dockerfile for PODS 2026 Artifact - Categorical Data Processing
# Provides complete reproducibility environment with Lean 4, TLA+, and Python
#
# Build: docker build -t pods2026-artifact .
# Run:   docker run -it pods2026-artifact

FROM ubuntu:22.04

# Prevent interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Set up locale
RUN apt-get update && apt-get install -y locales && \
    locale-gen en_US.UTF-8 && \
    update-locale LANG=en_US.UTF-8

ENV LANG=en_US.UTF-8
ENV LC_ALL=en_US.UTF-8

# Install system dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    python3 \
    python3-pip \
    default-jre \
    wget \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Verify Java installation for TLA+
RUN java -version

# Install Lean 4 via elan (non-interactive)
ENV ELAN_HOME=/root/.elan
ENV PATH="${ELAN_HOME}/bin:${PATH}"

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | \
    sh -s -- -y --default-toolchain leanprover/lean4:v4.3.0

# Verify Lean installation
RUN lean --version

# Create tools directory and download TLA+ tools
RUN mkdir -p /tools
RUN wget -O /tools/tla2tools.jar \
    https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/tla2tools.jar

# Create TLC wrapper script
RUN echo '#!/bin/bash\njava -XX:+UseParallelGC -Xmx4g -jar /tools/tla2tools.jar "$@"' > /usr/local/bin/tlc && \
    chmod +x /usr/local/bin/tlc

# Set working directory
WORKDIR /app

# Copy requirements first for better layer caching
COPY requirements.txt .

# Install Python dependencies
RUN pip3 install --no-cache-dir -r requirements.txt

# Copy the entire repository
COPY . .

# Ensure scripts are executable
RUN chmod +x scripts/*.sh tla/*.sh 2>/dev/null || true

# Copy TLA+ tools to tla directory for local use
RUN cp /tools/tla2tools.jar tla/ 2>/dev/null || true

# Build Lean proofs (optional - uncomment to pre-build in image)
# RUN cd lean && lake exe cache get && lake build

# Default command: show help
CMD ["bash", "-c", "echo 'PODS 2026 Artifact Container' && echo '' && echo 'Run verification:' && echo '  ./scripts/verify_all.sh' && echo '' && echo 'Or run specific components:' && echo '  cd lean && lake build' && echo '  cd tla && ./run_all.sh' && echo '  cd examples && python3 running_example.py' && bash"]
