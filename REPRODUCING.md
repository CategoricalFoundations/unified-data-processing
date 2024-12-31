# Reproduction Guide

This document provides complete instructions for reproducing all verification results from the paper.

## Table of Contents

1. [Docker-based Reproduction](#1-docker-based-reproduction) ⭐ **Recommended**
2. [Environment Setup](#2-environment-setup)
3. [Lean 4 Verification](#3-lean-4-verification)
4. [TLA+ Model Checking](#4-tla-model-checking)
5. [Running Examples](#5-running-examples)
6. [Benchmark Validation](#6-benchmark-validation)
7. [Troubleshooting](#7-troubleshooting)

---

## Option 0: Docker Reproduction (Recommended)

> [!IMPORTANT]
> **For reviewers**: This is the recommended method for artifact evaluation. It provides a fully containerized environment with all dependencies pre-configured, ensuring consistent results across different machines.

```bash
# One-command reproduction
chmod +x reproduce_docker.sh && ./reproduce_docker.sh
```

---

## 1. Docker-based Reproduction (Details)

> [!TIP]
> If the one-liner above works, you're done! The sections below provide additional Docker options and manual installation instructions.

### 1.1 Prerequisites

- Docker 20.10+ installed ([Get Docker](https://docs.docker.com/get-docker/))
- At least 8GB RAM and 10GB disk space

### 1.2 One-Command Reproduction

```bash
# Clone the repository
git clone https://github.com/CategoricalFoundations/unified-data-processing.git
cd unified-data-processing

# Run complete verification (builds image and runs all tests)
./reproduce_docker.sh
```

This will:
1. Build a Docker image with Ubuntu 22.04, Lean 4, TLA+ tools, and Python
2. Execute the full verification suite inside the container
3. Report results for all four verification phases

### 1.3 Alternative Docker Commands

```bash
# Build image only (useful for inspection)
./reproduce_docker.sh --build

# Interactive shell (for manual exploration)
./reproduce_docker.sh --shell

# Run specific verification steps manually
docker run -it pods2026-artifact bash
# Inside container:
cd lean && lake build
cd tla && ./run_all.sh
cd examples && python3 running_example.py
```

### 1.4 Expected Docker Verification Output

```
========================================================================
Verification Summary
========================================================================

  Lean 4 Proofs: PASSED
  TLA+ Model Checking: PASSED
  Python Examples: PASSED
  Complexity Benchmarks: PASSED

All available verifications passed!
```

**Expected Time**: ~15 minutes for image build, ~3 hours for full verification

---

## 2. Environment Setup

### 2.1 System Requirements

- **OS**: Linux (Ubuntu 20.04+), macOS (11+), or Windows 10+ with WSL2
- **RAM**: Minimum 8GB, recommended 16GB for TLA+ model checking
- **Disk**: 5GB free space
- **CPU**: Multi-core recommended for parallel verification

### 2.2 Install Lean 4

```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Source the environment
source ~/.elan/env

# Verify installation
lean --version
# Expected: Lean (version 4.3.0, ...)
```

### 2.3 Install TLA+ Toolbox

**Option A: GUI Installation**
1. Download from https://github.com/tlaplus/tlaplus/releases
2. Install TLA+ Toolbox 1.7.1 or later
3. Ensure `tlc` is in PATH

**Option B: Command Line Only**
```bash
# Download TLC jar
wget https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/tla2tools.jar

# Create wrapper script
echo '#!/bin/bash
java -XX:+UseParallelGC -jar /path/to/tla2tools.jar "$@"' > ~/bin/tlc
chmod +x ~/bin/tlc
```

### 2.4 Install Python Dependencies

```bash
# Create virtual environment (recommended)
python3 -m venv venv
source venv/bin/activate

# Install dependencies
pip install numpy matplotlib pandas tqdm
```

### 2.5 Clone Repository

```bash
git clone https://github.com/CategoricalFoundations/unified-data-processing.git
cd unified-data-processing
```

---

## 3. Lean 4 Verification

### 3.1 Build All Proofs

```bash
cd lean

# Download Mathlib cache (saves ~30 minutes)
lake exe cache get

# Build all proofs
lake build

# Expected output:
# Building Main
# Build completed successfully
```

**Expected Time**: ~5 minutes (with cache), ~35 minutes (without cache)

### 3.2 Verify Specific Theorems

```bash
# Check a specific file
lake build Categories

# Run with verbose output
lake build -v Adjunctions
```

### 3.3 Inspect Proof Status

```bash
# List all theorems and their status
lake exe list_theorems

# Check for any remaining 'sorry' axiomatizations
grep -r "sorry" *.lean
```

### 3.4 Expected Results

```
✓ Categories.lean       - 14 theorems verified
✓ Adjunctions.lean      - 21 theorems (19 verified, 2 axiomatized)
✓ KanExtensions.lean    - 16 theorems (14 verified, 2 axiomatized)
✓ DeltaUniqueness.lean  - 4 theorems verified
✓ ZRelations.lean       - 11 theorems verified
✓ CorrectionMonad.lean  - 9 theorems (8 verified, 1 axiomatized)
✓ Main.lean            - 14 integration tests passed
─────────────────────────────────────────────────
Total: 89 theorems, 84 verified, 5 axiomatized
```

### 3.5 Understanding Axiomatizations

The 5 axiomatized proofs are documented in `lean/AXIOMS.md`. Each has:
- Complete mathematical proof in the paper
- Explanation of why formalization is pending
- Path to eventual full verification

---

## 4. TLA+ Model Checking

### 4.1 Run All Model Checks

```bash
cd tla

# Run all specifications (sequential)
./run_all.sh

# Or run in parallel (faster, needs more RAM)
./run_all.sh --parallel
```

**Expected Time**: ~2 hours (sequential), ~45 minutes (parallel with 4+ cores)

### 4.2 Run Individual Specifications

```bash
# ParadigmTransform (safety + liveness)
tlc ParadigmTransform.tla -config MC.cfg -workers 4

# ZRelations (ring properties)
tlc ZRelations.tla -config MC.cfg -workers 4

# CorrectionProtocol (eventual consistency)
tlc CorrectionProtocol.tla -config MC.cfg -workers 4
```

### 4.3 Expected Results

```
ParadigmTransform.tla
─────────────────────
States explored: 4,200,000
Distinct states: 847,000
Safety violations: 0
Liveness violations: 0
Time: 42 minutes

ZRelations.tla
──────────────
States explored: 3,100,000
Distinct states: 623,000
Safety violations: 0
Time: 31 minutes

CorrectionProtocol.tla
──────────────────────
States explored: 5,100,000
Distinct states: 1,020,000
Safety violations: 0
Liveness violations: 0
Time: 54 minutes
```

### 4.4 Adjusting Model Parameters

For faster checking (reduced state space):
```tla
\* In MC.cfg, modify:
MaxDataSize = 3      \* Default: 4
WindowSize = 2       \* Default: 3
MaxEpoch = 4         \* Default: 6
```

For more thorough checking (larger state space):
```tla
MaxDataSize = 5
WindowSize = 4
MaxEpoch = 8
\* Warning: May require 32GB+ RAM
```

---

## 5. Running Examples

### 5.1 Paper Running Example (Example 1.1)

```bash
cd examples
python running_example.py
```

**Expected Output**:
```
=== Running Example from Paper ===

Batch Query: Sum({|10, 20, 30|}) = 60

Stream Processing:
  Event (t1: 10) → Running sum: 10
  Event (t2: 20) → Running sum: 30
  Event (t3: 30) → Running sum: 60

With Retraction:
  Event (t4: -20) → Running sum: 40

Kan Extension Verification:
  Batch result: 60
  Stream result: 60
  ✓ Kan extension preserves semantics
```

### 5.2 IVM Delta Rule Demonstration

```bash
python ivm_demo.py
```

**Expected Output**:
```
=== IVM Delta Rules as Categorical Consequences ===

Initial State: R = {(1, 'a'), (2, 'b'), (3, 'c')}
Update: ΔR = {(4, 'd')}

Selection σ_{x > 1}:
  Full recompute: {(2, 'b'), (3, 'c'), (4, 'd')}
  Incremental:    {(2, 'b'), (3, 'c')} + {(4, 'd')}
  ✓ Results match (Theorem 5.5)

Projection π_2:
  Full recompute: {'a', 'b', 'c', 'd'}
  Incremental:    {'a', 'b', 'c'} + {'d'}
  ✓ Results match (Theorem 5.5)

Join R ⋈ S:
  Full recompute: {(1, 'a', 'x'), ...}
  Incremental:    (R ⋈ S) + (ΔR ⋈ S)
  ✓ Results match (Theorem 5.5)

=== Uniqueness Demonstration (Theorem 5.6) ===
Any alternative delta rule Δ' satisfying decomposition
must equal Δ on the Kan extension image.
```

### 5.3 Correction Monad Demonstration

```bash
python late_data_demo.py
```

**Expected Output**:
```
=== Correction Monad for Late Data ===

Stream with late arrival:
  t=0: Event (a, +1), timestamp=5
  t=1: Watermark advances to 10
  t=2: Late event (b, +1), timestamp=3 (LATE!)

Without Correction Monad:
  G(S) = {a: 1}  (b dropped)

With Correction Monad:
  G^T(S) = (current: {a: 1}, pending: {b: 1})
  After apply: {a: 1, b: 1}
  ✓ Late data recovered

Eventual Preservation (Theorem 7.5):
  After all corrections: result = perfect result
```

---

## 6. Benchmark Validation

### 6.1 Run All Benchmarks

```bash
cd benchmarks

# IVM Delta Rules (Theorem 5.6)
python ivm_benchmark.py

# Paradigm Transformations (Theorem 8.1)
python paradigm_transform_benchmark.py

# Correction Monad (Theorem 7.4)
python correction_monad_benchmark.py
```

### 6.2 Expected Results

**IVM Benchmark (Theorem 5.6)**:
```
Results: 1000/1000 pairs satisfy Δ_std = Δ_alt
Theorem 5.6 empirically verified: ✓
```

**Paradigm Transform (Theorem 8.1)**:
```
✓ F_BS (Batch→Stream): Complexity validated O(n)
✓ G_SB (Stream→Batch): Complexity validated O(n)
✓ G_GS (Graph→Stream): Complexity validated O(n log n)
✓ F_SG (Stream→Graph): Complexity validated O(n log n)

✓ Plot generated: benchmarks/results/complexity_plot.png
```

> [!NOTE]
> The `paradigm_transform_benchmark.py` script now generates a visual complexity plot comparing empirical G_GS runtimes against the theoretical Θ(n log n) bound. The plot is saved to `benchmarks/results/complexity_plot.png`.

**Correction Monad (Theorem 7.4)**:
```
Results: 1000/1000 achieved eventual preservation
Theorem 7.4 verified: ✓
```

### 6.3 Integration Script

```bash
# Run all verifications at once
cd scripts
./run_all_benchmarks.sh
```

---

## 7. Troubleshooting

### 7.1 Lean Build Failures

**Problem**: `lake build` fails with missing dependencies

**Solution**:
```bash
lake update
lake exe cache get
lake build
```

**Problem**: Out of memory during build

**Solution**:
```bash
# Reduce parallelism
lake build -j 1
```

### 7.2 TLA+ Failures

**Problem**: TLC runs out of memory

**Solution**:
```bash
# Increase Java heap
java -Xmx8g -jar tla2tools.jar ...

# Or reduce model size in MC.cfg
```

**Problem**: Liveness check hangs

**Solution**:
```bash
# Use simulation mode for liveness
tlc -simulate -depth 1000000 CorrectionProtocol.tla
```

### 7.3 Python Examples

**Problem**: Import errors

**Solution**:
```bash
pip install -r requirements.txt
```

### 7.4 Getting Help

If you encounter issues not covered here:
1. Check `issues/` directory for known problems
2. Ensure all version requirements are met
3. Contact authors via PODS review system

---

## Appendix: Version Information

| Tool | Required Version | Tested Versions |
|------|------------------|-----------------|
| Lean | 4.3.0 | 4.3.0, 4.4.0 |
| Mathlib | 2024-01-01+ | Commit in lakefile.lean |
| TLA+ Toolbox | 1.7.1+ | 1.7.1, 1.8.0 |
| Java | 11+ | 11, 17, 21 |
| Python | 3.10+ | 3.10, 3.11, 3.12 |

---

## Verification Checklist

Use this checklist to confirm complete reproduction:

- [ ] Lean 4 builds without errors
- [ ] All 84 Lean theorems verified (5 axiomatized acknowledged)
- [ ] ParadigmTransform.tla: 0 violations
- [ ] ZRelations.tla: 0 violations  
- [ ] CorrectionProtocol.tla: 0 violations
- [ ] Running example produces expected output
- [ ] IVM demo demonstrates delta rules
- [ ] Late data demo shows correction monad
- [ ] Complexity benchmark confirms $\Theta(n \log n)$

**Total verification time**: ~3 hours (first run), ~30 minutes (subsequent)
