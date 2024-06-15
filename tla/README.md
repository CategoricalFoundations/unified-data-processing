# TLA+ Specifications

This directory contains TLA+ specifications for model-checking operational properties of the categorical data processing framework.

## Files

| File | Description | States | Properties |
|------|-------------|--------|------------|
| `ParadigmTransform.tla` | Batch-Stream transformation safety | ~4.2M | 5 safety, 2 liveness |
| `ZRelations.tla` | Z-relation algebraic properties | ~3.1M | 6 safety, 2 liveness |
| `CorrectionProtocol.tla` | Late data handling protocol | ~5.1M | 6 safety, 3 liveness |
| `MC.cfg` | Model checker configuration | — | — |

## Quick Start

### Prerequisites

- TLA+ Toolbox 1.7.1+ or standalone TLC
- Java 11+

### Running with TLA+ Toolbox

1. Open TLA+ Toolbox
2. Create new spec, add `.tla` file
3. Create model with constants from MC.cfg
4. Run model checker

### Running with Command Line

```bash
# ParadigmTransform
java -jar tla2tools.jar -config MC_ParadigmTransform.cfg ParadigmTransform.tla

# ZRelations
java -jar tla2tools.jar -config MC_ZRelations.cfg ZRelations.tla

# CorrectionProtocol
java -jar tla2tools.jar -config MC_CorrectionProtocol.cfg CorrectionProtocol.tla
```

### Parallel Execution

```bash
java -XX:+UseParallelGC -Xmx8g -jar tla2tools.jar \
  -workers 4 \
  -config MC.cfg \
  ParadigmTransform.tla
```

## Model Parameters

### ParadigmTransform.tla

| Constant | Default | Description |
|----------|---------|-------------|
| `MaxDataSize` | 4 | Maximum batch/stream size |
| `WindowSize` | 3 | Window for G_SB extraction |
| `MaxTimestamp` | 8 | Maximum event timestamp |

### ZRelations.tla

| Constant | Default | Description |
|----------|---------|-------------|
| `MaxTuples` | 4 | Max distinct tuples |
| `MaxMultiplicity` | 3 | Max absolute multiplicity |
| `TupleSpace` | {1,2,3,4} | Set of tuple values |

### CorrectionProtocol.tla

| Constant | Default | Description |
|----------|---------|-------------|
| `MaxEvents` | 4 | Max total events |
| `MaxLateness` | 2 | Maximum lateness δ_max |
| `DataValues` | {1,2,3} | Set of data values |

## Properties Verified

### Safety Properties

1. **TypeInvariant**: All variables have correct types
2. **CorrectionCompleteness**: current + pending = perfect (Theorem 7.5)
3. **MultiplicityBounds**: Z-relation multiplicities stay bounded
4. **NoDataLossSmallBatch**: Round-trip preserves small batches
5. **WatermarkMonotonicity**: Watermarks only advance

### Liveness Properties

1. **EventualConsistency**: Eventually result = perfect result
2. **Progress**: System can always make progress
3. **EventualParadigmReachability**: Can reach any paradigm

## Expected Results

After running all specifications with default parameters:

```
ParadigmTransform.tla
  States explored: 4,247,128
  Distinct states: 847,423
  Safety violations: 0
  Liveness violations: 0

ZRelations.tla
  States explored: 3,128,456
  Distinct states: 623,891
  Safety violations: 0
  
CorrectionProtocol.tla
  States explored: 5,142,789
  Distinct states: 1,028,558
  Safety violations: 0
  Liveness violations: 0
```

## Extending the Specifications

### Adding New Properties

1. Define property in INVARIANT or PROPERTY section
2. Add to MC.cfg
3. Run model checker

### Increasing State Space

Modify constants in MC.cfg:
```
CONSTANT MaxDataSize = 6
CONSTANT MaxEvents = 6
```

**Warning**: State space grows exponentially. Monitor memory usage.

## Troubleshooting

### Out of Memory

```bash
java -Xmx16g -jar tla2tools.jar ...
```

### Slow Liveness Checking

Use simulation mode:
```bash
java -jar tla2tools.jar -simulate -depth 1000000 Spec.tla
```

### Deadlock Detection

Add to specification:
```tla
DeadlockFree == ENABLED(Next)
```

## Correspondence to Paper Theorems

| Theorem | Property | File |
|---------|----------|------|
| 4.10 | NoDataLossSmallBatch | ParadigmTransform.tla |
| 6.2 | ZUnionCommutative, etc. | ZRelations.tla |
| 7.5 | EventualConsistency | CorrectionProtocol.tla |
| 7.6 | CorrectionCompleteness | CorrectionProtocol.tla |
