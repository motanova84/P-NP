# 📡 PNP Bridge - Riemann Zeta Zero Search Agent

## Overview

The **PNP Bridge** (`pnp_bridge.py`) is a specialized agent that demonstrates how coherence transforms the complexity of Riemann zeta function zero search from NP to P-equivalent operations.

## Key Concept

Traditional zero-finding for ζ(s) requires exhaustive search (NP-like complexity), but with sufficient coherence (Ψ ≥ 0.888), the zeros can be located through resonance, reducing complexity to polynomial time.

## Features

- **Classical vs Coherent Search**: Compare traditional exhaustive search with coherent resonance-based search
- **Complexity Transition Analysis**: Analyze how complexity changes across different coherence levels
- **Zero Detection Simulation**: Simulate experiments with configurable coherence parameters
- **JSON Export**: Save analysis and simulation results for further processing

## Usage

### 1. Conceptual Overview (Default Mode)

```bash
python pnp_bridge.py
```

Displays a conceptual explanation of the P-NP bridge mechanism.

### 2. Analysis Mode

```bash
python pnp_bridge.py --analyze
```

Analyzes complexity transitions across coherence levels (0.5 to 0.999999).

**Options:**
- `--t-min FLOAT`: Minimum t value (default: 14.0)
- `--t-max FLOAT`: Maximum t value (default: 100.0)
- `--output FILE`: Save results to JSON file

**Example:**
```bash
python pnp_bridge.py --analyze --t-min 50 --t-max 500 --output results.json
```

### 3. Simulation Mode

```bash
python pnp_bridge.py --simulate
```

Simulates zero detection experiments comparing classical and coherent approaches.

**Options:**
- `--coherence FLOAT`: Coherence level (default: 0.999)
- `--output FILE`: Save results to JSON file

**Example:**
```bash
python pnp_bridge.py --simulate --coherence 0.95 --output simulation.json
```

## Key Parameters

### Coherence Levels
- **< 0.888**: Classical behavior (no coherence advantage)
- **≥ 0.888**: Basic resonance (10x advantage)
- **≥ 0.95**: Moderate resonance (100x advantage)
- **≥ 0.99**: High resonance (10,000x advantage)
- **≥ 0.999**: Very high resonance (1,000,000x advantage)
- **≥ 0.999999**: Near-perfect resonance (infinite advantage)

### Critical Threshold
The critical coherence threshold is **0.888**, at which point the transition from NP to P-equivalent complexity occurs.

## Output

### Analysis Output
Shows a table comparing:
- Classical complexity per zero
- Coherent complexity per zero
- Acceleration factor
- P-equivalence status

Also identifies the coherence transition point where NP→P occurs.

### Simulation Output
Provides metrics for both classical and coherent detection:
- Number of detections
- False positive rate
- Recall (sensitivity)
- Precision
- F1 Score
- Improvement factors

## Dependencies

- numpy
- json (standard library)
- argparse (standard library)
- dataclasses (standard library)

## Implementation Details

The bridge uses:
- Exponential reduction in evaluation points with coherence
- Resonance zones that make zeros "emerge" rather than being found
- Riemann-Siegel formula-based spacing estimates
- Stochastic simulation with coherence-boosted detection

## Examples

### Find the transition point
```bash
python pnp_bridge.py --analyze
```
Output shows: `🎯 PUNTO DE TRANSICIÓN NP→P: C ≥ 0.888000`

### Compare different coherence levels
```bash
python pnp_bridge.py --simulate --coherence 0.888
python pnp_bridge.py --simulate --coherence 0.999
```

### Export full analysis
```bash
python pnp_bridge.py --analyze --t-min 10 --t-max 1000 --output full_analysis.json
```

## Theoretical Foundation

The transformation is based on:

```
T_total(ζ) = T_scan / Ψ(s)
```

Where:
- `T_total`: Total time to find all zeros
- `T_scan`: Classical scan time
- `Ψ(s)`: Coherence function

As `Ψ(s) → 1`, the complexity approaches constant time, making zero-finding P-equivalent.

## Integration

This agent is part of the P-NP repository's agent ecosystem and demonstrates the theoretical principles applied to the Riemann Hypothesis zero-finding problem.
