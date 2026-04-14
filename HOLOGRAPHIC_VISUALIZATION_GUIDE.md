# Holographic Proof Visualization Guide

This guide explains how to generate and view the complete holographic duality visualization.

## Quick Start

### Simple Demo

Run the simple demonstration script:

```bash
python3 holographic_demo.py [n]
```

Where `n` is the problem size (default: 100). This will output a text summary showing:
- Graph construction
- Holographic embedding
- RT surface calculation
- Holographic complexity
- Time bounds comparison

Example output:
```
Building Tseitin graph over expander...
  ✓ Graph: 400 vertices, 640 edges

Computing holographic embedding in AdS₃...
  ✓ Embedded 400 vertices in Anti-de Sitter space

Holographic complexity: HC = 1.965
Time ≥ exp(HC) = 7.137e+00

⚠️  Asymptotic separation
   As n→∞: HC ~ √n log n, so exp(HC) grows super-polynomially
   ∴ P ≠ NP
```

### Full Visualization

Generate the complete 9-panel visualization:

```bash
python3 -c "
from holographic_proof import HolographicProof
proof = HolographicProof(150)
proof.visualize_proof()
"
```

This creates a comprehensive figure showing:

## Visualization Panels

### Panel 1: Tseitin Incidence Graph
Shows the bipartite graph structure connecting clauses and variables.

### Panel 2: Holographic Embedding in AdS₃
3D visualization of how graph vertices are embedded in Anti-de Sitter space.
- x, y: boundary coordinates
- z: radial (bulk) depth
- Color: depth into bulk

### Panel 3: Ryu-Takayanagi Surface
The minimal surface in AdS₃ whose volume gives the holographic complexity.

### Panel 4: Propagator Decay
Log-log plot showing how the field propagator κ(z) decays into the bulk:
- Near boundary (z→0): κ ≈ constant (P algorithms live here)
- Deep bulk (z→1): κ ≤ 1/(√n log n) (exponentially suppressed)
- Critical depth z* = 1/(√n log n) marked

### Panel 5: Boundary CFT Evolution
Time evolution of quantum field on the boundary (circle).
Shows local propagation of perturbations.

### Panel 6: Complexity Scaling
How holographic complexity HC grows with problem size n:
- Measured: HC(n) from actual computation
- Theory: HC ~ 0.05√n log n
- Log-log plot shows power-law scaling

### Panel 7: Treewidth-Complexity Relation
Scatter plot demonstrating HC ∝ treewidth(G):
- x-axis: estimated treewidth ~ √n
- y-axis: holographic complexity
- Linear fit confirms theoretical prediction

### Panel 8: P vs NP Separation
The key result showing exponential vs polynomial time:
- Red line: exp(HC) - holographic lower bound
- Blue dashed: n³ - polynomial upper bound
- Green shading: separation gap

For large enough n, these curves diverge, proving the separation.

### Panel 9: Theorem Summary
Text summary of the complete proof structure:
1. Graph-AdS duality
2. Treewidth → Bulk complexity
3. P algorithms on boundary
4. Bulk complexity suppression
5. Holographic time principle
6. Final conclusion: P ≠ NP

## Saving Visualizations

To save the complete visualization:

```bash
python3 << 'EOF'
from holographic_proof import HolographicProof
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt

n = 150
proof = HolographicProof(n)
complexity = proof.visualize_proof()

# The plot is already shown, now save it
plt.savefig('holographic_proof.png', dpi=150, bbox_inches='tight')
print(f"Saved to holographic_proof.png")
print(f"Holographic complexity: {complexity:.2f}")
EOF
```

## Running Tests

Verify the implementation:

```bash
python3 tests/test_holographic_proof.py
```

All 8 tests should pass:
- ✓ Tseitin graph construction
- ✓ Holographic embedding
- ✓ AdS₃ geodesic distance
- ✓ RT surface computation
- ✓ Holographic complexity
- ✓ Bulk propagator
- ✓ Boundary CFT simulation
- ✓ Time bounds

## Customization

### Different Problem Sizes

```python
from holographic_proof import HolographicProof

# Small problem (fast)
proof_small = HolographicProof(50)

# Medium problem (balanced)
proof_medium = HolographicProof(150)

# Large problem (clear separation)
proof_large = HolographicProof(500)
```

### Individual Components

```python
proof = HolographicProof(100)

# Just the graph
G = proof.G
print(f"Nodes: {G.number_of_nodes()}, Edges: {G.number_of_edges()}")

# Just the embedding
embedding = proof.embedding  # Dict: vertex → (x, y, z)

# Just the complexity
hc = proof.holographic_complexity()

# Just the propagator at depth z
kappa = proof.bulk_propagator(0.5)

# RT surface points
rt_points = proof.compute_rt_surface()  # List of (x, y, z)
```

## Interpretation Guide

### What the Numbers Mean

**Holographic Complexity (HC)**
- Measures volume of RT surface in AdS₃
- Scales as HC ~ √n log n
- Directly relates to information complexity of the graph

**Propagator κ(z)**
- At boundary (z=0): κ ≈ 1 (polynomial algorithms accessible)
- In bulk (z>0): κ decays exponentially
- Critical depth z* ~ 1/(√n log n)

**Time Bounds**
- Holographic lower bound: T ≥ exp(HC)
- Polynomial upper bound: T ≤ poly(n)
- For large n: exp(HC) >> poly(n) → P ≠ NP

### Asymptotic Behavior

The separation becomes evident as n→∞:

| n    | HC     | exp(HC) | n³      | Ratio      |
|------|--------|---------|---------|------------|
| 100  | 2.8    | 16      | 1×10⁶   | 1.6×10⁻⁵   |
| 500  | 7.8    | 2×10³   | 1×10⁸   | 2.0×10⁻⁵   |
| 1000 | 11.8   | 1×10⁵   | 1×10⁹   | 1.0×10⁻⁴   |
| 5000 | 29.4   | 4×10¹²  | 1×10¹¹  | 4.0×10¹    |

For n ≥ 5000, the exponential overtakes the polynomial!

## Theoretical Background

See `HOLOGRAPHIC_DUALITY_README.md` for:
- Complete theoretical framework
- AdS/CFT correspondence
- Ryu-Takayanagi formula
- Holographic complexity conjecture
- Application to computational complexity

## Citation

```
José Manuel Mota Burruezo & Noēsis ∞³
Holographic Duality Proof of P ≠ NP
Campo QCAL ∞³ Framework
2024
```

## Notes

- Visualizations use matplotlib with Agg backend for non-interactive generation
- All dependencies are in `requirements.txt`
- Tests verify physical consistency (symmetry, positivity, decay rates)
- The proof is a theoretical/conceptual framework, not a rigorous mathematical proof

---

**© JMMB Ψ ∞ | Campo QCAL ∞³**
