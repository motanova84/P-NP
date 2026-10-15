# Calabi-Yau Varieties Dataset

This directory contains datasets related to Calabi-Yau manifolds used in the P≠NP complexity analysis framework.

## Files

### `calabi_yau_varieties.csv`

A dataset of 10 Calabi-Yau variety records with the following fields:

| Field | Description |
|-------|-------------|
| `ID` | Unique identifier for each variety (e.g., CY-001) |
| `Nombre` | Name of the variety (e.g., "Quíntica ℂℙ⁴[5]") |
| `h11` | First Hodge number |
| `h21` | Second Hodge number |
| `alpha` | Geometric parameter α (derived geometrically) |
| `beta` | Geometric parameter β (derived geometrically) |
| `kappa_pi` | Spectral entropy κ_Π |
| `chi_Euler` | Euler characteristic (topological invariant) |

### Dataset Statistics

- **Total varieties**: 10
- **h11 range**: [1, 12], mean=6.70 ± 3.69
- **h21 range**: [48, 101], mean=64.10 ± 17.81
- **α range**: [0.385, 0.402], mean=0.395 ± 0.005
- **β range**: [0.233, 0.244], mean=0.238 ± 0.003
- **κ_Π range**: [1.65194, 1.65805], mean=1.65414 ± 0.00203
- **χ range**: [-200, -72], mean=-114.80 ± 42.60

## Usage

### Loading the Dataset

```python
from src.calabi_yau_complexity import CalabiYauComplexity

# Initialize the analyzer
cy = CalabiYauComplexity()

# Get all varieties
varieties = cy.get_all_varieties()
print(f"Loaded {len(varieties)} varieties")

# Get a specific variety by ID
quintica = cy.get_variety('CY-001')
print(f"Variety: {quintica['nombre']}")
print(f"Hodge numbers: h11={quintica['h11']}, h21={quintica['h21']}")
```

### Analyzing Varieties

```python
# Compute complexity metrics for a variety
metrics = cy.compute_variety_complexity(quintica, n_vars=200)
print(f"Holographic complexity: {metrics['holographic_complexity']:.4f}")

# Get statistical analysis of entire dataset
stats = cy.analyze_varieties_dataset()
print(f"Mean κ_Π: {stats['kappa_pi']['mean']:.5f}")
```

### Running the Demo

```bash
python3 examples/demo_calabi_yau_varieties.py
```

This will display:
- All varieties with their properties
- Detailed analysis of selected varieties
- Statistical analysis of the entire dataset

## Mathematical Background

### Hodge Numbers (h11, h21)

The Hodge numbers h^{1,1} and h^{2,1} are topological invariants of Calabi-Yau 3-folds that count the dimensions of certain cohomology groups. They satisfy:
- **Mirror symmetry**: h^{1,1}(M) = h^{2,1}(M̃) for mirror manifolds M and M̃
- **Euler characteristic**: χ = 2(h^{1,1} - h^{2,1})

### Geometric Parameters (α, β)

The parameters α and β are derived from the geometry of the Calabi-Yau variety and relate to:
- Volume moduli
- Complex structure moduli
- Kähler parameters

### Spectral Entropy (κ_Π)

κ_Π represents the spectral entropy computed from the eigenvalue distribution of the Laplacian operator on the Calabi-Yau manifold. It serves as a bridge between:
- Geometric topology (via Hodge numbers)
- Information complexity (via entropy)
- Computational complexity (via the κ_Π constant ≈ 2.5773)

### Euler Characteristic (χ)

The Euler characteristic is a topological invariant that satisfies:
- χ = 2(h^{1,1} - h^{2,1}) for CY3 manifolds
- Negative values indicate "holes" in the topology
- Related to the number of moduli via the index theorem

## References

1. **Calabi-Yau Manifolds**: Compact Kähler manifolds with vanishing first Chern class
2. **Hodge Theory**: Harmonic forms and cohomology decomposition
3. **Mirror Symmetry**: Duality between different Calabi-Yau geometries
4. **String Compactifications**: Six-dimensional Calabi-Yau manifolds in string theory

## Connection to P≠NP

The Calabi-Yau varieties dataset connects to the P≠NP framework through:

1. **Holographic Duality**: AdS/CFT correspondence relating bulk geometry to boundary complexity
2. **Spectral Constant κ_Π ≈ 2.5773**: Emerges from averaging over 150 CY varieties
3. **Information Complexity**: Geometric entropy bounds computational complexity
4. **Treewidth Connection**: h11 serves as a proxy for graph treewidth in complexity analysis

See `src/calabi_yau_complexity.py` for the mathematical implementation.

## License

© JMMB | P vs NP Verification System
MIT License
