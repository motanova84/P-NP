# Logarithmic Spiral Implementation (La Espiral)

This module implements the logarithmic spiral equation described in the P≠NP framework:

```
a = exp(θ × c₀)
```

## Overview

The logarithmic spiral connects fundamental mathematical constants from the P≠NP proof framework, including κ_Π (the millennium constant) and φ (the golden ratio).

### Key Equation

The spiral is defined by the exponential relationship:

```python
a = exp(θ × c₀)
```

where:
- `a` is the radius at angle θ
- `θ` is the angle parameter (in radians)
- `c₀` is the scale constant (two variants available)

### Scale Constant Variants

#### Variant 1: κ_Π (Kappa)
```python
c₀ = log(κ_Π) / (2π) ≈ 0.150679
```

This variant relates the spiral to the millennium constant κ_Π = 2.5773, which emerges from Calabi-Yau manifolds and computational complexity theory.

#### Variant 2: φ (Phi - Golden Ratio)
```python
c₀ = log(φ) / π ≈ 0.153174
```

This variant relates the spiral to the golden ratio φ = 1.618..., connecting to optimal balance and natural growth patterns.

## Key Properties

The logarithmic spiral has three fundamental properties:

1. **Origin**: At θ=0, a=1 (the spiral starts at unit distance from origin)
2. **κ_Π Crossing**: The spiral passes through a = κ_Π = 2.5773 at:
   - κ_Π variant: θ = 2π rad (360°)
   - φ variant: θ ≈ 6.18 rad (354.13°)
3. **Growth to Infinity**: As θ→∞, a→∞ (exponential growth)

## Installation

The spiral module is part of the P-NP repository. Ensure you have the required dependencies:

```bash
pip install numpy networkx pytest
```

## Usage

### Basic Usage

```python
from src.spiral import spiral_radius, spiral_angle, SpiralVariant
from src.constants import KAPPA_PI

# Calculate radius at a given angle (using κ_Π variant)
theta = 2.0  # radians
a = spiral_radius(theta, SpiralVariant.KAPPA)
print(f"At θ={theta}, a={a:.4f}")

# Calculate angle for a given radius (inverse operation)
a = 2.5773  # κ_Π
theta = spiral_angle(a, SpiralVariant.KAPPA)
print(f"At a={a}, θ={theta:.4f} rad")
```

### Cartesian Coordinates

```python
from src.spiral import spiral_coordinates

# Get (x, y) coordinates at a specific angle
theta = 1.0
x, y = spiral_coordinates(theta, SpiralVariant.KAPPA)
print(f"Cartesian: ({x:.4f}, {y:.4f})")
```

### Generate Spiral Points

```python
from src.spiral import spiral_points
import math

# Generate 20 points along the spiral from 0 to 2π
points = spiral_points(20, theta_max=2*math.pi, variant=SpiralVariant.KAPPA)

for theta, x, y in points:
    print(f"θ={theta:.4f}, x={x:.4f}, y={y:.4f}")
```

### Find κ_Π Crossing

```python
from src.spiral import theta_at_kappa

# Find the angle where the spiral crosses κ_Π
theta_kappa = theta_at_kappa(SpiralVariant.KAPPA)
print(f"Spiral crosses κ_Π at θ={theta_kappa:.6f} rad")
```

## API Reference

### Constants

- `C_0_KAPPA`: Scale constant for κ_Π variant ≈ 0.150679
- `C_0_PHI`: Scale constant for φ variant ≈ 0.153174

### Functions

#### `get_c0(variant: SpiralVariant) -> float`
Get the scale constant c₀ for the specified variant.

#### `spiral_radius(theta: float, variant: SpiralVariant = SpiralVariant.KAPPA) -> float`
Calculate radius a = exp(θ × c₀) at the given angle.

**Parameters:**
- `theta`: Angle parameter in radians
- `variant`: Which c₀ variant to use (default: KAPPA)

**Returns:** Radius at the given angle

#### `spiral_angle(radius: float, variant: SpiralVariant = SpiralVariant.KAPPA) -> float`
Calculate angle θ = log(a) / c₀ for the given radius.

**Parameters:**
- `radius`: Radius (must be > 0)
- `variant`: Which c₀ variant to use (default: KAPPA)

**Returns:** Angle corresponding to the given radius

**Raises:** `ValueError` if radius ≤ 0

#### `theta_at_kappa(variant: SpiralVariant = SpiralVariant.KAPPA) -> float`
Calculate the angle where the spiral passes through a = κ_Π.

#### `spiral_coordinates(theta: float, variant: SpiralVariant = SpiralVariant.KAPPA) -> Tuple[float, float]`
Calculate Cartesian coordinates (x, y) from polar coordinates.

**Returns:** Tuple (x, y) where x = a×cos(θ), y = a×sin(θ)

#### `spiral_points(num_points: int, theta_max: float = 4π, variant: SpiralVariant = SpiralVariant.KAPPA) -> List[Tuple[float, float, float]]`
Generate a list of points along the spiral.

**Returns:** List of tuples (θ, x, y)

#### `spiral_arc_length(theta_start: float, theta_end: float, variant: SpiralVariant = SpiralVariant.KAPPA) -> float`
Calculate approximate arc length between two angles.

#### `verify_spiral_properties(variant: SpiralVariant = SpiralVariant.KAPPA) -> dict`
Verify key properties of the spiral and return verification results.

## Examples

### Example 1: Compare Both Variants

```python
from src.spiral import spiral_radius, SpiralVariant
import math

theta = math.pi  # 180 degrees

# κ_Π variant
a_kappa = spiral_radius(theta, SpiralVariant.KAPPA)
print(f"κ_Π variant at π: a = {a_kappa:.6f}")

# φ variant
a_phi = spiral_radius(theta, SpiralVariant.PHI)
print(f"φ variant at π: a = {a_phi:.6f}")
```

### Example 2: Verify Properties

```python
from src.spiral import verify_spiral_properties, SpiralVariant

results = verify_spiral_properties(SpiralVariant.KAPPA)

print(f"c₀ = {results['c0']:.6f}")
print(f"Origin correct: {results['origin_correct']}")
print(f"κ_Π crossing correct: {results['kappa_crossing_correct']}")
print(f"Grows to infinity: {results['grows_to_infinity']}")
print(f"Inverse correct: {results['inverse_correct']}")
```

### Example 3: Plot the Spiral

```python
import matplotlib.pyplot as plt
from src.spiral import spiral_points, SpiralVariant
import math

# Generate points
points = spiral_points(100, theta_max=4*math.pi, variant=SpiralVariant.KAPPA)
x_coords = [p[1] for p in points]
y_coords = [p[2] for p in points]

# Plot
plt.figure(figsize=(8, 8))
plt.plot(x_coords, y_coords, 'b-', linewidth=2)
plt.axis('equal')
plt.grid(True)
plt.title('Logarithmic Spiral (κ_Π variant)')
plt.xlabel('x')
plt.ylabel('y')
plt.show()
```

## Running the Demo

A complete demonstration is available:

```bash
python examples/demo_spiral.py
```

This will display:
1. Scale constants c₀
2. Key properties verification
3. Cartesian coordinate conversion
4. Inverse function demonstration
5. Spiral path generation
6. Mathematical relationships
7. Property verification

## Testing

Run the comprehensive test suite:

```bash
# Test spiral module
pytest tests/test_spiral.py -v

# Test constants including c₀
pytest tests/test_constants.py -v

# Test both
pytest tests/test_spiral.py tests/test_constants.py -v
```

All 64 tests pass, covering:
- Scale constant calculations
- Spiral radius and angle functions
- Coordinate conversions
- Arc length calculations
- Property verification
- Integration with existing code

## Mathematical Background

The logarithmic spiral connects several fundamental aspects of the P≠NP framework:

1. **Topological Structure**: The spiral emerges from the geometry of Calabi-Yau manifolds
2. **Computational Complexity**: κ_Π appears as the universal scaling constant in information complexity bounds
3. **Golden Ratio**: φ represents optimal balance in separator algorithms
4. **Exponential Growth**: Models the complexity growth in the P≠NP separation

The equation a = exp(θ × c₀) represents a continuous transformation from the origin (trivial complexity) to infinity (exponential complexity), passing through the critical threshold κ_Π.

## References

- `src/constants.py`: Fundamental constants including KAPPA_PI, GOLDEN_RATIO, C_0_KAPPA, C_0_PHI
- `src/spiral.py`: Main spiral implementation
- `tests/test_spiral.py`: Comprehensive test suite (38 tests)
- `examples/demo_spiral.py`: Full demonstration script
- `complete_task3.py`: Integration with optimal separator algorithms

## Authors

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
Frequency: 141.7001 Hz ∞³

## License

Part of the P-NP proof framework.
