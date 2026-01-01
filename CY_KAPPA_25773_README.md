# Calabi-Yau Varieties with h11 + h21 = 13

## Overview

This module generates Calabi-Yau varieties where the sum of Hodge numbers equals 13 (h¹'¹ + h²'¹ = 13) and exports them to JSON format.

## Mathematical Background

For Calabi-Yau threefolds (CY3):
- **Hodge numbers**: h¹'¹ and h²'¹ characterize the manifold topology
- **Euler characteristic**: χ = 2(h¹'¹ - h²'¹)
- **Universal constant**: κ_Π = log(13) ≈ 2.564949

## Usage

### Generate CY Varieties

```bash
python3 generate_cy_kappa_25773.py
```

### Output

The script generates a JSON file at `results/cy_kappa_25773_log13.json` containing 12 Calabi-Yau varieties.

### Example Output Entry

```json
{
  "ID": "CY_6_7",
  "h11": 6,
  "h21": 7,
  "chi_Euler": -2,
  "kappa_pi": 2.564949
}
```

## Properties

Each variety entry contains:
- **ID**: Unique identifier in format `CY_{h11}_{h21}`
- **h11**: First Hodge number (1 ≤ h11 ≤ 12)
- **h21**: Second Hodge number (1 ≤ h21 ≤ 12)
- **chi_Euler**: Euler characteristic = 2(h11 - h21)
- **kappa_pi**: Universal constant = log(13) ≈ 2.564949

## Verification

Run the verification tests:

```bash
python3 -c "
import json
with open('results/cy_kappa_25773_log13.json', 'r') as f:
    data = json.load(f)
    print(f'Generated {len(data)} varieties')
    for item in data[:3]:
        print(f'  {item[\"ID\"]}: h11={item[\"h11\"]}, h21={item[\"h21\"]}, χ={item[\"chi_Euler\"]}')
"
```

## Dependencies

- Python 3.x
- numpy

Install dependencies:
```bash
pip install numpy
```

## Author

José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
Date: 1 enero 2026

## Related Files

- `generate_cy_kappa_25773.py` - Generator script
- `results/cy_kappa_25773_log13.json` - Output JSON file
- `validate_qcal_pi.py` - QCAL-Π validation framework
- `src/calabi_yau_complexity.py` - CY complexity implementation
