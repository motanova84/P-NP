# Data Directory

This directory contains benchmark CNF instances for testing the computational dichotomy framework.

## Structure

```
data/
└── benchmarks/
    ├── small.cnf      # Low treewidth instance (chain formula)
    └── expander.cnf   # High treewidth instance (Tseitin over expander)
```

## Benchmark Instances

### `small.cnf`

**Properties:**
- 5 variables, 6 clauses
- Chain structure: x₁ → x₂ → x₃ → x₄ → x₅
- Expected treewidth: 2
- Complexity: **Tractable** (polynomial time)

**Usage:**
```python
from src.icq_pnp import CNFFormula
# Parse and analyze the formula
```

### `expander.cnf`

**Properties:**
- 9 variables, 48 clauses
- Tseitin formula over 6-vertex, 3-regular graph
- Odd charge assignment (unsatisfiable)
- Expected treewidth: High (Ω(n))
- Complexity: **Intractable** (exponential time expected)

**Usage:**
```python
from src.icq_pnp.tseitin_generator import generate_expander_tseitin
# Generate similar instances
num_vars, clauses = generate_expander_tseitin(n=12, d=3)
```

## CNF Format

Standard DIMACS CNF format:

```
c Comment line
p cnf <num_vars> <num_clauses>
<literal> <literal> ... 0
...
```

Where:
- Positive integer `i` represents variable xᵢ
- Negative integer `-i` represents ¬xᵢ
- Each line ends with `0`

## Adding New Benchmarks

To add new benchmark instances:

1. Generate CNF formula using the framework:
   ```python
   from src.icq_pnp import generate_low_treewidth_formula
   formula = generate_low_treewidth_formula(n=20)
   # Convert to DIMACS format and save
   ```

2. Or generate Tseitin formulas:
   ```python
   from src.icq_pnp.tseitin_generator import generate_expander_tseitin
   num_vars, clauses = generate_expander_tseitin(n=15, d=4)
   # Convert to DIMACS format and save
   ```

3. Place files in `data/benchmarks/` with descriptive names

## Testing Benchmarks

Run tests on benchmark instances:

```bash
# Run all tests including benchmark validation
pytest tests/ -v

# Or test specific functionality
python -m src.icq_pnp.computational_dichotomy --demo
```

---

**Purpose**: These benchmarks validate the theoretical predictions of the 
computational dichotomy framework through empirical testing.
