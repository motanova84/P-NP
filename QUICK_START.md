# Quick Start Guide

## Installation

### Prerequisites
- Python 3.8 or higher
- pip package manager
- (Optional) Lean 4 for formal verification

### Setup

1. **Clone the repository:**
```bash
git clone https://github.com/motanova84/P-NP.git
cd P-NP
```

2. **Install Python dependencies:**
```bash
pip install -r requirements.txt
```

3. **(Optional) Install Lean 4:**
```bash
# Follow instructions at https://leanprover.github.io/
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## Running Examples

### Python Framework

**Basic demonstration:**
```bash
python computational_dichotomy.py
```

Output will show:
- Low treewidth formula (tractable)
- High treewidth formula (intractable)  
- Structural coupling with expanders
- Non-evasion property

**Comprehensive examples:**
```bash
python examples.py
```

This demonstrates:
- Various formula types (path, tree, grid, clique)
- Tseitin expander construction
- Graph product padding
- No-evasion demonstration
- Complexity comparison

### Interactive Python Usage

```python
from computational_dichotomy import CNF, IncidenceGraph, ComputationalDichotomy

# Create a CNF formula
cnf = CNF(
    variables={1, 2, 3, 4, 5},
    clauses=[
        {1, 2}, {-1, 3}, {2, 3}, {-2, 4}, {3, 5}
    ]
)

# Analyze complexity
result = ComputationalDichotomy.analyze_formula(cnf)

print(f"Treewidth: {result['treewidth']}")
print(f"In P: {result['in_P']}")
print(f"Time complexity: {result['time_complexity']}")
```

### Lean Formalization

```bash
# Build Lean project
lake build

# Check specific theorem
lake env lean computational_dichotomy.lean
```

## Understanding the Output

### Treewidth Analysis

```
treewidth: 5
num_variables: 20
log_n: 4.32
in_P: False
```

**Interpretation:**
- Formula has 20 variables
- Treewidth is 5
- log₂(20) ≈ 4.32
- tw = 5 > O(log 20) ≈ 4.32 → Not in P
- Expected time: 2^Ω(5) ≈ exponential

### Dichotomy Criterion

```
dichotomy_criterion: tw = 5 > O(log 20) = 8.64
```

This shows whether the formula satisfies the P criterion:
- tw ≤ O(log n): Tractable (in P)
- tw > ω(log n): Intractable (not in P)

## Common Use Cases

### 1. Testing if a Formula is Tractable

```python
from computational_dichotomy import CNF, ComputationalDichotomy

# Your formula
cnf = CNF(variables={...}, clauses=[...])

# Quick check
result = ComputationalDichotomy.analyze_formula(cnf)
if result['in_P']:
    print("Formula is tractable - use DP algorithm")
else:
    print("Formula is hard - exponential time required")
```

### 2. Applying Structural Coupling

```python
from computational_dichotomy import StructuralCoupling

# Apply Tseitin expander
expanded = StructuralCoupling.tseitin_expander(cnf, expansion_factor=2.0)

# Apply graph product padding  
padded = StructuralCoupling.graph_product_padding(cnf, factor=3)
```

### 3. Computing Information Complexity

```python
from computational_dichotomy import (
    CommunicationProtocol, StructuralCoupling, IncidenceGraph
)

# Create protocol
protocol = CommunicationProtocol(
    num_parties=2,
    partition={0: {1,2,3}, 1: {4,5,6}},
    complexity=0.0
)

# Compute IC
inc_graph = IncidenceGraph(cnf)
tw = inc_graph.compute_treewidth()
ic = StructuralCoupling.compute_information_complexity(protocol, cnf, tw)

print(f"Information Complexity: {ic:.2f} bits")
```

## Exploring Different Formula Types

### Path Formula (Low Treewidth)
```python
# Chain structure: very tractable
path_cnf = CNF(
    variables=set(range(1, 11)),
    clauses=[{i, i+1} for i in range(1, 10)]
)
```

### Grid Formula (Medium Treewidth)
```python
# 2D grid: moderate complexity
grid_vars = set(range(1, 17))
grid_clauses = []
for i in range(4):
    for j in range(4):
        if j < 3:
            grid_clauses.append({i*4 + j + 1, i*4 + j + 2})
        if i < 3:
            grid_clauses.append({i*4 + j + 1, (i+1)*4 + j + 1})
grid_cnf = CNF(variables=grid_vars, clauses=grid_clauses)
```

### Clique Formula (High Treewidth)
```python
# Complete graph: very hard
clique_vars = set(range(1, 11))
clique_clauses = [
    {i, j} for i in range(1, 11) for j in range(i+1, 11)
]
clique_cnf = CNF(variables=clique_vars, clauses=clique_clauses)
```

## Debugging and Validation

### Verbose Analysis
```python
import networkx as nx
from computational_dichotomy import IncidenceGraph

inc_graph = IncidenceGraph(cnf)

# Inspect graph structure
print(f"Nodes: {inc_graph.graph.number_of_nodes()}")
print(f"Edges: {inc_graph.graph.number_of_edges()}")
print(f"Density: {nx.density(inc_graph.graph):.3f}")

# Compute treewidth with details
tw = inc_graph.compute_treewidth()
print(f"Treewidth: {tw}")
```

### Visualizing Incidence Graphs

```python
import matplotlib.pyplot as plt

# Draw graph
pos = nx.spring_layout(inc_graph.graph)
nx.draw(inc_graph.graph, pos, with_labels=True)
plt.savefig('incidence_graph.png')
```

## Troubleshooting

### Issue: "ModuleNotFoundError: No module named 'networkx'"
**Solution:** Install requirements
```bash
pip install -r requirements.txt
```

### Issue: High memory usage with large formulas
**Solution:** Use sampling or heuristic treewidth computation
```python
# For formulas with > 1000 variables, use heuristic bounds
if cnf.num_variables() > 1000:
    print("Warning: Using heuristic treewidth estimation")
```

### Issue: Lean build fails
**Solution:** Ensure Mathlib is properly installed
```bash
lake update
lake build
```

## Next Steps

1. **Read the documentation:**
   - [KEY_INGREDIENT.md](KEY_INGREDIENT.md) - Core concepts
   - [TECHNICAL_APPENDIX.md](TECHNICAL_APPENDIX.md) - Mathematical details
   - [README.md](README.md) - Overview

2. **Experiment with examples:**
   - Modify `examples.py` with your own formulas
   - Test different expansion factors
   - Compare different formula structures

3. **Contribute:**
   - Add new examples
   - Improve treewidth computation
   - Formal verification in Lean

## Resources

- **Graph Theory:** Understanding treewidth and tree decompositions
- **Information Theory:** Mutual information and communication complexity
- **SAT Solving:** CNF formulas and satisfiability
- **Lean:** Formal verification and theorem proving

## Getting Help

If you encounter issues or have questions:
1. Check existing documentation
2. Review the examples
3. Open an issue on GitHub
4. Consult the references in TECHNICAL_APPENDIX.md

---

**Happy exploring!** 🚀
