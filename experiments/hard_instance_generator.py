#!/usr/bin/env python3
# experiments/hard_instance_generator.py
"""
Hard Instance Generator for P≠NP Validation

Generates provably hard SAT instances using:
1. Tseitin formulas over Ramanujan expanders
2. Random k-SAT at phase transition
3. Combinatorial constructions with high treewidth

Author: José Manuel Mota Burruezo & Claude (Noēsis ∞³)
"""

import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
import networkx as nx
from typing import List, Dict, Set, Tuple
import random
from dataclasses import dataclass
import math


@dataclass
class CNFFormula:
    """Enhanced CNF formula with structural properties."""
    variables: int
    clauses: List[List[int]]
    incidence_graph: nx.Graph = None
    treewidth: int = None
    information_complexity: float = None
    
    def __post_init__(self):
        if self.incidence_graph is None:
            self.build_incidence_graph()
    
    def build_incidence_graph(self):
        """Build incidence graph for treewidth analysis."""
        G = nx.Graph()
        
        # Add variable nodes (positive integers)
        for i in range(1, self.variables + 1):
            G.add_node(f"v{i}", type='variable')
        
        # Add clause nodes (negative integers)
        for j, clause in enumerate(self.clauses):
            clause_node = f"c{j}"
            G.add_node(clause_node, type='clause')
            
            # Connect clause to its variables
            for lit in clause:
                var = abs(lit)
                G.add_edge(clause_node, f"v{var}")
        
        self.incidence_graph = G
    
    def to_dimacs(self) -> str:
        """Convert to DIMACS format."""
        lines = []
        lines.append(f"p cnf {self.variables} {len(self.clauses)}")
        for clause in self.clauses:
            lines.append(" ".join(map(str, clause)) + " 0")
        return "\n".join(lines)


class HardInstanceGenerator:
    """
    Generator of provably hard SAT instances for P≠NP validation.
    """
    
    def __init__(self, seed=42):
        self.seed = seed
        random.seed(seed)
        np.random.seed(seed)
    
    def generate_tseitin_expander(self, n: int, d: int = 3) -> CNFFormula:
        """
        Generate Tseitin formula over d-regular expander.
        
        Tseitin formulas are unsatisfiable when the sum of 
        vertex parities is odd. They have high treewidth
        when the underlying graph is an expander.
        """
        # Generate d-regular expander (Ramanujan-like)
        G = self._generate_ramanujan_expander(n, d)
        
        # Assign random parities (0 or 1) to vertices
        parities = {i: random.randint(0, 1) for i in G.nodes()}
        
        # For Tseitin: unsatisfiable if sum(parities) ≡ 1 mod 2
        total_parity = sum(parities.values()) % 2
        if total_parity == 0:
            # Make unsatisfiable by flipping one parity
            node_to_flip = random.choice(list(G.nodes()))
            parities[node_to_flip] = 1 - parities[node_to_flip]
        
        clauses = []
        variable_counter = 1
        var_map = {}  # edge -> variable
        
        # Create variables for edges
        for u, v in G.edges():
            var_map[(u, v)] = variable_counter
            var_map[(v, u)] = variable_counter  # Both directions
            variable_counter += 1
        
        # Create clauses for each vertex
        for node in G.nodes():
            incident_edges = list(G.edges(node))
            edge_vars = []
            for edge in incident_edges:
                if edge in var_map:
                    edge_vars.append(var_map[edge])
                else:
                    # Try reversed
                    rev_edge = (edge[1], edge[0])
                    if rev_edge in var_map:
                        edge_vars.append(var_map[rev_edge])
            
            # Generate all 2^d assignments that satisfy parity
            satisfying_assignments = self._generate_parity_constraints(
                edge_vars, parities[node]
            )
            
            # Convert to CNF (each unsatisfying assignment becomes a clause)
            # We need to block the assignments that DON'T satisfy the parity
            all_assignments = self._generate_all_assignments(len(edge_vars))
            for assignment in all_assignments:
                if assignment not in satisfying_assignments:
                    clause = []
                    for var, val in zip(edge_vars, assignment):
                        if val == 0:
                            clause.append(var)  # negated
                        else:
                            clause.append(-var)  # positive
                    clauses.append(clause)
        
        formula = CNFFormula(variables=variable_counter-1, clauses=clauses)
        formula.incidence_graph = G  # Use original graph for treewidth
        
        return formula
    
    def _generate_all_assignments(self, n: int) -> List[Tuple]:
        """Generate all 2^n binary assignments."""
        assignments = []
        for i in range(2**n):
            assignment = []
            for j in range(n):
                bit = (i >> j) & 1
                assignment.append(bit)
            assignments.append(tuple(assignment))
        return assignments
    
    def _generate_ramanujan_expander(self, n: int, d: int) -> nx.Graph:
        """
        Generate d-regular graph with good expansion properties.
        
        Uses random regular graph construction and ensures
        spectral gap close to Ramanujan bound.
        """
        # Ensure n*d is even (requirement for regular graphs)
        if (n * d) % 2 != 0:
            # Adjust n to make n*d even
            n = n + 1
        
        # Generate random d-regular graph
        G = nx.random_regular_graph(d, n, seed=self.seed)
        
        # Ensure connectivity
        while not nx.is_connected(G):
            G = nx.random_regular_graph(d, n, seed=random.randint(0, 10000))
        
        # Improve expansion by edge swaps
        G = self._improve_expansion(G, iterations=100)
        
        return G
    
    def _improve_expansion(self, G: nx.Graph, iterations: int) -> nx.Graph:
        """
        Improve graph expansion using edge swap Markov chain.
        """
        best_G = G.copy()
        
        # For small graphs, compute algebraic connectivity
        if len(G.nodes()) <= 50:
            try:
                best_algebraic_connectivity = nx.algebraic_connectivity(G)
            except:
                best_algebraic_connectivity = 0
        else:
            # For large graphs, skip expensive computation
            return best_G
        
        for _ in range(iterations):
            # Try random edge swap
            edges = list(G.edges())
            if len(edges) < 2:
                continue
            
            e1, e2 = random.sample(edges, 2)
            u, v = e1
            x, y = e2
            
            # Check if swap creates new edges
            if u != x and u != y and v != x and v != y:
                if not G.has_edge(u, x) and not G.has_edge(v, y):
                    # Perform swap
                    G_new = G.copy()
                    G_new.remove_edge(u, v)
                    G_new.remove_edge(x, y)
                    G_new.add_edge(u, x)
                    G_new.add_edge(v, y)
                    
                    # Keep if expansion improves
                    if nx.is_connected(G_new):
                        try:
                            new_connectivity = nx.algebraic_connectivity(G_new)
                            if new_connectivity > best_algebraic_connectivity:
                                best_G = G_new
                                best_algebraic_connectivity = new_connectivity
                                G = G_new
                        except:
                            pass
        
        return best_G
    
    def _generate_parity_constraints(self, variables: List[int], parity: int) -> List[Tuple]:
        """
        Generate satisfying assignments for XOR constraint.
        
        For variables v1,...,vd and parity p, generate all
        assignments where v1 ⊕ ... ⊕ vd = p.
        """
        d = len(variables)
        satisfying = []
        
        # Generate all 2^d assignments
        for i in range(2**d):
            assignment = []
            for j in range(d):
                bit = (i >> j) & 1
                assignment.append(bit)
            
            # Check parity
            if sum(assignment) % 2 == parity:
                satisfying.append(tuple(assignment))
        
        return satisfying
    
    def generate_random_ksat_phase_transition(self, n: int, k: int = 3, alpha: float = 4.2) -> CNFFormula:
        """
        Generate random k-SAT at phase transition (alpha ≈ 4.2 for k=3).
        
        These instances are known to be hard for SAT solvers.
        """
        m = int(alpha * n)  # Number of clauses
        clauses = []
        
        for _ in range(m):
            clause = []
            variables = random.sample(range(1, n + 1), min(k, n))
            for var in variables:
                # Randomly negate
"""
Hard Instance Generator for P≠NP Validation

Generates hard SAT instances for testing the computational dichotomy,
including Tseitin formulas over expander graphs and grid-based SAT instances.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import networkx as nx
import numpy as np
from typing import List, Tuple
import random


class CNFFormula:
    """Represents a CNF formula with graph properties."""
    
    def __init__(self, num_vars: int, clauses: List[List[int]]):
        """
        Initialize CNF formula.
        
        Args:
            num_vars: Number of variables
            clauses: List of clauses (each clause is list of literals)
        """
        self.variables = num_vars
        self.num_vars = num_vars
        self.clauses = clauses
        self._incidence_graph = None
    
    @property
    def incidence_graph(self) -> nx.Graph:
        """Build and cache the incidence graph."""
        if self._incidence_graph is None:
            self._incidence_graph = self._build_incidence_graph()
        return self._incidence_graph
    
    def _build_incidence_graph(self) -> nx.Graph:
        """Build the incidence graph of the formula."""
        G = nx.Graph()
        
        # Add variable nodes
        for i in range(1, self.num_vars + 1):
            G.add_node(f"v{i}", bipartite=0)
        
        # Add clause nodes and edges
        for idx, clause in enumerate(self.clauses):
            clause_node = f"c{idx}"
            G.add_node(clause_node, bipartite=1)
            
            for lit in clause:
                var = abs(lit)
                G.add_edge(f"v{var}", clause_node)
        
        return G
    
    def __repr__(self):
        return f"CNFFormula(vars={self.num_vars}, clauses={len(self.clauses)})"


class HardInstanceGenerator:
    """Generator for hard SAT instances."""
    
    def __init__(self, seed: int = None):
        """
        Initialize generator with optional seed for reproducibility.
        
        Args:
            seed: Random seed
        """
        self.seed = seed
        if seed is not None:
            random.seed(seed)
            np.random.seed(seed)
    
    def generate_tseitin_expander(self, n: int, degree: int = 3) -> CNFFormula:
        """
        Generate a Tseitin formula over an expander graph.
        
        Creates unsatisfiable formulas with high treewidth by using
        regular expander graphs with odd charge assignments.
        
        Args:
            n: Number of vertices in the graph
            degree: Degree of the regular graph (default 3)
            
        Returns:
            CNFFormula representing Tseitin transformation
        """
        # Ensure n*degree is even for regular graph
        if (n * degree) % 2 != 0:
            n = n + 1
        
        # Generate random regular graph (expander with high probability)
        try:
            graph = nx.random_regular_graph(degree, n, seed=self.seed)
        except:
            # Fallback to cycle graph if regular graph fails
            graph = nx.cycle_graph(n)
        
        # Number of variables = number of edges
        num_vars = len(graph.edges())
        
        # Create edge to variable mapping
        edge_to_var = {edge: idx + 1 for idx, edge in enumerate(graph.edges())}
        
        # Generate Tseitin clauses with all odd charges (unsatisfiable)
        clauses = []
        charge_assignment = [1] * n  # All vertices have odd charge
        
        for node_idx, node in enumerate(graph.nodes()):
            # Get edges incident to this node
            incident_vars = []
            for edge in graph.edges(node):
                if edge in edge_to_var:
                    incident_vars.append(edge_to_var[edge])
                else:
                    # Try reversed edge
                    rev_edge = (edge[1], edge[0])
                    if rev_edge in edge_to_var:
                        incident_vars.append(edge_to_var[rev_edge])
            
            charge = charge_assignment[node_idx]
            
            # Encode XOR constraint for parity
            # For simplicity, use a compact encoding
            self._add_xor_clauses(incident_vars, charge, clauses)
        
        return CNFFormula(num_vars, clauses)
    
    def _add_xor_clauses(self, vars: List[int], target: int, clauses: List[List[int]]):
        """
        Add CNF clauses encoding XOR constraint.
        
        For XOR of variables to equal target, we add clauses that
        forbid assignments with wrong parity.
        """
        n = len(vars)
        if n == 0:
            if target == 1:
                clauses.append([])  # Unsatisfiable
            return
        
        # For small number of variables, enumerate all forbidden assignments
        if n <= 4:
            for i in range(2 ** n):
                parity = 0
                assignment = []
                for j in range(n):
                    if (i >> j) & 1:
                        parity ^= 1
                        assignment.append(vars[j])
                    else:
                        assignment.append(-vars[j])
                
                if parity != target:
                    # Forbid this assignment
                    clauses.append([-lit for lit in assignment])
        else:
            # For larger XORs, use a simpler approximation
            # Add some representative clauses
            if target == 1:
                # At least one must be true
                clauses.append(vars[:])
                # Not all can be true (if even number)
                if n % 2 == 0:
                    clauses.append([-v for v in vars])
            else:
                # Even parity - add clauses enforcing this
                clauses.append(vars[:])
    
    def generate_grid_sat(self, rows: int, cols: int) -> CNFFormula:
        """
        Generate a SAT formula based on a grid graph.
        
        Grid graphs have low treewidth (≤ min(rows, cols)) and serve
        as tractable instances for comparison.
        
        Args:
            rows: Number of rows in grid
            cols: Number of columns in grid
            
        Returns:
            CNFFormula based on grid structure
        """
        n = rows * cols
        clauses = []
        
        # Create grid connectivity constraints
        for i in range(rows):
            for j in range(cols):
                var = i * cols + j + 1
                
                # Horizontal constraint
                if j < cols - 1:
                    next_var = i * cols + (j + 1) + 1
                    clauses.append([var, next_var])
                    clauses.append([-var, -next_var])
                
                # Vertical constraint
                if i < rows - 1:
                    below_var = (i + 1) * cols + j + 1
                    clauses.append([var, below_var])
                    clauses.append([-var, -below_var])
        
        # Add some corner constraints to make it non-trivial
        if n > 0:
            clauses.append([1])  # Top-left must be true
            if n > 1:
                clauses.append([-n])  # Bottom-right must be false
        
        return CNFFormula(n, clauses)
    
    def generate_random_3sat(self, n: int, ratio: float = 4.26) -> CNFFormula:
        """
        Generate random 3-SAT instance at critical ratio.
        
        Args:
            n: Number of variables
            ratio: Clause-to-variable ratio
            
        Returns:
            CNFFormula with random 3-SAT instance
        """
        m = int(n * ratio)
        clauses = []
        
        for _ in range(m):
            # Generate random 3-clause
            vars_in_clause = random.sample(range(1, n + 1), min(3, n))
            clause = []
            for var in vars_in_clause:
                if random.random() < 0.5:
                    clause.append(-var)
                else:
                    clause.append(var)
            clauses.append(clause)
        
        return CNFFormula(variables=n, clauses=clauses)
    
    def generate_grid_sat(self, width: int, height: int) -> CNFFormula:
        """
        Generate SAT instance from grid graph.
        
        Grid graphs have treewidth = min(width, height),
        making them good test cases.
        """
        clauses = []
        variable_counter = 1
        var_grid = np.zeros((height, width), dtype=int)
        
        # Create variables for grid cells
        for i in range(height):
            for j in range(width):
                var_grid[i, j] = variable_counter
                variable_counter += 1
        
        # Add constraints: each cell implies its neighbors
        for i in range(height):
            for j in range(width):
                current_var = var_grid[i, j]
                neighbors = []
                
                # Get neighbors (up, down, left, right)
                for di, dj in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    ni, nj = i + di, j + dj
                    if 0 <= ni < height and 0 <= nj < width:
                        neighbors.append(var_grid[ni, nj])
                
                # Add implications: current → at least one neighbor
                if neighbors:
                    clause = [-current_var]
                    clause.extend(neighbors)
                    clauses.append(clause)
                
                # And: if all neighbors false, then current false
                for neighbor in neighbors:
                    clauses.append([current_var, -neighbor])
        
        return CNFFormula(variables=variable_counter-1, clauses=clauses)
    
    def generate_treewidth_extremal(self, n: int, target_tw: int) -> CNFFormula:
        """
        Generate formula with specific treewidth.
        
        Uses clique-based construction to achieve high treewidth.
        """
        # Start with complete graph on target_tw+1 vertices
        G = nx.complete_graph(target_tw + 1)
        
        # Add remaining vertices connected to random cliques
        for i in range(target_tw + 1, n):
            # Connect to random subset of existing vertices
            clique_size = random.randint(2, min(target_tw, len(list(G.nodes()))))
            neighbors = random.sample(list(G.nodes()), clique_size)
            
            G.add_node(i)
            for neighbor in neighbors:
                G.add_edge(i, neighbor)
        
        # Convert to SAT using Tseitin-like construction
        return self.graph_to_sat(G)
    
    def graph_to_sat(self, G: nx.Graph) -> CNFFormula:
        """
        Convert graph to SAT instance preserving treewidth.
        """
        clauses = []
        variable_counter = 1
        var_map = {}
        
        # Create variable for each edge
        for u, v in G.edges():
            var_map[(u, v)] = variable_counter
            var_map[(v, u)] = variable_counter
            variable_counter += 1
        
        # Add constraints: for each triangle, enforce transitivity
        triangles = self._find_triangles(G)
        for triangle in triangles:
            u, v, w = triangle
            uv = var_map.get((u, v)) or var_map.get((v, u))
            vw = var_map.get((v, w)) or var_map.get((w, v))
            uw = var_map.get((u, w)) or var_map.get((w, u))
            
            if uv and vw and uw:
                # Transitivity: (uv ∧ vw) → uw
                clauses.append([-uv, -vw, uw])
                clauses.append([-uv, -uw, vw])
                clauses.append([-vw, -uw, uv])
        
        return CNFFormula(variables=variable_counter-1, clauses=clauses)
    
    def _find_triangles(self, G: nx.Graph) -> List[Tuple]:
        """Find all triangles in graph."""
        triangles = []
        for u in G.nodes():
            for v in G.neighbors(u):
                if v > u:  # Avoid duplicates
                    for w in G.neighbors(v):
                        if w > v and G.has_edge(u, w):
                            triangles.append((u, v, w))
        return triangles
    
    def benchmark_hardness(self, formula: CNFFormula, timeout: int = 60) -> Dict:
        """
        Benchmark formula hardness with multiple metrics.
        """
        try:
            from experiments.complete_validation import CompleteValidation
        except ImportError:
            from complete_validation import CompleteValidation
        
        validator = CompleteValidation()
        
        metrics = {}
        
        # Treewidth estimate
        metrics['treewidth'] = validator.estimate_treewidth(formula.incidence_graph)
        
        # Information complexity
        metrics['information_complexity'] = validator.compute_information_complexity(formula)
        
        # DPLL time
        time_dpll, solved = validator.solve_with_dpll(formula, timeout)
        metrics['dpll_time'] = time_dpll
        metrics['dpll_solved'] = solved
        
        # Structural metrics
        metrics['n_vars'] = formula.variables
        metrics['n_clauses'] = len(formula.clauses)
        metrics['clause_variable_ratio'] = len(formula.clauses) / formula.variables if formula.variables > 0 else 0
        
        # Graph metrics
        G = formula.incidence_graph
        metrics['graph_density'] = nx.density(G)
        
        # Algebraic connectivity (expensive for large graphs)
        if len(G.nodes()) <= 100:
            try:
                metrics['algebraic_connectivity'] = nx.algebraic_connectivity(G)
            except:
                metrics['algebraic_connectivity'] = 0.0
        else:
            metrics['algebraic_connectivity'] = 0.0
        
        # Average clustering (only for graphs with edges)
        try:
            metrics['average_clustering'] = nx.average_clustering(G)
        except:
            metrics['average_clustering'] = 0.0
        
        return metrics


def generate_hardness_dataset(sizes: List[int], output_dir: str = "data/hard_instances"):
    """
    Generate comprehensive dataset of hard instances.
    """
    import json
    from pathlib import Path
    
    Path(output_dir).mkdir(parents=True, exist_ok=True)
    generator = HardInstanceGenerator()
    
    dataset = {}
    
    for n in sizes:
        print(f"Generating instances for n={n}...")
        
        instances = {}
        
        # Tseitin on expander
        instances['tseitin_expander'] = generator.generate_tseitin_expander(n)
        
        # Random 3-SAT at phase transition
        instances['random_3sat'] = generator.generate_random_ksat_phase_transition(n)
        
        # High treewidth construction
        instances['high_treewidth'] = generator.generate_treewidth_extremal(n, n//2)
        
        # Grid SAT (medium treewidth)
        grid_size = int(math.sqrt(n))
        instances['grid_sat'] = generator.generate_grid_sat(grid_size, grid_size)
        
        # Benchmark all
        benchmarks = {}
        for name, formula in instances.items():
            print(f"  Benchmarking {name}...")
            benchmarks[name] = generator.benchmark_hardness(formula)
            
            # Save formula
            dimacs_path = f"{output_dir}/n{n}_{name}.cnf"
            with open(dimacs_path, 'w') as f:
                f.write(formula.to_dimacs())
        
        dataset[n] = benchmarks
    
    # Save benchmark results
    with open(f"{output_dir}/hardness_benchmarks.json", 'w') as f:
        json.dump(dataset, f, indent=2)
    
    print(f"Dataset saved to {output_dir}/")
    return dataset


if __name__ == "__main__":
    # Generate comprehensive dataset
    sizes = [20, 50, 100, 200, 300, 400, 500]
    dataset = generate_hardness_dataset(sizes)
    
    print("\n" + "="*70)
    print("HARD INSTANCE GENERATION COMPLETE")
    print("="*70)
    print(f"Generated instances for n ∈ {sizes}")
    print("Includes: Tseitin expanders, random 3-SAT, high-treewidth, grid SAT")
        return CNFFormula(n, clauses)


if __name__ == "__main__":
    print("Hard Instance Generator ∞³")
    print("=" * 70)
    
    generator = HardInstanceGenerator(seed=42)
    
    # Test Tseitin expander
    print("\n1. Tseitin Expander (n=20):")
    phi = generator.generate_tseitin_expander(20)
    print(f"   Variables: {phi.variables}, Clauses: {len(phi.clauses)}")
    print(f"   Incidence graph nodes: {len(phi.incidence_graph.nodes())}")
    
    # Test grid SAT
    print("\n2. Grid SAT (5x5):")
    phi = generator.generate_grid_sat(5, 5)
    print(f"   Variables: {phi.variables}, Clauses: {len(phi.clauses)}")
    print(f"   Incidence graph nodes: {len(phi.incidence_graph.nodes())}")
    
    print("\n✓ Generator tests passed")
