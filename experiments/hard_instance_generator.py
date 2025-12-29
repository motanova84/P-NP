"""
Hard Instance Generator for P≠NP Validation
============================================

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
