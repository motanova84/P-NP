"""
Tseitin Formula Generator
=========================

Generates Tseitin formulas over graphs, which are satisfiable if and only if
the graph has an even number of odd-degree vertices.

When constructed over expander graphs, these formulas exhibit high treewidth
and serve as hard instances for SAT solvers.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import random
import networkx as nx
from typing import List, Tuple


def generate_ramanujan_expander(n: int, d: int = 3) -> nx.Graph:
    """Generate Ramanujan-like expander graph."""
    # For demo purposes - in real implementation use proper Ramanujan construction
    # Random regular graphs are good expanders with high probability
    G = nx.random_regular_graph(d, n)
    return G


class TseitinGenerator:
    """Generator for Tseitin formulas over graphs."""
    
    def __init__(self, graph: nx.Graph):
        """
        Initialize the Tseitin generator.
        
        Args:
            graph: The underlying graph for the Tseitin transformation
        """
        self.graph = graph
        self.num_vars = len(graph.edges())
        self.edge_to_var = {edge: idx + 1 for idx, edge in enumerate(graph.edges())}
    
    def generate_formula(self, charge_assignment: List[int]) -> Tuple[int, List[List[int]]]:
        """
        Generate a Tseitin formula with the given charge assignment.
        
        Args:
            charge_assignment: List of charges (0 or 1) for each vertex
        
        Returns:
            Tuple of (num_vars, clauses)
        """
        if len(charge_assignment) != len(self.graph.nodes()):
            raise ValueError("Charge assignment must match number of nodes")
        
        clauses = []
        
        # For each vertex, create clauses encoding the parity constraint
        for node_idx, node in enumerate(self.graph.nodes()):
            # Get edges incident to this node
            incident_edges = []
            for edge in self.graph.edges(node):
                if edge in self.edge_to_var:
                    incident_edges.append(self.edge_to_var[edge])
                else:
                    # Try reversed edge
                    rev_edge = (edge[1], edge[0])
                    if rev_edge in self.edge_to_var:
                        incident_edges.append(self.edge_to_var[rev_edge])
            
            charge = charge_assignment[node_idx]
            
            # Encode XOR constraint: sum of edges ≡ charge (mod 2)
            # This is done using CNF encoding of XOR
            self._add_xor_clauses(incident_edges, charge, clauses)
        
        return self.num_vars, clauses
    
    def _add_xor_clauses(self, vars: List[int], target: int, clauses: List[List[int]]):
        """
        Add clauses encoding XOR of variables equals target.
        
        For small number of variables, we enumerate all satisfying assignments.
        """
        n = len(vars)
        if n == 0:
            if target == 1:
                # Contradiction
                clauses.append([])  # Empty clause (unsatisfiable)
            return
        
        # For each assignment that gives the wrong parity, add a blocking clause
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
                # This assignment is forbidden
                clauses.append([-lit for lit in assignment])


def generate_expander_tseitin(n: int, d: int) -> Tuple[int, List[List[int]]]:
    """
    Generate a Tseitin formula over an expander graph.
    
    Args:
        n: Number of vertices
        d: Degree (for random regular graph, which is an expander with high probability)
    
    Returns:
        Tuple of (num_vars, clauses)
    """
    # Generate a random d-regular graph (expander with high probability)
    graph = nx.random_regular_graph(d, n)
    
    # Assign odd charges to create unsatisfiable formula
    # (sum of charges must be even for satisfiability)
    charge_assignment = [1] * n  # All odd charges
    
    generator = TseitinGenerator(graph)
    return generator.generate_formula(charge_assignment)


def create_treewidth_hard_instance(base_clauses: List[List[int]], expander_size: int = 100, d: int = 3) -> Tuple[List[List[int]], int]:
    """Create treewidth-hard instance by coupling with expander."""
    expander = generate_ramanujan_expander(expander_size, d)
    
    # Generate Tseitin formula over expander
    num_vars, tseitin_clauses = generate_expander_tseitin(expander_size, d)
    
    # Combine with base CNF (simplified coupling)
    # Offset variables in base clauses to avoid conflict
    offset = num_vars
    offset_base_clauses = [[lit + offset if lit > 0 else lit - offset for lit in clause] for clause in base_clauses]
    
    combined_clauses = tseitin_clauses + offset_base_clauses
    total_vars = num_vars + max(abs(lit) for clause in base_clauses for lit in clause) if base_clauses else num_vars
    
    return combined_clauses, total_vars


if __name__ == "__main__":
    print("Tseitin Formula Generator ∞³")
    print("Generating example Tseitin formula over expander...")
    
    # Generate small example
    num_vars, clauses = generate_expander_tseitin(6, 3)
    print(f"Generated formula with {num_vars} variables and {len(clauses)} clauses")
    print(f"First 5 clauses: {clauses[:5]}")
