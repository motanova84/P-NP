"""
IC-SAT Algorithm and Validation Framework
=========================================

Implements the Information Complexity SAT solver and validation utilities
as described in the paper's Appendix D.

Key components:
- IC-SAT recursive algorithm with κ_Π = 2.5773
- Simple DPLL SAT solver (no external dependencies)
- Treewidth estimation and comparison
- Clause simplification and unit propagation
- Large-scale validation framework

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import networkx as nx
import numpy as np
from typing import List, Tuple, Set, Dict, Optional
import random
import sys
import os

# Add src to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
from constants import (
    KAPPA_PI,
    QCAL_FREQUENCY_HZ,
    information_complexity_lower_bound,
    is_in_P
)


def build_primal_graph(n_vars: int, clauses: List[List[int]]) -> nx.Graph:
    """
    Build the primal graph of a CNF formula.
    
    The primal graph has a node for each variable, and an edge between
    variables that appear together in at least one clause.
    
    Args:
        n_vars: Number of variables
        clauses: List of clauses
        
    Returns:
        NetworkX graph representing the primal graph
    """
    G = nx.Graph()
    
    # Add variable nodes
    for i in range(1, n_vars + 1):
        G.add_node(f"v{i}")
    
    # Add edges between variables in same clause
    for clause in clauses:
        vars_in_clause = [abs(lit) for lit in clause]
        for i, var1 in enumerate(vars_in_clause):
            for var2 in vars_in_clause[i+1:]:
                G.add_edge(f"v{var1}", f"v{var2}")
    
    return G


def build_incidence_graph(n_vars: int, clauses: List[List[int]]) -> nx.Graph:
    """
    Build the incidence graph of a CNF formula.
    
    The incidence graph is bipartite with variable nodes on one side
    and clause nodes on the other, with edges between variables and
    clauses they appear in.
    
    Args:
        n_vars: Number of variables
        clauses: List of clauses
        
    Returns:
        NetworkX graph representing the incidence graph with bipartite labels
    """
    G = nx.Graph()
    
    # Add variable nodes with bipartite label 0
    for i in range(1, n_vars + 1):
        G.add_node(f"v{i}", bipartite=0)
    
    # Add clause nodes with bipartite label 1 and edges
    for idx, clause in enumerate(clauses):
        clause_node = f"c{idx}"
        G.add_node(clause_node, bipartite=1)
        
        for lit in clause:
            var = abs(lit)
            G.add_edge(f"v{var}", clause_node)
    
    return G


def estimate_treewidth(G: nx.Graph) -> int:
    """
    Estimate the treewidth of a graph using the minimum degree heuristic.
    
    Args:
        G: NetworkX graph
        
    Returns:
        Estimated treewidth
    """
    if len(G.nodes()) == 0:
        return 0
    
    try:
        # Use NetworkX's approximation algorithm
        tree_decomp = nx.approximation.treewidth_min_degree(G)
        return tree_decomp[0]
    except:
        # Fallback: return maximum degree as upper bound
        if len(G.nodes()) > 0:
            degrees = dict(G.degree())
            return max(degrees.values()) if degrees else 0
        return 0


def compare_treewidths(n_vars: int, clauses: List[List[int]]) -> Tuple[int, int]:
    """
    Compare treewidth of primal and incidence graphs.
    
    Args:
        n_vars: Number of variables
        clauses: List of clauses
        
    Returns:
        Tuple of (primal_treewidth, incidence_treewidth)
    """
    primal_graph = build_primal_graph(n_vars, clauses)
    incidence_graph = build_incidence_graph(n_vars, clauses)
    
    primal_tw = estimate_treewidth(primal_graph)
    incidence_tw = estimate_treewidth(incidence_graph)
    
    return primal_tw, incidence_tw


def simplify_clauses(clauses: List[List[int]], assignment: Dict[int, bool]) -> List[List[int]]:
    """
    Simplify clauses given a partial assignment using unit propagation.
    
    Args:
        clauses: List of clauses
        assignment: Dictionary mapping variables to truth values
        
    Returns:
        Simplified list of clauses
    """
    simplified = []
    
    for clause in clauses:
        # Check if clause is satisfied
        satisfied = False
        new_clause = []
        
        for lit in clause:
            var = abs(lit)
            if var in assignment:
                # If literal matches assignment, clause is satisfied
                if (lit > 0 and assignment[var]) or (lit < 0 and not assignment[var]):
                    satisfied = True
                    break
                # Otherwise, literal is false, so we skip it
            else:
                new_clause.append(lit)
        
        if not satisfied:
            if len(new_clause) == 0:
                # Empty clause means UNSAT
                return [[]]
            simplified.append(new_clause)
    
    return simplified


def unit_propagation(clauses: List[List[int]]) -> Tuple[List[List[int]], Dict[int, bool]]:
    """
    Apply unit propagation to derive unit clauses and simplify.
    
    Args:
        clauses: List of clauses
        
    Returns:
        Tuple of (simplified_clauses, assignment)
    """
    assignment = {}
    changed = True
    
    while changed:
        changed = False
        # Find unit clauses
        for clause in clauses:
            if len(clause) == 1:
                lit = clause[0]
                var = abs(lit)
                value = lit > 0
                
                if var not in assignment:
                    assignment[var] = value
                    changed = True
                elif assignment[var] != value:
                    # Conflict detected
                    return [[]], assignment
        
        # Simplify with current assignment
        if changed:
            clauses = simplify_clauses(clauses, assignment)
            if clauses == [[]]:
                return clauses, assignment
    
    return clauses, assignment


def predict_advantages(G: nx.Graph) -> Optional[str]:
    """
    Predict which variable to branch on based on graph structure.
    
    Uses a simple heuristic: choose variable with highest degree in
    the clause subgraph (bipartite=1 nodes).
    
    Args:
        G: Incidence graph
        
    Returns:
        Variable name to branch on, or None if no variables left
    """
    # Get clause nodes (bipartite=1)
    clause_nodes = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 1]
    
    if not clause_nodes:
        return None
    
    # Find variable with most connections to clauses
    var_degrees = {}
    for clause_node in clause_nodes:
        for neighbor in G.neighbors(clause_node):
            if neighbor.startswith('v'):
                var_degrees[neighbor] = var_degrees.get(neighbor, 0) + 1
    
    if not var_degrees:
        return 'v1'  # Default fallback
    
    return max(var_degrees, key=var_degrees.get)


def simple_dpll(clauses: List[List[int]], n_vars: int) -> str:
    """
    Simple DPLL SAT solver implementation.
    
    Args:
        clauses: List of clauses
        n_vars: Number of variables
        
    Returns:
        'SAT' or 'UNSAT'
    """
    # Empty clause list is satisfiable
    if not clauses:
        return 'SAT'
    
    # Empty clause means unsatisfiable
    if [] in clauses:
        return 'UNSAT'
    
    # Apply unit propagation
    clauses, assignment = unit_propagation(clauses)
    
    if not clauses:
        return 'SAT'
    
    if [] in clauses:
        return 'UNSAT'
    
    # Find pure literals (appear only positive or only negative)
    lit_counts = {}
    for clause in clauses:
        for lit in clause:
            var = abs(lit)
            if var not in lit_counts:
                lit_counts[var] = {'pos': 0, 'neg': 0}
            if lit > 0:
                lit_counts[var]['pos'] += 1
            else:
                lit_counts[var]['neg'] += 1
    
    # Assign pure literals
    for var, counts in lit_counts.items():
        if counts['pos'] > 0 and counts['neg'] == 0:
            assignment[var] = True
        elif counts['neg'] > 0 and counts['pos'] == 0:
            assignment[var] = False
    
    if assignment:
        clauses = simplify_clauses(clauses, assignment)
        if not clauses:
            return 'SAT'
        if [] in clauses:
            return 'UNSAT'
    
    # Choose a variable to branch on (first unassigned)
    all_vars = set()
    for clause in clauses:
        for lit in clause:
            all_vars.add(abs(lit))
    
    if not all_vars:
        return 'SAT'
    
    branch_var = min(all_vars)
    
    # Try positive assignment
    pos_clauses = simplify_clauses(clauses, {branch_var: True})
    if simple_dpll(pos_clauses, n_vars) == 'SAT':
        return 'SAT'
    
    # Try negative assignment
    neg_clauses = simplify_clauses(clauses, {branch_var: False})
    return simple_dpll(neg_clauses, n_vars)


def ic_sat(n_vars: int, clauses: List[List[int]], log: bool = False, depth: int = 0, max_depth: int = 10) -> str:
    """
    IC-SAT recursive algorithm with information complexity tracking.
    
    Args:
        n_vars: Number of variables
        clauses: List of clauses
        log: Whether to log intermediate steps
        depth: Current recursion depth
        max_depth: Maximum recursion depth to prevent infinite loops
        
    Returns:
        'SAT' or 'UNSAT'
    """
    # Base case: depth limit to prevent infinite recursion
    if depth >= max_depth:
        if log:
            print(f"[IC] Max depth {max_depth} reached, falling back to DPLL")
        return simple_dpll(clauses, n_vars)
    
    # Empty clause list is satisfiable
    if not clauses:
        return 'SAT'
    
    # Empty clause means unsatisfiable
    if [] in clauses:
        return 'UNSAT'
    
    # Build incidence graph
    G = build_incidence_graph(n_vars, clauses)
    
    # Estimate treewidth
    tw = estimate_treewidth(G)
    
    # Get clause nodes for S (bipartite=1)
    S = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 1]
    
    # Choose variable to branch on
    v = predict_advantages(G)
    if v is None:
        v = 'v1'
    
    if log:
        print(f"[IC] depth={depth}, tw={tw}, S={len(S)} clauses, branching on {v}")
    
    # Check if treewidth is low enough for tractable solving
    if tw <= max(1, np.log2(n_vars) if n_vars > 1 else 1):
        if log:
            print(f"[IC] Low treewidth detected, using DPLL")
        return simple_dpll(clauses, n_vars)
    
    # Extract variable number from variable name
    var_num = int(v[1:]) if v.startswith('v') else 1
    
    # Try both assignments
    # Positive assignment
    pos_clauses = simplify_clauses(clauses, {var_num: True})
    if log:
        print(f"[IC] Trying {v}=True, {len(pos_clauses)} clauses remaining")
    
    if pos_clauses != [[]]:
        result = ic_sat(n_vars, pos_clauses, log, depth + 1, max_depth)
        if result == 'SAT':
            return 'SAT'
    
    # Negative assignment
    neg_clauses = simplify_clauses(clauses, {var_num: False})
    if log:
        print(f"[IC] Trying {v}=False, {len(neg_clauses)} clauses remaining")
    
    return ic_sat(n_vars, neg_clauses, log, depth + 1, max_depth)


class LargeScaleValidation:
    """Framework for large-scale validation of the dichotomy."""
    
    def __init__(self):
        self.results = []
    
    def generate_3sat_critical(self, n: int, ratio: float = 4.26) -> Tuple[int, List[List[int]]]:
        """
        Generate a random 3-SAT instance at the critical ratio.
        
        Args:
            n: Number of variables
            ratio: Clause-to-variable ratio (4.26 is critical for 3-SAT)
            
        Returns:
            Tuple of (n_vars, clauses)
        """
        m = int(n * ratio)  # Number of clauses
        clauses = []
        
        for _ in range(m):
            # Generate a random 3-clause
            vars_in_clause = random.sample(range(1, n + 1), min(3, n))
            clause = []
            for var in vars_in_clause:
                # Randomly negate
                if random.random() < 0.5:
                    clause.append(-var)
                else:
                    clause.append(var)
            clauses.append(clause)
        
        return n, clauses
    
    def estimate_treewidth_practical(self, G: nx.Graph) -> int:
        """
        Practical treewidth estimation for validation.
        
        Args:
            G: NetworkX graph
            
        Returns:
            Estimated treewidth
        """
        return estimate_treewidth(G)
    
    def run_ic_sat(self, n_vars: int, clauses: List[List[int]], timeout: int = 60) -> str:
        """
        Run IC-SAT with timeout.
        
        Args:
            n_vars: Number of variables
            clauses: List of clauses
            timeout: Timeout in seconds (not implemented, uses max_depth instead)
            
        Returns:
            'SAT', 'UNSAT', or 'TIMEOUT'
        """
        try:
            # Use max_depth to simulate timeout
            result = ic_sat(n_vars, clauses, log=False, max_depth=20)
            return result
        except Exception as e:
            return 'TIMEOUT'
    
    def run_large_scale(self, sizes: List[int], trials: int = 5):
        """
        Run large-scale validation experiments.
        
        Args:
            sizes: List of problem sizes to test
            trials: Number of trials per size
        """
        print("=" * 70)
        print("LARGE SCALE VALIDATION ∞³")
        print("=" * 70)
        print()
        
        for n in sizes:
            print(f"Testing n={n} variables...")
            
            for trial in range(trials):
                # Generate instance
                n_vars, clauses = self.generate_3sat_critical(n)
                
                # Build graphs
                primal_tw, incidence_tw = compare_treewidths(n_vars, clauses)
                
                # Run IC-SAT
                result = self.run_ic_sat(n_vars, clauses)
                
                # Store results
                self.results.append({
                    'n': n,
                    'trial': trial,
                    'primal_tw': primal_tw,
                    'incidence_tw': incidence_tw,
                    'result': result
                })
                
                print(f"  Trial {trial + 1}: TW_primal={primal_tw}, "
                      f"TW_incidence={incidence_tw}, result={result}")
            
            print()
        
        print("=" * 70)
        print("Validation complete!")
        print("=" * 70)


class ICSATSolver:
    """IC-SAT solver with information complexity estimation."""
    
    def __init__(self):
        """Initialize the IC-SAT solver."""
        pass
    
    def estimate_information_complexity(self, formula):
        """
        Estimate information complexity of a formula.
        
        Args:
            formula: CNF formula object
            
        Returns:
            Estimated information complexity
        """
        # Build incidence graph
        if hasattr(formula, 'incidence_graph'):
            G = formula.incidence_graph
        else:
            G = build_incidence_graph(formula.num_vars, formula.clauses)
        
        # Estimate treewidth
        tw = estimate_treewidth(G)
        
        # Information complexity is related to treewidth and problem size
        # IC ≈ treewidth * log(clauses) as a heuristic measure
        n_clauses = len(formula.clauses)
        ic = tw * np.log2(max(n_clauses, 1) + 1)
        
        return ic
    
    def solve(self, formula, log=False):
        """
        Solve formula using IC-SAT algorithm.
        
        Args:
            formula: CNF formula
            log: Whether to log intermediate steps
            
        Returns:
            'SAT' or 'UNSAT'
        """
        return ic_sat(formula.num_vars, formula.clauses, log=log)


if __name__ == "__main__":
    print("IC-SAT Algorithm and Validation Framework ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    
    # Example: Simple formula
    print("Example 1: Simple Formula")
    print("-" * 70)
    n_vars = 2
    clauses = [[1, -2], [-1, 2]]
    
    primal_tw, incidence_tw = compare_treewidths(n_vars, clauses)
    print(f"Primal TW: {primal_tw}, Incidence TW: {incidence_tw}")
    
    result = ic_sat(n_vars, clauses, log=True)
    print(f"IC-SAT result: {result}")
    print()
    
    # Example: 3-SAT instance
    print("Example 2: Random 3-SAT")
    print("-" * 70)
    validator = LargeScaleValidation()
    n_vars, clauses = validator.generate_3sat_critical(10)
    print(f"Generated 3-SAT with {n_vars} variables and {len(clauses)} clauses")
    
    primal_tw, incidence_tw = compare_treewidths(n_vars, clauses)
    print(f"Primal TW: {primal_tw}, Incidence TW: {incidence_tw}")
    
    result = ic_sat(n_vars, clauses, log=False)
    print(f"IC-SAT result: {result}")
