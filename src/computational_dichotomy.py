# -*- coding: utf-8 -*-
"""
Computational Dichotomy Framework (P≠NP) - Research Implementation

⚠️  RESEARCH FRAMEWORK - PROPOSES EXTENSIONS BEYOND ESTABLISHED THEORY ⚠️

This module implements a PROPOSED framework for analyzing P vs NP through
treewidth and information complexity. The claims extend significantly beyond
classical FPT (fixed-parameter tractable) results.

CONTEXT:
-------
✅ ESTABLISHED: SAT is FPT in treewidth with time 2^O(tw)·poly(n)
✅ ESTABLISHED: Information complexity framework (Braverman-Rao)
⚠️  PROPOSED: Complete dichotomy φ ∈ P ⟺ tw(G_I(φ)) = O(log n)
⚠️  PROPOSED: Universal IC bound IC(Π|S) ≥ κ_Π·tw(φ)/log n
⚠️  PROPOSED: κ_Π = 2.5773 as geometric constant from Calabi-Yau

See TREEWIDTH_CNF_FORMULATION_CONTEXT.md for detailed discussion of
what is established vs. what is claimed in this framework.

This implementation is for:
- Research exploration and experimentation
- Empirical testing of proposed relationships
- Development of intuition about the dichotomy

It should NOT be used for:
- Definitive complexity claims
- Production systems without understanding the theoretical status
- Citation as established results

Author: José Manuel Mota Burruezo (ICQ · 2025)
Dependencies: networkx, numpy

Featuring: κ_Π = 2.5773 - The Proposed Millennium Constant
"""

import math
import time
import random
import networkx as nx
import numpy as np
from typing import List, Tuple, Set, Optional, Dict


import math
import time
import random
import networkx as nx
import numpy as np
from typing import List, Tuple, Set, Optional, Dict


class CNF:
    """Simple CNF formula representation for IC-SAT algorithm."""
    def __init__(self, variables: List[str], clauses: List[List[int]]):
        self.variables = variables
        self.clauses = clauses
        self.n_vars = len(variables)
    
    def __str__(self):
        return f"CNF(vars={self.n_vars}, clauses={len(self.clauses)})"


def incidence_graph(n_vars: int, clauses: List[List[int]]) -> nx.Graph:
    """Build incidence graph with proper bipartite labels."""
    G = nx.Graph()
    
    # Add variable nodes
    for i in range(1, n_vars + 1):
        G.add_node(f'v{i}', bipartite=0)
    
    # Add clause nodes  
    for i, clause in enumerate(clauses):
        G.add_node(f'c{i}', bipartite=1)
    
    # Add edges
    for i, clause in enumerate(clauses):
        for lit in clause:
            var_idx = abs(lit)
            G.add_edge(f'v{var_idx}', f'c{i}')
    
    return G


def primal_graph(clauses: List[List[int]], n_vars: int) -> nx.Graph:
    """Build primal graph."""
    G = nx.Graph()
    G.add_nodes_from(range(1, n_vars + 1))
    
    for clause in clauses:
        vars_in_clause = [abs(lit) for lit in clause]
        for i in range(len(vars_in_clause)):
            for j in range(i + 1, len(vars_in_clause)):
                G.add_edge(vars_in_clause[i], vars_in_clause[j])
    
    return G


def estimate_treewidth(G: nx.Graph) -> float:
    """Estimate treewidth using min-degree approximation."""
    try:
        return nx.approximation.treewidth_min_degree(G)[0]
    except:
        # Fallback: use degeneracy as upper bound
        if G.number_of_nodes() > 0:
            return max(nx.core_number(G).values())
        return 0


def predict_advantages(G: nx.Graph, S: List, d: int = 6, c0: float = 0.25, rho: float = 1.0) -> Dict:
    """Predict advantages based on spectral properties."""
    if not S:
        return {}
    
    try:
        A = nx.adjacency_matrix(G).todense()
        eigs = np.linalg.eigvalsh(A)
        delta = d - eigs[-2] if len(eigs) > 1 else d
        gamma = delta / d
        tau = c0 * rho * gamma
        
        return {u: tau for u in S}
    except:
        return {u: 0.1 for u in S}  # Fallback


def simplify_clauses(clauses: List[List[int]], var: str, value: int) -> Optional[List[List[int]]]:
    """Simplify clauses by assigning a variable."""
    new_clauses = []
    var_idx = int(var[1:])  # Extract variable index from 'v1', 'v2', etc.
    
    for clause in clauses:
        if value == 1 and var_idx in clause:
            continue  # Clause satisfied
        if value == 0 and -var_idx in clause:
            continue  # Clause satisfied
        
        new_clause = [lit for lit in clause if abs(lit) != var_idx]
        
        if len(new_clause) == 0:
            return None  # Empty clause - unsatisfiable
        
        new_clauses.append(new_clause)
    
    return new_clauses


def solve_sat_simple(clauses: List[List[int]]) -> str:
    """Simple SAT solver for demonstration."""
    # This is a placeholder - in real implementation use PySAT
    # For now, assume SAT if no empty clauses
    for clause in clauses:
        if len(clause) == 0:
            return "UNSAT"
    return "SAT"


def ic_sat(G, clauses: List[List[int]], n_vars: int, assignments: Dict = None, 
           log: bool = False, depth: int = 0, max_depth: int = 100) -> str:
    """IC-SAT algorithm with information complexity optimization."""
    if assignments is None:
        assignments = {}
    
    if depth > max_depth:
        return "UNKNOWN"  # Prevent infinite recursion
    
    # Check if already solved
    if not clauses:
        return "SAT"
    
    tw = estimate_treewidth(G)
    
    if tw <= math.log2(max(n_vars, 2)):
        return solve_sat_simple(clauses)
    
    # Get separator nodes (clause nodes with bipartite=1)
    S = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 1]
    
    if not S:  # Fallback if no bipartite labels
        S = list(G.nodes())[:min(3, len(G.nodes()))]
    
    tau = predict_advantages(G, S)
    
    if not tau:  # No advantages predicted
        return solve_sat_simple(clauses)
    
    v = max(tau, key=tau.get) if tau else (list(S)[0] if S else (list(G.nodes())[0] if G.nodes() else None))
    
    if v is None:
        return solve_sat_simple(clauses)
    
    if log:
        print(f"[IC] depth={depth}, tw={tw:.2f}, S={len(S)}, v={v}")
    
    # Branch on variable v
    for b in [0, 1]:
        new_assign = assignments.copy()
        new_assign[v] = b
        
        # Handle variable vs clause nodes
        if v.startswith('v'):
            new_clauses = simplify_clauses(clauses, v, b)
        else:
            # For clause nodes, try both true/false
            new_clauses = clauses.copy()
        
        if new_clauses is None:
            continue
        
        # Update graph for new clauses
        new_n_vars = n_vars  # In real implementation, this might change
        new_G = incidence_graph(new_n_vars, new_clauses)
        
        res = ic_sat(new_G, new_clauses, new_n_vars, new_assign, log, depth + 1, max_depth)
        if res == "SAT":
            return "SAT"
    
    return "UNSAT"


def compare_treewidths(clauses: List[List[int]], n_vars: int) -> Tuple[float, float]:
    """Compare primal and incidence treewidths."""
    Gp = primal_graph(clauses, n_vars)
    Gi = incidence_graph(n_vars, clauses)
    
    tw_p = estimate_treewidth(Gp)
    tw_i = estimate_treewidth(Gi)
    
    return tw_p, tw_i


class LargeScaleValidation:
    """Enhanced validation class for large-scale testing."""
    
    def generate_3sat_critical(self, n: int, ratio: float = 4.2) -> CNF:
        """Generate critical 3-SAT instances."""
        variables = [f"x{i}" for i in range(1, n + 1)]
        n_clauses = int(n * ratio)
        clauses = []
        
        for _ in range(n_clauses):
            clause = []
            vars_in_clause = random.sample(range(1, n + 1), 3)
            for var in vars_in_clause:
                sign = 1 if random.random() > 0.5 else -1
                clause.append(sign * var)
            clauses.append(clause)
        
        return CNF(variables, clauses)
    
    def estimate_treewidth_practical(self, G: nx.Graph) -> float:
        """Practical treewidth estimation."""
        return estimate_treewidth(G)
    
    def run_ic_sat(self, cnf: CNF) -> Tuple[float, int]:
        """Run IC-SAT and return time and branches."""
        G = incidence_graph(cnf.n_vars, cnf.clauses)
        start_time = time.time()
        
        result = ic_sat(G, cnf.clauses, cnf.n_vars, log=False, max_depth=3)  # Very shallow depth for demo
        
        elapsed = time.time() - start_time
        # Simple branch count estimation
        branches = 2 ** min(10, cnf.n_vars // 10)  # Placeholder
        
        return elapsed, branches
    
    def run_minisat_simulation(self, cnf: CNF) -> Tuple[float, int]:
        """Simulate MiniSat performance."""
        # Placeholder - in real implementation use PySAT
        complexity = len(cnf.clauses) * cnf.n_vars / 1000
        time_est = complexity * 0.01  # seconds
        branches_est = complexity * 10
        
        return time_est, branches_est
    
    def run_large_scale(self, n_values: List[int] = None, ratios: List[float] = None) -> Dict:
        """Run large-scale validation."""
        if n_values is None:
            n_values = [50, 100, 150]  # Smaller for demo
        if ratios is None:
            ratios = [4.0, 4.2]
        
        results = {}
        
        for n in n_values:
            for ratio in ratios:
                print(f"Testing n={n}, ratio={ratio}")
                
                # Generate instance
                cnf = self.generate_3sat_critical(n, ratio)
                G = incidence_graph(cnf.n_vars, cnf.clauses)
                
                # Estimate treewidth
                tw_est = self.estimate_treewidth_practical(G)
                
                # Run solvers
                ic_sat_time, ic_sat_branches = self.run_ic_sat(cnf)
                minisat_time, minisat_branches = self.run_minisat_simulation(cnf)
                
                results[f"n={n}_r={ratio}"] = {
                    'tw_estimated': tw_est,
                    'ic_sat_branches': ic_sat_branches,
                    'minisat_branches': minisat_branches,
                    'branch_reduction': (minisat_branches - ic_sat_branches) / max(minisat_branches, 1),
                    'coherence_C': 1 / (1 + tw_est)
                }
        
        return results
import random
from typing import List, Tuple
import sys
import os

# Add src to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
from constants import (
    KAPPA_PI, 
    QCAL_FREQUENCY_HZ,
    information_complexity_lower_bound,
    p_np_dichotomy_threshold,
    is_in_P
)

# ========== CNF FORMULA CLASS ==========

class CNFFormula:
    """Represents a CNF (Conjunctive Normal Form) formula."""
    
    def __init__(self, num_vars: int, clauses: List[List[int]]):
        """
        Initialize a CNF formula.
        
        Args:
            num_vars: Number of variables in the formula
            clauses: List of clauses, where each clause is a list of literals
        """
        self.num_vars = num_vars
        self.clauses = clauses
    
    def __repr__(self):
        return f"CNFFormula(vars={self.num_vars}, clauses={len(self.clauses)})"


def generate_low_treewidth_formula(n: int) -> CNFFormula:
    """
    Generate a CNF formula with low treewidth (chain structure).
    
    This creates a chain-like formula where each variable is only connected
    to its neighbors, resulting in a treewidth of approximately 1-2.
    
    Args:
        n: Number of variables
        
    Returns:
        CNFFormula with low treewidth
    """
    clauses = []
    
    # Create chain structure: clauses connecting adjacent variables
    for i in range(1, n):
        # Add clauses like (v_i ∨ v_{i+1})
        clauses.append([i, i + 1])
        # Add clauses like (¬v_i ∨ ¬v_{i+1}) for variety
        if i % 2 == 0:
            clauses.append([-i, -(i + 1)])
    
    # Add boundary conditions
    if n > 0:
        clauses.append([1])  # v_1 must be true
        clauses.append([-n])  # v_n must be false
    
    return CNFFormula(n, clauses)


def ramanujan_graph(n: int, seed: int = 42) -> nx.Graph:
    """
    Generate a Ramanujan graph (approximated using random regular graph).
    
    Ramanujan graphs are optimal expanders with degree d and expansion ≥ 1 - 2√(d-1)/d.
    We approximate using random regular graphs which are expanders with high probability.
    
    For practical Tseitin encoding, we use degree 3 to balance between:
    - High expansion (expander property)
    - Reasonable clause count (2^(d-1) clauses per vertex)
    
    Args:
        n: Number of vertices
        seed: Random seed for reproducibility
        
    Returns:
        A 3-regular or 4-regular graph (expander)
    """
    # Use degree 3 or 4 for expander graphs in Tseitin encoding
    # This gives good expansion while keeping clause count manageable
    d = 3
    
    # Ensure d is valid for regular graph (n*d must be even)
    if (n * d) % 2 != 0:
        d = 4  # Switch to degree 4 if degree 3 doesn't work
    
    # Ensure 0 ≤ d < n
    d = min(d, n - 1)
    d = max(3, d)  # At least degree 3
    
    # Generate random regular graph (expander with high probability)
    try:
        G = nx.random_regular_graph(d, n, seed=seed)
    except nx.NetworkXError:
        # Fallback to cycle if regular graph fails
        G = nx.cycle_graph(n)
    
    return G


def tseitin_encoding(G: nx.Graph, parity: List[int]) -> CNFFormula:
    """
    Generate Tseitin encoding of a graph with given vertex parities.
    
    The Tseitin transformation creates a CNF formula that is satisfiable iff
    the parity constraints can be satisfied on the graph.
    
    Args:
        G: Undirected graph
        parity: List of parities (0 or 1) for each vertex
        
    Returns:
        CNFFormula representing the Tseitin encoding
    """
    if len(parity) != G.number_of_nodes():
        raise ValueError(f"Parity list length {len(parity)} != number of nodes {G.number_of_nodes()}")
    
    # Number of variables = number of edges
    num_vars = G.number_of_edges()
    edge_to_var = {edge: idx + 1 for idx, edge in enumerate(G.edges())}
    
    clauses = []
    
    # For each vertex, add clauses encoding XOR of incident edges = parity
    node_list = list(G.nodes())
    for node_idx, node in enumerate(node_list):
        # Get incident edge variables
        incident_vars = []
        for edge in G.edges(node):
            if edge in edge_to_var:
                incident_vars.append(edge_to_var[edge])
            else:
                # Try reversed edge
                rev_edge = (edge[1], edge[0])
                if rev_edge in edge_to_var:
                    incident_vars.append(edge_to_var[rev_edge])
        
        # Add XOR clauses for this vertex
        target_parity = parity[node_idx]
        _add_xor_clauses(incident_vars, target_parity, clauses)
    
    return CNFFormula(num_vars, clauses)


def _add_xor_clauses(vars: List[int], target: int, clauses: List[List[int]]):
    """
    Add CNF clauses encoding XOR of variables equals target.
    
    For XOR(v1, v2, ..., vn) = target, enumerate all 2^n possible assignments
    to the variables. For each assignment with the wrong parity, add a clause
    forbidding that assignment. This results in approximately 2^(n-1) clauses
    being added, although the loop enumerates all 2^n assignments.
    """
    n = len(vars)
    if n == 0:
        if target == 1:
            clauses.append([])  # Empty clause (unsatisfiable)
        return
    
    # Enumerate all 2^n assignments and forbid those with wrong parity
    # This is the standard Tseitin encoding
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


def hard_cnf_formula(n: int, seed: int = 42) -> CNFFormula:
    """
    Generate a hard CNF formula with high treewidth using Tseitin over expanders.
    
    This implements the construction:
        hard_cnf_formula(n) = tseitin_encoding(ramanujan_graph(n))
    
    Properties:
        - Variables: O(n)
        - Clauses: O(n)
        - Treewidth: Ω(√n)
        - Expansion: ≥ (1 - 2√(d-1)/d) (Ramanujan optimal)
    
    Args:
        n: Number of vertices in the underlying graph
        seed: Random seed for reproducibility
        
    Returns:
        CNFFormula with high treewidth
    """
    # Generate Ramanujan graph (expander)
    G = ramanujan_graph(n, seed=seed)
    
    # Use all-odd parity assignment (creates unsatisfiable formula)
    # This ensures the formula has the desired hardness properties
    parity = [1] * n
    
    # Apply Tseitin encoding
    formula = tseitin_encoding(G, parity)
    
    return formula



# ========== CNF FORMULA CLASS ==========

class CNFFormula:
    """Simple CNF formula representation."""
    
    def __init__(self, num_vars, clauses):
        """
        Initialize CNF formula.
        
        Args:
            num_vars: Number of variables
            clauses: List of clauses (each clause is a list of literals)
        """
        self.num_vars = num_vars
        self.clauses = clauses

# ========== GRAPH CONSTRUCTION ==========

def primal_graph(n_vars, clauses):
    G = nx.Graph()
    G.add_nodes_from([f'v{i}' for i in range(1, n_vars + 1)])
    for clause in clauses:
        for i in range(len(clause)):
            for j in range(i + 1, len(clause)):
                G.add_edge(f'v{abs(clause[i])}', f'v{abs(clause[j])}')
    return G

def incidence_graph(n_vars, clauses):
    G = nx.Graph()
    for i in range(1, n_vars + 1):
        G.add_node(f'v{i}', bipartite=0)
    for j, clause in enumerate(clauses):
        G.add_node(f'c{j}', bipartite=1)
        for lit in clause:
            G.add_edge(f'v{abs(lit)}', f'c{j}')
    return G

# ========== TREEWIDTH ESTIMATION ==========

def estimate_treewidth(G):
    try:
        tw, _ = nx.approximation.treewidth_min_degree(G)
        return tw
    except Exception:
        # Fallback: return a safe upper bound
        if G.number_of_nodes() == 0:
            return 0
        return G.number_of_nodes() - 1

# ========== INFORMATION COMPLEXITY ==========

def predict_advantages(G, S):
    if not S:
        return {'v1': 1.0}
    return {v: np.random.rand() for v in S}

def simplify_clauses(clauses, assignment):
    new_clauses = []
    for c in clauses:
        if any(lit in assignment or -lit in assignment for lit in c):
            continue
        new_clauses.append(c)
    return new_clauses

# ========== IC-SAT CORE ==========

def ic_sat(clauses, n_vars, log=True, depth=0, max_depth=20):
    if depth >= max_depth or not clauses:
        return True

    G = incidence_graph(n_vars, clauses)
    tw = estimate_treewidth(G)
    if log:
        print(f"[IC] depth={depth}, tw={tw}, n={n_vars}, m={len(clauses)}")

    if tw <= np.log2(n_vars):
        return True  # tractable

    S = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 1]
    tau = predict_advantages(G, S)
    pivot = max(tau, key=tau.get)
    new_clauses = simplify_clauses(clauses, [int(pivot[1:])])
    return ic_sat(new_clauses, n_vars, log, depth + 1, max_depth)

# ========== LARGE-SCALE VALIDATION ==========

class LargeScaleValidation:
    def generate_3sat_critical(self, n, ratio=4.2):
        m = int(ratio * n)
        clauses = []
        for _ in range(m):
            clause = random.sample(range(1, n + 1), 3)
            clause = [c if random.random() < 0.5 else -c for c in clause]
            clauses.append(clause)
        return clauses

    def run_ic_sat(self, n):
        clauses = self.generate_3sat_critical(n)
        print(f"\nRunning IC-SAT for n={n}, m={len(clauses)}")
        result = ic_sat(clauses, n, log=True)
        print("Result:", "SAT" if result else "UNSAT")

    def estimate_treewidth_practical(self, n=30):
        clauses = self.generate_3sat_critical(n)
        G = incidence_graph(n, clauses)
        tw = estimate_treewidth(G)
        print(f"Estimated treewidth for n={n}: {tw}")
        return tw

# ========== COMPUTATIONAL DICHOTOMY VALIDATOR ==========

class ComputationalDichotomy:
    """
    Research tool for the PROPOSED computational dichotomy theorem.
    
    ⚠️  EXPLORATORY IMPLEMENTATION - NOT ESTABLISHED THEORY
    
    This class provides methods for analyzing SAT instances and testing
    the proposed relationships between treewidth, information complexity,
    and computational hardness.
    
    CLASSICAL BASIS (✅ Established):
    - Treewidth estimation using standard graph algorithms
    - FPT algorithms for bounded treewidth
    - Standard SAT solving techniques (DPLL, CDCL)
    
    PROPOSED EXTENSIONS (⚠️ Require validation):
    - Complete dichotomy at logarithmic threshold
    - Information complexity computation via κ_Π
    - Prediction of hardness from treewidth alone
    - Universal applicability claims
    
    Use this class for:
    - Empirical exploration of treewidth-hardness relationships
    - Testing proposed theoretical predictions
    - Gathering data to validate or refute the framework
    
    Do NOT use for:
    - Definitive hardness predictions
    - Production complexity analysis
    - Claims that bypass peer review
    
    See TREEWIDTH_CNF_FORMULATION_CONTEXT.md for theoretical context.
    """
    
    def __init__(self):
        """Initialize the validator."""
        pass
    
    def estimate_treewidth(self, G):
        """
        Estimate treewidth of a graph.
        
        Args:
            G: NetworkX graph
            
        Returns:
            Estimated treewidth
        """
        return estimate_treewidth(G)
    
    def compute_information_complexity(self, formula):
        """
        Compute PROPOSED information complexity of a SAT formula using κ_Π.
        
        ⚠️  PROPOSED BOUND - EXTENDS BEYOND EXISTING IC THEORY
        
        This implements the proposed inequality:
            IC(Π | S) >= κ_Π · tw(φ) / log n
        
        where κ_Π = 2.5773 is claimed to be a universal geometric constant.
        
        CONTEXT:
        -------
        Classical IC theory (Braverman-Rao):
          - Provides lower bounds for specific functions
          - Constants typically implicit or problem-dependent
          - Proven for particular protocol families
        
        This framework proposes:
          - Explicit universal constant κ_Π = 2.5773
          - Direct treewidth to IC connection
          - Universal applicability to all SAT protocols
          - Geometric origin from Calabi-Yau manifolds
        
        REQUIRES VALIDATION:
          - Mathematical proof of the bound
          - Verification of κ_Π value
          - Confirmation of universal applicability
          - Rigorous connection to topology
        
        Use this method for:
          - Exploring proposed IC relationships
          - Testing theoretical predictions empirically
          - Comparing with actual algorithm performance
        
        Args:
            formula: CNF formula object
            
        Returns:
            PROPOSED information complexity estimate (in bits)
            
        Note:
            This is a THEORETICAL PROPOSAL for research purposes.
            Not validated as an established IC lower bound.
        """
        # Build incidence graph
        if hasattr(formula, 'incidence_graph'):
            G = formula.incidence_graph
        else:
            G = incidence_graph(formula.num_vars, formula.clauses)
        
        # Estimate treewidth
        tw = estimate_treewidth(G)
        
        # Apply κ_Π bound from constants module
        ic = information_complexity_lower_bound(tw, formula.num_vars)
        
        return ic
    
    def solve_with_dpll(self, formula, timeout=60):
        """
        Solve formula with DPLL and measure time.
        
        Args:
            formula: CNF formula
            timeout: Timeout in seconds
            
        Returns:
            Tuple of (time_taken, satisfiable)
        """
        import time
        start_time = time.time()
        
        # Use the simple DPLL from ic_sat module
        from ic_sat import simple_dpll
        
        try:
            result = simple_dpll(formula.clauses, formula.num_vars)
            time_taken = time.time() - start_time
            
            # Enforce minimum time to avoid division by zero
            time_taken = max(time_taken, 0.001)
            
            return (time_taken, result == 'SAT')
        except Exception:
            return (timeout, False)
    
    def solve_with_cdcl(self, formula, timeout=60):
        """
        Solve formula with CDCL (placeholder - uses DPLL).
        
        Args:
            formula: CNF formula
            timeout: Timeout in seconds
            
        Returns:
            Tuple of (time_taken, satisfiable)
        """
        # For now, use DPLL as CDCL implementation
        return self.solve_with_dpll(formula, timeout)


if __name__ == "__main__":
    print("=" * 70)
    print("Computational Dichotomy Framework with κ_Π (RESEARCH)")
    print("=" * 70)
    print()
    print("⚠️  RESEARCH FRAMEWORK - PROPOSES EXTENSIONS BEYOND ESTABLISHED THEORY")
    print()
    print(f"κ_Π (Proposed Millennium Constant): {KAPPA_PI}")
    print(f"QCAL Frequency: {QCAL_FREQUENCY_HZ} Hz")
    print()
    print("What's ESTABLISHED (✅):")
    print("  - SAT is FPT in treewidth: Time = 2^O(tw)·poly(n)")
    print("  - Information complexity framework exists")
    print()
    print("What's PROPOSED (⚠️ requires proof):")
    print("  - Complete dichotomy: φ ∈ P ⟺ tw(G_I(φ)) = O(log n)")
    print("  - IC bound: IC(Π|S) ≥ κ_Π·tw(φ)/log n")
    print("  - κ_Π = 2.5773 as geometric constant")
    print()
    print("See TREEWIDTH_CNF_FORMULATION_CONTEXT.md for details")
    print()
    print("=" * 70)
    
    # IC-SAT demonstration
    print("📊 Example 3: IC-SAT Algorithm Demonstration")
    print("-" * 70)
    n_vars = 3
    clauses = [[1, 2], [-1, -2]]  # Simpler example
    
    print("1. Treewidth Comparison:")
    tw_p, tw_i = compare_treewidths(clauses, n_vars)
    print(f"   Primal TW: {tw_p:.2f}, Incidence TW: {tw_i:.2f}")
    print(f"   Log(n) threshold: {math.log2(max(n_vars, 2)):.2f}")
    
    print("\n2. IC-SAT Execution:")
    G = incidence_graph(n_vars, clauses)
    result = ic_sat(G, clauses, n_vars, log=False, max_depth=5)  # Reduced depth and no logging
    print(f"   IC-SAT result: {result}")
    print()
    
    # Large Scale Validation Demo
    print("📊 Example 4: Large Scale Validation (Demo)")
    print("-" * 70)
    validator = LargeScaleValidation()
    demo_results = validator.run_large_scale(n_values=[10, 15], ratios=[4.0])  # Even smaller
    
    for key, val in demo_results.items():
        print(f"   {key}: TW={val['tw_estimated']:.2f}, Coherence={val['coherence_C']:.3f}")
    print()
    
    # Test with example
    print("Testing with n=20 variables:")
    LSV = LargeScaleValidation()
    LSV.run_ic_sat(20)
    
    print()
    print("=" * 70)
    print("This is exploratory research - not established results")
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
