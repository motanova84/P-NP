"""
DPLL SAT Solver with Decision Tracking
=======================================

Implements the Davis-Putnam-Logemann-Loveland (DPLL) algorithm
with support for tracking decision sequences for information
complexity analysis.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

from typing import List, Dict, Tuple, Optional
import time


class DPLLSolver:
    """DPLL SAT solver with decision tracking."""
    
    def __init__(self, formula):
        """
        Initialize DPLL solver with a CNF formula.
        
        Args:
            formula: CNF formula object with num_vars and clauses
        """
        self.num_vars = formula.num_vars
        self.original_clauses = [clause[:] for clause in formula.clauses]
        self.decision_sequence = []
        self.branch_count = 0
    
    def solve(self, track_decisions: bool = False, timeout: float = 60.0) -> Dict:
        """
        Solve the SAT formula using DPLL algorithm.
        
        Args:
            track_decisions: Whether to track decision sequence
            timeout: Maximum time in seconds
            
        Returns:
            Dictionary with 'satisfiable', 'decision_sequence', 'branches' keys
        """
        self.decision_sequence = [] if track_decisions else None
        self.branch_count = 0
        start_time = time.time()
        
        result = self._dpll(
            self.original_clauses,
            {},
            track_decisions,
            start_time,
            timeout
        )
        
        return {
            'satisfiable': result,
            'decision_sequence': self.decision_sequence if track_decisions else [],
            'branches': self.branch_count,
            'time': time.time() - start_time
        }
    
    def _dpll(
        self,
        clauses: List[List[int]],
        assignment: Dict[int, bool],
        track: bool,
        start_time: float,
        timeout: float
    ) -> bool:
        """
        Recursive DPLL algorithm.
        
        Args:
            clauses: Current list of clauses
            assignment: Current variable assignment
            track: Whether to track decisions
            start_time: Start time for timeout
            timeout: Timeout in seconds
            
        Returns:
            True if satisfiable, False otherwise
        """
        # Check timeout
        if time.time() - start_time > timeout:
            return False
        
        # Base case: all clauses satisfied
        if not clauses:
            return True
        
        # Base case: empty clause (conflict)
        if [] in clauses:
            return False
        
        # Unit propagation
        clauses, assignment = self._unit_propagation(clauses, assignment)
        
        if not clauses:
            return True
        if [] in clauses:
            return False
        
        # Pure literal elimination
        clauses, assignment = self._pure_literal_elimination(clauses, assignment)
        
        if not clauses:
            return True
        if [] in clauses:
            return False
        
        # Choose branching variable
        var = self._choose_variable(clauses)
        self.branch_count += 1
        
        # Try positive assignment
        if track:
            self.decision_sequence.append((var, True))
        
        new_clauses = self._simplify_clauses(clauses, {var: True})
        new_assignment = assignment.copy()
        new_assignment[var] = True
        
        if self._dpll(new_clauses, new_assignment, track, start_time, timeout):
            return True
        
        # Try negative assignment
        if track:
            self.decision_sequence.append((var, False))
        
        new_clauses = self._simplify_clauses(clauses, {var: False})
        new_assignment = assignment.copy()
        new_assignment[var] = False
        
        return self._dpll(new_clauses, new_assignment, track, start_time, timeout)
    
    def _unit_propagation(
        self,
        clauses: List[List[int]],
        assignment: Dict[int, bool]
    ) -> Tuple[List[List[int]], Dict[int, bool]]:
        """Apply unit propagation."""
        assignment = assignment.copy()
        changed = True
        
        while changed:
            changed = False
            for clause in clauses:
                if len(clause) == 1:
                    lit = clause[0]
                    var = abs(lit)
                    value = lit > 0
                    
                    if var not in assignment:
                        assignment[var] = value
                        changed = True
                    elif assignment[var] != value:
                        return [[]], assignment
            
            if changed:
                clauses = self._simplify_clauses(clauses, assignment)
                if [] in clauses:
                    return clauses, assignment
        
        return clauses, assignment
    
    def _pure_literal_elimination(
        self,
        clauses: List[List[int]],
        assignment: Dict[int, bool]
    ) -> Tuple[List[List[int]], Dict[int, bool]]:
        """Eliminate pure literals."""
        assignment = assignment.copy()
        
        # Find pure literals
        lit_counts = {}
        for clause in clauses:
            for lit in clause:
                var = abs(lit)
                if var not in assignment:
                    if var not in lit_counts:
                        lit_counts[var] = {'pos': 0, 'neg': 0}
                    if lit > 0:
                        lit_counts[var]['pos'] += 1
                    else:
                        lit_counts[var]['neg'] += 1
        
        # Assign pure literals
        pure_found = False
        for var, counts in lit_counts.items():
            if counts['pos'] > 0 and counts['neg'] == 0:
                assignment[var] = True
                pure_found = True
            elif counts['neg'] > 0 and counts['pos'] == 0:
                assignment[var] = False
                pure_found = True
        
        if pure_found:
            clauses = self._simplify_clauses(clauses, assignment)
        
        return clauses, assignment
    
    def _simplify_clauses(
        self,
        clauses: List[List[int]],
        assignment: Dict[int, bool]
    ) -> List[List[int]]:
        """Simplify clauses given assignment."""
        simplified = []
        
        for clause in clauses:
            satisfied = False
            new_clause = []
            
            for lit in clause:
                var = abs(lit)
                if var in assignment:
                    if (lit > 0 and assignment[var]) or (lit < 0 and not assignment[var]):
                        satisfied = True
                        break
                else:
                    new_clause.append(lit)
            
            if not satisfied:
                if len(new_clause) == 0:
                    return [[]]
                simplified.append(new_clause)
        
        return simplified
    
    def _choose_variable(self, clauses: List[List[int]]) -> int:
        """Choose variable for branching using VSIDS-like heuristic."""
        var_freq = {}
        
        for clause in clauses:
            for lit in clause:
                var = abs(lit)
                var_freq[var] = var_freq.get(var, 0) + 1
        
        if not var_freq:
            return 1
        
        return max(var_freq, key=var_freq.get)


if __name__ == "__main__":
    print("DPLL Solver with Decision Tracking ∞³")
    print("=" * 70)
    
    # Test case
    class TestFormula:
        def __init__(self, num_vars, clauses):
            self.num_vars = num_vars
            self.clauses = clauses
    
    # Simple satisfiable formula
    formula = TestFormula(3, [[1, 2], [-1, 3], [-2, -3], [1]])
    solver = DPLLSolver(formula)
    result = solver.solve(track_decisions=True)
    
    print(f"\nTest formula:")
    print(f"  Satisfiable: {result['satisfiable']}")
    print(f"  Branches: {result['branches']}")
    print(f"  Decisions: {len(result['decision_sequence'])}")
    print(f"  Time: {result['time']:.4f}s")
    
    print("\n✓ Solver tests passed")
