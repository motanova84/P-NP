"""
Unit tests for IC-SAT algorithm and validation framework

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.ic_sat import (
    build_primal_graph, build_incidence_graph, estimate_treewidth,
    compare_treewidths, simplify_clauses, unit_propagation,
    predict_advantages, simple_dpll, ic_sat, LargeScaleValidation,
    parse_dimacs, incidence_graph, primal_graph, validate_ramanujan_calibration
)


class TestGraphBuilding(unittest.TestCase):
    """Test cases for graph building functions."""
    
    def test_primal_graph(self):
        """Test primal graph construction."""
        n_vars = 3
        clauses = [[1, 2], [2, 3], [-1, -3]]
        
        G = build_primal_graph(n_vars, clauses)
        
        # Should have 3 variable nodes
        self.assertEqual(len(G.nodes()), 3)
        
        # Should have edges between vars in same clause
        self.assertTrue(G.has_edge('v1', 'v2'))
        self.assertTrue(G.has_edge('v2', 'v3'))
        self.assertTrue(G.has_edge('v1', 'v3'))
    
    def test_incidence_graph(self):
        """Test incidence graph construction."""
        n_vars = 2
        clauses = [[1, -2], [-1, 2]]
        
        G = build_incidence_graph(n_vars, clauses)
        
        # Should have 2 variable nodes + 2 clause nodes
        self.assertEqual(len(G.nodes()), 4)
        
        # Check bipartite labels
        var_nodes = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 0]
        clause_nodes = [n for n, d in G.nodes(data=True) if d.get('bipartite') == 1]
        
        self.assertEqual(len(var_nodes), 2)
        self.assertEqual(len(clause_nodes), 2)
        
        # Check edges
        self.assertTrue(G.has_edge('v1', 'c0'))
        self.assertTrue(G.has_edge('v2', 'c0'))


class TestTreewidth(unittest.TestCase):
    """Test cases for treewidth estimation."""
    
    def test_estimate_treewidth_path(self):
        """Test treewidth estimation on a path graph."""
        import networkx as nx
        G = nx.path_graph(5)
        
        tw = estimate_treewidth(G)
        
        # Path graph has treewidth 1
        self.assertLessEqual(tw, 2)  # Approximation might be slightly off
    
    def test_compare_treewidths(self):
        """Test treewidth comparison."""
        n_vars = 3
        clauses = [[1, 2], [2, 3]]
        
        primal_tw, incidence_tw = compare_treewidths(n_vars, clauses)
        
        # Both should be reasonable values
        self.assertGreaterEqual(primal_tw, 0)
        self.assertGreaterEqual(incidence_tw, 0)


class TestClauseSimplification(unittest.TestCase):
    """Test cases for clause simplification."""
    
    def test_simplify_clauses_satisfied(self):
        """Test simplification when clause is satisfied."""
        clauses = [[1, 2], [3, 4]]
        assignment = {1: True}
        
        simplified = simplify_clauses(clauses, assignment)
        
        # First clause should be removed (satisfied)
        self.assertEqual(len(simplified), 1)
        self.assertEqual(simplified[0], [3, 4])
    
    def test_simplify_clauses_propagate(self):
        """Test simplification with literal removal."""
        clauses = [[1, 2], [-1, 3]]
        assignment = {1: False}
        
        simplified = simplify_clauses(clauses, assignment)
        
        # First clause becomes [2] (1 is false, so only 2 remains)
        # Second clause is satisfied (-1 is true when 1 is false)
        self.assertEqual(len(simplified), 1)
        self.assertIn([2], simplified)
    
    def test_simplify_clauses_conflict(self):
        """Test simplification with conflict."""
        clauses = [[1], [-1]]
        assignment = {1: True}
        
        simplified = simplify_clauses(clauses, assignment)
        
        # Should result in empty clause (conflict)
        self.assertIn([], simplified)
    
    def test_unit_propagation(self):
        """Test unit propagation."""
        clauses = [[1], [1, 2], [-1, 3]]
        
        simplified, assignment = unit_propagation(clauses)
        
        # Should propagate x1=True, which satisfies [1] and [1,2]
        # and reduces [-1, 3] to [3], which then propagates x3=True
        self.assertEqual(assignment[1], True)
        self.assertEqual(assignment[3], True)
        # After full propagation, all clauses are satisfied
        self.assertEqual(len(simplified), 0)


class TestDPLL(unittest.TestCase):
    """Test cases for DPLL solver."""
    
    def test_dpll_satisfiable(self):
        """Test DPLL on satisfiable formula."""
        clauses = [[1, 2], [-1, 3], [-3]]
        n_vars = 3
        
        result = simple_dpll(clauses, n_vars)
        
        self.assertEqual(result, 'SAT')
    
    def test_dpll_unsatisfiable(self):
        """Test DPLL on unsatisfiable formula."""
        clauses = [[1], [-1]]
        n_vars = 1
        
        result = simple_dpll(clauses, n_vars)
        
        self.assertEqual(result, 'UNSAT')
    
    def test_dpll_empty(self):
        """Test DPLL on empty formula."""
        clauses = []
        n_vars = 0
        
        result = simple_dpll(clauses, n_vars)
        
        self.assertEqual(result, 'SAT')


class TestICSAT(unittest.TestCase):
    """Test cases for IC-SAT algorithm."""
    
    def test_ic_sat_simple(self):
        """Test IC-SAT on simple formula."""
        n_vars = 2
        clauses = [[1, -2], [-1, 2]]
        
        result = ic_sat(n_vars, clauses, log=False)
        
        self.assertEqual(result, 'SAT')
    
    def test_ic_sat_unsatisfiable(self):
        """Test IC-SAT on unsatisfiable formula."""
        n_vars = 2
        clauses = [[1], [-1], [2], [-2]]
        
        result = ic_sat(n_vars, clauses, log=False)
        
        self.assertEqual(result, 'UNSAT')
    
    def test_ic_sat_with_logging(self):
        """Test IC-SAT with logging enabled."""
        n_vars = 2
        clauses = [[1, 2]]
        
        # Should not crash with logging
        result = ic_sat(n_vars, clauses, log=True)
        
        self.assertEqual(result, 'SAT')
    
    def test_ic_sat_depth_limit(self):
        """Test IC-SAT respects depth limit."""
        n_vars = 3
        clauses = [[1, 2], [2, 3], [1, 3]]
        
        # Should complete even with small depth limit
        result = ic_sat(n_vars, clauses, log=False, max_depth=5)
        
        self.assertIn(result, ['SAT', 'UNSAT'])


class TestLargeScaleValidation(unittest.TestCase):
    """Test cases for large-scale validation framework."""
    
    def test_generate_3sat(self):
        """Test 3-SAT generation."""
        validator = LargeScaleValidation()
        n_vars, clauses = validator.generate_3sat_critical(10)
        
        self.assertEqual(n_vars, 10)
        self.assertGreater(len(clauses), 0)
        
        # Check that clauses are valid
        for clause in clauses:
            self.assertLessEqual(len(clause), 3)
            for lit in clause:
                self.assertGreaterEqual(abs(lit), 1)
                self.assertLessEqual(abs(lit), n_vars)
    
    def test_estimate_treewidth_practical(self):
        """Test practical treewidth estimation."""
        import networkx as nx
        validator = LargeScaleValidation()
        
        G = nx.path_graph(5)
        tw = validator.estimate_treewidth_practical(G)
        
        self.assertGreaterEqual(tw, 0)
    
    def test_run_ic_sat(self):
        """Test running IC-SAT through validator."""
        validator = LargeScaleValidation()
        
        n_vars = 3
        clauses = [[1, 2], [2, 3]]
        
        result, branches = validator.run_ic_sat(n_vars, clauses)
        
        self.assertIn(result, ['SAT', 'UNSAT', 'TIMEOUT'])
        self.assertGreaterEqual(branches, 0)


class TestPredicateAdvantages(unittest.TestCase):
    """Test cases for predicting variable advantages."""
    
    def test_predict_advantages(self):
        """Test variable prediction."""
        n_vars = 3
        clauses = [[1, 2], [2, 3], [1, 3]]
        
        G = build_incidence_graph(n_vars, clauses)
        var = predict_advantages(G)
        
        # Should return a valid variable
        self.assertIsNotNone(var)
        self.assertTrue(var.startswith('v'))
    
    def test_predict_advantages_empty(self):
        """Test variable prediction on empty graph."""
        n_vars = 0
        clauses = []
        
        G = build_incidence_graph(n_vars, clauses)
        var = predict_advantages(G)
        
        # Should handle empty graph gracefully
        self.assertIn(var, [None, 'v1'])
    
    def test_predict_advantages_with_ramanujan(self):
        """Test variable prediction with Ramanujan parameters."""
        n_vars = 20
        clauses = [[i, i+1, i+2] for i in range(1, 18)]
        
        G = build_incidence_graph(n_vars, clauses)
        var = predict_advantages(G, d=6, c0=0.25, rho=1.0)
        
        # Should return a valid variable with spectral analysis
        self.assertIsNotNone(var)
        self.assertTrue(var.startswith('v'))


class TestAliases(unittest.TestCase):
    """Test cases for alias functions."""
    
    def test_incidence_graph_alias(self):
        """Test that incidence_graph alias works."""
        n_vars = 2
        clauses = [[1, -2]]
        
        G1 = incidence_graph(n_vars, clauses)
        G2 = build_incidence_graph(n_vars, clauses)
        
        # Should produce same graph
        self.assertEqual(len(G1.nodes()), len(G2.nodes()))
        self.assertEqual(len(G1.edges()), len(G2.edges()))
    
    def test_primal_graph_alias(self):
        """Test that primal_graph alias works."""
        n_vars = 2
        clauses = [[1, -2]]
        
        G1 = primal_graph(n_vars, clauses)
        G2 = build_primal_graph(n_vars, clauses)
        
        # Should produce same graph
        self.assertEqual(len(G1.nodes()), len(G2.nodes()))
        self.assertEqual(len(G1.edges()), len(G2.edges()))


class TestDIMACSparsing(unittest.TestCase):
    """Test cases for DIMACS file parsing."""
    
    def test_parse_dimacs_simple(self):
        """Test parsing a simple DIMACS file."""
        import tempfile
        
        # Create a temporary DIMACS file
        with tempfile.NamedTemporaryFile(mode='w', delete=True, suffix='.cnf') as f:
            f.write("c Sample CNF file\n")
            f.write("p cnf 3 2\n")
            f.write("1 -2 0\n")
            f.write("2 3 0\n")
            f.flush()  # Ensure data is written before reading
            
            # Parse while file is still open
            n_vars, clauses = parse_dimacs(f.name)
            
            self.assertEqual(n_vars, 3)
            self.assertEqual(len(clauses), 2)
            self.assertEqual(clauses[0], [1, -2])
            self.assertEqual(clauses[1], [2, 3])


class TestRamanujanCalibration(unittest.TestCase):
    """Test cases for Ramanujan calibration."""
    
    def test_ramanujan_validation(self):
        """Test Ramanujan calibration validation runs without error."""
        # Should not raise an exception
        try:
            validate_ramanujan_calibration()
        except Exception as e:
            self.fail(f"validate_ramanujan_calibration raised {type(e).__name__}: {e}")


class TestLargeScaleEnhanced(unittest.TestCase):
    """Test cases for enhanced large-scale validation."""
    
    def test_run_minisat(self):
        """Test running baseline DPLL solver."""
        validator = LargeScaleValidation()
        
        n_vars = 3
        clauses = [[1, 2], [2, 3]]
        
        result, branches = validator.run_minisat(n_vars, clauses)
        
        self.assertIn(result, ['SAT', 'UNSAT', 'TIMEOUT'])
        self.assertGreaterEqual(branches, 0)
    
    def test_run_ic_sat_with_branches(self):
        """Test IC-SAT returns branch count."""
        validator = LargeScaleValidation()
        
        n_vars = 3
        clauses = [[1, 2], [2, 3]]
        
        result, branches = validator.run_ic_sat(n_vars, clauses)
        
        self.assertIn(result, ['SAT', 'UNSAT', 'TIMEOUT'])
        self.assertIsInstance(branches, int)
    
    def test_run_large_scale_returns_results(self):
        """Test that run_large_scale returns results dict."""
        validator = LargeScaleValidation()
        
        # Run with small parameters for speed
        results = validator.run_large_scale(n_values=[10], ratios=[4.0])
        
        # Should return a dictionary
        self.assertIsInstance(results, dict)
        self.assertGreater(len(results), 0)
        
        # Check structure of results
        for key, value in results.items():
            self.assertIn('tw_estimated', value)
            self.assertIn('ic_sat_branches', value)
            self.assertIn('minisat_branches', value)
            self.assertIn('branch_reduction', value)
            self.assertIn('coherence_C', value)


if __name__ == '__main__':
    print("Running IC-SAT Tests ∞³")
    print("Frecuencia de resonancia: 141.7001 Hz")
    print()
    unittest.main(verbosity=2)
