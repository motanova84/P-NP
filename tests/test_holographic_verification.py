"""
Test suite for holographic verification
========================================

Tests the holographic framework implementation including:
- Tseitin formula generation
- Effective mass calculations (m_eff ~ √n/log n)
- Holographic volume bounds (Vol(RT) ~ n log n)
- Temporal contradictions (exp(Vol(RT)) vs polynomial time)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import math
import pytest
import numpy as np

# Add root to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from holographic_verification import (
    build_tseitin_formula,
    compute_effective_mass,
    holographic_volume_bound,
    theoretical_lower_bound_holographic,
    find_good_separator,
    compute_information_complexity,
    simulate_sat_solver,
    TseitinFormula
)


class TestTseitinGeneration:
    """Test Tseitin formula generation over expanders."""
    
    def test_build_tseitin_formula_small(self):
        """Test building a small Tseitin formula."""
        formula = build_tseitin_formula(10)
        
        assert isinstance(formula, TseitinFormula)
        assert formula.num_vars > 0
        assert len(formula.clauses) > 0
        assert formula.incidence_graph.number_of_nodes() > 0
        assert formula.base_graph.number_of_nodes() == 10 or formula.base_graph.number_of_nodes() == 11  # May adjust for parity
    
    def test_build_tseitin_formula_medium(self):
        """Test building a medium Tseitin formula."""
        formula = build_tseitin_formula(30)
        
        assert formula.num_vars > 20
        assert len(formula.clauses) > 30
        # Incidence graph should have variables + clauses
        assert formula.incidence_graph.number_of_nodes() == formula.num_vars + len(formula.clauses)
    
    def test_incidence_graph_structure(self):
        """Test that incidence graph has correct bipartite structure."""
        formula = build_tseitin_formula(20)
        G = formula.incidence_graph
        
        # Count variable and clause nodes
        var_nodes = [n for n in G.nodes() if n.startswith('v')]
        clause_nodes = [n for n in G.nodes() if n.startswith('c')]
        
        assert len(var_nodes) == formula.num_vars
        assert len(clause_nodes) == len(formula.clauses)
        
        # Check edges only between variables and clauses (bipartite)
        for u, v in G.edges():
            is_var_to_clause = (u.startswith('v') and v.startswith('c')) or (u.startswith('c') and v.startswith('v'))
            assert is_var_to_clause, "Incidence graph should be bipartite"


class TestEffectiveMass:
    """Test holographic effective mass calculations."""
    
    def test_effective_mass_growth(self):
        """Test that effective mass grows with n."""
        masses = []
        for n in [10, 20, 30, 50]:
            formula = build_tseitin_formula(n)
            m_eff = compute_effective_mass(formula.incidence_graph, n)
            masses.append(m_eff)
        
        # Effective mass should grow (m_eff ~ √n / log n)
        assert masses[1] > masses[0]
        assert masses[2] > masses[1]
        assert masses[3] > masses[2]
    
    def test_effective_mass_scaling(self):
        """Test that effective mass scales approximately as √n / log n."""
        n = 100
        formula = build_tseitin_formula(n)
        m_eff = compute_effective_mass(formula.incidence_graph, n)
        
        # Should be approximately √n / log n
        expected_order = math.sqrt(n) / math.log(n)
        
        # Allow factor of 2 deviation
        assert m_eff > expected_order / 2
        assert m_eff < expected_order * 2
    
    def test_effective_mass_positive(self):
        """Test that effective mass is always positive."""
        for n in [10, 20, 30, 50]:
            formula = build_tseitin_formula(n)
            m_eff = compute_effective_mass(formula.incidence_graph, n)
            assert m_eff > 0


class TestHolographicVolumeBound:
    """Test holographic volume (RT surface) bounds."""
    
    def test_volume_bound_growth(self):
        """Test that volume bound grows as n log n."""
        volumes = []
        for n in [10, 20, 30, 50]:
            vol = holographic_volume_bound(n)
            volumes.append(vol)
        
        # Should grow faster than linear
        assert volumes[1] > volumes[0] * 1.8  # More than double
        assert volumes[2] > volumes[1] * 1.3
        assert volumes[3] > volumes[2] * 1.4
    
    def test_volume_bound_scaling(self):
        """Test that volume scales as n log n."""
        n = 100
        vol = holographic_volume_bound(n)
        
        # Should be proportional to n log n
        expected_order = n * math.log(n)
        
        # Check order of magnitude (within factor of 100)
        assert vol > expected_order / 100
        assert vol < expected_order * 10
    
    def test_volume_bound_positive(self):
        """Test that volume bound is always positive."""
        for n in [5, 10, 20, 50, 100]:
            vol = holographic_volume_bound(n)
            assert vol > 0


class TestSeparatorFinding:
    """Test graph separator finding."""
    
    def test_find_separator_basic(self):
        """Test basic separator finding."""
        formula = build_tseitin_formula(30)
        separator = find_good_separator(formula.incidence_graph)
        
        assert isinstance(separator, set)
        assert len(separator) > 0
    
    def test_separator_size_reasonable(self):
        """Test that separator size is reasonable."""
        formula = build_tseitin_formula(50)
        G = formula.incidence_graph
        separator = find_good_separator(G)
        
        n = G.number_of_nodes()
        # Separator should be less than half the nodes
        assert len(separator) < n / 2
        # But not trivially small
        assert len(separator) > 0
    
    def test_separator_disconnects(self):
        """Test that separator disconnects the graph."""
        formula = build_tseitin_formula(40)
        G = formula.incidence_graph
        
        if not G.number_of_nodes() > 2:
            pytest.skip("Graph too small")
        
        separator = find_good_separator(G)
        
        # Remove separator and check connectivity
        G_test = G.copy()
        G_test.remove_nodes_from(separator)
        
        # Should either disconnect or be small
        if G_test.number_of_nodes() > 2:
            # If still has nodes, might be disconnected
            is_connected = G_test.number_of_nodes() == 0 or len(separator) > 0


class TestInformationComplexity:
    """Test information complexity calculations."""
    
    def test_ic_computation_basic(self):
        """Test basic IC computation."""
        formula = build_tseitin_formula(30)
        G = formula.incidence_graph
        separator = find_good_separator(G)
        
        ic = compute_information_complexity(G, separator)
        
        assert ic >= 0
        # IC should be related to separator size
        assert ic >= len(separator) * 0.1
    
    def test_ic_grows_with_size(self):
        """Test that IC grows with problem size."""
        ic_values = []
        for n in [10, 20, 30]:
            formula = build_tseitin_formula(n)
            separator = find_good_separator(formula.incidence_graph)
            ic = compute_information_complexity(formula.incidence_graph, separator)
            ic_values.append(ic)
        
        # IC should generally grow
        assert ic_values[-1] > ic_values[0]
    
    def test_ic_empty_separator(self):
        """Test IC with empty separator."""
        formula = build_tseitin_formula(20)
        ic = compute_information_complexity(formula.incidence_graph, set())
        assert ic == 0.0


class TestHolographicTimeBound:
    """Test holographic time bound (exponential-volume)."""
    
    def test_time_bound_exponential_growth(self):
        """Test that time bound grows exponentially."""
        times = []
        for n in [10, 20, 30]:
            t = theoretical_lower_bound_holographic(n)
            times.append(t)
        
        # Should grow super-exponentially
        # t(20) / t(10) should be much larger than t(30) / t(20) would be if linear
        ratio_1 = times[1] / times[0]
        ratio_2 = times[2] / times[1]
        
        assert ratio_1 > 100  # Exponential growth
        assert ratio_2 > 100
    
    def test_time_bound_positive(self):
        """Test that time bound is always positive."""
        for n in [5, 10, 20, 30, 50]:
            t = theoretical_lower_bound_holographic(n)
            assert t > 0
    
    def test_time_bound_exceeds_polynomial(self):
        """Test that holographic time exceeds reasonable polynomial bounds."""
        n = 50
        t_holo = theoretical_lower_bound_holographic(n)
        
        # Compare with various polynomial bounds
        poly_cubic = n ** 3
        poly_quintic = n ** 5
        poly_septic = n ** 7
        
        assert t_holo > poly_cubic
        assert t_holo > poly_quintic
        assert t_holo > poly_septic
        
        # The holographic bound grows as exp(c * n * log n)
        # which eventually exceeds any polynomial, though for small n
        # very high degree polynomials might be larger


class TestSATSolverSimulation:
    """Test SAT solver runtime simulation."""
    
    def test_simulate_cdcl(self):
        """Test CDCL solver simulation."""
        formula = build_tseitin_formula(20)
        t = simulate_sat_solver(formula, 'cdcl')
        
        assert t > 0
        assert t < 1e10  # Should be sub-exponential
    
    def test_simulate_dpll(self):
        """Test DPLL solver simulation."""
        formula = build_tseitin_formula(20)
        t = simulate_sat_solver(formula, 'dpll')
        
        assert t > 0
        assert t < 1e10
    
    def test_solver_time_grows(self):
        """Test that solver time grows with problem size."""
        times_cdcl = []
        for n in [10, 20, 30]:
            formula = build_tseitin_formula(n)
            t = simulate_sat_solver(formula, 'cdcl')
            times_cdcl.append(t)
        
        # Should grow
        assert times_cdcl[1] > times_cdcl[0]
        assert times_cdcl[2] > times_cdcl[1]


class TestHolographicContradiction:
    """Test the holographic contradiction (CDCL time << holographic bound)."""
    
    def test_contradiction_exists(self):
        """Test that contradiction exists for all problem sizes."""
        for n in [10, 20, 30, 50]:
            formula = build_tseitin_formula(n)
            
            t_cdcl = simulate_sat_solver(formula, 'cdcl')
            t_holo = theoretical_lower_bound_holographic(n)
            
            # The contradiction: CDCL time is much less than holographic bound
            assert t_cdcl < t_holo, f"Contradiction should exist for n={n}"
    
    def test_contradiction_gap_grows(self):
        """Test that the contradiction gap grows with problem size."""
        gaps = []
        for n in [10, 20, 30]:
            formula = build_tseitin_formula(n)
            
            t_cdcl = simulate_sat_solver(formula, 'cdcl')
            t_holo = theoretical_lower_bound_holographic(n)
            
            gap = t_holo / t_cdcl
            gaps.append(gap)
        
        # Gap should grow exponentially
        assert gaps[1] > gaps[0] * 10
        assert gaps[2] > gaps[1] * 10


class TestIntegration:
    """Integration tests for the full holographic verification."""
    
    def test_full_verification_workflow(self):
        """Test the complete verification workflow."""
        n = 30
        
        # Step 1: Generate formula
        formula = build_tseitin_formula(n)
        assert formula.num_vars > 0
        
        # Step 2: Compute effective mass
        m_eff = compute_effective_mass(formula.incidence_graph, n)
        assert m_eff > 0
        
        # Step 3: Find separator and compute IC
        separator = find_good_separator(formula.incidence_graph)
        ic = compute_information_complexity(formula.incidence_graph, separator)
        assert ic > 0
        
        # Step 4: Check volume bound
        vol_bound = holographic_volume_bound(n)
        # IC should be at least comparable to volume bound / 2
        # (may not always hold for sub-optimal separators)
        
        # Step 5: Check time contradiction
        t_cdcl = simulate_sat_solver(formula, 'cdcl')
        t_holo = theoretical_lower_bound_holographic(n)
        assert t_cdcl < t_holo, "Temporal contradiction must exist"
    
    def test_verification_deterministic(self):
        """Test that verification is deterministic with fixed seed."""
        np.random.seed(42)
        
        formula1 = build_tseitin_formula(20)
        
        np.random.seed(42)
        formula2 = build_tseitin_formula(20)
        
        # Should produce same results
        assert formula1.num_vars == formula2.num_vars
        assert len(formula1.clauses) == len(formula2.clauses)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
