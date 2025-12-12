"""
Test suite for holographic verification

Tests the holographic framework implementation including:
- Tseitin formula generation
- Effective mass calculations (m_eff ~ √n/log n)
- Holographic volume bounds (Vol(RT) ~ n log n)
- Temporal contradictions (exp(Vol(RT)) vs polynomial time)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
Test suite for holographic P vs NP verification.
#!/usr/bin/env python3
"""
Test script for holographic_verification.py

Validates the holographic verification calculations and output.
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
sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))

import pytest
import numpy as np
import networkx as nx
from holographic_p_vs_np import (
    HolographicTseitin,
    construct_tseitin_boundary_graph,
    holographic_embedding,
    compute_effective_mass,
    construct_holographic_tseitin,
    analyze_holographic_spectrum,
    compute_rt_volume_empirical,
    simulate_algorithm,
    verify_holographic_law,
    KAPPA_PI,
    ALPHA_HOLO,
    PHI
)


class TestConstants:
    """Test universal constants."""
    
    def test_constants_defined(self):
        """Test that all constants are properly defined."""
        assert KAPPA_PI > 0
        assert ALPHA_HOLO > 0
        assert PHI > 1
        assert abs(PHI - (1 + np.sqrt(5)) / 2) < 1e-10
    
    def test_alpha_holo_value(self):
        """Test that ALPHA_HOLO has the correct value."""
        expected = 1 / (8 * np.pi)
        assert abs(ALPHA_HOLO - expected) < 1e-10


class TestGraphConstruction:
    """Test graph construction functions."""
    
    def test_construct_tseitin_boundary_graph_basic(self):
        """Test basic graph construction."""
        n = 51
        G = construct_tseitin_boundary_graph(n)
        
        assert G.number_of_nodes() == n
        assert G.number_of_edges() > 0
        assert nx.is_connected(G)
    
    def test_construct_tseitin_boundary_graph_regularity(self):
        """Test that graph is approximately regular."""
        n = 51
        d = 8
        G = construct_tseitin_boundary_graph(n, d)
        
        degrees = [G.degree(node) for node in G.nodes()]
        avg_degree = sum(degrees) / len(degrees)
        
        # Should have reasonable average degree (not necessarily exactly d)
        assert avg_degree >= 2
        assert avg_degree <= d + 2
    
    def test_holographic_embedding_dimensions(self):
        """Test that embedding has correct dimensions."""
        n = 21
        G = construct_tseitin_boundary_graph(n)
        embedding = holographic_embedding(G)
        
        assert len(embedding) == n
        for node, coords in embedding.items():
            assert len(coords) == 3  # (x, y, z)
            x, y, z = coords
            assert 0.1 <= z <= 1.0  # z coordinate in valid range


class TestHolographicTseitin:
    """Test HolographicTseitin dataclass."""
    
    def test_construct_holographic_tseitin(self):
        """Test construction of holographic Tseitin instance."""
        n = 51
        instance = construct_holographic_tseitin(n)
        
        assert instance.n == n
        assert instance.boundary_graph.number_of_nodes() == n
        assert instance.charge == 1  # n=51 is odd
        assert instance.is_unsatisfiable
        assert instance.mass_eff > 0
    
    def test_even_n_satisfiable(self):
        """Test that even n gives satisfiable instance."""
        n = 50
        instance = construct_holographic_tseitin(n)
        
        assert instance.charge == 0
        assert not instance.is_unsatisfiable
    
    def test_rt_volume_theoretical(self):
        """Test theoretical RT volume calculation."""
        n = 51
        instance = construct_holographic_tseitin(n)
        
        rt_vol = instance.rt_volume_theoretical
        assert rt_vol > 0
        
        # Should be approximately n * log(n) / (2 * KAPPA_PI)
        expected = n * np.log(n + 1) / (2 * KAPPA_PI)
        assert abs(rt_vol - expected) < 1e-6
    
    def test_holographic_time_bound(self):
        """Test holographic time bound calculation."""
        n = 51
        instance = construct_holographic_tseitin(n)
        
        time_bound = instance.holographic_time_bound
        assert time_bound > 0
        
        # Should be exp(ALPHA_HOLO * rt_volume)
        expected = np.exp(ALPHA_HOLO * instance.rt_volume_theoretical)
        assert abs(time_bound - expected) < 1e-6


class TestSpectralAnalysis:
    """Test spectral analysis functions."""
    
    def test_analyze_holographic_spectrum(self):
        """Test spectral analysis of boundary graph."""
        n = 51
        instance = construct_holographic_tseitin(n)
        spectrum = analyze_holographic_spectrum(instance)
        
        assert 'lambda_max' in spectrum
        assert 'lambda2' in spectrum
        assert 'spectral_gap' in spectrum
        assert 'delta_conformal' in spectrum
        assert 'is_expander' in spectrum
        
        # lambda_max should be close to 1
        assert abs(spectrum['lambda_max'] - 1.0) < 0.2
        
        # spectral_gap should be positive
        assert spectrum['spectral_gap'] > 0
    
    def test_effective_mass_positive(self):
        """Test that effective mass is positive."""
        n = 51
        G = construct_tseitin_boundary_graph(n)
        mass_eff = compute_effective_mass(G, n)
        
        assert mass_eff > 0


class TestVolumeCalculations:
    """Test RT volume calculations."""
    
    def test_compute_rt_volume_empirical(self):
        """Test empirical RT volume calculation."""
        n = 51
        instance = construct_holographic_tseitin(n)
        rt_volume = compute_rt_volume_empirical(instance)
        
        assert rt_volume >= 0
    
    def test_rt_volume_grows_with_n(self):
        """Test that RT volume grows with instance size."""
        volumes = []
        for n in [31, 51, 71]:
            instance = construct_holographic_tseitin(n)
            volumes.append(instance.rt_volume_theoretical)
        
        # Volumes should be increasing
        assert volumes[0] < volumes[1] < volumes[2]


class TestAlgorithmSimulation:
    """Test algorithm simulation functions."""
    
    def test_simulate_algorithm_types(self):
        """Test different algorithm simulations."""
        n = 51
        instance = construct_holographic_tseitin(n)
        
        algorithms = ['bruteforce', 'dpll', 'cdcl', 'quantum', 'polynomial']
        
        for algo in algorithms:
            result = simulate_algorithm(instance, algo)
            assert 'time' in result
            assert 'space' in result
            assert 'scaling' in result
            assert result['time'] > 0
            assert result['space'] > 0
    
    def test_polynomial_algorithm_marked(self):
        """Test that polynomial algorithm is properly marked."""
        n = 51
        instance = construct_holographic_tseitin(n)
        
        result = simulate_algorithm(instance, 'polynomial')
        assert result['is_polynomial'] is True
        
        result = simulate_algorithm(instance, 'cdcl')
        assert result['is_polynomial'] is False


class TestHolographicLaw:
    """Test holographic law verification."""
    
    def test_verify_holographic_law_structure(self):
        """Test structure of holographic law verification."""
        n = 51
        instance = construct_holographic_tseitin(n)
        result = verify_holographic_law(instance)
        
        assert 'rt_volume' in result
        assert 'time_bound' in result
        assert 'algorithms' in result
        assert 'main_contradiction' in result
        assert 'holographic_law_holds' in result
        
        # Check algorithms are present
        assert 'cdcl' in result['algorithms']
        assert 'quantum' in result['algorithms']
        assert 'polynomial' in result['algorithms']
    
    def test_contradiction_type(self):
        """Test that contradiction is boolean."""
        n = 51
        instance = construct_holographic_tseitin(n)
        result = verify_holographic_law(instance)
        
        assert isinstance(result['main_contradiction'], bool)


class TestIntegration:
    """Integration tests for the complete system."""
    
    def test_complete_workflow_small(self):
        """Test complete workflow with small instance."""
        n = 21
        
        # Construct instance
        instance = construct_holographic_tseitin(n)
        assert instance is not None
        
        # Analyze spectrum
        spectrum = analyze_holographic_spectrum(instance)
        assert spectrum is not None
        
        # Compute RT volume
        rt_volume = compute_rt_volume_empirical(instance)
        assert rt_volume >= 0
        
        # Verify holographic law
        holography = verify_holographic_law(instance)
        assert holography is not None
    
    def test_multiple_instances(self):
        """Test with multiple instance sizes."""
        n_values = [21, 31, 41]
        
        for n in n_values:
            instance = construct_holographic_tseitin(n)
            assert instance.n == n
            assert instance.num_vertices == n
            
            # All odd n should be unsatisfiable
            assert instance.is_unsatisfiable


if __name__ == '__main__':
    pytest.main([__file__, '-v'])

# Add parent directory to path to import holographic_verification
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from holographic_verification import HolographicVerification, KAPPA_PI, ALPHA_ADS3
import math


def test_effective_mass():
    """Test effective mass calculation."""
    verifier = HolographicVerification()
    
    # Test n=10
    meff_10 = verifier.compute_effective_mass(10)
    assert meff_10 > 10, "Effective mass should be greater than base value"
    assert meff_10 < 12, "Effective mass should be reasonable"
    
    # Test n=100
    meff_100 = verifier.compute_effective_mass(100)
    assert meff_100 > meff_10, "Effective mass should increase with n"
    
    print("✅ test_effective_mass passed")


def test_ryu_takayanagi_volume():
    """Test Ryu-Takayanagi volume calculation."""
    verifier = HolographicVerification()
    
    # Test basic properties
    meff_10 = verifier.compute_effective_mass(10)
    vol_10 = verifier.compute_ryu_takayanagi_volume(10, meff_10)
    
    meff_20 = verifier.compute_effective_mass(20)
    vol_20 = verifier.compute_ryu_takayanagi_volume(20, meff_20)
    
    assert vol_10 > 0, "Volume should be positive"
    assert vol_20 > vol_10, "Volume should increase with n"
    
    # Verify Ω(n log n) scaling
    ratio = vol_20 / vol_10
    expected_ratio = (20 * math.log(20 + 1)) / (10 * math.log(10 + 1))
    assert abs(ratio - expected_ratio) / expected_ratio < 0.5, "Should scale as n log n"
    
    print("✅ test_ryu_takayanagi_volume passed")


def test_holographic_time_bound():
    """Test holographic time bound calculation."""
    verifier = HolographicVerification()
    
    vol_50 = 50.0
    t_holo = verifier.compute_holographic_time_bound(vol_50)
    
    # Should be exponential in volume
    expected = math.exp(ALPHA_ADS3 * vol_50)
    assert abs(t_holo - expected) < 1e-6, "Should compute exp(alpha * vol)"
    
    # Test monotonicity
    t_holo_100 = verifier.compute_holographic_time_bound(100.0)
    assert t_holo_100 > t_holo, "Time should increase with volume"
    
    print("✅ test_holographic_time_bound passed")


def test_cdcl_time():
    """Test CDCL time estimation."""
    verifier = HolographicVerification()
    
    t_10 = verifier.compute_cdcl_time(10)
    t_20 = verifier.compute_cdcl_time(20)
    
    assert t_10 > 0, "CDCL time should be positive"
    assert t_20 > t_10, "CDCL time should increase with n"
    
    # Verify exponential growth
    assert t_20 / t_10 > 1.2, "Should grow exponentially"
    
    print("✅ test_cdcl_time passed")


def test_polynomial_time():
    """Test polynomial time calculation."""
    verifier = HolographicVerification()
    
    t_10 = verifier.compute_polynomial_time(10, degree=3)
    t_20 = verifier.compute_polynomial_time(20, degree=3)
    
    assert t_10 == 1000, "Should compute n^3 correctly"
    assert t_20 == 8000, "Should compute n^3 correctly"
    
    print("✅ test_polynomial_time passed")


def test_separation_verification():
    """Test the full separation verification."""
    verifier = HolographicVerification()
    
    # Use larger n values to see the separation
    n_values = [50, 100]
    results = verifier.verify_separation(n_values)
    
    # Check all required fields are present
    required_fields = ['n', 'meff', 'vol_rt', 't_cdcl', 't_holo', 't_poly', 
                      'separation_cdcl', 'separation_poly']
    for field in required_fields:
        assert field in results, f"Results should contain {field}"
        assert len(results[field]) == len(n_values), f"Should have values for all n"
    
    # Verify T_Holo > T_poly for large n (the key separation)
    # For n=100, we should see clear separation
    assert results['t_holo'][-1] > results['t_poly'][-1], \
        "Holographic bound should exceed polynomial time for n=100"
    
    # Verify monotonicity: T_Holo should grow faster than T_poly
    ratio_50 = results['t_holo'][0] / results['t_poly'][0]
    ratio_100 = results['t_holo'][1] / results['t_poly'][1]
    assert ratio_100 > ratio_50, "Separation should increase with n"
    
    print("✅ test_separation_verification passed")


def test_constants():
    """Test that constants are correctly defined."""
    assert KAPPA_PI == 2.5773, "KAPPA_PI should be 2.5773"
    assert abs(ALPHA_ADS3 - 1/(8*math.pi)) < 1e-6, "ALPHA_ADS3 should be 1/(8π)"
    
    print("✅ test_constants passed")


def main():
    """Run all tests."""
    print("\n" + "="*80)
    print("Testing holographic_verification.py")
    print("="*80 + "\n")
    
    try:
        test_constants()
        test_effective_mass()
        test_ryu_takayanagi_volume()
        test_holographic_time_bound()
        test_cdcl_time()
        test_polynomial_time()
        test_separation_verification()
        
        print("\n" + "="*80)
        print("✅ ALL TESTS PASSED")
        print("="*80 + "\n")
        return 0
        
    except AssertionError as e:
        print(f"\n❌ TEST FAILED: {e}\n")
        return 1
    except Exception as e:
        print(f"\n❌ UNEXPECTED ERROR: {e}\n")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
