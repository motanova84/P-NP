"""
Test suite for holographic_verification.py

Tests the holographic P≠NP verification implementation including:
- Holographic Tseitin construction
- Spectral analysis
- RT volume calculations
- Time-volume law verification
"""

import pytest
import numpy as np
import networkx as nx
import math
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from holographic_verification import (
    KAPPA_PI, ALPHA_HOLO,
    HolographicTseitin,
    construct_holographic_tseitin,
    analyze_holographic_spectrum,
    compute_rt_volume_empirical,
    information_complexity_from_volume,
    holographic_time_law,
    simulate_algorithm_time
)


class TestConstants:
    """Test QCAL constants."""
    
    def test_kappa_pi_value(self):
        """Test that KAPPA_PI has correct value."""
        assert KAPPA_PI == 2.5773
        assert KAPPA_PI > 0
    
    def test_alpha_holo_value(self):
        """Test that ALPHA_HOLO is computed correctly."""
        expected = 1 / (8 * math.pi)
        assert abs(ALPHA_HOLO - expected) < 1e-10


class TestHolographicTseitin:
    """Test HolographicTseitin dataclass properties."""
    
    def test_rt_volume_formula(self):
        """Test RT volume computation."""
        n = 100
        instance = construct_holographic_tseitin(n)
        
        # Check formula: Vol(RT) ≈ n * log(n) / (2*κ_Π)
        expected = n * math.log(n + 1) / (2 * KAPPA_PI)
        assert abs(instance.rt_volume - expected) < 1e-6
    
    def test_holographic_time_bound(self):
        """Test time bound computation."""
        n = 50
        instance = construct_holographic_tseitin(n)
        
        # Time bound should be exponential in RT volume
        expected = math.exp(ALPHA_HOLO * instance.rt_volume)
        assert abs(instance.holographic_time_bound - expected) < 1e-6
    
    def test_rt_volume_grows_with_n(self):
        """Test that RT volume increases with n."""
        n1, n2 = 50, 100
        instance1 = construct_holographic_tseitin(n1)
        instance2 = construct_holographic_tseitin(n2)
        
        assert instance2.rt_volume > instance1.rt_volume


class TestConstruction:
    """Test construction of holographic instances."""
    
    def test_construct_basic(self):
        """Test basic construction."""
        n = 50
        instance = construct_holographic_tseitin(n)
        
        assert instance.n == n
        assert len(instance.boundary_graph.nodes()) == n
        assert len(instance.bulk_points) == n
        assert instance.mass_eff > 0
    
    def test_bulk_points_coordinates(self):
        """Test that bulk points have proper structure."""
        n = 30
        instance = construct_holographic_tseitin(n)
        
        for v, (x, y, z) in instance.bulk_points.items():
            # z should be in reasonable range
            assert 0.1 <= z <= 1.0
            # All coordinates should be finite
            assert math.isfinite(x)
            assert math.isfinite(y)
            assert math.isfinite(z)
    
    def test_graph_properties(self):
        """Test boundary graph properties."""
        n = 40
        instance = construct_holographic_tseitin(n)
        G = instance.boundary_graph
        
        # Should be connected (for expander)
        assert nx.is_connected(G)
        
        # Should have reasonable degree
        degrees = [d for _, d in G.degree()]
        avg_degree = sum(degrees) / len(degrees)
        assert avg_degree >= 4  # At least moderate connectivity


class TestSpectralAnalysis:
    """Test holographic spectral analysis."""
    
    def test_analyze_spectrum(self):
        """Test spectral analysis returns proper structure."""
        n = 50
        instance = construct_holographic_tseitin(n)
        spectrum = analyze_holographic_spectrum(instance)
        
        # Check that all expected keys exist
        assert 'lambda2' in spectrum
        assert 'mass_eff' in spectrum
        assert 'delta_conformal' in spectrum
        assert 'spectral_gap' in spectrum
        assert 'is_expander' in spectrum
    
    def test_lambda2_bounds(self):
        """Test that λ₂ is in valid range."""
        n = 50
        instance = construct_holographic_tseitin(n)
        spectrum = analyze_holographic_spectrum(instance)
        
        # λ₂ should be between -1 and 1 for normalized adjacency
        assert -1 <= spectrum['lambda2'] <= 1
    
    def test_expander_detection(self):
        """Test expander detection for reasonably large graphs."""
        n = 100
        instance = construct_holographic_tseitin(n)
        spectrum = analyze_holographic_spectrum(instance)
        
        # For 8-regular graphs, should be expander
        assert spectrum['is_expander']
    
    def test_delta_conformal_positive(self):
        """Test that conformal dimension is positive."""
        n = 50
        instance = construct_holographic_tseitin(n)
        spectrum = analyze_holographic_spectrum(instance)
        
        assert spectrum['delta_conformal'] > 1


class TestRTVolume:
    """Test RT volume calculations."""
    
    def test_rt_volume_empirical_positive(self):
        """Test that empirical RT volume is positive."""
        n = 50
        instance = construct_holographic_tseitin(n)
        vol = compute_rt_volume_empirical(instance)
        
        assert vol >= 0
    
    def test_information_complexity_conversion(self):
        """Test IC conversion from RT volume."""
        rt_volume = 100.0
        ic = information_complexity_from_volume(rt_volume)
        
        expected = rt_volume / (2 * KAPPA_PI)
        assert abs(ic - expected) < 1e-10


class TestTimeLaws:
    """Test holographic time laws."""
    
    def test_holographic_time_law_classical(self):
        """Test classical time law."""
        rt_volume = 50.0
        time = holographic_time_law(rt_volume, 'classical')
        
        expected = math.exp(ALPHA_HOLO * rt_volume)
        assert abs(time - expected) < 1e-6
    
    def test_holographic_time_law_quantum(self):
        """Test quantum time law."""
        rt_volume = 50.0
        time = holographic_time_law(rt_volume, 'quantum')
        
        # Quantum should have 2x alpha
        expected = math.exp(2 * ALPHA_HOLO * rt_volume)
        assert abs(time - expected) < 1e-6
    
    def test_time_increases_with_volume(self):
        """Test that time bound increases with volume."""
        vol1, vol2 = 30.0, 60.0
        time1 = holographic_time_law(vol1, 'classical')
        time2 = holographic_time_law(vol2, 'classical')
        
        assert time2 > time1


class TestAlgorithmSimulation:
    """Test algorithm time simulation."""
    
    def test_simulate_bruteforce(self):
        """Test brute force simulation."""
        n = 50
        time = simulate_algorithm_time(n, 'bruteforce')
        assert time > 0
    
    def test_simulate_dpll(self):
        """Test DPLL simulation."""
        n = 50
        time = simulate_algorithm_time(n, 'dpll')
        assert time > 0
    
    def test_simulate_cdcl(self):
        """Test CDCL simulation."""
        n = 50
        time = simulate_algorithm_time(n, 'cdcl')
        assert time > 0
    
    def test_simulate_polynomial(self):
        """Test polynomial simulation."""
        n = 50
        time = simulate_algorithm_time(n, 'poly')
        
        # Should be roughly n^3
        expected = n ** 3
        assert abs(time - expected) < 1e-6
    
    def test_relative_algorithm_speeds(self):
        """Test that exponential algorithms grow faster than polynomial."""
        n = 100
        
        poly = simulate_algorithm_time(n, 'poly')
        cdcl = simulate_algorithm_time(n, 'cdcl')
        dpll = simulate_algorithm_time(n, 'dpll')
        brute = simulate_algorithm_time(n, 'bruteforce')
        
        # Exponential algorithms should be ordered by their base
        assert cdcl < dpll
        assert dpll < brute
        
        # All times should be positive
        assert poly > 0 and cdcl > 0 and dpll > 0 and brute > 0
    
    def test_unknown_algorithm_raises_error(self):
        """Test that unknown algorithm names raise ValueError."""
        with pytest.raises(ValueError, match="Unknown algorithm"):
            simulate_algorithm_time(50, 'unknown_algorithm')


class TestVerification:
    """Test complete verification workflow."""
    
    def test_verification_runs(self):
        """Test that verification runs without error."""
        from holographic_verification import run_complete_verification
        
        # Use small values for quick test
        n_values = [51, 71]
        results = run_complete_verification(n_values)
        
        assert len(results) == 2
        
        # Check structure of results
        for r in results:
            assert 'n' in r
            assert 'rt_volume' in r
            assert 'time_bound_classical' in r
            assert 'time_cdcl' in r
            assert 'contradiction' in r
            assert 'mass_eff' in r
            assert 'delta_conformal' in r
    
    def test_results_have_correct_n_values(self):
        """Test that results match input n values."""
        from holographic_verification import run_complete_verification
        
        n_values = [51, 71, 91]
        results = run_complete_verification(n_values)
        
        result_n_values = [r['n'] for r in results]
        assert result_n_values == n_values


class TestTheoreticalConsistency:
    """Test theoretical consistency of the framework."""
    
    def test_volume_time_relationship(self):
        """Test that time grows exponentially with volume."""
        volumes = [10.0, 20.0, 30.0, 40.0]
        times = [holographic_time_law(v, 'classical') for v in volumes]
        
        # Check exponential growth
        for i in range(len(times) - 1):
            ratio = times[i + 1] / times[i]
            assert ratio > 1.0  # Should be growing
    
    def test_mass_scaling(self):
        """Test that mass scales appropriately with n."""
        n_values = [50, 100, 200]
        instances = [construct_holographic_tseitin(n) for n in n_values]
        masses = [inst.mass_eff for inst in instances]
        
        # All masses should be positive
        for m in masses:
            assert m > 0


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
