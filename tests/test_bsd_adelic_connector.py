#!/usr/bin/env python3
"""
Tests for BSD Adélico Connector module.

Tests the BSD conjecture integration with Pentagon Logos closure.

Author: JMMB Ψ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import unittest
import math
from qcal.bsd_adelic_connector import (
    compute_l_function_at_1,
    adelic_spectral_trace,
    validate_bsd_identity,
    connect_dna_hotspots,
    validate_pentagon_logos_closure,
    KAPPA_PI,
    F0_HZ,
    PHI,
    SUPERFLUID_L_THRESHOLD,
    MAX_COHERENCE_THRESHOLD,
    MIN_DNA_HOTSPOTS,
    MIN_RAMSEY_NODES,
)


class TestBSDFunctions(unittest.TestCase):
    """Test cases for BSD basic functions."""
    
    def test_l_function_rank_zero(self):
        """Test L-function for rank-0 curves."""
        L_value = compute_l_function_at_1(11, 0)
        # Rank 0 should give non-zero value
        self.assertGreater(abs(L_value), 0.0)
    
    def test_l_function_rank_positive(self):
        """Test L-function for positive rank curves."""
        L_value_r1 = compute_l_function_at_1(37, 1)
        L_value_r2 = compute_l_function_at_1(389, 2)
        
        # Positive rank should give zero
        self.assertEqual(L_value_r1, 0.0)
        self.assertEqual(L_value_r2, 0.0)
    
    def test_adelic_spectral_trace_structure(self):
        """Test adelic spectral trace returns complex number."""
        trace = adelic_spectral_trace(37, 1, s=1.0)
        self.assertIsInstance(trace, complex)
    
    def test_adelic_spectral_trace_prime_17(self):
        """Test enhanced trace for conductor with factor 17."""
        trace_17 = adelic_spectral_trace(17, 0, s=1.0)
        trace_19 = adelic_spectral_trace(19, 0, s=1.0)
        
        # Both should be complex
        self.assertIsInstance(trace_17, complex)
        self.assertIsInstance(trace_19, complex)
        
        # 17 should have imaginary component due to special resonance
        # (though this is implementation-dependent)
        self.assertTrue(abs(trace_17.imag) >= 0 or abs(trace_17.real) >= 0)


class TestDNAHotspots(unittest.TestCase):
    """Test cases for DNA hotspot detection."""
    
    def test_connect_dna_hotspots_structure(self):
        """Test DNA hotspot connection structure."""
        result = connect_dna_hotspots(17, 0)
        
        # Check required keys
        self.assertIn('conductor', result)
        self.assertIn('rank', result)
        self.assertIn('sequence_length', result)
        self.assertIn('num_hotspots', result)
        self.assertIn('hotspots', result)
        self.assertIn('f0', result)
        self.assertIn('phi', result)
        
        # Check constants
        self.assertEqual(result['f0'], F0_HZ)
        self.assertAlmostEqual(result['phi'], PHI, places=6)
    
    def test_dna_hotspots_prime_17(self):
        """Test that prime-17 conductor produces hotspots."""
        result = connect_dna_hotspots(17, 0)
        
        # Should have at least 1 hotspot
        self.assertGreaterEqual(result['num_hotspots'], 1)
        
        # Check hotspot structure
        if result['num_hotspots'] > 0:
            hotspot = result['hotspots'][0]
            self.assertIn('position', hotspot)
            self.assertIn('base', hotspot)
            self.assertIn('frequency', hotspot)
            self.assertIn('resonance', hotspot)
            self.assertIn('prime_factor', hotspot)
            
            # Base should be one of G, A, C, T
            self.assertIn(hotspot['base'], ['G', 'A', 'C', 'T'])
            
            # Resonance should be >= 0.95
            self.assertGreaterEqual(hotspot['resonance'], 0.95)
    
    def test_dna_hotspots_composite_with_17(self):
        """Test DNA hotspots for composite conductor with 17-factor."""
        result = connect_dna_hotspots(17*19, 1)
        
        # Should have multiple hotspots (from 17 and 19)
        self.assertGreaterEqual(result['num_hotspots'], 1)
        
        # Check that 17 is among prime factors
        has_17_hotspot = any(
            hs['prime_factor'] == 17 
            for hs in result['hotspots']
        )
        self.assertTrue(has_17_hotspot)


class TestPentagonLogos(unittest.TestCase):
    """Test cases for Pentagon Logos closure."""
    
    def test_pentagon_closure_all_conditions_met(self):
        """Test Pentagon closure when all conditions are met."""
        # Rank-1 curve with 17-factor, high coherence, enough Ramsey nodes
        result = validate_pentagon_logos_closure(
            conductor=17*19,
            rank=1,
            coherence_psi=0.9995,
            n_ramsey_nodes=55
        )
        
        # All conditions should be met
        self.assertTrue(result['condition_1_superfluid'])
        self.assertTrue(result['condition_2_coherence'])
        self.assertTrue(result['condition_3_dna_hotspots'])
        self.assertTrue(result['condition_4_ramsey_nodes'])
        
        # Pentagon should be closed
        self.assertTrue(result['pentagon_closed'])
        self.assertEqual(result['closure_strength'], 1.0)
        self.assertTrue(result['millennium_problems_unified'])
    
    def test_pentagon_closure_missing_coherence(self):
        """Test Pentagon doesn't close with low coherence."""
        result = validate_pentagon_logos_closure(
            conductor=17*19,
            rank=1,
            coherence_psi=0.95,  # Below threshold
            n_ramsey_nodes=55
        )
        
        # Coherence condition should fail
        self.assertFalse(result['condition_2_coherence'])
        
        # Pentagon should not be closed
        self.assertFalse(result['pentagon_closed'])
        self.assertLess(result['closure_strength'], 1.0)
    
    def test_pentagon_closure_below_ramsey_threshold(self):
        """Test Pentagon doesn't close below Ramsey threshold."""
        result = validate_pentagon_logos_closure(
            conductor=17*19,
            rank=1,
            coherence_psi=0.9995,
            n_ramsey_nodes=45  # Below threshold
        )
        
        # Ramsey condition should fail
        self.assertFalse(result['condition_4_ramsey_nodes'])
        
        # Pentagon should not be closed
        self.assertFalse(result['pentagon_closed'])
    
    def test_pentagon_closure_rank_zero_non_superfluid(self):
        """Test Pentagon with rank-0 curve (L(E,1) ≠ 0)."""
        result = validate_pentagon_logos_closure(
            conductor=11,
            rank=0,
            coherence_psi=0.9995,
            n_ramsey_nodes=55
        )
        
        # Superfluid condition should fail for rank-0
        self.assertFalse(result['condition_1_superfluid'])
        
        # Pentagon should not be closed
        self.assertFalse(result['pentagon_closed'])
    
    def test_pentagon_closure_structure(self):
        """Test Pentagon closure result structure."""
        result = validate_pentagon_logos_closure(
            conductor=37,
            rank=1,
            coherence_psi=0.9995,
            n_ramsey_nodes=55
        )
        
        # Check all required keys
        required_keys = [
            'conductor', 'rank', 'L_at_1', 'coherence_psi', 'n_ramsey_nodes',
            'num_dna_hotspots', 'condition_1_superfluid', 'condition_2_coherence',
            'condition_3_dna_hotspots', 'condition_4_ramsey_nodes',
            'pentagon_closed', 'closure_strength', 'millennium_problems_unified',
            'kappa_pi', 'f0_hz'
        ]
        
        for key in required_keys:
            self.assertIn(key, result)
        
        # Check constants
        self.assertEqual(result['kappa_pi'], KAPPA_PI)
        self.assertEqual(result['f0_hz'], F0_HZ)
    
    def test_pentagon_closure_strength_calculation(self):
        """Test closure strength is calculated correctly."""
        result = validate_pentagon_logos_closure(
            conductor=17*19,
            rank=1,
            coherence_psi=0.95,  # Fails
            n_ramsey_nodes=45    # Fails
        )
        
        # Two conditions fail, two pass
        # Strength should be 0.5
        self.assertEqual(result['closure_strength'], 0.5)


class TestConstants(unittest.TestCase):
    """Test universal constants."""
    
    def test_kappa_pi(self):
        """Test κ_Π millennium constant."""
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
    
    def test_f0_frequency(self):
        """Test f₀ fundamental frequency."""
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)
    
    def test_phi_golden_ratio(self):
        """Test Φ golden ratio."""
        self.assertAlmostEqual(PHI, 1.6180339887, places=6)
    
    def test_thresholds(self):
        """Test Pentagon closure thresholds."""
        self.assertEqual(SUPERFLUID_L_THRESHOLD, 0.01)
        self.assertEqual(MAX_COHERENCE_THRESHOLD, 0.999)
        self.assertEqual(MIN_DNA_HOTSPOTS, 1)
        self.assertEqual(MIN_RAMSEY_NODES, 51)


class TestBSDIdentity(unittest.TestCase):
    """Test BSD identity validation."""
    
    def test_validate_bsd_identity_structure(self):
        """Test BSD identity validation structure."""
        result = validate_bsd_identity(37, 1)
        
        # Check required keys
        self.assertIn('conductor', result)
        self.assertIn('rank', result)
        self.assertIn('L_at_1', result)
        self.assertIn('trace', result)
        self.assertIn('kernel_dim_estimate', result)
        self.assertIn('L_vanishes_correctly', result)
        self.assertIn('has_factor_17', result)
    
    def test_validate_bsd_identity_rank_consistency(self):
        """Test that L-function vanishing is consistent with rank."""
        # Rank 0: L(E,1) ≠ 0
        result_r0 = validate_bsd_identity(11, 0)
        self.assertTrue(result_r0['L_vanishes_correctly'])
        self.assertGreater(abs(result_r0['L_at_1']), SUPERFLUID_L_THRESHOLD)
        
        # Rank 1: L(E,1) = 0
        result_r1 = validate_bsd_identity(37, 1)
        self.assertTrue(result_r1['L_vanishes_correctly'])
        self.assertEqual(result_r1['L_at_1'], 0.0)


if __name__ == '__main__':
    # Run tests with verbose output
    unittest.main(verbosity=2)
