#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Trinity Seal Implementation
======================================

Tests the complete Trinity: f₀, Δf, κ_π

Author: José Manuel Mota Burruezo (ICQ · 2026)
"""

import unittest
import math
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.kappa_pi_trinity import TrinitySeal, DELTA_F, F0_FREQUENCY, KAPPA_PI_TARGET


class TestTrinitySeal(unittest.TestCase):
    """Test the Trinity Seal class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.seal = TrinitySeal()
    
    def test_trinity_constants(self):
        """Test that Trinity constants are correctly initialized."""
        self.assertAlmostEqual(self.seal.f0, 141.7001, places=4)
        self.assertAlmostEqual(self.seal.delta_f, 10.0, places=1)
        self.assertAlmostEqual(self.seal.kappa_pi, 2.5773, places=4)
    
    def test_delta_f_constant(self):
        """Test that DELTA_F is defined correctly."""
        self.assertEqual(DELTA_F, 10.0)
        self.assertEqual(self.seal.delta_f, DELTA_F)
    
    def test_resolution_time_basic(self):
        """Test basic resolution time calculation."""
        # For complexity = 100, κ_π = 2.5773, Δf = 10
        # T = 100 / (2.5773 * 10) = 100 / 25.773
        complexity = 100
        expected_time = complexity / (self.seal.kappa_pi * self.seal.delta_f)
        actual_time = self.seal.resolution_time(complexity)
        self.assertAlmostEqual(actual_time, expected_time, places=6)
    
    def test_resolution_time_exponential(self):
        """Test resolution time for exponential complexity."""
        complexity = 2**50
        t_res = self.seal.resolution_time(complexity)
        # Should be a very large number
        self.assertGreater(t_res, 1e12)
        # Should be finite
        self.assertLess(t_res, float('inf'))
    
    def test_resolution_time_scales_with_kappa(self):
        """Test that resolution time decreases as κ_π increases."""
        complexity = 2**30
        
        # Base time with standard κ_π
        t_base = self.seal.resolution_time(complexity)
        
        # Time with 10x larger κ_π
        seal_10x = TrinitySeal()
        seal_10x.kappa_pi = self.seal.kappa_pi * 10
        t_10x = seal_10x.resolution_time(complexity)
        
        # Should be approximately 10x faster
        self.assertAlmostEqual(t_10x, t_base / 10, delta=t_base * 0.01)
    
    def test_noetic_conductivity_basic(self):
        """Test basic noetic conductivity calculation."""
        conductivity = self.seal.noetic_conductivity()
        
        # Check all expected keys
        self.assertIn('kappa_pi', conductivity)
        self.assertIn('info_flow_rate', conductivity)
        self.assertIn('penetration_coefficient', conductivity)
        self.assertIn('phase_liquidity', conductivity)
        self.assertIn('coherence_preservation', conductivity)
        self.assertIn('is_superconducting', conductivity)
    
    def test_info_flow_rate(self):
        """Test information flow rate calculation."""
        conductivity = self.seal.noetic_conductivity()
        expected_rate = self.seal.kappa_pi * self.seal.delta_f
        self.assertAlmostEqual(conductivity['info_flow_rate'], expected_rate, places=4)
    
    def test_penetration_coefficient(self):
        """Test penetration coefficient calculation."""
        conductivity = self.seal.noetic_conductivity()
        expected_coeff = self.seal.kappa_pi / math.pi
        self.assertAlmostEqual(conductivity['penetration_coefficient'], expected_coeff, places=4)
    
    def test_phase_liquidity(self):
        """Test phase liquidity calculation."""
        conductivity = self.seal.noetic_conductivity()
        expected_liquidity = (self.seal.kappa_pi * self.seal.delta_f) / self.seal.f0
        self.assertAlmostEqual(conductivity['phase_liquidity'], expected_liquidity, places=6)
    
    def test_coherence_preservation(self):
        """Test coherence preservation calculation."""
        conductivity = self.seal.noetic_conductivity()
        expected_preservation = math.exp(-1 / self.seal.kappa_pi)
        self.assertAlmostEqual(conductivity['coherence_preservation'], expected_preservation, places=6)
    
    def test_not_superconducting_at_standard(self):
        """Test that standard κ_π is not superconducting."""
        conductivity = self.seal.noetic_conductivity()
        self.assertFalse(conductivity['is_superconducting'])
        self.assertLess(self.seal.kappa_pi, 100)
    
    def test_superconducting_at_high_kappa(self):
        """Test that high κ_π is superconducting."""
        conductivity = self.seal.noetic_conductivity(kappa_pi=150.0)
        self.assertTrue(conductivity['is_superconducting'])
    
    def test_friction_regime_low(self):
        """Test friction regime classification for low κ_π."""
        regime = self.seal.friction_regime(kappa_pi=0.5)
        self.assertIn("HIGH_FRICTION", regime)
        self.assertIn("P ≠ NP", regime)
    
    def test_friction_regime_moderate(self):
        """Test friction regime classification for moderate κ_π."""
        regime = self.seal.friction_regime()  # Uses standard 2.5773
        self.assertIn("MODERATE_FRICTION", regime)
    
    def test_friction_regime_low_friction(self):
        """Test friction regime classification approaching transition."""
        regime = self.seal.friction_regime(kappa_pi=50.0)
        self.assertIn("LOW_FRICTION", regime)
    
    def test_friction_regime_superconducting(self):
        """Test friction regime classification for superconducting."""
        regime = self.seal.friction_regime(kappa_pi=200.0)
        self.assertIn("SUPERCONDUCTING", regime)
        self.assertIn("P → NP", regime)
    
    def test_collapse_velocity_basic(self):
        """Test collapse velocity calculation."""
        velocity = self.seal.collapse_velocity()
        expected_velocity = self.seal.kappa_pi * self.seal.delta_f
        self.assertAlmostEqual(velocity, expected_velocity, places=4)
    
    def test_collapse_velocity_scales(self):
        """Test that collapse velocity scales with κ_π."""
        v1 = self.seal.collapse_velocity(kappa_pi=1.0)
        v2 = self.seal.collapse_velocity(kappa_pi=10.0)
        self.assertAlmostEqual(v2, v1 * 10, places=4)
    
    def test_octave_coupling(self):
        """Test octave coupling calculation."""
        coupling = self.seal.octave_coupling()
        # Should be a small positive number
        self.assertGreater(coupling, 0)
        self.assertLess(coupling, 1)
    
    def test_octave_coupling_decreases_with_octaves(self):
        """Test that coupling decreases with more octaves."""
        coupling_100 = self.seal.octave_coupling(n_octaves=100)
        coupling_1000 = self.seal.octave_coupling(n_octaves=1000)
        self.assertGreater(coupling_100, coupling_1000)
    
    def test_batimiento_without_kappa(self):
        """Test batimiento classification without κ_π."""
        result = self.seal.batimiento_to_music(with_kappa=False)
        self.assertIn("NOISE", result)
        self.assertIn("incoherent", result)
    
    def test_batimiento_with_kappa(self):
        """Test batimiento classification with κ_π."""
        result = self.seal.batimiento_to_music(with_kappa=True)
        self.assertIn("MÚSICA", result)
        self.assertIn("ESFERAS", result)
    
    def test_trinity_report_structure(self):
        """Test that trinity report has correct structure."""
        report = self.seal.get_trinity_report()
        
        # Check main sections
        self.assertIn('trinity_components', report)
        self.assertIn('noetic_properties', report)
        self.assertIn('regime', report)
        self.assertIn('collapse_velocity', report)
        self.assertIn('octave_coupling', report)
        self.assertIn('musical_nature', report)
        self.assertIn('resolution_time_example', report)
    
    def test_trinity_components_in_report(self):
        """Test trinity components in report."""
        report = self.seal.get_trinity_report()
        components = report['trinity_components']
        
        self.assertIn('f0_heartbeat', components)
        self.assertIn('delta_f_breathing', components)
        self.assertIn('kappa_pi_conductivity', components)
        
        # Check values
        self.assertEqual(components['f0_heartbeat']['value'], self.seal.f0)
        self.assertEqual(components['delta_f_breathing']['value'], self.seal.delta_f)
        self.assertEqual(components['kappa_pi_conductivity']['value'], self.seal.kappa_pi)
    
    def test_resolution_time_examples_in_report(self):
        """Test resolution time examples in report."""
        report = self.seal.get_trinity_report()
        examples = report['resolution_time_example']
        
        self.assertIn('complexity_2_100', examples)
        self.assertIn('complexity_factorial_20', examples)
        
        # Check they are positive numbers
        self.assertGreater(examples['complexity_2_100'], 0)
        self.assertGreater(examples['complexity_factorial_20'], 0)
    
    def test_superconductivity_limit(self):
        """Test behavior as κ_π approaches infinity."""
        # Test with very large κ_π
        large_kappa = 1e6
        complexity = 2**50
        
        t_res = complexity / (large_kappa * self.seal.delta_f)
        
        # Resolution time should be much smaller than with standard κ_π
        t_res_standard = complexity / (self.seal.kappa_pi * self.seal.delta_f)
        self.assertLess(t_res, t_res_standard / 1000)
        
        # Regime should be superconducting
        regime = self.seal.friction_regime(kappa_pi=large_kappa)
        self.assertIn("SUPERCONDUCTING", regime)
    
    def test_trinity_seal_mathematical_consistency(self):
        """Test mathematical consistency of Trinity Seal."""
        # Resolution time should equal complexity divided by product
        complexity = 12345
        t_res = self.seal.resolution_time(complexity)
        expected = complexity / (self.seal.kappa_pi * self.seal.delta_f)
        self.assertAlmostEqual(t_res, expected, places=10)
    
    def test_delta_f_role_in_resolution(self):
        """Test that Δf properly affects resolution time."""
        complexity = 1000
        
        # Double Δf should halve resolution time
        seal1 = TrinitySeal()
        seal1.delta_f = 10.0
        t1 = seal1.resolution_time(complexity)
        
        seal2 = TrinitySeal()
        seal2.delta_f = 20.0
        t2 = seal2.resolution_time(complexity)
        
        self.assertAlmostEqual(t2, t1 / 2, places=6)


class TestTrinityConstants(unittest.TestCase):
    """Test Trinity constant definitions."""
    
    def test_f0_frequency(self):
        """Test f₀ frequency constant."""
        self.assertAlmostEqual(F0_FREQUENCY, 141.7001, places=4)
    
    def test_delta_f_frequency(self):
        """Test Δf beating frequency constant."""
        self.assertEqual(DELTA_F, 10.0)
    
    def test_kappa_pi_constant(self):
        """Test κ_π conductivity constant."""
        self.assertAlmostEqual(KAPPA_PI_TARGET, 2.5773, places=4)
    
    def test_trinity_ratio(self):
        """Test the ratio between Trinity components."""
        # f₀ / Δf should be approximately 14.17
        ratio = F0_FREQUENCY / DELTA_F
        self.assertAlmostEqual(ratio, 14.17001, places=4)
    
    def test_trinity_product(self):
        """Test the product κ_π · Δf."""
        product = KAPPA_PI_TARGET * DELTA_F
        # Should be approximately 25.773
        self.assertAlmostEqual(product, 25.773, places=2)


class TestTrinityIntegration(unittest.TestCase):
    """Integration tests for the complete Trinity."""
    
    def test_trinity_seal_creation(self):
        """Test creating a Trinity Seal."""
        seal = TrinitySeal()
        self.assertIsNotNone(seal)
        self.assertIsInstance(seal, TrinitySeal)
    
    def test_full_workflow(self):
        """Test a complete workflow using the Trinity Seal."""
        seal = TrinitySeal()
        
        # Calculate resolution time
        complexity = 2**40
        t_res = seal.resolution_time(complexity)
        self.assertGreater(t_res, 0)
        
        # Get conductivity properties
        conductivity = seal.noetic_conductivity()
        self.assertIn('kappa_pi', conductivity)
        
        # Check regime
        regime = seal.friction_regime()
        self.assertIsInstance(regime, str)
        
        # Get full report
        report = seal.get_trinity_report()
        self.assertIn('trinity_components', report)
    
    def test_p_neq_np_maintained(self):
        """Test that P ≠ NP is maintained at standard κ_π."""
        seal = TrinitySeal()
        regime = seal.friction_regime()
        
        # At standard κ_π = 2.5773, we should have moderate friction
        # which maintains P ≠ NP
        self.assertIn("MODERATE_FRICTION", regime)
        self.assertIn("P ≠ NP", regime)
    
    def test_p_approaches_np_at_high_kappa(self):
        """Test that P → NP as κ_π → ∞."""
        seal = TrinitySeal()
        regime = seal.friction_regime(kappa_pi=500.0)
        
        # At very high κ_π, we approach superconductivity
        self.assertIn("SUPERCONDUCTING", regime)
        self.assertIn("P → NP", regime)


if __name__ == '__main__':
    unittest.main()
