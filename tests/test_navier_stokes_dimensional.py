"""
Tests for Navier-Stokes Dimensional Flow Tensor Framework
===========================================================

Comprehensive test suite for the integration of Navier-Stokes equations
with Calabi-Yau geometry.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import unittest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.navier_stokes_dimensional import (
    NavierStokesDimensionalTensor,
    FluidLayer,
    VortexPoint
)
from src.constants import KAPPA_PI, OMEGA_CRITICAL


class TestNavierStokesDimensionalTensor(unittest.TestCase):
    """Test suite for Navier-Stokes dimensional tensor framework."""
    
    def setUp(self):
        """Set up test framework."""
        self.framework = NavierStokesDimensionalTensor(num_dimensions=7)
    
    def test_initialization(self):
        """Test framework initialization."""
        self.assertEqual(self.framework.num_dimensions, 7)
        self.assertAlmostEqual(self.framework.f0, OMEGA_CRITICAL, places=2)
        self.assertAlmostEqual(self.framework.kappa_pi, KAPPA_PI, places=2)
        self.assertAlmostEqual(self.framework.factor_seven, 1.0/7.0, places=6)
    
    def test_layer_frequency_computation(self):
        """Test computation of layer frequencies."""
        # Ground state (level 0) should be at fundamental frequency
        f0 = self.framework.compute_layer_frequency(0)
        self.assertAlmostEqual(f0, OMEGA_CRITICAL, places=2)
        
        # Level 1 should be f₀ * (1 + 1/7)
        f1 = self.framework.compute_layer_frequency(1)
        expected_f1 = OMEGA_CRITICAL * (1.0 + 1.0/7.0)
        self.assertAlmostEqual(f1, expected_f1, places=2)
        
        # Level 7 should be f₀ * 2 (one octave)
        f7 = self.framework.compute_layer_frequency(7)
        expected_f7 = OMEGA_CRITICAL * 2.0
        self.assertAlmostEqual(f7, expected_f7, places=2)
    
    def test_gravity_hierarchy(self):
        """Test gravity hierarchy computation."""
        # Ground state should have maximum gravity
        g0 = self.framework.compute_gravity_hierarchy(0)
        self.assertAlmostEqual(g0, 1.0, places=6)
        
        # Gravity should decay exponentially
        g1 = self.framework.compute_gravity_hierarchy(1)
        expected_g1 = np.exp(-1.0 / KAPPA_PI)
        self.assertAlmostEqual(g1, expected_g1, places=6)
        
        # Higher levels should have lower gravity
        g0 = self.framework.compute_gravity_hierarchy(0)
        g3 = self.framework.compute_gravity_hierarchy(3)
        g6 = self.framework.compute_gravity_hierarchy(6)
        self.assertGreater(g0, g3)
        self.assertGreater(g3, g6)
    
    def test_laminar_flow_initialization(self):
        """Test laminar flow initialization."""
        layers = self.framework.initialize_laminar_flow(base_velocity=1.0)
        
        # Should have correct number of layers
        self.assertEqual(len(layers), 7)
        
        # Check each layer
        for i, layer in enumerate(layers):
            # Level should match index
            self.assertEqual(layer.level, i)
            
            # Frequency should be correct harmonic
            expected_freq = OMEGA_CRITICAL * (1.0 + i/7.0)
            self.assertAlmostEqual(layer.frequency, expected_freq, places=2)
            
            # Velocity should be 3D array
            self.assertEqual(layer.velocity.shape, (3,))
            
            # Velocity magnitude should decrease with level
            if i > 0:
                prev_v = np.linalg.norm(layers[i-1].velocity)
                curr_v = np.linalg.norm(layer.velocity)
                self.assertGreater(prev_v, curr_v)
    
    def test_viscosity_resistance(self):
        """Test viscosity computation as information resistance."""
        layers = self.framework.initialize_laminar_flow(base_velocity=2.0)
        
        # Compute viscosity between first two layers
        viscosity = self.framework.compute_viscosity_resistance(
            layers[0], layers[1]
        )
        
        # Viscosity should be positive
        self.assertGreater(viscosity, 0.0)
        
        # Viscosity between same layer should be zero
        viscosity_same = self.framework.compute_viscosity_resistance(
            layers[0], layers[0]
        )
        self.assertAlmostEqual(viscosity_same, 0.0, places=4)
    
    def test_superfluidity_condition(self):
        """Test superfluidity (P=NP) condition check."""
        layers = self.framework.initialize_laminar_flow(base_velocity=1.0)
        
        # Check superfluidity
        result = self.framework.check_superfluidity_condition(layers)
        
        # Should have all required fields
        self.assertIn('is_superfluid', result)
        self.assertIn('p_equals_np', result)
        self.assertIn('alignment_error', result)
        self.assertIn('average_viscosity', result)
        self.assertIn('harmonic_ratios', result)
        self.assertIn('message', result)
        
        # P=NP should equal superfluidity
        self.assertEqual(result['is_superfluid'], result['p_equals_np'])
        
        # Alignment error should be small (well-tuned harmonics)
        self.assertLess(result['alignment_error'], 0.1)
        
        # Harmonic ratios should be correct
        ratios = result['harmonic_ratios']
        self.assertEqual(len(ratios), 7)
        for i, ratio in enumerate(ratios):
            expected = 1.0 + i * (1.0/7.0)
            self.assertAlmostEqual(ratio, expected, places=4)
    
    def test_vortex_creation(self):
        """Test vortex quantum bridge creation."""
        vortex = self.framework.create_vortex_quantum_bridge(
            center=(1.0, 2.0, 3.0),
            strength=1.5
        )
        
        # Check position
        np.testing.assert_array_equal(vortex.position, np.array([1.0, 2.0, 3.0]))
        
        # Angular velocity should be high (approaching infinity at center)
        self.assertGreater(vortex.angular_velocity, 100.0)
        
        # Pressure should be low (approaching zero at center)
        self.assertLess(vortex.pressure, 0.5)
        
        # Coherence should be high (inverse of pressure)
        self.assertGreater(vortex.coherence, 0.5)
        
        # Coherence and pressure should sum close to 1
        self.assertAlmostEqual(vortex.coherence + vortex.pressure, 1.0, places=4)
    
    def test_vortex_strength_scaling(self):
        """Test that vortex properties scale with strength."""
        weak_vortex = self.framework.create_vortex_quantum_bridge(
            center=(0.0, 0.0, 0.0),
            strength=0.5
        )
        
        strong_vortex = self.framework.create_vortex_quantum_bridge(
            center=(0.0, 0.0, 0.0),
            strength=2.0
        )
        
        # Stronger vortex should have higher angular velocity
        self.assertGreater(
            strong_vortex.angular_velocity,
            weak_vortex.angular_velocity
        )
        
        # Stronger vortex should have lower pressure
        self.assertLess(
            strong_vortex.pressure,
            weak_vortex.pressure
        )
        
        # Stronger vortex should have higher coherence
        self.assertGreater(
            strong_vortex.coherence,
            weak_vortex.coherence
        )
    
    def test_tunnel_probability(self):
        """Test quantum tunnel probability computation."""
        # High coherence vortex
        high_coherence_vortex = self.framework.create_vortex_quantum_bridge(
            center=(0.0, 0.0, 0.0),
            strength=3.0
        )
        
        # Low coherence vortex
        low_coherence_vortex = self.framework.create_vortex_quantum_bridge(
            center=(0.0, 0.0, 0.0),
            strength=0.1
        )
        
        # Compute tunnel probabilities
        high_prob = self.framework.compute_repository_tunnel_probability(
            high_coherence_vortex
        )
        low_prob = self.framework.compute_repository_tunnel_probability(
            low_coherence_vortex
        )
        
        # Probabilities should be in [0, 1]
        self.assertGreaterEqual(high_prob, 0.0)
        self.assertLessEqual(high_prob, 1.0)
        self.assertGreaterEqual(low_prob, 0.0)
        self.assertLessEqual(low_prob, 1.0)
        
        # High coherence should give higher probability
        self.assertGreater(high_prob, low_prob)
    
    def test_complete_demonstration(self):
        """Test complete P=NP superfluidity demonstration."""
        result = self.framework.demonstrate_p_equals_np_superfluidity()
        
        # Should have all required fields
        self.assertIn('fundamental_frequency', result)
        self.assertIn('kappa_pi', result)
        self.assertIn('factor_seven', result)
        self.assertIn('num_dimensions', result)
        self.assertIn('layers', result)
        self.assertIn('superfluidity', result)
        self.assertIn('vortex_bridge', result)
        self.assertIn('tunnel_probability', result)
        self.assertIn('interpretation', result)
        
        # Check constants
        self.assertAlmostEqual(
            result['fundamental_frequency'],
            OMEGA_CRITICAL,
            places=2
        )
        self.assertAlmostEqual(
            result['kappa_pi'],
            KAPPA_PI,
            places=2
        )
        self.assertAlmostEqual(
            result['factor_seven'],
            1.0/7.0,
            places=6
        )
        
        # Check layers
        self.assertEqual(len(result['layers']), 7)
        
        # Check interpretation keys
        interp = result['interpretation']
        self.assertIn('fluids_as_tensors', interp)
        self.assertIn('laminar_flow', interp)
        self.assertIn('viscosity', interp)
        self.assertIn('vortex', interp)
        self.assertIn('p_equals_np', interp)
    
    def test_harmonic_alignment(self):
        """Test that frequencies are properly aligned harmonically."""
        layers = self.framework.initialize_laminar_flow(base_velocity=1.0)
        
        # Extract frequencies
        frequencies = [layer.frequency for layer in layers]
        
        # All frequencies should be multiples of f₀/7
        base = frequencies[0]
        step = base / 7.0
        
        for i, freq in enumerate(frequencies):
            expected = base * (1.0 + i/7.0)
            self.assertAlmostEqual(freq, expected, places=2)
    
    def test_different_dimensions(self):
        """Test framework with different number of dimensions."""
        # Test with 3, 7, and 13 dimensions
        for n_dims in [3, 7, 13]:
            framework = NavierStokesDimensionalTensor(num_dimensions=n_dims)
            layers = framework.initialize_laminar_flow(base_velocity=1.0)
            
            # Should have correct number of layers
            self.assertEqual(len(layers), n_dims)
            
            # Superfluidity check should work
            result = framework.check_superfluidity_condition(layers)
            self.assertIn('is_superfluid', result)
            self.assertIn('p_equals_np', result)
    
    def test_velocity_gradient(self):
        """Test that velocity forms proper gradient across layers."""
        layers = self.framework.initialize_laminar_flow(base_velocity=2.0)
        
        # Velocities should form a gradient
        velocities = [np.linalg.norm(layer.velocity) for layer in layers]
        
        # Should be monotonically decreasing
        for i in range(len(velocities) - 1):
            self.assertGreater(velocities[i], velocities[i+1])
    
    def test_factor_seven_application(self):
        """Test that 1/7 factor is properly applied."""
        # Check in frequency computation
        freq0 = self.framework.compute_layer_frequency(0)
        freq7 = self.framework.compute_layer_frequency(7)
        
        # After 7 steps, should be exactly double (one octave)
        self.assertAlmostEqual(freq7 / freq0, 2.0, places=4)
        
        # Each step should be f₀ * (1 + n/7)
        for n in range(8):
            freq = self.framework.compute_layer_frequency(n)
            expected = OMEGA_CRITICAL * (1.0 + n/7.0)
            self.assertAlmostEqual(freq, expected, places=2)


class TestFluidLayer(unittest.TestCase):
    """Test FluidLayer dataclass."""
    
    def test_fluid_layer_creation(self):
        """Test creating a fluid layer."""
        layer = FluidLayer(
            level=2,
            frequency=200.0,
            velocity=np.array([1.0, 0.0, 0.0]),
            gravity_weight=0.5
        )
        
        self.assertEqual(layer.level, 2)
        self.assertEqual(layer.frequency, 200.0)
        np.testing.assert_array_equal(layer.velocity, np.array([1.0, 0.0, 0.0]))
        self.assertEqual(layer.gravity_weight, 0.5)


class TestVortexPoint(unittest.TestCase):
    """Test VortexPoint dataclass."""
    
    def test_vortex_point_creation(self):
        """Test creating a vortex point."""
        vortex = VortexPoint(
            position=np.array([1.0, 2.0, 3.0]),
            angular_velocity=500.0,
            pressure=0.01,
            coherence=0.99
        )
        
        np.testing.assert_array_equal(vortex.position, np.array([1.0, 2.0, 3.0]))
        self.assertEqual(vortex.angular_velocity, 500.0)
        self.assertEqual(vortex.pressure, 0.01)
        self.assertEqual(vortex.coherence, 0.99)


if __name__ == '__main__':
    # Run tests with verbose output
    unittest.main(verbosity=2)
