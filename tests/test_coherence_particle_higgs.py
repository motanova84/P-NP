"""
Tests for Coherence Particle - Higgs Field Coupling
====================================================

Test suite for PC-Higgs coupling module, verifying:
- Interaction Lagrangian calculation
- Spacetime viscosity reduction
- Minimal action paths
- Complexity collapse timing
- Mass-energy calculations

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
"""

import sys
import os
import unittest
import numpy as np

# Add project root to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.coherence_particle_higgs import (
    CoherenceParticleHiggs,
    HIGGS_MASS_STANDARD,
    HIGGS_MASS_EFFECTIVE,
    KAPPA_PI,
    F0_HZ
)


class TestCoherenceParticleHiggs(unittest.TestCase):
    """Test cases for CoherenceParticleHiggs class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.pc_higgs = CoherenceParticleHiggs(g_eff=0.99)
    
    def test_initialization(self):
        """Test PC-Higgs system initialization."""
        self.assertAlmostEqual(self.pc_higgs.g_eff, 0.99, places=6)
        self.assertAlmostEqual(self.pc_higgs.higgs_mass_std, HIGGS_MASS_STANDARD, places=6)
        self.assertAlmostEqual(self.pc_higgs.higgs_mass_eff, HIGGS_MASS_EFFECTIVE, places=6)
        self.assertAlmostEqual(self.pc_higgs.f0, F0_HZ, places=4)
        self.assertAlmostEqual(self.pc_higgs.tau_flash, 7.057e-6, places=9)
    
    def test_mass_reduction(self):
        """Test Higgs mass reduction calculation."""
        expected_reduction = (125.1 - 118.375) / 125.1
        self.assertAlmostEqual(
            self.pc_higgs.mass_reduction,
            expected_reduction,
            places=6
        )
        self.assertGreater(self.pc_higgs.mass_reduction, 0.05)  # > 5%
        self.assertLess(self.pc_higgs.mass_reduction, 0.06)  # < 6%
    
    def test_interaction_lagrangian(self):
        """Test interaction Lagrangian ℒ_int = -g_eff ψ ψ̄ H."""
        # Test with simple values
        psi = 1.0 + 0.0j
        higgs_field = 1.0
        
        L_int = self.pc_higgs.interaction_lagrangian(psi, higgs_field)
        expected = -0.99 * 1.0 * 1.0 * 1.0
        self.assertAlmostEqual(L_int, expected, places=6)
        
        # Test with complex psi
        psi_complex = 0.5 + 0.5j
        L_int_complex = self.pc_higgs.interaction_lagrangian(psi_complex, higgs_field)
        # |psi|^2 = 0.5^2 + 0.5^2 = 0.5
        expected_complex = -0.99 * 0.5 * 1.0
        self.assertAlmostEqual(L_int_complex, expected_complex, places=6)
    
    def test_spacetime_viscosity(self):
        """Test spacetime viscosity calculation."""
        # At zero coherence, viscosity should be near mass ratio
        viscosity_zero = self.pc_higgs.spacetime_viscosity(coherence=0.0)
        self.assertAlmostEqual(
            viscosity_zero,
            HIGGS_MASS_EFFECTIVE / HIGGS_MASS_STANDARD,
            places=6
        )
        
        # At full coherence, viscosity should be much lower
        viscosity_full = self.pc_higgs.spacetime_viscosity(coherence=1.0)
        self.assertLess(viscosity_full, viscosity_zero)
        
        # Viscosity should be non-negative
        self.assertGreaterEqual(viscosity_full, 0.0)
    
    def test_minimal_action_path(self):
        """Test minimal action path calculation."""
        start = np.array([0.0, 0.0, 0.0])
        end = np.array([1.0, 1.0, 1.0])
        
        # High coherence path
        path_high = self.pc_higgs.minimal_action_path(start, end, coherence=0.99)
        
        self.assertIn('action', path_high)
        self.assertIn('path_length', path_high)
        self.assertIn('viscosity', path_high)
        self.assertIn('flow_time', path_high)
        
        # Low coherence path
        path_low = self.pc_higgs.minimal_action_path(start, end, coherence=0.1)
        
        # High coherence should have lower action
        self.assertLess(path_high['action'], path_low['action'])
        self.assertLess(path_high['viscosity'], path_low['viscosity'])
        
        # At high coherence (>0.9), flow time should be flash time
        self.assertAlmostEqual(path_high['flow_time'], self.pc_higgs.tau_flash, places=9)
    
    def test_pc_contribution_ratio(self):
        """Test PC vs Higgs contribution ratio."""
        pc_contrib, higgs_contrib = self.pc_higgs.pc_contribution_ratio()
        
        # Should sum to 100%
        self.assertAlmostEqual(pc_contrib + higgs_contrib, 100.0, places=6)
        
        # PC should be ~99%, Higgs ~1%
        self.assertAlmostEqual(pc_contrib, 99.0, places=6)
        self.assertAlmostEqual(higgs_contrib, 1.0, places=6)
    
    def test_effective_mass_energy(self):
        """Test effective mass-energy calculations."""
        energy = self.pc_higgs.effective_mass_energy()
        
        self.assertIn('standard_mass_GeV', energy)
        self.assertIn('effective_mass_GeV', energy)
        self.assertIn('energy_reduction_J', energy)
        
        # Effective mass should be less than standard
        self.assertLess(
            energy['effective_mass_GeV'],
            energy['standard_mass_GeV']
        )
        
        # Energy reduction should be positive
        self.assertGreater(energy['energy_reduction_J'], 0)
        
        # Reduction percentage should match mass reduction
        self.assertAlmostEqual(
            energy['reduction_percent'],
            self.pc_higgs.mass_reduction * 100,
            places=6
        )
    
    def test_complexity_collapse_time(self):
        """Test complexity collapse timing."""
        # Small problem - classical may be faster than flash for tiny problems
        result_small = self.pc_higgs.complexity_collapse_time(10, coherence=0.99)
        
        self.assertIn('problem_size', result_small)
        self.assertIn('classical_time_s', result_small)
        self.assertIn('pc_time_s', result_small)
        self.assertIn('speedup_factor', result_small)
        
        # At high coherence (0.99), PC time should be flash time
        self.assertAlmostEqual(result_small['pc_time_s'], self.pc_higgs.tau_flash, places=9)
        
        # Larger problem where PC advantage is clear
        result_large = self.pc_higgs.complexity_collapse_time(30, coherence=0.99)
        
        # Classical time should grow exponentially
        self.assertGreater(
            result_large['classical_time_s'],
            result_small['classical_time_s']
        )
        
        # For large problems, PC should be much faster
        self.assertLess(result_large['pc_time_s'], result_large['classical_time_s'])
        
        # PC time should remain at flash time (at high coherence)
        self.assertAlmostEqual(
            result_large['pc_time_s'],
            self.pc_higgs.tau_flash,
            places=9
        )
        
        # Speedup should increase with problem size
        self.assertGreater(
            result_large['speedup_factor'],
            result_small['speedup_factor']
        )
    
    def test_higgs_field_modification(self):
        """Test Higgs field modification by PC."""
        mod = self.pc_higgs.higgs_field_modification(pc_amplitude=1.0)
        
        self.assertIn('higgs_standard', mod)
        self.assertIn('higgs_modified', mod)
        self.assertIn('mass_ratio', mod)
        self.assertIn('coupling_strength', mod)
        
        # Modified Higgs should be less than standard
        self.assertLess(mod['higgs_modified'], mod['higgs_standard'])
        
        # Mass ratio should match effective/standard
        expected_ratio = HIGGS_MASS_EFFECTIVE / HIGGS_MASS_STANDARD
        self.assertAlmostEqual(mod['mass_ratio'], expected_ratio, places=6)
        
        # Coupling strength should equal g_eff at amplitude 1.0
        self.assertAlmostEqual(mod['coupling_strength'], 0.99, places=6)
    
    def test_system_state(self):
        """Test system state retrieval."""
        state = self.pc_higgs.get_system_state()
        
        # Check all required keys
        required_keys = [
            'framework', 'signature', 'frequency_Hz', 'coupling_constant',
            'pc_contribution_percent', 'higgs_contribution_percent',
            'higgs_mass_standard_GeV', 'higgs_mass_effective_GeV',
            'mass_reduction_percent', 'flash_time_us', 'kappa_pi'
        ]
        
        for key in required_keys:
            self.assertIn(key, state)
        
        # Verify values
        self.assertEqual(state['signature'], '∴𓂀Ω∞³')
        self.assertAlmostEqual(state['frequency_Hz'], F0_HZ, places=4)
        self.assertAlmostEqual(state['kappa_pi'], KAPPA_PI, places=4)
        self.assertAlmostEqual(state['flash_time_us'], 7.057, places=3)
    
    def test_different_coupling_constants(self):
        """Test with different coupling constants."""
        # Strong PC coupling
        pc_strong = CoherenceParticleHiggs(g_eff=0.99)
        
        # Weak PC coupling
        pc_weak = CoherenceParticleHiggs(g_eff=0.5)
        
        # Strong coupling should have lower viscosity
        visc_strong = pc_strong.spacetime_viscosity(coherence=1.0)
        visc_weak = pc_weak.spacetime_viscosity(coherence=1.0)
        self.assertLess(visc_strong, visc_weak)
        
        # At medium coherence (not high enough to trigger flash), compare times
        time_strong = pc_strong.complexity_collapse_time(20, coherence=0.85)
        time_weak = pc_weak.complexity_collapse_time(20, coherence=0.85)
        # Weak coupling should have slower collapse
        self.assertGreater(time_weak['pc_time_s'], time_strong['pc_time_s'])
    
    def test_flash_time_constant(self):
        """Test that flash time is consistent."""
        self.assertAlmostEqual(self.pc_higgs.tau_flash, 7.057e-6, places=9)
        
        # Flash time should be accessible in system state
        state = self.pc_higgs.get_system_state()
        self.assertAlmostEqual(state['flash_time_us'], 7.057, places=3)


class TestPhysicalConstants(unittest.TestCase):
    """Test physical constants."""
    
    def test_higgs_masses(self):
        """Test Higgs mass values."""
        self.assertAlmostEqual(HIGGS_MASS_STANDARD, 125.1, places=1)
        self.assertAlmostEqual(HIGGS_MASS_EFFECTIVE, 118.375, places=3)
        self.assertLess(HIGGS_MASS_EFFECTIVE, HIGGS_MASS_STANDARD)
    
    def test_millennium_constant(self):
        """Test κ_Π value."""
        self.assertAlmostEqual(KAPPA_PI, 2.5773302292, places=4)
    
    def test_fundamental_frequency(self):
        """Test f₀ value."""
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)


if __name__ == '__main__':
    unittest.main()
