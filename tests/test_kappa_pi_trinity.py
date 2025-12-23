#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Kappa Pi Trinity Module
==================================

Comprehensive tests verifying the trinity unification of κ_Π.

Author: José Manuel Mota Burruezo (ICQ · 2025)
"""

import pytest
import math
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.kappa_pi_trinity import (
    PHI, PI, E, LAMBDA_CY, KAPPA_PI_TARGET, F0_FREQUENCY,
    GeometryDerivation,
    PhysicsDerivation,
    BiologyDerivation,
    KappaPiTrinity,
)


class TestConstants:
    """Test fundamental constants."""
    
    def test_phi_golden_ratio(self):
        """Test golden ratio value."""
        expected = (1 + math.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10
    
    def test_kappa_pi_target(self):
        """Test target κ_Π value."""
        assert abs(KAPPA_PI_TARGET - 2.5773) < 1e-10
    
    def test_frequency(self):
        """Test QCAL frequency."""
        assert abs(F0_FREQUENCY - 141.7001) < 1e-10


class TestGeometryDerivation:
    """Test geometry/mathematics derivation of κ_Π."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.geo = GeometryDerivation()
    
    def test_calculate(self):
        """Test geometric calculation."""
        kappa = self.geo.calculate()
        assert kappa > 0
        assert abs(kappa - KAPPA_PI_TARGET) < 0.01
    
    def test_verify(self):
        """Test verification passes."""
        assert self.geo.verify(tolerance=0.01)
    
    def test_components(self):
        """Test component extraction."""
        components = self.geo.get_components()
        
        assert 'phi' in components
        assert 'pi' in components
        assert 'e' in components
        assert 'lambda_cy' in components
        assert 'pi_over_e' in components
        assert 'kappa_pi' in components
        
        # Check pi/e calculation
        assert abs(components['pi_over_e'] - (PI / E)) < 1e-10
        
        # Check final kappa_pi
        expected = PHI * (PI / E) * LAMBDA_CY
        assert abs(components['kappa_pi'] - expected) < 1e-10
    
    def test_formula_correctness(self):
        """Test that formula produces correct value."""
        # Manual calculation
        kappa_manual = PHI * (PI / E) * LAMBDA_CY
        kappa_method = self.geo.calculate()
        
        assert abs(kappa_manual - kappa_method) < 1e-10


class TestPhysicsDerivation:
    """Test physics/frequency derivation of κ_Π."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.phys = PhysicsDerivation()
    
    def test_calculate(self):
        """Test physics calculation."""
        kappa = self.phys.calculate()
        assert kappa > 0
        assert abs(kappa - KAPPA_PI_TARGET) < 0.01
    
    def test_verify(self):
        """Test verification passes."""
        assert self.phys.verify(tolerance=0.01)
    
    def test_harmonic_factor(self):
        """Test harmonic factor calculation."""
        factor = self.phys.calculate_harmonic_factor()
        
        # Harmonic factor should be positive
        assert factor > 0
        
        # Should relate f0 and kappa_pi
        kappa_from_factor = F0_FREQUENCY / factor
        assert abs(kappa_from_factor - KAPPA_PI_TARGET) < 0.01
    
    def test_components(self):
        """Test component extraction."""
        components = self.phys.get_components()
        
        assert 'f0' in components
        assert 'harmonic_factor' in components
        assert 'kappa_pi' in components
        
        assert components['f0'] == F0_FREQUENCY
    
    def test_frequency_relationship(self):
        """Test relationship between frequency and kappa_pi."""
        components = self.phys.get_components()
        
        # Verify: f0 / harmonic_factor = kappa_pi
        calculated = components['f0'] / components['harmonic_factor']
        assert abs(calculated - components['kappa_pi']) < 1e-10


class TestBiologyDerivation:
    """Test biology/coherence derivation of κ_Π."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.bio = BiologyDerivation()
    
    def test_calculate(self):
        """Test biology calculation."""
        kappa = self.bio.calculate()
        assert kappa > 0
        assert abs(kappa - KAPPA_PI_TARGET) < 0.01
    
    def test_verify(self):
        """Test verification passes."""
        assert self.bio.verify(tolerance=0.01)
    
    def test_a_eff_max(self):
        """Test maximum effective area calculation."""
        a_eff = self.bio.calculate_a_eff_max()
        
        # Should be positive
        assert a_eff > 0
        
        # Should satisfy: kappa = sqrt(2*pi*a_eff)
        kappa_from_area = math.sqrt(2 * PI * a_eff)
        assert abs(kappa_from_area - KAPPA_PI_TARGET) < 0.01
    
    def test_components(self):
        """Test component extraction."""
        components = self.bio.get_components()
        
        assert 'a_eff_max' in components
        assert 'two_pi_a_eff' in components
        assert 'kappa_pi' in components
        
        # Verify relationship
        assert abs(components['two_pi_a_eff'] - 2 * PI * components['a_eff_max']) < 1e-10
    
    def test_sqrt_relationship(self):
        """Test square root relationship."""
        components = self.bio.get_components()
        
        # Verify: sqrt(2*pi*a_eff) = kappa_pi
        calculated = math.sqrt(components['two_pi_a_eff'])
        assert abs(calculated - components['kappa_pi']) < 1e-10


class TestKappaPiTrinity:
    """Test the complete trinity unification."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.trinity = KappaPiTrinity()
    
    def test_verify_all(self):
        """Test that all three derivations verify."""
        verifications = self.trinity.verify_all(tolerance=0.01)
        
        assert verifications['geometry']
        assert verifications['physics']
        assert verifications['biology']
    
    def test_calculate_all(self):
        """Test calculation from all three paths."""
        values = self.trinity.calculate_all()
        
        assert 'geometry' in values
        assert 'physics' in values
        assert 'biology' in values
        assert 'target' in values
        
        # All should be close to target
        assert abs(values['geometry'] - KAPPA_PI_TARGET) < 0.01
        assert abs(values['physics'] - KAPPA_PI_TARGET) < 0.01
        assert abs(values['biology'] - KAPPA_PI_TARGET) < 0.01
        assert values['target'] == KAPPA_PI_TARGET
    
    def test_convergence(self):
        """Test convergence metrics."""
        convergence = self.trinity.get_convergence()
        
        assert 'mean_kappa_pi' in convergence
        assert 'target_kappa_pi' in convergence
        assert 'max_deviation' in convergence
        assert 'converged' in convergence
        
        # Mean should be close to target
        assert abs(convergence['mean_kappa_pi'] - KAPPA_PI_TARGET) < 0.01
        
        # Should converge
        assert convergence['converged']
        assert convergence['max_deviation'] < 0.01
    
    def test_individual_deviations(self):
        """Test individual path deviations."""
        convergence = self.trinity.get_convergence()
        
        # Each deviation should be small
        assert convergence['geometry_deviation'] < 0.01
        assert convergence['physics_deviation'] < 0.01
        assert convergence['biology_deviation'] < 0.01
    
    def test_is_master_constant(self):
        """Test master constant verification."""
        assert self.trinity.is_master_constant(tolerance=0.01)
    
    def test_full_report(self):
        """Test full report generation."""
        report = self.trinity.get_full_report()
        
        # Check structure
        assert 'target_constant' in report
        assert 'geometry' in report
        assert 'physics' in report
        assert 'biology' in report
        assert 'convergence' in report
        assert 'is_master_constant' in report
        
        # Check each path has required fields
        for path in ['geometry', 'physics', 'biology']:
            assert 'value' in report[path]
            assert 'verified' in report[path]
            assert 'components' in report[path]
            assert report[path]['verified']
        
        # Master constant should be verified
        assert report['is_master_constant']
    
    def test_convergence_quality(self):
        """Test quality of convergence."""
        values = self.trinity.calculate_all()
        
        # Calculate variance among the three values
        vals = [values['geometry'], values['physics'], values['biology']]
        mean = sum(vals) / len(vals)
        variance = sum((v - mean) ** 2 for v in vals) / len(vals)
        
        # Variance should be very small (tight convergence)
        assert variance < 1e-10


class TestTrinityIntegration:
    """Integration tests for trinity unification."""
    
    def test_all_paths_produce_same_value(self):
        """Test that all three paths produce the same κ_Π value."""
        trinity = KappaPiTrinity()
        
        geo_value = trinity.geometry.calculate()
        phys_value = trinity.physics.calculate()
        bio_value = trinity.biology.calculate()
        
        # All should be very close to each other
        assert abs(geo_value - phys_value) < 0.01
        assert abs(phys_value - bio_value) < 0.01
        assert abs(bio_value - geo_value) < 0.01
    
    def test_consistency_with_divine_unification(self):
        """Test consistency with existing divine_unification module."""
        from src.divine_unification import KAPPA_PI as DIV_KAPPA_PI
        
        trinity = KappaPiTrinity()
        trinity_kappa = trinity.geometry.calculate()
        
        # Should match the KAPPA_PI from divine_unification
        assert abs(trinity_kappa - DIV_KAPPA_PI) < 0.01
    
    def test_reproducibility(self):
        """Test that calculations are reproducible."""
        trinity1 = KappaPiTrinity()
        trinity2 = KappaPiTrinity()
        
        report1 = trinity1.get_full_report()
        report2 = trinity2.get_full_report()
        
        # Should produce identical results
        assert report1['geometry']['value'] == report2['geometry']['value']
        assert report1['physics']['value'] == report2['physics']['value']
        assert report1['biology']['value'] == report2['biology']['value']


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
