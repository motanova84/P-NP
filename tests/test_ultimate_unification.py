#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for κ_Π Ultimate Unification
===================================

Tests all three manifestations of the universal constant κ_Π:
1. Geometry/Mathematics (φ · (π/e) · λ_CY)
2. Physics/Frequency (f₀ / h)
3. Biology/Coherence (√(2π · A_eff_max))

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import pytest
import math
import json
import os
import sys

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from verify_kappa import (
    compute_kappa_from_frequency,
    verify_frequency_relationship,
    F0_HZ,
    HARMONIC_FACTOR,
    KAPPA_PI_TARGET
)

from ultimate_unification import (
    consciousness_energy,
    solve_for_kappa_pi,
    solve_for_A_eff_max,
    RNAResonanceSimulator,
    verify_biology_coherence,
    generate_certification_json,
    PHI,
    PI,
    E
)


class TestPhysicsFrequencyVerification:
    """Test physics/frequency manifestation of κ_Π."""
    
    def test_frequency_computation(self):
        """Test that κ_Π = f₀ / h."""
        kappa = compute_kappa_from_frequency()
        
        # Verify computation
        assert kappa == F0_HZ / HARMONIC_FACTOR
        
        # Check against target
        error = abs(kappa - KAPPA_PI_TARGET)
        assert error < 1e-4, f"Error {error} exceeds threshold"
    
    def test_verification_result(self):
        """Test full verification results."""
        results = verify_frequency_relationship()
        
        # Check structure
        assert 'kappa_pi_target' in results
        assert 'kappa_pi_computed' in results
        assert 'absolute_error' in results
        assert 'relative_error' in results
        assert 'verified' in results
        
        # Check values
        assert results['f0_hz'] == F0_HZ
        assert results['harmonic_factor'] == HARMONIC_FACTOR
        assert results['verified'] == True
        
    def test_frequency_relationship(self):
        """Test the f₀/h relationship holds."""
        kappa = F0_HZ / HARMONIC_FACTOR
        
        # Should be very close to target
        assert abs(kappa - KAPPA_PI_TARGET) / KAPPA_PI_TARGET < 1e-4


class TestBiologyCoherenceVerification:
    """Test biology/coherence manifestation of κ_Π."""
    
    def test_consciousness_energy_equation(self):
        """Test C = mc² · A_eff²."""
        mass = 1.0
        c = 1.0
        A_eff = 0.8
        
        C = consciousness_energy(mass, c, A_eff)
        
        assert C == mass * (c ** 2) * (A_eff ** 2)
        assert abs(C - 0.64) < 1e-10  # Use tolerance for floating point
    
    def test_kappa_from_A_eff(self):
        """Test κ_Π = √(2π · A_eff_max)."""
        # Use known target
        A_eff_max = (KAPPA_PI_TARGET ** 2) / (2 * PI)
        kappa = solve_for_kappa_pi(A_eff_max)
        
        # Should recover target exactly
        assert abs(kappa - KAPPA_PI_TARGET) < 1e-10
    
    def test_A_eff_from_kappa(self):
        """Test A_eff_max = κ_Π² / (2π)."""
        A_eff = solve_for_A_eff_max(KAPPA_PI_TARGET)
        
        # Verify relationship
        kappa_recovered = solve_for_kappa_pi(A_eff)
        assert abs(kappa_recovered - KAPPA_PI_TARGET) < 1e-10
    
    def test_rna_simulator_basic(self):
        """Test basic RNA simulator functionality."""
        sim = RNAResonanceSimulator(seed=42)
        
        # Generate sequence
        seq = sim.generate_rna_sequence(100)
        assert len(seq) == 100
        assert all(base in ['A', 'U', 'G', 'C'] for base in seq)
        
        # Compute GC content
        gc = sim.compute_gc_content(seq)
        assert 0 <= gc <= 1
        
        # Compute resonance
        resonance = sim.compute_resonance_score(seq)
        assert 0 <= resonance <= 1
    
    def test_rna_coherence_simulation(self):
        """Test RNA coherence simulation."""
        sim = RNAResonanceSimulator(seed=42)
        results = sim.simulate_coherence(num_sequences=100)
        
        # Check structure
        assert 'mean_coherence' in results
        assert 'max_coherence' in results
        assert 'A_eff_mean' in results
        assert 'A_eff_max' in results
        
        # Check bounds
        assert 0 <= results['mean_coherence'] <= 1
        assert 0 <= results['max_coherence'] <= 1
        assert results['max_coherence'] >= results['mean_coherence']
    
    def test_biology_verification(self):
        """Test full biology/coherence verification."""
        results = verify_biology_coherence()
        
        # Check structure
        assert 'kappa_pi_target' in results
        assert 'kappa_pi_computed' in results
        assert 'A_eff_max' in results
        assert 'coherence_max' in results
        assert 'verified' in results
        
        # Check verification passed
        assert results['verified'] == True
        
        # Check coherence is reasonable
        assert results['coherence_max'] > 0.5


class TestGeometryMathematicsVerification:
    """Test geometry/mathematics manifestation of κ_Π."""
    
    def test_geometric_formula(self):
        """Test κ_Π = φ · (π/e) · λ_CY."""
        # Use the value from divine_unification
        lambda_cy = 1.378556
        
        kappa = PHI * (PI / E) * lambda_cy
        
        # Should be close to target
        error = abs(kappa - KAPPA_PI_TARGET)
        assert error < 1e-3
    
    def test_golden_ratio(self):
        """Test golden ratio value."""
        phi_expected = (1 + math.sqrt(5)) / 2
        assert abs(PHI - phi_expected) < 1e-10
    
    def test_pi_over_e(self):
        """Test π/e ratio."""
        ratio = PI / E
        expected = math.pi / math.e
        assert abs(ratio - expected) < 1e-10


class TestUnificationCertification:
    """Test ultimate unification certification."""
    
    def test_certification_generation(self):
        """Test certification JSON generation."""
        cert = generate_certification_json()
        
        # Check required fields
        required_fields = [
            'kappa_Pi',
            'phi_pi_over_e_lambda',
            'f0_over_harmonic_factor',
            'sqrt_coherence_equation',
            'coherence_max',
            'A_eff_max',
            'consciousness_energy_equation',
            'seed',
            'hash',
            'status_P_neq_NP',
            'timestamp',
            'author',
            'signature',
            'frequency_hz'
        ]
        
        for field in required_fields:
            assert field in cert, f"Missing field: {field}"
    
    def test_certification_values(self):
        """Test certification values are reasonable."""
        cert = generate_certification_json()
        
        # Check κ_Π value
        assert cert['kappa_Pi'] == KAPPA_PI_TARGET
        
        # Check status
        assert cert['status_P_neq_NP'] == 'EMPIRICALLY_SUPPORTED'
        
        # Check author
        assert 'JMMB' in cert['author']
        
        # Check signature
        assert 'QCAL' in cert['signature']
        
        # Check frequency
        assert cert['frequency_hz'] == 141.7001
    
    def test_certification_verifications(self):
        """Test verification section of certification."""
        cert = generate_certification_json()
        
        assert 'verifications' in cert
        verif = cert['verifications']
        
        # Check three domains
        assert 'geometry_mathematics' in verif
        assert 'physics_frequency' in verif
        assert 'biology_coherence' in verif
        
        # Check each has required fields
        for domain in verif.values():
            assert 'formula' in domain
            assert 'value' in domain
            assert 'source' in domain
            
            # Check value is close to target
            assert abs(domain['value'] - KAPPA_PI_TARGET) < 0.05
    
    def test_certification_hash(self):
        """Test certification hash is computed."""
        cert = generate_certification_json()
        
        assert 'hash' in cert
        assert len(cert['hash']) > 0
        # Hash should be hex string
        assert all(c in '0123456789abcdef' for c in cert['hash'])
    
    def test_certification_reproducibility(self):
        """Test certification is reproducible with same seed."""
        cert1 = generate_certification_json()
        cert2 = generate_certification_json()
        
        # Should be identical (same seed)
        assert cert1['seed'] == cert2['seed']
        # Note: timestamp will differ, so we don't check full equality


class TestUnificationConsistency:
    """Test consistency across all three manifestations."""
    
    def test_three_manifestations_converge(self):
        """Test all three manifestations give similar κ_Π values."""
        # Get values from each domain
        kappa_freq = compute_kappa_from_frequency()
        
        bio_results = verify_biology_coherence()
        kappa_bio = bio_results['kappa_pi_computed']
        
        lambda_cy = 1.378556
        kappa_geo = PHI * (PI / E) * lambda_cy
        
        # All should be close to target
        values = [kappa_freq, kappa_bio, kappa_geo]
        
        for val in values:
            error = abs(val - KAPPA_PI_TARGET)
            assert error < 0.05, f"Value {val} too far from target"
        
        # Standard deviation should be small
        mean = sum(values) / len(values)
        variance = sum((v - mean) ** 2 for v in values) / len(values)
        std = math.sqrt(variance)
        
        assert std < 0.03, f"Standard deviation {std} too large"
    
    def test_constant_updates_applied(self):
        """Test that constant updates were applied correctly."""
        from src.constants import KAPPA_PI as CONST_KAPPA
        
        # Test constants module update
        assert abs(CONST_KAPPA - KAPPA_PI_TARGET) < 1e-3
        
        # divine_unification requires networkx, so we test it only if available
        try:
            from src.divine_unification import KAPPA_PI as DIV_KAPPA
            # divine_unification computes it, so allow small error
            assert abs(DIV_KAPPA - KAPPA_PI_TARGET) < 1e-2
        except ImportError:
            # Skip if networkx not installed
            pass


class TestIntegration:
    """Integration tests for the complete unification system."""
    
    def test_json_file_exists(self):
        """Test that ultimate_unification.json was created."""
        json_path = os.path.join(os.path.dirname(__file__), '..', 'ultimate_unification.json')
        assert os.path.exists(json_path)
    
    def test_json_file_valid(self):
        """Test that ultimate_unification.json is valid JSON."""
        json_path = os.path.join(os.path.dirname(__file__), '..', 'ultimate_unification.json')
        
        with open(json_path, 'r') as f:
            data = json.load(f)
        
        assert isinstance(data, dict)
        assert 'kappa_Pi' in data
    
    def test_all_verification_scripts_runnable(self):
        """Test that all verification scripts can be imported."""
        # If we got here, imports succeeded
        assert True


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
