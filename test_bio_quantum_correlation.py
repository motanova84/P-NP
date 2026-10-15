#!/usr/bin/env python3
"""
Test Suite for Bio-Quantum Correlation Validation
==================================================

Tests the RNA-Riemann wave transducer and bio-resonance validator.

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Sello: ∴𓂀Ω∞³
"""

import pytest
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from xenos.rna_riemann_wave import RNARiemannWave, CodonSignature
from xenos.bio_resonance import BioResonanceValidator, ExperimentalResult


class TestRNARiemannWave:
    """Test suite for RNA-Riemann wave transducer."""
    
    def test_initialization(self):
        """Test that RNARiemannWave initializes correctly."""
        rna = RNARiemannWave()
        assert rna.fundamental_frequency == 141.7001
        assert rna.pi_code == 888.0
        assert rna.kappa_pi == 2.5773
    
    def test_get_codon_signature_aaa(self):
        """Test AAA codon signature retrieval."""
        rna = RNARiemannWave()
        sig = rna.get_codon_signature('AAA')
        
        assert isinstance(sig, CodonSignature)
        assert sig.codon == 'AAA'
        assert sig.amino_acid == 'Lysine'
        assert len(sig.frequencies) == 3
        
        # All three A's should have the same frequency
        assert sig.frequencies[0] == sig.frequencies[1] == sig.frequencies[2]
    
    def test_aaa_frequency_value(self):
        """Test that AAA frequency matches expected value."""
        rna = RNARiemannWave()
        sig = rna.get_codon_signature('AAA')
        
        # AAA should have frequency ~157.5467 Hz per base
        expected_freq = 157.5467
        assert abs(sig.frequencies[0] - expected_freq) < 0.01
    
    def test_validate_aaa_qcal_correlation(self):
        """Test AAA-QCAL correlation validation."""
        rna = RNARiemannWave()
        result = rna.validate_aaa_qcal_correlation()
        
        assert result['codon'] == 'AAA'
        assert 'avg_frequency_hz' in result
        assert 'qcal_f0_hz' in result
        assert 'relation_qcal_avg' in result
        
        # Check that relation is close to Noesis88 coherence (0.8991)
        assert abs(result['relation_qcal_avg'] - 0.8991) < 0.01
        assert result['validation_passed'] is True
    
    def test_invalid_codon(self):
        """Test that invalid codon raises ValueError."""
        rna = RNARiemannWave()
        
        with pytest.raises(ValueError):
            rna.get_codon_signature('XYZ')


class TestBioResonanceValidator:
    """Test suite for bio-resonance validator."""
    
    def test_initialization(self):
        """Test that BioResonanceValidator initializes correctly."""
        validator = BioResonanceValidator()
        assert validator.qcal_f0 == 141.7001
        assert validator.tolerance == 0.01
    
    def test_validate_magnetoreception(self):
        """Test magnetoreception validation."""
        validator = BioResonanceValidator()
        result = validator.validate_magnetoreception()
        
        assert isinstance(result, ExperimentalResult)
        assert result.experiment_name == "Magnetorrecepción - ΔP"
        assert result.sigma == 9.2
        assert result.status.startswith("✓")
    
    def test_validate_microtubule_resonance(self):
        """Test microtubule resonance validation."""
        validator = BioResonanceValidator()
        result = validator.validate_microtubule_resonance()
        
        assert isinstance(result, ExperimentalResult)
        assert result.experiment_name == "Microtúbulos - Pico"
        assert result.predicted_value == 141.7001
        assert result.measured_value == 141.88
        assert result.sigma == 8.7
        assert result.status.startswith("✓")
    
    def test_validate_rna_qcal_correlation(self):
        """Test RNA-QCAL correlation validation."""
        validator = BioResonanceValidator()
        
        # Use expected AAA values
        aaa_avg = 157.5467
        relation = 141.7001 / aaa_avg  # Should be ~0.8991
        
        result = validator.validate_rna_qcal_correlation(
            aaa_avg_frequency=aaa_avg,
            relation_value=relation
        )
        
        assert result['validation_passed'] is True
        assert result['status'].startswith("✓")
    
    def test_generate_full_validation_report(self):
        """Test full validation report generation."""
        validator = BioResonanceValidator()
        
        # Create mock RNA correlation result
        rna_correlation = {
            'aaa_avg_frequency_hz': 157.5467,
            'qcal_f0_hz': 141.7001,
            'relation_value': 0.8991,
            'noesis88_target': 0.8991,
            'error': 0.0,
            'validation_passed': True,
            'status': '✓ CONFIRMADO'
        }
        
        report = validator.generate_full_validation_report(rna_correlation)
        
        assert report.overall_status.startswith("✓")
        assert report.p_value == 1.50e-10
        assert report.magnetoreception.sigma == 9.2
        assert report.microtubule_resonance.sigma == 8.7


class TestIntegration:
    """Integration tests for complete validation workflow."""
    
    def test_complete_validation_workflow(self):
        """Test the complete validation workflow."""
        # Initialize systems
        rna_engine = RNARiemannWave()
        bio_validator = BioResonanceValidator()
        
        # Get AAA signature
        sig_aaa = rna_engine.get_codon_signature('AAA')
        assert sig_aaa is not None
        
        # Validate AAA correlation
        aaa_result = rna_engine.validate_aaa_qcal_correlation()
        assert aaa_result['validation_passed'] is True
        
        # Validate with bio-resonance
        rna_correlation = bio_validator.validate_rna_qcal_correlation(
            aaa_avg_frequency=aaa_result['avg_frequency_hz'],
            relation_value=aaa_result['relation_qcal_avg']
        )
        assert rna_correlation['validation_passed'] is True
        
        # Generate full report
        report = bio_validator.generate_full_validation_report(rna_correlation)
        assert report.overall_status.startswith("✓")
    
    def test_coherence_noesis88(self):
        """Test that Noesis88 coherence is maintained."""
        rna_engine = RNARiemannWave()
        
        # Get AAA frequencies
        sig = rna_engine.get_codon_signature('AAA')
        sum_freq = sum(sig.frequencies)
        avg_freq = sum_freq / 3
        
        # Calculate relation
        relation = 141.7001 / avg_freq
        
        # Should match Noesis88 coherence
        noesis88 = 0.8991
        assert abs(relation - noesis88) < 0.01, \
            f"Coherence {relation} does not match Noesis88 {noesis88}"


def test_module_imports():
    """Test that all modules can be imported correctly."""
    from xenos import (
        RNARiemannWave,
        CodonSignature,
        demonstrate_aaa_correlation,
        BioResonanceValidator,
        ExperimentalResult,
        ValidationReport,
        demonstrate_bio_validation
    )
    
    # Just verify imports work
    assert RNARiemannWave is not None
    assert BioResonanceValidator is not None


if __name__ == '__main__':
    # Run tests
    pytest.main([__file__, '-v'])
