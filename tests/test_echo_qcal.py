"""
Test suite for the echo_qcal verification system
=================================================

Tests the Teorema de Coherencia Soberana (ℂₛ) verification system,
including all three layers: Cₖ, Aₜ, and Aᵤ.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import pytest
import numpy as np

# Add echo_qcal to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from echo_qcal import (
    verify_cryptographic_layer,
    verify_temporal_alignment,
    verify_unitary_architecture,
    generate_certificate,
    ResonantNexusEngine
)


class TestCryptographicLayer:
    """Test suite for Cₖ (Cryptographic Layer) verification."""
    
    def test_verify_cryptographic_layer(self):
        """Test that cryptographic layer verification returns correct status."""
        result = verify_cryptographic_layer()
        
        assert result['layer'] == 'Cₖ (Cryptographic)'
        assert result['status'] == 'VERIFIED'
        assert result['genesis_address'] == '1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa'
        assert 'timestamp' in result
    
    def test_genesis_address_format(self):
        """Test that genesis address has correct format."""
        result = verify_cryptographic_layer()
        address = result['genesis_address']
        
        # Bitcoin address starts with 1
        assert address.startswith('1')
        # Bitcoin address length is typically 26-35 characters
        assert 26 <= len(address) <= 35


class TestTemporalAlignment:
    """Test suite for Aₜ (Temporal/Cosmological Layer) verification."""
    
    def test_verify_temporal_alignment(self):
        """Test that temporal alignment verification returns correct status."""
        result = verify_temporal_alignment()
        
        assert result['layer'] == 'Aₜ (Cosmological/Temporal)'
        assert result['status'] == 'VERIFIED'
        assert result['base_frequency'] == 141.7001
        assert 'timestamp' in result
    
    def test_qcal_frequency(self):
        """Test that QCAL frequency is correct."""
        result = verify_temporal_alignment()
        
        f0 = result['base_frequency']
        assert f0 == 141.7001, "Base frequency must be 141.7001 Hz"
    
    def test_temporal_deviation(self):
        """Test that temporal deviation is within expected range."""
        result = verify_temporal_alignment()
        
        delta_t_ms = result['temporal_deviation_ms']
        # Should be approximately 3.514 ms
        assert 3.0 < delta_t_ms < 4.0, "Temporal deviation should be ~3.514 ms"
    
    def test_statistical_significance(self):
        """Test that p-value indicates high significance."""
        result = verify_temporal_alignment()
        
        p_value = result['p_value']
        # Should be highly significant (p < 10^-5)
        assert p_value < 1e-5, "P-value should be < 10^-5 for high significance"


class TestUnitaryArchitecture:
    """Test suite for Aᵤ (Unitary Architecture Layer) verification."""
    
    def test_verify_unitary_architecture(self):
        """Test that unitary architecture verification returns correct status."""
        result = verify_unitary_architecture()
        
        assert result['layer'] == 'Aᵤ (Semantic/Unitary Architecture)'
        assert result['status'] == 'VERIFIED'
        assert 'timestamp' in result
    
    def test_qcal_parameters(self):
        """Test that QCAL parameters are exactly correct."""
        result = verify_unitary_architecture()
        
        # Base frequency
        assert result['base_frequency']['match'] == True
        assert result['base_frequency']['expected'] == 141.7001
        assert result['base_frequency']['difference'] < 1e-10
        
        # Volatility
        assert result['volatility']['match'] == True
        assert result['volatility']['expected'] == 0.04
        assert result['volatility']['difference'] < 1e-10
        
        # Harmonic weights
        assert result['harmonic_weights']['match'] == True
        assert result['harmonic_weights']['expected'] == [0.5, 0.3, 0.15, 0.05]
        assert all(d < 1e-10 for d in result['harmonic_weights']['differences'])
    
    def test_architecture_components(self):
        """Test that all architecture components are present."""
        result = verify_unitary_architecture()
        
        arch = result['architecture']
        assert arch['ResonantNexusEngine_class'] == True
        assert arch['harmonic_generation'] == True
        assert arch['coherent_noise'] == True
        assert arch['match'] == True


class TestResonantNexusEngine:
    """Test suite for ResonantNexusEngine class."""
    
    def test_engine_initialization(self):
        """Test that engine initializes with correct parameters."""
        engine = ResonantNexusEngine(
            base_frequency=141.7001,
            volatility=0.04,
            harmonic_weights=[0.5, 0.3, 0.15, 0.05]
        )
        
        assert engine.base_frequency == 141.7001
        assert engine.volatility == 0.04
        assert engine.harmonic_weights == [0.5, 0.3, 0.15, 0.05]
    
    def test_default_parameters(self):
        """Test that engine uses correct default parameters."""
        engine = ResonantNexusEngine()
        
        assert engine.base_frequency == 141.7001
        assert engine.volatility == 0.04
        assert engine.harmonic_weights == [0.5, 0.3, 0.15, 0.05]
    
    def test_harmonic_generation(self):
        """Test that harmonic generation works correctly."""
        engine = ResonantNexusEngine()
        time_points = np.linspace(0, 1, 100)
        
        harmonics = engine.generate_harmonics(time_points)
        
        assert len(harmonics) == len(time_points)
        assert isinstance(harmonics, np.ndarray)
        # Signal should be bounded by sum of weights (approximately)
        assert harmonics.min() >= -1.5
        assert harmonics.max() <= 1.5
    
    def test_coherent_noise(self):
        """Test that coherent noise is added correctly."""
        engine = ResonantNexusEngine()
        signal = np.array([0.0] * 100)
        
        noisy_signal = engine.add_coherent_noise(signal)
        
        assert len(noisy_signal) == len(signal)
        assert isinstance(noisy_signal, np.ndarray)
        # Noise should not be all zeros
        assert not np.allclose(noisy_signal, signal)
    
    def test_harmonic_weights_sum(self):
        """Test that harmonic weights sum to expected value."""
        engine = ResonantNexusEngine()
        weights_sum = sum(engine.harmonic_weights)
        
        # Should sum to 1.0
        assert abs(weights_sum - 1.0) < 1e-10


class TestCertificateGeneration:
    """Test suite for certificate generation."""
    
    def test_generate_certificate(self):
        """Test that certificate generation works."""
        certificate = generate_certificate()
        
        assert isinstance(certificate, str)
        assert 'ℂₛ' in certificate
        assert 'DEMOSTRADO' in certificate
        # Certificate contains the frequency in summary output, not in certificate box itself
    
    def test_certificate_file_created(self):
        """Test that certificate file is created."""
        generate_certificate()
        cert_path = os.path.join(
            os.path.dirname(__file__), 
            '..', 
            'teorema_Cs_certificado.txt'
        )
        
        assert os.path.exists(cert_path)


class TestTeoremaCs:
    """Test suite for complete Teorema ℂₛ verification."""
    
    def test_all_layers_verified(self):
        """Test that all three layers verify successfully."""
        ck_result = verify_cryptographic_layer()
        at_result = verify_temporal_alignment()
        au_result = verify_unitary_architecture()
        
        assert ck_result['status'] == 'VERIFIED'
        assert at_result['status'] == 'VERIFIED'
        assert au_result['status'] == 'VERIFIED'
    
    def test_teorema_conjunction(self):
        """Test that ℂₛ = Cₖ ∧ Aₜ ∧ Aᵤ = True."""
        ck_result = verify_cryptographic_layer()
        at_result = verify_temporal_alignment()
        au_result = verify_unitary_architecture()
        
        Ck = ck_result['status'] == 'VERIFIED'
        At = at_result['status'] == 'VERIFIED'
        Au = au_result['status'] == 'VERIFIED'
        
        # Teorema ℂₛ
        Cs = Ck and At and Au
        
        assert Cs == True, "Teorema ℂₛ must be True"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
