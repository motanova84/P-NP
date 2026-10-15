"""
Test suite for SovereignCoherenceMonitor
=========================================

Tests the sovereign coherence monitoring system including layer verification,
coherence peak detection, transmission execution, and ledger operations.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os
import pytest
import asyncio
import json
import tempfile
import shutil
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from echo_qcal.sovereign_coherence_monitor import SovereignCoherenceMonitor


@pytest.fixture
def temp_dir():
    """Fixture to provide temporary directory for tests."""
    with tempfile.TemporaryDirectory() as tmpdir:
        old_cwd = os.getcwd()
        os.chdir(tmpdir)
        yield tmpdir
        os.chdir(old_cwd)


class TestMonitorInitialization:
    """Test suite for SovereignCoherenceMonitor initialization."""
    
    def test_monitor_initialization(self, temp_dir):
        """Test that monitor initializes with correct parameters."""
        monitor = SovereignCoherenceMonitor()
        
        assert monitor.f0 == 141.7001
        assert monitor.tau0 == 1 / 141.7001
        assert monitor.sigma == 0.04
        assert monitor.verification_interval == 60
        assert monitor.coherence_check_interval == 0.001
        assert monitor.transmission_threshold == 0.0001
    
    def test_system_state_initialization(self, temp_dir):
        """Test that system state initializes correctly."""
        monitor = SovereignCoherenceMonitor()
        
        assert monitor.system_state['C_k_verified'] == False
        assert monitor.system_state['A_t_verified'] == False
        assert monitor.system_state['A_u_verified'] == False
        assert monitor.system_state['Cs_theorem_proven'] == False
        assert monitor.system_state['last_verification'] is None
        assert monitor.system_state['next_coherence_peak'] is None
        assert monitor.system_state['transmission_count'] == 0
    
    def test_lock_created(self, temp_dir):
        """Test that asyncio lock is created."""
        monitor = SovereignCoherenceMonitor()
        
        assert hasattr(monitor, 'system_state_lock')
        assert isinstance(monitor.system_state_lock, asyncio.Lock)
    
    def test_directories_created(self, temp_dir):
        """Test that config and log directories are created."""
        monitor = SovereignCoherenceMonitor()
        
        assert monitor.config_dir.exists()
        assert monitor.log_dir.exists()


class TestCryptographicLayerVerification:
    """Test suite for cryptographic layer (Cₖ) verification."""
    
    @pytest.mark.asyncio
    async def test_verify_cryptographic_layer_structure(self, temp_dir):
        """Test that cryptographic layer verification returns correct structure."""
        monitor = SovereignCoherenceMonitor()
        result = await monitor.verify_cryptographic_layer()
        
        assert 'verified' in result
        assert 'timestamp' in result
        assert isinstance(result['verified'], bool)
    
    @pytest.mark.asyncio
    async def test_verify_cryptographic_layer_with_mock(self, temp_dir):
        """Test cryptographic verification with mocked bitcoinlib."""
        monitor = SovereignCoherenceMonitor()
        
        with patch('echo_qcal.sovereign_coherence_monitor.Key') as MockKey:
            mock_key = MockKey.return_value
            mock_key.verify_message.return_value = True
            
            result = await monitor.verify_cryptographic_layer()
            
            assert result['verified'] == True
            assert 'address' in result
            assert 'message' in result
            assert 'signature_hash' in result
    
    @pytest.mark.asyncio
    async def test_verify_cryptographic_layer_error_handling(self, temp_dir):
        """Test error handling in cryptographic verification."""
        monitor = SovereignCoherenceMonitor()
        
        with patch('echo_qcal.sovereign_coherence_monitor.Key') as MockKey:
            mock_key = MockKey.return_value
            mock_key.verify_message.side_effect = Exception("Test error")
            
            result = await monitor.verify_cryptographic_layer()
            
            assert result['verified'] == False
            assert 'error' in result


class TestTemporalLayerVerification:
    """Test suite for temporal layer (Aₜ) verification."""
    
    @pytest.mark.asyncio
    async def test_verify_temporal_layer_structure(self, temp_dir):
        """Test that temporal layer verification returns correct structure."""
        monitor = SovereignCoherenceMonitor()
        result = await monitor.verify_temporal_layer()
        
        assert 'verified' in result
        assert 'block9_timestamp' in result
        assert 'delta_T_ms' in result
        assert 'coherence_percent' in result
        assert 'p_value' in result
        assert 'bayes_factor' in result
        assert 'phase' in result
        assert 'timestamp' in result
    
    @pytest.mark.asyncio
    async def test_temporal_constants_used(self, temp_dir):
        """Test that temporal verification uses named constants."""
        monitor = SovereignCoherenceMonitor()
        result = await monitor.verify_temporal_layer()
        
        # Block 9 timestamp should be the known constant
        assert result['block9_timestamp'] == 1231511700.000000
        
        # p_value should be calculated from constants
        assert isinstance(result['p_value'], float)
        assert result['p_value'] > 0
    
    @pytest.mark.asyncio
    async def test_temporal_phase_calculation(self, temp_dir):
        """Test that phase is calculated correctly."""
        monitor = SovereignCoherenceMonitor()
        result = await monitor.verify_temporal_layer()
        
        phase = result['phase']
        assert 0 <= phase < 1, "Phase must be in range [0, 1)"


class TestSemanticLayerVerification:
    """Test suite for semantic layer (Aᵤ) verification."""
    
    @pytest.mark.asyncio
    async def test_verify_semantic_layer_structure(self, temp_dir):
        """Test that semantic layer verification returns correct structure."""
        monitor = SovereignCoherenceMonitor()
        result = await monitor.verify_semantic_layer()
        
        assert 'verified' in result
        assert 'parameters_found' in result or 'error' in result
        assert 'timestamp' in result
    
    @pytest.mark.asyncio
    async def test_semantic_parameters_checked(self, temp_dir):
        """Test that semantic layer checks for required parameters."""
        monitor = SovereignCoherenceMonitor()
        result = await monitor.verify_semantic_layer()
        
        # If file is found, should have parameters_found
        if 'parameters_found' in result:
            params = result['parameters_found']
            assert 'f0_141.7001' in params
            assert 'sigma_0.04' in params
            assert 'harmonic_weights' in params
            assert 'no_random_noise' in params
    
    @pytest.mark.asyncio
    async def test_semantic_path_resolution(self, temp_dir):
        """Test that semantic layer uses proper path resolution."""
        monitor = SovereignCoherenceMonitor()
        
        # The path should be constructed using Path(__file__).parent.parent
        # This test verifies it doesn't fail due to relative path issues
        result = await monitor.verify_semantic_layer()
        
        # Should either find the file or return appropriate error
        assert 'verified' in result
    
    @pytest.mark.asyncio
    async def test_ast_random_check(self, temp_dir):
        """Test that AST-based random check works."""
        monitor = SovereignCoherenceMonitor()
        
        # Test with code that doesn't use random
        code_no_random = "import numpy as np\nx = np.sin(2 * np.pi * 141.7001)"
        result = monitor._check_no_random_usage(code_no_random)
        assert result == True
        
        # Test with code that uses random
        code_with_random = "import random\nx = random.uniform(0, 1)"
        result = monitor._check_no_random_usage(code_with_random)
        assert result == False
        
        # Test with np.random
        code_with_np_random = "import numpy as np\nx = np.random.uniform(0, 1)"
        result = monitor._check_no_random_usage(code_with_np_random)
        assert result == False


class TestCoherencePeakDetection:
    """Test suite for coherence peak detection."""
    
    @pytest.mark.asyncio
    async def test_calculate_next_coherence_peak(self, temp_dir):
        """Test that next coherence peak is calculated."""
        monitor = SovereignCoherenceMonitor()
        
        async with monitor.system_state_lock:
            initial_peak = monitor.system_state['next_coherence_peak']
        
        await monitor.calculate_next_coherence_peak()
        
        async with monitor.system_state_lock:
            new_peak = monitor.system_state['next_coherence_peak']
        
        assert new_peak is not None
        assert isinstance(new_peak, float)
    
    @pytest.mark.asyncio
    async def test_peak_is_in_future(self, temp_dir):
        """Test that calculated peak is in the future."""
        monitor = SovereignCoherenceMonitor()
        await monitor.calculate_next_coherence_peak()
        
        from datetime import datetime, timezone
        current_time = datetime.now(timezone.utc).timestamp()
        
        async with monitor.system_state_lock:
            next_peak = monitor.system_state['next_coherence_peak']
        
        if next_peak:
            assert next_peak > current_time


class TestTransmissionExecution:
    """Test suite for transmission execution."""
    
    @pytest.mark.asyncio
    async def test_activate_resonance_engine(self, temp_dir):
        """Test resonance engine activation."""
        monitor = SovereignCoherenceMonitor()
        result = await monitor.activate_resonance_engine()
        
        assert 'f0' in result
        assert 'sigma' in result
        assert 'harmonic_weights' in result
        assert 'cycles' in result
        assert 'coherence_score' in result
        assert 'phase_coherence' in result
        
        # Check that coherence score is deterministic (not random)
        assert result['coherence_score'] == 0.995
    
    @pytest.mark.asyncio
    async def test_generate_coherence_signature(self, temp_dir):
        """Test coherence signature generation."""
        monitor = SovereignCoherenceMonitor()
        result = await monitor.generate_coherence_signature()
        
        assert 'message' in result
        assert 'timestamp' in result
        assert 'phase' in result
        assert 'signature_simulated' in result
    
    @pytest.mark.asyncio
    async def test_calculate_current_phase(self, temp_dir):
        """Test current phase calculation."""
        monitor = SovereignCoherenceMonitor()
        phase = monitor.calculate_current_phase()
        
        assert isinstance(phase, float)
        assert 0 <= phase < 1


class TestLedgerOperations:
    """Test suite for ledger operations."""
    
    @pytest.mark.asyncio
    async def test_update_genesis_ledger(self, temp_dir):
        """Test ledger update functionality."""
        monitor = SovereignCoherenceMonitor()
        
        transmission_id = "test123"
        resonance_data = {
            'f0': 141.7001,
            'coherence_score': 0.995,
            'phase_coherence': True
        }
        coherence_signature = {
            'message': 'test',
            'timestamp': '2025-01-01T00:00:00Z',
            'phase': 0.5
        }
        
        result = await monitor.update_genesis_ledger(
            transmission_id,
            resonance_data,
            coherence_signature
        )
        
        assert 'entry_id' in result
        assert 'entry_hash' in result
        assert 'timestamp' in result
        assert 'coherence_phase' in result
        assert result['entry_id'] == transmission_id
    
    @pytest.mark.asyncio
    async def test_get_ledger_previous_hash(self, temp_dir):
        """Test getting previous ledger hash."""
        monitor = SovereignCoherenceMonitor()
        
        # First call should return initial hash
        initial_hash = monitor.get_ledger_previous_hash()
        assert initial_hash == '0' * 64
        
        # After adding entry, should return that entry's hash
        transmission_id = "test123"
        resonance_data = {'f0': 141.7001, 'coherence_score': 0.995, 'phase_coherence': True}
        coherence_signature = {'message': 'test', 'timestamp': '2025-01-01T00:00:00Z', 'phase': 0.5}
        
        entry = await monitor.update_genesis_ledger(
            transmission_id,
            resonance_data,
            coherence_signature
        )
        
        # Next call should return the entry's hash
        next_hash = monitor.get_ledger_previous_hash()
        assert next_hash == entry['entry_hash']
    
    @pytest.mark.asyncio
    async def test_emit_transmission_certificate(self, temp_dir):
        """Test certificate emission."""
        monitor = SovereignCoherenceMonitor()
        
        transmission_id = "test123"
        ledger_entry = {
            'entry_id': transmission_id,
            'entry_hash': 'abc123',
            'resonance_metrics': {
                'f0': 141.7001,
                'coherence_score': 0.995,
                'phase_coherence': True
            }
        }
        
        certificate = await monitor.emit_transmission_certificate(
            transmission_id,
            ledger_entry
        )
        
        assert isinstance(certificate, str)
        assert 'CERTIFICADO DE TRANSMISIÓN SOBERANA' in certificate
        assert transmission_id in certificate


class TestLoggingSystem:
    """Test suite for logging system."""
    
    def test_log_event(self, temp_dir):
        """Test that log_event writes correctly."""
        monitor = SovereignCoherenceMonitor()
        
        test_data = {
            'event': 'test_event',
            'value': 123
        }
        
        monitor.log_event(monitor.system_log, test_data)
        
        # Verify log file was created and contains data
        assert monitor.system_log.exists()
        
        with open(monitor.system_log, 'r') as f:
            logged = json.loads(f.read().strip())
        
        assert logged['event'] == 'test_event'
        assert logged['value'] == 123
        assert 'timestamp' in logged


class TestSystemState:
    """Test suite for system state management."""
    
    @pytest.mark.asyncio
    async def test_system_state_thread_safety(self, temp_dir):
        """Test that system state is thread-safe with lock."""
        monitor = SovereignCoherenceMonitor()
        
        # Test that we can acquire and release lock
        async with monitor.system_state_lock:
            monitor.system_state['test_value'] = 42
        
        async with monitor.system_state_lock:
            assert monitor.system_state['test_value'] == 42
    
    @pytest.mark.asyncio
    async def test_datetime_serialization(self, temp_dir):
        """Test that system state uses ISO strings for datetime."""
        monitor = SovereignCoherenceMonitor()
        
        # Simulate setting last_verification
        test_iso_string = '2025-01-01T00:00:00+00:00'
        
        async with monitor.system_state_lock:
            monitor.system_state['last_verification'] = test_iso_string
        
        # Should be able to serialize to JSON
        async with monitor.system_state_lock:
            state_copy = monitor.system_state.copy()
        
        json_str = json.dumps(state_copy)
        assert test_iso_string in json_str


class TestDisplayMethods:
    """Test suite for display methods."""
    
    def test_display_verification_results(self, temp_dir):
        """Test that display methods don't crash."""
        monitor = SovereignCoherenceMonitor()
        
        ck_result = {'verified': True, 'signature_hash': 'abc123'}
        at_result = {'verified': True, 'delta_T_ms': 1.2, 'coherence_percent': 99.9, 'p_value': 1e-6}
        au_result = {
            'verified': True,
            'parameters_found': {
                'f0_141.7001': True,
                'sigma_0.04': True,
                'harmonic_weights': True,
                'no_random_noise': True
            }
        }
        
        # Should not raise exception
        monitor.display_verification_results(ck_result, at_result, au_result)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
