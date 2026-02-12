#!/usr/bin/env python3
"""
Test Suite for QCAL Biosensor Omega Integration
================================================

Tests for RNAVolatileMemory, BiosensorHub, and DisharmonyDetector.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ
"""

import sys
import os
import math
from datetime import datetime, timedelta

# Add qcal to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from qcal.rna_volatile_memory import RNAVolatileMemory, F0_QCAL, PHI
from qcal.biosensor_hub import BiosensorHub, BiosensorType, CONSCIOUSNESS_THRESHOLD
from qcal.disharmony_detector import DisharmonyDetector, DisharmonyLevel


class TestRNAVolatileMemory:
    """Test suite for RNA Volatile Memory."""
    
    def test_initialization(self):
        """Test that RNAVolatileMemory initializes correctly."""
        memory = RNAVolatileMemory()
        
        assert memory.f0 == F0_QCAL
        assert memory.phi == PHI
        assert memory.tau == 10.0
        assert len(memory.memory_states) == 0
    
    def test_psi_decay_calculation(self):
        """Test the Ψ(t) decay calculation."""
        memory = RNAVolatileMemory()
        
        # At t=0, Ψ should equal Ψ₀
        psi_0 = 1.0
        psi_t0 = memory.calculate_psi_decay(psi_0, t=0)
        assert abs(psi_t0 - psi_0) < 0.001
        
        # At t>0, Ψ should decay
        psi_t5 = memory.calculate_psi_decay(psi_0, t=5)
        assert psi_t5 < psi_0
        
        # Check decay formula: Ψ(t) = Ψ₀ · exp(-t/τ) · cos(2πf₀t)
        t = 5.0
        expected = psi_0 * math.exp(-t / memory.tau) * math.cos(2 * math.pi * memory.f0 * t)
        assert abs(psi_t5 - expected) < 0.001
    
    def test_emit_information(self):
        """Test information emanation."""
        memory = RNAVolatileMemory()
        
        info = {'test': 'data', 'value': 42}
        state = memory.emit_information(info, psi_0=0.9)
        
        assert state.psi_amplitude == 0.9
        assert state.frequency_hz == F0_QCAL
        assert state.information_content == info
        assert state.coherence_level == 1.0  # Max at emission
        assert len(memory.memory_states) == 1
    
    def test_read_information(self):
        """Test information reading with decay."""
        memory = RNAVolatileMemory()
        
        info = {'message': 'test'}
        memory.emit_information(info, psi_0=1.0)
        
        # Read immediately
        result = memory.read_information()
        assert result['coherence'] > 0.9
        assert result['is_readable'] is True
        assert result['information'] == info
    
    def test_therapeutic_frequency(self):
        """Test therapeutic frequency calculation."""
        memory = RNAVolatileMemory()
        
        # f_therapeutic = 141.7001 Hz × coherence × Φ
        coherence = 0.8
        freq = memory.calculate_therapeutic_frequency(coherence)
        
        expected = F0_QCAL * coherence * PHI
        assert abs(freq - expected) < 0.01
        
        # Check specific value
        assert abs(freq - 183.52) < 1.0
    
    def test_sello_and_emanacion(self):
        """Test that seal and emanation are present."""
        from qcal.rna_volatile_memory import __sello__, __emanacion__
        
        assert __sello__ == "∴𓂀Ω∞³Φ"
        assert "141.7001 Hz" in __emanacion__
        assert "Φ" in __emanacion__


class TestBiosensorHub:
    """Test suite for Biosensor Hub."""
    
    def test_initialization(self):
        """Test that BiosensorHub initializes correctly."""
        hub = BiosensorHub()
        
        assert hub.f0 == F0_QCAL
        assert hub.phi == PHI
        assert len(hub.readings) == 0
        assert len(hub.coherence_profiles) == 0
    
    def test_add_reading(self):
        """Test adding biosensor readings."""
        hub = BiosensorHub()
        
        reading = hub.add_reading(BiosensorType.EEG, 65.0, frequency_hz=40.0)
        
        assert reading.sensor_type == BiosensorType.EEG
        assert reading.raw_value == 65.0
        assert reading.frequency_hz == 40.0
        assert 0 <= reading.psi_coherence <= 1
        assert len(hub.readings) == 1
    
    def test_coherence_calculation(self):
        """Test total coherence calculation."""
        hub = BiosensorHub()
        
        # Test the formula: Ψ_total = √(Ψ₁² + Ψ₂² + Ψ₃² + Ψ₄²) / 2
        psi_total = hub.calculate_total_coherence(0.8, 0.7, 0.6, 0.5)
        
        expected = math.sqrt(0.8**2 + 0.7**2 + 0.6**2 + 0.5**2) / 2.0
        assert abs(psi_total - expected) < 0.001
        
        # Should be in range [0, 1]
        assert 0 <= psi_total <= 1
    
    def test_create_coherence_profile(self):
        """Test coherence profile creation."""
        hub = BiosensorHub()
        
        # Add some readings
        hub.add_reading(BiosensorType.EEG, 65.0)
        hub.add_reading(BiosensorType.HRV, 120.0)
        hub.add_reading(BiosensorType.GSR, 8.0)
        hub.add_reading(BiosensorType.RESPIRATORY, 7.0)
        
        profile = hub.create_coherence_profile()
        
        assert 0 <= profile.psi_total <= 1
        assert 0 <= profile.consciousness_level <= 1
        assert isinstance(profile.is_conscious, bool)
        assert len(hub.coherence_profiles) == 1
    
    def test_consciousness_threshold(self):
        """Test consciousness threshold detection."""
        hub = BiosensorHub()
        
        # High coherence - should be conscious
        profile_high = hub.create_coherence_profile(
            psi_cerebral=0.8,
            psi_cardiaca=0.7,
            psi_emocional=0.6,
            psi_respiratorio=0.5
        )
        assert profile_high.psi_total > CONSCIOUSNESS_THRESHOLD
        assert profile_high.is_conscious is True
        
        # Low coherence - should not be conscious
        profile_low = hub.create_coherence_profile(
            psi_cerebral=0.2,
            psi_cardiaca=0.2,
            psi_emocional=0.2,
            psi_respiratorio=0.2
        )
        assert profile_low.psi_total < CONSCIOUSNESS_THRESHOLD
        assert profile_low.is_conscious is False


class TestDisharmonyDetector:
    """Test suite for Disharmony Detector."""
    
    def test_initialization(self):
        """Test that DisharmonyDetector initializes correctly."""
        detector = DisharmonyDetector()
        
        assert detector.f0 == F0_QCAL
        assert detector.phi == PHI
        assert detector.baseline is None
        assert len(detector.disharmony_reports) == 0
    
    def test_set_baseline(self):
        """Test setting baseline coherence."""
        detector = DisharmonyDetector()
        
        baseline = detector.set_baseline(psi_baseline=0.85)
        
        assert baseline.psi_baseline == 0.85
        assert baseline.frequency_baseline_hz == F0_QCAL
        assert baseline.therapeutic_frequency_hz > 0
        assert detector.baseline is not None
    
    def test_therapeutic_frequency_calculation(self):
        """Test therapeutic frequency calculation."""
        detector = DisharmonyDetector()
        
        # f_therapeutic = 141.7001 Hz × coherence × Φ
        coherence = 0.7
        freq = detector.calculate_therapeutic_frequency(coherence)
        
        expected = F0_QCAL * coherence * PHI
        assert abs(freq - expected) < 0.01
    
    def test_disharmony_classification(self):
        """Test disharmony level classification."""
        detector = DisharmonyDetector()
        
        # Test different coherence levels
        assert detector._classify_disharmony(0.9) == DisharmonyLevel.COHERENT
        assert detector._classify_disharmony(0.7) == DisharmonyLevel.SLIGHT_DISHARMONY
        assert detector._classify_disharmony(0.5) == DisharmonyLevel.MODERATE_DISHARMONY
        assert detector._classify_disharmony(0.3) == DisharmonyLevel.SEVERE_DISHARMONY
        assert detector._classify_disharmony(0.1) == DisharmonyLevel.CRITICAL_DISHARMONY
    
    def test_detect_disharmony(self):
        """Test disharmony detection."""
        detector = DisharmonyDetector()
        detector.set_baseline(psi_baseline=0.85)
        
        # Moderate disharmony
        report = detector.detect_disharmony(psi_current=0.55)
        
        assert report.psi_current == 0.55
        assert report.psi_baseline == 0.85
        assert report.deviation > 0
        assert report.disharmony_level == DisharmonyLevel.MODERATE_DISHARMONY
        assert report.therapeutic_frequency_hz > 0
        assert len(report.recommendations) > 0
        assert len(detector.disharmony_reports) == 1
    
    def test_gamma_band_reset(self):
        """Test gamma band reset detection."""
        detector = DisharmonyDetector()
        detector.set_baseline(psi_baseline=0.85)
        
        # Low coherence should trigger gamma reset
        report_low = detector.detect_disharmony(psi_current=0.3)
        assert report_low.gamma_band_reset_needed is True
        
        # High coherence should not trigger gamma reset
        report_high = detector.detect_disharmony(psi_current=0.8)
        assert report_high.gamma_band_reset_needed is False
    
    def test_phi_harmonic(self):
        """Test Φ harmonic calculation (229.4 Hz)."""
        from qcal.disharmony_detector import F_THERAPEUTIC_HARMONIC
        
        # 141.7001 Hz × Φ ≈ 229.4 Hz
        expected = F0_QCAL * PHI
        assert abs(F_THERAPEUTIC_HARMONIC - expected) < 0.01
        assert abs(F_THERAPEUTIC_HARMONIC - 229.4) < 1.0


class TestIntegration:
    """Integration tests for the complete biosensor system."""
    
    def test_full_workflow(self):
        """Test complete workflow: Memory → Hub → Detector."""
        # 1. Create memory and emit patient data
        memory = RNAVolatileMemory()
        patient_data = {'id': 'test123', 'baseline': 0.85}
        memory.emit_information(patient_data)
        
        # 2. Create hub and add readings
        hub = BiosensorHub()
        hub.add_reading(BiosensorType.EEG, 65.0, frequency_hz=40.0)
        hub.add_reading(BiosensorType.HRV, 120.0)
        hub.add_reading(BiosensorType.GSR, 8.0)
        hub.add_reading(BiosensorType.RESPIRATORY, 7.0)
        
        # 3. Create coherence profile
        profile = hub.create_coherence_profile()
        
        # 4. Create detector and detect disharmony
        detector = DisharmonyDetector()
        detector.set_baseline(psi_baseline=0.85)
        report = detector.detect_disharmony(psi_current=profile.psi_total)
        
        # Verify complete workflow
        assert len(memory.memory_states) > 0
        assert len(hub.readings) == 4
        assert len(hub.coherence_profiles) > 0
        assert len(detector.disharmony_reports) > 0
        assert report.therapeutic_frequency_hz > 0
    
    def test_export_functionality(self):
        """Test export to dict functionality."""
        memory = RNAVolatileMemory()
        hub = BiosensorHub()
        detector = DisharmonyDetector()
        
        # Export all components
        memory_dict = memory.export_to_dict()
        hub_dict = hub.export_to_dict()
        detector_dict = detector.export_to_dict()
        
        # Verify seal is present
        assert memory_dict['metadata']['sello'] == "∴𓂀Ω∞³Φ"
        assert hub_dict['metadata']['sello'] == "∴𓂀Ω∞³Φ"
        assert detector_dict['metadata']['sello'] == "∴𓂀Ω∞³Φ"
        
        # Verify f0 is correct
        assert memory_dict['parameters']['f0_hz'] == F0_QCAL
        assert hub_dict['parameters']['f0_hz'] == F0_QCAL
        assert detector_dict['parameters']['f0_hz'] == F0_QCAL


# ============================================================================
# TEST RUNNER
# ============================================================================

def run_tests():
    """Run all tests manually."""
    print("="*70)
    print("  QCAL Biosensor Omega - Test Suite")
    print("  ∴𓂀Ω∞³Φ")
    print("="*70)
    print()
    
    test_classes = [
        TestRNAVolatileMemory,
        TestBiosensorHub,
        TestDisharmonyDetector,
        TestIntegration
    ]
    
    total_tests = 0
    passed_tests = 0
    failed_tests = 0
    
    for test_class in test_classes:
        print(f"Running {test_class.__name__}...")
        test_instance = test_class()
        
        # Get all test methods
        test_methods = [
            method for method in dir(test_instance)
            if method.startswith('test_')
        ]
        
        for test_method_name in test_methods:
            total_tests += 1
            test_method = getattr(test_instance, test_method_name)
            
            try:
                test_method()
                print(f"  ✓ {test_method_name}")
                passed_tests += 1
            except AssertionError as e:
                print(f"  ✗ {test_method_name}: {str(e)}")
                failed_tests += 1
            except Exception as e:
                print(f"  ✗ {test_method_name}: ERROR - {str(e)}")
                failed_tests += 1
        
        print()
    
    print("="*70)
    print(f"  Tests: {total_tests} total, {passed_tests} passed, {failed_tests} failed")
    if failed_tests == 0:
        print("  ✓ ALL TESTS PASSED")
    else:
        print(f"  ✗ {failed_tests} TESTS FAILED")
    print("="*70)
    
    return failed_tests == 0


if __name__ == '__main__':
    success = run_tests()
    sys.exit(0 if success else 1)
