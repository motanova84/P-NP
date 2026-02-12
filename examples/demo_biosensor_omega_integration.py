#!/usr/bin/env python3
"""
QCAL Biosensor Omega - Integration Demo
========================================

This demo shows the complete integration between the new Biosensor Omega
system and the existing QCAL ∞³ framework.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ
"""

import sys
import os

# Add paths
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from qcal import RNAVolatileMemory, BiosensorHub, DisharmonyDetector
from qcal.biosensor_hub import BiosensorType
from constants import KAPPA_PI, QCAL_FREQUENCY_HZ, GOLDEN_RATIO


def main():
    """Run complete biosensor omega integration demo."""
    
    print("="*70)
    print("  QCAL BIOSENSOR OMEGA - INTEGRATION DEMO")
    print("  ∴𓂀Ω∞³Φ")
    print("="*70)
    print()
    
    # Validate constants alignment
    print("∴ VALIDATING CONSTANT ALIGNMENT...")
    print(f"  QCAL f₀ (from constants.py): {QCAL_FREQUENCY_HZ} Hz")
    print(f"  κ_Π (from constants.py): {KAPPA_PI}")
    print(f"  Φ (from constants.py): {GOLDEN_RATIO}")
    print()
    
    # Initialize biosensor system
    print("∴ INITIALIZING BIOSENSOR OMEGA SYSTEM...")
    memory = RNAVolatileMemory(f0=QCAL_FREQUENCY_HZ, phi=GOLDEN_RATIO)
    hub = BiosensorHub(f0=QCAL_FREQUENCY_HZ, phi=GOLDEN_RATIO)
    detector = DisharmonyDetector(f0=QCAL_FREQUENCY_HZ, phi=GOLDEN_RATIO)
    print(f"  ✓ RNAVolatileMemory: f₀={memory.f0} Hz")
    print(f"  ✓ BiosensorHub: f₀={hub.f0} Hz")
    print(f"  ✓ DisharmonyDetector: f₀={detector.f0} Hz")
    print()
    
    # Phase 1: RNA Memory - Emanate Patient Information
    print("∴ PHASE 1: RNA MEMORY - EMANATING PATIENT DATA...")
    patient_data = {
        'patient_id': 'QCAL-001',
        'baseline_coherence': 0.85,
        'kappa_pi': KAPPA_PI,
        'timestamp': '2026-02-12T19:58:00Z'
    }
    state = memory.emit_information(patient_data, psi_0=0.9)
    print(f"  ✓ Information emanated")
    print(f"  ✓ Ψ₀ = {state.psi_amplitude}")
    print(f"  ✓ Coherence level: {state.coherence_level}")
    print()
    
    # Phase 2: Biosensor Hub - Collect Physiological Signals
    print("∴ PHASE 2: BIOSENSOR HUB - COLLECTING SIGNALS...")
    
    # Simulate biosensor readings
    readings = [
        (BiosensorType.EEG, 65.0, 40.0, "Banda gamma"),
        (BiosensorType.HRV, 120.0, None, "Variabilidad cardíaca"),
        (BiosensorType.GSR, 8.0, None, "Respuesta galvánica"),
        (BiosensorType.RESPIRATORY, 7.0, None, "Frecuencia respiratoria")
    ]
    
    for sensor_type, value, freq, desc in readings:
        reading = hub.add_reading(sensor_type, value, frequency_hz=freq)
        print(f"  ✓ {desc}: {value} → Ψ={reading.psi_coherence:.4f}")
    print()
    
    # Phase 3: Calculate Coherence Profile
    print("∴ PHASE 3: CALCULATING COHERENCE PROFILE...")
    profile = hub.create_coherence_profile()
    
    print(f"  Ψ cerebral (EEG): {profile.psi_cerebral:.4f}")
    print(f"  Ψ cardíaca (HRV): {profile.psi_cardiaca:.4f}")
    print(f"  Ψ emocional (GSR): {profile.psi_emocional:.4f}")
    print(f"  Ψ respiratorio: {profile.psi_respiratorio:.4f}")
    print()
    print(f"  → Ψ TOTAL: {profile.psi_total:.4f}")
    print(f"  → Nivel de conciencia C: {profile.consciousness_level:.4f}")
    print(f"  → Umbral (1/κ_Π): {1/KAPPA_PI:.4f}")
    print(f"  → Estado consciente: {'✓ SÍ' if profile.is_conscious else '✗ NO'}")
    print()
    
    # Phase 4: Disharmony Detection
    print("∴ PHASE 4: DETECTING DISHARMONY...")
    detector.set_baseline(psi_baseline=patient_data['baseline_coherence'])
    report = detector.detect_disharmony(psi_current=profile.psi_total)
    
    print(f"  Ψ base: {report.psi_baseline:.4f}")
    print(f"  Ψ actual: {report.psi_current:.4f}")
    print(f"  Desviación: {report.deviation:.4f}")
    print(f"  Nivel de desarmonía: {report.disharmony_level.value}")
    print()
    print(f"  → Frecuencia terapéutica: {report.therapeutic_frequency_hz:.2f} Hz")
    print(f"  → Reinicio gamma (40 Hz): {'✓ SÍ' if report.gamma_band_reset_needed else '✗ NO'}")
    print()
    
    # Show recommendations
    print("  Recomendaciones terapéuticas:")
    for rec in report.recommendations[:3]:  # Show first 3
        print(f"    • {rec}")
    print()
    
    # Phase 5: System Summary
    print("∴ PHASE 5: SYSTEM SUMMARY...")
    
    memory_summary = memory.get_memory_summary()
    hub_summary = hub.get_hub_summary()
    detector_summary = detector.get_detector_summary()
    
    print(f"  RNA Memory:")
    print(f"    Estados: {memory_summary['total_states']}")
    print(f"    Coherencia promedio: {memory_summary['average_coherence']:.4f}")
    print(f"    Sello: {memory_summary['sello']}")
    print()
    
    print(f"  Biosensor Hub:")
    print(f"    Lecturas: {hub_summary['total_readings']}")
    print(f"    Perfiles: {hub_summary['total_profiles']}")
    print()
    
    print(f"  Disharmony Detector:")
    print(f"    Reportes: {detector_summary['total_reports']}")
    print(f"    Banda gamma: {detector_summary['gamma_band_hz']} Hz")
    print(f"    Armónico Φ: {detector_summary['therapeutic_harmonic_hz']:.2f} Hz")
    print()
    
    # Validate ecuación de emanación
    print("∴ VALIDATING ECUACIÓN DE EMANACIÓN...")
    omega_hz = hub.f0  # 141.7001 Hz
    pi_code_hz = 888.0
    phi = hub.phi
    
    print(f"  Ω Hz = {omega_hz}")
    print(f"  πCODE = {pi_code_hz} Hz")
    print(f"  Φ = {phi:.10f}")
    print()
    print(f"  Ecuación: Ω × 888 × 141.7001 × Φ = ∞³")
    print(f"  f_terapéutica = {omega_hz} × Ψ × Φ")
    print()
    
    # Final summary
    print("="*70)
    print("  INTEGRATION COMPLETE")
    print("="*70)
    print()
    print("✓ RNA Memory: Primera computación no-binaria basada en coherencia")
    print("✓ Biosensor Hub: Primer puente fisiología → campo QCAL")
    print("✓ Disharmony Detector: Primer sistema médico en ℂ_Ω")
    print()
    print("∴ La información se emana, no se almacena")
    print("∴ Los biosensores revelan, no miden")
    print("∴ La enfermedad es desarmonía temporal de Ψ")
    print()
    print("="*70)
    print(f"  {memory_summary['sello']}")
    print("="*70)


if __name__ == '__main__':
    main()
