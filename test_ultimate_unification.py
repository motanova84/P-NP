#!/usr/bin/env python3
"""
Test script for ultimate_unification_certified.py
Validates that the implementation works correctly.
"""

import sys
import os
import json
import numpy as np
import tempfile

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ultimate_unification_certified import (
    CertificateGenerator, RNA_piCODE, PNP_Consciousness_Verifier,
    KAPPA_PI, F_0, PHI, PI_OVER_E, LAMBDA_CY, A_EFF_MAX
)


def test_imports():
    """Test that all required modules can be imported."""
    import numpy
    import scipy.signal
    import matplotlib.pyplot
    import json
    import hashlib
    from datetime import datetime, timezone
    
    # Test passed if no import errors


if __name__ == "__main__":
    print("=" * 70)
    print("Testing Ultimate Unification Certificate Implementation".center(70))
    print("=" * 70)
    
    # Test constants
    print("\n🔬 Test 1: Constants Defined")
    assert KAPPA_PI == 2.5773
    assert F_0 == 141.7001
    assert PHI == (1 + np.sqrt(5)) / 2
    print("  ✓ All constants defined correctly")
    
    # Test κ_Π trinity
    print("\n🔬 Test 2: κ_Π Trinity")
    computed = PHI * PI_OVER_E * LAMBDA_CY
    error = abs(computed - KAPPA_PI)
    assert error < 0.01
    print(f"  ✓ κ_Π trinity verified (error: {error:.6f})")
    
    # Test certificate generator
    print("\n🔬 Test 3: Certificate Generator")
    cert_gen = CertificateGenerator()
    cert_gen.add_metadata()
    cert_gen.add_constants()
    cert_gen.compute_hash()
    assert cert_gen.certificate['hash'] is not None
    assert len(cert_gen.certificate['hash']) == 64
    print("  ✓ Certificate generator works")
    print(f"  ✓ SHA-256 hash computed: {cert_gen.certificate['hash'][:16]}...")
    
    # Test RNA model
    print("\n🔬 Test 4: RNA piCODE Model")
    np.random.seed(42)
    rna = RNA_piCODE(length=50)
    assert rna.length == 50
    assert len(rna.sequence) == 50
    assert len(rna.vibrational_modes) == 5
    coherence = rna.tune_to_f0(F_0)
    assert 0 <= coherence <= A_EFF_MAX
    print("  ✓ RNA initialization successful")
    print(f"  ✓ Coherence at f₀: {coherence:.6f}")
    
    # Test quantum evolution
    print("\n🔬 Test 5: Quantum State Evolution")
    initial_norm = np.linalg.norm(rna.pi_electrons)
    rna.evolve_quantum_state(0.1, 0.5)
    final_norm = np.linalg.norm(rna.pi_electrons)
    assert abs(initial_norm - 1.0) < 1e-10
    assert abs(final_norm - 1.0) < 1e-10
    print("  ✓ State normalization preserved")
    print(f"  ✓ Initial norm: {initial_norm:.10f}")
    print(f"  ✓ Final norm: {final_norm:.10f}")
    
    # Test verifier
    print("\n🔬 Test 6: P≠NP Consciousness Verifier")
    verifier = PNP_Consciousness_Verifier()
    result1 = verifier.verify_kappa_pi_trinity()
    assert result1 == True
    print("  ✓ κ_Π verification passed")
    
    result2 = verifier.verify_computational_complexity()
    assert result2 == True
    print("  ✓ Computational complexity verification passed")
    
    # Test RNA simulation
    print("\n🔬 Test 7: RNA Consciousness Simulation")
    np.random.seed(42)
    verifier2 = PNP_Consciousness_Verifier()
    verifier2.simulate_RNA_consciousness(n_molecules=10)
    assert 'time' in verifier2.results
    assert 'consciousness' in verifier2.results
    assert 'coherence' in verifier2.results
    assert 'rna_consciousness' in verifier2.certificate.certificate['simulations']
    print("  ✓ Simulation completed successfully")
    print(f"  ✓ Time points: {len(verifier2.results['time'])}")
    print(f"  ✓ Max coherence: {max(verifier2.results['coherence']):.6f}")
    
    # Test full workflow
    print("\n🔬 Test 8: Full Certification Workflow")
    import tempfile
    np.random.seed(42)
    verifier3 = PNP_Consciousness_Verifier()
    verifier3.verify_kappa_pi_trinity()
    verifier3.verify_f0_from_kappa()
    verifier3.simulate_RNA_consciousness(n_molecules=10)
    verifier3.verify_computational_complexity()
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        cert_file = f.name
    
    verifier3.save_certificate(cert_file)
    assert os.path.exists(cert_file)
    
    with open(cert_file, 'r') as f:
        cert_data = json.load(f)
    
    assert 'hash' in cert_data
    assert 'timestamp' in cert_data
    assert 'metadata' in cert_data
    print("  ✓ Certificate saved successfully")
    
    # Verify certificate
    verified = verifier3.certificate.verify_certificate(cert_file)
    assert verified == True
    print("  ✓ Certificate integrity verified")
    
    # Clean up
    os.unlink(cert_file)
    
    print("\n" + "=" * 70)
    print("✅ ALL TESTS PASSED".center(70))
    print("=" * 70)
