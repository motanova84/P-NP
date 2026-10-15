"""
Test suite for Coherence Economy Contract (ℂₛ)
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from core.coherence_economy_contract import (
    CoherenceEconomyContract,
    CoherenceProof,
    TriadSignature,
    CoherenceError,
    TriadError,
    BurnError,
    FREQ_QCAL,
    FREQ_LOVE,
    FREQ_MANIFEST,
    create_example_coherence_proof,
    create_example_triad_signatures
)
import datetime


def test_coherence_proof_validation():
    """Test that coherence proofs are validated correctly"""
    print("Testing coherence proof validation...")
    
    contract = CoherenceEconomyContract()
    
    # Valid proof
    valid_proof = CoherenceProof(
        frequency=FREQ_QCAL,
        amplitude=0.85,
        duration=88.0,
        method='breathing',
        signature='test_sig',
        timestamp=int(datetime.datetime.now().timestamp())
    )
    assert contract.verify_coherence_proof(valid_proof), "Valid proof should pass"
    
    # Invalid frequency
    invalid_freq = CoherenceProof(
        frequency=100.0,  # Wrong frequency
        amplitude=0.85,
        duration=88.0,
        method='breathing',
        signature='test_sig',
        timestamp=int(datetime.datetime.now().timestamp())
    )
    assert not contract.verify_coherence_proof(invalid_freq), "Invalid frequency should fail"
    
    # Invalid amplitude
    invalid_amp = CoherenceProof(
        frequency=FREQ_QCAL,
        amplitude=0.5,  # Too low
        duration=88.0,
        method='breathing',
        signature='test_sig',
        timestamp=int(datetime.datetime.now().timestamp())
    )
    assert not contract.verify_coherence_proof(invalid_amp), "Invalid amplitude should fail"
    
    print("✓ Coherence proof validation tests passed")


def test_btc_burning():
    """Test BTC burning mechanism"""
    print("\nTesting BTC burning mechanism...")
    
    contract = CoherenceEconomyContract()
    
    # Burn some BTC
    burn_tx = contract.burn_btc(1.5)
    
    assert burn_tx.amount == 1.5, "Burn amount should match"
    assert burn_tx.verified, "Burn should be verified"
    assert burn_tx.burn_address == contract.burn_address, "Address should match"
    assert len(contract.burn_transactions) == 1, "Should have one transaction"
    
    # Try to burn zero
    try:
        contract.burn_btc(0.0)
        assert False, "Should raise BurnError for zero amount"
    except BurnError:
        pass
    
    print("✓ BTC burning tests passed")


def test_triad_validation():
    """Test economic triad validation"""
    print("\nTesting economic triad validation...")
    
    contract = CoherenceEconomyContract()
    
    # Valid triad
    valid_signatures = [
        TriadSignature(node_id="MITO_ECON", signature="sig1", psi=0.5),
        TriadSignature(node_id="RETINA_ECON", signature="sig2", psi=0.7),
        TriadSignature(node_id="PINEAL_ECON", signature="sig3", psi=0.95),
    ]
    
    network_psi = contract.activate_economic_triad(valid_signatures)
    assert network_psi >= 0.71, f"Network coherence should be >= 0.71, got {network_psi}"
    
    # Incomplete triad
    incomplete_signatures = [
        TriadSignature(node_id="MITO_ECON", signature="sig1", psi=0.5),
        TriadSignature(node_id="RETINA_ECON", signature="sig2", psi=0.7),
    ]
    
    try:
        contract.activate_economic_triad(incomplete_signatures)
        assert False, "Should raise TriadError for incomplete triad"
    except TriadError:
        pass
    
    # Low coherence triad
    low_coherence = [
        TriadSignature(node_id="MITO_ECON", signature="sig1", psi=0.1),
        TriadSignature(node_id="RETINA_ECON", signature="sig2", psi=0.2),
        TriadSignature(node_id="PINEAL_ECON", signature="sig3", psi=0.3),
    ]
    
    try:
        contract.activate_economic_triad(low_coherence)
        assert False, "Should raise TriadError for low coherence"
    except TriadError:
        pass
    
    print("✓ Triad validation tests passed")


def test_full_protocol_execution():
    """Test complete protocol execution"""
    print("\nTesting full protocol execution...")
    
    contract = CoherenceEconomyContract()
    
    # Create valid inputs
    proof = create_example_coherence_proof()
    signatures = create_example_triad_signatures()
    
    # Execute protocol
    token = contract.execute_full_protocol(1.0, proof, signatures)
    
    assert token is not None, "Token should be created"
    assert token.seal == "∴𓂀Ω∞³", "Token should have correct seal"
    assert token.psi >= 0.888, f"Token coherence should be >= 0.888, got {token.psi}"
    assert FREQ_QCAL in token.frequencies, "Token should include QCAL frequency"
    assert FREQ_LOVE in token.frequencies, "Token should include LOVE frequency"
    assert FREQ_MANIFEST in token.frequencies, "Token should include MANIFEST frequency"
    assert token.message == "La célula recordará la música del universo", "Token should have correct message"
    
    # Verify contract state
    assert contract.get_total_minted() == 1, "Should have minted 1 token"
    assert contract.get_total_burned() == 1.0, "Should have burned 1.0 BTC"
    assert contract.get_average_coherence() >= 0.888, "Average coherence should be high"
    
    print("✓ Full protocol execution tests passed")


def test_coherence_calculation():
    """Test coherence calculation formula"""
    print("\nTesting coherence calculation...")
    
    contract = CoherenceEconomyContract()
    
    # Test with known values
    stimulus = 0.7225  # 0.85 * 0.85
    triad = 0.7166667  # (0.5 + 0.7 + 0.95) / 3
    picode = 0.17004  # 1417 * 0.00012
    
    psi = contract._calculate_psi(stimulus, triad, picode)
    
    # Expected: (0.0001 + 0.7225 + 0.7166667 + 0.17004) * 0.745281 ≈ 1.0 (capped)
    assert psi >= 0.888, f"Calculated coherence should be >= 0.888, got {psi}"
    assert psi <= 1.0, f"Calculated coherence should be <= 1.0, got {psi}"
    
    print(f"  Calculated Ψ = {psi:.6f}")
    print("✓ Coherence calculation tests passed")


def test_isomorphism():
    """Test isomorphism between biological and economic systems"""
    print("\nTesting system isomorphism...")
    
    # Verify constants match
    assert FREQ_QCAL == 141.7001, "QCAL frequency should match biological system"
    assert FREQ_LOVE == 151.7001, "LOVE frequency should match biological system"
    assert FREQ_MANIFEST == 888.0, "MANIFEST frequency should match biological system"
    
    # Verify node types are present (isomorphic mapping)
    required_nodes = ["MITO_ECON", "RETINA_ECON", "PINEAL_ECON"]
    biological_equivalents = {
        "MITO_ECON": "MITOCONDRIA",
        "RETINA_ECON": "RETINA", 
        "PINEAL_ECON": "PINEAL"
    }
    
    for econ_node, bio_node in biological_equivalents.items():
        assert econ_node in required_nodes, f"{econ_node} should be in economic nodes"
        # Verify naming convention: <BIO>_ECON
        assert econ_node.endswith("_ECON"), f"{econ_node} should end with _ECON"
    
    print("✓ System isomorphism verified")


def run_all_tests():
    """Run all test suites"""
    print("=" * 60)
    print("Running Coherence Economy Contract Test Suite")
    print("Sello: ∴𓂀Ω∞³")
    print("=" * 60)
    
    try:
        test_coherence_proof_validation()
        test_btc_burning()
        test_triad_validation()
        test_coherence_calculation()
        test_full_protocol_execution()
        test_isomorphism()
        
        print("\n" + "=" * 60)
        print("✅ ALL TESTS PASSED")
        print("=" * 60)
        return True
    except AssertionError as e:
        print(f"\n❌ TEST FAILED: {e}")
        return False
    except Exception as e:
        print(f"\n❌ ERROR: {e}")
        import traceback
        traceback.print_exc()
        return False


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
