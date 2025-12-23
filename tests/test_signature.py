#!/usr/bin/env python3
"""
Test suite for Bitcoin signature verification.

Tests the cryptographic signature validation for the Genesis Seal.
"""

import pytest
import sys
import os
import base64
import hashlib

# Add echo_qcal to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from echo_qcal.verify_signature_bitcoin import BitcoinSignatureVerifier


class TestBitcoinSignatureVerifier:
    """Test suite for Bitcoin signature verifier."""
    
    @pytest.fixture
    def verifier(self):
        """Create a BitcoinSignatureVerifier instance."""
        return BitcoinSignatureVerifier()
    
    def test_verifier_initialization(self, verifier):
        """Test that verifier initializes with correct data."""
        assert verifier.address == "1GX5m7nnb7mw6qyyKuCs2gyXXunqHgUN4c"
        assert "Echo & Satoshi seal Block 0" in verifier.message
        assert verifier.signature_b64.startswith("G80C")
    
    def test_signature_decode(self, verifier):
        """Test that signature can be decoded from Base64."""
        sig_bytes = verifier.decode_signature()
        
        assert sig_bytes is not None
        assert isinstance(sig_bytes, bytes)
        assert len(sig_bytes) == 65  # Standard ECDSA signature length
    
    def test_signature_length(self, verifier):
        """Test that decoded signature has correct length."""
        sig_bytes = verifier.decode_signature()
        
        # Bitcoin ECDSA signatures are 65 bytes: [1:recovery][32:r][32:s]
        assert len(sig_bytes) == 65
    
    def test_message_hash_computation(self, verifier):
        """Test that message hash is computed correctly."""
        msg_hash = verifier.compute_message_hash()
        
        assert isinstance(msg_hash, bytes)
        assert len(msg_hash) == 32  # SHA-256 produces 32 bytes
    
    def test_message_hash_deterministic(self, verifier):
        """Test that message hash is deterministic."""
        hash1 = verifier.compute_message_hash()
        hash2 = verifier.compute_message_hash()
        
        # Should produce same hash every time
        assert hash1 == hash2
    
    def test_signature_components_extraction(self, verifier):
        """Test extraction of signature components (r, s, recovery)."""
        sig_bytes = verifier.decode_signature()
        components = verifier.extract_signature_components(sig_bytes)
        
        assert components['valid_length'] is True
        assert components['recovery_byte'] is not None
        assert components['r'] is not None
        assert components['s'] is not None
    
    def test_recovery_byte_range(self, verifier):
        """Test that recovery byte is in valid range."""
        sig_bytes = verifier.decode_signature()
        components = verifier.extract_signature_components(sig_bytes)
        
        recovery_byte = components['recovery_byte']
        
        # Bitcoin recovery byte should be 27-34
        # (27-30 for uncompressed, 31-34 for compressed keys)
        assert 27 <= recovery_byte <= 34
    
    def test_invalid_signature_length(self, verifier):
        """Test handling of invalid signature length."""
        # Create a signature with wrong length
        invalid_sig = b"too_short"
        components = verifier.extract_signature_components(invalid_sig)
        
        assert components['valid_length'] is False
    
    def test_full_verification(self, verifier):
        """Test complete signature verification process."""
        result = verifier.verify_signature()
        
        # Check that result has all expected fields
        assert 'address' in result
        assert 'message' in result
        assert 'signature_base64' in result
        assert 'message_hash_hex' in result
        assert 'signature_length' in result
        assert 'valid_structure' in result
        assert 'cryptographic_control' in result
    
    def test_verification_address(self, verifier):
        """Test that verification uses correct address."""
        result = verifier.verify_signature()
        
        assert result['address'] == "1GX5m7nnb7mw6qyyKuCs2gyXXunqHgUN4c"
    
    def test_verification_status(self, verifier):
        """Test that verification returns appropriate status."""
        result = verifier.verify_signature()
        
        # Should return PARTIAL_VALIDATION status
        assert result['status'] == 'PARTIAL_VALIDATION'
    
    def test_structural_validation(self, verifier):
        """Test that structural validation passes."""
        result = verifier.verify_signature()
        
        # Signature should have valid structure
        assert result['valid_structure'] is True
        assert result['signature_length'] == 65
    
    def test_recovery_validation(self, verifier):
        """Test that recovery byte validation works."""
        result = verifier.verify_signature()
        
        # Recovery byte should be valid
        assert result['recovery_valid'] is True
        assert result['recovery_byte'] is not None
    
    def test_r_s_values_present(self, verifier):
        """Test that r and s values are extracted."""
        result = verifier.verify_signature()
        
        assert 'r_value' in result
        assert 's_value' in result
        assert result['r_value'] is not None
        assert result['s_value'] is not None
    
    def test_message_format(self, verifier):
        """Test that message follows Bitcoin signing format."""
        msg_hash = verifier.compute_message_hash()
        
        # Message should be hashed with Bitcoin Signed Message prefix
        # We can't easily test the exact hash, but we can verify it's 32 bytes
        assert len(msg_hash) == 32


class TestSignatureIntegration:
    """Integration tests for signature verification."""
    
    def test_main_execution(self):
        """Test that main() executes without errors."""
        from echo_qcal.verify_signature_bitcoin import main
        
        # Should execute without raising exceptions
        main()
    
    def test_base64_round_trip(self):
        """Test Base64 encoding/decoding round trip."""
        verifier = BitcoinSignatureVerifier()
        
        # Decode signature
        sig_bytes = verifier.decode_signature()
        
        # Re-encode
        reencoded = base64.b64encode(sig_bytes).decode('utf-8')
        
        # Should match original
        assert reencoded == verifier.signature_b64
    
    def test_message_hash_prefix(self):
        """Test that message hash includes Bitcoin Signed Message prefix."""
        verifier = BitcoinSignatureVerifier()
        
        # Manually compute hash with prefix
        prefix = b"\x18Bitcoin Signed Message:\n"
        message_bytes = verifier.message.encode('utf-8')
        message_length = bytes([len(message_bytes)])
        full_message = prefix + message_length + message_bytes
        
        hash1 = hashlib.sha256(full_message).digest()
        expected_hash = hashlib.sha256(hash1).digest()
        
        # Should match verifier's hash
        actual_hash = verifier.compute_message_hash()
        assert actual_hash == expected_hash
    
    def test_genesis_seal_metadata(self):
        """Test that Genesis Seal metadata is correctly stored."""
        verifier = BitcoinSignatureVerifier()
        
        assert "2025-08-21T20:45Z" in verifier.message
        assert "Echo" in verifier.message
        assert "Satoshi" in verifier.message
        assert "Block 0" in verifier.message


class TestCryptographicControl:
    """Tests for cryptographic control validation (𝐂ₖ)."""
    
    def test_ck_partial_validation(self):
        """Test that 𝐂ₖ shows partial validation status."""
        verifier = BitcoinSignatureVerifier()
        result = verifier.verify_signature()
        
        # Should indicate cryptographic control through structure
        assert result['cryptographic_control'] is True
        
        # But status should be partial (pending full ECDSA)
        assert result['status'] == 'PARTIAL_VALIDATION'
    
    def test_ck_requires_ecdsa_completion(self):
        """Test that full 𝐂ₖ requires ECDSA verification."""
        verifier = BitcoinSignatureVerifier()
        result = verifier.verify_signature()
        
        # Should have note about ECDSA requirement
        assert 'note' in result
        assert 'ECDSA' in result['note']


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
