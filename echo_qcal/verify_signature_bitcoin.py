#!/usr/bin/env python3
"""
Bitcoin Signature Verification - Cryptographic Control (𝐂ₖ)

This module verifies the cryptographic signature on the Patoshi address
that establishes the Genesis Seal (Block 0) intent.

The signature demonstrates cryptographic control and conscious intention
for the QCAL ∞³ protocol activation.
"""

import hashlib
import base64
from typing import Dict, Optional


class BitcoinSignatureVerifier:
    """Verifies Bitcoin ECDSA signatures for Genesis Seal validation."""
    
    # Genesis Seal Data
    PATOSHI_ADDRESS = "1GX5m7nnb7mw6qyyKuCs2gyXXunqHgUN4c"
    SEALED_MESSAGE = "Echo & Satoshi seal Block 0: 2025-08-21T20:45Z"
    SIGNATURE_BASE64 = "G80CqNxfcucQRxHHJanbQ5m8S6QNICzlCqU54oXPiQRtDRDFL5lxRvBldhBTNqPes3UfC7ZDuuuESPlEPlagjRI="
    
    def __init__(self):
        """Initialize the signature verifier."""
        self.address = self.PATOSHI_ADDRESS
        self.message = self.SEALED_MESSAGE
        self.signature_b64 = self.SIGNATURE_BASE64
        
    def decode_signature(self) -> Optional[bytes]:
        """
        Decode the Base64 signature.
        
        Returns:
            Decoded signature bytes or None if invalid
        """
        try:
            return base64.b64decode(self.signature_b64)
        except Exception as e:
            print(f"Error decoding signature: {e}")
            return None
    
    def compute_message_hash(self) -> bytes:
        """
        Compute the double SHA-256 hash of the message.
        
        Bitcoin signs the hash of: "Bitcoin Signed Message:\n" + message
        
        Returns:
            32-byte message hash
        """
        # Bitcoin message signing prepends this prefix
        prefix = b"\x18Bitcoin Signed Message:\n"
        message_bytes = self.message.encode('utf-8')
        message_length = bytes([len(message_bytes)])
        
        # Construct the full message
        full_message = prefix + message_length + message_bytes
        
        # Double SHA-256
        hash1 = hashlib.sha256(full_message).digest()
        hash2 = hashlib.sha256(hash1).digest()
        
        return hash2
    
    def extract_signature_components(self, signature_bytes: bytes) -> Dict:
        """
        Extract r, s, and recovery byte from the signature.
        
        Bitcoin ECDSA signature format: [1 byte: recovery] [32 bytes: r] [32 bytes: s]
        
        Args:
            signature_bytes: Raw signature bytes
            
        Returns:
            Dictionary with signature components
        """
        if len(signature_bytes) != 65:
            return {
                'valid_length': False,
                'length': len(signature_bytes),
                'recovery_byte': None,
                'r': None,
                's': None
            }
        
        recovery_byte = signature_bytes[0]
        r = int.from_bytes(signature_bytes[1:33], byteorder='big')
        s = int.from_bytes(signature_bytes[33:65], byteorder='big')
        
        return {
            'valid_length': True,
            'length': len(signature_bytes),
            'recovery_byte': recovery_byte,
            'recovery_byte_hex': hex(recovery_byte),
            'r': r,
            'r_hex': hex(r),
            's': s,
            's_hex': hex(s)
        }
    
    def verify_signature(self) -> Dict:
        """
        Verify the Bitcoin ECDSA signature.
        
        Note: Full ECDSA verification requires elliptic curve operations.
        This function performs structural validation and extracts components.
        
        Returns:
            Dictionary with verification results
        """
        # Decode signature
        sig_bytes = self.decode_signature()
        if sig_bytes is None:
            return {
                'status': 'ERROR',
                'message': 'Failed to decode signature',
                'valid': False
            }
        
        # Compute message hash
        msg_hash = self.compute_message_hash()
        msg_hash_hex = msg_hash.hex()
        
        # Extract signature components
        components = self.extract_signature_components(sig_bytes)
        
        # Structural validation
        valid_structure = components['valid_length']
        
        # Recovery byte should be in range 27-34 (compressed) or 31-34 (compressed with odd/even)
        recovery_valid = False
        if components['recovery_byte'] is not None:
            recovery_valid = 27 <= components['recovery_byte'] <= 34
        
        # Result compilation
        result = {
            'address': self.address,
            'message': self.message,
            'signature_base64': self.signature_b64,
            'message_hash_hex': msg_hash_hex,
            'signature_length': components['length'],
            'valid_structure': valid_structure,
            'recovery_byte': components.get('recovery_byte'),
            'recovery_byte_hex': components.get('recovery_byte_hex'),
            'recovery_valid': recovery_valid,
            'r_value': components.get('r_hex'),
            's_value': components.get('s_hex'),
            'status': 'PARTIAL_VALIDATION',
            'note': 'Full ECDSA verification requires elliptic curve library',
            'cryptographic_control': valid_structure and recovery_valid
        }
        
        return result


def main():
    """Main verification function."""
    print("=" * 70)
    print("🔐 Bitcoin Genesis Seal Signature Verification (𝐂ₖ)")
    print("=" * 70)
    print()
    
    verifier = BitcoinSignatureVerifier()
    
    print("📋 Genesis Seal Metadata")
    print("-" * 70)
    print(f"Address:   {verifier.address}")
    print(f"Message:   {verifier.message}")
    print(f"Signature: {verifier.signature_b64[:50]}...")
    print()
    
    # Perform verification
    print("🔍 Signature Verification Process")
    print("-" * 70)
    
    result = verifier.verify_signature()
    
    print(f"Message Hash:      {result['message_hash_hex']}")
    print(f"Signature Length:  {result['signature_length']} bytes")
    print(f"Valid Structure:   {result['valid_structure']}")
    print()
    
    if result['recovery_byte'] is not None:
        print(f"Recovery Byte:     {result['recovery_byte']} ({result['recovery_byte_hex']})")
        print(f"Recovery Valid:    {result['recovery_valid']}")
        print()
    
    print(f"r-value: {result.get('r_value', 'N/A')[:50]}...")
    print(f"s-value: {result.get('s_value', 'N/A')[:50]}...")
    print()
    
    print("📊 Verification Status")
    print("-" * 70)
    print(f"Status:              {result['status']}")
    print(f"Cryptographic Ctrl:  {result['cryptographic_control']}")
    print()
    
    if result['cryptographic_control']:
        print("━" * 70)
        print("🟠 CRYPTOGRAPHIC CONTROL - PARTIAL VALIDATION")
        print("━" * 70)
        print()
        print("Signature structure is valid. Full ECDSA verification requires")
        print("additional elliptic curve cryptography operations.")
        print()
        print("The signature demonstrates structural integrity and represents")
        print("the Genesis Seal intent for QCAL ∞³ protocol activation.")
        print()
        print("Status: 🟠 PENDING (Full ECDSA verification with recovery byte)")
    else:
        print("⚠️  Signature structure validation failed")
    
    print()
    
    # Additional note on completion
    print("📝 Note on 𝐂ₖ Completion")
    print("-" * 70)
    print("To complete the Cryptographic Control proof (𝐂ₖ), the recovery")
    print("byte 'V' must be validated using full ECDSA signature verification")
    print("with elliptic curve operations (secp256k1).")
    print()
    print("This requires libraries such as: ecdsa, bitcoinlib, or coincurve")
    print()


if __name__ == "__main__":
    main()
