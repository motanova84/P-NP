"""
Bitcoin Signature Verification

This module verifies the ECDSA signature from the Genesis Block (Block 0)
that cryptographically seals the Echo-QCAL convergence.

Note: Full verification requires the recovery byte (V parameter) which is
implementation-dependent. This module provides the framework for verification.
"""

import argparse
from typing import Tuple, Optional
import sys

from .qcal_constants import GENESIS_ADDRESS, GENESIS_MESSAGE, GENESIS_SIGNATURE


def verify_echo_signature(
    signature: Optional[str] = None,
    message: Optional[str] = None,
    address: Optional[str] = None,
    check_format: bool = True
) -> Tuple[bool, str]:
    """
    Verify the Echo-Satoshi signature on Block 0.
    
    Args:
        signature: Base64-encoded signature (default: GENESIS_SIGNATURE)
        message: Message that was signed (default: GENESIS_MESSAGE)
        address: Bitcoin address that signed (default: GENESIS_ADDRESS)
        check_format: If True, only verify format; full verification requires bitcoinlib
        
    Returns:
        Tuple of (is_valid, explanation)
    """
    # Use defaults if not provided
    signature = signature or GENESIS_SIGNATURE
    message = message or GENESIS_MESSAGE
    address = address or GENESIS_ADDRESS
    
    # Basic format validation
    if check_format:
        # Check signature is base64
        try:
            import base64
            decoded = base64.b64decode(signature)
            
            # Bitcoin signatures are 65 bytes (with recovery byte)
            if len(decoded) == 65:
                format_valid = True
                format_msg = f"✅ Signature format valid: {len(decoded)} bytes"
            else:
                format_valid = False
                format_msg = f"⚠️  Signature length unexpected: {len(decoded)} bytes (expected 65)"
        except Exception as e:
            format_valid = False
            format_msg = f"❌ Invalid base64 encoding: {e}"
        
        # Check address format
        if address.startswith('1') and len(address) >= 26 and len(address) <= 35:
            address_valid = True
            address_msg = "✅ Address format valid (P2PKH)"
        else:
            address_valid = False
            address_msg = f"❌ Invalid address format: {address}"
        
        if format_valid and address_valid:
            return True, f"Format validation passed. {format_msg}\n{address_msg}\n⚠️  Full cryptographic verification requires recovery byte V."
        else:
            return False, f"{format_msg}\n{address_msg}"
    
    # Attempt full verification (requires bitcoinlib or similar)
    try:
        # Try with bitcoinlib if available
        try:
            from bitcoinlib.keys import Key
            
            result = Key.verify_message(address, signature, message)
            
            if result:
                return True, "✅ Signature cryptographically verified!"
            else:
                return False, "❌ Signature verification failed"
                
        except ImportError:
            # bitcoinlib not available
            return False, "⚠️  bitcoinlib not installed. Install with: pip install bitcoinlib\n   Format validation passed, but full verification unavailable."
        
    except Exception as e:
        return False, f"❌ Verification error: {e}\n   This may indicate the recovery byte (V) is needed."


def analyze_signature_components(signature: Optional[str] = None) -> dict:
    """
    Analyze the components of the signature.
    
    Args:
        signature: Base64-encoded signature (default: GENESIS_SIGNATURE)
        
    Returns:
        Dictionary with signature component analysis
    """
    import base64
    
    signature = signature or GENESIS_SIGNATURE
    
    try:
        decoded = base64.b64decode(signature)
        sig_bytes = list(decoded)
        
        if len(sig_bytes) == 65:
            # Standard format: [V][R (32 bytes)][S (32 bytes)]
            v = sig_bytes[0]
            r = bytes(sig_bytes[1:33])
            s = bytes(sig_bytes[33:65])
            
            return {
                'valid_format': True,
                'length': len(sig_bytes),
                'v': v,
                'r_hex': r.hex(),
                's_hex': s.hex(),
                'recovery_byte': v,
            }
        else:
            return {
                'valid_format': False,
                'length': len(sig_bytes),
                'note': f'Expected 65 bytes, got {len(sig_bytes)}'
            }
    except Exception as e:
        return {
            'valid_format': False,
            'error': str(e)
        }


def verify_cryptographic_layer() -> Tuple[bool, str]:
    """
    Verify the cryptographic layer of sovereign coherence (𝐂ₖ).
    
    Returns:
        Tuple of (is_verified, explanation)
    """
    # Check signature format
    is_valid, msg = verify_echo_signature(check_format=True)
    
    if is_valid:
        components = analyze_signature_components()
        
        explanation = (
            "CRYPTOGRAPHIC LAYER VERIFICATION (𝐂ₖ)\n"
            + "=" * 70 + "\n"
            + f"Address:  {GENESIS_ADDRESS}\n"
            + f"Message:  {GENESIS_MESSAGE}\n"
            + f"Signature: {GENESIS_SIGNATURE[:40]}...\n\n"
            + "Signature Analysis:\n"
            + f"  Format Valid: ✅\n"
            + f"  Length: {components.get('length', 0)} bytes\n"
            + f"  Recovery Byte (V): {components.get('v', 'N/A')}\n\n"
            + msg + "\n\n"
            + "STATUS: Cryptographic layer (𝐂ₖ) validated at format level.\n"
            + "        Full ECDSA verification pending recovery byte confirmation."
        )
        
        return True, explanation
    else:
        return False, f"Cryptographic layer verification failed:\n{msg}"


def main():
    """Command-line interface for signature verification."""
    parser = argparse.ArgumentParser(
        description='Verify Echo-Satoshi Genesis Block signature'
    )
    parser.add_argument(
        '--check-all',
        action='store_true',
        help='Run all verification checks'
    )
    parser.add_argument(
        '--analyze',
        action='store_true',
        help='Analyze signature components'
    )
    parser.add_argument(
        '--signature', '-s',
        type=str,
        help='Custom signature to verify'
    )
    parser.add_argument(
        '--message', '-m',
        type=str,
        help='Custom message to verify'
    )
    parser.add_argument(
        '--address', '-a',
        type=str,
        help='Custom address to verify against'
    )
    
    args = parser.parse_args()
    
    print("=" * 70)
    print("Echo-Satoshi Signature Verification")
    print("=" * 70)
    print()
    
    # Run verification
    if args.check_all or (not args.analyze):
        is_verified, explanation = verify_cryptographic_layer()
        print(explanation)
        print()
    
    # Analyze components
    if args.analyze:
        print("-" * 70)
        print("SIGNATURE COMPONENT ANALYSIS")
        print("-" * 70)
        
        components = analyze_signature_components(args.signature)
        
        if components.get('valid_format'):
            print(f"✅ Valid format: {components['length']} bytes")
            print(f"   Recovery Byte (V): {components['recovery_byte']}")
            print(f"   R component: {components['r_hex'][:40]}...")
            print(f"   S component: {components['s_hex'][:40]}...")
        else:
            print(f"❌ Invalid format: {components.get('note', components.get('error'))}")
        print()
    
    # Try custom verification if parameters provided
    if args.signature or args.message or args.address:
        print("-" * 70)
        print("CUSTOM SIGNATURE VERIFICATION")
        print("-" * 70)
        
        is_valid, msg = verify_echo_signature(
            signature=args.signature,
            message=args.message,
            address=args.address,
            check_format=True
        )
        
        print(msg)
        print()
        
        if is_valid:
            print("✅ Custom verification passed")
        else:
            print("❌ Custom verification failed")
        print()


if __name__ == '__main__':
    main()
