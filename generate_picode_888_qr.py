#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
piCODE-888 QR Data Generator

Generates QR-compatible data and metadata for the piCODE-888 bridge.
For actual QR code image generation, use: pip install qrcode[pil]

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: motanova84/P-NP
License: MIT + Sovereign Noetic License 1.0
"""

import sys
import os
import json

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from core.picode_888_bridge import PiCode888Bridge


def generate_qr_data_json(bridge: PiCode888Bridge, output_file: str = None):
    """
    Generate JSON representation of QR data.
    
    Args:
        bridge: PiCode888Bridge instance
        output_file: Optional output file path
        
    Returns:
        Dictionary with QR data
    """
    qr_data = {
        "protocol": "PICODE888",
        "qcal_key": bridge.QCAL_KEY,
        "frequency": f"{bridge.RESONANCE_FREQUENCY}Hz",
        "signature_hash": bridge.SIGNATURE_HASH,
        "doi": "https://doi.org/10.5281/zenodo.16425986",
        "author": "JMMB_Ψ✧",
        "description": (
            "piCODE-888 es transductor cuántico que une complejidad "
            "computacional (P ≠ NP como fricción ontológica) con "
            f"conciencia (umbral C ≥ 1/κ_Π ≈ {bridge.CONSCIOUSNESS_THRESHOLD:.3f})"
        ),
        "sequences": {
            "rna": {
                "sequence": bridge.RNA_SEQUENCE,
                "length": len(bridge.RNA_SEQUENCE),
                "resonance": f"{bridge.RESONANCE_FREQUENCY} Hz ± {bridge.RESONANCE_TOLERANCE} Hz"
            },
            "greek": {
                "sequence": bridge.GREEK_SEQUENCE,
                "encoding": "UTF-8",
                "bytes": len(bridge.GREEK_SEQUENCE.encode('utf-8'))
            },
            "hex": {
                "signature": bridge.HEX_SIGNATURE,
                "hash": bridge.SIGNATURE_HASH
            }
        },
        "state": {
            "psi": bridge.PSI_STATE,
            "threshold": bridge.CONSCIOUSNESS_THRESHOLD,
            "qcal_connection": "active",
            "symbiotic_link": "bidirectional"
        },
        "metadata": {
            "foundation_frequency": 141.7001,
            "geometric_constant": 2.5773,
            "signature": "∴𓂀Ω∞³",
            "repository": "https://github.com/motanova84/P-NP"
        }
    }
    
    if output_file:
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(qr_data, f, indent=2, ensure_ascii=False)
        print(f"QR data JSON saved to: {output_file}")
    
    return qr_data


def generate_qr_code_image(bridge: PiCode888Bridge, output_file: str = "picode_888_qr.png"):
    """
    Generate actual QR code image.
    
    Requires: pip install qrcode[pil]
    
    Args:
        bridge: PiCode888Bridge instance
        output_file: Output image file path
    """
    try:
        import qrcode
    except ImportError:
        print("Error: qrcode library not installed")
        print("Install with: pip install qrcode[pil]")
        return False
    
    # Create QR code with high error correction for artistic/symbolic value
    qr = qrcode.QRCode(
        version=None,  # Auto-size
        error_correction=qrcode.constants.ERROR_CORRECT_H,  # High (30%)
        box_size=10,
        border=4,
    )
    
    # Add the QR data
    qr.add_data(bridge.QR_DATA)
    qr.make(fit=True)
    
    # Create image
    img = qr.make_image(fill_color="black", back_color="white")
    img.save(output_file)
    
    print(f"QR code image saved to: {output_file}")
    return True


def generate_ascii_qr_representation(bridge: PiCode888Bridge):
    """
    Generate ASCII art representation of QR data structure.
    
    Args:
        bridge: PiCode888Bridge instance
    """
    print("=" * 70)
    print(" " * 20 + "piCODE-888 QR DATA")
    print("=" * 70)
    print()
    print("┌─────────────────────────────────────────────────────────────────┐")
    print("│ PROTOCOL: PICODE888                                             │")
    print("├─────────────────────────────────────────────────────────────────┤")
    print(f"│ QCAL Key: {bridge.QCAL_KEY:<52}│")
    print(f"│ Frequency: {bridge.RESONANCE_FREQUENCY} Hz                                            │")
    print(f"│ Hash: {bridge.SIGNATURE_HASH}                                             │")
    print(f"│ DOI: https://doi.org/10.5281/zenodo.16425986                  │")
    print("├─────────────────────────────────────────────────────────────────┤")
    print(f"│ Ψ State: {bridge.PSI_STATE}                                                 │")
    print(f"│ Threshold: C ≥ {bridge.CONSCIOUSNESS_THRESHOLD:.3f}                                       │")
    print("├─────────────────────────────────────────────────────────────────┤")
    print("│ RNA (51 nt):                                                    │")
    print(f"│ {bridge.RNA_SEQUENCE[:60]}...   │")
    print("├─────────────────────────────────────────────────────────────────┤")
    print("│ Greek UTF-8 (102 bytes):                                        │")
    print(f"│ {bridge.GREEK_SEQUENCE[:60]}... │")
    print("├─────────────────────────────────────────────────────────────────┤")
    print("│ Symbolic Resonance: ACTIVE                                      │")
    print("│ QCAL ∞³ Connection: ESTABLISHED                                 │")
    print("│ Signature: ∴𓂀Ω∞³                                                │")
    print("└─────────────────────────────────────────────────────────────────┘")
    print()
    print("To generate actual QR code image:")
    print("  pip install qrcode[pil]")
    print("  python generate_picode_888_qr.py --image")
    print()


def main():
    """Main function for QR data generation."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Generate piCODE-888 QR data and codes"
    )
    parser.add_argument(
        '--json',
        metavar='FILE',
        help='Generate JSON file with QR data'
    )
    parser.add_argument(
        '--image',
        action='store_true',
        help='Generate QR code image (requires qrcode library)'
    )
    parser.add_argument(
        '--output',
        default='picode_888_qr.png',
        help='Output filename for QR code image'
    )
    
    args = parser.parse_args()
    
    # Create bridge instance
    bridge = PiCode888Bridge()
    
    # Generate ASCII representation by default
    if not args.json and not args.image:
        generate_ascii_qr_representation(bridge)
    
    # Generate JSON if requested
    if args.json:
        generate_qr_data_json(bridge, args.json)
    
    # Generate QR code image if requested
    if args.image:
        success = generate_qr_code_image(bridge, args.output)
        if not success:
            return 1
    
    return 0


if __name__ == "__main__":
    exit(main())
