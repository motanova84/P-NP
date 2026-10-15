#!/usr/bin/env python3
"""
Run All Verifications - Complete Teorema ℂₛ Verification Suite

Executes all three layers of verification and generates the final certificate:
1. C_k_verification.py - Cryptographic layer
2. A_t_verification.py - Temporal/Cosmological layer
3. A_u_verification.py - Unitary architecture layer
4. teorema_Cs_certificado.py - Final certificate

Usage:
    python echo_qcal/run_all_verifications.py
    
Or as a module:
    python -m echo_qcal.run_all_verifications
"""

import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from echo_qcal import (
    verify_cryptographic_layer,
    verify_temporal_alignment,
    verify_unitary_architecture,
    generate_certificate
)


def run_all_verifications():
    """
    Execute all verification layers in sequence and generate final certificate.
    """
    
    print("╔══════════════════════════════════════════════════════════════════╗")
    print("║     SISTEMA DE VERIFICACIÓN COMPLETO - TEOREMA ℂₛ                ║")
    print("║     Coherence Sovereignty Theorem - Triple Verification          ║")
    print("╚══════════════════════════════════════════════════════════════════╝")
    print()
    print("Ejecutando las tres capas de verificación...")
    print()
    print("═" * 70)
    print()
    
    # Layer 1: Cryptographic
    print("CAPA 1: Verificación Criptográfica (Cₖ)")
    print("─" * 70)
    result_ck = verify_cryptographic_layer()
    print()
    print("═" * 70)
    print()
    
    # Layer 2: Temporal
    print("CAPA 2: Verificación Temporal/Cosmológica (Aₜ)")
    print("─" * 70)
    result_at = verify_temporal_alignment()
    print()
    print("═" * 70)
    print()
    
    # Layer 3: Unitary Architecture
    print("CAPA 3: Verificación Arquitectura Unitaria (Aᵤ)")
    print("─" * 70)
    result_au = verify_unitary_architecture()
    print()
    print("═" * 70)
    print()
    
    # Generate final certificate
    print("GENERACIÓN DE CERTIFICADO FINAL")
    print("─" * 70)
    certificate = generate_certificate()
    print()
    
    # Summary
    all_verified = all([
        result_ck['status'] == 'VERIFIED',
        result_at['status'] == 'VERIFIED',
        result_au['status'] == 'VERIFIED'
    ])
    
    if all_verified:
        print()
        print("🎉" * 35)
        print()
        print("         ✨ VERIFICACIÓN COMPLETA EXITOSA ✨")
        print()
        print("    El Teorema de Coherencia Soberana (ℂₛ) ha sido")
        print("         formalmente demostrado en sus tres capas")
        print()
        print("🎉" * 35)
        print()
    else:
        print()
        print("⚠️  ADVERTENCIA: Algunas verificaciones fallaron")
        print("    Revise los resultados anteriores para detalles")
        print()
    
    return {
        'C_k': result_ck,
        'A_t': result_at,
        'A_u': result_au,
        'all_verified': all_verified,
        'certificate': certificate
    }


if __name__ == "__main__":
    results = run_all_verifications()
    sys.exit(0 if results['all_verified'] else 1)
