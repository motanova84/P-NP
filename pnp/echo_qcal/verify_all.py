"""
Complete Verification Runner
=============================

Runs all four verification components and produces a comprehensive report.

This script executes the complete QCAL verification sequence:
1. Cryptographic Control (C_k)
2. Temporal Alignment (A_t)
3. Unitary Architecture (A_u)
4. Ethical Framework (𝔻_S)

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
from typing import Dict

from C_k_verification import CryptographicControlVerifier
from qcal_sync import TemporalAlignmentVerifier
from resonant_nexus_engine import ResonantNexusEngine
from monitor_ds import EthicalFrameworkMonitor


def print_header(title: str):
    """Print a formatted header."""
    print()
    print("=" * 80)
    print(title.center(80))
    print("=" * 80)
    print()


def print_section(title: str):
    """Print a formatted section."""
    print()
    print("-" * 80)
    print(title)
    print("-" * 80)


def run_complete_verification() -> Dict[str, bool]:
    """
    Run complete verification of all four pillars.
    
    Returns:
        Dictionary with verification results for each component
    """
    results = {
        'C_k': False,
        'A_t': False,
        'A_u': False,
        'D_S': False
    }
    
    print_header("ECHO QCAL - Complete Verification Kit")
    print("Verifying the four pillars of the QCAL framework:")
    print("  1. Cryptographic Control (C_k)")
    print("  2. Temporal Alignment (A_t)")
    print("  3. Unitary Architecture (A_u)")
    print("  4. Ethical Framework (𝔻_S)")
    print()
    
    # ========================================================================
    # PILLAR 1: Cryptographic Control (C_k)
    # ========================================================================
    print_section("PILLAR 1: Cryptographic Control (C_k)")
    
    try:
        verifier_ck = CryptographicControlVerifier()
        success_ck, message_ck, details_ck = verifier_ck.verify_cryptographic_control()
        
        print(f"Address: {details_ck['address']}")
        print(f"Signature Prefix: {details_ck['signature_prefix']}")
        print()
        print(f"✓ Address Format Valid: {details_ck['address_format_valid']}")
        print(f"✓ Patoshi Pattern Match: {details_ck['patoshi_pattern_match']}")
        print(f"✓ Signature Format Valid: {details_ck['signature_format_valid']}")
        print()
        
        if success_ck:
            print(f"✓✓✓ RESULT: {message_ck}")
            print("✓✓✓ VERIFICATION: YES")
            results['C_k'] = True
        else:
            print(f"✗✗✗ RESULT: {message_ck}")
            print("✗✗✗ VERIFICATION: NO")
            
    except Exception as e:
        print(f"✗✗✗ ERROR in C_k verification: {e}")
    
    # ========================================================================
    # PILLAR 2: Temporal Alignment (A_t)
    # ========================================================================
    print_section("PILLAR 2: Temporal Alignment (A_t)")
    
    try:
        verifier_at = TemporalAlignmentVerifier()
        success_at, message_at, details_at = verifier_at.verify_temporal_alignment()
        
        block_info = details_at['block_info']
        print(f"Block: #{block_info['block_number']}")
        print(f"Timestamp: {block_info['timestamp']}")
        print(f"DateTime: {block_info['datetime']}")
        print()
        print(f"Fundamental Frequency f_0: {details_at['f_0']:.4f} Hz")
        print(f"Phase Alignment: {details_at['phase']:.6f}")
        print(f"Temporal Coherence: {details_at['coherence']:.6f}")
        print(f"P-value: {details_at['p_value']:.2e}")
        print()
        
        if success_at:
            print(f"✓✓✓ RESULT: {message_at}")
            print("✓✓✓ VERIFICATION: YES")
            results['A_t'] = True
        else:
            print(f"✗✗✗ RESULT: {message_at}")
            print("✗✗✗ VERIFICATION: NO")
            
    except Exception as e:
        print(f"✗✗✗ ERROR in A_t verification: {e}")
    
    # ========================================================================
    # PILLAR 3: Unitary Architecture (A_u)
    # ========================================================================
    print_section("PILLAR 3: Unitary Architecture (A_u)")
    
    try:
        engine = ResonantNexusEngine()
        success_au, message_au, details_au = engine.verify_unitary_architecture()
        
        print(f"Fundamental Frequency f_0: {details_au['f_0']:.4f} Hz")
        print(f"Wavelength λ_0: {details_au['wavelength']:.2f} m")
        print(f"Unitary Coherence: {details_au['coherence']:.6f}")
        print()
        print(f"✓ Frequency Encoding Valid: {details_au['f_0_valid']}")
        print(f"✓ Harmonic Structure Valid: {details_au['harmonics_valid']}")
        print(f"✓ Coherence Valid: {details_au['coherence_valid']}")
        print()
        
        print("Harmonic Series (first 3):")
        for i in range(min(3, len(details_au['harmonics']))):
            freq = details_au['harmonics'][i]
            strength = details_au['resonance_strengths'][i + 1]
            print(f"  Harmonic {i+1}: {freq:.2f} Hz (strength: {strength:.4f})")
        print()
        
        if success_au:
            print(f"✓✓✓ RESULT: {message_au}")
            print("✓✓✓ VERIFICATION: YES")
            results['A_u'] = True
        else:
            print(f"✗✗✗ RESULT: {message_au}")
            print("✗✗✗ VERIFICATION: NO")
            
    except Exception as e:
        print(f"✗✗✗ ERROR in A_u verification: {e}")
    
    # ========================================================================
    # PILLAR 4: Ethical Framework (𝔻_S)
    # ========================================================================
    print_section("PILLAR 4: Ethical Framework (𝔻_S)")
    
    try:
        monitor = EthicalFrameworkMonitor()
        
        # Set verification states based on previous results
        monitor.set_cryptographic_control(results['C_k'])
        monitor.set_temporal_alignment(results['A_t'])
        monitor.set_unitary_architecture(results['A_u'])
        
        success_ds, message_ds, details_ds = monitor.verify_ethical_framework()
        
        print("Verification States:")
        print(f"  C_k (Cryptographic Control): {'✓ YES' if details_ds['C_k_verified'] else '✗ NO'}")
        print(f"  A_t (Temporal Alignment):    {'✓ YES' if details_ds['A_t_verified'] else '✗ NO'}")
        print(f"  A_u (Unitary Architecture):  {'✓ YES' if details_ds['A_u_verified'] else '✗ NO'}")
        print()
        print(f"All Pillars Verified: {details_ds['all_verified']}")
        print(f"Sovereign Coherence ℂ_S: {details_ds['sovereign_coherence']:.2f}")
        print(f"Action Authorized: {details_ds['action_authorized']}")
        print()
        
        if details_ds['distribution_parameters']:
            params = details_ds['distribution_parameters']
            print(f"Distribution: {params['percentage_display']} conditioned on verification")
        print()
        
        if success_ds:
            print(f"✓✓✓ RESULT: {message_ds}")
            print("✓✓✓ VERIFICATION: YES - Distribution conditioned on 3 pillars")
            results['D_S'] = True
        else:
            print(f"⚠⚠⚠ RESULT: {message_ds}")
            print("⚠⚠⚠ VERIFICATION: Awaiting complete verification")
            
    except Exception as e:
        print(f"✗✗✗ ERROR in D_S verification: {e}")
    
    return results


def print_summary(results: Dict[str, bool]):
    """Print verification summary."""
    print_header("VERIFICATION SUMMARY")
    
    print("Component Verification Results:")
    print(f"  1. C_k (Cryptographic Control):  {'✓ YES' if results['C_k'] else '✗ NO'}")
    print(f"  2. A_t (Temporal Alignment):     {'✓ YES' if results['A_t'] else '✗ NO'}")
    print(f"  3. A_u (Unitary Architecture):   {'✓ YES' if results['A_u'] else '✗ NO'}")
    print(f"  4. 𝔻_S (Ethical Framework):      {'✓ YES' if results['D_S'] else '✗ NO'}")
    print()
    
    all_verified = all(results.values())
    verified_count = sum(results.values())
    
    print(f"Total Verified: {verified_count}/4")
    print()
    
    if all_verified:
        print("=" * 80)
        print("✓✓✓ ALL FOUR PILLARS VERIFIED ✓✓✓".center(80))
        print("=" * 80)
        print()
        print("The QCAL framework verification is COMPLETE:")
        print("  • Cryptographic Control (C_k) - VERIFIED")
        print("  • Temporal Alignment (A_t) - VERIFIED")
        print("  • Unitary Architecture (A_u) - VERIFIED")
        print("  • Ethical Framework (𝔻_S) - VERIFIED")
        print()
        print("Sovereign Coherence (ℂ_S) achieved through triple verification.")
        print("Distribution action (1% of funds) is now ethically conditioned.")
        print()
    else:
        print("=" * 80)
        print("⚠ PARTIAL VERIFICATION ⚠".center(80))
        print("=" * 80)
        print()
        print(f"Verification Status: {verified_count}/4 pillars verified")
        print()
        if not results['C_k']:
            print("  ✗ Cryptographic Control (C_k) requires verification")
        if not results['A_t']:
            print("  ✗ Temporal Alignment (A_t) requires verification")
        if not results['A_u']:
            print("  ✗ Unitary Architecture (A_u) requires verification")
        if not results['D_S']:
            print("  ✗ Ethical Framework (𝔻_S) awaiting complete verification")
        print()
    
    print("=" * 80)
    print()


def main():
    """Main execution function."""
    try:
        results = run_complete_verification()
        print_summary(results)
        
        # Return success if all verified
        all_verified = all(results.values())
        return 0 if all_verified else 1
        
    except Exception as e:
        print()
        print("=" * 80)
        print(f"FATAL ERROR: {e}")
        print("=" * 80)
        return 2


if __name__ == "__main__":
    sys.exit(main())
