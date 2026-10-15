#!/usr/bin/env python3
"""
Test script for Sovereign Coherence Monitor
Runs a quick verification cycle without continuous monitoring
"""

import asyncio
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from sovereign_coherence_monitor import SovereignCoherenceMonitor


async def test_single_verification():
    """Run a single verification cycle for testing"""
    
    print("\n" + "=" * 70)
    print("TEST: SOVEREIGN COHERENCE MONITOR - SINGLE VERIFICATION CYCLE")
    print("=" * 70)
    
    monitor = SovereignCoherenceMonitor()
    
    # Run single verification of all layers
    print("\n🔍 Testing single verification cycle...")
    
    # Verify Capa Criptográfica (Cₖ)
    ck_result = await monitor.verify_cryptographic_layer()
    monitor.system_state['C_k_verified'] = ck_result['verified']
    
    # Verify Capa Cosmológica (Aₜ)
    at_result = await monitor.verify_temporal_layer()
    monitor.system_state['A_t_verified'] = at_result['verified']
    
    # Verify Capa Semántica (Aᵤ)
    au_result = await monitor.verify_semantic_layer()
    monitor.system_state['A_u_verified'] = au_result['verified']
    
    # Determine theorem status
    monitor.system_state['Cs_theorem_proven'] = all([
        monitor.system_state['C_k_verified'],
        monitor.system_state['A_t_verified'],
        monitor.system_state['A_u_verified']
    ])
    
    # Display results
    monitor.display_verification_results(ck_result, at_result, au_result)
    
    # Calculate next coherence peak if theorem is proven
    if monitor.system_state['Cs_theorem_proven']:
        await monitor.calculate_next_coherence_peak()
    
    # Test transmission data generation
    print("\n📡 Testing transmission data generation...")
    transmission_id = "test_transmission_001"
    
    try:
        resonance_data = await monitor.activate_resonance_engine()
        print(f"  ✅ Resonance engine activated")
        print(f"     • f₀: {resonance_data['f0']} Hz")
        print(f"     • Coherence score: {resonance_data['coherence_score']:.6f}")
        
        coherence_signature = await monitor.generate_coherence_signature()
        print(f"  ✅ Coherence signature generated")
        print(f"     • Phase: {coherence_signature['phase']:.6f}")
        
        ledger_entry = await monitor.update_genesis_ledger(
            transmission_id, resonance_data, coherence_signature
        )
        print(f"  ✅ Ledger updated")
        print(f"     • Entry hash: {ledger_entry['entry_hash'][:16]}...")
        
        certificate = await monitor.emit_transmission_certificate(
            transmission_id, ledger_entry
        )
        print(f"  ✅ Certificate emitted")
        if certificate is not None:
            print(f"     • Certificate: {str(certificate)[:80]}...")
        
    except Exception as e:
        print(f"  ❌ Error in transmission test: {e}")
    
    # Verify directory structure
    print("\n📁 Checking directory structure...")
    config_dir = Path("echo_qcal_config")
    log_dir = Path("echo_qcal_logs")
    
    if config_dir.exists():
        print(f"  ✅ {config_dir}/ created")
        files = list(config_dir.glob("*"))
        for f in files[:5]:  # Show first 5 files
            print(f"     • {f.name}")
    
    if log_dir.exists():
        print(f"  ✅ {log_dir}/ created")
        files = list(log_dir.glob("*"))
        for f in files[:5]:  # Show first 5 files
            print(f"     • {f.name}")
    
    # Summary
    print("\n" + "=" * 70)
    print("TEST SUMMARY:")
    print("=" * 70)
    print(f"  • Cₖ (Cryptographic): {'✅ PASS' if ck_result['verified'] else '❌ FAIL'}")
    print(f"  • Aₜ (Cosmological):  {'✅ PASS' if at_result['verified'] else '❌ FAIL'}")
    print(f"  • Aᵤ (Semantic):      {'✅ PASS' if au_result['verified'] else '❌ FAIL'}")
    print(f"  • Theorem ℂₛ:         {'✅ PROVEN' if monitor.system_state['Cs_theorem_proven'] else '❌ NOT PROVEN'}")
    print("=" * 70)
    
    return monitor.system_state['Cs_theorem_proven']


async def main():
    """Main test function"""
    try:
        success = await test_single_verification()
        sys.exit(0 if success else 1)
    except Exception as e:
        print(f"\n❌ Test failed with error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())
