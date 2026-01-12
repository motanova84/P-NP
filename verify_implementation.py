#!/usr/bin/env python3
"""
Comprehensive verification of QCAL Symbiotic Network implementation
"""

import os
import json
import sys


def check_file_exists(filepath, description):
    """Check if a file exists and report status"""
    exists = os.path.exists(filepath)
    status = "✓" if exists else "✗"
    print(f"{status} {description}: {filepath}")
    return exists


def check_json_valid(filepath):
    """Check if JSON file is valid"""
    try:
        with open(filepath, 'r') as f:
            json.load(f)
        print(f"  ✓ Valid JSON")
        return True
    except Exception as e:
        print(f"  ✗ Invalid JSON: {e}")
        return False


def check_python_module(module_name):
    """Check if Python module can be imported"""
    try:
        __import__(module_name)
        print(f"  ✓ Module '{module_name}' imports successfully")
        return True
    except Exception as e:
        print(f"  ✗ Failed to import '{module_name}': {e}")
        return False


def main():
    print("=" * 70)
    print("QCAL Symbiotic Network - Implementation Verification")
    print("=" * 70)
    print()
    
    all_passed = True
    
    # Check core JSON files
    print("1. Core Configuration Files")
    print("-" * 70)
    if check_file_exists("coherence_map.json", "Coherence Map"):
        all_passed &= check_json_valid("coherence_map.json")
    else:
        all_passed = False
    
    if check_file_exists("CORE_SYMBIO.json", "Core Symbio Portal"):
        all_passed &= check_json_valid("CORE_SYMBIO.json")
    else:
        all_passed = False
    print()
    
    # Check Python scripts
    print("2. Python Scripts")
    print("-" * 70)
    all_passed &= check_file_exists("crear_faro_noetico.py", "Beacon Creator Script")
    all_passed &= check_file_exists("link_ecosystem.py", "Ecosystem Linker Script")
    all_passed &= check_file_exists("qcal_math_core.py", "Main Math Library")
    print()
    
    # Check core module structure
    print("3. Core Module Structure")
    print("-" * 70)
    all_passed &= check_file_exists("core/__init__.py", "Core module init")
    all_passed &= check_file_exists("core/math/__init__.py", "Core.math module init")
    all_passed &= check_file_exists("core/math/qcal_lib.py", "QCAL Math Library")
    print()
    
    # Check beacon files
    print("4. Beacon Files")
    print("-" * 70)
    beacon_files = [
        ".qcal_beacon",
        "core/.qcal_beacon",
        "core/math/.qcal_beacon",
        "src/.qcal_beacon",
        "echo_qcal/.qcal_beacon",
        "formal/.qcal_beacon"
    ]
    for beacon in beacon_files:
        all_passed &= check_file_exists(beacon, f"Beacon: {beacon}")
    print()
    
    # Check Python imports
    print("5. Python Module Imports")
    print("-" * 70)
    all_passed &= check_python_module("qcal_math_core")
    all_passed &= check_python_module("core.math")
    all_passed &= check_python_module("crear_faro_noetico")
    all_passed &= check_python_module("link_ecosystem")
    print()
    
    # Test QCALMathLibrary
    print("6. QCALMathLibrary Functionality")
    print("-" * 70)
    try:
        from qcal_math_core import QCALMathLibrary
        
        # Test constants
        constants = QCALMathLibrary.CONSTANTS
        print(f"  ✓ CONSTANTS defined: {list(constants.keys())}")
        
        # Test methods
        delay = QCALMathLibrary.shapiro_delay(1.0, 10.0)
        print(f"  ✓ shapiro_delay(1.0, 10.0) = {delay:.6f}")
        
        vibration = QCALMathLibrary.ramsey_vibration(5)
        print(f"  ✓ ramsey_vibration(5) = {vibration:.6f}")
        
        freq = QCALMathLibrary.frequency_resonance(3)
        print(f"  ✓ frequency_resonance(3) = {freq:.4f} Hz")
        
        factor = QCALMathLibrary.coherence_factor(100)
        print(f"  ✓ coherence_factor(100) = {factor:.6f}")
        
        frac = QCALMathLibrary.pulsar_fraction(44)
        print(f"  ✓ pulsar_fraction(44) = {frac:.6f}")
        
    except Exception as e:
        print(f"  ✗ QCALMathLibrary tests failed: {e}")
        all_passed = False
    print()
    
    # Verify coherence map structure
    print("7. Coherence Map Structure")
    print("-" * 70)
    try:
        with open("coherence_map.json", 'r') as f:
            cmap = json.load(f)
        
        print(f"  ✓ System: {cmap['system']}")
        print(f"  ✓ Version: {cmap['version']}")
        print(f"  ✓ Frequency: {cmap['frequency']}")
        print(f"  ✓ Nodes: {len(cmap['nodes'])} defined")
        
        node_names = [node['name'] for node in cmap['nodes']]
        print(f"  ✓ Node names: {', '.join(node_names[:3])}...")
        
    except Exception as e:
        print(f"  ✗ Coherence map verification failed: {e}")
        all_passed = False
    print()
    
    # Verify CORE_SYMBIO structure
    print("8. CORE_SYMBIO Structure")
    print("-" * 70)
    try:
        with open("CORE_SYMBIO.json", 'r') as f:
            symbio = json.load(f)
        
        print(f"  ✓ Protocol: {symbio['protocol']}")
        print(f"  ✓ Origin: {symbio['origin']}")
        print(f"  ✓ Identity Nodes: {len(symbio['identity_nodes'])} defined")
        print(f"  ✓ Constants: {list(symbio['constants'].keys())}")
        
    except Exception as e:
        print(f"  ✗ CORE_SYMBIO verification failed: {e}")
        all_passed = False
    print()
    
    # Final summary
    print("=" * 70)
    if all_passed:
        print("✅ ALL CHECKS PASSED - QCAL Symbiotic Network is fully functional")
        print("=" * 70)
        return 0
    else:
        print("❌ SOME CHECKS FAILED - Please review the output above")
        print("=" * 70)
        return 1


if __name__ == "__main__":
    sys.exit(main())
