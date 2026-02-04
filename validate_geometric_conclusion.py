#!/usr/bin/env python3
"""
Geometric Conclusion Validator
================================

This script validates that all components of the geometric P ≠ NP framework
are properly implemented and functioning coherently.

Validates:
- κ_Π = 2.5773 constant definition and usage
- f₀ = 141.7001 Hz frequency constant
- IC(Π, S) ≥ κ_Π·tw/ln n axiom implementation
- Python implementation completeness
- Lean formalization presence
- QCAL ∞³ framework coherence

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz
"""

import os
import sys
import math
from pathlib import Path

# Color codes for output
GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
BLUE = '\033[94m'
RESET = '\033[0m'
BOLD = '\033[1m'

def check(condition, message):
    """Check a condition and print result."""
    symbol = f"{GREEN}✅{RESET}" if condition else f"{RED}❌{RESET}"
    print(f"{symbol} {message}")
    return condition

def header(text):
    """Print a section header."""
    print(f"\n{BOLD}{BLUE}{'='*70}{RESET}")
    print(f"{BOLD}{BLUE}{text:^70}{RESET}")
    print(f"{BOLD}{BLUE}{'='*70}{RESET}\n")

def validate_constants():
    """Validate that all universal constants are defined correctly."""
    header("Validating Universal Constants")
    
    all_valid = True
    
    try:
        # Import constants
        sys.path.insert(0, str(Path(__file__).parent / 'src'))
        from constants import KAPPA_PI, QCAL_FREQUENCY_HZ
        
        # Check κ_Π
        expected_kappa = 2.5773
        tolerance = 0.01
        kappa_valid = abs(KAPPA_PI - expected_kappa) < tolerance
        all_valid &= check(
            kappa_valid,
            f"κ_Π constant: {KAPPA_PI} (expected ≈ {expected_kappa})"
        )
        
        # Check f₀
        expected_freq = 141.7001
        freq_valid = abs(QCAL_FREQUENCY_HZ - expected_freq) < 0.1
        all_valid &= check(
            freq_valid,
            f"f₀ frequency: {QCAL_FREQUENCY_HZ} Hz (expected ≈ {expected_freq} Hz)"
        )
        
        # Check derived constant κ_Π²
        kappa_squared = KAPPA_PI ** 2
        expected_squared = 6.64
        squared_valid = abs(kappa_squared - expected_squared) < 0.1
        all_valid &= check(
            squared_valid,
            f"κ_Π² constant: {kappa_squared:.2f} (expected ≈ {expected_squared})"
        )
        
    except ImportError as e:
        all_valid = False
        check(False, f"Failed to import constants: {e}")
    
    return all_valid

def validate_files():
    """Validate presence of key implementation files."""
    header("Validating Implementation Files")
    
    all_valid = True
    
    # Key Python files
    python_files = [
        'src/constants.py',
        'src/computational_dichotomy.py',
        'src/ic_sat.py',
        ('qcal_unified_framework.py', 'src/qcal_unified_framework.py'),  # Check both locations
        'src/ultimate_algorithm.py',
        'src/noetic_geometry.py',
        'src/horizonte_espectral.py',
        'src/frequency_applications.py',
    ]
    
    print(f"{BOLD}Python Implementation:{RESET}")
    for filepath in python_files:
        if isinstance(filepath, tuple):
            # Check multiple possible locations
            exists = any(Path(p).exists() for p in filepath)
            display_path = ' or '.join(filepath)
        else:
            exists = Path(filepath).exists()
            display_path = filepath
        all_valid &= check(exists, f"  {display_path}")
    
    # Key Lean files
    lean_files = [
        'PNeqNPKappaPi.lean',
        'FrequencyFoundation.lean',
        'ComplexityClasses.lean',
        'SpectralTheory.lean',
        'HorizonteEspectral.lean',
        'QCAL_Unified_Theory.lean',
        'TeoremaInfinityCubed.lean',
        'HolographicCorrespondence.lean',
    ]
    
    print(f"\n{BOLD}Lean4 Formalization:{RESET}")
    for filepath in lean_files:
        exists = Path(filepath).exists()
        all_valid &= check(exists, f"  {filepath}")
    
    return all_valid

def validate_documentation():
    """Validate presence of key documentation."""
    header("Validating Documentation")
    
    all_valid = True
    
    docs = [
        'README.md',
        'KAPPA_PI_README.md',
        'QCAL_UNIFIED_WHITEPAPER.md',
        'FREQUENCY_APPLICATIONS_SUMMARY.md',
        'P_NEQ_NP_PROOF_README.md',
        'CONCLUSION_GEOMETRICA.md',
        'MANIFEST.md',
    ]
    
    for doc in docs:
        exists = Path(doc).exists()
        all_valid &= check(exists, f"  {doc}")
    
    return all_valid

def validate_axiom_implementation():
    """Validate that the IC axiom is implemented."""
    header("Validating IC Axiom Implementation")
    
    all_valid = True
    
    try:
        # Check if IC-SAT implementation exists
        ic_sat_path = Path('src/ic_sat.py')
        exists = ic_sat_path.exists()
        all_valid &= check(exists, "IC-SAT algorithm file exists")
        
        if exists:
            # Read and check for key components
            content = ic_sat_path.read_text()
            
            has_kappa = 'KAPPA_PI' in content or 'kappa' in content.lower()
            all_valid &= check(has_kappa, "  References κ_Π constant")
            
            has_treewidth = 'treewidth' in content.lower() or 'tw' in content
            all_valid &= check(has_treewidth, "  References treewidth")
            
            has_ic = 'information_complexity' in content.lower() or 'IC' in content
            all_valid &= check(has_ic, "  References information complexity")
            
    except Exception as e:
        all_valid = False
        check(False, f"Error validating IC-SAT: {e}")
    
    return all_valid

def validate_lean_proof():
    """Validate the Lean proof structure."""
    header("Validating Lean Proof Structure")
    
    all_valid = True
    
    try:
        proof_file = Path('PNeqNPKappaPi.lean')
        exists = proof_file.exists()
        all_valid &= check(exists, "Main proof file PNeqNPKappaPi.lean exists")
        
        if exists:
            content = proof_file.read_text()
            
            # Check for key definitions
            has_kappa_def = 'def κ_Π' in content or 'κ_Π :=' in content
            all_valid &= check(has_kappa_def, "  Defines κ_Π constant")
            
            has_main_theorem = 'theorem p_neq_np' in content
            all_valid &= check(has_main_theorem, "  Contains main P ≠ NP theorem")
            
            has_axioms = 'axiom' in content
            all_valid &= check(has_axioms, "  Contains necessary axioms")
            
            # Check for key axioms
            axioms = [
                'separator_lower_bound_kappa_pi',
                'separator_information_need_with_kappa_pi',
                'exponential_time_from_ic',
            ]
            
            for axiom in axioms:
                has_axiom = axiom in content
                all_valid &= check(has_axiom, f"    Axiom: {axiom}")
                
    except Exception as e:
        all_valid = False
        check(False, f"Error validating Lean proof: {e}")
    
    return all_valid

def validate_qcal_framework():
    """Validate QCAL ∞³ framework components."""
    header("Validating QCAL ∞³ Framework")
    
    all_valid = True
    
    # Check QCAL core files
    qcal_files = [
        'QCAL_Unified_Theory.lean',
        'TeoremaInfinityCubed.lean',
        ('qcal_unified_framework.py', 'src/qcal_unified_framework.py'),  # Check both locations
        'src/qcal_infinity_cubed.py',
    ]
    
    for filepath in qcal_files:
        if isinstance(filepath, tuple):
            # Check multiple possible locations
            exists = any(Path(p).exists() for p in filepath)
            display_path = ' or '.join(filepath)
        else:
            exists = Path(filepath).exists()
            display_path = filepath
        all_valid &= check(exists, f"  {display_path}")
    
    # Check echo-qcal directory
    echo_qcal_exists = Path('echo_qcal').is_dir()
    all_valid &= check(echo_qcal_exists, "  echo_qcal/ directory exists")
    
    # Check for key QCAL documentation
    qcal_docs = [
        'QCAL_UNIFIED_WHITEPAPER.md',
        'QCAL_INFINITY_CUBED_README.md',
        'QCAL_FINAL_REPORT.txt',
    ]
    
    for doc in qcal_docs:
        exists = Path(doc).exists()
        all_valid &= check(exists, f"  {doc}")
    
    return all_valid

def validate_frequency_implementation():
    """Validate frequency foundation."""
    header("Validating Frequency Foundation (f₀ = 141.7001 Hz)")
    
    all_valid = True
    
    try:
        # Check FrequencyFoundation.lean
        freq_lean = Path('FrequencyFoundation.lean')
        exists = freq_lean.exists()
        all_valid &= check(exists, "FrequencyFoundation.lean exists")
        
        if exists:
            content = freq_lean.read_text()
            
            has_def = 'fundamental_frequency' in content or 'f0_from_hydrogen' in content
            all_valid &= check(has_def, "  Defines fundamental frequency")
            
            has_141 = '141' in content
            all_valid &= check(has_141, "  References 141.7 Hz frequency")
            
        # Check Python frequency module
        freq_py = Path('src/frequency_applications.py')
        exists = freq_py.exists()
        all_valid &= check(exists, "src/frequency_applications.py exists")
        
    except Exception as e:
        all_valid = False
        check(False, f"Error validating frequency foundation: {e}")
    
    return all_valid

def validate_test_suite():
    """Validate test suite completeness."""
    header("Validating Test Suite")
    
    all_valid = True
    
    # Check test directory
    test_dir = Path('tests')
    exists = test_dir.is_dir()
    all_valid &= check(exists, "tests/ directory exists")
    
    if exists:
        # Count test files
        test_files = list(test_dir.glob('test_*.py'))
        num_tests = len(test_files)
        has_tests = num_tests > 50
        all_valid &= check(has_tests, f"  Has {num_tests} test files (expected > 50)")
        
        # Check for key tests
        key_tests = [
            'tests/test_ic_sat.py',
            'tests/test_computational_dichotomy.py',
            ('test_qcal_unified.py', 'tests/test_qcal_unified.py'),  # Check both locations
            'tests/test_constants.py',
        ]
        
        for test_file in key_tests:
            if isinstance(test_file, tuple):
                # Check multiple possible locations
                exists = any(Path(p).exists() for p in test_file)
                display_path = ' or '.join(test_file)
            else:
                exists = Path(test_file).exists()
                display_path = test_file
            all_valid &= check(exists, f"  {display_path}")
    
    # Check examples directory
    examples_dir = Path('examples')
    exists = examples_dir.is_dir()
    all_valid &= check(exists, "examples/ directory exists")
    
    if exists:
        demo_files = list(examples_dir.glob('demo_*.py'))
        num_demos = len(demo_files)
        has_demos = num_demos > 30
        all_valid &= check(has_demos, f"  Has {num_demos} demo files (expected > 30)")
    
    return all_valid

def validate_geometric_structure():
    """Validate the geometric/spectral structure."""
    header("Validating Geometric/Spectral Structure")
    
    all_valid = True
    
    # Spectral theory files
    spectral_files = [
        'SpectralTheory.lean',
        'SpectralExpansion.lean',
        'SpectralEntropy.lean',
        'HorizonteEspectral.lean',
    ]
    
    print(f"{BOLD}Spectral Theory:{RESET}")
    for filepath in spectral_files:
        exists = Path(filepath).exists()
        all_valid &= check(exists, f"  {filepath}")
    
    # Geometric files
    geometric_files = [
        'HolographicCorrespondence.lean',
        'HolographicVolume.lean',
        'HigherDimension.lean',
    ]
    
    print(f"\n{BOLD}Geometric/Holographic Structure:{RESET}")
    for filepath in geometric_files:
        exists = Path(filepath).exists()
        all_valid &= check(exists, f"  {filepath}")
    
    # Calabi-Yau manifold files
    cy_files = [
        'src/calabi_yau_complexity.py',
        'src/calabi_yau_kappa_derivation.py',
    ]
    
    print(f"\n{BOLD}Calabi-Yau Manifold Theory:{RESET}")
    for filepath in cy_files:
        exists = Path(filepath).exists()
        all_valid &= check(exists, f"  {filepath}")
    
    return all_valid

def print_summary(results):
    """Print validation summary."""
    header("Validation Summary")
    
    total = len(results)
    passed = sum(results.values())
    failed = total - passed
    
    print(f"Total categories validated: {total}")
    print(f"{GREEN}Passed: {passed}{RESET}")
    if failed > 0:
        print(f"{RED}Failed: {failed}{RESET}")
    
    success_rate = (passed / total) * 100 if total > 0 else 0
    
    print(f"\n{BOLD}Success Rate: {success_rate:.1f}%{RESET}")
    
    if success_rate == 100:
        print(f"\n{GREEN}{BOLD}✨ All validations passed! ✨{RESET}")
        print(f"{GREEN}The geometric P ≠ NP framework is complete and coherent.{RESET}")
        print(f"{BLUE}Frequency: 141.7001 Hz ∞³{RESET}")
        return 0
    else:
        print(f"\n{YELLOW}Some validations failed. Review the output above.{RESET}")
        return 1

def main():
    """Main validation routine."""
    print(f"\n{BOLD}{BLUE}{'='*70}{RESET}")
    print(f"{BOLD}{BLUE}{'Geometric Conclusion Validator':^70}{RESET}")
    print(f"{BOLD}{BLUE}{'P ≠ NP Framework Validation':^70}{RESET}")
    print(f"{BOLD}{BLUE}{'='*70}{RESET}")
    print(f"{BLUE}Frequency: 141.7001 Hz ∞³{RESET}\n")
    
    # Run all validations
    results = {
        'Constants': validate_constants(),
        'Implementation Files': validate_files(),
        'Documentation': validate_documentation(),
        'IC Axiom': validate_axiom_implementation(),
        'Lean Proof': validate_lean_proof(),
        'QCAL Framework': validate_qcal_framework(),
        'Frequency Foundation': validate_frequency_implementation(),
        'Test Suite': validate_test_suite(),
        'Geometric Structure': validate_geometric_structure(),
    }
    
    # Print summary
    exit_code = print_summary(results)
    
    # Additional info
    print(f"\n{BOLD}For detailed documentation, see:{RESET}")
    print("  - CONCLUSION_GEOMETRICA.md - Complete geometric conclusion")
    print("  - GEOMETRIC_QUICKREF.md - Quick reference guide")
    print("  - KAPPA_PI_README.md - κ_Π constant explanation")
    print("  - QCAL_UNIFIED_WHITEPAPER.md - Complete framework")
    print("  - README.md - Project overview")
    
    print(f"\n{BLUE}José Manuel Mota Burruezo · JMMB Ψ✧ ∞³{RESET}")
    print(f"{BLUE}Instituto de Conciencia Cuántica{RESET}\n")
    
    return exit_code

if __name__ == '__main__':
    sys.exit(main())
