#!/usr/bin/env python3
"""
Comprehensive test suite for all implemented phases
Tests Phase 1-5 implementations
"""

import sys
import subprocess

def test_kappa_verification():
    """Test Phase 1: κ_Π verification"""
    print("=" * 60)
    print("TESTING PHASE 1: κ_Π Verification")
    print("=" * 60)
    
    try:
        result = subprocess.run(
            ["python3", "scripts/verify_kappa.py"],
            capture_output=True, text=True, timeout=10
        )
        print(result.stdout)
        if result.returncode == 0:
            print("✅ Phase 1 PASSED")
            return True
        else:
            print("❌ Phase 1 FAILED")
            print(result.stderr)
            return False
    except Exception as e:
        print(f"❌ Phase 1 ERROR: {e}")
        return False

def test_calabi_yau_complexity():
    """Test Phase 2: Calabi-Yau complexity"""
    print("\n" + "=" * 60)
    print("TESTING PHASE 2: Calabi-Yau Complexity Connection")
    print("=" * 60)
    
    try:
        result = subprocess.run(
            ["python3", "src/calabi_yau_complexity.py"],
            capture_output=True, text=True, timeout=10
        )
        print(result.stdout)
        if result.returncode == 0 and "RESULTADO" in result.stdout:
            print("✅ Phase 2 PASSED")
            return True
        else:
            print("❌ Phase 2 FAILED")
            print(result.stderr)
            return False
    except Exception as e:
        print(f"❌ Phase 2 ERROR: {e}")
        return False

def test_purification():
    """Test Phase 3: Scientific purification"""
    print("\n" + "=" * 60)
    print("TESTING PHASE 3: Scientific Purification")
    print("=" * 60)
    
    try:
        result = subprocess.run(
            ["bash", "scripts/purify_documentation.sh"],
            capture_output=True, text=True, timeout=10
        )
        print(result.stdout)
        if result.returncode == 0:
            print("✅ Phase 3 PASSED")
            return True
        else:
            print("❌ Phase 3 FAILED")
            return False
    except Exception as e:
        print(f"❌ Phase 3 ERROR: {e}")
        return False

def test_physical_frequency():
    """Test Phase 3b: Physical frequency derivation"""
    print("\n" + "=" * 60)
    print("TESTING PHASE 3b: Physical Frequency f₀")
    print("=" * 60)
    
    try:
        result = subprocess.run(
            ["python3", "src/physical_frequency.py"],
            capture_output=True, text=True, timeout=10
        )
        print(result.stdout)
        if result.returncode == 0 and "141.7001" in result.stdout:
            print("✅ Phase 3b PASSED")
            return True
        else:
            print("❌ Phase 3b FAILED")
            return False
    except Exception as e:
        print(f"❌ Phase 3b ERROR: {e}")
        return False

def test_audit_sorries():
    """Test Phase 4: Proof audit"""
    print("\n" + "=" * 60)
    print("TESTING PHASE 4: Proof Audit")
    print("=" * 60)
    
    try:
        result = subprocess.run(
            ["bash", "scripts/audit_sorries.sh"],
            capture_output=True, text=True, timeout=10
        )
        print(result.stdout[:500])  # Print first 500 chars
        if result.returncode == 0:
            print("✅ Phase 4 PASSED")
            return True
        else:
            print("❌ Phase 4 FAILED")
            return False
    except Exception as e:
        print(f"❌ Phase 4 ERROR: {e}")
        return False

def test_file_existence():
    """Test that all required files exist"""
    print("\n" + "=" * 60)
    print("TESTING: File Existence")
    print("=" * 60)
    
    import os
    
    required_files = [
        "Formal/KappaPi/Derivation.lean",
        "Formal/CalabiYauComplexity/Duality.lean",
        "Formal/StructuralCoupling/Complete.lean",
        "scripts/verify_kappa.py",
        "scripts/purify_documentation.sh",
        "scripts/audit_sorries.sh",
        "scripts/create_submission_package.sh",
        "src/calabi_yau_complexity.py",
        "src/physical_frequency.py",
        "docs/README_SCIENTIFIC.md",
    ]
    
    all_exist = True
    for file in required_files:
        exists = os.path.exists(file)
        status = "✅" if exists else "❌"
        print(f"{status} {file}")
        if not exists:
            all_exist = False
    
    if all_exist:
        print("\n✅ All required files exist")
        return True
    else:
        print("\n❌ Some files missing")
        return False

def main():
    """Run all tests"""
    print("\n" + "=" * 60)
    print("COMPREHENSIVE TEST SUITE")
    print("Testing Phase 1-5 Implementation")
    print("=" * 60 + "\n")
    
    results = []
    
    # Test file existence first
    results.append(("File Existence", test_file_existence()))
    
    # Test each phase
    results.append(("Phase 1 (κ_Π)", test_kappa_verification()))
    results.append(("Phase 2 (CY-Complexity)", test_calabi_yau_complexity()))
    results.append(("Phase 3 (Purification)", test_purification()))
    results.append(("Phase 3b (f₀)", test_physical_frequency()))
    results.append(("Phase 4 (Audit)", test_audit_sorries()))
    
    # Summary
    print("\n" + "=" * 60)
    print("TEST SUMMARY")
    print("=" * 60)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for name, result in results:
        status = "✅ PASSED" if result else "❌ FAILED"
        print(f"{name:30s}: {status}")
    
    print(f"\nTotal: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n✅ ALL TESTS PASSED!")
        return 0
    else:
        print(f"\n⚠️  {total - passed} test(s) failed")
        return 1

if __name__ == "__main__":
    sys.exit(main())
