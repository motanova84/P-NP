#!/usr/bin/env python3
"""
Generate comprehensive ENV.lock file for QCAL ∞³ ecosystem reproducibility
This ensures that auditors can reproduce bit-by-bit results across all repos.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Purpose: Garantiza reproducibilidad bit a bit de resultados para validación externa
"""

import subprocess
import sys
import hashlib
import json
import os
from datetime import datetime, timezone

def run_command(cmd):
    """Execute a shell command and return its output."""
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=30)
        return result.stdout.strip() if result.returncode == 0 else None
    except Exception as e:
        return f"Error: {str(e)}"

def get_file_hash(filepath):
    """Calculate SHA256 hash of a file."""
    try:
        sha256 = hashlib.sha256()
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(4096), b''):
                sha256.update(chunk)
        return sha256.hexdigest()
    except Exception as e:
        return f"Error: {str(e)}"

def get_json_file_info(filepath):
    """Get information about a JSON configuration file."""
    try:
        with open(filepath, 'r') as f:
            data = json.load(f)
        return {
            'path': filepath,
            'sha256': get_file_hash(filepath),
            'size_bytes': os.path.getsize(filepath),
            'keys': list(data.keys()) if isinstance(data, dict) else None
        }
    except Exception as e:
        return {'path': filepath, 'error': str(e)}

def generate_env_lock():
    """Generate comprehensive ENV.lock content."""
    
    content = []
    content.append("=" * 80)
    content.append("ENV.lock - Complete Environment Specification")
    content.append("QCAL ∞³ Ecosystem - P-NP Repository")
    content.append("=" * 80)
    content.append("")
    content.append(f"Generated: {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC")
    content.append(f"Purpose: Garantiza reproducibilidad bit a bit de resultados")
    content.append(f"         para validación externa y auditoría científica")
    content.append("")
    
    # Section 1: System Information
    content.append("=" * 80)
    content.append("SECTION 1: SYSTEM AND OPERATING ENVIRONMENT")
    content.append("=" * 80)
    content.append("")
    
    # OS information
    os_name = run_command("cat /etc/os-release | grep PRETTY_NAME | cut -d'=' -f2 | tr -d '\"'")
    os_version = run_command("cat /etc/os-release | grep VERSION_ID | cut -d'=' -f2 | tr -d '\"'")
    kernel = run_command("uname -r")
    arch = run_command("uname -m")
    
    content.append(f"Operating System: {os_name}")
    content.append(f"OS Version: {os_version}")
    content.append(f"Kernel: {kernel}")
    content.append(f"Architecture: {arch}")
    content.append("")
    
    # Section 2: Toolchain
    content.append("=" * 80)
    content.append("SECTION 2: TOOLCHAIN VERSIONS")
    content.append("=" * 80)
    content.append("")
    
    # Python
    python_version = run_command("python3 --version")
    pip_version = run_command("pip3 --version")
    content.append(f"Python: {python_version}")
    content.append(f"Pip: {pip_version}")
    content.append("")
    
    # GCC/G++
    gcc_version = run_command("gcc --version | head -1")
    gpp_version = run_command("g++ --version | head -1")
    if gcc_version:
        content.append(f"GCC: {gcc_version}")
    if gpp_version:
        content.append(f"G++: {gpp_version}")
    content.append("")
    
    # Lean 4
    lean_version = run_command("lean --version 2>&1 | head -1")
    lake_version = run_command("lake --version 2>&1 | head -1")
    
    # Read from lean-toolchain file
    lean_toolchain = None
    try:
        with open('lean-toolchain', 'r') as f:
            lean_toolchain = f.read().strip()
    except Exception:
        pass
    
    if lean_version and "not found" not in lean_version:
        content.append(f"Lean 4: {lean_version}")
        content.append(f"Lake: {lake_version}")
    else:
        content.append(f"Lean 4: Not installed (expected version from lean-toolchain: {lean_toolchain})")
        content.append(f"  Note: Install with: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh")
    
    if lean_toolchain:
        content.append(f"Lean Toolchain (lean-toolchain file): {lean_toolchain}")
    content.append("")
    
    # Git
    git_version = run_command("git --version")
    content.append(f"Git: {git_version}")
    content.append("")
    
    # Section 3: Repository State
    content.append("=" * 80)
    content.append("SECTION 3: REPOSITORY STATE")
    content.append("=" * 80)
    content.append("")
    
    git_commit = run_command("git rev-parse HEAD")
    git_branch = run_command("git rev-parse --abbrev-ref HEAD")
    git_remote = run_command("git config --get remote.origin.url")
    
    content.append(f"Git Commit (HEAD): {git_commit}")
    content.append(f"Git Branch: {git_branch}")
    content.append(f"Git Remote: {git_remote}")
    content.append("")
    
    # Section 4: Python Dependencies
    content.append("=" * 80)
    content.append("SECTION 4: PYTHON DEPENDENCIES")
    content.append("=" * 80)
    content.append("")
    content.append("Python packages installed (pip freeze):")
    content.append("")
    
    pip_freeze = run_command("pip3 freeze")
    if pip_freeze:
        for line in pip_freeze.split('\n'):
            content.append(f"  {line}")
    content.append("")
    
    # Hash of pip freeze for verification
    pip_freeze_hash = hashlib.sha256(pip_freeze.encode()).hexdigest() if pip_freeze else "N/A"
    content.append(f"SHA256 checksum of pip freeze output: {pip_freeze_hash}")
    content.append("")
    
    # Section 5: Lean Dependencies
    content.append("=" * 80)
    content.append("SECTION 5: LEAN 4 DEPENDENCIES")
    content.append("=" * 80)
    content.append("")
    
    # Read lakefile.lean
    try:
        with open('lakefile.lean', 'r') as f:
            lakefile_content = f.read()
        
        content.append("Lakefile configuration:")
        content.append("")
        
        # Extract mathlib dependency
        for line in lakefile_content.split('\n'):
            if 'require mathlib' in line or '@' in line:
                content.append(f"  {line.strip()}")
        
        content.append("")
        content.append(f"Lakefile SHA256: {get_file_hash('lakefile.lean')}")
    except Exception as e:
        content.append(f"Error reading lakefile.lean: {e}")
    
    content.append("")
    
    # Section 6: Configuration Files and Datasets
    content.append("=" * 80)
    content.append("SECTION 6: CONFIGURATION FILES AND DATASETS")
    content.append("=" * 80)
    content.append("")
    
    config_files = [
        'coherence_map.json',
        'CORE_SYMBIO.json',
        'symbolic_map_CY_kappa.json',
        'ultimate_unification.json',
        'requirements.txt'
    ]
    
    content.append("Critical configuration files:")
    content.append("")
    
    for filepath in config_files:
        if os.path.exists(filepath):
            file_hash = get_file_hash(filepath)
            file_size = os.path.getsize(filepath)
            content.append(f"  {filepath}:")
            content.append(f"    SHA256: {file_hash}")
            content.append(f"    Size: {file_size} bytes")
            
            # For JSON files, show keys
            if filepath.endswith('.json'):
                try:
                    with open(filepath, 'r') as f:
                        data = json.load(f)
                    if isinstance(data, dict):
                        content.append(f"    Keys: {', '.join(data.keys())}")
                except:
                    pass
            content.append("")
    
    # Section 7: Universal Constants
    content.append("=" * 80)
    content.append("SECTION 7: UNIVERSAL CONSTANTS AND SEEDS")
    content.append("=" * 80)
    content.append("")
    
    # Read from CORE_SYMBIO.json
    try:
        with open('CORE_SYMBIO.json', 'r') as f:
            core_symbio = json.load(f)
        
        content.append("QCAL ∞³ Universal Constants:")
        content.append("")
        if 'constants' in core_symbio:
            for key, value in core_symbio['constants'].items():
                content.append(f"  {key} = {value}")
        content.append("")
        
        content.append("Key frequencies and values:")
        content.append("  f₀ = 141.7001 Hz (fundamental QCAL frequency)")
        content.append("  κ_Π = 2.5773302292 (Calabi-Yau geometric constant)")
        content.append("  σ_detection = 18.2 (detection significance for GW150914/250114)")
        content.append("")
    except Exception:
        pass
    
    content.append("Random Seeds:")
    content.append("  Default NumPy seed: None (explicitly set in scripts if needed)")
    content.append("  Note: For reproducible results, scripts should set: np.random.seed(42)")
    content.append("")
    
    # Section 8: Build and Test Commands
    content.append("=" * 80)
    content.append("SECTION 8: BUILD AND VERIFICATION COMMANDS")
    content.append("=" * 80)
    content.append("")
    
    content.append("Python environment setup:")
    content.append("  pip install -r requirements.txt")
    content.append("")
    
    content.append("Lean 4 build (requires elan/Lean 4 installation):")
    content.append("  lake build")
    content.append("  lake exe pnp")
    content.append("")
    
    content.append("Test execution:")
    content.append("  ./run_all_tests.sh          # Comprehensive Python test suite")
    content.append("  python3 simple_demo.py       # Quick demonstration")
    content.append("  ./verify_build.sh            # Lean project verification")
    content.append("")
    
    content.append("Key validations:")
    content.append("  python3 validate_qcal_pi.py                    # QCAL π theorem")
    content.append("  python3 verify_kappa.py                        # κ_Π verification")
    content.append("  python3 holographic_verification.py            # Holographic proof")
    content.append("  python3 kappa_verification.py                  # Calabi-Yau validation")
    content.append("")
    
    # Section 9: Ecosystem Links
    content.append("=" * 80)
    content.append("SECTION 9: QCAL ∞³ ECOSYSTEM REPOSITORIES")
    content.append("=" * 80)
    content.append("")
    
    content.append("Related repositories for complete context:")
    content.append("")
    content.append("  1. motanova84/P-NP")
    content.append("     Role: Complexity theory resolution")
    content.append("     Key: κ_Π = 2.5773, treewidth-IC framework")
    content.append("")
    content.append("  2. motanova84/141hz")
    content.append("     Role: GW150914/GW250114 analysis at 141.7001 Hz")
    content.append("     Key: Universal frequency detection")
    content.append("")
    content.append("  3. motanova84/Riemann-adelic")
    content.append("     Role: Quantum geometry and zeta function")
    content.append("     Key: Spectral proof framework")
    content.append("")
    content.append("  4. motanova84/adelic-bsd")
    content.append("     Role: Arithmetic compatibility")
    content.append("     Key: Birch-Swinnerton-Dyer connections")
    content.append("")
    content.append("  5. motanova84/3D-Navier-Stokes")
    content.append("     Role: Fluid dynamics and millennium problem")
    content.append("     Key: Dimensional analysis")
    content.append("")
    content.append("  6. motanova84/Ramsey")
    content.append("     Role: SAT verification and R(6,6)=108")
    content.append("     Key: Combinatorial validation")
    content.append("")
    content.append("  7. motanova84/economia-qcal-nodo-semilla")
    content.append("     Role: QCAL economy and πCODE")
    content.append("     Key: Economic coherence framework")
    content.append("")
    
    content.append("Note: All repositories share the QCAL ∞³ protocol and use")
    content.append("      consistent constants (f₀, κ_Π, etc.) for cross-validation.")
    content.append("")
    
    # Section 10: Verification Instructions
    content.append("=" * 80)
    content.append("SECTION 10: EXTERNAL VERIFICATION PROCEDURE")
    content.append("=" * 80)
    content.append("")
    
    content.append("For auditors and reviewers to reproduce results:")
    content.append("")
    content.append("1. System Setup:")
    content.append("   - Install Ubuntu 24.04 LTS (or compatible Linux distribution)")
    content.append("   - Install Python 3.12.3 or compatible version")
    content.append("   - Install GCC 13.3.0 or compatible C/C++ compiler")
    content.append("")
    content.append("2. Clone Repository:")
    content.append("   git clone https://github.com/motanova84/P-NP.git")
    content.append("   cd P-NP")
    content.append(f"   git checkout {git_commit}")
    content.append("")
    content.append("3. Install Python Dependencies:")
    content.append("   pip3 install -r requirements.txt")
    content.append("   # Verify with: pip3 freeze > /tmp/check.txt")
    content.append(f"   # Compare SHA256: {pip_freeze_hash}")
    content.append("")
    content.append("4. Install Lean 4 (optional, for formal verification):")
    content.append("   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh")
    content.append("   export PATH=\"$HOME/.elan/bin:$PATH\"")
    content.append("   lake build")
    content.append("")
    content.append("5. Verify Configuration Files:")
    content.append("   # Check SHA256 checksums of configuration files listed in Section 6")
    content.append("   sha256sum coherence_map.json CORE_SYMBIO.json")
    content.append("")
    content.append("6. Run Tests:")
    content.append("   ./run_all_tests.sh")
    content.append("   python3 simple_demo.py")
    content.append("")
    content.append("7. Validate Key Results:")
    content.append("   python3 kappa_verification.py  # Should confirm κ_Π ≈ 2.5773")
    content.append("   python3 validate_qcal_pi.py    # Should validate QCAL π theorem")
    content.append("   python3 holographic_verification.py  # Should verify holographic proof")
    content.append("")
    content.append("Expected outcomes:")
    content.append("  - 141.7001 Hz frequency detection reproduced")
    content.append("  - κ_Π = 2.5773302292 constant verified across 150 CY manifolds")
    content.append("  - Lean 4 proofs compile without 'sorry' axioms")
    content.append("  - All tests pass with consistent results")
    content.append("")
    
    # Footer
    content.append("=" * 80)
    content.append("END OF ENV.lock")
    content.append("=" * 80)
    content.append("")
    content.append("This file serves as the 'reality hash' for QCAL ∞³ reproducibility.")
    content.append("Any modification to the environment should be reflected here.")
    content.append("")
    content.append("For questions or verification issues, contact: motanova84")
    content.append(f"Generated by: generate_env_lock.py")
    content.append(f"Timestamp: {datetime.now(timezone.utc).isoformat()}Z")
    content.append("")
    
    return '\n'.join(content)

if __name__ == '__main__':
    env_lock_content = generate_env_lock()
    
    # Write to ENV.lock
    with open('ENV.lock', 'w') as f:
        f.write(env_lock_content)
    
    print("✅ ENV.lock generated successfully")
    print(f"   File size: {len(env_lock_content)} bytes")
    print(f"   Lines: {len(env_lock_content.split(chr(10)))}")
    print("")
    print("This file provides complete environment specification for:")
    print("  - System and toolchain versions")
    print("  - All Python dependencies with exact versions")
    print("  - Lean 4 dependencies and configuration")
    print("  - Configuration files with checksums")
    print("  - Universal constants and seeds")
    print("  - Build/test commands")
    print("  - Ecosystem repository links")
    print("  - External verification procedures")
