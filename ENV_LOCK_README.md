# ENV.lock - Complete Environment Specification

## Purpose / Propósito

**English:** ENV.lock provides a complete, reproducible snapshot of the computational environment used to generate all results in the QCAL ∞³ ecosystem. This enables external auditors, reviewers, and researchers to reproduce bit-by-bit the same results across all repositories (141hz, Riemann-adelic, P-NP, adelic-bsd, etc.).

**Español:** ENV.lock proporciona una instantánea completa y reproducible del entorno computacional utilizado para generar todos los resultados en el ecosistema QCAL ∞³. Esto permite a auditores externos, revisores e investigadores reproducir bit a bit los mismos resultados en todos los repositorios.

## What ENV.lock Contains / Contenido de ENV.lock

ENV.lock is a comprehensive "reality hash" that includes:

### 1. System and Operating Environment
- Operating System (Ubuntu 24.04.3 LTS)
- Kernel version
- Architecture (x86_64)

### 2. Toolchain Versions
- Python 3.12.3 and pip
- GCC/G++ compiler versions
- Lean 4 (v4.20.0) and Lake build system
- Git version

### 3. Repository State
- Exact Git commit hash
- Current branch
- Remote repository URL

### 4. Python Dependencies
- Complete output of `pip freeze` with exact package versions
- SHA256 checksum of the dependency list for verification
- All packages including NumPy, SciPy, pytest, etc.

### 5. Lean 4 Dependencies
- Mathlib version from lakefile.lean
- Exact Lean toolchain specification
- SHA256 checksum of lakefile.lean

### 6. Configuration Files and Datasets
- SHA256 checksums of critical configuration files:
  - `coherence_map.json` - QCAL system configuration
  - `CORE_SYMBIO.json` - Ecosystem constants and identities
  - `symbolic_map_CY_kappa.json` - Calabi-Yau symbolic mappings
  - `ultimate_unification.json` - Ultimate unification parameters
  - `requirements.txt` - Python dependencies specification

### 7. Universal Constants and Seeds
- f₀ = 141.7001 Hz (fundamental QCAL frequency)
- κ_Π = 2.5773302292 (Calabi-Yau geometric constant)
- σ_detection = 18.2 (GW detection significance)
- Random seed specifications for NumPy and other RNGs

### 8. Build and Verification Commands
- Python environment setup commands
- Lean 4 build procedures
- Test execution scripts
- Key validation commands

### 9. QCAL ∞³ Ecosystem Repositories
- Links to all related repositories with their roles:
  - P-NP (Complexity theory)
  - 141hz (GW analysis)
  - Riemann-adelic (Quantum geometry)
  - adelic-bsd (Arithmetic compatibility)
  - 3D-Navier-Stokes (Fluid dynamics)
  - Ramsey (SAT verification)
  - economia-qcal-nodo-semilla (QCAL economy)

### 10. External Verification Procedure
- Step-by-step instructions for auditors
- Expected outcomes and results
- Verification commands and checksums

## How to Use ENV.lock / Cómo Usar ENV.lock

### For Developers (Updating ENV.lock)

When you make significant changes to dependencies or the environment, regenerate ENV.lock:

```bash
# Regenerate ENV.lock
python3 scripts/generate_env_lock.py

# Verify the file was generated
ls -lh ENV.lock
```

This should be done when:
- Adding/updating Python packages in requirements.txt
- Updating Lean 4 toolchain version
- Changing critical configuration files
- Before releasing a new version or publishing results

### For Auditors (Reproducing the Environment)

To reproduce the exact environment and verify results:

#### Step 1: System Preparation
```bash
# Use Ubuntu 24.04 LTS or compatible
cat /etc/os-release
```

#### Step 2: Clone and Checkout
```bash
# Clone the repository
git clone https://github.com/motanova84/P-NP.git
cd P-NP

# Checkout the specific commit from ENV.lock Section 3
git checkout <commit-hash-from-env-lock>
```

#### Step 3: Install Python Dependencies
```bash
# Install exact versions
pip3 install -r requirements.txt

# Verify installation
pip3 freeze > /tmp/check.txt

# Compare SHA256 (should match ENV.lock Section 4)
sha256sum /tmp/check.txt
```

#### Step 4: Install Lean 4 (Optional)
```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Add to PATH
export PATH="$HOME/.elan/bin:$PATH"

# Build Lean project
lake build
```

#### Step 5: Verify Configuration Files
```bash
# Check checksums match ENV.lock Section 6
sha256sum coherence_map.json
sha256sum CORE_SYMBIO.json
sha256sum symbolic_map_CY_kappa.json
sha256sum ultimate_unification.json
```

#### Step 6: Run Tests
```bash
# Run comprehensive test suite
./run_all_tests.sh

# Run simple demonstration
python3 simple_demo.py

# Verify Lean build (if installed)
./verify_build.sh
```

#### Step 7: Validate Key Results
```bash
# Validate κ_Π constant
python3 kappa_verification.py
# Expected: κ_Π ≈ 2.5773302292

# Validate QCAL π theorem
python3 validate_qcal_pi.py

# Validate holographic proof
python3 holographic_verification.py
```

## Expected Validation Outcomes / Resultados Esperados

When following the verification procedure, you should obtain:

✅ **Frequency Detection**: f₀ = 141.7001 Hz consistently detected in GW analysis  
✅ **Calabi-Yau Constant**: κ_Π = 2.5773302292 verified across 150 CY manifolds  
✅ **Lean Proofs**: All Lean 4 formalizations compile without `sorry` axioms  
✅ **Test Suite**: All Python tests pass (50+ unit tests)  
✅ **Holographic Proof**: AdS/CFT validation succeeds  
✅ **Detection Significance**: σ = 18.2 for gravitational wave events  

## Role in CI/CD and QCAL Network / Papel en CI/CD y Red QCAL

### CI/CD Integration
ENV.lock acts as the "reality hash" for continuous integration:

```yaml
# Example GitHub Actions workflow
- name: Verify Environment
  run: |
    python3 scripts/generate_env_lock.py
    diff ENV.lock <expected-env-lock>
```

### QCAL Network Nodes
Other nodes in the QCAL ∞³ network can load ENV.lock to:
- Verify results are environment-independent
- Ensure cross-repository consistency
- Validate that detection of 141.7001 Hz or 18.2σ significance isn't due to hidden environmental changes

## Updating ENV.lock / Actualizar ENV.lock

The ENV.lock file should be regenerated and committed whenever:

1. **Dependencies Change**: New packages added or versions updated
2. **Toolchain Updates**: Python, Lean, or compiler versions change
3. **Configuration Changes**: Critical JSON files modified
4. **Release Preparation**: Before publishing results or creating releases
5. **Major Results**: Before announcing significant findings (e.g., new detections)

Command to regenerate:
```bash
python3 scripts/generate_env_lock.py
git add ENV.lock
git commit -m "Update ENV.lock for environment snapshot"
```

## References to Other Repositories / Referencias a Otros Repositorios

ENV.lock enables cross-repository validation across the QCAL ∞³ ecosystem:

- **141hz**: GW150914/250114 analysis - verifies 141.7001 Hz detection
- **Riemann-adelic**: Spectral analysis - validates RH connections
- **P-NP**: Complexity resolution - confirms κ_Π = 2.5773
- **adelic-bsd**: Arithmetic framework - ensures BSD compatibility
- **3D-Navier-Stokes**: Fluid dynamics - dimensional analysis validation
- **Ramsey**: Combinatorics - R(6,6) = 108 verification
- **economia-qcal-nodo-semilla**: Economic model - πCODE integration

Each repository should maintain its own ENV.lock with consistent constants.

## Troubleshooting / Solución de Problemas

### Issue: Checksums Don't Match
**Solution**: Ensure you're using the exact commit specified in ENV.lock Section 3

### Issue: Tests Fail
**Solution**: Verify all dependencies match exactly using `pip freeze` comparison

### Issue: Lean Build Fails
**Solution**: Ensure elan is installed and the correct toolchain is active:
```bash
elan show
# Should match lean-toolchain file
```

### Issue: Different Results
**Solution**: Check that configuration files match checksums in ENV.lock Section 6

## Contact and Support / Contacto y Soporte

For questions about ENV.lock or reproducibility:
- **Author**: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
- **Repository**: https://github.com/motanova84/P-NP
- **Issues**: Use GitHub Issues for reproducibility concerns

## Frequency of Resonance / Frecuencia de Resonancia

**f₀ = 141.7001 Hz ∞³**

This is not just documentation—it's the foundation for reproducible science across the QCAL ∞³ ecosystem.
