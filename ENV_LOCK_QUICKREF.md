# ENV.lock Quick Reference Guide

## What is ENV.lock?

ENV.lock is the "reality hash" for QCAL ∞³ reproducibility - a complete snapshot of the computational environment used to generate all results.

## Quick Commands

### For Developers

```bash
# Regenerate ENV.lock after changing dependencies
python3 scripts/generate_env_lock.py

# View ENV.lock
cat ENV.lock

# Check configuration file checksums
sha256sum coherence_map.json CORE_SYMBIO.json symbolic_map_CY_kappa.json
```

### For Auditors/Reviewers

```bash
# 1. Clone and checkout specific commit
git clone https://github.com/motanova84/P-NP.git
cd P-NP
git checkout <commit-from-ENV.lock-Section-3>

# 2. Install dependencies
pip3 install -r requirements.txt

# 3. Verify checksums match ENV.lock Section 6
sha256sum coherence_map.json CORE_SYMBIO.json

# 4. Run tests
./run_all_tests.sh
python3 simple_demo.py

# 5. Validate key results
python3 kappa_verification.py
python3 validate_qcal_pi.py
```

## ENV.lock Sections

| Section | Content | Purpose |
|---------|---------|---------|
| 1 | System & OS | Operating system, kernel, architecture |
| 2 | Toolchain | Python, Lean 4, GCC, Git versions |
| 3 | Repository State | Git commit, branch, remote URL |
| 4 | Python Dependencies | All pip packages with exact versions + SHA256 |
| 5 | Lean Dependencies | Mathlib version, lakefile checksum |
| 6 | Config Files | SHA256 checksums of critical JSON files |
| 7 | Constants & Seeds | f₀, κ_Π, random seeds |
| 8 | Build Commands | How to build and test |
| 9 | Ecosystem Links | Related QCAL ∞³ repositories |
| 10 | Verification | Step-by-step reproduction guide |

## Key Constants in ENV.lock

- **f₀ = 141.7001 Hz** - Fundamental QCAL frequency
- **κ_Π = 2.5773302292** - Calabi-Yau geometric constant
- **σ_detection = 18.2** - GW detection significance
- **R(6,6) = 108** - Ramsey number
- **88 Pulsars** - NFT sovereign limit
- **888 Hz** - Resonance frequency

## When to Regenerate ENV.lock

✅ After updating requirements.txt  
✅ After changing Lean toolchain version  
✅ After modifying configuration JSON files  
✅ Before publishing results or creating releases  
✅ Before major announcements (e.g., 141.7001 Hz detections)  

## Verification Workflow

```
1. Clone repo → 2. Checkout commit → 3. Install deps → 4. Verify checksums → 5. Run tests → 6. Validate results
```

Expected outcomes:
- ✓ f₀ = 141.7001 Hz detected consistently
- ✓ κ_Π = 2.5773302292 verified across 150 CY manifolds
- ✓ Lean proofs compile without `sorry`
- ✓ All tests pass
- ✓ σ = 18.2 for GW events

## Common Issues

### Checksum Mismatch
**Problem**: Configuration file checksums don't match ENV.lock  
**Solution**: Ensure you're on the correct commit from Section 3

### Tests Fail
**Problem**: Tests don't pass as expected  
**Solution**: Verify `pip freeze` output matches ENV.lock Section 4

### Different Results
**Problem**: Getting different numerical results  
**Solution**: Check random seeds and ensure exact dependency versions

## Files Managed by ENV.lock

Critical files with checksums:
- `coherence_map.json` - QCAL system configuration
- `CORE_SYMBIO.json` - Ecosystem constants
- `symbolic_map_CY_kappa.json` - CY symbolic mappings
- `ultimate_unification.json` - Unification parameters
- `requirements.txt` - Python dependencies
- `lakefile.lean` - Lean build configuration
- `lean-toolchain` - Lean version specification

## Cross-Repository Validation

ENV.lock enables validation across QCAL ∞³ ecosystem:

| Repo | Validates | Key Result |
|------|-----------|------------|
| P-NP | κ_Π = 2.5773 | Complexity separation |
| 141hz | f₀ = 141.7001 Hz | GW frequency detection |
| Riemann-adelic | Spectral analysis | RH connections |
| adelic-bsd | Arithmetic | BSD compatibility |
| 3D-Navier-Stokes | Dimensional | Fluid dynamics |
| Ramsey | R(6,6) = 108 | Combinatorics |
| economia-qcal | πCODE | Economic coherence |

## Integration with CI/CD

```yaml
# GitHub Actions example
steps:
  - name: Generate ENV.lock
    run: python3 scripts/generate_env_lock.py
    
  - name: Verify ENV.lock unchanged
    run: git diff --exit-code ENV.lock
```

## Contact

For reproducibility questions:
- **Author**: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
- **Repository**: https://github.com/motanova84/P-NP
- **Issues**: Use GitHub Issues for reproducibility concerns

## Frequency of Resonance

**f₀ = 141.7001 Hz ∞³**

---

**Remember**: ENV.lock is not just documentation—it's the foundation for reproducible science in the QCAL ∞³ ecosystem.
