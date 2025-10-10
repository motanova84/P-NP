# Quick Start Guide

## For Users with Working Network Connection

Once you have proper network connectivity, follow these steps:

### 1. Install Lean 4
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile  # or restart your shell
```

### 2. Build the Project
```bash
cd /path/to/P-NP
lake build
```

Expected output:
```
info: downloading component 'lean'
info: installing component 'lean'
info: [1/4] Building PvsNP.Treewidth
info: [2/4] Building PvsNP.SILB
info: [3/4] Building PvsNP.Main
info: [4/4] Building Main
```

### 3. Run the Executable
```bash
lake exe pvsnp
```

Expected output:
```
P vs NP Formalization Framework
================================
This is a Lean 4 formalization of the P vs NP problem
using treewidth and information complexity.
```

### 4. Verify Individual Files (Optional)
```bash
lean --check PvsNP/Main.lean
lean --check PvsNP/Treewidth.lean
lean --check PvsNP/SILB.lean
lean --check tests/BasicTests.lean
```

Each should complete without errors.

### 5. Use the Automated Verification Script
```bash
./verify_build.sh
```

This will run all checks automatically and report the results.

## Understanding the Code

### Core Theorem: P ≠ NP
Located in `PvsNP/Main.lean`:
```lean
theorem P_ne_NP : ¬ (ComplexityClass.P = ComplexityClass.NP) := by
  sorry
```

The `sorry` keyword indicates this is a proof stub. The actual proof will be developed using the Treewidth-SILB framework.

### Computational Dichotomy
Also in `PvsNP/Main.lean`:
```lean
theorem computational_dichotomy (φ : CNF) (n : Nat) :
    (treewidth (incidence_graph φ) ≤ n → True) ∧
    (treewidth (incidence_graph φ) > n → True) := by
  constructor <;> intro <;> trivial
```

This theorem demonstrates the dichotomy based on treewidth. The actual formalization will be more sophisticated.

## Project Status

✅ **Complete:**
- Project structure
- Basic type definitions
- Placeholder theorems
- Build configuration
- Documentation

🚧 **In Development:**
- Full proof of P ≠ NP
- Treewidth algorithms
- SILB framework implementation
- Comprehensive test suite

## For Developers

To extend this project:

1. **Add treewidth algorithms:** Edit `PvsNP/Treewidth.lean`
2. **Implement SILB theory:** Edit `PvsNP/SILB.lean`
3. **Complete the proof:** Edit the `P_ne_NP` theorem in `PvsNP/Main.lean`
4. **Add tests:** Create new test files in the `tests/` directory

## Troubleshooting

### "lake: command not found"
- Ensure `~/.elan/bin` is in your PATH
- Run: `export PATH="$HOME/.elan/bin:$PATH"`
- Add to `~/.bashrc` or `~/.zshrc` to make permanent

### "error: error during download"
- Check your internet connection
- Try again later if GitHub is having issues
- Ensure you're not behind a restrictive firewall

### Build errors
- Ensure you're using Lean 4.3.0 (specified in `lean-toolchain`)
- Run `lake clean` and try again
- Check the error message for specific file issues

## Resources

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Lean 4 Theorem Proving](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Zulip Chat](https://leanprover.zulipchat.com/)

## Next Steps

1. Complete the treewidth theory in `PvsNP/Treewidth.lean`
2. Implement SILB framework in `PvsNP/SILB.lean`
3. Work on the actual proof of `P_ne_NP`
4. Add integration with Mathlib for graph theory
5. Create comprehensive test suites
6. Add examples and documentation
