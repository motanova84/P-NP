# Development Setup Guide

## Lean 4 Setup

### Installing Lean 4

1. **Install elan (Lean version manager)**:
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   source ~/.profile  # or restart terminal
   ```

2. **Verify installation**:
   ```bash
   lean --version
   lake --version
   ```

3. **Build the project**:
   ```bash
   cd /path/to/P-NP
   lake build
   ```

### Expected Output

On first build, Lake will:
- Download and cache dependencies (may take several minutes)
- Compile all `.lean` files
- Report any errors

**Note**: The current project uses `sorry` placeholders, so it will compile but not prove anything yet.

### Common Issues

**Issue**: `unknown package 'Mathlib'`  
**Solution**: Add Mathlib dependency to `lakefile.lean` or use `lake update`

**Issue**: Build timeout  
**Solution**: Increase timeout or build individual files with `lean PNP/SILB.lean`

## Python Setup

### Requirements

- Python 3.8 or higher
- pip package manager

### Installation

```bash
cd python_validation
pip install -r requirements.txt
```

### Running Tests

```bash
# Run empirical validation
python empirical_validation.py

# Run solver comparison (requires SAT solvers)
python solver_comparison.py
```

### Installing SAT Solvers (Optional)

**Ubuntu/Debian**:
```bash
sudo apt-get update
sudo apt-get install minisat
# For CryptoMiniSat, build from source
```

**macOS**:
```bash
brew install minisat
# For CryptoMiniSat
brew install cryptominisat
```

**From Source**:
```bash
# CryptoMiniSat
git clone https://github.com/msoos/cryptominisat.git
cd cryptominisat
mkdir build && cd build
cmake ..
make
sudo make install
```

## IDE Setup

### VS Code (Recommended)

1. **Install VS Code**: https://code.visualstudio.com/

2. **Install Lean 4 extension**:
   - Open VS Code
   - Go to Extensions (Ctrl+Shift+X)
   - Search for "lean4"
   - Install official "lean4" extension

3. **Open project**:
   ```bash
   code /path/to/P-NP
   ```

4. **Wait for indexing**: First time may take several minutes

### Emacs

1. **Install lean4-mode**:
   ```elisp
   (use-package lean4-mode
     :ensure t)
   ```

2. **Configure**:
   ```elisp
   (setq lean4-mode-server-command "lake serve")
   ```

### Neovim

1. **Install nvim-leanprover**:
   ```vim
   Plug 'Julian/lean.nvim'
   ```

2. **Configure LSP**: Follow lean.nvim documentation

## Verification Workflow

### 1. Edit Lean Files

Example: Edit `PNP/SILB.lean`

```lean
theorem separator_bound {n : Nat} (f : (Fin n) → Bool) (s : Separator) :
    (∑ i in s.nodes, Influence f i s) ≥ 0.5 * Variance f s := by
  sorry  -- Replace with actual proof
```

### 2. Check Proof

```bash
lake build PNP/SILB.lean
```

Or use editor integration (hover for errors, Ctrl+Shift+Enter to check)

### 3. Run Full Build

```bash
lake build
```

### 4. Run Main Executable

```bash
lake exe pnp
```

## Testing Changes

### Lean Tests (when implemented)

```bash
# Run all tests
lake test

# Run specific test
lean --run test/test_silb.lean
```

### Python Tests

```bash
cd python_validation

# Run with verbose output
python empirical_validation.py -v

# Test specific size
python -c "
from empirical_validation import *
results = run_empirical_validation(n_instances=10, var_sizes=[100])
print_validation_report(results)
"
```

## Continuous Integration

The project uses GitHub Actions for CI. See `.github/workflows/ci.yml`.

### Local CI Simulation

```bash
# Install act (GitHub Actions local runner)
# https://github.com/nektos/act

# Run CI locally
act -j build
```

### CI Pipeline

1. **Build**: Compiles all Lean files
2. **Lint**: Checks for `sorry` count
3. **Test**: Runs test suite (when implemented)

## Contributing

### Before Committing

1. **Build succeeds**: `lake build`
2. **Tests pass**: `lake test` (if applicable)
3. **Format code**: Use Lean formatter
4. **Update docs**: If adding new theorems/modules

### Commit Message Format

```
<type>: <subject>

<body>

<footer>
```

Types: `feat`, `fix`, `docs`, `refactor`, `test`, `chore`

Example:
```
feat: add treewidth preservation theorem

Implements tight_sat_reduction theorem in MainTheorem.lean.
Proves that SAT reduction preserves treewidth within constant factor.

Addresses GAP 1 requirement for tight reductions.
```

## Troubleshooting

### Lean Build Issues

**Symptom**: "lake: command not found"  
**Fix**: Ensure elan is installed and `~/.elan/bin` is in PATH

**Symptom**: "unknown identifier"  
**Fix**: Check imports, ensure dependencies are built

**Symptom**: "timeout"  
**Fix**: Build individual files, check for infinite loops

### Python Issues

**Symptom**: "ModuleNotFoundError: No module named 'numpy'"  
**Fix**: `pip install -r requirements.txt`

**Symptom**: "No SAT solvers detected"  
**Fix**: Install solvers or skip solver comparison tests

## Resources

### Lean 4
- [Lean Manual](https://leanprover.github.io/lean4/doc/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)

### Complexity Theory
- [Arora-Barak](http://theory.cs.princeton.edu/complexity/) - Computational Complexity textbook
- [Kushilevitz-Nisan](https://www.cambridge.org/core/books/communication-complexity/5F44993E3B2597174B71D3F21E748443) - Communication Complexity

### SAT Solving
- [Handbook of Satisfiability](https://www.iospress.nl/book/handbook-of-satisfiability-2/)
- [SAT Competition](http://satcompetition.org/)

## Getting Help

1. **GitHub Issues**: For bugs and feature requests
2. **Discussions**: For questions and ideas
3. **Lean Zulip**: https://leanprover.zulipchat.com/
