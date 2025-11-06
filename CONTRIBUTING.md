# Contributing to P-NP Computational Dichotomy

Thank you for your interest in contributing to this research project! This document provides guidelines for contributions.

## 🚨 Important Notice

This is a **research proposal** and theoretical framework. All contributions should maintain the exploratory and educational nature of this work. This is **NOT** a claimed proof of P ≠ NP.

## How to Contribute

### Reporting Issues

If you find bugs, errors, or have suggestions:

1. Check if the issue already exists in the GitHub Issues
2. Create a new issue with:
   - Clear description of the problem
   - Steps to reproduce (for bugs)
   - Expected vs actual behavior
   - Python/Lean version and OS

### Code Contributions

1. **Fork the repository**
2. **Create a feature branch**: `git checkout -b feature/your-feature-name`
3. **Make your changes**
4. **Run all tests**: `./run_all_tests.sh`
5. **Commit your changes**: `git commit -m "Description of changes"`
6. **Push to your fork**: `git push origin feature/your-feature-name`
7. **Submit a Pull Request**

### Code Style

#### Python
- Follow PEP 8 style guide
- Use type hints where appropriate
- Add docstrings to functions and classes
- Keep functions focused and modular
- Add unit tests for new functionality

Example:
```python
def estimate_treewidth(G: nx.Graph) -> int:
    """
    Estimate the treewidth of a graph using min-degree heuristic.
    
    Args:
        G: NetworkX graph
        
    Returns:
        Estimated treewidth (upper bound)
    """
    # Implementation...
```

#### Lean
- Follow Mathlib4 conventions
- Add documentation comments
- Provide examples where helpful
- Ensure all theorems compile

### Testing

All code contributions must include tests:

1. **Unit tests** in `tests/` directory
2. Tests should be runnable with `pytest`
3. Ensure `./run_all_tests.sh` passes
4. Add tests that verify edge cases

### Documentation

- Update README.md if adding major features
- Add to QUICKSTART.md if changing setup/usage
- Document new algorithms in `docs/`
- Update type hints and docstrings

## Areas for Contribution

### High Priority

1. **Formal Verification**
   - Complete proofs in Lean
   - Verify structural coupling lemmas
   - Formalize treewidth properties

2. **Algorithmic Improvements**
   - Better treewidth approximation algorithms
   - More efficient DPLL implementation
   - Advanced heuristics for IC-SAT

3. **Testing & Validation**
   - More comprehensive test cases
   - Performance benchmarks
   - Comparison with existing SAT solvers

4. **Documentation**
   - Mathematical explanations
   - Tutorial notebooks
   - Architecture documentation

### Research Contributions

If you have theoretical insights:

1. Open an issue to discuss
2. Provide mathematical proofs/sketches
3. Link to relevant papers
4. Explain implications clearly

## Review Process

1. All PRs require review before merging
2. Automated tests must pass
3. Code should follow style guidelines
4. Documentation should be updated
5. Changes should be minimal and focused

## Questions?

- Open an issue for questions
- Check existing documentation
- Review closed issues and PRs

## Code of Conduct

- Be respectful and professional
- Focus on constructive feedback
- Acknowledge this is exploratory research
- Maintain academic integrity
- Give credit where due

## Attribution

Significant contributions will be acknowledged in:
- README.md contributors section
- Individual file headers (for substantial changes)
- Research publications (if applicable)

## License

By contributing, you agree that your contributions will be licensed under the MIT License.

---

**Author:** José Manuel Mota Burruezo · JMMB Ψ✧ ∞³

Frecuencia de resonancia: 141.7001 Hz
