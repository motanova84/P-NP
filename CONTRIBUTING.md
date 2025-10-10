# Contributing to P-NP Framework

Thank you for your interest in contributing to this formal verification project!

## Ways to Contribute

### 1. Proof Completion
Replace `sorry` placeholders with actual proofs. Priority areas:
- `SILB.lean`: Separator bounds and influence analysis
- `ExpanderTools.lean`: Expander graph properties
- `MainTheorem.lean`: Universal compression barrier

### 2. Bound Improvement
Help improve the constant α from 0.006 to Ω(1):
- Better separator analysis
- Alternative gadget constructions
- Fourier-based techniques

### 3. Empirical Validation
Expand test coverage:
- More SAT instance types
- Additional solver integrations
- Statistical analysis improvements

### 4. Documentation
- Explain proof techniques
- Add examples and tutorials
- Improve API documentation

## Getting Started

1. **Fork the repository**
2. **Set up development environment** (see docs/SETUP.md)
3. **Pick an issue** from GitHub Issues or create a new one
4. **Make your changes**
5. **Submit a pull request**

## Development Guidelines

### Lean Code Style

- Use meaningful variable names
- Add documentation comments for public definitions
- Follow Mathlib style conventions
- Run `lake build` before committing

Example:
```lean
/-- 
  Separator in a communication protocol.
  
  A separator is a cut-set in the protocol tree that partitions
  the computation between Alice and Bob's inputs.
-/
structure Separator where
  nodes : Set Nat
  size : Nat
  deriving DecidableEq
```

### Python Code Style

- Follow PEP 8
- Add type hints
- Include docstrings for all functions
- Use meaningful variable names

Example:
```python
def estimate_treewidth(instance: SATInstance) -> TreewidthMetrics:
    """
    Estimate treewidth using min-degree heuristic.
    
    Args:
        instance: SAT instance in CNF format
    
    Returns:
        TreewidthMetrics with estimated treewidth and timing
    """
```

### Documentation Style

- Use Markdown for all documentation
- Include code examples
- Add references to papers/resources
- Keep examples up-to-date

## Pull Request Process

1. **Create a branch** with descriptive name: `feature/improve-silb-bounds`
2. **Make focused changes**: One logical change per PR
3. **Write tests** if applicable
4. **Update documentation**: Especially if adding new features
5. **Build successfully**: Ensure `lake build` passes
6. **Submit PR** with clear description

### PR Template

```markdown
## Description
Brief description of changes

## Motivation
Why is this change needed?

## Changes Made
- [ ] Added theorem X to SILB.lean
- [ ] Updated documentation
- [ ] Added tests

## Testing
How were changes tested?

## Related Issues
Fixes #123
```

## Code Review Process

1. Maintainer reviews within 1 week
2. Address feedback promptly
3. CI must pass (Lean builds, Python tests)
4. At least one approval required
5. Merge when ready

## Reporting Issues

### Bug Reports

Include:
- What you expected
- What actually happened
- Steps to reproduce
- Environment (OS, Lean version, etc.)

### Feature Requests

Include:
- Use case / motivation
- Proposed solution (if any)
- Alternatives considered

### Proof Gaps

Include:
- Which theorem
- Why `sorry` is challenging
- Attempted approaches
- References that might help

## Community Guidelines

### Be Respectful
- Treat everyone with respect
- Assume good intentions
- Provide constructive feedback

### Be Collaborative
- Share knowledge
- Help newcomers
- Credit others' work

### Be Patient
- Formal verification is hard
- Proofs take time
- Reviews may be delayed

## Recognition

Contributors are credited in:
- Git commit history
- CONTRIBUTORS.md file
- Paper acknowledgments (if published)

## Questions?

- **GitHub Issues**: For bugs and features
- **GitHub Discussions**: For questions and ideas
- **Lean Zulip**: For Lean-specific questions

## License

By contributing, you agree that your contributions will be licensed under the MIT License.

## Thank You!

Your contributions help advance our understanding of computational complexity!
