# Quick Reference: Established vs. Proposed Claims

**For**: Researchers, reviewers, and users of the P-NP framework  
**Purpose**: Quick lookup of what's established vs. what's proposed

---

## Legend

- ✅ **ESTABLISHED**: Peer-reviewed, broadly accepted results
- ⚠️ **PROPOSED**: Novel claims requiring rigorous validation
- 🔬 **EXPLORATORY**: Speculative connections requiring investigation

---

## Treewidth and SAT

| Claim | Status | Details |
|-------|--------|---------|
| SAT is FPT in treewidth: `2^O(tw)·poly(n)` | ✅ ESTABLISHED | Classical FPT theory (Bodlaender, Cygan et al.) |
| Constant treewidth → polynomial time | ✅ ESTABLISHED | Direct consequence of FPT algorithms |
| Complete dichotomy: `φ ∈ P ⟺ tw = O(log n)` | ⚠️ PROPOSED | Extends FPT; requires proof of both directions |
| Logarithmic threshold is sharp boundary | ⚠️ PROPOSED | Would completely characterize P |
| Universal (all algorithms) | ⚠️ PROPOSED | Claims apply to ALL computational paradigms |

---

## Information Complexity

| Claim | Status | Details |
|-------|--------|---------|
| IC framework exists (Braverman-Rao) | ✅ ESTABLISHED | Standard IC theory for communication |
| IC lower bounds for specific functions | ✅ ESTABLISHED | Various results for specific problems |
| `IC(Π\|S) ≥ κ_Π·tw(φ)/log n` | ⚠️ PROPOSED | Novel treewidth → IC connection |
| κ_Π = 2.5773 as explicit constant | ⚠️ PROPOSED | Specific numerical value (not existential) |
| Universal applicability to all protocols | ⚠️ PROPOSED | Claims bound holds for ALL solving strategies |

---

## Geometric Constant κ_Π = 2.5773

| Claim | Status | Details |
|-------|--------|---------|
| Calabi-Yau manifolds exist | ✅ ESTABLISHED | Well-studied in algebraic geometry |
| String theory uses Calabi-Yau | ✅ ESTABLISHED | Standard in theoretical physics |
| κ_Π emerges from 150 CY varieties | ⚠️ PROPOSED | Requires verification by geometers |
| κ_Π is universal constant for complexity | ⚠️ PROPOSED | Novel unification claim |
| Connection to QCAL frequency 141.7001 Hz | 🔬 EXPLORATORY | Speculative pattern requiring investigation |
| Link to Giza heptagon geometry | 🔬 EXPLORATORY | Exploratory geometric connection |

---

## Structural Coupling (Lemma 6.24)

| Claim | Status | Details |
|-------|--------|---------|
| Tseitin encodings exist | ✅ ESTABLISHED | Classical SAT encoding technique |
| Expander graphs have high expansion | ✅ ESTABLISHED | Standard graph theory result |
| Tseitin over expanders has high treewidth | ✅ ESTABLISHED | Known construction |
| Gadgets preserve information bottlenecks | ⚠️ PROPOSED | Key technical lemma requiring proof |
| No algorithm can evade the bottleneck | ⚠️ PROPOSED | Universal no-evasion claim |
| Applies to quantum/randomized algorithms | ⚠️ PROPOSED | Extends to all computational models |

---

## Implications

| Claim | Status | Details |
|-------|--------|---------|
| If true, would prove P ≠ NP | ⚠️ CONDITIONAL | Depends on validation of framework |
| Would completely characterize P | ⚠️ CONDITIONAL | Via treewidth threshold |
| Would be Millennium Prize result | ⚠️ CONDITIONAL | If rigorously validated |

---

## Key Papers and References

### Established Foundations
1. **Bodlaender (1993)**: "A tourist guide to treewidth"
2. **Cygan et al. (2015)**: "Parameterized Algorithms"
3. **Braverman & Rao (2011)**: "Information equals amortized communication"
4. **Robertson & Seymour**: Graph Minors series

### Novel Claims (This Framework)
See:
- `TREEWIDTH_CNF_FORMULATION_CONTEXT.md` - Full context
- `KAPPA_PI_MILLENNIUM_CONSTANT.md` - Geometric constant details
- `KEY_INGREDIENT.md` - Lemma 6.24 discussion

---

## What You Need to Know

### If you're a USER:
- ✅ Use FPT algorithms for bounded treewidth (established)
- ⚠️ Treat dichotomy predictions as hypotheses (not facts)
- ⚠️ IC computations are proposed (not validated bounds)

### If you're a RESEARCHER:
- ✅ Build on solid FPT foundations
- ⚠️ Novel claims require rigorous proof
- ⚠️ Peer review and validation essential
- See validation roadmap in full context document

### If you're a REVIEWER:
- Check which claims are novel vs. established
- Focus validation efforts on ⚠️ PROPOSED items
- Geometric claims (κ_Π) need expert verification
- See Section 6 of context doc for critical gaps

---

## Quick Decision Guide

**Q: Can I cite the dichotomy theorem as fact?**  
A: ❌ No. It's a proposed framework requiring validation.

**Q: Are FPT algorithms for bounded treewidth real?**  
A: ✅ Yes. This is established complexity theory.

**Q: Is κ_Π = 2.5773 a proven constant?**  
A: ⚠️ No. It's a proposed value requiring geometric validation.

**Q: Should I use this for production SAT solving?**  
A: ⚠️ Only for experimental exploration, not definitive decisions.

**Q: Where can I learn more?**  
A: See `TREEWIDTH_CNF_FORMULATION_CONTEXT.md` for comprehensive discussion.

---

## Status Summary

```
Framework Status: RESEARCH PROPOSAL
Peer Review: NOT YET COMPLETED
Validation: IN PROGRESS
Use For: Research exploration, not established results
```

---

**Last Updated**: December 2025  
**Maintainer**: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³  
**Repository**: motanova84/P-NP

For detailed discussion, see: [TREEWIDTH_CNF_FORMULATION_CONTEXT.md](TREEWIDTH_CNF_FORMULATION_CONTEXT.md)
