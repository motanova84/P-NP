#!/usr/bin/env python3
"""
Unit tests for structural projection verification.

This test module validates the structural projection operator
properties defined in Boolean CFT.

Run: python3 -m pytest test_structural_projection.py -v
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from verify_structural_projection import (
    CNFClause, CNFFormula, SatisfiabilityProjector,
    KAPPA_PI, F_0, PHI
)
import numpy as np


def test_kappa_pi_constant():
    """Test that κ_Π constant is correctly defined"""
    assert abs(KAPPA_PI - 2.5773) < 1e-4


def test_f0_constant():
    """Test that f₀ constant is correctly defined"""
    assert abs(F_0 - 141.7001) < 1e-4


def test_phi_constant():
    """Test that golden ratio is correctly defined"""
    expected_phi = (1 + np.sqrt(5)) / 2
    assert abs(PHI - expected_phi) < 1e-10


def test_cnf_clause_satisfaction():
    """Test CNF clause satisfaction logic"""
    clause = CNFClause([(0, True), (1, False)])  # x₀ ∨ ¬x₁
    
    # Test cases: (x₀, x₁) -> satisfies?
    assert clause.is_satisfied([True, True]) == True   # T ∨ F = T
    assert clause.is_satisfied([True, False]) == True  # T ∨ T = T
    assert clause.is_satisfied([False, True]) == False # F ∨ F = F
    assert clause.is_satisfied([False, False]) == True # F ∨ T = T


def test_cnf_formula_satisfaction():
    """Test CNF formula satisfaction"""
    # (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂)
    formula = CNFFormula(
        n_vars=3,
        clauses=[
            CNFClause([(0, True), (1, True)]),
            CNFClause([(0, False), (2, True)])
        ]
    )
    
    # Test satisfying assignment: x₀=F, x₁=T, x₂=T
    assert formula.is_satisfied([False, True, True]) == True
    
    # Test non-satisfying assignment: x₀=F, x₁=F, x₂=F
    assert formula.is_satisfied([False, False, False]) == False


def test_projection_hermitian():
    """Test that projection operator is Hermitian (P† = P)"""
    formula = CNFFormula(
        n_vars=3,
        clauses=[CNFClause([(0, True), (1, True)])]
    )
    projector = SatisfiabilityProjector(formula)
    
    is_hermitian, error = projector.verify_hermitian()
    assert is_hermitian, f"Projection not Hermitian, error: {error}"
    assert error < 1e-10


def test_projection_idempotent():
    """Test that projection operator is idempotent (P² = P)"""
    formula = CNFFormula(
        n_vars=3,
        clauses=[CNFClause([(0, True), (1, True)])]
    )
    projector = SatisfiabilityProjector(formula)
    
    is_idempotent, error = projector.verify_idempotent()
    assert is_idempotent, f"Projection not idempotent, error: {error}"
    assert error < 1e-10


def test_projection_eigenvalues():
    """Test that projection eigenvalues are in {0, 1}"""
    formula = CNFFormula(
        n_vars=3,
        clauses=[CNFClause([(0, True), (1, True)])]
    )
    projector = SatisfiabilityProjector(formula)
    
    valid, eigenvalues = projector.verify_eigenvalues()
    assert valid, "Projection eigenvalues not in {0, 1}"
    
    # Check all eigenvalues are close to 0 or 1
    for ev in eigenvalues:
        assert abs(ev) < 1e-9 or abs(ev - 1) < 1e-9


def test_projection_normalization():
    """Test that projection preserves normalization"""
    formula = CNFFormula(
        n_vars=3,
        clauses=[CNFClause([(0, True), (1, True)])]
    )
    projector = SatisfiabilityProjector(formula)
    
    preserves, ratio = projector.verify_normalization_preservation()
    assert preserves, f"Projection doesn't preserve norm, ratio: {ratio}"
    assert 0 <= ratio <= 1 + 1e-10


def test_tautology_projection():
    """Test projection for a tautology (identity operator)"""
    # x₀ ∨ ¬x₀ is always true
    formula = CNFFormula(
        n_vars=2,
        clauses=[CNFClause([(0, True), (0, False)])]
    )
    projector = SatisfiabilityProjector(formula)
    
    # For tautology, rank should equal dimension (identity)
    rank = projector.get_projection_rank()
    assert rank == projector.dimension, "Tautology should be identity"
    
    # Dimension factor should be 1.0
    dim_factor = projector.get_projection_dimension_factor()
    assert abs(dim_factor - 1.0) < 1e-10


def test_contradiction_projection():
    """Test projection for a contradiction (zero operator)"""
    # x₀ ∧ ¬x₀ is always false
    formula = CNFFormula(
        n_vars=2,
        clauses=[
            CNFClause([(0, True)]),
            CNFClause([(0, False)])
        ]
    )
    projector = SatisfiabilityProjector(formula)
    
    # For contradiction, rank should be 0 (zero operator)
    rank = projector.get_projection_rank()
    assert rank == 0, "Contradiction should have rank 0"
    
    # Dimension factor should be 0.0
    dim_factor = projector.get_projection_dimension_factor()
    assert abs(dim_factor) < 1e-10


def test_satisfying_configs():
    """Test that satisfying configurations are correctly identified"""
    # Simple formula: x₀ ∨ x₁
    formula = CNFFormula(
        n_vars=2,
        clauses=[CNFClause([(0, True), (1, True)])]
    )
    
    sat_configs = formula.satisfying_configs()
    
    # Should have 3 satisfying configs: (T,T), (T,F), (F,T)
    assert len(sat_configs) == 3
    
    # Check specific configs
    assert [True, True] in sat_configs
    assert [True, False] in sat_configs
    assert [False, True] in sat_configs
    assert [False, False] not in sat_configs


def test_projection_rank_matches_satisfying_configs():
    """Test that projection rank equals number of satisfying configs"""
    formula = CNFFormula(
        n_vars=3,
        clauses=[CNFClause([(0, True), (1, True)])]
    )
    
    projector = SatisfiabilityProjector(formula)
    sat_configs = formula.satisfying_configs()
    
    # Rank should equal number of satisfying configurations
    assert projector.get_projection_rank() == len(sat_configs)


def test_central_charge_relation():
    """Test that central charge formula is consistent"""
    # c = 1 - 6/κ_Π²
    c = 1 - 6 / (KAPPA_PI ** 2)
    
    # Should be approximately 0.097 (more accurate value)
    assert abs(c - 0.0967) < 0.001


if __name__ == "__main__":
    # Run tests if executed directly
    import pytest
    pytest.main([__file__, "-v"])
