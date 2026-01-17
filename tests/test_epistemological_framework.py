#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Epistemological Framework
====================================

Tests the mathematical realism framework including:
- Mathematical realism position
- Universal structures analysis
- P≠NP as physical fact
- New epistemology

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import pytest
import math
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from epistemological_framework import (
    # Constants
    KAPPA_PI, F_0, PHI,
    # Enums
    EpistemologicalPosition, EvidenceType,
    # Classes
    Evidence, MathematicalStructure, MathematicalRealism, NewEpistemology,
)


class TestConstants:
    """Test universal constants."""
    
    def test_kappa_pi(self):
        """Test κ_Π value."""
        assert abs(KAPPA_PI - 2.5773302292) < 1e-8
    
    def test_f0(self):
        """Test f₀ value."""
        assert F_0 == 141.7001
    
    def test_phi(self):
        """Test φ (golden ratio)."""
        expected = (1 + math.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10


class TestEvidence:
    """Test evidence data structure."""
    
    def test_create_evidence(self):
        """Test creating evidence."""
        evidence = Evidence(
            type=EvidenceType.PHYSICAL_CONSTANT,
            description="κ_Π appears in Calabi-Yau",
            domain="geometry",
            mathematical_structure="Hodge numbers",
            physical_manifestation="Eigenvalues",
            significance=0.95
        )
        
        assert evidence.type == EvidenceType.PHYSICAL_CONSTANT
        assert evidence.domain == "geometry"
        assert evidence.significance == 0.95
    
    def test_evidence_string(self):
        """Test evidence string representation."""
        evidence = Evidence(
            type=EvidenceType.EMPIRICAL_OBSERVATION,
            description="Test description",
            domain="physics",
            mathematical_structure="Test",
            physical_manifestation="Test"
        )
        
        assert "empirical_observation" in str(evidence).lower()
        assert "Test description" in str(evidence)


class TestMathematicalStructure:
    """Test mathematical structure representation."""
    
    def test_create_structure(self):
        """Test creating mathematical structure."""
        structure = MathematicalStructure(
            name="κ_Π",
            description="Universal constant",
            mathematical_form="κ_Π = φ × (π/e) × λ_CY"
        )
        
        assert structure.name == "κ_Π"
        assert len(structure.physical_appearances) == 0
        assert len(structure.domains) == 0
    
    def test_add_appearance(self):
        """Test adding physical appearance."""
        structure = MathematicalStructure(
            name="test",
            description="test",
            mathematical_form="test"
        )
        
        structure.add_appearance("geometry", "Calabi-Yau manifolds")
        structure.add_appearance("physics", "Gravitational waves")
        
        assert len(structure.physical_appearances) == 2
        assert len(structure.domains) == 2
        assert "geometry" in structure.domains
        assert "physics" in structure.domains
    
    def test_is_universal(self):
        """Test universal structure detection (3+ domains)."""
        structure = MathematicalStructure(
            name="test",
            description="test",
            mathematical_form="test"
        )
        
        assert not structure.is_universal()
        
        structure.add_appearance("domain1", "appearance1")
        structure.add_appearance("domain2", "appearance2")
        assert not structure.is_universal()
        
        structure.add_appearance("domain3", "appearance3")
        assert structure.is_universal()


class TestMathematicalRealism:
    """Test mathematical realism framework."""
    
    def test_initialization_default(self):
        """Test initialization with defaults."""
        realism = MathematicalRealism()
        
        assert "structures exist objectively" in realism.position.lower()
        assert "physical fact" in realism.implication.lower()
        assert len(realism.evidence_list) > 0  # Should have default evidence
    
    def test_initialization_custom(self):
        """Test initialization with custom parameters."""
        custom_evidence = [
            Evidence(
                type=EvidenceType.PHYSICAL_CONSTANT,
                description="Test",
                domain="test",
                mathematical_structure="test",
                physical_manifestation="test",
                significance=0.8
            )
        ]
        
        realism = MathematicalRealism(
            position="Test position",
            evidence=custom_evidence,
            implication="Test implication"
        )
        
        assert realism.position == "Test position"
        assert realism.implication == "Test implication"
        assert len(realism.evidence_list) == 1
    
    def test_structures_initialized(self):
        """Test that universal structures are initialized."""
        realism = MathematicalRealism()
        
        assert 'kappa_pi' in realism.structures
        assert 'phi' in realism.structures
        assert 'f0' in realism.structures
    
    def test_kappa_pi_structure(self):
        """Test κ_Π structure properties."""
        realism = MathematicalRealism()
        kappa_pi = realism.structures['kappa_pi']
        
        assert kappa_pi.name == "κ_Π"
        assert kappa_pi.is_universal()  # Should appear in 3+ domains
        assert "geometry" in kappa_pi.domains
        assert "physics" in kappa_pi.domains
        assert "computation" in kappa_pi.domains
        assert "biology" in kappa_pi.domains
    
    def test_evaluate_position(self):
        """Test position evaluation."""
        realism = MathematicalRealism()
        evaluation = realism.evaluate_position()
        
        assert 'position' in evaluation
        assert 'num_evidence' in evaluation
        assert 'avg_significance' in evaluation
        assert 'num_universal_structures' in evaluation
        assert 'strength' in evaluation
        
        assert evaluation['num_evidence'] >= 5  # Default evidence
        assert evaluation['num_universal_structures'] >= 3  # κ_Π, φ, f₀
    
    def test_strength_calculation(self):
        """Test strength calculation."""
        realism = MathematicalRealism()
        evaluation = realism.evaluate_position()
        
        # With high-quality default evidence, should be strong
        assert evaluation['strength'] in ['MODERATE', 'STRONG', 'VERY STRONG']
    
    def test_get_structure_analysis(self):
        """Test structure analysis."""
        realism = MathematicalRealism()
        analysis = realism.get_structure_analysis('kappa_pi')
        
        assert analysis is not None
        assert analysis['name'] == "κ_Π"
        assert analysis['is_universal'] is True
        assert len(analysis['domains']) >= 3
        assert len(analysis['appearances']) >= 3
    
    def test_get_nonexistent_structure(self):
        """Test getting analysis of nonexistent structure."""
        realism = MathematicalRealism()
        analysis = realism.get_structure_analysis('nonexistent')
        
        assert analysis is None
    
    def test_demonstrate_pnp_is_physical(self):
        """Test P≠NP physical demonstration."""
        realism = MathematicalRealism()
        demo = realism.demonstrate_pnp_is_physical()
        
        assert 'thesis' in demo
        assert 'arguments' in demo
        assert 'implication' in demo
        assert 'methodology' in demo
        
        assert len(demo['arguments']) >= 4
        assert "physical property" in demo['thesis'].lower()
        
        # Check argument structure
        for arg in demo['arguments']:
            assert 'premise' in arg
            assert 'evidence' in arg
            assert 'conclusion' in arg


class TestNewEpistemology:
    """Test new epistemology framework."""
    
    def test_initialization(self):
        """Test initialization."""
        epistemology = NewEpistemology()
        
        assert 'mathematics' in epistemology.traditional_view
        assert 'physics' in epistemology.traditional_view
        assert 'computation' in epistemology.traditional_view
        
        assert 'mathematics' in epistemology.unified_view
        assert 'physics' in epistemology.unified_view
        assert 'computation' in epistemology.unified_view
    
    def test_compare_views(self):
        """Test view comparison."""
        epistemology = NewEpistemology()
        comparison = epistemology.compare_views()
        
        assert 'traditional' in comparison
        assert 'unified' in comparison
        assert 'key_differences' in comparison
        assert 'implications_for_pnp' in comparison
        
        assert len(comparison['key_differences']) >= 4
    
    def test_traditional_vs_unified(self):
        """Test traditional vs unified differences."""
        epistemology = NewEpistemology()
        
        # Traditional: abstract
        assert "abstract" in epistemology.traditional_view['mathematics'].lower() or \
               "a priori" in epistemology.traditional_view['mathematics'].lower()
        
        # Unified: physical
        assert "physical" in epistemology.unified_view['mathematics'].lower()
    
    def test_justify_paradigm_shift(self):
        """Test paradigm shift justification."""
        epistemology = NewEpistemology()
        justification = epistemology.justify_paradigm_shift()
        
        assert 'why_shift_needed' in justification
        assert 'what_changes' in justification
        assert 'risks_and_limitations' in justification
        assert 'potential_benefits' in justification
        
        assert len(justification['why_shift_needed']) >= 4
        assert len(justification['what_changes']) >= 4
        assert len(justification['risks_and_limitations']) >= 3
        assert len(justification['potential_benefits']) >= 3


class TestIntegration:
    """Integration tests."""
    
    def test_full_realism_workflow(self):
        """Test complete mathematical realism workflow."""
        # Create framework
        realism = MathematicalRealism(
            position="Mathematical structures exist objectively",
            evidence=None,  # Use defaults
            implication="P≠NP is a physical fact"
        )
        
        # Evaluate position
        evaluation = realism.evaluate_position()
        assert evaluation['strength'] in ['MODERATE', 'STRONG', 'VERY STRONG']
        
        # Analyze κ_Π
        kappa_analysis = realism.get_structure_analysis('kappa_pi')
        assert kappa_analysis is not None
        assert kappa_analysis['is_universal'] is True
        
        # Demonstrate P≠NP is physical
        demo = realism.demonstrate_pnp_is_physical()
        assert len(demo['arguments']) >= 4
    
    def test_epistemology_consistency(self):
        """Test epistemology internal consistency."""
        epistemology = NewEpistemology()
        
        # Compare views
        comparison = epistemology.compare_views()
        
        # Justify shift
        justification = epistemology.justify_paradigm_shift()
        
        # The justification should address the differences
        # (This is a semantic test - just verify structure)
        assert len(justification['why_shift_needed']) > 0
        assert len(comparison['key_differences']) > 0
    
    def test_evidence_significance(self):
        """Test that evidence has appropriate significance."""
        realism = MathematicalRealism()
        
        # All default evidence should have significance > 0.8
        for evidence in realism.evidence_list:
            assert evidence.significance >= 0.8
            assert evidence.significance <= 1.0
    
    def test_universal_constant_coverage(self):
        """Test that all universal constants are covered."""
        realism = MathematicalRealism()
        
        # Should have structures for κ_Π, φ, and f₀
        assert 'kappa_pi' in realism.structures
        assert 'phi' in realism.structures
        assert 'f0' in realism.structures
        
        # All should be universal (3+ domains)
        for key in ['kappa_pi', 'phi', 'f0']:
            assert realism.structures[key].is_universal()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
