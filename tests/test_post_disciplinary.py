"""
Tests for post-disciplinary science framework
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

import pytest
from post_disciplinary import (
    PostDisciplinaryScience,
    PNeqNPUnifiedApproach,
    UnifiedReality,
    Aspect,
    Domain,
    Tool
)


class TestPostDisciplinaryScience:
    """Tests for PostDisciplinaryScience class"""
    
    def test_initialization(self):
        """Test that framework initializes correctly"""
        science = PostDisciplinaryScience()
        
        assert 'κ_Π' in science.concept_network
        assert 'complexity' in science.concept_network
        assert 'structure' in science.concept_network
        assert len(science.available_tools) > 0
    
    def test_concept_network_structure(self):
        """Test concept network has proper structure"""
        science = PostDisciplinaryScience()
        kappa_concepts = science.concept_network['κ_Π']
        
        # Should have multiple domains
        assert 'mathematical' in kappa_concepts
        assert 'geometric' in kappa_concepts
        assert 'physical' in kappa_concepts
        assert 'biological' in kappa_concepts
        assert 'computational' in kappa_concepts
    
    def test_get_tools_from_all_fields(self):
        """Test getting tools based on aspect requirements"""
        science = PostDisciplinaryScience()
        
        # Aspect needing precision
        aspect = Aspect("Test", [Domain.MATHEMATICAL], 
                       needs_precision=True)
        tools = science.get_tools_from_all_fields(aspect)
        
        # Should get tools that match criteria
        assert len(tools) > 0
        assert any(tool.name == "FormalProof" for tool in tools)
    
    def test_solve_problem(self):
        """Test problem solving integrates multiple domains"""
        science = PostDisciplinaryScience()
        
        aspects = [
            Aspect("Logical", [Domain.MATHEMATICAL], 
                   needs_precision=True),
            Aspect("Physical", [Domain.PHYSICAL], 
                   needs_measurement=True)
        ]
        
        solution = science.solve_problem("Test Problem", aspects)
        
        # Should integrate multiple domains
        assert solution['problem'] == "Test Problem"
        assert solution['domains_integrated'] >= 2
        assert 'tools_used' in solution
        assert 'verification_methods' in solution


class TestPNeqNPUnifiedApproach:
    """Tests for unified approach to P≠NP"""
    
    def test_initialization(self):
        """Test initialization with correct constants"""
        unified = PNeqNPUnifiedApproach()
        
        assert unified.kappa_pi == 2.5773
        assert unified.f0 == 141.7001
    
    def test_demonstrate_integration(self):
        """Test integration demonstration includes all domains"""
        unified = PNeqNPUnifiedApproach()
        integration = unified.demonstrate_integration()
        
        # Should have all key domains
        assert 'mathematics' in integration
        assert 'geometry' in integration
        assert 'physics' in integration
        assert 'biology' in integration
        assert 'computation' in integration
        assert 'philosophy' in integration
        
        # Each should have required fields
        for domain_data in integration.values():
            assert 'tools' in domain_data
            assert 'contribution' in domain_data
            assert 'novel' in domain_data
            assert 'status' in domain_data
    
    def test_show_emergence(self):
        """Test emergence demonstration"""
        unified = PNeqNPUnifiedApproach()
        emergence = unified.show_emergence()
        
        assert 'individual_insights' in emergence
        assert 'emergent_insight' in emergence
        assert len(emergence['individual_insights']) > 0
        assert 'κ_Π' in emergence['emergent_insight']
    
    def test_verify_predictions(self):
        """Test predictions are verifiable"""
        unified = PNeqNPUnifiedApproach()
        predictions = unified.verify_predictions()
        
        # Should have predictions for multiple domains
        assert 'mathematical' in predictions
        assert 'physical' in predictions
        assert 'computational' in predictions
        assert 'biological' in predictions
        
        # Each prediction should be verifiable
        for pred in predictions.values():
            assert pred['verifiable'] is True
            assert 'timeline' in pred
    
    def test_solve_p_vs_np_post_disciplinarily(self):
        """Test complete post-disciplinary solution"""
        unified = PNeqNPUnifiedApproach()
        solution = unified.solve_p_vs_np_post_disciplinarily()
        
        # Should have all steps
        assert 'step1_aspects' in solution
        assert 'step2_tools' in solution
        assert 'step3_synthesis' in solution
        assert 'step4_verification' in solution
        assert 'conclusion' in solution
        
        # Should mention κ_Π
        assert 'κ_Π' in solution['step3_synthesis']


class TestUnifiedReality:
    """Tests for unified reality concept"""
    
    def test_initialization(self):
        """Test initialization with multiple description methods"""
        reality = UnifiedReality()
        
        assert 'mathematical' in reality.descriptions
        assert 'physical' in reality.descriptions
        assert 'computational' in reality.descriptions
        assert 'biological' in reality.descriptions
    
    def test_describe_kappa_pi(self):
        """Test describing κ_Π from different perspectives"""
        reality = UnifiedReality()
        
        math_desc = reality.describe_mathematically('kappa_pi')
        phys_desc = reality.describe_physically('kappa_pi')
        comp_desc = reality.describe_computationally('kappa_pi')
        bio_desc = reality.describe_biologically('kappa_pi')
        
        # All descriptions should be non-empty strings
        assert isinstance(math_desc, str) and len(math_desc) > 0
        assert isinstance(phys_desc, str) and len(phys_desc) > 0
        assert isinstance(comp_desc, str) and len(comp_desc) > 0
        assert isinstance(bio_desc, str) and len(bio_desc) > 0
        
        # But all point to same reality
        assert reality.are_same(math_desc, phys_desc)
    
    def test_get_all_descriptions(self):
        """Test getting all descriptions at once"""
        reality = UnifiedReality()
        descriptions = reality.get_all_descriptions('kappa_pi')
        
        assert len(descriptions) == 4
        assert 'mathematical' in descriptions
        assert 'physical' in descriptions
        assert 'computational' in descriptions
        assert 'biological' in descriptions


class TestAspect:
    """Tests for Aspect dataclass"""
    
    def test_aspect_creation(self):
        """Test creating an aspect with various properties"""
        aspect = Aspect(
            "Test Aspect",
            [Domain.MATHEMATICAL, Domain.PHYSICAL],
            needs_precision=True,
            needs_measurement=True,
            involves_consciousness=True
        )
        
        assert aspect.name == "Test Aspect"
        assert Domain.MATHEMATICAL in aspect.domains
        assert Domain.PHYSICAL in aspect.domains
        assert aspect.needs_precision is True
        assert aspect.needs_measurement is True
        assert aspect.involves_consciousness is True


class TestTool:
    """Tests for Tool dataclass"""
    
    def test_tool_creation(self):
        """Test creating a tool"""
        tool = Tool(
            "TestTool",
            Domain.MATHEMATICAL,
            "A test tool"
        )
        
        assert tool.name == "TestTool"
        assert tool.domain == Domain.MATHEMATICAL
        assert tool.description == "A test tool"
    
    def test_tool_applicability(self):
        """Test tool applicability function"""
        tool = Tool(
            "PrecisionTool",
            Domain.MATHEMATICAL,
            "For precise work",
            lambda aspect: aspect.needs_precision
        )
        
        aspect_needing_precision = Aspect(
            "Test", [Domain.MATHEMATICAL], needs_precision=True
        )
        aspect_not_needing = Aspect(
            "Test2", [Domain.MATHEMATICAL], needs_precision=False
        )
        
        assert tool.applicable_to(aspect_needing_precision)
        assert not tool.applicable_to(aspect_not_needing)


def test_demonstrate_post_disciplinary_approach():
    """Test the main demonstration function runs without error"""
    from post_disciplinary import demonstrate_post_disciplinary_approach
    
    # Should run and return tuple of objects
    result = demonstrate_post_disciplinary_approach()
    
    assert isinstance(result, tuple)
    assert len(result) == 3


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
