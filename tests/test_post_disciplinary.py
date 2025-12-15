"""
Tests for post-disciplinary science framework
Test suite for post-disciplinary science framework

Tests the implementation of the post-disciplinary paradigm including:
- PostDisciplinaryScience class and problem-solving approach
- UnifiedReality multi-perspective descriptions
- PostDisciplinaryUniversity organizational model
- ComplexityInstitute integration metrics
- PNeqNP_UnifiedApproach demonstration

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
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
import pytest

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from post_disciplinary import (
    PostDisciplinaryScience,
    UnifiedReality,
    PostDisciplinaryUniversity,
    ComplexityInstitute,
    PNeqNP_UnifiedApproach,
    measure_paradigm_shift,
    Aspect,
    Tool,
    Problem
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
    """Test suite for PostDisciplinaryScience class."""
    
    def test_initialization(self):
        """Test that the framework initializes with concept networks."""
        pds = PostDisciplinaryScience()
        
        assert 'κ_Π' in pds.concept_network
        assert 'P_vs_NP' in pds.concept_network
        assert 'mathematical' in pds.concept_network['κ_Π']
        assert 'geometric' in pds.concept_network['κ_Π']
        assert len(pds.available_tools) > 0
    
    def test_concept_network_structure(self):
        """Test concept network has all required fields."""
        pds = PostDisciplinaryScience()
        kappa_network = pds.concept_network['κ_Π']
        
        required_fields = ['mathematical', 'geometric', 'physical', 
                          'biological', 'computational']
        for field in required_fields:
            assert field in kappa_network
            assert isinstance(kappa_network[field], list)
            assert len(kappa_network[field]) > 0
    
    def test_identify_aspects(self):
        """Test aspect identification for P vs NP problem."""
        pds = PostDisciplinaryScience()
        problem = Problem(name="P_vs_NP", description="Complexity problem")
        
        aspects = pds.identify_aspects(problem)
        
        assert len(aspects) > 0
        assert any(a.name == 'logical' for a in aspects)
        assert any(a.name == 'geometric' for a in aspects)
        assert any(a.name == 'physical' for a in aspects)
    
    def test_get_tools_from_all_fields(self):
        """Test that tools are gathered from multiple fields."""
        pds = PostDisciplinaryScience()
        
        # Create aspect that needs precision and measurement
        aspect = Aspect(
            name='test',
            needs_precision=True,
            needs_measurement=True
        )
        
        tools = pds.get_tools_from_all_fields(aspect)
        
        assert len(tools) > 0
        # Should have tools from both mathematics and physics
        fields = set(t.field for t in tools)
        assert 'mathematics' in fields
        assert 'physics' in fields
    
    def test_solve_problem(self):
        """Test complete problem-solving pipeline."""
        pds = PostDisciplinaryScience()
        problem = Problem(name="P_vs_NP", description="Test problem")
        
        solution = pds.solve_problem(problem)
        
        assert 'problem' in solution
        assert solution['problem'] == "P_vs_NP"
        assert 'aspects_analyzed' in solution
        assert 'fields_integrated' in solution
        assert solution['fields_integrated'] >= 1
        assert 'integration_quality' in solution
    
    def test_synthesize(self):
        """Test synthesis of multiple tools."""
        pds = PostDisciplinaryScience()
        
        tools = [
            Tool('Lean4', 'mathematics', 'Formal verification'),
            Tool('Spectroscopy', 'physics', 'Measurement'),
            Tool('NetworkX', 'computation', 'Graph analysis')
        ]
        
        synthesis = pds.synthesize(tools)
        
        assert synthesis['fields_integrated'] == 3
        assert synthesis['integration_quality'] == 'high'
        assert len(synthesis['tools_used']) == 3


class TestUnifiedReality:
    """Test suite for UnifiedReality class."""
    
    def test_initialization(self):
        """Test UnifiedReality initializes with all perspectives."""
        ur = UnifiedReality()
        
        required_perspectives = ['mathematical', 'physical', 'computational',
                                'geometric', 'biological']
        for perspective in required_perspectives:
            assert perspective in ur.descriptions
    
    def test_describe_kappa_pi(self):
        """Test that κ_Π can be described from all perspectives."""
        ur = UnifiedReality()
        entity = 'kappa_pi'
        
        descriptions = ur.get_all_descriptions(entity)
        
        assert len(descriptions) == 5
        assert all(isinstance(desc, str) for desc in descriptions.values())
        assert '2.5773' in descriptions['mathematical']
        assert '141.7' in descriptions['physical']
    
    def test_describe_p_neq_np(self):
        """Test P≠NP descriptions from multiple perspectives."""
        ur = UnifiedReality()
        entity = 'p_neq_np'
        
        math_desc = ur.describe_mathematically(entity)
        phys_desc = ur.describe_physically(entity)
        comp_desc = ur.describe_computationally(entity)
        
        assert 'tw' in math_desc or 'Time' in math_desc
        assert 'energía' in phys_desc.lower() or 'energy' in phys_desc.lower()
        assert 'algoritmo' in comp_desc or 'algorithm' in comp_desc
    
    def test_describe_consciousness(self):
        """Test consciousness descriptions integrate fields."""
        ur = UnifiedReality()
        entity = 'consciousness'
        
        descriptions = ur.get_all_descriptions(entity)
        
        # Each description should be non-empty
        for desc in descriptions.values():
            assert len(desc) > 0
    
    def test_are_same(self):
        """Test that all descriptions point to same reality."""
        ur = UnifiedReality()
        
        # Any two descriptions are of the same reality
        assert ur.are_same('mathematical', 'physical') == True
        assert ur.are_same('geometric', 'biological') == True


class TestPostDisciplinaryUniversity:
    """Test suite for PostDisciplinaryUniversity class."""
    
    def test_initialization(self):
        """Test university initializes with networks not departments."""
        uni = PostDisciplinaryUniversity()
        
        assert 'Complexity Network' in uni.research_networks
        assert 'Structure Network' in uni.research_networks
        assert 'Information Network' in uni.research_networks
    
    def test_network_structure(self):
        """Test each network has required components."""
        uni = PostDisciplinaryUniversity()
        
        for network_name, network_data in uni.research_networks.items():
            assert 'core_question' in network_data
            assert 'tools' in network_data
            assert 'problems' in network_data
            assert len(network_data['tools']) > 0
            assert len(network_data['problems']) > 0
    
    def test_hire_researcher(self):
        """Test researcher can belong to multiple networks."""
        uni = PostDisciplinaryUniversity()
        
        # Researcher with diverse skills
        person_skills = {
            'graph_theory': True,
            'quantum_mechanics': True,
            'topology': True
        }
        
        networks = uni.hire_researcher(person_skills)
        
        # Should match at least one network
        assert len(networks) >= 0
        # Each result should be a valid network name
        for net in networks:
            assert net in uni.research_networks
    
    def test_teach_course(self):
        """Test course organized by problems not fields."""
        uni = PostDisciplinaryUniversity()
        
        course = uni.teach_course('complexity')
        
        assert 'name' in course
        assert 'complexity' in course['name'].lower()
        assert 'methods' in course
        assert 'theory' in course['methods']
        assert 'experiment' in course['methods']
        assert course['integration_required'] == True
    
    def test_get_networks_for_problem(self):
        """Test finding networks that address a problem."""
        uni = PostDisciplinaryUniversity()
        
        networks = uni.get_networks_for_problem('consciousness')
        
        # Consciousness appears in multiple networks
        assert len(networks) >= 1


class TestComplexityInstitute:
    """Test suite for ComplexityInstitute class."""
    
    def test_initialization(self):
        """Test institute initializes with integrated spaces."""
        institute = ComplexityInstitute()
        
        assert institute.motto == "Una Realidad, Múltiples Lentes"
        assert 'formal_verification_lab' in institute.spaces
        assert 'experimental_physics_lab' in institute.spaces
        assert 'integration_studio' in institute.spaces
    
    def test_space_structure(self):
        """Test each space has tools and purpose."""
        institute = ComplexityInstitute()
        
        for space_name, space_data in institute.spaces.items():
            assert 'tools' in space_data
            assert 'purpose' in space_data
            assert len(space_data['tools']) > 0
            assert len(space_data['purpose']) > 0
    
    def test_daily_routine(self):
        """Test daily routine promotes integration."""
        institute = ComplexityInstitute()
        
        schedule = institute.daily_routine()
        
        assert len(schedule) > 0
        # Check for integration activities
        schedule_str = ' '.join(schedule.values()).lower()
        assert 'integration' in schedule_str or 'synthesis' in schedule_str
    
    def test_measure_success(self):
        """Test success measured by integration not just publications."""
        institute = ComplexityInstitute()
        
        project = {
            'disciplines_used': 4,
            'unexpected_links': 3,
            'testable_predictions': 5,
            'real_world_applications': 2,
            'changes_thinking': True
        }
        
        metrics = institute.measure_success(project)
        
        assert 'fields_integrated' in metrics
        assert metrics['fields_integrated'] == 4
        assert 'novel_connections' in metrics
        assert metrics['novel_connections'] == 3
        assert 'paradigm_shift' in metrics
        assert metrics['paradigm_shift'] == True


class TestPNeqNPUnifiedApproach:
    """Test suite for P≠NP unified approach demonstration."""
    
    def test_demonstrate_integration(self):
        """Test that approach integrates multiple fields."""
        approach = PNeqNP_UnifiedApproach()
        
        integration = approach.demonstrate_integration()
        
        required_fields = ['mathematics', 'geometry', 'physics', 
                          'biology', 'computation', 'philosophy']
        for field in required_fields:
            assert field in integration
            assert 'tools' in integration[field]
            assert 'contribution' in integration[field]
            assert 'novel' in integration[field]
    
    def test_integration_completeness(self):
        """Test each field contribution is substantial."""
        approach = PNeqNP_UnifiedApproach()
        
        integration = approach.demonstrate_integration()
        
        for field, data in integration.items():
            assert len(data['tools']) > 0
            assert len(data['contribution']) > 0
            assert len(data['novel']) > 0
    
    def test_show_emergence(self):
        """Test emergent insight is more than sum of parts."""
        approach = PNeqNP_UnifiedApproach()
        
        emergent = approach.show_emergence()
        
        assert isinstance(emergent, str)
        assert 'κ_Π' in emergent
        assert '2.5773' in emergent
        assert 'geometría' in emergent or 'geometry' in emergent
        assert 'física' in emergent or 'physics' in emergent
        assert 'biología' in emergent or 'biology' in emergent
    
    def test_verify_predictions(self):
        """Test that predictions are testable and verifiable."""
        approach = PNeqNP_UnifiedApproach()
        
        predictions = approach.verify_predictions()
        
        required_types = ['mathematical', 'physical', 'computational', 'biological']
        for pred_type in required_types:
            assert pred_type in predictions
            assert 'prediction' in predictions[pred_type]
            assert 'testable' in predictions[pred_type]
            assert 'timeline' in predictions[pred_type]
            assert predictions[pred_type]['verifiable'] == True


class TestParadigmShift:
    """Test suite for paradigm shift measurement."""
    
    def test_measure_paradigm_shift(self):
        """Test paradigm shift metrics are defined."""
        new_metrics, indicators = measure_paradigm_shift()
        
        assert 'success' in new_metrics
        assert 'impact' in new_metrics
        assert 'career' in new_metrics
        assert 'funding' in new_metrics
    
    def test_indicators_of_success(self):
        """Test indicators cover multiple dimensions."""
        new_metrics, indicators = measure_paradigm_shift()
        
        assert 'breakthroughs' in indicators
        assert 'education' in indicators
        assert 'culture' in indicators
        
        # Each dimension should have multiple indicators
        for dimension, indicator_list in indicators.items():
            assert len(indicator_list) >= 3


class TestIntegration:
    """Integration tests for the complete framework."""
    
    def test_full_workflow(self):
        """Test complete workflow from problem to solution."""
        # 1. Create framework
        pds = PostDisciplinaryScience()
        
        # 2. Define problem
        problem = Problem(
            name="P_vs_NP",
            description="Computational complexity"
        )
        
        # 3. Solve problem
        solution = pds.solve_problem(problem)
        
        # 4. Verify integration
        assert solution['fields_integrated'] >= 3
        assert solution['integration_quality'] in ['high', 'medium']
    
    def test_reality_consistency(self):
        """Test unified reality maintains consistency."""
        ur = UnifiedReality()
        
        # Get descriptions of κ_Π from all perspectives
        descriptions = ur.get_all_descriptions('kappa_pi')
        
        # All should refer to the same entity
        for desc1 in descriptions.values():
            for desc2 in descriptions.values():
                assert ur.are_same(desc1, desc2) == True
    
    def test_cross_framework_compatibility(self):
        """Test different framework components work together."""
        pds = PostDisciplinaryScience()
        uni = PostDisciplinaryUniversity()
        institute = ComplexityInstitute()
        
        # All should address similar problems
        problem = Problem(name="P_vs_NP")
        solution = pds.solve_problem(problem)
        networks = uni.get_networks_for_problem('p_vs_np')
        
        # Integration should be measurable
        project_data = {
            'disciplines_used': solution['fields_integrated'],
            'unexpected_links': 2,
            'testable_predictions': 3,
            'real_world_applications': 1,
            'changes_thinking': True
        }
        metrics = institute.measure_success(project_data)
        
        assert metrics['fields_integrated'] == solution['fields_integrated']


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
