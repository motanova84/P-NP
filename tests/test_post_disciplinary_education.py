"""
Tests for post-disciplinary education framework
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

import pytest
from post_disciplinary_education import (
    ElementaryUnifiedScience,
    PostDisciplinaryUniversity,
    ComplexityInstitute,
    Complexity101Course,
    measure_paradigm_shift,
    AssessmentMethod,
    ResearchNetwork
)


class TestElementaryUnifiedScience:
    """Tests for elementary education"""
    
    def test_grade_3_lesson(self):
        """Test Grade 3 curriculum"""
        elementary = ElementaryUnifiedScience()
        lesson = elementary.teach_grade_3()
        
        assert lesson['grade'] == 3
        assert lesson['age'] == '8 years'
        assert 'activities' in lesson
        assert len(lesson['activities']) > 0
        assert 'key_lesson' in lesson
        
        # Check activities have required fields
        for activity in lesson['activities']:
            assert 'name' in activity
            assert 'question' in activity
    
    def test_grade_8_lesson(self):
        """Test Grade 8 curriculum"""
        elementary = ElementaryUnifiedScience()
        lesson = elementary.teach_grade_8()
        
        assert lesson['grade'] == 8
        assert lesson['age'] == '13 years'
        assert 'required_perspectives' in lesson
        assert len(lesson['required_perspectives']) >= 4
        assert 'rubric' in lesson
        
        # Rubric should have integration criteria
        assert 'integration' in lesson['rubric']
        assert 'coherence' in lesson['rubric']


class TestPostDisciplinaryUniversity:
    """Tests for post-disciplinary university structure"""
    
    def test_initialization(self):
        """Test university initializes with research networks"""
        university = PostDisciplinaryUniversity()
        
        assert 'Complexity Network' in university.research_networks
        assert 'Structure Network' in university.research_networks
        assert 'Information Network' in university.research_networks
    
    def test_research_networks(self):
        """Test research networks have proper structure"""
        university = PostDisciplinaryUniversity()
        
        for name, network in university.research_networks.items():
            assert isinstance(network, ResearchNetwork)
            assert len(network.core_question) > 0
            assert len(network.tools) > 0
            assert len(network.problems) > 0
    
    def test_hire_researcher(self):
        """Test hiring researcher for multiple networks"""
        university = PostDisciplinaryUniversity()
        
        person = {
            'name': 'Test Researcher',
            'can_contribute_to_question': True
        }
        
        hired = university.hire_researcher(person)
        
        assert 'affiliations' in hired
        # Can be in multiple networks
        assert isinstance(hired['affiliations'], list)
    
    def test_teach_course(self):
        """Test course creation"""
        university = PostDisciplinaryUniversity()
        course = university.teach_course('complexity')
        
        assert 'complexity' in course.topic.lower()
        assert len(course.methods) > 0
        assert len(course.assessments) > 0


class TestComplexityInstitute:
    """Tests for Complexity Institute model"""
    
    def test_initialization(self):
        """Test institute initializes properly"""
        institute = ComplexityInstitute()
        
        assert institute.motto == "Una Realidad, Múltiples Lentes"
        assert len(institute.spaces) > 0
    
    def test_spaces(self):
        """Test institute has required spaces"""
        institute = ComplexityInstitute()
        
        # Should have integration and specialized spaces
        assert 'integration_studio' in institute.spaces
        assert 'formal_verification_lab' in institute.spaces
        
        # Each space should have purpose and tools
        for space, details in institute.spaces.items():
            assert 'tools' in details
            assert 'purpose' in details
    
    def test_daily_routine(self):
        """Test daily routine structure"""
        institute = ComplexityInstitute()
        schedule = institute.daily_routine()
        
        assert len(schedule) > 0
        # Should have integration activities
        assert any('integration' in activity.lower() or 'synthesis' in activity.lower() 
                  for activity in schedule.values())
    
    def test_measure_success(self):
        """Test success measurement"""
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
        assert 'novel_connections' in metrics
        assert 'integration_score' in metrics
        assert metrics['fields_integrated'] == 4
        assert metrics['integration_score'] > 0


class TestComplexity101Course:
    """Tests for Complexity 101 course"""
    
    def test_initialization(self):
        """Test course initializes"""
        course = Complexity101Course()
        
        assert 'Complexity 101' in course.course_name
        assert len(course.weeks) > 0
    
    def test_curriculum_structure(self):
        """Test curriculum has proper structure"""
        course = Complexity101Course()
        
        # Should have multiple weeks
        assert len(course.weeks) >= 5
        
        # Check structure
        for week in course.weeks:
            assert 'weeks' in week
            assert 'topic' in week
            # Either has subjects+lab or project
            assert 'subjects' in week or 'project' in week
    
    def test_syllabus(self):
        """Test syllabus generation"""
        course = Complexity101Course()
        syllabus = course.get_syllabus()
        
        assert 'course_name' in syllabus
        assert 'approach' in syllabus
        assert 'curriculum' in syllabus
        assert 'assessment_criteria' in syllabus
        
        # Should emphasize integration
        assert 'integration' in syllabus['assessment_criteria']


class TestParadigmShift:
    """Tests for paradigm shift metrics"""
    
    def test_measure_paradigm_shift(self):
        """Test paradigm shift measurement"""
        metrics = measure_paradigm_shift()
        
        assert 'old_metrics' in metrics
        assert 'new_metrics' in metrics
        assert 'indicators_of_success' in metrics
        
        # Should have success, impact, career, funding
        assert 'success' in metrics['old_metrics']
        assert 'success' in metrics['new_metrics']
        
        # New metrics should be different from old
        assert metrics['old_metrics']['success'] != metrics['new_metrics']['success']
    
    def test_indicators_structure(self):
        """Test indicators of success structure"""
        metrics = measure_paradigm_shift()
        indicators = metrics['indicators_of_success']
        
        # Should have multiple categories
        assert 'breakthroughs' in indicators
        assert 'education' in indicators
        assert 'culture' in indicators
        
        # Each should have multiple indicators
        for category in indicators.values():
            assert len(category) > 0


class TestAssessmentMethod:
    """Tests for assessment method enum"""
    
    def test_assessment_methods_exist(self):
        """Test all assessment methods are defined"""
        assert AssessmentMethod.PROVE
        assert AssessmentMethod.BUILD
        assert AssessmentMethod.MEASURE
        assert AssessmentMethod.EXPLAIN
        assert AssessmentMethod.INTEGRATE


class TestResearchNetwork:
    """Tests for research network dataclass"""
    
    def test_research_network_creation(self):
        """Test creating a research network"""
        network = ResearchNetwork(
            name="Test Network",
            core_question="What is the question?",
            tools=['tool1', 'tool2'],
            problems=['problem1', 'problem2']
        )
        
        assert network.name == "Test Network"
        assert len(network.tools) == 2
        assert len(network.problems) == 2
        assert len(network.researchers) == 0  # default


def test_demonstrate_educational_framework():
    """Test the main demonstration function"""
    from post_disciplinary_education import demonstrate_educational_framework
    
    # Should run without error
    demonstrate_educational_framework()
    # If we get here, it worked


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
