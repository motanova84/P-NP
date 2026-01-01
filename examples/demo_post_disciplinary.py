"""
Post-Disciplinary Science Demonstration
========================================

Interactive demonstration of the post-disciplinary science framework
applied to the P vs NP problem.

This example shows how the same problem can be approached from multiple
perspectives simultaneously, leading to emergent insights.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from post_disciplinary import (
    PostDisciplinaryScience,
    UnifiedReality,
    PostDisciplinaryUniversity,
    ComplexityInstitute,
    PNeqNP_UnifiedApproach,
    measure_paradigm_shift,
    Problem
)


def print_section(title):
    """Print a formatted section header."""
    print("\n" + "=" * 80)
    print(f"  {title}")
    print("=" * 80)


def demonstrate_post_disciplinary_approach():
    """Main demonstration of the post-disciplinary framework."""
    
    print_section("POST-DISCIPLINARY SCIENCE: P≠NP AS CASE STUDY")
    
    print("\nTraditional approach: P≠NP is purely mathematical")
    print("Post-disciplinary approach: P≠NP is a multi-domain phenomenon")
    
    # 1. Create the framework
    print_section("STEP 1: Initialize Post-Disciplinary Framework")
    
    pds = PostDisciplinaryScience()
    print(f"\nConcept networks available: {list(pds.concept_network.keys())}")
    print(f"Tool categories: {list(pds.available_tools.keys())}")
    
    # 2. Define the problem
    print_section("STEP 2: Define Problem (P vs NP)")
    
    problem = Problem(
        name="P_vs_NP",
        description="Is P equal to NP? Can every problem whose solution can be "
                   "quickly verified also be quickly solved?"
    )
    print(f"\nProblem: {problem.name}")
    print(f"Description: {problem.description}")
    
    # 3. Identify aspects
    print_section("STEP 3: Identify Aspects from Multiple Perspectives")
    
    aspects = pds.identify_aspects(problem)
    print(f"\nIdentified {len(aspects)} aspects:")
    for i, aspect in enumerate(aspects, 1):
        print(f"  {i}. {aspect.name}: {aspect.description}")
    
    # 4. Solve post-disciplinarily
    print_section("STEP 4: Solve Using ALL Relevant Tools")
    
    solution = pds.solve_problem(problem)
    print(f"\nProblem analyzed: {solution['problem']}")
    print(f"Aspects analyzed: {', '.join(solution['aspects_analyzed'])}")
    print(f"Fields integrated: {solution['fields_integrated']}")
    print(f"Integration quality: {solution['integration_quality']}")
    print(f"Total tools employed: {len(solution['tools_used'])}")
    
    print("\nTools by field:")
    tools_by_field = {}
    for tool in solution['tools_used']:
        field = tool['field']
        if field not in tools_by_field:
            tools_by_field[field] = []
        tools_by_field[field].append(tool['name'])
    
    for field, tools in tools_by_field.items():
        print(f"  {field}: {', '.join(tools)}")
    
    # 5. Show unified reality
    print_section("STEP 5: Unified Reality - Multiple Descriptions")
    
    ur = UnifiedReality()
    print("\nκ_Π = 2.5773 described from different perspectives:")
    print("(All describing the SAME reality)\n")
    
    descriptions = ur.get_all_descriptions('kappa_pi')
    for perspective, description in descriptions.items():
        print(f"  {perspective.upper()}:")
        print(f"    → {description}\n")
    
    print("All these descriptions are equivalent:")
    print(f"  are_same(mathematical, physical) = {ur.are_same('math', 'phys')}")
    
    # 6. Show institutional model
    print_section("STEP 6: Post-Disciplinary University Organization")
    
    uni = PostDisciplinaryUniversity()
    print("\nResearch Networks (not departments):")
    for network_name, network_data in uni.research_networks.items():
        print(f"\n  {network_name}:")
        print(f"    Core Question: {network_data['core_question']}")
        print(f"    Tools: {len(network_data['tools'])} interdisciplinary tools")
        print(f"    Problems: {', '.join(network_data['problems'])}")
    
    print("\n\nExample: Hiring a researcher")
    researcher_skills = {
        'graph_theory': True,
        'quantum_mechanics': True,
        'consciousness_theory': True
    }
    networks = uni.hire_researcher(researcher_skills)
    print(f"  Skills: {', '.join(researcher_skills.keys())}")
    print(f"  Affiliations: {', '.join(networks) if networks else 'Will match with relevant networks'}")
    
    # 7. Show institute model
    print_section("STEP 7: Complexity Institute - Integrated Spaces")
    
    institute = ComplexityInstitute()
    print(f"\nMotto: {institute.motto}\n")
    print("Integrated research spaces:")
    for space_name, space_data in institute.spaces.items():
        print(f"\n  {space_name}:")
        print(f"    Purpose: {space_data['purpose']}")
        print(f"    Tools: {', '.join(space_data['tools'][:3])}...")
    
    print("\n\nDaily Schedule (promotes integration):")
    schedule = institute.daily_routine()
    for time, activity in schedule.items():
        print(f"  {time} - {activity}")
    
    # 8. Show our work as model
    print_section("STEP 8: Our P≠NP Work as Model")
    
    approach = PNeqNP_UnifiedApproach()
    integration = approach.demonstrate_integration()
    
    print(f"\nFields integrated in our approach: {len(integration)}")
    for field, data in integration.items():
        print(f"\n  {field.upper()}:")
        print(f"    Tools: {', '.join(data['tools'])}")
        print(f"    Contribution: {data['contribution']}")
        print(f"    Novel insight: {data['novel']}")
    
    # 9. Show emergent insight
    print_section("STEP 9: Emergent Insight (More than Sum of Parts)")
    
    emergent = approach.show_emergence()
    print(emergent)
    
    # 10. Show verifiable predictions
    print_section("STEP 10: Verifiable Predictions")
    
    predictions = approach.verify_predictions()
    print("\nTestable predictions from the unified approach:\n")
    for pred_type, pred_data in predictions.items():
        print(f"  {pred_type.upper()}:")
        print(f"    Prediction: {pred_data['prediction']}")
        print(f"    Test method: {pred_data['testable']}")
        print(f"    Timeline: {pred_data['timeline']}")
        print(f"    Verifiable: {'✓' if pred_data['verifiable'] else '✗'}\n")
    
    # 11. Paradigm shift metrics
    print_section("STEP 11: Measuring Paradigm Shift")
    
    new_metrics, indicators = measure_paradigm_shift()
    
    print("\nOLD vs NEW metrics:")
    print("\n  Traditional metrics:")
    print("    - Papers in field-specific journals")
    print("    - Citations within discipline")
    print("    - Department-specific advancement")
    
    print("\n  Post-disciplinary metrics:")
    for metric, description in new_metrics.items():
        print(f"    - {metric}: {description}")
    
    print("\n\nIndicators of success:")
    for category, indicator_list in indicators.items():
        print(f"\n  {category.upper()}:")
        for indicator in indicator_list:
            print(f"    • {indicator}")
    
    # 12. Final vision
    print_section("FINAL VISION")
    
    print("""
The question is no longer "What field are you in?"
The question is "What reality are you exploring?"

Post-disciplinary science recognizes that:
• The boundaries between fields are artificial
• Reality is unified; our descriptions are multiple
• Complex problems require integrated approaches
• P≠NP is not just mathematics - it's a property of the universe

κ_Π = 2.5773 appears in:
  - Geometry (Calabi-Yau manifolds)
  - Physics (resonance at 141.7 Hz)
  - Biology (RNA vibrational modes)
  - Computation (treewidth threshold)
  - Consciousness (integration threshold)

This is not coincidence. This is unity.
""")
    
    print("=" * 80)


if __name__ == "__main__":
    try:
        demonstrate_post_disciplinary_approach()
        print("\n✓ Demonstration completed successfully\n")
    except Exception as e:
        print(f"\n✗ Error: {e}\n")
        raise
