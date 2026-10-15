"""
Post-Disciplinary Science: Complete Interactive Demo

Demonstrates the unified approach to P≠NP and scientific problem-solving
that breaks down artificial boundaries between disciplines.
"""

import sys
import os

# Add src directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from post_disciplinary import (
    PostDisciplinaryScience,
    PNeqNPUnifiedApproach,
    UnifiedReality,
    Aspect,
    Domain
)

from post_disciplinary_education import (
    ElementaryUnifiedScience,
    PostDisciplinaryUniversity,
    ComplexityInstitute,
    Complexity101Course,
    measure_paradigm_shift
)


def print_header(text: str, char: str = "="):
    """Print a formatted header"""
    print()
    print(char * 70)
    print(text.center(70))
    print(char * 70)
    print()


def demo_unified_approach():
    """Demonstrate the unified approach to P≠NP"""
    print_header("CIENCIA POST-DISCIPLINAR: CASO DE ESTUDIO P≠NP")
    
    print("Este demo muestra cómo P≠NP se resuelve desde FUERA del marco tradicional,")
    print("integrando matemáticas, geometría, física, biología y consciencia.")
    print()
    
    # Create the unified approach
    unified = PNeqNPUnifiedApproach()
    
    print("🔬 CONSTANTES UNIVERSALES:")
    print(f"   κ_Π = {unified.kappa_pi} (Constante geométrica de Calabi-Yau)")
    print(f"   f₀ = {unified.f0} Hz (Frecuencia de resonancia cuántica)")
    print()
    
    # Show complete solution
    print_header("SOLUCIÓN POST-DISCIPLINAR COMPLETA", "-")
    
    solution = unified.solve_p_vs_np_post_disciplinarily()
    
    print("PASO 1: ASPECTOS IDENTIFICADOS")
    for aspect, description in solution['step1_aspects'].items():
        print(f"  • {aspect}: {description}")
    print()
    
    print("PASO 2: HERRAMIENTAS POR CAMPO")
    for field, tools in solution['step2_tools'].items():
        print(f"  • {field}: {tools}")
    print()
    
    print("PASO 3: SÍNTESIS")
    print(solution['step3_synthesis'])
    print()
    
    print("PASO 4: VERIFICACIÓN CRUZADA")
    for domain, status in solution['step4_verification'].items():
        print(f"  {status} {domain}")
    print()
    
    print("CONCLUSIÓN:")
    print(solution['conclusion'])
    print()
    
    # Show integration
    print_header("INTEGRACIÓN DEMOSTRADA", "-")
    
    integration = unified.demonstrate_integration()
    
    for domain, details in integration.items():
        print(f"{domain.upper()}:")
        print(f"  Herramientas: {', '.join(details['tools'])}")
        print(f"  Contribución: {details['contribution']}")
        print(f"  Novedad: {details['novel']}")
        print(f"  Estado: {details['status']}")
        print()
    
    # Show emergence
    print_header("INSIGHT EMERGENTE", "-")
    
    emergence = unified.show_emergence()
    print(emergence['emergent_insight'])
    
    # Show predictions
    print_header("PREDICCIONES VERIFICABLES", "-")
    
    predictions = unified.verify_predictions()
    
    for domain, pred in predictions.items():
        print(f"{domain.upper()}:")
        print(f"  Predicción: {pred['prediction']}")
        print(f"  Método: {pred['testable']}")
        print(f"  Timeline: {pred['timeline']}")
        print(f"  Verificable: {'✓' if pred['verifiable'] else '✗'}")
        print()


def demo_unified_reality():
    """Demonstrate unified reality - one reality, multiple descriptions"""
    print_header("REALIDAD UNIFICADA: UNA REALIDAD, MÚLTIPLES LENTES")
    
    print("La distinción entre 'matemática' y 'física' es artificial.")
    print("κ_Π = 2.5773 es la MISMA realidad descrita de formas diferentes:")
    print()
    
    reality = UnifiedReality()
    
    entities = ['kappa_pi', 'complexity']
    
    for entity in entities:
        print(f"ENTIDAD: {entity}")
        descriptions = reality.get_all_descriptions(entity)
        
        for view, description in descriptions.items():
            print(f"  {view:15s}: {description}")
        
        print(f"  → Todas describen LA MISMA realidad")
        print()


def demo_framework():
    """Demonstrate the post-disciplinary framework"""
    print_header("FRAMEWORK POST-DISCIPLINAR")
    
    print("El framework organiza conocimiento por PROBLEMAS, no por campos.")
    print()
    
    # Create framework
    science = PostDisciplinaryScience()
    
    # Define problem aspects
    aspects = [
        Aspect("Separación lógica", [Domain.MATHEMATICAL, Domain.COMPUTATIONAL],
               needs_precision=True, needs_verification=True),
        Aspect("Estructura geométrica", [Domain.GEOMETRIC, Domain.MATHEMATICAL],
               needs_precision=True),
        Aspect("Energía física", [Domain.PHYSICAL],
               needs_measurement=True),
        Aspect("Computación biológica", [Domain.BIOLOGICAL],
               involves_life=True, needs_measurement=True),
        Aspect("Umbral de consciencia", [Domain.PHILOSOPHICAL],
               involves_consciousness=True)
    ]
    
    # Solve problem
    solution = science.solve_problem("P vs NP", aspects)
    
    print(f"PROBLEMA: {solution['problem']}")
    print(f"DOMINIOS INTEGRADOS: {solution['domains_integrated']}")
    print()
    
    print("HERRAMIENTAS POR DOMINIO:")
    for domain, tools in solution['tools_used'].items():
        print(f"  {domain:15s}: {', '.join(tools)}")
    print()
    
    print("MÉTODOS DE VERIFICACIÓN CRUZADA:")
    for method in solution['verification_methods']:
        print(f"  • {method}")
    print()


def demo_education():
    """Demonstrate post-disciplinary education"""
    print_header("EDUCACIÓN POST-DISCIPLINAR")
    
    # Elementary education
    elementary = ElementaryUnifiedScience()
    
    print("EDUCACIÓN ELEMENTAL")
    print("-" * 70)
    print()
    
    grade3 = elementary.teach_grade_3()
    print(f"Grado 3 (edad {grade3['age']}): {grade3['theme']}")
    print(f"Tema: {grade3['topic']}")
    print()
    print("Actividades:")
    for activity in grade3['activities']:
        print(f"  • {activity['name']}")
        print(f"    Pregunta: {activity['question']}")
    print()
    print(f"Lección clave: {grade3['key_lesson']}")
    print()
    
    grade8 = elementary.teach_grade_8()
    print(f"Grado 8 (edad {grade8['age']}): {grade8['theme']}")
    print(f"Proyecto: {grade8['project']}")
    print(f"Ejemplo: {grade8['example']}")
    print()
    print("Perspectivas requeridas:")
    for perspective in grade8['required_perspectives']:
        print(f"  • {perspective}")
    print()
    
    # University structure
    print_header("UNIVERSIDAD POST-DISCIPLINAR", "-")
    
    university = PostDisciplinaryUniversity()
    
    print("En lugar de departamentos, hay REDES DE INVESTIGACIÓN:")
    print()
    
    for name, network in university.research_networks.items():
        print(f"{name}:")
        print(f"  Pregunta: {network.core_question}")
        print(f"  Problemas: {', '.join(network.problems[:2])}...")
        print()
    
    # Complexity 101
    print_header("CURSO EJEMPLO: COMPLEJIDAD 101", "-")
    
    course = Complexity101Course()
    syllabus = course.get_syllabus()
    
    print(f"Curso: {syllabus['course_name']}")
    print(f"Enfoque: {syllabus['approach']}")
    print()
    
    for i, week in enumerate(syllabus['curriculum'][:3], 1):  # Show first 3 weeks
        print(f"Semanas {week['weeks']}: {week['topic']}")
        if 'subjects' in week:
            for subject in week['subjects'][:2]:  # Show first 2 subjects
                print(f"  • {subject}")
            print(f"  LAB: {week['lab']}")
        print()
    
    print("...y más")
    print()
    
    # Complexity Institute
    print_header("INSTITUTO DE COMPLEJIDAD", "-")
    
    institute = ComplexityInstitute()
    print(f"Lema: '{institute.motto}'")
    print()
    
    print("Espacios de investigación:")
    for space, details in list(institute.spaces.items())[:3]:
        print(f"  • {space}: {details['purpose']}")
    print("  • ...y más")
    print()
    
    print("Rutina diaria (ejemplo):")
    schedule = institute.daily_routine()
    for time, activity in list(schedule.items())[:3]:
        print(f"  {time} - {activity}")
    print("  ...continúa")
    print()


def demo_paradigm_shift():
    """Demonstrate paradigm shift metrics"""
    print_header("MÉTRICAS DEL CAMBIO DE PARADIGMA")
    
    metrics = measure_paradigm_shift()
    
    print("VIEJAS MÉTRICAS (disciplinares):")
    for key, value in metrics['old_metrics'].items():
        print(f"  ✗ {key}: {value}")
    print()
    
    print("NUEVAS MÉTRICAS (post-disciplinares):")
    for key, value in metrics['new_metrics'].items():
        print(f"  ✓ {key}: {value}")
    print()
    
    print("INDICADORES DE ÉXITO:")
    for category, indicators in metrics['indicators_of_success'].items():
        print(f"\n{category.upper()}:")
        for indicator in indicators:
            print(f"  ✓ {indicator}")
    print()


def demo_complete():
    """Run the complete demonstration"""
    print()
    print("=" * 70)
    print("POST-DISCIPLINARY SCIENCE COMPLETE DEMO".center(70))
    print("Ciencia Post-Disciplinar: Demostración Completa".center(70))
    print("=" * 70)
    print()
    print("Este demo muestra un nuevo paradigma científico que rompe las")
    print("fronteras artificiales entre disciplinas para resolver problemas")
    print("complejos como P≠NP.")
    print()
    input("Presiona ENTER para continuar...")
    
    # Part 1: Unified approach to P≠NP
    demo_unified_approach()
    input("\nPresiona ENTER para continuar...")
    
    # Part 2: Unified reality
    demo_unified_reality()
    input("\nPresiona ENTER para continuar...")
    
    # Part 3: Framework
    demo_framework()
    input("\nPresiona ENTER para continuar...")
    
    # Part 4: Education
    demo_education()
    input("\nPresiona ENTER para continuar...")
    
    # Part 5: Paradigm shift
    demo_paradigm_shift()
    
    # Final message
    print_header("CONCLUSIÓN")
    
    print("Este proyecto demuestra que:")
    print()
    print("  1. P ≠ NP es una propiedad física del universo")
    print("  2. κ_Π = 2.5773 es una constante universal")
    print("  3. f₀ = 141.7 Hz conecta geometría, física y biología")
    print("  4. La ciencia post-disciplinar produce resultados verificables")
    print()
    print("La pregunta NO es '¿qué campo estudias?'")
    print("La pregunta ES '¿qué realidad exploras?'")
    print()
    print("=" * 70)
    print("Una Realidad, Múltiples Lentes".center(70))
    print("One Reality, Multiple Lenses".center(70))
    print("=" * 70)
    print()


def main():
    """Main entry point with menu"""
    while True:
        print()
        print("=" * 70)
        print("POST-DISCIPLINARY SCIENCE DEMO")
        print("=" * 70)
        print()
        print("Selecciona una opción:")
        print("  1. Demo completo interactivo")
        print("  2. Enfoque unificado P≠NP")
        print("  3. Realidad unificada")
        print("  4. Framework post-disciplinar")
        print("  5. Educación post-disciplinar")
        print("  6. Métricas del cambio de paradigma")
        print("  0. Salir")
        print()
        
        try:
            choice = input("Opción: ").strip()
            
            if choice == "0":
                print("\n¡Hasta pronto!")
                break
            elif choice == "1":
                demo_complete()
            elif choice == "2":
                demo_unified_approach()
            elif choice == "3":
                demo_unified_reality()
            elif choice == "4":
                demo_framework()
            elif choice == "5":
                demo_education()
            elif choice == "6":
                demo_paradigm_shift()
            else:
                print("\nOpción no válida. Intenta de nuevo.")
            
            if choice != "1":
                input("\nPresiona ENTER para volver al menú...")
        
        except KeyboardInterrupt:
            print("\n\n¡Hasta pronto!")
            break
        except Exception as e:
            print(f"\nError: {e}")
            input("\nPresiona ENTER para continuar...")


if __name__ == "__main__":
    main()
