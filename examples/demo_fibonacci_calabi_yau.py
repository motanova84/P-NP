#!/usr/bin/env python3
"""
demo_fibonacci_calabi_yau.py - Demonstration of Fibonacci structure analysis

Interactive demonstration of the investigation into Fibonacci structure
in Calabi-Yau moduli spaces and the natural emergence of φ².

Usage:
    python examples/demo_fibonacci_calabi_yau.py

© JMMB | P vs NP Verification System
Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from calabi_yau_fibonacci_analysis import (
    fibonacci_sequence,
    phi_power_sequence,
    verify_phi_fibonacci_relation,
    load_extended_cy_data,
    compute_fibonacci_metrics,
    analyze_phi_squared_clustering,
    test_fibonacci_recursion_hypothesis,
    generate_fibonacci_report,
    plot_fibonacci_analysis,
    run_complete_fibonacci_analysis,
    PHI,
    PHI_SQUARED,
    KAPPA_PI_TARGET
)


def demo_paso_1():
    """Demonstrate PASO 1: Algebraic foundation of φ²."""
    print("=" * 80)
    print("🧠 PASO 1 — Fundamento Algebraico de φ²")
    print("=" * 80)
    print()
    
    print(f"φ (razón áurea) = (1 + √5)/2 = {PHI:.10f}")
    print(f"φ² = φ + 1 = {PHI_SQUARED:.10f}")
    print()
    
    print("Propiedades fundamentales:")
    print(f"  φ² - φ - 1 = 0  (ecuación característica)")
    print(f"  φ² = {PHI_SQUARED:.10f}")
    print(f"  φ + 1 = {PHI + 1:.10f}")
    print(f"  Verificación: φ² = φ + 1 ✓" if abs(PHI_SQUARED - (PHI + 1)) < 1e-10 else "  Error!")
    print()
    
    print("Relación con números de Fibonacci:")
    print()
    fib = fibonacci_sequence(10)
    print("n\tF_n\tφ^n\t\tF_n·φ + F_{n-1}")
    print("-" * 80)
    for n in range(1, 11):
        result = verify_phi_fibonacci_relation(n)
        print(f"{n}\t{result['F_n']}\t{result['phi_n_direct']:.6f}\t{result['phi_n_formula']:.6f}")
    print()
    
    print("Conclusión PASO 1:")
    print("  φ² emerge naturalmente de la recursión de Fibonacci")
    print("  φ^n = F_n·φ + F_{n-1} conecta crecimiento discreto y continuo")
    print()


def demo_paso_2():
    """Demonstrate PASO 2: Test Fibonacci hypothesis in (h^{1,1}, h^{2,1})."""
    print("=" * 80)
    print("🧩 PASO 2 — Hipótesis: Estructura Fibonacci en (h^{1,1}, h^{2,1})")
    print("=" * 80)
    print()
    
    df = load_extended_cy_data()
    
    print("Hipótesis a probar:")
    print("  ¿Existe recursión tipo Fibonacci en los números de Hodge?")
    print("  h_n^{2,1} ≈ h_{n-1}^{2,1} + h_{n-2}^{1,1}")
    print("  o bien: N_n ≈ N_{n-1} + N_{n-2}")
    print()
    
    result = test_fibonacci_recursion_hypothesis(df)
    
    print(f"Resultado del test:")
    print(f"  Total de casos probados: {result['total_tested']}")
    print(f"  Casos con patrón Fibonacci: {result['fibonacci_like_count']}")
    print(f"  Porcentaje: {result['fibonacci_percentage']:.1f}%")
    print()
    
    if result['details']:
        print("Ejemplos de análisis:")
        for i, detail in enumerate(result['details'][:5], 1):
            marker = "✓" if detail['is_fibonacci_like'] else "✗"
            print(f"  {marker} N_{i+1}={detail['N_curr']}: esperado {detail['expected_sum']}, "
                  f"desviación={detail['deviation']:.1f}")
    print()
    
    print("Conclusión PASO 2:")
    if result['fibonacci_percentage'] > 20:
        print(f"  ✓ Se observa estructura recursiva Fibonacci-like en {result['fibonacci_percentage']:.1f}% de casos")
    else:
        print("  ⚠️  La recursión Fibonacci no es dominante en los datos")
    print()


def demo_paso_3():
    """Demonstrate PASO 3: Model N_n ∼ φ^n and verify κ_Π."""
    print("=" * 80)
    print("🧬 PASO 3 — Modelo Propuesto: N_n ∼ φ^n ⇒ κ_Π(N_n) ∼ n/2")
    print("=" * 80)
    print()
    
    print("Modelo matemático:")
    print("  Si N_n ∼ φ^n, entonces:")
    print("  κ_Π(N_n) = log_φ²(N_n) = log_φ²(φ^n) = n·log_φ²(φ) = n/2")
    print()
    
    print("Verificación con valores de φ^n:")
    print()
    print("n\tφ^n\t\tκ_Π(φ^n)\tn/2")
    print("-" * 80)
    
    for n in range(4, 8):
        phi_n = PHI ** n
        kappa = n / 2.0
        kappa_actual = kappa  # By definition
        print(f"{n}\t{phi_n:.3f}\t\t{kappa_actual:.3f}\t\t{kappa:.3f}")
    print()
    
    print("Implicación para κ_Π = 2.5773:")
    print(f"  Si κ_Π = {KAPPA_PI_TARGET}, entonces:")
    n_expected = 2 * KAPPA_PI_TARGET
    N_expected = PHI ** n_expected
    print(f"  n = 2·κ_Π = {n_expected:.4f}")
    print(f"  N = φ^n = φ^{n_expected:.4f} ≈ {N_expected:.2f}")
    print()
    print(f"  El entero más cercano es N ≈ {round(N_expected)}")
    print()


def demo_paso_4():
    """Demonstrate PASO 4: Verify with CICY/KS data."""
    print("=" * 80)
    print("📊 PASO 4 — Verificación con Datos CICY/Kreuzer-Skarke")
    print("=" * 80)
    print()
    
    df = load_extended_cy_data()
    df = compute_fibonacci_metrics(df)
    
    print("Buscar variedades con N cerca de φ^n para n = 4, 5, 6, 7:")
    print()
    
    for n in [4, 5, 6, 7]:
        phi_n = PHI ** n
        expected_kappa = n / 2.0
        
        print(f"φ^{n} ≈ {phi_n:.2f} (κ_Π esperado = {expected_kappa:.3f}):")
        
        # Find varieties close to φ^n
        close_varieties = df[abs(df['N'] - phi_n) < 2]
        
        if len(close_varieties) > 0:
            for _, var in close_varieties.head(3).iterrows():
                deviation = abs(var['kappa_phi2'] - expected_kappa)
                marker = "✓" if deviation < 0.1 else "~"
                print(f"  {marker} {var['name']}: N={var['N']}, κ_Π={var['kappa_phi2']:.4f}, "
                      f"desv={deviation:.4f}")
        else:
            print(f"  (No se encontraron variedades cerca de φ^{n})")
        print()
    
    # Also check Fibonacci numbers
    print("Variedades con N = números de Fibonacci:")
    print()
    fib_nums = [2, 3, 5, 8, 13, 21]
    
    for fib_n in fib_nums:
        fib_varieties = df[df['N'] == fib_n]
        if len(fib_varieties) > 0:
            avg_kappa = fib_varieties['kappa_phi2'].mean()
            print(f"  N = {fib_n}: {len(fib_varieties)} variedades, κ_Π medio = {avg_kappa:.4f}")
    print()


def demo_paso_5():
    """Demonstrate PASO 5: h^{1,1}/h^{2,1} ratio clustering."""
    print("=" * 80)
    print("🎯 PASO 5 — Clustering de Ratios h^{1,1}/h^{2,1} cerca de φ²")
    print("=" * 80)
    print()
    
    df = load_extended_cy_data()
    df = compute_fibonacci_metrics(df)
    
    clustering = analyze_phi_squared_clustering(df)
    
    print("Análisis de distribución de ratios:")
    print(f"  Total de ratios analizados: {clustering['total_ratios']}")
    print(f"  Ratio medio: {clustering['mean_ratio']:.4f}")
    print(f"  Ratio mediano: {clustering['median_ratio']:.4f}")
    print(f"  Desviación estándar: {clustering['std_ratio']:.4f}")
    print()
    
    print("Comparación con constantes áureas:")
    print(f"  φ ≈ {PHI:.4f}")
    print(f"  φ² ≈ {PHI_SQUARED:.4f}")
    print()
    print(f"  Ratios cercanos a φ (±0.2): {clustering['close_to_phi_count']}")
    print(f"  Ratios cercanos a φ² (±0.2): {clustering['close_to_phi2_count']}")
    print()
    print(f"  Distancia media a φ: {clustering['mean_dist_to_phi']:.4f}")
    print(f"  Distancia media a φ²: {clustering['mean_dist_to_phi2']:.4f}")
    print()
    
    print("Conclusión PASO 5:")
    if clustering['clustering_evidence']:
        print("  ✓ Se observa evidencia de clustering cerca de φ²")
    else:
        print("  ⚠️  Evidencia de clustering limitada")
    
    print(f"  El ratio más cercano a φ²: {clustering['closest_to_phi2']:.4f}")
    print()


def demo_visualization():
    """Demonstrate visualization generation."""
    print("=" * 80)
    print("📈 Generación de Visualizaciones")
    print("=" * 80)
    print()
    
    df = load_extended_cy_data()
    df = compute_fibonacci_metrics(df)
    
    print("Creando gráficos de análisis Fibonacci...")
    plot_path = plot_fibonacci_analysis(df)
    print(f"✓ Gráfico guardado en: {plot_path}")
    print()
    print("El gráfico incluye:")
    print("  1. N vs κ_Π con números de Fibonacci marcados")
    print("  2. Distribución de ratios h^{1,1}/h^{2,1}")
    print("  3. Proximidad a valores φ^n")
    print("  4. κ_Π esperado vs actual para N ≈ φ^n")
    print()


def demo_full_report():
    """Demonstrate full report generation."""
    print("=" * 80)
    print("📄 Generación de Reporte Completo")
    print("=" * 80)
    print()
    
    df = load_extended_cy_data()
    df = compute_fibonacci_metrics(df)
    
    print("Generando reporte completo...")
    report = generate_fibonacci_report(df)
    print("✓ Reporte generado")
    print()
    print("El reporte incluye:")
    print("  ✓ Fundamento algebraico de φ²")
    print("  ✓ Test de estructura Fibonacci")
    print("  ✓ Modelo N_n ∼ φ^n")
    print("  ✓ Verificación con datos CICY/KS")
    print("  ✓ Análisis de clustering de ratios")
    print("  ✓ Conclusiones y evaluación general")
    print()


def main():
    """Run all demonstrations."""
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  Fibonacci Structure in Calabi-Yau Moduli - Interactive Demo".center(78) + "║")
    print("║" + "  Investigación algebraico-geométrica de φ² en conteos de moduli".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    
    demos = [
        ("PASO 1: Fundamento Algebraico", demo_paso_1),
        ("PASO 2: Hipótesis Fibonacci", demo_paso_2),
        ("PASO 3: Modelo N_n ∼ φ^n", demo_paso_3),
        ("PASO 4: Verificación CICY/KS", demo_paso_4),
        ("PASO 5: Clustering φ²", demo_paso_5),
        ("Visualizaciones", demo_visualization),
        ("Reporte Completo", demo_full_report),
    ]
    
    for i, (name, demo_func) in enumerate(demos, 1):
        print()
        demo_func()
        if i < len(demos):
            input("Presiona Enter para continuar al siguiente paso...")
    
    print()
    print("=" * 80)
    print("¿Deseas ejecutar el análisis completo integrado?")
    print("=" * 80)
    response = input("Ejecutar análisis completo? (s/n): ").strip().lower()
    
    if response == 's' or response == 'y':
        print()
        print()
        results = run_complete_fibonacci_analysis()
        print()
        print("✓ Análisis completo finalizado!")
        print(f"✓ Reporte guardado en: /tmp/fibonacci_cy_report.txt")
        print(f"✓ Gráfico guardado en: /tmp/fibonacci_cy_analysis.png")
    
    print()
    print("=" * 80)
    print("Demo completada!")
    print("© JMMB | P vs NP Verification System")
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 80)
    print()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
