#!/usr/bin/env python3
"""
Demo: Análisis de Distribución κ_Π para Variedades Calabi-Yau
=============================================================

Este script demuestra el uso completo del módulo kappa_pi_distribution
para analizar la distribución de κ_Π en variedades Calabi-Yau.

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Fecha: 1 enero 2026
"""

import sys
import os

# Agregar ruta al path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import numpy as np
from src.kappa_pi_distribution import (
    compute_kappa_distribution,
    plot_kappa_distribution,
    generate_scientific_report,
    compare_with_theoretical_distribution,
    analyze_local_density
)


def generate_realistic_cy_data(n_manifolds: int = 500, seed: int = 42) -> list:
    """
    Genera datos realistas de variedades Calabi-Yau.
    
    Incluye:
    - Distribución log-normal para la mayoría de casos
    - Algunos casos especiales con N pequeño
    - Casos anómalos cerca de N=13
    
    Args:
        n_manifolds: Número de variedades a generar
        seed: Semilla para reproducibilidad
    
    Returns:
        Lista de tuplas (h11, h21)
    """
    np.random.seed(seed)
    cy_list = []
    
    # 1. Mayoría con distribución log-normal (80%)
    n_regular = int(0.8 * n_manifolds)
    for _ in range(n_regular):
        # Log-normal para h11 y h21
        h11 = int(np.random.lognormal(mean=3.0, sigma=1.5)) + 1
        h21 = int(np.random.lognormal(mean=3.0, sigma=1.5)) + 1
        
        # Limitar valores razonables
        h11 = min(max(h11, 1), 500)
        h21 = min(max(h21, 1), 500)
        
        cy_list.append((h11, h21))
    
    # 2. Casos con N pequeño (10%)
    n_small = int(0.1 * n_manifolds)
    for _ in range(n_small):
        h11 = np.random.randint(1, 20)
        h21 = np.random.randint(1, 20)
        cy_list.append((h11, h21))
    
    # 3. Casos anómalos cerca de N=13 (10%)
    n_anomalous = n_manifolds - n_regular - n_small
    
    # Algunos exactamente N=13
    for i in range(min(n_anomalous // 2, 20)):
        h11 = np.random.randint(1, 13)
        h21 = 13 - h11
        cy_list.append((h11, h21))
    
    # Algunos cerca de N=13
    for i in range(n_anomalous - min(n_anomalous // 2, 20)):
        N_target = 13 + np.random.randint(-2, 3)  # [11, 15]
        h11 = np.random.randint(1, max(2, N_target))
        h21 = max(1, N_target - h11)
        cy_list.append((h11, h21))
    
    return cy_list


def main():
    """Función principal del demo"""
    
    print("╔══════════════════════════════════════════════════════════════════════════╗")
    print("║         DEMO: Análisis de Distribución κ_Π - Calabi-Yau                 ║")
    print("╚══════════════════════════════════════════════════════════════════════════╝\n")
    
    # 1. Generar datos de variedades CY
    print("📊 Generando datos de variedades Calabi-Yau...")
    n_manifolds = 500
    cy_list = generate_realistic_cy_data(n_manifolds=n_manifolds)
    print(f"   ✅ {len(cy_list)} variedades generadas\n")
    
    # 2. Calcular distribución de κ_Π
    print("🔢 Calculando distribución de κ_Π = log₂(h11 + h21)...")
    kappas, Ns, stats = compute_kappa_distribution(cy_list, base=2)
    print(f"   ✅ Distribución calculada\n")
    
    # 3. Mostrar estadísticas básicas
    print("📈 Estadísticas básicas:")
    print(f"   • Media κ_Π:              {stats['mean']:.4f}")
    print(f"   • Desviación estándar:    {stats['std']:.4f}")
    print(f"   • Mediana:                {stats['median']:.4f}")
    print(f"   • Rango:                  [{stats['min']:.4f}, {stats['max']:.4f}]")
    print(f"   • log₂(13):               {stats['special_N13_kappa']:.4f}")
    print(f"   • Variedades con N=13:    {stats['special_N13_count']}\n")
    
    # 4. Análisis de densidad local
    print("🔍 Analizando densidad local cerca de N=13...")
    density = analyze_local_density(Ns, target_N=13, window=2)
    print(f"   • Ocurrencias exactas N=13:      {density['exact_count']}")
    print(f"   • Ocurrencias en [11-15]:        {density['window_count']}")
    print(f"   • Densidad observada:            {density['exact_density']:.6f}")
    print(f"   • Densidad esperada:             {density['expected_density']:.6f}")
    print(f"   • Ratio anomalía:                {density['anomaly_ratio']:.2f}x")
    print(f"   • {'✅ ANOMALÍA DETECTADA' if density['is_anomalous'] else '❌ Sin anomalía'}\n")
    
    # 5. Comparación con modelos teóricos
    print("📊 Comparando con modelos teóricos...")
    
    # Modelo exponencial
    exp_model = compare_with_theoretical_distribution(Ns, model='exponential')
    print(f"\n   Modelo Exponencial P(N) ~ exp(-αN):")
    print(f"   • α = {exp_model['alpha']:.6f}")
    print(f"   • Media teórica: {exp_model['mean_theoretical']:.2f}")
    print(f"   • Media observada: {exp_model['mean_observed']:.2f}")
    print(f"   • χ² = {exp_model['chi_squared']:.4f}")
    
    # Modelo log-normal
    lognorm_model = compare_with_theoretical_distribution(Ns, model='lognormal')
    print(f"\n   Modelo Log-Normal:")
    print(f"   • μ = {lognorm_model['mu']:.4f}")
    print(f"   • σ = {lognorm_model['sigma']:.4f}")
    print(f"   • Mediana teórica: {lognorm_model['median_theoretical']:.2f}")
    print(f"   • Mediana observada: {lognorm_model['median_observed']:.2f}\n")
    
    # 6. Generar reporte científico completo
    print("=" * 78)
    report = generate_scientific_report(kappas, Ns, stats)
    print(report)
    
    # 7. Visualización
    print("\n📊 Generando visualizaciones...")
    
    # Crear directorio de salida si no existe
    output_dir = os.path.join(os.path.dirname(__file__), '..', 'output')
    os.makedirs(output_dir, exist_ok=True)
    
    # Guardar figura
    output_path = os.path.join(output_dir, 'kappa_pi_distribution.png')
    plot_kappa_distribution(
        kappas, 
        Ns, 
        special_kappa=stats['special_N13_kappa'],
        save_path=output_path,
        show=False
    )
    
    print(f"   ✅ Visualización guardada en: {output_path}")
    
    # 8. Análisis detallado de clustering
    print("\n🔍 Análisis de clustering:")
    
    # Coeficiente de variación
    cv = stats['std'] / stats['mean']
    print(f"   • Coeficiente de variación: {cv:.4f}")
    
    if cv < 0.3:
        print("   → Distribución muestra FUERTE clustering")
    elif cv < 0.5:
        print("   → Distribución muestra clustering moderado")
    else:
        print("   → Distribución relativamente dispersa")
    
    # Distribución de percentiles
    kappas_array = np.array(kappas)
    percentiles = [10, 25, 50, 75, 90]
    print(f"\n   Percentiles de κ_Π:")
    for p in percentiles:
        val = np.percentile(kappas_array, p)
        print(f"   • P{p:02d}: {val:.4f}")
    
    # 9. Preguntas científicas específicas
    print("\n" + "=" * 78)
    print("🎯 RESPUESTAS A PREGUNTAS CIENTÍFICAS")
    print("=" * 78)
    
    print("\n1️⃣  ¿La distribución de κ_Π es suave o hay clustering?")
    if cv < 0.3:
        print("   ➜ HAY CLUSTERING SIGNIFICATIVO")
        print(f"   ➜ El coeficiente de variación ({cv:.4f}) indica")
        print("      concentración de valores alrededor de la media")
    else:
        print("   ➜ DISTRIBUCIÓN RELATIVAMENTE SUAVE")
        print(f"   ➜ El coeficiente de variación ({cv:.4f}) indica")
        print("      dispersión moderada")
    
    print("\n2️⃣  ¿Existe anomalía o resonancia cerca de log₂(13) ≈ 3.700?")
    if density['is_anomalous']:
        print(f"   ➜ SÍ - ANOMALÍA DETECTADA")
        print(f"   ➜ La densidad observada es {density['anomaly_ratio']:.2f}x mayor")
        print("      que la esperada por una distribución suave")
        print(f"   ➜ {density['exact_count']} variedades con N=13 exacto")
    else:
        print(f"   ➜ NO - Sin anomalía significativa")
        print(f"   ➜ La densidad observada ({density['exact_density']:.6f}) es")
        print(f"      comparable a la esperada ({density['expected_density']:.6f})")
    
    print("\n3️⃣  ¿Cuál es la media y desviación estándar?")
    print(f"   ➜ μ(κ_Π) = {stats['mean']:.4f}")
    print(f"   ➜ σ(κ_Π) = {stats['std']:.4f}")
    print(f"   ➜ Intervalo [μ-σ, μ+σ]: [{stats['mean']-stats['std']:.4f}, {stats['mean']+stats['std']:.4f}]")
    
    print("\n4️⃣  ¿Qué tan raras son las CY con N = 13?")
    rarity_pct = stats['density_N13'] * 100
    print(f"   ➜ Frecuencia: {stats['special_N13_count']}/{stats['total_manifolds']} = {rarity_pct:.4f}%")
    
    if rarity_pct < 0.5:
        print("   ➜ MUY RARO - Menos del 0.5% de las variedades")
    elif rarity_pct < 2.0:
        print("   ➜ RARO - Entre 0.5% y 2% de las variedades")
    elif rarity_pct < 5.0:
        print("   ➜ POCO COMÚN - Entre 2% y 5% de las variedades")
    else:
        print("   ➜ COMÚN - Más del 5% de las variedades")
    
    # 10. Conclusión final
    print("\n" + "=" * 78)
    print("📝 CONCLUSIÓN CIENTÍFICA")
    print("=" * 78)
    
    if density['is_anomalous'] and cv < 0.5:
        print("\n✅ La coherencia espectral en N=13 ES SIGNIFICATIVA:")
        print("   • Se observa clustering en la distribución de κ_Π")
        print("   • Existe anomalía estadística cerca de log₂(13)")
        print("   • La densidad observada excede la esperada")
        print("\n   ⚠️  Esto requiere análisis adicional de la base de datos")
        print("       completa para confirmar si es un patrón genuino o")
        print("       un artefacto de la muestra.")
    elif density['is_anomalous']:
        print("\n⚠️  Se detecta anomalía en N=13, pero:")
        print("   • La distribución general es dispersa")
        print("   • Puede ser fluctuación estadística")
        print("   • Se recomienda aumentar tamaño de muestra")
    elif cv < 0.3:
        print("\n📊 Distribución muestra clustering, pero:")
        print("   • No hay anomalía particular en N=13")
        print("   • El clustering es general, no específico")
        print("   • La estructura es consistente con modelos suaves")
    else:
        print("\n✅ La distribución sigue un patrón ESPERADO:")
        print("   • No hay clustering significativo")
        print("   • No hay anomalía en N=13")
        print("   • Consistente con distribución suave P(N)~exp(-αN)")
        print("\n   ➜ Sin análisis de TODA la base de datos, la 'coherencia")
        print("      espectral' proclamada NO puede ser validada.")
    
    print("\n" + "=" * 78)
    print("✅ Demo completado exitosamente")
    print("=" * 78 + "\n")


if __name__ == "__main__":
    main()
