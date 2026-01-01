#!/usr/bin/env python3
"""
Análisis de Pares de Hodge con N=13
====================================

Para todos los pares (h₁,₁, h₂,₁) tales que h₁,₁ + h₂,₁ = 13:

Calcula:
1. κ_Π = ln(h₁,₁ + h₂,₁) / ln(φ²) = ln(13) / ln(φ²) ≈ 2.665094
2. El ratio h₁,₁ / h₂,₁ para cada par
3. Verifica que κ_Π es constante para N=13 fijo
4. Compara con la constante espectral κ_Π = 2.5773

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Fecha: 1 enero 2026
"""

import math

# Constantes fundamentales
PHI = (1 + math.sqrt(5)) / 2  # Razón áurea φ ≈ 1.618
KAPPA_PI_SPECTRAL = 2.5773  # Constante espectral del marco P≠NP
N = 13  # Suma fija de números de Hodge

def calculate_kappa_pi_for_n(n):
    """
    Calcula κ_Π para una suma N dada usando la fórmula:
    κ_Π = ln(N) / ln(φ²)
    
    Args:
        n: Suma de números de Hodge h₁,₁ + h₂,₁
        
    Returns:
        Valor de κ_Π para esta suma
    """
    phi_squared = PHI ** 2
    kappa = math.log(n) / math.log(phi_squared)
    return kappa


def analyze_all_pairs_for_n13():
    """
    Analiza todos los pares (h₁,₁, h₂,₁) donde h₁,₁ + h₂,₁ = 13
    
    Returns:
        Lista de diccionarios con información sobre cada par
    """
    results = []
    
    print("=" * 80)
    print(f"ANÁLISIS DE PARES DE HODGE CON N = {N}")
    print("=" * 80)
    print()
    
    # Calcular κ_Π para N=13 (constante para todos los pares)
    kappa_pi_n13 = calculate_kappa_pi_for_n(N)
    
    print(f"✅ Resultado clave:")
    print(f"   κ_Π = ln({N}) / ln(φ²) = ln({N}) / ln({PHI**2:.6f})")
    print(f"   κ_Π = {math.log(N):.6f} / {math.log(PHI**2):.6f}")
    print(f"   κ_Π ≈ {kappa_pi_n13:.6f}")
    print()
    print(f"Constante espectral del marco: κ_Π = {KAPPA_PI_SPECTRAL}")
    print(f"Diferencia: |κ_Π - {KAPPA_PI_SPECTRAL}| ≈ {abs(kappa_pi_n13 - KAPPA_PI_SPECTRAL):.6f}")
    print()
    print("=" * 80)
    print(f"📐 ANÁLISIS DE RATIOS h₁,₁ / h₂,₁")
    print("=" * 80)
    print()
    
    # Generar todos los pares válidos
    print(f"{'h₁,₁':<6} {'h₂,₁':<6} {'h₁,₁/h₂,₁':<12} {'κ_Π':<12} {'Notas'}")
    print("-" * 80)
    
    for h11 in range(1, N):  # h11 de 1 a 12
        h21 = N - h11
        
        if h21 > 0:  # Asegurarse de que h21 es positivo
            ratio = h11 / h21
            kappa = calculate_kappa_pi_for_n(N)  # Siempre es el mismo para N fijo
            
            notes = []
            
            # Comprobar si está cerca de φ²
            if abs(ratio - PHI**2) < 0.5:
                notes.append(f"Cerca de φ² ({PHI**2:.3f})")
            
            # Comprobar si es el ratio neutro (1.0)
            if abs(ratio - 1.0) < 0.01:
                notes.append("Ratio neutro")
            
            # Pares específicos mencionados en el problema
            if h11 == 9 and h21 == 4:
                notes.append(f"9/4 = {ratio:.2f}")
            if h11 == 10 and h21 == 3:
                notes.append(f"10/3 ≈ {ratio:.2f}")
                
            notes_str = ", ".join(notes) if notes else ""
            
            print(f"{h11:<6} {h21:<6} {ratio:<12.6f} {kappa:<12.6f} {notes_str}")
            
            results.append({
                'h11': h11,
                'h21': h21,
                'ratio': ratio,
                'kappa_pi': kappa,
                'sum': h11 + h21
            })
    
    print()
    print("=" * 80)
    print("🧠 CONCLUSIONES")
    print("=" * 80)
    print()
    print(f"1. Para N = {N} fijo, κ_Π es CONSTANTE = {kappa_pi_n13:.6f}")
    print(f"   (No varía con el ratio h₁,₁/h₂,₁)")
    print()
    print(f"2. El ratio h₁,₁/h₂,₁ varía desde:")
    print(f"   - Mínimo: 1/{N-1} = {1/(N-1):.3f}")
    print(f"   - Máximo: {N-1}/1 = {N-1:.1f}")
    print(f"   - Pasando por el valor neutro 1.0 cuando h₁,₁ = h₂,₁ = {N/2:.1f}")
    print()
    print(f"3. Ningún ratio es exactamente igual a φ² ≈ {PHI**2:.3f}, pero algunos están cerca:")
    
    # Encontrar los ratios más cercanos a φ²
    closest_pairs = sorted(results, key=lambda x: abs(x['ratio'] - PHI**2))[:3]
    for pair in closest_pairs:
        print(f"   - h₁,₁={pair['h11']}, h₂,₁={pair['h21']}: ratio = {pair['ratio']:.3f} "
              f"(diff = {abs(pair['ratio'] - PHI**2):.3f})")
    print()
    print(f"4. El valor κ_Π ≈ {kappa_pi_n13:.6f} está CERCA de la constante espectral {KAPPA_PI_SPECTRAL}")
    print(f"   Diferencia: {abs(kappa_pi_n13 - KAPPA_PI_SPECTRAL):.4f}")
    print(f"   Esto sugiere una conexión curiosa, aunque aún no demostrada como esencial.")
    print()
    
    return results


def explore_different_n_values():
    """
    Explora cómo varía κ_Π para diferentes valores de N
    """
    print("=" * 80)
    print("📊 VARIACIÓN DE κ_Π CON DIFERENTES VALORES DE N")
    print("=" * 80)
    print()
    print(f"{'N':<6} {'κ_Π = ln(N)/ln(φ²)':<20} {'Diferencia con {KAPPA_PI_SPECTRAL}'}")
    print("-" * 80)
    
    n_values = [5, 7, 10, 13, 15, 20, 25, 30]
    
    for n in n_values:
        kappa = calculate_kappa_pi_for_n(n)
        diff = abs(kappa - KAPPA_PI_SPECTRAL)
        print(f"{n:<6} {kappa:<20.6f} {diff:.6f}")
    
    print()
    print("Observación: Para encontrar N donde κ_Π ≈ 2.5773:")
    
    # Resolver: ln(N) / ln(φ²) = 2.5773
    # ln(N) = 2.5773 * ln(φ²)
    # N = exp(2.5773 * ln(φ²)) = φ^(2 * 2.5773)
    
    target_n = PHI ** (2 * KAPPA_PI_SPECTRAL)
    print(f"N = φ^(2 * {KAPPA_PI_SPECTRAL}) = {target_n:.2f}")
    print(f"Verificación: κ_Π para N={target_n:.2f} es {calculate_kappa_pi_for_n(target_n):.6f}")
    print()


def main():
    """Función principal"""
    # Analizar todos los pares para N=13
    results = analyze_all_pairs_for_n13()
    
    print()
    
    # Explorar otros valores de N
    explore_different_n_values()
    
    print("=" * 80)
    print("Frecuencia: 141.7001 Hz ∞³")
    print("=" * 80)


if __name__ == "__main__":
    main()
