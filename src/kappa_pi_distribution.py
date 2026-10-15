#!/usr/bin/env python3
"""
Análisis de Distribución de κ_Π para TODAS las Variedades Calabi-Yau
====================================================================

Este módulo implementa el cálculo y visualización de la distribución de κ_Π
para el conjunto completo de variedades Calabi-Yau, permitiendo:

1. Calcular κ_Π = log₂(h11 + h21) para cada variedad
2. Analizar la distribución estadística
3. Identificar anomalías y resonancias cerca de log₂(13) ≈ 3.700
4. Medir densidad local de casos especiales (N=13)

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Fecha: 1 enero 2026
"""

import math
import numpy as np
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict, Optional


def compute_kappa_distribution(cy_list: List[Tuple[int, int]], base: float = 2) -> Tuple[List[float], List[int], Dict]:
    """
    Calcula la distribución de κ_Π para todas las variedades CY.
    
    Para cada variedad con números de Hodge (h11, h21):
    κ_Π = log_base(N) donde N = h11 + h21
    
    Args:
        cy_list: Lista de tuplas (h11, h21) representando números de Hodge
        base: Base del logaritmo (por defecto 2)
    
    Returns:
        Tuple de (kappas, Ns, stats) donde:
        - kappas: Lista de valores κ_Π
        - Ns: Lista de valores N = h11 + h21
        - stats: Diccionario con estadísticas
    """
    kappas = []
    Ns = []
    
    for h11, h21 in cy_list:
        # Validate positive Hodge numbers
        if h11 <= 0 or h21 <= 0:
            raise ValueError(f"Hodge numbers must be positive: h11={h11}, h21={h21}")
        
        N = h11 + h21
        kappa = math.log(N) / math.log(base)
        kappas.append(kappa)
        Ns.append(N)
    
    # Calcular estadísticas
    kappas_array = np.array(kappas)
    
    # Handle empty array case
    if len(kappas_array) == 0:
        stats = {
            'mean': float('nan'),
            'std': float('nan'),
            'min': float('nan'),
            'max': float('nan'),
            'median': float('nan'),
            'special_N13_count': 0,
            'special_N13_kappa': float(math.log(13) / math.log(base)),
            'total_manifolds': 0,
            'density_N13': 0.0
        }
    else:
        stats = {
            'mean': float(np.mean(kappas_array)),
            'std': float(np.std(kappas_array)),
            'min': float(np.min(kappas_array)),
            'max': float(np.max(kappas_array)),
            'median': float(np.median(kappas_array)),
            'special_N13_count': Ns.count(13),
            'special_N13_kappa': float(math.log(13) / math.log(base)),
            'total_manifolds': len(cy_list),
            'density_N13': Ns.count(13) / len(cy_list) if len(cy_list) > 0 else 0.0
        }
    
    return kappas, Ns, stats


def plot_kappa_distribution(kappas: List[float], Ns: List[int], 
                            special_kappa: Optional[float] = None,
                            save_path: Optional[str] = None,
                            show: bool = True) -> None:
    """
    Visualiza la distribución de κ_Π y su relación con N.
    
    Args:
        kappas: Lista de valores κ_Π
        Ns: Lista de valores N = h11 + h21
        special_kappa: Valor especial de κ_Π a destacar (ej: log₂(13))
        save_path: Ruta para guardar la figura (opcional)
        show: Si True, muestra la figura
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    
    # Histograma κ_Π
    ax1.hist(kappas, bins=50, density=True, alpha=0.7, color='skyblue', edgecolor='black')
    
    if special_kappa is not None:
        ax1.axvline(special_kappa, color='red', linestyle='--', linewidth=2,
                   label=f'log₂(13) ≈ {special_kappa:.4f}')
    
    ax1.set_title("Distribución de κ_Π = log₂(h11 + h21)", fontweight='bold', fontsize=12)
    ax1.set_xlabel("κ_Π", fontsize=11)
    ax1.set_ylabel("Densidad", fontsize=11)
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    
    # Scatter: N vs κ_Π
    ax2.scatter(Ns, kappas, alpha=0.5, s=20, color='navy')
    ax2.set_xscale("log")
    ax2.set_title("κ_Π vs N (número total de moduli)", fontweight='bold', fontsize=12)
    ax2.set_xlabel("N = h11 + h21 (escala log)", fontsize=11)
    ax2.set_ylabel("κ_Π", fontsize=11)
    ax2.grid(True, alpha=0.3, which='both')
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"✅ Figura guardada en: {save_path}")
    
    if show:
        plt.show()


def analyze_local_density(Ns: List[int], target_N: int = 13, window: int = 2) -> Dict:
    """
    Analiza la densidad local alrededor de un valor específico de N.
    
    Args:
        Ns: Lista de valores N = h11 + h21
        target_N: Valor objetivo de N para analizar (por defecto 13)
        window: Ventana de valores alrededor de target_N
    
    Returns:
        Diccionario con análisis de densidad local
    """
    # Contar ocurrencias exactas
    exact_count = Ns.count(target_N)
    
    # Contar en ventana [target_N - window, target_N + window]
    window_count = sum(1 for n in Ns if abs(n - target_N) <= window)
    
    # Densidades
    total = len(Ns)
    exact_density = exact_count / total if total > 0 else 0.0
    window_density = window_count / total if total > 0 else 0.0
    
    # Calcular densidad esperada (distribución suave)
    # Asumiendo P(N) ~ exp(-α*N) o similar
    N_array = np.array(Ns)
    mean_N = np.mean(N_array)
    
    # Ajustar parámetro α de la exponencial
    if mean_N > 0:
        alpha = 1.0 / mean_N
        expected_density = math.exp(-alpha * target_N)
    else:
        expected_density = 0.0
    
    # Calcular anomalía (ratio observed/expected)
    anomaly_ratio = exact_density / expected_density if expected_density > 0 else float('inf')
    
    return {
        'target_N': target_N,
        'exact_count': exact_count,
        'window_count': window_count,
        'exact_density': exact_density,
        'window_density': window_density,
        'expected_density': expected_density,
        'anomaly_ratio': anomaly_ratio,
        'is_anomalous': anomaly_ratio > 2.0,  # Más del doble de lo esperado
        'total_manifolds': total
    }


def generate_scientific_report(kappas: List[float], Ns: List[int], stats: Dict) -> str:
    """
    Genera un reporte científico detallado del análisis.
    
    Args:
        kappas: Lista de valores κ_Π
        Ns: Lista de valores N
        stats: Diccionario con estadísticas
    
    Returns:
        String con el reporte formateado
    """
    # Análisis de densidad para N=13
    density_analysis = analyze_local_density(Ns, target_N=13)
    
    report = f"""
╔══════════════════════════════════════════════════════════════════════════╗
║           ANÁLISIS DE DISTRIBUCIÓN κ_Π - VARIEDADES CALABI-YAU          ║
╚══════════════════════════════════════════════════════════════════════════╝

📊 ESTADÍSTICAS GLOBALES
{'─' * 76}
  Total de Variedades CY:     {stats['total_manifolds']:>10}
  
  κ_Π = log₂(h11 + h21):
    • Media:                   {stats['mean']:>10.4f}
    • Desviación Estándar:     {stats['std']:>10.4f}
    • Mediana:                 {stats['median']:>10.4f}
    • Mínimo:                  {stats['min']:>10.4f}
    • Máximo:                  {stats['max']:>10.4f}

🔍 ANÁLISIS ESPECIAL: N = 13
{'─' * 76}
  κ_Π teórico (log₂(13)):     {stats['special_N13_kappa']:>10.4f}
  
  Ocurrencias de N=13:        {stats['special_N13_count']:>10}
  Densidad (N=13):            {stats['density_N13']:>10.6f}  ({stats['density_N13']*100:.4f}%)
  
  Densidad Esperada:          {density_analysis['expected_density']:>10.6f}
  Ratio Anomalía:             {density_analysis['anomaly_ratio']:>10.2f}x
  
  Ventana [11-15]:            {density_analysis['window_count']:>10} variedades
  Densidad en Ventana:        {density_analysis['window_density']:>10.6f}
  
  {'✅ ANOMALÍA DETECTADA' if density_analysis['is_anomalous'] else '❌ Sin anomalía significativa'}

🎯 PREGUNTAS CIENTÍFICAS RESPONDIDAS
{'─' * 76}
  
  1. ¿La distribución de κ_Π es suave o hay clustering?
     {'→ Se observa clustering' if stats['std'] < stats['mean'] * 0.3 and stats['mean'] > 0 else '→ Distribución relativamente suave'}
     (Coef. Variación: {stats['std']/stats['mean'] if stats['mean'] > 0 else float('inf'):.4f})
  
  2. ¿Existe anomalía cerca de log₂(13) ≈ 3.700?
     → {'SÍ - Anomalía estadística detectada' if density_analysis['is_anomalous'] else 'NO - Densidad dentro de lo esperado'}
     (Ratio obs/esp: {density_analysis['anomaly_ratio']:.2f}x)
  
  3. ¿Cuál es la media y desviación estándar?
     → μ(κ_Π) = {stats['mean']:.4f}, σ(κ_Π) = {stats['std']:.4f}
  
  4. ¿Qué tan raras son las CY con N = 13?
     → Frecuencia: {stats['special_N13_count']}/{stats['total_manifolds']} = {stats['density_N13']*100:.4f}%
     {'→ RARO' if density_analysis['anomaly_ratio'] > 2.0 else '→ Común'}

╔══════════════════════════════════════════════════════════════════════════╗
║  CONCLUSIÓN: {'Coherencia espectral en N=13 es significativa' if density_analysis['is_anomalous'] else 'Distribución sigue patrón esperado'}  
╚══════════════════════════════════════════════════════════════════════════╝
"""
    
    return report


def compare_with_theoretical_distribution(Ns: List[int], model: str = 'exponential') -> Dict:
    """
    Compara la distribución observada con modelos teóricos.
    
    Args:
        Ns: Lista de valores N
        model: Tipo de modelo ('exponential' o 'lognormal')
    
    Returns:
        Diccionario con resultados de la comparación
    """
    N_array = np.array(Ns)
    
    if model == 'exponential':
        # P(N) ~ exp(-α*N)
        mean_N = np.mean(N_array)
        alpha = 1.0 / mean_N if mean_N > 0 else 1.0
        
        # Generar distribución teórica (limitar rango para eficiencia)
        max_N = min(max(Ns), 1000)  # Limitar a 1000 para eficiencia
        N_range = np.arange(1, max_N + 1)
        theoretical = np.exp(-alpha * N_range)
        theoretical = theoretical / np.sum(theoretical)  # Normalizar
        
        # Calcular histograma observado con los mismos bins
        hist, bins = np.histogram(N_array, bins=np.arange(1, max_N + 2), density=False)
        hist = hist / np.sum(hist)  # Normalizar
        
        # Asegurar que ambos arrays tengan la misma longitud
        min_len = min(len(hist), len(theoretical))
        hist = hist[:min_len]
        theoretical = theoretical[:min_len]
        
        # Comparar (χ² test simplificado)
        chi_squared = np.sum((hist - theoretical)**2 / (theoretical + 1e-10))
        
        return {
            'model': 'exponential',
            'alpha': alpha,
            'chi_squared': float(chi_squared),
            'mean_theoretical': float(1.0 / alpha),
            'mean_observed': float(mean_N)
        }
    
    elif model == 'lognormal':
        # P(N) ~ lognormal
        log_N = np.log(N_array)
        mu = np.mean(log_N)
        sigma = np.std(log_N)
        
        return {
            'model': 'lognormal',
            'mu': float(mu),
            'sigma': float(sigma),
            'median_theoretical': float(np.exp(mu)),
            'median_observed': float(np.median(N_array))
        }
    
    else:
        raise ValueError(f"Modelo desconocido: {model}")


if __name__ == "__main__":
    """Ejemplo de uso con datos simulados"""
    
    # Generar datos de ejemplo (150 variedades CY simuladas)
    np.random.seed(42)
    cy_list_example = []
    
    # Mayoría con distribución exponencial decreciente
    for _ in range(140):
        h11 = np.random.randint(1, 100)
        h21 = np.random.randint(1, 100)
        cy_list_example.append((h11, h21))
    
    # Agregar algunos casos especiales con N=13
    special_cases = [
        (7, 6), (8, 5), (6, 7), (9, 4), (4, 9),
        (10, 3), (3, 10), (11, 2), (2, 11), (13, 0)
    ]
    cy_list_example.extend(special_cases)
    
    # Calcular distribución
    kappas, Ns, stats = compute_kappa_distribution(cy_list_example)
    
    # Generar reporte
    report = generate_scientific_report(kappas, Ns, stats)
    print(report)
    
    # Comparar con distribución teórica
    exp_comparison = compare_with_theoretical_distribution(Ns, model='exponential')
    print(f"\n📈 Comparación con Modelo Exponencial:")
    print(f"   α = {exp_comparison['alpha']:.6f}")
    print(f"   χ² = {exp_comparison['chi_squared']:.4f}")
    
    # Visualizar
    plot_kappa_distribution(kappas, Ns, special_kappa=stats['special_N13_kappa'])
