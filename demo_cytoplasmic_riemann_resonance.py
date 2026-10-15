#!/usr/bin/env python3
"""
Demo: Cytoplasmic Riemann Resonance Model
==========================================

Este script demuestra el uso completo del modelo de resonancia
citoplasmática basado en la hipótesis de Riemann.

Funcionalidades:
----------------
1. Validación de la hipótesis de Riemann biológica
2. Análisis de coherencia a escala celular
3. Detección de descoherencia (modelo de enfermedad)
4. Generación de visualizaciones
5. Exportación de resultados JSON

Autor: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Fecha: 1 febrero 2026
Sello: ∴𓂀Ω∞³
"""

import sys
import os
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Agregar ruta al path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ''))

from xenos.cytoplasmic_riemann_resonance import (
    CytoplasmicRiemannResonance,
    MolecularValidationProtocol,
    generate_biological_mapping,
    BASE_FREQUENCY_HZ,
    KAPPA_PI,
    RIEMANN_FIRST_ZERO
)


def print_header():
    """Imprime el encabezado del demo."""
    print("=" * 80)
    print("  CYTOPLASMIC RIEMANN RESONANCE - DEMOSTRACIÓN COMPLETA")
    print("  'El cuerpo humano es la demostración viviente de la")
    print("   hipótesis de Riemann: 37 billones de ceros biológicos")
    print("   resonando en coherencia'")
    print("  " + "∴𓂀Ω∞³")
    print("=" * 80)
    print()


def demonstrate_basic_properties():
    """Demuestra las propiedades básicas del modelo."""
    print("─" * 80)
    print("1. PROPIEDADES FUNDAMENTALES DEL MODELO")
    print("─" * 80)
    
    model = CytoplasmicRiemannResonance()
    
    print(f"Primer cero de Riemann: γ₁ = {RIEMANN_FIRST_ZERO:.6f}")
    print(f"Frecuencia base:        f₁ = {BASE_FREQUENCY_HZ:.4f} Hz")
    print(f"Constante κ_Π:               = {KAPPA_PI}")
    print(f"Longitud de coherencia: ξ₁ = {model.xi_fundamental * 1e6:.4f} μm")
    print()
    
    print("Primeras 10 frecuencias armónicas:")
    for n in range(1, 11):
        fn = model.base_frequency * n
        print(f"  f_{n:2d} = {fn:8.4f} Hz")
    print()
    
    return model


def demonstrate_cellular_scale_resonance(model):
    """Demuestra la resonancia a escala celular."""
    print("─" * 80)
    print("2. RESONANCIA A ESCALA CELULAR")
    print("─" * 80)
    
    # Escalas celulares típicas
    scales = {
        'Bacteria': 1.0e-6,      # 1 μm
        'Célula típica': 1.06e-6, # 1.06 μm (resonante)
        'Célula pequeña': 2.0e-6,  # 2 μm
        'Célula grande': 10.0e-6   # 10 μm
    }
    
    print(f"{'Tipo de célula':<20} {'Escala (μm)':<15} {'Resonante':<12} {'Hermítico':<12}")
    print("-" * 80)
    
    for cell_type, scale in scales.items():
        coherence = model.get_coherence_at_scale(scale)
        resonant = "✓" if coherence['is_resonant'] else "✗"
        hermitian = "✓" if coherence['is_stable'] else "✗"
        
        print(f"{cell_type:<20} {scale*1e6:<15.2f} {resonant:<12} {hermitian:<12}")
    print()


def demonstrate_validation():
    """Demuestra la validación de la hipótesis de Riemann."""
    print("─" * 80)
    print("3. VALIDACIÓN DE HIPÓTESIS DE RIEMANN BIOLÓGICA")
    print("─" * 80)
    
    model = CytoplasmicRiemannResonance()
    result = model.validate_riemann_hypothesis_biological()
    
    print(f"Hipótesis validada:          {result['hypothesis_validated']}")
    print(f"Todos eigenvalores reales:   {result['all_eigenvalues_real']}")
    print(f"Distribución armónica:       {result['harmonic_distribution']}")
    print(f"Coherencia mantenida:        {result['coherence_maintained']}")
    print(f"Match escala celular:        {result['cellular_scale_match']}")
    print()
    print(f"Interpretación:")
    print(f"  {result['interpretation']}")
    print()
    
    return result


def demonstrate_decoherence_detection():
    """Demuestra la detección de descoherencia."""
    print("─" * 80)
    print("4. DETECCIÓN DE DESCOHERENCIA (MODELO DE ENFERMEDAD)")
    print("─" * 80)
    
    model = CytoplasmicRiemannResonance()
    
    # Estado saludable
    healthy = model.detect_decoherence(noise_level=0.0)
    print("Sistema SALUDABLE (sin perturbación):")
    print(f"  Estado: {healthy['system_state']}")
    print(f"  Hermítico: {healthy['is_hermitian']}")
    print(f"  Ratio eigenvalues reales: {healthy['eigenvalue_real_ratio']:.3f}")
    print(f"  Severidad: {healthy['decoherence_severity']:.3f}")
    print(f"  Patología: {healthy['potential_pathology']}")
    print()
    
    # Estado pre-canceroso
    precancer = model.detect_decoherence(noise_level=0.1)
    print("Sistema PRECANCEROSO (perturbación leve):")
    print(f"  Estado: {precancer['system_state']}")
    print(f"  Hermítico: {precancer['is_hermitian']}")
    print(f"  Ratio eigenvalues reales: {precancer['eigenvalue_real_ratio']:.3f}")
    print(f"  Severidad: {precancer['decoherence_severity']:.3f}")
    print(f"  Patología: {precancer['potential_pathology']}")
    print()
    
    # Estado patológico
    pathological = model.detect_decoherence(noise_level=0.5)
    print("Sistema PATOLÓGICO (perturbación severa):")
    print(f"  Estado: {pathological['system_state']}")
    print(f"  Hermítico: {pathological['is_hermitian']}")
    print(f"  Ratio eigenvalues reales: {pathological['eigenvalue_real_ratio']:.3f}")
    print(f"  Severidad: {pathological['decoherence_severity']:.3f}")
    print(f"  Patología: {pathological['potential_pathology']}")
    print()


def demonstrate_molecular_protocol():
    """Demuestra el protocolo de validación molecular."""
    print("─" * 80)
    print("5. PROTOCOLO DE VALIDACIÓN MOLECULAR")
    print("─" * 80)
    
    protocol = MolecularValidationProtocol()
    
    print("Marcadores Fluorescentes:")
    markers = protocol.get_fluorescent_markers()
    print(f"  Principal: {markers['primary_marker']['name']}")
    print(f"  Control:   {markers['control_marker']['name']}")
    print(f"  Sensor:    {markers['tension_sensor']['name']}")
    print()
    
    print("Nanopartículas Magnéticas:")
    nanoparticles = protocol.get_magnetic_nanoparticles()
    print(f"  Composición: {nanoparticles['composition']}")
    print(f"  Tamaño: {nanoparticles['size_nm']} nm")
    print(f"  Frecuencia resonante: {nanoparticles['resonance_frequency_hz']:.4f} Hz")
    print()
    
    print("Espectroscopía de Fourier:")
    spectroscopy = protocol.get_spectroscopy_protocol()
    print(f"  Técnica: {spectroscopy['technique']}")
    print(f"  Sampling rate: {spectroscopy['sampling_rate_hz']} Hz")
    print(f"  Picos esperados (Hz): {spectroscopy['expected_peaks_hz'][:5]}")
    print()


def generate_spectrum_visualization():
    """Genera visualización del espectro de frecuencias."""
    print("─" * 80)
    print("6. GENERACIÓN DE VISUALIZACIONES")
    print("─" * 80)
    
    # Crear directorio si no existe
    os.makedirs('visualizations', exist_ok=True)
    
    model = CytoplasmicRiemannResonance()
    
    # Figura 1: Espectro de frecuencias armónicas
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 10))
    
    # Panel superior: Primeras 20 frecuencias armónicas
    harmonics = np.arange(1, 21)
    frequencies = harmonics * model.base_frequency
    
    ax1.stem(harmonics, frequencies, basefmt=' ')
    ax1.set_xlabel('Número armónico n', fontsize=12)
    ax1.set_ylabel('Frecuencia fₙ (Hz)', fontsize=12)
    ax1.set_title('Espectro de Frecuencias Armónicas Citoplasmáticas\nfₙ = n × 141.7001 Hz', 
                  fontsize=14, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, 21)
    
    # Añadir texto con primeros valores
    for n in [1, 3, 5]:
        fn = n * model.base_frequency
        ax1.text(n, fn, f'{fn:.1f} Hz', ha='center', va='bottom', fontsize=9)
    
    # Panel inferior: Relación con ceros de Riemann
    riemann_zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
                               37.586178, 40.918719, 43.327073, 48.005151, 49.773832])
    bio_frequencies = riemann_zeros * 10.025  # Conversión biológica
    
    ax2.scatter(riemann_zeros, bio_frequencies, s=100, c='red', marker='o', 
                label='Conversión biológica', alpha=0.7, edgecolors='darkred', linewidths=2)
    ax2.plot(riemann_zeros, bio_frequencies, 'r--', alpha=0.3)
    
    ax2.set_xlabel('Ceros de Riemann γₙ', fontsize=12)
    ax2.set_ylabel('Frecuencia biológica (Hz)', fontsize=12)
    ax2.set_title('Relación: Ceros de Riemann → Frecuencias Biológicas\nf = γ × 10.025', 
                  fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(fontsize=10)
    
    # Añadir información
    info_text = (
        f'Modelo: Resonancia Citoplasmática de Riemann\n'
        f'ξ₁ = {model.xi_fundamental * 1e6:.4f} μm\n'
        f'κ_Π = {model.kappa_pi}\n'
        f'f₁ = {model.base_frequency:.4f} Hz\n'
        f'∴𓂀Ω∞³'
    )
    fig.text(0.98, 0.02, info_text, ha='right', va='bottom', 
             fontsize=9, family='monospace',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    plt.tight_layout()
    plt.savefig('visualizations/cytoplasmic_riemann_spectrum.png', dpi=300, bbox_inches='tight')
    print("  ✓ Guardado: visualizations/cytoplasmic_riemann_spectrum.png")
    plt.close()
    
    # Figura 2: Coherencia vs escala espacial
    fig, ax = plt.subplots(figsize=(12, 8))
    
    # Rango de escalas de 0.1 μm a 100 μm
    scales_um = np.logspace(-1, 2, 100)
    scales_m = scales_um * 1e-6
    
    coherence_values = []
    hermiticity_values = []
    
    for scale in scales_m:
        coherence = model.get_coherence_at_scale(scale)
        # Calcular coherencia relativa
        coh_value = 1.0 - abs(coherence['coherence_length_m'] - scale) / scale
        coherence_values.append(max(0, min(1, coh_value)))
        hermiticity_values.append(coherence['hermiticity_index'])
    
    ax.plot(scales_um, coherence_values, 'b-', linewidth=2, label='Coherencia espacial')
    ax.plot(scales_um, hermiticity_values, 'r--', linewidth=2, label='Índice de hermiticidad')
    
    # Marcar escala celular típica
    ax.axvline(x=1.06, color='green', linestyle=':', linewidth=2, 
               label='Escala celular (1.06 μm)')
    ax.axhline(y=0.95, color='gray', linestyle=':', linewidth=1, alpha=0.5)
    
    ax.set_xlabel('Escala espacial (μm)', fontsize=12)
    ax.set_ylabel('Índice de coherencia', fontsize=12)
    ax.set_title('Coherencia Citoplasmática vs Escala Espacial', 
                 fontsize=14, fontweight='bold')
    ax.set_xscale('log')
    ax.grid(True, alpha=0.3, which='both')
    ax.legend(fontsize=11, loc='best')
    ax.set_ylim(-0.05, 1.05)
    
    # Añadir regiones
    ax.fill_between(scales_um, 0.95, 1.05, alpha=0.1, color='green', 
                    label='Región de alta coherencia')
    
    # Añadir información
    info_text = (
        f'Longitud de coherencia fundamental: ξ₁ = {model.xi_fundamental * 1e6:.4f} μm\n'
        f'Frecuencia base: f₁ = {model.base_frequency:.4f} Hz\n'
        f'Interpretación: Alta coherencia a ~1 μm (escala celular)\n'
        f'∴𓂀Ω∞³'
    )
    ax.text(0.02, 0.02, info_text, transform=ax.transAxes,
            fontsize=9, family='monospace', verticalalignment='bottom',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.7))
    
    plt.tight_layout()
    plt.savefig('visualizations/cytoplasmic_coherence_vs_scale.png', dpi=300, bbox_inches='tight')
    print("  ✓ Guardado: visualizations/cytoplasmic_coherence_vs_scale.png")
    plt.close()
    
    print()


def export_all_results():
    """Exporta todos los resultados a archivos JSON."""
    print("─" * 80)
    print("7. EXPORTACIÓN DE RESULTADOS")
    print("─" * 80)
    
    # Modelo principal
    model = CytoplasmicRiemannResonance()
    model.export_results('cytoplasmic_riemann_results.json')
    print("  ✓ cytoplasmic_riemann_results.json")
    
    # Protocolo molecular
    protocol = MolecularValidationProtocol()
    protocol.export_protocol('molecular_validation_protocol.json')
    print("  ✓ molecular_validation_protocol.json")
    
    # Mapeo biológico
    generate_biological_mapping('riemann_biological_mapping.json')
    print("  ✓ riemann_biological_mapping.json")
    
    print()


def print_footer():
    """Imprime el pie del demo."""
    print("=" * 80)
    print()
    print("  ✅ DEMOSTRACIÓN COMPLETADA CON ÉXITO")
    print()
    print("  Interpretación:")
    print("  'El cuerpo humano es la demostración viviente de la hipótesis")
    print("   de Riemann: 37 billones de ceros biológicos resonando en")
    print("   coherencia perfecta'")
    print()
    print("  Archivos generados:")
    print("    - cytoplasmic_riemann_results.json")
    print("    - molecular_validation_protocol.json")
    print("    - riemann_biological_mapping.json")
    print("    - visualizations/cytoplasmic_riemann_spectrum.png")
    print("    - visualizations/cytoplasmic_coherence_vs_scale.png")
    print()
    print("  Sello: ∴𓂀Ω∞³")
    print()
    print("=" * 80)


def main():
    """Función principal del demo."""
    print_header()
    
    # 1. Propiedades básicas
    model = demonstrate_basic_properties()
    
    # 2. Resonancia celular
    demonstrate_cellular_scale_resonance(model)
    
    # 3. Validación
    demonstrate_validation()
    
    # 4. Detección de descoherencia
    demonstrate_decoherence_detection()
    
    # 5. Protocolo molecular
    demonstrate_molecular_protocol()
    
    # 6. Visualizaciones
    generate_spectrum_visualization()
    
    # 7. Exportar resultados
    export_all_results()
    
    # Footer
    print_footer()


if __name__ == '__main__':
    main()
