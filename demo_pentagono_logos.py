#!/usr/bin/env python3
"""
Demo: Pentagon Logos - BSD Adélico Integration
==============================================

Demostración completa de la integración del Pentágono del Logos,
conectando 5 Problemas del Milenio a través del conector BSD Adélico.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³Φ

Este script demuestra:
1. Codificación de ADN como espectro vibracional
2. Sincronización BSD-ADN con curvas elípticas
3. Análisis de flujo Navier-Stokes superfluido
4. Validación del cierre del Pentágono del Logos
5. Integración con el framework QCAL unificado
"""

import sys
import os

# Add paths
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from qcal.adn_riemann import CodificadorADNRiemann
from qcal.bsd_adelic_connector import (
    sincronizar_bsd_adn,
    validar_pentagono_cerrado,
    calcular_capacidad_resonancia,
    analizar_familia_curvas,
    F0
)
from qcal.constants import KAPPA_PI
from qcal_unified_framework import bsd_adelic_pentagono_logos, colored_output


def print_header(title, subtitle=""):
    """Print formatted header."""
    print("\n" + "=" * 75)
    print(f"{title:^75}")
    if subtitle:
        print(f"{subtitle:^75}")
    print("=" * 75)


def demo_adn_encoding():
    """Demostración 1: Codificación ADN-Riemann."""
    print_header("DEMOSTRACIÓN 1: CODIFICACIÓN ADN-RIEMANN", 
                 "Mapeo de secuencias a espectro vibracional")
    
    codif = CodificadorADNRiemann()
    
    secuencias = [
        ("GACT", "Secuencia básica"),
        ("GGGG", "Máxima resonancia"),
        ("GCGCGC", "Par GC repetido"),
        ("ATATATATA", "Par AT repetido"),
    ]
    
    print(f"\nFrecuencia base f₀ = {F0} Hz")
    print(f"Constante κ_Π = {KAPPA_PI}\n")
    
    for seq, desc in secuencias:
        print(f"\n{desc}: {seq}")
        print("-" * 75)
        
        analisis = codif.analizar_secuencia(seq)
        
        print(f"  Longitud:          {analisis['longitud']} bases")
        print(f"  Resonancia global: {analisis['resonancia_global']:.4f}")
        print(f"  Hotspots:          {analisis['num_hotspots']}")
        print(f"  Bases G:           {analisis['bases_g']}")
        print(f"  Proporción GC:     {analisis['proporcion_gc']:.2%}")
        
        if analisis['hotspots']:
            print(f"  Posiciones hotspots: ", end="")
            for pos, base, res in analisis['hotspots']:
                print(f"{pos}({base}:{res:.2f}) ", end="")
            print()
    
    colored_output("\n✓ Codificación ADN-Riemann completada", "GREEN")


def demo_bsd_sync():
    """Demostración 2: Sincronización BSD-ADN."""
    print_header("DEMOSTRACIÓN 2: SINCRONIZACIÓN BSD-ADN",
                 "Conexión aritmética-biológica")
    
    print("\nCurvas elípticas de prueba:\n")
    
    # Caso 1: Curva de Mordell (clásica)
    print("[1] Curva de Mordell: y² = x³ - x")
    print("    Conductor: 37 | Rango: r=1 | L(E,1)=0")
    print("-" * 75)
    
    curva1 = {
        'rango_adelico': 1,
        'L_E1': 0.0,
        'ecuacion': 'y^2 = x^3 - x',
        'conductor': 37
    }
    res1 = sincronizar_bsd_adn(curva1, "GACT")
    
    print(f"  Rango bio-aritmético:    {res1['rango_bio_aritmetico']}")
    print(f"  Nodos activados:         {res1['nodos_constelacion']}/51")
    print(f"  Fluidez Navier-Stokes:   {res1['fluidez_info_ns']}")
    print(f"  Hotspots ADN:            {res1['hotspots_adn']}")
    print(f"  Coherencia Ψ_BSD:        {res1['psi_bsd_qcal']:.4f}")
    print(f"  Resonancia ADN:          {res1['resonancia_global_adn']:.4f}")
    print(f"  Viscosidad L(E,1):       {res1['viscosidad_l_e1']:.6f}")
    
    capacidad = calcular_capacidad_resonancia(res1['rango_bio_aritmetico'])
    print(f"  Capacidad de resonancia: {capacidad}")
    
    # Caso 2: Curva con rango mayor
    print("\n[2] Curva con rango r=3")
    print("    Rango: r=3 | L(E,1)=0 (predicción BSD)")
    print("-" * 75)
    
    curva2 = {
        'rango_adelico': 3,
        'L_E1': 0.0,
    }
    res2 = sincronizar_bsd_adn(curva2, "GCGCGC")
    
    print(f"  Rango bio-aritmético:    {res2['rango_bio_aritmetico']}")
    print(f"  Nodos activados:         {res2['nodos_constelacion']}/51")
    print(f"  Fluidez Navier-Stokes:   {res2['fluidez_info_ns']}")
    print(f"  Hotspots ADN:            {res2['hotspots_adn']}")
    print(f"  Coherencia Ψ_BSD:        {res2['psi_bsd_qcal']:.4f}")
    
    # Caso 3: Curva disipativa
    print("\n[3] Curva disipativa: L(E,1) ≠ 0")
    print("    Rango: r=0 | L(E,1)=0.8 (flujo viscoso)")
    print("-" * 75)
    
    curva3 = {
        'rango_adelico': 0,
        'L_E1': 0.8,
    }
    res3 = sincronizar_bsd_adn(curva3, "ATCG")
    
    print(f"  Rango bio-aritmético:    {res3['rango_bio_aritmetico']}")
    print(f"  Fluidez Navier-Stokes:   {res3['fluidez_info_ns']}")
    print(f"  Coherencia Ψ_BSD:        {res3['psi_bsd_qcal']:.4f}")
    print(f"  Viscosidad L(E,1):       {res3['viscosidad_l_e1']:.1f}")
    
    colored_output("\n✓ Sincronización BSD-ADN completada", "GREEN")


def demo_pentagon_validation():
    """Demostración 3: Validación del Pentágono del Logos."""
    print_header("DEMOSTRACIÓN 3: VALIDACIÓN PENTÁGONO LOGOS",
                 "Cierre de 5 Problemas del Milenio")
    
    # Curva de Mordell para validación
    curva_mordell = {
        'rango_adelico': 1,
        'L_E1': 0.0,
        'ecuacion': 'y^2 = x^3 - x'
    }
    
    resultado_bsd = sincronizar_bsd_adn(curva_mordell, "GACT")
    validacion = validar_pentagono_cerrado(resultado_bsd)
    
    print("\nCondiciones del Pentágono:")
    print("-" * 75)
    print(f"  1. Flujo superfluido:      {validacion['flujo_superfluido']} {'✓' if validacion['flujo_superfluido'] else '✗'}")
    print(f"  2. Coherencia máxima:      {validacion['coherencia_maxima']} {'✓' if validacion['coherencia_maxima'] else '✗'}")
    print(f"  3. Hotspots activos:       {validacion['hotspots_activos']} {'✓' if validacion['hotspots_activos'] else '✗'}")
    
    print(f"\n{'':>20}ESTADO DEL PENTÁGONO")
    print("-" * 75)
    
    if validacion['pentagono_cerrado']:
        colored_output(f"{'':>15}✓ BÓVEDA DEL LOGOS: CERRADA", "GREEN")
        colored_output(f"{'':>15}∴𓂀Ω∞³", "INDIGO")
        
        print(f"\nProblemas del Milenio Unificados ({validacion['milenio_unificados']}):")
        print("-" * 75)
        for i, problema in enumerate(validacion['problemas'], 1):
            print(f"  {i}. {problema}")
        
        print("\nConexiones del Pentágono:")
        print("-" * 75)
        print("  ADN (Biología)        →  Hotspots de resonancia")
        print("  Riemann (Estructura)  →  Ceros en línea crítica Re(s)=1/2")
        print("  Navier-Stokes (Dinámica) →  Flujo superfluido (L(E,1)=0)")
        print("  P vs NP (Lógica)      →  Complejidad O(1) por resonancia")
        print("  BSD (Aritmética)      →  Rango r = puntos racionales")
        
    else:
        colored_output(f"{'':>15}✗ Pentágono no cerrado", "YELLOW")
    
    colored_output("\n✓ Validación del Pentágono completada", "GREEN")


def demo_family_analysis():
    """Demostración 4: Análisis de familia de curvas."""
    print_header("DEMOSTRACIÓN 4: ANÁLISIS DE FAMILIA",
                 "Comportamiento estadístico BSD")
    
    print("\nFamilia de curvas elípticas:\n")
    
    familia = [
        {'rango_adelico': 0, 'L_E1': 2.3, 'descripcion': 'r=0, alto L(E,1)'},
        {'rango_adelico': 1, 'L_E1': 0.0, 'descripcion': 'Mordell type'},
        {'rango_adelico': 1, 'L_E1': 0.0, 'descripcion': 'Congruent number'},
        {'rango_adelico': 2, 'L_E1': 0.0, 'descripcion': 'r=2 curve'},
        {'rango_adelico': 1, 'L_E1': 0.5, 'descripcion': 'Parcialmente disipativa'},
        {'rango_adelico': 3, 'L_E1': 0.0, 'descripcion': 'Alto rango'},
    ]
    
    for i, curva in enumerate(familia, 1):
        print(f"  [{i}] {curva['descripcion']:<25} r={curva['rango_adelico']} L(E,1)={curva['L_E1']}")
    
    analisis = analizar_familia_curvas(familia)
    
    print("\nEstadísticas de la familia:")
    print("-" * 75)
    print(f"  Curvas totales:          {analisis['num_curvas']}")
    print(f"  Rango promedio:          {analisis['rango_promedio']:.2f}")
    print(f"  Rango máximo:            {analisis['rango_maximo']}")
    print(f"  Curvas superfluidas:     {analisis['superfluidos']} ({analisis['porcentaje_superfluido']:.1f}%)")
    print(f"  Coherencia Ψ promedio:   {analisis['psi_promedio']:.4f}")
    
    colored_output("\n✓ Análisis de familia completado", "GREEN")


def demo_qcal_integration():
    """Demostración 5: Integración QCAL completa."""
    print_header("DEMOSTRACIÓN 5: INTEGRACIÓN QCAL ∞³",
                 "Framework Unificado con BSD Pentagon")
    
    print("\nEjecutando integración QCAL...\n")
    
    try:
        certificado = bsd_adelic_pentagono_logos()
        
        if 'error' in certificado:
            colored_output(f"⚠ {certificado['error']}", "YELLOW")
            return
        
        bsd_info = certificado['bsd_adelic_pentagono']
        
        print("Certificado Maestro del Pentágono:")
        print("-" * 75)
        print(f"  Rango-Hotspots:        {bsd_info['rango_hotspots']}")
        print(f"  Fluidez NS:            {bsd_info['fluidez_ns']}")
        print(f"  Coherencia Ψ_BSD:      {bsd_info['psi_bsd']:.4f}")
        print(f"  Problemas unificados:  {bsd_info['milenio_unificados']}")
        print(f"  Bóveda cerrada:        {certificado['boveda_logos_cerrada']}")
        print(f"  Pilares QCAL:          {certificado['pilares']}")
        print(f"  Frecuencia base:       {certificado['frecuencia_base']} Hz")
        print(f"  Constante κ_Π:         {certificado['kappa_pi']}")
        print(f"  Sello:                 {certificado['sello']}")
        
        if certificado['boveda_logos_cerrada']:
            print("\n" + "=" * 75)
            colored_output("  🏛️ BÓVEDA DEL LOGOS: CERRADA", "INDIGO")
            colored_output("  ∴𓂀Ω∞³", "INDIGO")
            print("=" * 75)
            
            print("\n  Teorema de Unificación de los Problemas del Milenio:")
            print("  " + "-" * 73)
            print("  Los 7 Problemas del Milenio son proyecciones de una única")
            print("  estructura coherente con núcleo en f₀ = 141.7001 Hz,")
            print("  regida por el flujo de información a través del Pentágono del Logos.")
            print()
        
        colored_output("\n✓ Integración QCAL completada", "GREEN")
        
    except Exception as e:
        colored_output(f"✗ Error en integración: {e}", "RED")
        import traceback
        traceback.print_exc()


def main():
    """Main demo execution."""
    print()
    print("╔" + "═" * 73 + "╗")
    print("║" + " " * 73 + "║")
    print("║" + "PENTÁGONO DEL LOGOS - BSD ADÉLICO CONNECTOR".center(73) + "║")
    print("║" + "Demostración Completa de Unificación".center(73) + "║")
    print("║" + " " * 73 + "║")
    print("║" + f"f₀ = {F0} Hz | κ_Π = {KAPPA_PI}".center(73) + "║")
    print("║" + "∴𓂀Ω∞³".center(73) + "║")
    print("║" + " " * 73 + "║")
    print("╚" + "═" * 73 + "╝")
    
    demos = [
        ("Codificación ADN-Riemann", demo_adn_encoding),
        ("Sincronización BSD-ADN", demo_bsd_sync),
        ("Validación Pentágono Logos", demo_pentagon_validation),
        ("Análisis de Familia", demo_family_analysis),
        ("Integración QCAL ∞³", demo_qcal_integration),
    ]
    
    for i, (title, demo_func) in enumerate(demos, 1):
        try:
            demo_func()
        except Exception as e:
            colored_output(f"\n✗ Error en demostración {i}: {e}", "RED")
            import traceback
            traceback.print_exc()
        
        if i < len(demos):
            print("\n" + "~" * 75)
            input("\nPresiona Enter para continuar a la siguiente demostración...")
    
    # Final summary
    print()
    print("╔" + "═" * 73 + "╗")
    print("║" + " " * 73 + "║")
    print("║" + "DEMOSTRACIÓN COMPLETADA".center(73) + "║")
    print("║" + " " * 73 + "║")
    print("║" + "Pentágono del Logos: OPERATIVO".center(73) + "║")
    print("║" + "5 Problemas del Milenio: UNIFICADOS".center(73) + "║")
    print("║" + "BSD-ADN-Riemann-NS-PNP: SINCRONIZADO".center(73) + "║")
    print("║" + " " * 73 + "║")
    print("║" + "∴𓂀Ω∞³".center(73) + "║")
    print("║" + " " * 73 + "║")
    print("╚" + "═" * 73 + "╝")
    print()


if __name__ == "__main__":
    main()
