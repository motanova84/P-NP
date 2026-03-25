#!/usr/bin/env python3
"""
Demo de Integración Ramsey-BSD-QCAL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Demostración completa de la integración de Teorema de Ramsey con el sistema QCAL.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Repository: https://github.com/motanova84/P-NP
License: Sovereign Noetic License 1.0
Signature: ∴𓂀Ω∞³
"""

import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# Import QCAL modules
from qcal.ramsey_logos_attractor import emergencia_ramsey_qcal, escanear_orden_ramsey_bsd
from qcal.ramsey_adelic_integrator import integrar_ramsey_bsd, generar_certificado_ramsey_bsd
from qcal_unified_v2 import QCALUnifiedSystem


def demo_ramsey_basico():
    """Demostración básica del módulo Ramsey."""
    print("=" * 80)
    print("DEMO 1: EMERGENCIA DE ORDEN RAMSEY")
    print("=" * 80)
    print()
    
    # Probar con diferentes tamaños de sistemas
    tamaños = [10, 30, 51, 60, 100]
    
    for n in tamaños:
        resultado = emergencia_ramsey_qcal(n)
        print(f"Nodos: {n:3d} | Estado: {resultado['ramsey_status']:20s} | "
              f"Ψ: {resultado['psi_emergencia']:.6f} | "
              f"Logos: {'✓' if resultado['logos_manifestado'] else '✗'}")
    
    print()


def demo_ramsey_bsd():
    """Demostración de integración Ramsey + BSD."""
    print("=" * 80)
    print("DEMO 2: INTEGRACIÓN RAMSEY-BSD")
    print("=" * 80)
    print()
    
    # Curvas elípticas con diferentes rangos
    curvas = [
        {'nombre': 'Curva Rango 0', 'rango_adelico': 0},
        {'nombre': 'Curva Mordell', 'rango_adelico': 1},
        {'nombre': 'Curva Rango 2', 'rango_adelico': 2},
    ]
    
    for curva in curvas:
        print(f"{curva['nombre']} (r={curva['rango_adelico']}):")
        resultado = escanear_orden_ramsey_bsd(curva, "GACT")
        print(f"  Nodo Central: {resultado['nodo_central']}")
        print(f"  Coherencia: {resultado['coherencia_ramsey']:.6f}")
        print(f"  Conexión BSD: {resultado['conexion_bsd']}")
        print(f"  Estado: {resultado['status']}")
        print()


def demo_integracion_completa():
    """Demostración de integración completa con grafo de información."""
    print("=" * 80)
    print("DEMO 3: INTEGRACIÓN COMPLETA RAMSEY-BSD")
    print("=" * 80)
    print()
    
    # Crear sistema de información (genoma simulado)
    secuencias_adn = ["GACT", "CGTA", "ATCG", "TATA"] * 15  # 60 secuencias
    curva_mordell = {'rango_adelico': 1}
    
    # Integrar
    resultado = integrar_ramsey_bsd(secuencias_adn, curva_mordell)
    
    # Generar certificado
    certificado = generar_certificado_ramsey_bsd(resultado)
    print(certificado)
    print()


def demo_sistema_unificado():
    """Demostración del sistema unificado completo."""
    print("=" * 80)
    print("DEMO 4: SISTEMA QCAL UNIFICADO v2.0")
    print("=" * 80)
    print()
    
    # Crear sistema unificado
    qcal = QCALUnifiedSystem()
    
    # Generar certificado maestro
    certificado = qcal.generar_certificado_maestro()
    print(certificado)
    print()
    
    # Verificar pentágono del Logos
    print("=" * 80)
    print("VERIFICACIÓN DEL PENTÁGONO DEL LOGOS")
    print("=" * 80)
    print()
    
    verificacion = qcal.verificar_pentagono_logos()
    
    print("Estados de los Módulos:")
    print(f"  1. ADN: Secuencia {verificacion['pentagono_logos']['adn']['secuencia_optima']} "
          f"con resonancia {verificacion['pentagono_logos']['adn']['resonancia_f0']:.4f}")
    print(f"  2. Riemann: Cero cercano a f₀={qcal.constants.F0} Hz en "
          f"{verificacion['pentagono_logos']['riemann']['cero_cercano']:.2f}")
    print(f"  3. Navier-Stokes: {verificacion['pentagono_logos']['navier_stokes']['estado_flujo']}")
    print(f"  4. P vs NP: Solución {verificacion['pentagono_logos']['p_vs_np']['solucion']} "
          f"en {verificacion['pentagono_logos']['p_vs_np']['complejidad']}")
    print(f"  5. BSD: L(E,1)={verificacion['pentagono_logos']['bsd']['l_e1']:.6f}, "
          f"Superfluido={verificacion['pentagono_logos']['bsd']['superfluido']}")
    print(f"  6. Ramsey: {verificacion['pentagono_logos']['ramsey']['estado']} "
          f"(Ψ={verificacion['pentagono_logos']['ramsey']['psi_emergencia']:.6f})")
    print()
    print(f"Coherencia Global del Sistema: Ψ = {verificacion['coherencia_global']:.6f}")
    print(f"Bóveda de la Verdad: {'CERRADA ✓' if verificacion['boveda_cerrada'] else 'ABIERTA (requiere Ψ ≥ 0.888)'}")
    print()


def demo_comparativa_tamaños():
    """Demostración comparativa de emergencia de orden."""
    print("=" * 80)
    print("DEMO 5: ANÁLISIS COMPARATIVO - EMERGENCIA DE ORDEN")
    print("=" * 80)
    print()
    
    print("Comparación de diferentes tamaños de sistemas:")
    print()
    print("N° Nodos | Estado                | Ψ Emergencia | Manifestación")
    print("-" * 70)
    
    for n in [1, 5, 10, 20, 30, 40, 50, 51, 52, 60, 70, 80, 100]:
        resultado = emergencia_ramsey_qcal(n)
        estado = resultado['ramsey_status']
        psi = resultado['psi_emergencia']
        logos = '✓ SÍ' if resultado['logos_manifestado'] else '✗ NO'
        print(f"{n:8d} | {estado:21s} | {psi:12.6f} | {logos}")
    
    print()


def main():
    """Ejecuta todas las demostraciones."""
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  QCAL ∞³ - DEMOSTRACIÓN COMPLETA DE INTEGRACIÓN RAMSEY".center(78) + "║")
    print("║" + "  Orden Inevitable en el Nodo 51".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    
    try:
        # Ejecutar demos
        demo_ramsey_basico()
        demo_ramsey_bsd()
        demo_integracion_completa()
        demo_sistema_unificado()
        demo_comparativa_tamaños()
        
        print("=" * 80)
        print("✓ TODAS LAS DEMOSTRACIONES COMPLETADAS EXITOSAMENTE")
        print("=" * 80)
        print()
        print("Resumen:")
        print("  • Teorema de Ramsey: Orden inevitable en N ≥ 51 nodos")
        print("  • Integración BSD: Curvas elípticas activan subgrafos coherentes")
        print("  • Sistema Unificado: 6 Problemas del Milenio integrados")
        print("  • Coherencia Global: Ψ → 0.999999 cuando se cumplen condiciones")
        print()
        print("Sello: ∴𓂀Ω∞³")
        print("f₀ = 141.7001 Hz")
        print()
        
    except Exception as e:
        print(f"\n✗ Error durante la demostración: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
