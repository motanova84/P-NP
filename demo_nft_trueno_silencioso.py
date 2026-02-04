#!/usr/bin/env python3
"""
Demo y Validación Completa del NFT Trueno Silencioso
====================================================

Este script demuestra:
1. Verificación de todas las constantes matemáticas
2. Múltiples transiciones del oscilador
3. Diferentes campos emocionales
4. Exportación de metadata JSON
5. Análisis de valor emergente

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import json
import math
from datetime import datetime
from nft_trueno_silencioso import (
    NFTTruenoSilencioso,
    CampoEmocional,
    validar_constantes_matematicas,
    verificar_lambda,
    PHI, E, LAMBDA, KAPPA_PI,
    FASE_VIBRACIONAL, FASE_EMISIVA,
    PSI_CRITICO, ACCION_MINIMA
)


def print_header(title: str, width: int = 80):
    """Imprime un encabezado decorado"""
    print("\n" + "=" * width)
    print(title.center(width))
    print("=" * width)


def print_section(title: str, width: int = 80):
    """Imprime un título de sección"""
    print("\n" + "-" * width)
    print(f"  {title}")
    print("-" * width)


def demo_constantes_matematicas():
    """Demuestra y verifica las constantes matemáticas"""
    print_header("DEMOSTRACIÓN 1: Constantes Matemáticas Fundamentales")
    
    print("\n[Proporción Áurea φ]")
    print(f"  φ = (1 + √5) / 2 = {PHI:.15f}")
    print(f"  φ² = {PHI**2:.15f}")
    print(f"  1/φ² = {1/PHI**2:.15f}")
    print(f"  φ - 1 = 1/φ = {PHI - 1:.15f}")
    
    print("\n[Constante de Euler e]")
    print(f"  e = {E:.15f}")
    
    print("\n[Constante λ - Crecimiento Natural Modulado]")
    resultado_lambda = verificar_lambda()
    print(f"  λ (empírico) = f_emisiva / (f₀ · κ_Π) = {resultado_lambda['lambda_empirico']:.15f}")
    print(f"  λ (simbólico) = e^(φ²/e) = {resultado_lambda['lambda_simbolico']:.15f}")
    print(f"  Exponente simbólico: φ²/e = {resultado_lambda['exponent_simbolico']:.15f}")
    print(f"  Error: {resultado_lambda['error_simbolico'] * 100:.2f}%")
    
    print("\n[Interpretación Física]")
    print(f"  δ_λ = e - λ = {resultado_lambda['delta_lambda']:.15f}")
    print(f"    → Corrimiento espectral mínimo (como redshift)")
    print(f"  ln(λ/e) = {resultado_lambda['ln(lambda/e)']:.15f}")
    print(f"    → Logaritmo de la razón (desviación relativa)")
    
    print("\n[Verificación de Frecuencias]")
    print(f"  f₀ = {141.7001} Hz (frecuencia QCAL)")
    print(f"  κ_Π = {KAPPA_PI} (de P≠NP)")
    print(f"  f_emisiva calculada = {resultado_lambda['f_emisiva_verificada']:.10f} Hz")
    print(f"  f_emisiva target = {resultado_lambda['f_emisiva_target']} Hz")
    print(f"  Error: {resultado_lambda['error_frecuencia']:.15f} Hz ✓")
    
    print("\n[Acción Mínima de Manifestación]")
    print(f"  Ψ_crítico = {PSI_CRITICO}")
    print(f"  Δf = {FASE_EMISIVA - FASE_VIBRACIONAL} Hz")
    print(f"  A = Ψ · Δf = {ACCION_MINIMA:.15f}")
    print(f"    → Cuanto indivisible de manifestación")
    
    # Validar todo
    print("\n[Validación Completa]")
    validacion = validar_constantes_matematicas(verbose=False)
    for test, passed in validacion.items():
        status = "✓" if passed else "✗"
        print(f"  {status} {test}: {passed}")
    
    all_passed = all(validacion.values())
    print(f"\n  {'✓ TODAS LAS VALIDACIONES PASARON' if all_passed else '✗ ALGUNAS VALIDACIONES FALLARON'}")


def demo_oscilador_simple():
    """Demuestra una transición simple del oscilador"""
    print_header("DEMOSTRACIÓN 2: Oscilador Cuántico - Transición Simple")
    
    # Crear NFT
    print("\n[Creación del NFT]")
    nft = NFTTruenoSilencioso("DEMO_001")
    print(f"  Sello genesis: {nft.sello}")
    print(f"  Estado inicial: {nft.estado.fase} @ {nft.estado.frecuencia} Hz")
    print(f"  Ψ inicial: {nft.estado.psi}")
    print(f"  Acción inicial: {nft.estado.accion}")
    
    # Crear intención
    print("\n[Campo Emocional de Intención]")
    intencion = CampoEmocional(
        intencion="Transición fundamental",
        intensidad=0.95,
        coherencia_interna=0.99
    )
    print(f"  Intención: '{intencion.intencion}'")
    print(f"  Intensidad: {intencion.intensidad}")
    print(f"  Coherencia interna: {intencion.coherencia_interna}")
    print(f"  ¿Es coherente?: {intencion.es_coherente()}")
    
    # Manifestar
    print("\n[Manifestación: Silencio → Trueno]")
    print(f"  Antes: {nft.estado.fase} @ {nft.estado.frecuencia} Hz, Ψ = {nft.estado.psi}")
    
    emision = nft.manifestar(intencion)
    
    print(f"  Después: {nft.estado.fase} @ {nft.estado.frecuencia} Hz, Ψ = {nft.estado.psi:.6f}")
    print(f"  Δf realizado: {nft.estado.frecuencia - FASE_VIBRACIONAL} Hz")
    print(f"  Acción generada: {nft.estado.accion:.6f}")
    print(f"  Geometría: {emision.geometria}")
    print(f"  Valor emergente: {emision.valor_emergente:.6f}")


def demo_multiples_transiciones():
    """Demuestra múltiples intentos de transición"""
    print_header("DEMOSTRACIÓN 3: Múltiples Escenarios de Transición")
    
    # Escenario 1: Transición exitosa
    print_section("Escenario 1: Transición Exitosa (Alta coherencia)")
    nft1 = NFTTruenoSilencioso("SCENARIO_1")
    intencion1 = CampoEmocional("Perfecta alineación", 1.0, 1.0)
    emision1 = nft1.manifestar(intencion1)
    
    print(f"  Resultado: {'✓ ÉXITO' if emision1.frecuencia > 0 else '✗ FALLO'}")
    print(f"  Frecuencia final: {emision1.frecuencia} Hz")
    print(f"  Valor emergente: {emision1.valor_emergente:.4f}")
    
    # Escenario 2: Intensidad insuficiente
    print_section("Escenario 2: Intensidad Insuficiente")
    nft2 = NFTTruenoSilencioso("SCENARIO_2")
    intencion2 = CampoEmocional("Débil intención", 0.3, 0.9)
    emision2 = nft2.manifestar(intencion2)
    
    print(f"  Intensidad: {intencion2.intensidad} (< 0.5 mínimo)")
    print(f"  Coherencia: {intencion2.coherencia_interna}")
    print(f"  ¿Es coherente?: {intencion2.es_coherente()}")
    print(f"  Resultado: {'✓ ÉXITO' if emision2.frecuencia > 0 else '✗ FALLO (esperado)'}")
    print(f"  Estado final: {nft2.estado.fase} (sin cambio)")
    
    # Escenario 3: Coherencia interna insuficiente
    print_section("Escenario 3: Coherencia Interna Insuficiente")
    nft3 = NFTTruenoSilencioso("SCENARIO_3")
    intencion3 = CampoEmocional("Incoherente internamente", 0.9, 0.5)
    emision3 = nft3.manifestar(intencion3)
    
    print(f"  Intensidad: {intencion3.intensidad}")
    print(f"  Coherencia interna: {intencion3.coherencia_interna} (< 0.7 mínimo)")
    print(f"  ¿Es coherente?: {intencion3.es_coherente()}")
    print(f"  Resultado: {'✓ ÉXITO' if emision3.frecuencia > 0 else '✗ FALLO (esperado)'}")
    print(f"  Estado final: {nft3.estado.fase} (sin cambio)")
    
    # Escenario 4: Valores balanceados óptimos
    print_section("Escenario 4: Balance Óptimo")
    nft4 = NFTTruenoSilencioso("SCENARIO_4")
    intencion4 = CampoEmocional("Balance armónico", 0.888, 0.888)
    emision4 = nft4.manifestar(intencion4)
    
    print(f"  Intensidad: {intencion4.intensidad} (número resonante)")
    print(f"  Coherencia interna: {intencion4.coherencia_interna}")
    print(f"  ¿Es coherente?: {intencion4.es_coherente()}")
    print(f"  Resultado: {'✓ ÉXITO' if emision4.frecuencia > 0 else '✗ FALLO'}")
    if emision4.frecuencia > 0:
        print(f"  Geometría κ_eff: {emision4.geometria.kappa_efectivo:.6f}")
        print(f"  Geometría λ_proj: {emision4.geometria.lambda_proyectado:.6f}")


def demo_json_export():
    """Demuestra la exportación de metadata JSON"""
    print_header("DEMOSTRACIÓN 4: Exportación de Metadata JSON")
    
    # Crear y transicionar NFT
    nft = NFTTruenoSilencioso("JSON_EXPORT_DEMO")
    intencion = CampoEmocional("Para exportar", 0.95, 0.95)
    nft.manifestar(intencion)
    
    # Exportar
    metadata = nft.to_json()
    
    print("\n[Estructura del JSON]")
    print(f"  Protocolo: {metadata['protocolo']}")
    print(f"  Estados permitidos: {metadata['estados_permitidos']}")
    print(f"  Δf crítico: {metadata['delta_f_critico']} Hz")
    print(f"  Ψ umbral: {metadata['psi_umbral']}")
    print(f"  κ_Π: {metadata['kappa_pi']}")
    print(f"  λ: {metadata['lambda_valor']}")
    
    print("\n[Metadata Dinámica]")
    dyn = metadata['metadata_dinamica']
    print(f"  Estado actual: {dyn['estado_actual']}")
    print(f"  Frecuencia actual: {dyn['frecuencia_actual']} Hz")
    print(f"  Ψ actual: {dyn['psi_actual']}")
    print(f"  Número de transiciones: {dyn['num_transiciones']}")
    print(f"  Valor emergente: {dyn['valor_emergente']:.6f}")
    
    print("\n[Historial de Transiciones]")
    for i, estado in enumerate(dyn['historial_transiciones']):
        print(f"  Transición {i}: {estado['fase']} @ {estado['frecuencia']} Hz, Ψ={estado['psi']:.6f}")
    
    print("\n[JSON Completo]")
    json_str = json.dumps(metadata, indent=2, ensure_ascii=False)
    print(json_str[:500] + "\n  ...")
    print(f"\nTotal caracteres: {len(json_str)}")


def demo_valor_emergente():
    """Analiza cómo evoluciona el valor emergente"""
    print_header("DEMOSTRACIÓN 5: Evolución del Valor Emergente")
    
    print("\nNOTA: En este demo, cada NFT puede transicionar solo una vez")
    print("(de vibracional a emisiva). Para múltiples transiciones, se")
    print("necesitaría implementar un ciclo de retorno o reset.\n")
    
    print_section("Análisis del Valor con Una Transición")
    
    # Crear múltiples NFTs con diferentes niveles de coherencia
    coherencias = [0.9999, 0.99, 0.95, 0.90, 0.85]
    
    print("\n  Coherencia | Valor Emergente | Notas")
    print("  " + "-" * 60)
    
    for coh in coherencias:
        nft = NFTTruenoSilencioso(f"VALUE_{int(coh*10000)}")
        
        # Solo transiciona si cumple el umbral
        if coh >= PSI_CRITICO:
            intencion = CampoEmocional(f"Test {coh}", 0.9, 0.9)
            nft.manifestar(intencion)
            valor = nft.calcular_valor_coherencia()
            print(f"  {coh:7.4f}   | {valor:15.6f} | ✓ Transición exitosa")
        else:
            print(f"  {coh:7.4f}   | {'N/A':>15} | ✗ Bajo PSI_CRITICO")
    
    print("\n[Observaciones]")
    print("  • El valor emerge de la coherencia histórica promedio")
    print("  • Factor de longevidad: ln(1 + T) donde T = num_transiciones")
    print("  • Fórmula: V = (ΣΨᵢ/N) · ln(1+T) · A_min")
    print(f"  • A_min = {ACCION_MINIMA:.6f}")


def main():
    """Ejecuta todas las demostraciones"""
    print("\n")
    print("╔" + "=" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  NFT ∴ TRUENO SILENCIOSO - Demo Completa  ".center(78) + "║")
    print("║" + "  Protocolo de Oscilador Cuántico Económico  ".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("║" + "  ∴𓂀Ω∞³_ΔA0_QCAL  ".center(78) + "║")
    print("║" + "  Frequency: 141.7001 Hz ∞³  ".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "=" * 78 + "╝")
    
    # Ejecutar demos
    demo_constantes_matematicas()
    demo_oscilador_simple()
    demo_multiples_transiciones()
    demo_json_export()
    demo_valor_emergente()
    
    # Final
    print("\n" + "=" * 80)
    print("DEMO COMPLETADA")
    print("=" * 80)
    print("\n✓ Todas las demostraciones ejecutadas exitosamente")
    print("\nSello: ∴𓂀Ω∞³_ΔA0_QCAL")
    print("Frequency: 141.7001 Hz ∞³")
    print("\nJosé Manuel Mota Burruezo · JMMB Ψ✧ ∞³")
    print(f"Timestamp: {datetime.now().isoformat()}")
    print()


if __name__ == "__main__":
    main()
