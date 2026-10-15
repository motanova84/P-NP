#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Demostración del NFT Oscilador QCAL (Trueno Silencioso ∞³)
===========================================================

Este script demuestra el uso del módulo NFT Oscillator QCAL
integrado en el sistema Noēsis88.
"""

from noesis88.modules.NFT import (
    crear_nft_genesis,
    verificar_protocolo,
    FASE_VIBRACIONAL,
    FASE_EMISIVA,
    PSI_CRITICO
)

def main():
    print("=" * 70)
    print("DEMOSTRACIÓN: NFT OSCILADOR QCAL - TRUENO SILENCIOSO ∞³")
    print("=" * 70)
    
    # 1. Verificar protocolo
    print("\n1. VERIFICACIÓN DEL PROTOCOLO")
    print("-" * 70)
    resultado = verificar_protocolo()
    print(f"   Frecuencia Vibracional (Silencio): {FASE_VIBRACIONAL} Hz")
    print(f"   Frecuencia Emisiva (Trueno): {FASE_EMISIVA} Hz")
    print(f"   Ψ Crítico: {PSI_CRITICO}")
    
    # 2. Crear NFT Genesis
    print("\n2. CREACIÓN DEL NFT GENESIS")
    print("-" * 70)
    nft = crear_nft_genesis(owner_id="DemoUser")
    print(f"   Propietario: {nft.owner_id}")
    print(f"   Sello Genesis: {nft.sello_genesis}")
    print(f"   Estado Inicial: {nft.estado.fase}")
    print(f"   Coherencia Inicial (Ψ): {nft.estado.psi:.6f}")
    
    # 3. Primera manifestación
    print("\n3. PRIMERA MANIFESTACIÓN")
    print("-" * 70)
    emision1 = nft.manifestar("coherencia_inicial")
    print(f"   Exitosa: {emision1.exitosa}")
    print(f"   Frecuencia: {emision1.frecuencia} Hz")
    print(f"   Intención: {emision1.intencion}")
    print(f"   Geometría 4D: [{', '.join(f'{x:.4f}' for x in emision1.geometria)}]")
    print(f"   Curvatura ΔA₀: {emision1.curvatura}")
    print(f"   Valor Emergente: {emision1.valor_emergente:.8f}")
    
    # 4. Ciclo respiratorio
    print("\n4. CICLO RESPIRATORIO")
    print("-" * 70)
    resp = nft.respirar()
    print(f"   Estado: {resp['estado']}")
    print(f"   Coherencia (Ψ): {resp['psi']:.6f}")
    print(f"   Latido: {resp['latido']}")
    
    # 5. Serie de manifestaciones
    print("\n5. SERIE DE MANIFESTACIONES")
    print("-" * 70)
    intenciones = [
        "expansion_consciencia",
        "conexion_simbiotic",
        "sintesis_coherente",
        "trascendencia_campo"
    ]
    
    for i, intencion in enumerate(intenciones, 2):
        emision = nft.manifestar(intencion)
        print(f"   {i}. {intencion}")
        print(f"      Ψ actual: {nft.estado.psi:.6f}")
        print(f"      Valor: {emision.valor_emergente:.6f}")
        print(f"      Sello: {emision.sello_transicion[:16]}...")
    
    # 6. Estado final
    print("\n6. ESTADO FINAL DEL OSCILADOR")
    print("-" * 70)
    estado = nft.to_dict()
    print(f"   Transiciones Exitosas: {estado['transiciones_exitosas']}")
    print(f"   Acción Acumulada: {estado['accion_acumulada']:.4f}")
    print(f"   Valor de Coherencia: {estado['valor_coherencia']:.8f}")
    print(f"   Estados en Historial: {len(estado['historial'])}")
    print(f"   Emisiones Totales: {len(estado['emisiones'])}")
    
    # 7. Resumen
    print("\n7. RESUMEN")
    print("-" * 70)
    print(f"   ✓ NFT activo y respirando")
    print(f"   ✓ {nft.transiciones_exitosas} manifestaciones exitosas")
    print(f"   ✓ Coherencia mantenida: Ψ = {nft.estado.psi:.6f}")
    print(f"   ✓ Estado: {nft.estado.fase}")
    
    print("\n" + "=" * 70)
    print("∴ PROTOCOLO TRUENO SILENCIOSO ∞³ - OPERATIVO")
    print("El NFT respira. Late. Emite. Es.")
    print("=" * 70)


if __name__ == "__main__":
    main()
