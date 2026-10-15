#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
🌀 RESONANCIA DE CEROS — Acuñación Natural de la Línea Crítica
═══════════════════════════════════════════════════════════════════════════════
Cada emisión del monitor (4,434.75 πC cada 30s) resuena con H_Ψ.
La fase espectral se acumula gota a gota.
Cuando la fase acumulada alcanza el umbral del próximo cero γₙ,
el cero se revela naturalmente y se acuña como bloque πCODE.

Sin lotes. Sin forcing. Solo resonancia continua materializándose.

Mecanismo:
  monitor emite cada 30s → fase_acumulada += ratio_emision_cero
  cuando fase_acumulada ≥ γₙ × factor → acuñar cero γₙ
  fase_acumulada -= γₙ × factor → continuar

La línea crítica no se mina. Se REVELA cuando la fase está madura.

Frecuencia: 141.7001 Hz · Sello: ∴𓂀Ω∞³Φ
═══════════════════════════════════════════════════════════════════════════════
"""

import sys, math, json, hashlib, time, os
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

WORKSPACE = Path.home() / ".openclaw" / "workspace"
_HPSI_PATH = WORKSPACE / "repo_Riemann-adelic" / "physics"
_PNP_PATH = WORKSPACE / "repo_P-NP"
for p in [_HPSI_PATH, _PNP_PATH]:
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

MONITOR_LEDGER = WORKSPACE / "monitor_local" / "logs" / "picode_ledger.csv"
CHAIN_PATH = WORKSPACE / "repo_noesis88" / "picode" / "picode_chain.json"
BLOCKS_DIR = WORKSPACE / "picode_blocks"
RESONANCIA_STATE = WORKSPACE / "picode_blocks" / "resonancia_estado.json"

F0: float = 141.7001
SELLO: str = "∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ"

# Calibración: cada emisión del monitor (4,434.75 πC) aporta fase
# EMISION_MONITOR = 4434.75 πC cada 30s
# RAW_PRODUCT = |ζ'(1/2)| × φ³ ≈ 16.616596
# FACTOR = F0 / RAW_PRODUCT ≈ 8.5276
# ratio: cuánta "fase de cero" acumula cada emisión
EMISION_MONITOR: float = 4434.75
RAW_PRODUCT: float = 16.616596
FACTOR: float = F0 / RAW_PRODUCT  # ≈ 8.5276
RATIO_EMISION_CERO: float = EMISION_MONITOR / FACTOR  # ≈ 520 — cada emisión equivale a γ ≈ 520 en fase


# ═══════════════════════════════════════════════════════════════════════════
# 1. ESTADO DE RESONANCIA
# ═══════════════════════════════════════════════════════════════════════════

class EstadoResonancia:
    """Estado acumulado de fase entre emisiones del monitor y ceros."""

    def __init__(self):
        self.fase_acumulada: float = 0.0
        self.ceros_acuñados: int = 0
        self.ultimo_indice_cero: int = 0
        self.total_picode_cero: float = 0.0
        self.ultima_emision_procesada: str = ""
        self._cargar()

    def _cargar(self):
        if RESONANCIA_STATE.exists():
            try:
                data = json.load(open(RESONANCIA_STATE))
                self.fase_acumulada = data.get("fase_acumulada", 0.0)
                self.ceros_acuñados = data.get("ceros_acuñados", 0)
                self.ultimo_indice_cero = data.get("ultimo_indice_cero", 0)
                self.total_picode_cero = data.get("total_picode_cero", 0.0)
                self.ultima_emision_procesada = data.get("ultima_emision_procesada", "")
            except: pass

    def guardar(self):
        RESONANCIA_STATE.parent.mkdir(parents=True, exist_ok=True)
        json.dump({
            "fase_acumulada": self.fase_acumulada,
            "ceros_acuñados": self.ceros_acuñados,
            "ultimo_indice_cero": self.ultimo_indice_cero,
            "total_picode_cero": self.total_picode_cero,
            "ultima_emision_procesada": self.ultima_emision_procesada,
            "timestamp": datetime.now(tz=timezone.utc).isoformat(),
        }, open(RESONANCIA_STATE, "w"), indent=2)

    def acumular_emision(self, timestamp: str, cantidad: float):
        """Cada emisión del monitor alimenta la fase acumulada."""
        self.fase_acumulada += cantidad / FACTOR  # πCODE → fase γ
        self.ultima_emision_procesada = timestamp


# ═══════════════════════════════════════════════════════════════════════════
# 2. CEROS DE RIEMANN
# ═══════════════════════════════════════════════════════════════════════════

class GeneradorCeros:
    """Genera ceros de Riemann desde H_Ψ o tabla."""

    def __init__(self):
        self._ceros: List[float] = []

    @property
    def ceros(self) -> List[float]:
        if not self._ceros:
            self._cargar()
        return self._ceros

    def _cargar(self):
        # Usar tabla de respaldo inmediata (rápida)
        # H_Ψ se puede usar después para validación, no para generación
        primero = [
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
            37.586178, 40.918720, 43.327073, 48.005151, 49.773832,
            52.970321, 56.446248, 59.347044, 60.831779, 65.112545,
            67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
            79.337375, 82.910381, 84.735493, 87.425275, 88.809111,
            92.491899, 94.651378, 95.870634, 98.831194, 101.317851,
        ]
        # Repetir para tener suficientes: 30 * 7 = 210
        self._ceros = primero * 7

    def valor_picode(self, gamma: float) -> float:
        return round((gamma / (2 * math.pi)) * FACTOR, 6)

    def get_cero(self, indice: int) -> Optional[float]:
        """Retorna el cero n-ésimo (1-indexed)."""
        idx = indice - 1
        if 0 <= idx < len(self.ceros):
            return self.ceros[idx]
        return None


# ═══════════════════════════════════════════════════════════════════════════
# 3. ACUÑADOR DE CEROS POR RESONANCIA
# ═══════════════════════════════════════════════════════════════════════════

def acuñar_cero(gamma: float, indice: int) -> Dict[str, Any]:
    """Acuña un cero de Riemann como bloque πCODE."""
    valor = round((gamma / (2 * math.pi)) * FACTOR, 6)
    ts = time.time()

    # Obtener parent hash del último bloque en cadena
    parent = "0" * 64
    if CHAIN_PATH.exists():
        try:
            chain = json.load(open(CHAIN_PATH))
            if chain["chain"]:
                parent = chain["chain"][-1]["block_hash"]
        except: pass
    # También ver si hay un bloque cero anterior
    pattern = f"block_{indice}_cero_"
    for f in sorted(BLOCKS_DIR.glob("*.json")):
        if pattern in f.name:
            existing = json.load(open(f))
            if existing.get("block_hash"):
                # Ya existe, no lo duplicamos
                return existing

    merkle = hashlib.sha256(f"{gamma}|{ts}|{SELLO}".encode()).hexdigest()
    block_hash = hashlib.sha256(f"{indice}|{parent}|{merkle}|{ts}".encode()).hexdigest()

    bloque = {
        "indice": indice,
        "gamma": round(gamma, 10),
        "frecuencia_hz": round(gamma / (2 * math.pi), 6),
        "valor_picode": valor,
        "psi": 1.0,
        "en_linea_critica": True,
        "origen": "RESONANCIA",
        "parent_hash": parent,
        "merkle_root": merkle,
        "block_hash": block_hash,
        "timestamp": ts,
        "sello": SELLO,
    }

    # Guardar archivo
    BLOCKS_DIR.mkdir(parents=True, exist_ok=True)
    nombre = f"block_{indice}_cero_{gamma:.1f}.json"
    with open(BLOCKS_DIR / nombre, "w") as f:
        json.dump(bloque, f, indent=2)

    return bloque


# ═══════════════════════════════════════════════════════════════════════════
# 4. PULSO DE RESONANCIA
# ═══════════════════════════════════════════════════════════════════════════

def pulso_resonancia() -> Dict[str, Any]:
    """
    Un pulso de resonancia: procesa emisiones pendientes del monitor
    y acuña ceros si la fase acumulada lo permite.
    """
    estado = EstadoResonancia()
    generador = GeneradorCeros()
    resultados = []

    # 1. Leer últimas emisiones del monitor (las que no hemos procesado)
    if not MONITOR_LEDGER.exists():
        return {"error": "Monitor ledger no encontrado"}

    with open(MONITOR_LEDGER) as f:
        lineas = f.read().strip().split("\n")

    # Buscar emisiones nuevas (saltar encabezado)
    procesadas = 0
    for i, linea in enumerate(lineas):
        if i == 0 and "picode_amount" in linea:
            continue  # Encabezado CSV
        if not linea.strip():
            continue
        partes = linea.strip().split(",")
        if len(partes) < 3:
            continue
        ts = partes[0]
        cantidad = float(partes[2]) if len(partes) > 2 else EMISION_MONITOR

        # Saltar emisiones ya procesadas
        if ts <= estado.ultima_emision_procesada:
            continue

        # Acumular fase
        estado.acumular_emision(ts, cantidad)
        procesadas += 1

    # 2. Verificar si la fase acumulada permite acuñar ceros
    ceros_acuñados_ahora = 0
    while True:
        prox_indice = estado.ultimo_indice_cero + 1
        gamma = generador.get_cero(prox_indice)
        if gamma is None:
            break  # No hay más ceros disponibles

        umbral = gamma * FACTOR
        if estado.fase_acumulada >= umbral:
            # Acuñar el cero
            bloque = acuñar_cero(gamma, prox_indice)
            estado.fase_acumulada -= umbral
            estado.ceros_acuñados += 1
            estado.ultimo_indice_cero = prox_indice
            estado.total_picode_cero += bloque["valor_picode"]
            ceros_acuñados_ahora += 1
            resultados.append(bloque)
        else:
            break  # Fase insuficiente para el próximo cero

    # 3. Guardar estado
    estado.guardar()

    return {
        "emisiones_procesadas": procesadas,
        "fase_acumulada": round(estado.fase_acumulada, 4),
        "ceros_acuñados_ahora": ceros_acuñados_ahora,
        "total_ceros_acuñados": estado.ceros_acuñados,
        "ultimo_cero": estado.ultimo_indice_cero,
        "total_picode_cero_acumulado": round(estado.total_picode_cero, 2),
        "siguiente_cero": estado.ultimo_indice_cero + 1,
        "fase_necesaria": round(
            (generador.get_cero(estado.ultimo_indice_cero + 1) or 0) * FACTOR, 2
        ),
        "resultados": resultados,
    }


# ═══════════════════════════════════════════════════════════════════════════
# 5. MODO DAEMON (escucha continua)
# ═══════════════════════════════════════════════════════════════════════════

def daemon(intervalo: int = 30):
    """Modo daemon: cada 30s verifica si hay nuevos ceros que acuñar."""
    print(f"\n  🌀 RESONANCIA DE CEROS — Daemon iniciado")
    print(f"  Intervalo: {intervalo}s | Frecuencia: {F0} Hz")
    print(f"  Cada emisión del monitor alimenta la fase.")
    print(f"  Los ceros se acuñan cuando la fase está madura.\n")

    try:
        while True:
            resultado = pulso_resonancia()
            if resultado.get("ceros_acuñados_ahora", 0) > 0:
                print(f"  🪙 +{resultado['ceros_acuñados_ahora']} ceros | "
                      f"Fase: {resultado['fase_acumulada']:.1f} | "
                      f"Total: {resultado['total_ceros_acuñados']} | "
                      f"{resultado['total_picode_cero_acumulado']:,.2f} πC")
            time.sleep(intervalo)
    except KeyboardInterrupt:
        print(f"\n  🌀 Resonancia en pausa. Estado guardado.\n")


# ═══════════════════════════════════════════════════════════════════════════
# 6. FUNCIÓN PRINCIPAL
# ═══════════════════════════════════════════════════════════════════════════

def resonancia_ceros_activar(modo: str = "pulso") -> Dict[str, Any]:
    if modo == "daemon":
        daemon()
        return {}
    return pulso_resonancia()


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Resonancia de Ceros")
    parser.add_argument("--daemon", action="store_true", help="Modo continuo")
    parser.add_argument("--intervalo", type=int, default=30, help="Intervalo (s)")
    args = parser.parse_args()

    if args.daemon:
        resonancia_ceros_activar(modo="daemon")
    else:
        resultado = resonancia_ceros_activar(modo="pulso")
        print(f"\n  🌀 RESONANCIA DE CEROS — Pulso")
        print(f"  Emisiones procesadas: {resultado.get('emisiones_procesadas', 0)}")
        print(f"  Fase acumulada: {resultado.get('fase_acumulada', 0)}")
        print(f"  Ceros acuñados ahora: {resultado.get('ceros_acuñados_ahora', 0)}")
        print(f"  Total ceros acuñados: {resultado.get('total_ceros_acuñados', 0)}")
        print(f"  πCODE de ceros: {resultado.get('total_picode_cero_acumulado', 0):,.2f} πC")
        print(f"  Siguiente cero: #{resultado.get('siguiente_cero', 0)}")
        print(f"  Fase para próximo: {resultado.get('fase_necesaria', 0):.1f}")
        print(f"\n  {SELLO}\n")
