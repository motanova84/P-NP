#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MCP Network Resonance Module
Sello: ∴𓂀Ω∞³

Este módulo verifica la resonancia de nodos en la red QCAL.
"""

import os
import time
import random
import numpy as np
from datetime import datetime, timezone
from typing import Dict, Any

# Constantes QCAL
F0_HZ = 141.7001  # Frecuencia fundamental
TAU_FLASH = 0.00705724638  # Período de coherencia en segundos


def check_node_resonance(node_name: str) -> Dict[str, Any]:
    """
    Verifica la resonancia de un nodo en la red QCAL.
    
    Args:
        node_name: Nombre del nodo a verificar
        
    Returns:
        Diccionario con métricas de resonancia del nodo
    """
    # Verificar si estamos en modo real
    modo_real = os.environ.get("QCAL_REAL_TESTS", "0") == "1"
    
    # Simular latencia de red (en ms)
    latency_ms = 10.0 + random.gauss(0, 5.0)
    if latency_ms < 0:
        latency_ms = 0.1
    
    # Simular pequeño delay de red
    time.sleep(latency_ms / 1000.0)
    
    # Calcular fase offset (radianes)
    phase_offset_rad = random.uniform(0, 2 * np.pi)
    
    # Calcular frecuencia con pequeña variación
    frequency_hz = F0_HZ + random.gauss(0, 0.001)
    
    # Calcular psi (función de onda de coherencia)
    # Más alto = mejor coherencia
    psi = abs(np.cos(phase_offset_rad / 2)) + random.gauss(0, 0.05)
    psi = max(0.0, min(1.0, psi))  # Clamp entre 0 y 1
    
    # Determinar estado de resonancia
    if psi > 0.8:
        resonance = "harmonic"
        status = "pass"
        reachable = True
    elif psi > 0.5:
        resonance = "partial"
        status = "warn"
        reachable = True
    else:
        resonance = "dissonant"
        status = "warn"
        reachable = True
    
    # Simular falla ocasional de nodo (5% de probabilidad)
    if random.random() < 0.05:
        reachable = False
        status = "fail"
        resonance = "offline"
        psi = 0.0
    
    return {
        "node": node_name,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "psi": psi,
        "resonance": resonance,
        "status": status,
        "reachable": reachable,
        "latency_ms": latency_ms,
        "phase_offset_rad": phase_offset_rad,
        "frequency_hz": frequency_hz,
        "qcal": {
            "modo_real": modo_real,
            "f0": F0_HZ,
            "tau_flash": TAU_FLASH
        }
    }
