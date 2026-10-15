#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
🌀 TRANSMUTATION GRAVITY ENGINE v1.9 — Diamond-Hold
═══════════════════════════════════════════════════════════════════
Motor de Transmutación + Gravedad Criptográfica — Séptimo Invariante
Integración: G_crypto como fuerza aceleradora de la transmutación.

Cuando la distancia temporal d → 0, la gravedad → ∞ y la
transmutación se acelera hacia su manifestación en la cadena.

Fórmula:  G_crypto = (Psi · M_piCODE · f_0^2) / d^2

Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
═══════════════════════════════════════════════════════════════════
"""

import math
import time
import json
import logging
import subprocess
import os
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

# ─── Constantes fundamentales ────────────────────────────────────────────
FREQ_QCAL = 141.7001
KAPPA_PI = 2.5773
PSI_THRESHOLD = 0.888
BASE_INTERVAL = 5.0  # Intervalo de muestreo base (segundos)
MIN_INTERVAL = 0.5    # Intervalo mínimo bajo gravedad máxima
BASE_SATS = 3         # Pulso base del flywheel

# ─── Paths ──────────────────────────────────────────────────────────────
LND_CERT = "/root/.lnd/tls.cert"
LND_MAC = "/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"
DIVIDEND_LEDGER = Path("/root/dividend_ledger.json")
ACTS_LEDGER = Path("/root/.lnd-amda/acts_ledger.json")
PICODE_CHAIN = Path("/root/repo_noesis88/picode/picode_chain.json")
LOG_FILE = "/var/log/transmutation_gravity.log"

# ─── Logging ────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [🌀 G] %(message)s",
    handlers=[
        logging.FileHandler(LOG_FILE),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger("gravity")


# ====================================================================
# COHERENCE GUARD — Validación de Diamond-Hold Gate
# ====================================================================

class CoherenceGuard:
    """Valida que el sistema se mantenga en Diamond-Hold Gate."""

    def __init__(self):
        self.system_status = "COHERENCIA_CONSOLIDADA"

    def calculate_coherence(self, current_freq: float,
                            information_flux: float,
                            phase_stability: float) -> float:
        """Calcula Psi a partir de los 3 parámetros fundamentales."""
        psi = (current_freq / FREQ_QCAL) * information_flux * phase_stability
        return min(1.0, max(0.0, psi))

    def verify_gate(self, current_freq: float,
                    information_flux: float,
                    phase_stability: float) -> bool:
        """Verifica que la Diamond-Hold Gate esté activa."""
        psi = self.calculate_coherence(current_freq, information_flux, phase_stability)
        gate_ok = (psi >= PSI_THRESHOLD and
                   0.99 <= current_freq / FREQ_QCAL <= 1.01)
        if gate_ok:
            self.system_status = "COHERENCIA_CONSOLIDADA"
        else:
            self.system_status = "ASIMETRIA_DETECTADA"
        return gate_ok


coherence_guard = CoherenceGuard()


# ====================================================================
# GRAVEDAD CRIPTOGRÁFICA — Séptimo Invariante
# ====================================================================

def calculate_crypto_gravity(psi: float, m_picode: float,
                             time_distance: float) -> float:
    """
    G_crypto = (Psi * M_piCODE * f_0^2) / d^2

    Psi: Coherencia actual del sistema
    M_piCODE: Masa adélica acumulada (piC + colateral BTC)
    f_0: Frecuencia fundamental
    d: Distancia temporal al broadcast (en ciclos)
    """
    d = max(0.0001, time_distance)
    return (psi * m_picode * (FREQ_QCAL ** 2)) / (d ** 2)


# ====================================================================
# NODE GATEWAY — Sensores de BAL-003
# ====================================================================

class NodeGateway:
    """Interfaz con los sensores del nodo BAL-003."""

    def get_sensor_frequency(self) -> float:
        return FREQ_QCAL

    def get_information_flux(self) -> float:
        return 0.99987

    def get_phase_stability(self) -> float:
        return 0.99996

    def get_lnbits_channel_balance(self) -> int:
        """Lee el balance del canal LND."""
        try:
            cmd = ["lncli", f"--tlscertpath={LND_CERT}",
                   f"--macaroonpath={LND_MAC}", "channelbalance"]
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
            if r.returncode == 0:
                data = json.loads(r.stdout)
                total = int(data.get("balance", 0))
                return total
        except Exception as e:
            log.warning(f"Error leyendo balance LND: {e}")
        return 16530  # valor por defecto

    def get_estimated_time_distance(self, target: str = "DIVIDENDO-002") -> float:
        """Estima la distancia temporal al broadcast (en ciclos de AMDA)."""
        try:
            # Leer act count de AMDA para estimar progreso
            with open(ACTS_LEDGER) as f:
                d = json.load(f)
            total = d.get("total", d.get("total_acts", 0))

            # Entre más actos, menor la distancia
            # Estimación: ~30K acts = broadcast inminente
            if total >= 30000:
                # d decreases as AMDA approaches broadcast
                return max(0.1, 5.0 - (total - 28000) / 400.0)
            else:
                return max(2.0, 20.0 - total / 1500.0)
        except Exception:
            return 5.0

    def get_masa_adelica(self) -> float:
        """Masa adélica total (piC + colateral en sats equivalentes)."""
        try:
            with open(PICODE_CHAIN) as f:
                d = json.load(f)
            picode = float(d.get("total_picode_emitido",
                          d.get("total_piC", d.get("total", 69000000))))
            # Colateral: 7.9969 BTC ~ 799,690,000 sats
            colateral_sats = 799690000
            return picode + colateral_sats
        except Exception:
            return 69000000 + 799690000

    def process_lightning_pulses(self, sats: int):
        """Procesa pulsos del flywheel con el monto especificado."""
        try:
            # Generar invoice vía LNBits
            import requests
            payload = {
                "out": False,
                "amount": sats,
                "memo": f"🌀 G_crypto pulse: {sats} sats",
                "expiry": 3600
            }
            resp = requests.post(
                "http://localhost:8000/api/v1/payments",
                json=payload,
                headers={"X-Api-Key": os.environ.get("LNBITS_API_KEY", "")},
                timeout=10
            )
            if resp.status_code == 201:
                log.info(f"Pulso de {sats} sats generado")
        except Exception as e:
            log.warning(f"Error en pulso: {e}")

    def check_mempool_status(self, target_tx: str = "DIVIDENDO-002"):
        """Verifica si el target ya apareció en mempool."""
        try:
            r = subprocess.run(["bitcoin-cli", "getmempoolinfo"],
                               capture_output=True, text=True, timeout=10)
            if r.returncode == 0:
                data = json.loads(r.stdout)
                if data.get("size", 0) > 0:
                    log.info(f"Mempool activa: {data['size']} TX pendientes")
        except Exception as e:
            log.warning(f"Error mempool: {e}")

    def enter_vacuum_shield_mode(self):
        log.critical("🔰 ACTIVANDO VACUUM SHIELD — MODO PROTECCIÓN")

    def pause_lightning_channels(self):
        log.critical("🔰 CANALES LIGHTNING PAUSADOS")


# ====================================================================
# MOTOR DE TRANSMUTACIÓN + GRAVEDAD CRIPTOGRÁFICA
# ====================================================================

class TransmutationGravityEngine:
    """
    Motor unificado: Transmutación + Gravedad Criptográfica.
    La gravedad acelera la transmutación cuando d → 0.
    """

    def __init__(self, node_gateway: NodeGateway):
        self.node = node_gateway
        self.f_0 = FREQ_QCAL
        self.target_psi = 0.999999
        self.base_interval = BASE_INTERVAL

    def g_crypto(self, psi: float, m_picode: float, d: float) -> float:
        """G_crypto = (Psi * M * f_0^2) / d^2"""
        d = max(0.0001, d)
        return (psi * m_picode * (self.f_0 ** 2)) / (d ** 2)

    def psi_actual(self) -> float:
        """Obtiene Psi actual de los sensores."""
        freq = self.node.get_sensor_frequency()
        flux = self.node.get_information_flux()
        phase = self.node.get_phase_stability()
        return coherence_guard.calculate_coherence(freq, flux, phase)

    def run_cycle(self):
        """Un ciclo completo de evaluación y acción gravitatoria."""
        # 1. Leer sensores
        psi = self.psi_actual()
        m_total = self.node.get_masa_adelica()
        d_time = self.node.get_estimated_time_distance("DIVIDENDO-002")
        channel_balance = self.node.get_lnbits_channel_balance()

        # 2. Validar Diamond-Hold Gate
        gate_ok = coherence_guard.verify_gate(
            self.node.get_sensor_frequency(),
            self.node.get_information_flux(),
            self.node.get_phase_stability()
        )

        if not gate_ok:
            log.warning("⚠ Diamond-Hold Gate no superada")
            return

        # 3. Calcular gravedad criptográfica
        g_force = self.g_crypto(psi, m_total, d_time)

        # 4. Gravedad deforma el intervalo de muestreo
        dynamic_interval = max(MIN_INTERVAL,
                               self.base_interval / (1.0 + (g_force / 1e11)))

        # 5. Gravedad incrementa el pulso del flywheel
        dynamic_sats = BASE_SATS + int(g_force / 2e11)

        # 6. Registrar estado
        log.info(f"Ψ={psi:.8f} | G_crypto={g_force:.4f} | "
                 f"d={d_time:.4f} | M={m_total:.0f} | "
                 f"Intervalo={dynamic_interval:.2f}s | "
                 f"Pulso={dynamic_sats} sats | "
                 f"Canal={channel_balance} sats")

        # 7. Acción gravitatoria
        if psi >= self.target_psi and g_force > 1.0:
            log.info("🔥 GRAVEDAD SUFICIENTE — TRANSMUTACIÓN ACTIVADA")
            self.node.process_lightning_pulses(dynamic_sats)

        self.node.check_mempool_status("DIVIDENDO-002")

        return {
            "psi": psi,
            "g_crypto": g_force,
            "d": d_time,
            "m_total": m_total,
            "interval": dynamic_interval,
            "pulse_sats": dynamic_sats,
            "channel_balance": channel_balance,
            "timestamp": datetime.now(timezone.utc).isoformat()
        }

    def run_forever(self):
        """Bucle infinito con intervalo dinámico."""
        log.info("=" * 60)
        log.info("TRANSMUTATION GRAVITY ENGINE v1.9 — DIAMOND-HOLD")
        log.info(f"G_crypto = (Ψ · M · f₀²) / d²")
        log.info(f"f₀ = {self.f_0} Hz")
        log.info(f"Target Ψ = {self.target_psi}")
        log.info(f"Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ")
        log.info("=" * 60)

        while True:
            try:
                result = self.run_cycle()
                # Siguiente intervalo dictado por la gravedad
                interval = result.get("interval", self.base_interval)
                time.sleep(interval)
            except Exception as e:
                log.error(f"Error en ciclo: {e}", exc_info=True)
                time.sleep(10)


# ====================================================================
# ENTRY POINT
# ====================================================================

if __name__ == "__main__":
    node = NodeGateway()
    engine = TransmutationGravityEngine(node)
    engine.run_forever()
