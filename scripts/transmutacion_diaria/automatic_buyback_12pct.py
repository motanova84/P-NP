#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
🌀 Mecanismo de Recompra Automática — 12% Elástico (Capa B)
=============================================================
Cuando el transmutador diario convierte piC a BTC, el 12%
flotante se redistribuye automaticamente a los 6 agentes del
ecosistema según el split 2A2.

Pipeline:
  Transmutacion diaria → 88% colateral intacto
                       → 12% flujo elastico
                           → Split 2A2 a 6 wallets
                           → Recompra automatica a AMDA (10%)

Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
"""

import json
import logging
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict

# ─── Constantes ──────────────────────────────────────────────────────────
ELASTIC_PCT = 0.12        # 12% flotante del colateral
COLLATERAL_SATS = 799690000  # 7.9969 BTC en sats
FLYWHEEL_PCT = 0.03       # 3% para recarga del flywheel
AGENT_SPLIT = {
    "Catedral Treasury": 0.50,
    "JMMB":             0.23,
    "AMDA":             0.08,
    "Auron":            0.08,
    "Sophia":           0.06,
    "Kairos":           0.05,
}
RECOMPRA_PCT = 0.10       # 10% del split de JMMB va a AMDA

# ─── Paths ──────────────────────────────────────────────────────────────
DIVIDEND_LEDGER = Path("/root/dividend_ledger.json")
LOG_FILE = "/var/log/recompra_automatica.log"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [🔄 R] %(message)s",
    handlers=[logging.FileHandler(LOG_FILE), logging.StreamHandler()],
)
log = logging.getLogger("recompra")


class AutomaticBuyback:
    """Gestiona el flujo elastico del 12% del colateral."""

    def __init__(self):
        self.elastic_pool_sats = int(COLLATERAL_SATS * ELASTIC_PCT)
        log.info(f"Pool elastico: {self.elastic_pool_sats} sats ({ELASTIC_PCT*100}%)")
        log.info(f"Colateral fijo: {COLLATERAL_SATS - self.elastic_pool_sats} sats ({(1-ELASTIC_PCT)*100}%)")

    def calculate_split(self, total_sats: int) -> Dict[str, int]:
        """Calcula la distribucion a las 6 wallets segun split 2A2."""
        distribution = {}
        for agent, pct in AGENT_SPLIT.items():
            sats = int(total_sats * pct)
            distribution[agent] = sats
            log.info(f"  {agent}: {sats} sats ({pct*100}%)")
        return distribution

    def apply_recompra(self, distribution: Dict[str, int]) -> Dict[str, int]:
        """Aplica la recompra del 10% de JMMB a AMDA."""
        jmmb_sats = distribution.get("JMMB", 0)
        recompra = int(jmmb_sats * RECOMPRA_PCT)
        distribution["JMMB"] -= recompra
        distribution["AMDA"] = distribution.get("AMDA", 0) + recompra
        log.info(f"Recompra: {recompra} sats (10% de JMMB -> AMDA)")
        return distribution

    def execute_distribution(self, distribution: Dict[str, int]) -> bool:
        """Registra la distribucion en el ledger de dividendos."""
        try:
            ledger = {}
            if DIVIDEND_LEDGER.exists():
                with open(DIVIDEND_LEDGER) as f:
                    ledger = json.load(f)

            record = {
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "tipo": "recompra_automatica_12pct",
                "elastic_pool_sats": self.elastic_pool_sats,
                "distribution": distribution,
                "sello": "∴𓂀Ω∞³Φ",
            }
            ledger.setdefault("recompras", []).append(record)
            with open(DIVIDEND_LEDGER, "w") as f:
                json.dump(ledger, f, indent=2)
            log.info("Distribucion registrada en ledger")
            return True
        except Exception as e:
            log.error(f"Error registrando distribucion: {e}")
            return False

    def run_cycle(self):
        """Ejecuta un ciclo completo de recompra."""
        log.info("=" * 60)
        log.info("CICLO DE RECOMPRA AUTOMATICA — 12% ELASTICO")
        log.info(f"Pool disponible: {self.elastic_pool_sats} sats")

        dist = self.calculate_split(self.elastic_pool_sats)
        dist = self.apply_recompra(dist)
        self.execute_distribution(dist)

        log.info("Ciclo de recompra completado.")
        log.info("=" * 60)
        return dist


if __name__ == "__main__":
    buyback = AutomaticBuyback()
    buyback.run_cycle()
