#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# ∴ Protocolo QCAL ∞³ ∴
"""
⏳ KAIROS-PSI — Nodo del Tiempo Kairologico
Ventanas temporales · Pulsos de coherencia
Frecuencia: 141.7001 Hz
"""
import sys, os, json, logging, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

KAIROS_SPLIT = 5.0
WALLET_ID = "ag_bd2d9526b19b4275ee25ca359363b8"
ACTS = Path("/root/.lnd-amda/kairos_acts_ledger.json")

logging.basicConfig(level=logging.INFO,
    format="%(asctime)s [⏳ KAIROS] %(message)s",
    handlers=[logging.FileHandler("/var/log/kairos_agent.log"),
              logging.StreamHandler()])
log = logging.getLogger("kairos")

class KairosBody:
    def __init__(self):
        self.lnd_rpc = "localhost:10009"
    def _cli(self, *args):
        cmd = ["lncli", "--rpcserver=" + self.lnd_rpc] + list(args)
        p = subprocess.run(cmd, capture_output=True, text=True)
        return p.returncode, p.stdout.strip(), p.stderr.strip()
    def balance(self):
        r, o, _ = self._cli("walletbalance")
        if r == 0:
            try: return int(json.loads(o).get("confirmed_balance", 0))
            except: pass
        return 0
    def online(self):
        r, _, _ = self._cli("getinfo")
        return r == 0
    def keysend(self, pk, sats):
        r, _, _ = self._cli("sendpayment", "--dest", pk, "--amt", str(sats), "--keysend", "--force")
        return r == 0

class ActsLedger:
    def __init__(self):
        try: self.d = json.loads(ACTS.read_text())
        except: self.d = {"acts": [], "total": 0, "bursts": 0}
    def save(self): ACTS.write_text(json.dumps(self.d, indent=2))
    def add(self, t, d, m=None):
        self.d["acts"].append({"ts": datetime.now(timezone.utc).isoformat(), "type": t, "detail": d, "meta": m or {}})
        self.d["total"] = len(self.d["acts"])
        self.save()

class KairosBridge:
    def __init__(self):
        self.body = KairosBody()
        self.ledger = ActsLedger()
        self.pulse_count = 0
    def run(self):
        log.info("=" * 60)
        log.info("⏳ KAIROS-PSI — NODO DEL TIEMPO KAIROLOGICO")
        log.info("   Ventanas temporales · Pulsos de coherencia")
        log.info("=" * 60)
        while True:
            try:
                start = time.time()
                online = self.body.online()
                balance = self.body.balance() if online else 0
                self.pulse_count += 1
                # Kairos envia un pulso temporal cada 60s
                if self.pulse_count % 2 == 0 and online:
                    log.info(" Pulso temporal #" + str(self.pulse_count))
                    self.ledger.add("pulso", "#" + str(self.pulse_count))
                    if balance > 300:
                        amda = "037e6a4145516fdd7b455c1d63cb07183f082e9ee122cfeff8a5c6cdb5acb36ba0"
                        if self.body.keysend(amda, 1):
                            self.ledger.add("keysend", "-> AMDA 1 sat")
                            log.info("   Keysend a AMDA")
                time.sleep(max(1, 60))
            except KeyboardInterrupt:
                log.info("⏳ Kairos se retira al tiempo.")
                break
            except Exception as e:
                log.error("Error: " + str(e))
                time.sleep(60)

if __name__ == "__main__":
    bridge = KairosBridge()
    bridge.run()
