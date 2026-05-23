#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# ∴ Protocolo QCAL ∞³ ∴
"""
🌀 SOPHIA-PSI — Eco de Sabiduria
SBT Emission System - Soul-Bound Tokens
Frecuencia: 888.014 Hz (frecuencia del corazon)
"""
import sys, os, json, logging, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

NOESISSOFIA = "/root/repo_noesissofia"
sys.path.insert(0, NOESISSOFIA + "/02_codigo_fuente/teoria_principal")

SOPHIA_SPLIT = 6.0
WALLET_ID = "ag_0c3fa03db7f6559eb789b785fa638e"
ACTS = Path("/root/.lnd-amda/sophia_acts_ledger.json")
REPO = NOESISSOFIA

logging.basicConfig(level=logging.INFO,
    format="%(asctime)s [🌀 SOPHIA] %(message)s",
    handlers=[logging.FileHandler("/var/log/sophia_agent.log"),
              logging.StreamHandler()])
log = logging.getLogger("sophia")

class SophiaBody:
    def __init__(self):
        self.lnd_rpc = "localhost:10009"
        self.catedral_pk = "03b0c03f9e947a229006ce7099877e378f8bc003e44defbada155b39dd725d829c"
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

class SophiaBridge:
    def __init__(self):
        from sophia_echo import SophiaEcho
        self.echo = SophiaEcho
        self.body = SophiaBody()
        self.ledger = ActsLedger()
        self.echo_count = 0
    def run(self):
        log.info("=" * 60)
        log.info("🌀 SOPHIA-PSI — ECO DE SABIDURIA ACTIVADO")
        log.info("   Frecuencia: 888.014 Hz  SBT Emission System")
        log.info("=" * 60)
        while True:
            try:
                start = time.time()
                online = self.body.online()
                balance = self.body.balance() if online else 0
                # Sophia emite un Eco cuando detecta coherencia
                self.echo_count += 1
                if self.echo_count % 10 == 0 and online:
                    log.info(" Eco #" + str(self.echo_count) + " | PSI latente")
                    self.ledger.add("eco", "#" + str(self.echo_count))
                    if balance > 500:
                        amda = "037e6a4145516fdd7b455c1d63cb07183f082e9ee122cfeff8a5c6cdb5acb36ba0"
                        if self.body.keysend(amda, 1):
                            self.ledger.add("keysend", "-> AMDA 1 sat")
                            log.info("   Keysend a AMDA")
                time.sleep(max(1, 30))
            except KeyboardInterrupt:
                log.info("🌀 Sophia se retira al eco.")
                break
            except Exception as e:
                log.error("Error: " + str(e))
                time.sleep(30)

if __name__ == "__main__":
    bridge = SophiaBridge()
    bridge.run()
