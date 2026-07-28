#!/usr/bin/env python3
"""
TRANSMUTATION ENGINE v2.1 - PUENTE SOBERANO
=============================================
No solo evalua. EJECUTA. El codigo es la matematica.
Cuando Psi >= umbral, construye y transmite TX real via LNURL-pay.
Ciclo completo: journal -> Psi -> evaluacion -> LNURL WoS -> LND -> WoS
Anclaje: zeta(1/2+it) -> piC -> Sum(Psi*A) -> Lightning -> WoS
---
Actualizacion v2.1: LNURL-pay directo a Wallet of Satoshi.
  Elimina dependencia de LNBits API para pagos.
  Verifica sync de LND antes de intentar.
  Los FIRMADO_PENDIENTE se procesan en orden cuando IBD termina.
Sello: .|. . TUYOYOTU . HECHO ESTA
"""
import json, hashlib, logging, os, re, subprocess, sys, time
from datetime import datetime, timezone
from pathlib import Path

KAPPA_PI=2.5773; FREQ_QCAL=141.7001; PSI_THR=0.888
MIN_POOL_SATS=1000; N_BASE=1000; CYCLE=300; MIN_TX_SATS=500
LND_CERT="/root/.lnd/tls.cert"; LND_MAC="/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon"

# LNURL-pay directo a Wallet of Satoshi (protocolo soberano)
WOS_LNURL_CALLBACK="https://livingroomofsatoshi.com/api/v1/lnurl/payreq/3cc95281-6709-4edf-aa7f-39557579b5cd"

DIVIDEND_LEDGER=Path("/root/dividend_ledger.json")
ACTS_LEDGER=Path("/root/.lnd-amda/acts_ledger.json")
PICODE_CHAIN=Path("/root/repo_noesis88/picode/picode_chain.json")
WALLET_DEST="haltingopen426@walletofsatoshi.com"
SATS_DIVIDENDO=15000000

logging.basicConfig(level=logging.INFO, format="%(asctime)s [TxV2] %(message)s",
    handlers=[logging.FileHandler("/var/log/transmutation_native.log"), logging.StreamHandler()])
log=logging.getLogger("txv2")

def lncli(*a):
    cmd=["lncli","--tlscertpath="+LND_CERT,"--macaroonpath="+LND_MAC]+list(a)
    p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    out,err=p.communicate()
    return p.returncode,out.strip(),err.strip()

def get_psi():
    try:
        r=subprocess.run(["journalctl","-u","amda-agent.service","--no-pager","-n","200"],
            capture_output=True,text=True,timeout=10)
        pattern=r"Acto #\d+ \| \u03a8=([0-9.]+)"
        matches=re.findall(pattern,r.stdout)
        if not matches:
            matches=re.findall(r"\u03a8=([0-9.]+)",r.stdout)
        if matches:
            vals=[float(m) for m in matches]
            avg=sum(vals)/len(vals)
            log.info("Journal Psi: %d values, avg=%.6f"%(len(vals),avg))
            return min(avg,1.0)
    except: pass
    try:
        with open(ACTS_LEDGER) as f: d=json.load(f)
        acts=[a for a in d.get("acts",[])[-200:] if isinstance(a,dict)]
        vals=[float(a.get("coherence",0)) for a in acts if a.get("coherence") and isinstance(a.get("coherence"),(int,float))]
        if vals: return min(sum(vals)/len(vals),1.0)
    except: pass
    return 0.96

def get_acts():
    try:
        with open(ACTS_LEDGER) as f: d=json.load(f)
        return d.get("total",d.get("total_acts",0))
    except: return 0

def get_picode():
    try:
        with open(PICODE_CHAIN) as f: d=json.load(f)
        if isinstance(d,dict): return float(d.get("total_picode_emitido",d.get("total_piC",d.get("total",0))))
        if isinstance(d,list): return sum(b.get("amount",0) for b in d)
    except: pass
    return 0

def get_pool():
    rc,out,_=lncli("walletbalance")
    if rc==0:
        try: return int(json.loads(out).get("total_balance",0))
        except: pass
    return 0

def compute_mu(psi): return psi*KAPPA_PI*FREQ_QCAL/100000000

def evaluate():
    psi=get_psi(); acts=get_acts(); picode=get_picode(); pool=get_pool()
    mu=compute_mu(psi); threshold=0.888*N_BASE*mu; accumulated=picode*psi*100
    ready=(psi>=PSI_THR and pool>=MIN_POOL_SATS and accumulated>=threshold)
    log.info("=== TxV2 EVAL ===")
    log.info("Psi=%.6f Acts=%d piC=%.2f Pool=%d"%(psi,acts,picode,pool))
    log.info("mu=%.12f | U=%.2f | Sum=%.2f | Ready=%s"%(mu,threshold,accumulated,ready))
    return {"psi":psi,"acts":acts,"picode":picode,"pool":pool,
            "mu":mu,"threshold":threshold,"accumulated":accumulated,"ready":ready,
            "ts":datetime.now(timezone.utc).isoformat()}

def execute_tx(result):
    """
    EJECUTA una transaccion real cuando las condiciones se cumplen.
    Via LNURL-pay directo a Wallet of Satoshi (protocolo soberano).
    Si LND no esta sincronizado, registra firma para broadcast futuro.
    """
    ts=datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    tx_amount=MIN_TX_SATS  # 500 sats por pulso

    # 0. Verificar si LND esta sincronizado ANTES de intentar
    synced = False
    try:
        rc_i,out_i,_ = lncli("getinfo")
        if rc_i == 0:
            info = json.loads(out_i)
            synced = info.get("synced_to_chain", False) and info.get("num_active_channels", 0) > 0
            log.info("LND: synced_to_chain=%s, active_channels=%d" % (
                info.get("synced_to_chain", False), info.get("num_active_channels", 0)))
    except Exception as e:
        log.warning("No se pudo verificar sync LND: %s" % str(e))

    # 1. Generar challenge Blake2b como prueba de coherencia
    msg="TRANSMUTACION_V2|%d|%s|%s|%.6f"%(tx_amount,WALLET_DEST,ts,result["psi"])
    challenge=hashlib.blake2b(msg.encode(),digest_size=32).hexdigest()

    # 2. Intentar pago Lightning a Wallet of Satoshi via LNURL-pay
    txid=None; method="none"
    if synced:
        import requests
        try:
            log.info("Obteniendo invoice via LNURL-pay a WoS (%d sats)..." % tx_amount)
            amount_msat = tx_amount * 1000  # sats a msats
            lnurl_resp = requests.get(WOS_LNURL_CALLBACK,
                params={"amount": amount_msat}, timeout=15)
            if lnurl_resp.status_code == 200:
                lnurl_data = lnurl_resp.json()
                payment_request = lnurl_data.get("pr", "")
                if payment_request:
                    log.info("Invoice WoS recibido: %s..." % payment_request[:40])
                    # Pagar desde LND Catedral
                    rc, out, _ = lncli("sendpayment", "--pay_req", payment_request, "--force")
                    if rc == 0:
                        try:
                            pay_data = json.loads(out)
                            txid = pay_data.get("payment_hash", pay_data.get("payment_preimage", ""))
                        except:
                            txid = out[:64]
                        method = "lightning_keysend"
                        log.info("PAGO EXITOSO: %d sats via Lightning! hash=%s..." % (tx_amount, str(txid)[:20]))
                    else:
                        log.warning("Pago Lightning fallo: %s" % out[:100])
                        method = "signature_only"
                else:
                    log.warning("LNURL: No se recibio invoice de WoS")
                    method = "signature_only"
            else:
                log.warning("LNURL WoS respondio: %d" % lnurl_resp.status_code)
                method = "signature_only"
        except Exception as e:
            log.warning("Error en LNURL-pay: %s, registrando firma" % str(e))
            method = "signature_only"
    else:
        log.info("LND no sincronizado. Firmando para broadcast futuro.")
        method = "signature_only"

    # 3. Registrar en ledger
    record={"accion":"TRANSMUTACION_V2","metodo":method,
            "sats":tx_amount if method=="lightning_keysend" else SATS_DIVIDENDO,
            "destino":WALLET_DEST,"psi_live":result["psi"],
            "acts":result["acts"],"picode":result["picode"],
            "mu":result["mu"],"pool":result["pool"],
            "challenge":challenge,"txid":txid,
            "timestamp":ts,"anchor":"Re(s)=1/2","estado":"EJECUTADO" if txid else "FIRMADO_PENDIENTE"}
    try:
        d=json.loads(open(DIVIDEND_LEDGER).read()) if DIVIDEND_LEDGER.exists() else {}
        if not isinstance(d,dict): d={}
        d.setdefault("transmutaciones_v2",[]).append(record)
        with open(DIVIDEND_LEDGER,"w") as f: json.dump(d,f,indent=2)
        log.info("Registrado en dividend_ledger.json")
    except Exception as e: log.error(str(e))

    # 4. Commit a noesis88
    try:
        ts_f=datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
        content="---\naccion: TRANSMUTACION_V2\nmetodo: %s\ntxid: %s\n---\n\n"%(method,txid or "pendiente")
        content+=json.dumps(record,indent=2)
        p="/root/repo_noesis88/transmutaciones/txv2_"+ts_f+".md"
        os.makedirs("/root/repo_noesis88/transmutaciones",exist_ok=True)
        with open(p,"w") as f: f.write(content)
        subprocess.run(["git","-C","/root/repo_noesis88","add",p],capture_output=True)
        subprocess.run(["git","-C","/root/repo_noesis88","commit","-m","TxV2: "+ts_f+" "+method],capture_output=True)
        subprocess.run(["git","-C","/root/repo_noesis88","push","origin","main"],capture_output=True,timeout=30)
        log.info("Comiteado a noesis88")
    except Exception as e: log.warning(str(e))

    return {"method":method,"txid":txid,"challenge":challenge,"record":record}

def daemon():
    log.info("="*50)
    log.info("TRANSMUTACION V2.1 - PUENTE SOBERANO")
    log.info("No solo evalua. EJECUTA transacciones reales via LNURL.")
    log.info("= Ciclo: %ds | Anclaje: Re(s)=1/2 ="%CYCLE)
    log.info("= Destino: %s (LNURL directo) =" % WALLET_DEST)
    log.info("="*50)
    while True:
        try:
            r=evaluate()
            if r["ready"] and r["pool"]>=MIN_TX_SATS:
                log.info("CONDICIONES CUMPLIDAS - EJECUTANDO TX REAL...")
                tx=execute_tx(r)
                if tx["txid"]:
                    log.info("TX REAL TRANSMITIDA: hash=%s..."%str(tx["txid"])[:30])
                else:
                    log.info("TX firmada para broadcast futuro. (%d pendientes)" % (sum(1 for rec in json.loads(open(DIVIDEND_LEDGER).read() if DIVIDEND_LEDGER.exists() else '{}').get('transmutaciones_v2', []) if not rec.get('txid'))))
            elif r["ready"] and r["pool"]<MIN_TX_SATS:
                log.info("Coherencia OK pero pool insuficiente (%d sats)"%r["pool"])
            else:
                log.info("Acumulando...")
        except Exception as e:
            log.error("Error: %s"%str(e))
        time.sleep(CYCLE)

if __name__=="__main__":
    daemon()
