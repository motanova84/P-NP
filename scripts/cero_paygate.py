#!/usr/bin/env python3
"""
QCAL CERO->PAYGATE v1.0 - Transmutacion inyecta valor directo
Puente: Cero de Riemann -> piCODE -> Credito de Validacion Noetica
BAL-003 | f0 = 141.7001 Hz
"""
import json, hashlib, logging, os, sys
from datetime import datetime, timezone
from pathlib import Path

SELLO = '∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ'
F0 = 141.7001
TRACKING_FILE = Path('/root/picode_blocks/cero_tracking.json')
FLOW_LEDGER = Path('/root/paygate_flow_ledger.json')
CREDIT_PCT = float(os.environ.get('CERO_PAYGATE_PCT', '10.0'))

logging.basicConfig(level=logging.INFO, format='%(asctime)s [CERO>GATE] %(message)s',
    handlers=[logging.FileHandler('/var/log/cero_paygate.log'), logging.StreamHandler()])
log = logging.getLogger('cero_paygate')

def cargar_tracking():
    if not TRACKING_FILE.exists():
        log.error('Tracking no encontrado: %s', TRACKING_FILE)
        return None
    try:
        with open(TRACKING_FILE) as f:
            return json.load(f)
    except Exception as e:
        log.error('Error: %s', e)
        return None

def ultimo_batch(tracking):
    batches = tracking.get('batches', tracking.get('bloques', []))
    return batches[-1] if batches else None

def procesar():
    log.info('=' * 50)
    log.info('CERO>PAYGATE - Iniciando (credito: %.1f%%)', CREDIT_PCT)
    tracking = cargar_tracking()
    if not tracking:
        sys.exit(1)
    batch = ultimo_batch(tracking)
    if not batch:
        log.error('Sin batches')
        sys.exit(1)
    total = batch.get('total_picode', 0)
    credito = total * (CREDIT_PCT / 100.0)
    d = batch.get('desde', '?')
    h = batch.get('hasta', '?')
    log.info('Batch %s->%s: %.2f piC -> credito %.2f piC', d, h, total, credito)
    nonce = os.urandom(8).hex()
    raw = f'{credito}|{d}-{h}|{nonce}|{F0}|{SELLO}'
    hsh = hashlib.sha3_512(raw.encode()).hexdigest()[:64]
    flujo = {'tipo': 'CERO_PICODE_VALIDATION',
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'batch_desde': d, 'batch_hasta': h,
        'n_ceros': batch.get('n_ceros', 100),
        'total_picode_batch': total,
        'credito_picode': round(credito, 2),
        'porcentaje': CREDIT_PCT,
        'hash_validacion': hsh[:16],
        'nonce': nonce, 'frecuencia_hz': F0,
        'sello': SELLO}
    try:
        ledger = {'flujos': []}
        if FLOW_LEDGER.exists():
            with open(FLOW_LEDGER) as f:
                ledger = json.load(f)
        ledger.setdefault('flujos', []).append(flujo)
        ledger['flujos'] = ledger['flujos'][-1000:]
        with open(FLOW_LEDGER, 'w') as f:
            json.dump(ledger, f, indent=2, ensure_ascii=False)
        log.info('Registrado: %.2f piC | Hash: %s', credito, hsh[:8])
    except Exception as e:
        log.error('Error: %s', e)
        sys.exit(1)
    log.info('CERO>PAYGATE COMPLETADO')
    log.info('=' * 50)

if __name__ == '__main__':
    procesar()
