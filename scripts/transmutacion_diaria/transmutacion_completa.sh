#!/bin/bash
# Transmutacion Diaria Completa - Fee Sweep + Quema + Recompra
# Ejecutado por el timer systemd a las 00:00 UTC
# v2.0 - Incluye Fee Sweep LND -> Bitcoin Core wallet catedral

echo "[$(date)] ==========================================="
echo "[$(date)] 🌀 CICLO DIARIO COMPLETO v2.0"
echo "[$(date)] Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ"
echo "[$(date)] ==========================================="

# Fase 0: Fee Sweep - asegurar UTXO para OP_RETURN
echo "[$(date)] 🔄 Fase 0: Fee Sweep - verificando wallet catedral..."
python3 /root/repo_P-NP/scripts/fee_sweep.py once
echo "[$(date)] ✅ Fee Sweep completado."

# 1. Transmutacion diaria (quema 44,400 piC + OP_RETURN)
echo "[$(date)] 🔥 Fase 1: Quema y anclaje..."
python3 /root/repo_P-NP/scripts/transmutacion_diaria/picode_transmutador.py --once
RESULT=$?
if [ $RESULT -ne 0 ]; then
    echo "[$(date)] ❌ Error en transmutacion. Codigo: $RESULT"
    exit 1
fi
echo "[$(date)] ✅ Quema y OP_RETURN completados."

# 2. Recompra automatica 12% (distribucion a 6 wallets)
echo "[$(date)] 💰 Fase 2: Recompra y distribucion..."
python3 /root/repo_P-NP/scripts/transmutacion_diaria/automatic_buyback_12pct.py
RESULT2=$?
if [ $RESULT2 -ne 0 ]; then
    echo "[$(date)] ❌ Error en recompra. Codigo: $RESULT2"
    exit 2
fi
echo "[$(date)] ✅ Recompra y distribucion 2A2 completada."

echo "[$(date)] ==========================================="
echo "[$(date)] 💸 Fase 3: Liquidando creditos a Wallet of Satoshi..."
python3 /root/repo_P-NP/scripts/ledger_to_wallet.py once
echo "[$(date)] ✅ Liquidacion completada."

echo "[$(date)] 🎯 CICLO DIARIO COMPLETO v3.0 - OK"
echo "[$(date)] Quema + OP_RETURN + Split 2A2 ejecutados"
echo "[$(date)] Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ"
echo "[$(date)] Silence Burden activo hasta proximo ciclo."
echo "[$(date)] ==========================================="
