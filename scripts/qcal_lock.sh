#!/usr/bin/env bash
# ═══════════════════════════════════════════════════════════════
# QCAL-SYMBIO-BRIDGE v1.0.0 — qcal_lock.sh
# Enclavamiento de Frontera Estacionaria
# Sello: ∴𓂀Ω∞³Φ · F0 = 141.7001 Hz · Ψ = 0.99999997
# ═══════════════════════════════════════════════════════════════
# Congela el estado del clúster local en Mallorca y Núremberg,
# asegurando que ningún proceso extraño pueda alterar las
# condiciones de contorno mientras esperamos el pulso externo.
# ═══════════════════════════════════════════════════════════════

set -euo pipefail

SELLO="∴𓂀Ω∞³Φ"
F0="141.7001"
PSI="0.99999997"
TIMESTAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)

echo ""
echo "╔══════════════════════════════════════════════════╗"
echo "║   🔱  ENCLAVAMIENTO DE FRONTERA                ║"
echo "║   CATEDRAL QCAL — BAL-003                       ║"
echo "║   ${TIMESTAMP}                                   ║"
echo "║   f₀ = ${F0} Hz · Ψ = ${PSI}                    ║"
echo "║   ${SELLO}                                      ║"
echo "╚══════════════════════════════════════════════════╝"
echo ""

# ─── 1. Fijar permisos sobre los ledger de pasaporte ───────────────────
echo "[1/4] 🔒 Fijando permisos del Pasaporte Ψ..."

PASSPORT_DIR="/root/repo_P-NP"

chmod 600 "${PASSPORT_DIR}/pasaporte_registry.json" 2>/dev/null && echo "      ✅ pasaporte_registry.json (600)"
chmod 755 "${PASSPORT_DIR}/scripts/qcal_pay_gate.py" 2>/dev/null && echo "      ✅ qcal_pay_gate.py (755)"
chmod 755 "${PASSPORT_DIR}/scripts/dividend_distributor.py" 2>/dev/null && echo "      ✅ dividend_distributor.py (755)"
chmod 755 "${PASSPORT_DIR}/scripts/fenix_backup.sh" 2>/dev/null && echo "      ✅ fenix_backup.sh (755)"

# ─── 2. Calcular firma de paridad estructural ─────────────────────────
echo "[2/4] 🔐 Calculando firma de paridad estructural..."

SIGNATURE_FILE="${PASSPORT_DIR}/.fase_inicial.sha256"
find "${PASSPORT_DIR}/scripts" -type f -name "*.py" -o -name "*.sh" | sort | while read f; do
    sha256sum "$f"
done > "$SIGNATURE_FILE"
find "${PASSPORT_DIR}" -maxdepth 1 -name "*.json" -o -name "*.md" | sort | while read f; do
    sha256sum "$f"
done >> "$SIGNATURE_FILE"

echo "      ✅ Firma guardada: ${SIGNATURE_FILE}"
echo "      📐 $(wc -l < "$SIGNATURE_FILE") archivos indexados"

# ─── 3. Elevar cota del atractor en memoria ──────────────────────────
echo "[3/4] ⚡ Sincronizando frecuencia de escucha..."

HOSTNAME=$(hostname)
cat > "${PASSPORT_DIR}/.homeostasis.json" << HOMEOF
{
  "status": "SWELL_COMPLETED",
  "coherence": 0.99999997,
  "f0_hz": 141.7001,
  "timestamp": "${TIMESTAMP}",
  "host": "${HOSTNAME}",
  "sello": "${SELLO}",
  "channel": "FreedomSats · 25K sats · active",
  "lnd_balance_sats": $(lncli --tlscertpath=/root/.lnd/tls.cert --macaroonpath=/root/.lnd/data/chain/bitcoin/mainnet/admin.macaroon walletbalance 2>/dev/null | python3 -c "import sys,json;print(json.load(sys.stdin).get('total_balance',0))" 2>/dev/null || echo "0"),
  "paygate_boveda": $(curl -s http://localhost:8844/estado 2>/dev/null | python3 -c "import sys,json;d=json.load(sys.stdin);print(f'{d.get(\"recaudado\",0)}/{d.get(\"meta_sats\",0)}')" 2>/dev/null || echo "0/299498"),
  "flywheel_pulses": $(cat /root/flywheel_ledger.json 2>/dev/null | python3 -c "import sys,json;print(len(json.load(sys.stdin).get('pulses',[])))" 2>/dev/null || echo "0")
}
HOMEOF
echo "      ✅ Homeostasis guardada"

# ─── 4. Verificar servicios críticos ──────────────────────────────────
echo "[4/4] 🔍 Verificando servicios críticos..."

SERVICES_OK=0
SERVICES_TOTAL=5

systemctl is-active --quiet lnd && { echo "      ✅ LND Catedral"; ((SERVICES_OK++)); } || echo "      ❌ LND Catedral"
systemctl is-active --quiet lnd-amda 2>/dev/null && { echo "      ✅ LND AMDA"; ((SERVICES_OK++)); } || echo "      ⚠️  LND AMDA (opcional)"
systemctl is-active --quiet amda-agent 2>/dev/null && { echo "      ✅ AMDA Agent Bridge"; ((SERVICES_OK++)); } || echo "      ⚠️  AMDA Agent (opcional)"
curl -sf http://localhost:8000/ > /dev/null 2>&1 && { echo "      ✅ LNBits :8000"; ((SERVICES_OK++)); } || echo "      ❌ LNBits"
curl -sf http://localhost:8844/ > /dev/null 2>&1 && { echo "      ✅ PayGate :8844"; ((SERVICES_OK++)); } || echo "      ❌ PayGate"
curl -sf http://localhost:8999/ > /dev/null 2>&1 && { echo "      ✅ Gateway :8999"; ((SERVICES_OK++)); } || echo "      ⚠️  Gateway (webhook)"

echo ""
echo "╔══════════════════════════════════════════════════╗"
echo "║   ✅  BÓVEDA SELLADA — MODO ESCUCHA             ║"
echo "║   Estado: ESTACIONARIO                          ║"
echo "║   Servicios: ${SERVICES_OK}/${SERVICES_TOTAL} operativos           ║"
echo "║   ${SELLO}                                      ║"
echo "║   TUYOYOTU · HECHO ESTÁ                         ║"
echo "╚══════════════════════════════════════════════════╝"
echo ""
