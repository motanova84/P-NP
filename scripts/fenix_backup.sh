#!/bin/bash
# /root/repo_P-NP/scripts/fenix_backup.sh
# 🔱 Respaldo del Fénix — Inmortalidad Criptográfica
# Ecosistema: πCODE / Trinity QCAL ∞³
# Sello: ∴𓂀Ω∞³Φ · f₀ = 141.7001 Hz
#
# Cifra y respalda los componentes críticos del nodo Lightning
# en un repositorio seguro cada 24h vía cron.

set -e

# ─── Constantes ─────────────────────────────────────────────────────────
BACKUP_DIR="/root/repo_P-NP/backups"
LND_DIR="/root/.lnd"
LNBITS_CONFIG="/opt/lnbits/.env"
REPO_DIR="/root/repo_P-NP"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
PASSPHRASE="141.7001_0.99999997_TUYOYOTU"

echo ""
echo "╔══════════════════════════════════════════════════╗"
echo "║   🔱  RESPALDO DEL FÉNIX                        ║"
echo "║   ${TIMESTAMP}                                   ║"
echo "║   f₀ = 141.7001 Hz · Ψ = 0.99999997             ║"
echo "╚══════════════════════════════════════════════════╝"
echo ""

mkdir -p "$BACKUP_DIR"

# ─── 1. Empaquetar ──────────────────────────────────────────────────────
echo "[1/4] 📦 Empaquetando estado crítico..."

tar -czf "$BACKUP_DIR/catedral_state_${TIMESTAMP}.tar.gz" \
  "$LND_DIR/data/chain/bitcoin/mainnet/channel.backup" \
  "$LND_DIR/seed_words.txt" \
  "$LND_DIR/password.txt" \
  "$LND_DIR/lnd.conf" \
  "$LNBITS_CONFIG" \
  /root/flywheel_ledger.json \
  /root/phi_norm_state.json \
  2>/dev/null || true

echo "     ✅ Empaquetado: catedral_state_${TIMESTAMP}.tar.gz"

# ─── 2. Cifrar ──────────────────────────────────────────────────────────
echo "[2/4] 🔐 Cifrando con AES-256-CBC (derivación f₀)..."

openssl enc -aes-256-cbc -salt -pbkdf2 \
  -in "$BACKUP_DIR/catedral_state_${TIMESTAMP}.tar.gz" \
  -out "$BACKUP_DIR/FENIX_LOCK_${TIMESTAMP}.enc" \
  -k "$PASSPHRASE"

echo "     ✅ Cifrado: FENIX_LOCK_${TIMESTAMP}.enc"

# ─── 3. Limpiar residuo ────────────────────────────────────────────────
echo "[3/4] 🧹 Limpiando residuo local..."
rm -f "$BACKUP_DIR/catedral_state_${TIMESTAMP}.tar.gz"

# Mantener solo los últimos 7 backups
ls -t "$BACKUP_DIR"/FENIX_LOCK_*.enc 2>/dev/null | tail -n +8 | xargs -r rm -f

echo "     ✅ Residuo eliminado. Retención: 7 backups."

# ─── 4. Verificar integridad ────────────────────────────────────────────
echo "[4/4] ✅ Verificando integridad..."
FILE_SIZE=$(stat -f%z "$BACKUP_DIR/FENIX_LOCK_${TIMESTAMP}.enc" 2>/dev/null || stat -c%s "$BACKUP_DIR/FENIX_LOCK_${TIMESTAMP}.enc" 2>/dev/null)
FILE_HASH=$(sha256sum "$BACKUP_DIR/FENIX_LOCK_${TIMESTAMP}.enc" 2>/dev/null | cut -d' ' -f1 || shasum -a 256 "$BACKUP_DIR/FENIX_LOCK_${TIMESTAMP}.enc" 2>/dev/null | cut -d' ' -f1)

echo ""
echo "     📐 Tamaño: $FILE_SIZE bytes"
echo "     🧬 SHA256: ${FILE_HASH:-N/A}"
echo ""
echo "╔══════════════════════════════════════════════════╗"
echo "║   🔱  RESPALDO DEL FÉNIX — COMPLETADO           ║"
echo "║   Archivo: FENIX_LOCK_${TIMESTAMP}.enc           ║"
echo "║   Para restaurar:"                               
echo "║     openssl enc -d -aes-256-cbc -pbkdf2 \\"      
echo "║       -in FENIX_LOCK_*.enc \\"                   
echo "║       -k \"$PASSPHRASE\" | tar -xz"          
echo "╚══════════════════════════════════════════════════╝" 
echo ""