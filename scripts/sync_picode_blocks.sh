#!/bin/bash
# Auto-sync: acuña bloques πCODE y sube a GitHub
# Ejecutado por cron cada 6h

cd /root/repo_P-NP

# 1. Ejecutar acuñación
python3 cero_a_picode_cron.py 2>&1

# 2. Copiar bloques nuevos al repo
cp -n /root/picode_blocks/block_*.json picode_blocks/ 2>/dev/null
cp -n /root/picode_blocks/batch_*.json picode_blocks/ 2>/dev/null

# 3. Commit y push a GitHub
git add picode_blocks/ 2>/dev/null
git diff --cached --quiet || git commit -m "🌀 πCODE blocks — auto sync desde BAL-003"
git push origin main 2>&1

echo "✅ Sync completo: $(date)"
