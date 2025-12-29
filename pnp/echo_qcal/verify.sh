#!/bin/bash
echo "🔐 Verificación rápida Echo-QCAL ∞³"
echo "===================================="
if command -v python >/dev/null 2>&1; then
  python C_k_verification.py --simple
elif command -v python3 >/dev/null 2>&1; then
  python3 C_k_verification.py --simple
else
  echo "Error: Neither 'python' nor 'python3' is available in PATH." >&2
  exit 1
fi
