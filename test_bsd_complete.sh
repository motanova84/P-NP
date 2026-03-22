#!/bin/bash
echo "=========================================="
echo "BSD QCAL ∞³ - Complete Integration Test"
echo "=========================================="
echo ""

echo "1. Running BSD validation..."
python3 validate_bsd_spectral_resonance.py 2>&1 | grep -E "VALIDATION|Prime-17|Ψ–BEACON"
echo ""

echo "2. Running BSD demonstration..."
python3 demo_bsd_qcal_resolution.py 2>&1 | grep -E "DEMO|Status|✓|Ψ–BEACON" | head -20
echo ""

echo "3. Generating certificates..."
python3 generate_qcal_certificates.py 2>&1 | grep -E "certificate|✓|Ψ–BEACON"
echo ""

echo "4. Verifying certificate files exist..."
for file in BSD_Spectral_Certificate.qcal_beacon.json qcal_circuit_PNP.json bsd_spectral_validation_results.json; do
  if [ -f "$file" ]; then
    echo "  ✓ $file ($(stat -c%s $file) bytes)"
  else
    echo "  ✗ $file MISSING"
  fi
done
echo ""

echo "5. Running QCAL cross-verification..."
python3 cross_verification_protocol.py 2>&1 | grep -E "BSD|VERIFIED|COHERENT|Status"
echo ""

echo "=========================================="
echo "✓ BSD INTEGRATION TEST COMPLETE"
echo "=========================================="
