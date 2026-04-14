#!/bin/bash
# create_submission_package.sh - Create submission package for academic review

PACKAGE_NAME="P_neq_NP_submission_$(date +%Y%m%d)"
PACKAGE_DIR="/tmp/$PACKAGE_NAME"

echo "=================================================="
echo "CREATING SUBMISSION PACKAGE"
echo "=================================================="
echo ""

# Create package directory structure
echo "1. Creating directory structure..."
mkdir -p "$PACKAGE_DIR"/{proofs,code,data,results,docs}

# Copy Lean proofs
echo "2. Copying Lean formal proofs..."
if [ -d "formal" ]; then
    cp -r formal/* "$PACKAGE_DIR/proofs/" 2>/dev/null || true
fi
# Copy .lean files from root
cp *.lean "$PACKAGE_DIR/proofs/" 2>/dev/null || true

# Copy Python code
echo "3. Copying validation code..."
mkdir -p "$PACKAGE_DIR/code"
cp *.py "$PACKAGE_DIR/code/" 2>/dev/null || true
cp scripts/*.py "$PACKAGE_DIR/code/" 2>/dev/null || true
cp src/*.py "$PACKAGE_DIR/code/" 2>/dev/null || true

# Copy requirements
if [ -f "requirements.txt" ]; then
    cp requirements.txt "$PACKAGE_DIR/"
fi

# Copy key documentation
echo "4. Copying documentation..."
cp README.md "$PACKAGE_DIR/docs/" 2>/dev/null || true
cp QUICKSTART.md "$PACKAGE_DIR/docs/" 2>/dev/null || true

# Copy results if they exist
echo "5. Copying results..."
if [ -d "results" ]; then
    cp -r results/* "$PACKAGE_DIR/results/" 2>/dev/null || true
fi

# Create README for package
echo "6. Creating package README..."
cat > "$PACKAGE_DIR/README.md" << 'EOF'
# P ≠ NP Formal Proof Package

## Verification Steps

### Option 1: Formal Verification
Verify formal mathematics:

```bash
cd proofs && lake build
# This compiles all Lean proofs
```

### Option 2: Empirical Validation
Validate empirically:

```bash
cd code && python cross_validation.py
# Runs validation on multiple SAT instances
```

### Key Components

#### Main Theorem (Section 4)
- Lemma 6.24: proofs/StructuralCoupling/Complete.lean (if exists)
- Theorem P ≠ NP: proofs/P_neq_NP.lean

#### Empirical Validation (Section 6)
- Code: code/cross_validation.py
- Results: results/

#### Fundamental Constants
- κ_Π derivation: code/verify_kappa.py
- Validation: code/kappa_verification.py

### FAQ

Q: How do I check for incomplete proofs?
A: Run `grep -r "sorry" proofs/` - should return empty.

Q: How to reproduce results?
A: Execute `cd code && python cross_validation.py`

### Contact
Author: José Manuel Mota Burruezo
Email: institutoconsciencia@proton.me
Response time: < 24 hours
EOF

echo "7. Compressing package..."
cd /tmp
tar -czf "${PACKAGE_NAME}.tar.gz" "$PACKAGE_NAME"

echo ""
echo "✅ PACKAGE CREATED: ${PACKAGE_NAME}.tar.gz"
echo "Location: /tmp/${PACKAGE_NAME}.tar.gz"
echo "Size: $(du -sh /tmp/${PACKAGE_NAME}.tar.gz | cut -f1)"
echo ""
echo "Contents:"
ls -lh "$PACKAGE_DIR"

exit 0
