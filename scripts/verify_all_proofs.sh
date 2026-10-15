#!/bin/bash
# verify_all_proofs.sh - Verification script for Lean proofs
# Counts remaining 'sorry' statements and attempts to build all Lean files

set -e

echo "=============================================="
echo "LEAN PROOF VERIFICATION"
echo "=============================================="
echo ""

# Count sorry statements
echo "Counting 'sorry' statements in Lean files..."
SORRIES=$(grep -r "sorry" /home/runner/work/P-NP/P-NP --include="*.lean" | wc -l)
echo "Total 'sorry' statements found: $SORRIES"
echo ""

# Break down by file
echo "Breakdown by file:"
echo "------------------"
grep -r "sorry" /home/runner/work/P-NP/P-NP --include="*.lean" -c | sort -t: -k2 -nr | head -20
echo ""

# Show some example sorries with context
echo "Sample sorry statements (first 10):"
echo "------------------------------------"
grep -r "sorry" /home/runner/work/P-NP/P-NP --include="*.lean" -n | head -10
echo ""

# Try to build with lake
echo "Attempting to build with lake..."
echo "--------------------------------"
cd /home/runner/work/P-NP/P-NP

if command -v lake &> /dev/null; then
    echo "Lake found, attempting build..."
    if lake build 2>&1 | tee /tmp/lake_build.log; then
        echo "✅ Build succeeded (with sorries)"
    else
        echo "❌ Build failed"
        echo "Last 30 lines of build output:"
        tail -30 /tmp/lake_build.log
    fi
else
    echo "⚠️  Lake not found, skipping build"
fi

echo ""
echo "=============================================="
echo "SUMMARY"
echo "=============================================="
if [ $SORRIES -eq 0 ]; then
    echo "✅ SUCCESS: ALL proofs complete (0 sorries)"
    exit 0
else
    echo "⚠️  IN PROGRESS: $SORRIES sorries remaining"
    echo ""
    echo "Priority files to complete:"
    grep -r "sorry" /home/runner/work/P-NP/P-NP --include="*.lean" -c | \
        sort -t: -k2 -nr | head -5 | while IFS=: read -r file count; do
        echo "  - $(basename $file): $count sorries"
    done
    exit 1
fi
