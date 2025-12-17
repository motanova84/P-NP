#!/bin/bash
# audit_sorries.sh - Audit Lean proofs for 'sorry' placeholders

echo "=================================================="
echo "AUDITING LEAN PROOFS FOR 'sorry' STATEMENTS"
echo "=================================================="
echo ""

# Find all .lean files
LEAN_FILES=$(find . -name "*.lean" -type f)

if [ -z "$LEAN_FILES" ]; then
    echo "⚠️  No .lean files found"
    exit 1
fi

# Count total .lean files
TOTAL_FILES=$(echo "$LEAN_FILES" | wc -l)
echo "Scanning $TOTAL_FILES Lean files..."
echo ""

# Search for 'sorry' statements
SORRY_RESULTS=$(grep -rn "sorry" --include="*.lean" . 2>/dev/null)

if [ -z "$SORRY_RESULTS" ]; then
    echo "✅ NO 'sorry' STATEMENTS FOUND"
    echo ""
    echo "All proofs are complete!"
    echo ""
    echo "Files scanned: $TOTAL_FILES"
    exit 0
else
    echo "❌ FOUND 'sorry' STATEMENTS:"
    echo ""
    echo "$SORRY_RESULTS"
    echo ""
    
    # Count sorries
    SORRY_COUNT=$(echo "$SORRY_RESULTS" | wc -l)
    echo "Total 'sorry' statements: $SORRY_COUNT"
    echo ""
    echo "⚠️  Proofs are incomplete. Please complete all 'sorry' placeholders."
    exit 1
fi
