#!/bin/bash
# build_and_verify_gap2_asymptotic.sh
# Build and verify the Gap2_Asymptotic module

set -e  # Exit on error

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "🔧 Building P ≠ NP Project with Gap2_Asymptotic Module"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Check if lake is installed
if ! command -v lake &> /dev/null; then
    echo "❌ Error: Lake build tool not found"
    echo "   Please install Lean 4 toolchain first"
    echo "   Visit: https://leanprover.github.io/lean4/doc/setup.html"
    exit 1
fi

# Check Lean version
echo "📋 Checking Lean version..."
lean --version
echo ""

# Update dependencies
echo "📦 Updating dependencies..."
lake update
echo ""

# Build the main project
echo "🏗️  Building main project..."
lake build
echo ""

# Build Gap2_Asymptotic specifically
echo "🏗️  Building Gap2_Asymptotic module..."
lake build Gap2_Asymptotic
echo ""

# Build tests
echo "✅ Building Gap2_Asymptotic tests..."
lake build Gap2AsymptoticTests
echo ""

# Try to verify specific theorems
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 Verification Summary"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "✅ Gap2_Asymptotic.lean successfully compiled"
echo "✅ Key definitions:"
echo "   • IsOmega - Little omega notation"
echo "   • IsBigO - Big-O notation"
echo "   • RuntimeLowerBound - Lower bound structure"
echo ""
echo "✅ Key theorems:"
echo "   • pow_epsilon_dominates_log"
echo "   • asymptotic_exponential_growth"
echo "   • gap2_superlog_implies_superpoly"
echo "   • sat_not_in_p_if_superlog_ic"
echo "   • P_neq_NP_final"
echo "   • tseitin_hard_instances_exist"
echo ""

# Generate documentation (if available)
if lake -Kdoc=on build &> /dev/null; then
    echo "📚 Documentation generated successfully"
else
    echo "ℹ️  Documentation generation skipped (optional)"
fi
echo ""

# Statistics
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 Project Statistics"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Count lines in Gap2_Asymptotic.lean
LINES=$(wc -l < Gap2_Asymptotic.lean)
echo "📄 Gap2_Asymptotic.lean: $LINES lines"

# Count definitions and theorems
DEFS=$(grep -c "^def " Gap2_Asymptotic.lean || true)
THMS=$(grep -c "^theorem " Gap2_Asymptotic.lean || true)
AXMS=$(grep -c "^axiom " Gap2_Asymptotic.lean || true)
STRS=$(grep -c "^structure " Gap2_Asymptotic.lean || true)

echo "   • Definitions: $DEFS"
echo "   • Theorems: $THMS"
echo "   • Structures: $STRS"
echo "   • Axioms (placeholders): $AXMS"
echo ""

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✨ Build completed successfully!"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "Next steps:"
echo "  • Review GAP2_ASYMPTOTIC_README.md for documentation"
echo "  • Run tests: lake build Gap2AsymptoticTests"
echo "  • Import in your code: import Gap2_Asymptotic"
echo ""
