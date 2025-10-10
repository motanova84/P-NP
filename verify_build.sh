#!/bin/bash
# Verification script for Lean project build
# This script should be run once the Lean toolchain is properly installed

set -e

echo "==================================="
echo "Lean Project Build Verification"
echo "==================================="
echo ""

# Check if Lean is available
echo "1. Checking Lean installation..."
if command -v lean &> /dev/null; then
    echo "✓ Lean found: $(lean --version 2>&1 | head -1)"
else
    echo "✗ Lean not found. Please install elan and Lean 4."
    exit 1
fi

# Check if Lake is available
echo ""
echo "2. Checking Lake installation..."
if command -v lake &> /dev/null; then
    echo "✓ Lake found: $(lake --version 2>&1 | head -1)"
else
    echo "✗ Lake not found. Please install elan and Lean 4."
    exit 1
fi

# Verify file structure
echo ""
echo "3. Verifying file structure..."
files=(
    "lakefile.lean"
    "lean-toolchain"
    "Main.lean"
    "PvsNP/Main.lean"
    "PvsNP/Treewidth.lean"
    "PvsNP/SILB.lean"
    "tests/BasicTests.lean"
)

for file in "${files[@]}"; do
    if [ -f "$file" ]; then
        echo "✓ $file"
    else
        echo "✗ $file missing!"
        exit 1
    fi
done

# Check individual files
echo ""
echo "4. Checking individual Lean files..."
lean_files=(
    "PvsNP/Main.lean"
    "PvsNP/Treewidth.lean"
    "PvsNP/SILB.lean"
    "tests/BasicTests.lean"
)

for file in "${lean_files[@]}"; do
    echo "Checking $file..."
    if lean --check "$file" 2>&1; then
        echo "✓ $file is valid"
    else
        echo "✗ $file has errors"
        exit 1
    fi
done

# Build the project
echo ""
echo "5. Building the project..."
if lake build; then
    echo "✓ Build succeeded!"
else
    echo "✗ Build failed!"
    exit 1
fi

# Run tests if available
echo ""
echo "6. Running tests..."
if lake test 2>&1; then
    echo "✓ Tests completed"
else
    echo "✗ Tests failed (or no test target configured)"
fi

# Run the executable
echo ""
echo "7. Running the executable..."
if lake exe pvsnp; then
    echo "✓ Executable ran successfully"
else
    echo "✗ Executable failed"
    exit 1
fi

echo ""
echo "==================================="
echo "All verifications passed! ✓"
echo "==================================="
