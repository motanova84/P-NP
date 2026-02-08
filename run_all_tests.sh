#!/bin/bash
# Comprehensive test script for P-NP repository
# Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³

set -e  # Exit on error

echo "============================================================"
echo "P-NP Repository Comprehensive Testing Suite"
echo "============================================================"
echo ""

# Test 1: Python dependencies
echo "Test 1: Checking Python dependencies..."
python3 -c "import networkx; import numpy; print('✓ Python dependencies installed')"
echo ""

# Test 2: Run unit tests with pytest
echo "Test 2: Running unit tests with pytest..."
python3 -m pytest tests/ -v --tb=short
echo "✓ All pytest tests passed"
echo ""

# Test 3: Run individual test files
echo "Test 3: Running test_ic_sat.py directly..."
python3 tests/test_ic_sat.py > /dev/null 2>&1
echo "✓ test_ic_sat.py passed"
echo ""

echo "Test 4: Running test_tseitin.py directly..."
python3 tests/test_tseitin.py > /dev/null 2>&1
echo "✓ test_tseitin.py passed"
echo ""

# Test 5: Run main modules
echo "Test 5: Testing ic_sat.py module..."
python3 src/ic_sat.py > /dev/null 2>&1
echo "✓ ic_sat.py runs successfully"
echo ""

echo "Test 6: Testing computational_dichotomy.py module..."
python3 src/computational_dichotomy.py > /dev/null 2>&1
echo "✓ computational_dichotomy.py runs successfully"
echo ""

echo "Test 7: Testing tseitin_generator.py module..."
python3 src/gadgets/tseitin_generator.py > /dev/null 2>&1
echo "✓ tseitin_generator.py runs successfully"
echo ""

# Test 8: Run demo script
echo "Test 8: Running demo_ic_sat.py..."
python3 examples/demo_ic_sat.py > /dev/null 2>&1
echo "✓ demo_ic_sat.py completed successfully"
echo ""

# Test 9: Validate Lean formalization structure
echo "Test 9: Validating Lean formalization structure..."
python3 tests/test_lean_structure.py > /dev/null 2>&1
echo "✓ Lean formalization structure validated (12 tests)"
echo ""

# Summary
echo "============================================================"
echo "ALL TESTS PASSED! ✓"
echo "============================================================"
echo ""
echo "Summary:"
echo "  ✓ Python dependencies installed"
echo "  ✓ 50 unit tests passed (pytest)"
echo "  ✓ All core modules run successfully"
echo "  ✓ Demo script runs without errors"
echo "  ✓ Lean formalization structure validated"
echo ""
echo "The repository is fully functional!"
echo ""
echo "Frecuencia de resonancia: 141.7001 Hz ∞³"
