"""
DIMACS CNF File Reader/Writer
==============================

Utilities for reading and writing CNF formulas in DIMACS format.

DIMACS CNF format:
- Comments start with 'c'
- Problem line: p cnf <num_vars> <num_clauses>
- Clauses: space-separated literals ending with 0

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

from typing import List, Tuple
import os


def read_cnf_file(filename: str) -> Tuple[int, List[List[int]]]:
    """
    Read a CNF formula from a DIMACS file.
    
    Args:
        filename: Path to DIMACS CNF file
        
    Returns:
        Tuple of (num_vars, clauses)
        
    Raises:
        FileNotFoundError: If file doesn't exist
        ValueError: If file format is invalid
    """
    if not os.path.exists(filename):
        raise FileNotFoundError(f"File not found: {filename}")
    
    num_vars = 0
    num_clauses = 0
    clauses = []
    
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            
            # Skip empty lines
            if not line:
                continue
            
            # Skip comments
            if line.startswith('c'):
                continue
            
            # Parse problem line
            if line.startswith('p'):
                parts = line.split()
                if len(parts) != 4 or parts[1] != 'cnf':
                    raise ValueError(f"Invalid problem line: {line}")
                num_vars = int(parts[2])
                num_clauses = int(parts[3])
                continue
            
            # Parse clause
            literals = [int(x) for x in line.split()]
            
            # Remove trailing 0
            if literals and literals[-1] == 0:
                literals = literals[:-1]
            
            if literals:  # Don't add empty clauses from empty lines
                clauses.append(literals)
    
    if num_vars == 0:
        raise ValueError("No problem line found in file")
    
    return num_vars, clauses


def write_cnf_file(filename: str, num_vars: int, clauses: List[List[int]], 
                   comments: List[str] = None):
    """
    Write a CNF formula to a DIMACS file.
    
    Args:
        filename: Path to output file
        num_vars: Number of variables
        clauses: List of clauses
        comments: Optional list of comment lines
    """
    with open(filename, 'w') as f:
        # Write comments
        if comments:
            for comment in comments:
                f.write(f"c {comment}\n")
        
        # Write problem line
        f.write(f"p cnf {num_vars} {len(clauses)}\n")
        
        # Write clauses
        for clause in clauses:
            clause_str = ' '.join(str(lit) for lit in clause)
            f.write(f"{clause_str} 0\n")


def cnf_to_string(num_vars: int, clauses: List[List[int]]) -> str:
    """
    Convert CNF formula to readable string.
    
    Args:
        num_vars: Number of variables
        clauses: List of clauses
        
    Returns:
        Human-readable string representation
    """
    lines = [f"CNF Formula: {num_vars} variables, {len(clauses)} clauses"]
    lines.append("")
    
    for i, clause in enumerate(clauses):
        literals = []
        for lit in clause:
            if lit > 0:
                literals.append(f"x{lit}")
            else:
                literals.append(f"¬x{abs(lit)}")
        
        clause_str = " ∨ ".join(literals)
        lines.append(f"  Clause {i+1}: {clause_str}")
    
    return "\n".join(lines)


if __name__ == "__main__":
    import sys
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from src.ic_sat import ic_sat, compare_treewidths, simple_dpll
    
    print("=" * 70)
    print("DIMACS CNF File Reader ∞³")
    print("=" * 70)
    print()
    
    # Read the example CNF file
    example_file = os.path.join(os.path.dirname(__file__), '..', 
                                'examples', 'sat', 'simple_example.cnf')
    
    if os.path.exists(example_file):
        print(f"Reading: {example_file}")
        print("-" * 70)
        
        num_vars, clauses = read_cnf_file(example_file)
        
        print(cnf_to_string(num_vars, clauses))
        print()
        
        # Analyze the formula
        print("Analysis:")
        print("-" * 70)
        
        primal_tw, incidence_tw = compare_treewidths(num_vars, clauses)
        print(f"Primal treewidth: {primal_tw}")
        print(f"Incidence treewidth: {incidence_tw}")
        print()
        
        # Solve with different methods
        print("Solving:")
        print("-" * 70)
        
        result_dpll = simple_dpll(clauses, num_vars)
        print(f"DPLL result: {result_dpll}")
        
        result_icsat = ic_sat(num_vars, clauses, log=False)
        print(f"IC-SAT result: {result_icsat}")
        print()
    else:
        print(f"Example file not found: {example_file}")
        print()
        
        # Create a test example
        print("Creating test example:")
        print("-" * 70)
        
        num_vars = 3
        clauses = [[1, 2], [-1, 3], [-2, -3]]
        
        print(cnf_to_string(num_vars, clauses))
        print()
        
        # Write to file
        test_file = "/tmp/test_example.cnf"
        write_cnf_file(test_file, num_vars, clauses, 
                       comments=["Test CNF formula", "Generated by cnf_utils.py"])
        
        print(f"Written to: {test_file}")
        print()
        
        # Read it back
        num_vars_read, clauses_read = read_cnf_file(test_file)
        print(f"Read back: {num_vars_read} vars, {len(clauses_read)} clauses")
        print(f"Match: {num_vars == num_vars_read and clauses == clauses_read}")
