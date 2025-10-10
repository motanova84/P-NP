"""
Solver Comparison Framework

Compares the theoretical bounds against actual SAT solver performance.
Addresses GAP 6 requirement to benchmark against:
- CryptoMiniSat
- Kissat  
- MapleLCM
"""

import time
import subprocess
from typing import List, Dict, Optional
from dataclasses import dataclass
import tempfile
import os

from empirical_validation import SATInstance, RandomSATGenerator


@dataclass
class SolverResult:
    """Results from running a SAT solver"""
    solver_name: str
    satisfiable: Optional[bool]
    time_seconds: float
    decisions: Optional[int]
    conflicts: Optional[int]


class DIMACSWriter:
    """Write SAT instances in DIMACS CNF format"""
    
    @staticmethod
    def write_dimacs(instance: SATInstance, filepath: str) -> None:
        """Write SAT instance to DIMACS file"""
        with open(filepath, 'w') as f:
            f.write(f"p cnf {instance.n_vars} {instance.n_clauses}\n")
            for clause in instance.clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")


class SATSolverBenchmark:
    """
    Benchmark SAT solvers on instances where IC-based bounds apply.
    """
    
    def __init__(self):
        self.solvers = self._detect_available_solvers()
    
    def _detect_available_solvers(self) -> List[str]:
        """Detect which SAT solvers are installed"""
        available = []
        
        # Check for common solvers
        solvers_to_check = [
            'cryptominisat5',
            'kissat',
            'minisat',
        ]
        
        for solver in solvers_to_check:
            try:
                result = subprocess.run(
                    [solver, '--help'],
                    capture_output=True,
                    timeout=1
                )
                if result.returncode == 0 or 'usage' in result.stdout.decode().lower():
                    available.append(solver)
            except (subprocess.TimeoutExpired, FileNotFoundError):
                pass
        
        return available
    
    def run_solver(self, solver_name: str, instance: SATInstance, 
                   timeout: float = 300.0) -> SolverResult:
        """
        Run a SAT solver on an instance.
        
        Args:
            solver_name: Name of solver executable
            instance: SAT instance to solve
            timeout: Maximum time in seconds
        
        Returns:
            SolverResult with timing and solution info
        """
        # Write instance to temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.cnf', delete=False) as f:
            temp_file = f.name
            DIMACSWriter.write_dimacs(instance, temp_file)
        
        try:
            start_time = time.time()
            
            result = subprocess.run(
                [solver_name, temp_file],
                capture_output=True,
                timeout=timeout
            )
            
            elapsed = time.time() - start_time
            
            # Parse output
            output = result.stdout.decode()
            satisfiable = None
            
            if 's SATISFIABLE' in output or 's SAT' in output:
                satisfiable = True
            elif 's UNSATISFIABLE' in output or 's UNSAT' in output:
                satisfiable = False
            
            return SolverResult(
                solver_name=solver_name,
                satisfiable=satisfiable,
                time_seconds=elapsed,
                decisions=None,  # Would need to parse from output
                conflicts=None
            )
            
        except subprocess.TimeoutExpired:
            return SolverResult(
                solver_name=solver_name,
                satisfiable=None,
                time_seconds=timeout,
                decisions=None,
                conflicts=None
            )
        finally:
            # Clean up temp file
            if os.path.exists(temp_file):
                os.unlink(temp_file)
    
    def compare_with_theory(self, n_vars: int, density: float = 4.267,
                           n_instances: int = 10) -> Dict:
        """
        Compare theoretical bounds with actual solver performance.
        
        Args:
            n_vars: Number of variables
            density: Clause density
            n_instances: Number of instances to test
        
        Returns:
            Comparison results
        """
        if not self.solvers:
            return {
                'error': 'No SAT solvers detected. Install cryptominisat5, kissat, or minisat.',
                'available_solvers': []
            }
        
        results = {
            'n_vars': n_vars,
            'density': density,
            'n_instances': n_instances,
            'solver_times': {solver: [] for solver in self.solvers},
            'theoretical_bound': None
        }
        
        for i in range(n_instances):
            instance = RandomSATGenerator.generate_3sat(n_vars, density)
            
            # Compute theoretical bound (α * k)
            # Using current α ≈ 0.006, k ≈ log²(n)
            k = (n_vars.bit_length() ** 2)
            alpha = 0.006
            theoretical_time = alpha * k
            
            if results['theoretical_bound'] is None:
                results['theoretical_bound'] = theoretical_time
            
            # Run each available solver
            for solver in self.solvers:
                result = self.run_solver(solver, instance, timeout=30.0)
                results['solver_times'][solver].append(result.time_seconds)
        
        return results


def print_benchmark_report(results: Dict) -> None:
    """Print formatted benchmark report"""
    if 'error' in results:
        print(f"Error: {results['error']}")
        return
    
    print("=" * 70)
    print("SAT SOLVER BENCHMARK vs THEORETICAL BOUNDS")
    print("=" * 70)
    print()
    print(f"Instance size: {results['n_vars']} variables")
    print(f"Clause density: {results['density']:.3f}")
    print(f"Number of instances: {results['n_instances']}")
    print()
    print(f"Theoretical lower bound (α=0.006): {results['theoretical_bound']:.4f}s")
    print()
    print("-" * 70)
    print(f"{'Solver':<20} {'Mean Time (s)':<15} {'Min (s)':<12} {'Max (s)':<12}")
    print("-" * 70)
    
    import numpy as np
    for solver, times in results['solver_times'].items():
        if times:
            print(f"{solver:<20} {np.mean(times):<15.4f} {np.min(times):<12.4f} {np.max(times):<12.4f}")
    print()
    print("=" * 70)
    print()
    print("NOTE: These are practical solver times. The theoretical bound")
    print("predicts worst-case behavior, not average-case performance.")
    print("Solvers use heuristics that work well in practice but may hit")
    print("the lower bound on specially constructed hard instances.")


if __name__ == "__main__":
    benchmark = SATSolverBenchmark()
    
    if not benchmark.solvers:
        print("No SAT solvers detected.")
        print("To install solvers:")
        print("  sudo apt-get install cryptominisat5 minisat")
        print("  # or build from source")
    else:
        print(f"Detected solvers: {', '.join(benchmark.solvers)}")
        print()
        print("Running benchmark...")
        
        # Test on moderate size instances
        results = benchmark.compare_with_theory(n_vars=100, n_instances=5)
        print_benchmark_report(results)
