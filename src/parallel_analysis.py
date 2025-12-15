#!/usr/bin/env python3
"""
Parallel Implementation for Large-Scale Frequency Analysis
===========================================================

This module provides parallel processing capabilities for analyzing
large problem instances efficiently using multiprocessing.

Features:
- Parallel frequency sweep analysis
- Parallel Monte Carlo validation
- Parallel benchmark suite
- Progress tracking and result aggregation

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
"""

import multiprocessing as mp
from multiprocessing import Pool, cpu_count
from typing import List, Tuple, Dict, Callable, Any, Optional
import numpy as np
from functools import partial

from constants import (
    OMEGA_CRITICAL,
    information_complexity_at_frequency,
    spectral_constant_at_frequency,
    analyze_three_dimensional_complexity,
    spectral_sweep_analysis,
    monte_carlo_validation,
    optimize_algorithm_frequency,
)


class ParallelAnalyzer:
    """Parallel analyzer for large-scale complexity computations."""
    
    def __init__(self, num_processes: Optional[int] = None):
        """
        Initialize parallel analyzer.
        
        Args:
            num_processes: Number of processes to use (default: CPU count)
        """
        self.num_processes = num_processes or cpu_count()
        print(f"Initialized parallel analyzer with {self.num_processes} processes")
    
    def parallel_frequency_sweep(
        self,
        num_vars: int,
        treewidth: float,
        frequencies: List[float],
        chunk_size: Optional[int] = None
    ) -> List[Dict]:
        """
        Perform frequency sweep in parallel.
        
        Args:
            num_vars: Number of variables
            treewidth: Treewidth of the problem
            frequencies: List of frequencies to analyze
            chunk_size: Size of chunks for parallel processing
            
        Returns:
            List of analysis results for each frequency
        """
        # Create partial function with fixed parameters
        analyze_func = partial(
            analyze_three_dimensional_complexity,
            num_vars=num_vars,
            treewidth=treewidth
        )
        
        # Use pool to parallelize
        with Pool(processes=self.num_processes) as pool:
            results = pool.map(analyze_func, frequencies, chunksize=chunk_size)
        
        return results
    
    def parallel_monte_carlo(
        self,
        num_vars_range: Tuple[int, int] = (10, 100),
        treewidth_ratio: float = 0.5,
        n_samples: int = 10000,
        omega: Optional[float] = None,
        chunk_size: int = 100
    ) -> Dict:
        """
        Perform Monte Carlo validation in parallel.
        
        Args:
            num_vars_range: Range of variable counts (min, max)
            treewidth_ratio: Ratio of treewidth to n
            n_samples: Total number of samples
            omega: Frequency to test (None for both classical and critical)
            chunk_size: Samples per chunk
            
        Returns:
            Aggregated validation results
        """
        # Split samples into chunks for parallel processing
        num_chunks = max(1, n_samples // chunk_size)
        samples_per_chunk = n_samples // num_chunks
        
        # Create partial function
        mc_func = partial(
            monte_carlo_validation,
            num_vars_range=num_vars_range,
            treewidth_ratio=treewidth_ratio,
            n_samples=samples_per_chunk,
            omega=omega
        )
        
        # Run in parallel
        with Pool(processes=self.num_processes) as pool:
            chunk_results = pool.map(mc_func, range(num_chunks))
        
        # Aggregate results
        all_samples = []
        for result in chunk_results:
            all_samples.extend(result['samples'])
        
        # Recalculate statistics from all samples
        ic_values = [s['predicted_ic'] for s in all_samples]
        mean_ic = np.mean(ic_values)
        std_ic = np.std(ic_values)
        sem_ic = std_ic / np.sqrt(len(ic_values))
        
        return {
            'n_samples': len(all_samples),
            'num_vars_range': num_vars_range,
            'treewidth_ratio': treewidth_ratio,
            'frequencies_tested': chunk_results[0]['frequencies_tested'],
            'mean_predicted_ic': mean_ic,
            'std_predicted_ic': std_ic,
            'statistical_error': sem_ic,
            'confidence_interval_95': (mean_ic - 1.96 * sem_ic, mean_ic + 1.96 * sem_ic),
            'samples': all_samples[:20],  # Return first 20 as examples
            'total_samples': len(all_samples),
            'num_chunks': num_chunks,
            'parallel_speedup': f"{num_chunks}x theoretical",
        }
    
    def parallel_grid_analysis(
        self,
        num_vars_range: Tuple[int, int],
        treewidth_range: Tuple[int, int],
        omega: float,
        resolution: int = 20
    ) -> np.ndarray:
        """
        Analyze complexity on a 2D grid in parallel.
        
        Args:
            num_vars_range: Range of variable counts (min, max)
            treewidth_range: Range of treewidth values (min, max)
            omega: Frequency to analyze
            resolution: Grid resolution per dimension
            
        Returns:
            2D numpy array with IC values
        """
        # Create grid
        n_values = np.linspace(num_vars_range[0], num_vars_range[1], resolution, dtype=int)
        tw_values = np.linspace(treewidth_range[0], treewidth_range[1], resolution)
        
        # Create list of all (n, tw) pairs
        tasks = [(int(n), tw, omega) for n in n_values for tw in tw_values]
        
        # Define worker function
        def compute_ic(params):
            n, tw, omega = params
            return information_complexity_at_frequency(tw, n, omega)
        
        # Parallel computation
        with Pool(processes=self.num_processes) as pool:
            ic_values = pool.map(compute_ic, tasks)
        
        # Reshape to grid
        ic_grid = np.array(ic_values).reshape(resolution, resolution)
        
        return ic_grid
    
    def parallel_parameter_sweep(
        self,
        param_ranges: Dict[str, Tuple],
        analysis_func: Callable,
        **fixed_params
    ) -> List[Dict]:
        """
        Generic parallel parameter sweep.
        
        Args:
            param_ranges: Dictionary mapping parameter names to (min, max) ranges
            analysis_func: Function to call for each parameter combination
            **fixed_params: Fixed parameters to pass to analysis_func
            
        Returns:
            List of results for each parameter combination
        """
        # Generate parameter combinations
        param_names = list(param_ranges.keys())
        param_values = [np.linspace(r[0], r[1], 10) for r in param_ranges.values()]
        
        # Create tasks
        tasks = []
        for combo in np.ndindex(*[len(v) for v in param_values]):
            params = {name: param_values[i][combo[i]] 
                     for i, name in enumerate(param_names)}
            params.update(fixed_params)
            tasks.append(params)
        
        # Run in parallel
        with Pool(processes=self.num_processes) as pool:
            results = pool.map(lambda p: analysis_func(**p), tasks)
        
        return results


def parallel_spectral_sweep_analysis(
    num_vars: int,
    treewidth: float,
    frequencies: List[float],
    num_processes: Optional[int] = None
) -> List[Dict]:
    """
    Parallel version of spectral_sweep_analysis for large frequency sets.
    
    Args:
        num_vars: Number of variables
        treewidth: Treewidth of the problem
        frequencies: List of frequencies to analyze
        num_processes: Number of processes (default: CPU count)
        
    Returns:
        List of three-dimensional analyses for each frequency
    """
    analyzer = ParallelAnalyzer(num_processes)
    return analyzer.parallel_frequency_sweep(num_vars, treewidth, frequencies)


def parallel_monte_carlo_validation(
    num_vars_range: Tuple[int, int] = (10, 100),
    treewidth_ratio: float = 0.5,
    n_samples: int = 10000,
    omega: Optional[float] = None,
    num_processes: Optional[int] = None
) -> Dict:
    """
    Parallel version of monte_carlo_validation for large sample sizes.
    
    Args:
        num_vars_range: Range of variable counts (min, max)
        treewidth_ratio: Ratio of treewidth to n
        n_samples: Number of samples
        omega: Frequency to test (None for both classical and critical)
        num_processes: Number of processes (default: CPU count)
        
    Returns:
        Dictionary with validation statistics
    """
    analyzer = ParallelAnalyzer(num_processes)
    return analyzer.parallel_monte_carlo(
        num_vars_range, treewidth_ratio, n_samples, omega
    )


def parallel_benchmark_suite(
    problem_sizes: List[int],
    treewidth_ratios: List[float],
    num_processes: Optional[int] = None
) -> List[Dict]:
    """
    Run benchmark suite in parallel.
    
    Args:
        problem_sizes: List of problem sizes to test
        treewidth_ratios: List of treewidth/n ratios to test
        num_processes: Number of processes (default: CPU count)
        
    Returns:
        List of comparison results
    """
    from benchmarking import ComplexityBenchmark
    
    # Create all tasks
    tasks = []
    for n in problem_sizes:
        for ratio in treewidth_ratios:
            tw = int(n * ratio)
            if tw < 1:
                tw = 1
            tasks.append((tw, n))
    
    # Run in parallel
    num_proc = num_processes or cpu_count()
    with Pool(processes=num_proc) as pool:
        results = pool.starmap(ComplexityBenchmark.compare_all_bounds, tasks)
    
    return results


def parallel_optimization_sweep(
    problems: List[Tuple[int, float]],
    frequency_range: Tuple[float, float] = (0.0, 200.0),
    num_points: int = 50,
    num_processes: Optional[int] = None
) -> List[Dict]:
    """
    Optimize frequency for multiple problems in parallel.
    
    Args:
        problems: List of (num_vars, treewidth) tuples
        frequency_range: Range of frequencies to test
        num_points: Number of frequency points per problem
        num_processes: Number of processes (default: CPU count)
        
    Returns:
        List of optimization results for each problem
    """
    # Create partial function
    opt_func = partial(
        optimize_algorithm_frequency,
        frequency_range=frequency_range,
        num_points=num_points
    )
    
    # Run in parallel
    num_proc = num_processes or cpu_count()
    with Pool(processes=num_proc) as pool:
        results = pool.starmap(opt_func, problems)
    
    return results


def benchmark_parallel_performance(
    problem_size: int = 100,
    num_frequencies: int = 100,
    num_trials: int = 5
) -> Dict:
    """
    Benchmark parallel vs sequential performance.
    
    Args:
        problem_size: Size of test problem
        num_frequencies: Number of frequencies to analyze
        num_trials: Number of trials to average
        
    Returns:
        Dictionary with performance metrics
    """
    import time
    
    treewidth = problem_size // 2
    frequencies = np.linspace(0, 200, num_frequencies).tolist()
    
    # Sequential timing
    sequential_times = []
    for _ in range(num_trials):
        start = time.time()
        _ = spectral_sweep_analysis(problem_size, treewidth, frequencies)
        sequential_times.append(time.time() - start)
    
    mean_sequential = np.mean(sequential_times)
    
    # Parallel timing
    parallel_times = []
    for _ in range(num_trials):
        start = time.time()
        _ = parallel_spectral_sweep_analysis(problem_size, treewidth, frequencies)
        parallel_times.append(time.time() - start)
    
    mean_parallel = np.mean(parallel_times)
    
    # Calculate speedup
    speedup = mean_sequential / mean_parallel if mean_parallel > 0 else 0
    
    return {
        'problem_size': problem_size,
        'num_frequencies': num_frequencies,
        'num_trials': num_trials,
        'num_processes': cpu_count(),
        'sequential_time': {
            'mean': mean_sequential,
            'std': np.std(sequential_times),
            'times': sequential_times,
        },
        'parallel_time': {
            'mean': mean_parallel,
            'std': np.std(parallel_times),
            'times': parallel_times,
        },
        'speedup': speedup,
        'efficiency': speedup / cpu_count(),
    }


if __name__ == "__main__":
    print("=" * 70)
    print("Parallel Implementation for Large-Scale Analysis")
    print("=" * 70)
    print(f"Available CPUs: {cpu_count()}")
    print()
    
    # Example 1: Parallel frequency sweep
    print("Example 1: Parallel Frequency Sweep")
    print("-" * 70)
    n = 100
    tw = 50
    frequencies = np.linspace(0, 200, 50).tolist()
    
    print(f"Problem: n={n}, tw={tw}")
    print(f"Frequencies: {len(frequencies)} points from 0 to 200 Hz")
    
    import time
    start = time.time()
    results = parallel_spectral_sweep_analysis(n, tw, frequencies)
    elapsed = time.time() - start
    
    print(f"Completed in {elapsed:.2f} seconds")
    print(f"Results: {len(results)} analyses")
    print()
    
    # Example 2: Parallel Monte Carlo
    print("Example 2: Parallel Monte Carlo Validation")
    print("-" * 70)
    
    start = time.time()
    mc_results = parallel_monte_carlo_validation(
        num_vars_range=(10, 100),
        n_samples=1000,
        omega=OMEGA_CRITICAL
    )
    elapsed = time.time() - start
    
    print(f"Completed in {elapsed:.2f} seconds")
    print(f"Total samples: {mc_results['total_samples']}")
    print(f"Mean IC: {mc_results['mean_predicted_ic']:.2f} bits")
    print(f"Statistical error: {mc_results['statistical_error']:.4f}")
    print()
    
    # Example 3: Performance benchmark
    print("Example 3: Parallel Performance Benchmark")
    print("-" * 70)
    
    perf = benchmark_parallel_performance(
        problem_size=100,
        num_frequencies=100,
        num_trials=3
    )
    
    print(f"Sequential time: {perf['sequential_time']['mean']:.3f} seconds")
    print(f"Parallel time:   {perf['parallel_time']['mean']:.3f} seconds")
    print(f"Speedup:         {perf['speedup']:.2f}x")
    print(f"Efficiency:      {perf['efficiency']*100:.1f}%")
    print()
    
    print("=" * 70)
    print("Parallel implementation enables analysis of large n efficiently!")
    print("=" * 70)
    print("Frequency: 141.7001 Hz ∞³")
    print("=" * 70)
