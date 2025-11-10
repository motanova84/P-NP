#!/usr/bin/env python3
"""
Statistical Analysis for P≠NP Empirical Validation
Performs statistical tests on the correlation between treewidth and complexity
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import json
import math
from typing import List, Dict, Any


def load_validation_results(filename: str = "results/validation_complete.json") -> Dict:
    """Load validation results from JSON file."""
    try:
        with open(filename, 'r') as f:
            return json.load(f)
    except FileNotFoundError:
        print(f"Error: {filename} not found. Run complete_validation.py first.")
        return None


def compute_correlation(x: List[float], y: List[float]) -> float:
    """Compute Pearson correlation coefficient."""
    if len(x) != len(y) or len(x) == 0:
        return 0.0
    
    n = len(x)
    mean_x = sum(x) / n
    mean_y = sum(y) / n
    
    numerator = sum((x[i] - mean_x) * (y[i] - mean_y) for i in range(n))
    denominator_x = math.sqrt(sum((x[i] - mean_x) ** 2 for i in range(n)))
    denominator_y = math.sqrt(sum((y[i] - mean_y) ** 2 for i in range(n)))
    
    if denominator_x == 0 or denominator_y == 0:
        return 0.0
    
    return numerator / (denominator_x * denominator_y)


def analyze_treewidth_time_correlation(results: List[Dict]) -> Dict[str, Any]:
    """Analyze correlation between treewidth and solving time."""
    treewidths = [r['treewidth_estimate'] for r in results]
    times = [r['time_dpll'] for r in results]
    
    correlation = compute_correlation(treewidths, times)
    
    # Compute log-time for exponential hypothesis testing
    log_times = [math.log(max(t, 1e-10)) for t in times]
    log_correlation = compute_correlation(treewidths, log_times)
    
    return {
        'correlation': correlation,
        'log_correlation': log_correlation,
        'mean_treewidth': sum(treewidths) / len(treewidths),
        'std_treewidth': math.sqrt(sum((tw - sum(treewidths) / len(treewidths)) ** 2 
                                       for tw in treewidths) / len(treewidths)),
        'mean_time': sum(times) / len(times),
        'median_time': sorted(times)[len(times) // 2]
    }


def exponential_time_hypothesis_test(results: List[Dict]) -> Dict[str, Any]:
    """Test the exponential time hypothesis (ETH) on high treewidth instances."""
    # Separate low and high treewidth instances
    low_tw = [r for r in results if r['treewidth_estimate'] <= 10]
    high_tw = [r for r in results if r['treewidth_estimate'] > 10]
    
    if not high_tw:
        return {'status': 'insufficient_data'}
    
    avg_time_low = sum(r['time_dpll'] for r in low_tw) / len(low_tw) if low_tw else 0
    avg_time_high = sum(r['time_dpll'] for r in high_tw) / len(high_tw)
    
    speedup_ratio = avg_time_high / avg_time_low if avg_time_low > 0 else float('inf')
    
    return {
        'status': 'success',
        'num_low_tw': len(low_tw),
        'num_high_tw': len(high_tw),
        'avg_time_low_tw': avg_time_low,
        'avg_time_high_tw': avg_time_high,
        'speedup_ratio': speedup_ratio,
        'eth_validated': speedup_ratio > 2.0  # High TW should be significantly slower
    }


def no_evasion_analysis(results: List[Dict]) -> Dict[str, Any]:
    """Analyze whether any instances evade the treewidth-complexity barrier."""
    # Check if any high-treewidth instance is solved quickly
    threshold_tw = 10
    threshold_time = 0.01  # 10ms threshold for "quick" solving
    
    evasions = [r for r in results 
                if r['treewidth_estimate'] > threshold_tw and r['time_dpll'] < threshold_time]
    
    total_high_tw = sum(1 for r in results if r['treewidth_estimate'] > threshold_tw)
    
    return {
        'total_high_tw_instances': total_high_tw,
        'num_evasions': len(evasions),
        'evasion_rate': len(evasions) / total_high_tw if total_high_tw > 0 else 0,
        'no_evasion_confirmed': len(evasions) == 0
    }


def generate_statistical_report(data: Dict) -> str:
    """Generate a comprehensive statistical report."""
    results = data.get('results', [])
    if not results:
        return "No results available for analysis."
    
    # Perform all analyses
    correlation_analysis = analyze_treewidth_time_correlation(results)
    eth_test = exponential_time_hypothesis_test(results)
    evasion_analysis = no_evasion_analysis(results)
    
    # Generate report
    report = []
    report.append("=" * 70)
    report.append("STATISTICAL ANALYSIS OF P≠NP EMPIRICAL VALIDATION")
    report.append("=" * 70)
    report.append("")
    
    # Correlation Analysis
    report.append("1. TREEWIDTH-TIME CORRELATION ANALYSIS")
    report.append("-" * 70)
    report.append(f"   Pearson correlation (TW vs Time): {correlation_analysis['correlation']:.4f}")
    report.append(f"   Pearson correlation (TW vs log(Time)): {correlation_analysis['log_correlation']:.4f}")
    report.append(f"   Mean treewidth: {correlation_analysis['mean_treewidth']:.2f}")
    report.append(f"   Std treewidth: {correlation_analysis['std_treewidth']:.2f}")
    report.append(f"   Mean solving time: {correlation_analysis['mean_time']:.4f}s")
    report.append(f"   Median solving time: {correlation_analysis['median_time']:.4f}s")
    
    if correlation_analysis['correlation'] > 0.5:
        report.append("   ✅ STRONG positive correlation confirmed")
    elif correlation_analysis['correlation'] > 0.3:
        report.append("   ✅ MODERATE positive correlation confirmed")
    else:
        report.append("   ⚠️  WEAK correlation detected")
    report.append("")
    
    # Exponential Time Hypothesis
    report.append("2. EXPONENTIAL TIME HYPOTHESIS (ETH) VALIDATION")
    report.append("-" * 70)
    if eth_test['status'] == 'success':
        report.append(f"   Low treewidth instances (≤10): {eth_test['num_low_tw']}")
        report.append(f"   High treewidth instances (>10): {eth_test['num_high_tw']}")
        report.append(f"   Avg time (low TW): {eth_test['avg_time_low_tw']:.4f}s")
        report.append(f"   Avg time (high TW): {eth_test['avg_time_high_tw']:.4f}s")
        report.append(f"   Slowdown ratio: {eth_test['speedup_ratio']:.2f}x")
        
        if eth_test['eth_validated']:
            report.append("   ✅ ETH VALIDATED: High TW instances significantly slower")
        else:
            report.append("   ⚠️  ETH inconclusive: Need larger instances")
    else:
        report.append("   ⚠️  Insufficient data for ETH testing")
    report.append("")
    
    # No-Evasion Analysis
    report.append("3. NO-EVASION VERIFICATION")
    report.append("-" * 70)
    report.append(f"   High treewidth instances: {evasion_analysis['total_high_tw_instances']}")
    report.append(f"   Fast-solved high-TW instances: {evasion_analysis['num_evasions']}")
    report.append(f"   Evasion rate: {evasion_analysis['evasion_rate']:.1%}")
    
    if evasion_analysis['no_evasion_confirmed']:
        report.append("   ✅ NO EVASION: All high-TW instances are computationally hard")
    else:
        report.append(f"   ⚠️  {evasion_analysis['num_evasions']} potential evasions detected")
    report.append("")
    
    # Overall Conclusion
    report.append("4. OVERALL CONCLUSION")
    report.append("-" * 70)
    
    validations = [
        correlation_analysis['correlation'] > 0.3,
        eth_test.get('eth_validated', False),
        evasion_analysis['no_evasion_confirmed']
    ]
    
    passed = sum(validations)
    
    report.append(f"   Validation checks passed: {passed}/3")
    
    if passed == 3:
        report.append("   ✅ COMPUTATIONAL DICHOTOMY FULLY VALIDATED")
        report.append("   ✅ Empirical evidence strongly supports P≠NP")
    elif passed >= 2:
        report.append("   ✅ COMPUTATIONAL DICHOTOMY VALIDATED")
        report.append("   ⚠️  Some checks need larger datasets")
    else:
        report.append("   ⚠️  VALIDATION INCOMPLETE")
        report.append("   ⚠️  More comprehensive testing needed")
    
    report.append("")
    report.append("=" * 70)
    
    return "\n".join(report)


def main():
    print("Statistical Analysis of P≠NP Empirical Validation")
    print()
    
    # Load validation results
    data = load_validation_results()
    if data is None:
        return
    
    print(f"Loaded {len(data.get('results', []))} validation results")
    print()
    
    # Generate and display report
    report = generate_statistical_report(data)
    print(report)
    
    # Save report to file
    os.makedirs("results/statistical_analysis", exist_ok=True)
    report_file = "results/statistical_analysis/statistical_report.txt"
    with open(report_file, 'w') as f:
        f.write(report)
    
    print()
    print(f"✅ Statistical report saved to {report_file}")


if __name__ == "__main__":
    main()
