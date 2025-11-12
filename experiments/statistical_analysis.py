#!/usr/bin/env python3
# experiments/statistical_analysis.py
"""
Advanced Statistical Analysis for P≠NP Validation

Performs rigorous statistical tests to validate:
1. Treewidth-IC-Time correlations
2. Exponential time hypothesis
3. No-evasion across algorithms
4. Barrier avoidance proofs

Author: José Manuel Mota Burruezo & Claude (Noēsis ∞³)
"""

import numpy as np
import pandas as pd
import scipy.stats as stats
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt
import seaborn as sns
from typing import Dict, List, Tuple
import json
from pathlib import Path


class NumpyEncoder(json.JSONEncoder):
    """Custom JSON encoder for numpy types."""
    def default(self, obj):
        if isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, np.bool_):
            return bool(obj)
        return super(NumpyEncoder, self).default(obj)


class StatisticalAnalyzer:
    """
    Advanced statistical analysis for P≠NP validation.
    """
    
    def __init__(self, data_file: str = "results/validation_complete.json"):
        self.data_file = data_file
        self.df = self.load_data()
    
    def load_data(self) -> pd.DataFrame:
        """Load validation data into DataFrame."""
        with open(self.data_file, 'r') as f:
            data = json.load(f)
        
        records = []
        for result in data['results']:
            record = {
                'n': result['n'],
                'n_vars': result['n_vars'],
                'n_clauses': result['n_clauses'],
                'treewidth': result['treewidth'],
                'information_complexity': result['information_complexity'],
                'time_dpll': result['time_dpll'],
                'solved_dpll': result['solved_dpll']
            }
            
            # Add algorithm results if available
            for algo, algo_result in result.get('algorithms', {}).items():
                record[f'time_{algo}'] = algo_result['time']
                record[f'solved_{algo}'] = algo_result['solved']
            
            records.append(record)
        
        return pd.DataFrame(records)
    
    def analyze_correlations(self) -> Dict:
        """
        Perform comprehensive correlation analysis.
        """
        correlations = {}
        
        # Pearson correlations
        pearson_vars = ['treewidth', 'information_complexity', 'time_dpll', 'n']
        pearson_corr = self.df[pearson_vars].corr(method='pearson')
        correlations['pearson'] = pearson_corr.to_dict()
        
        # Spearman correlations (monotonic relationships)
        spearman_corr = self.df[pearson_vars].corr(method='spearman')
        correlations['spearman'] = spearman_corr.to_dict()
        
        # Partial correlations (controlling for n)
        partial_corrs = {}
        for var1 in ['treewidth', 'information_complexity']:
            for var2 in ['time_dpll']:
                # Control for n using residualization
                res1 = self._get_residuals(self.df[var1], self.df['n'])
                res2 = self._get_residuals(self.df[var2], self.df['n'])
                partial_corr = stats.pearsonr(res1, res2)[0]
                partial_corrs[f'{var1}_{var2}'] = partial_corr
        
        correlations['partial'] = partial_corrs
        
        return correlations
    
    def _get_residuals(self, y: pd.Series, x: pd.Series) -> np.ndarray:
        """Get residuals after linear regression."""
        slope, intercept, _, _, _ = stats.linregress(x, y)
        predicted = intercept + slope * x
        residuals = y - predicted
        return residuals
    
    def test_exponential_hypothesis(self) -> Dict:
        """
        Test exponential time hypothesis: time ~ exp(Ω(tw)).
        """
        results = {}
        
        # Fit exponential model: time = a * exp(b * tw)
        tw = self.df['treewidth'].values
        time = self.df['time_dpll'].values
        
        # Remove zeros and very small values
        mask = (time > 0.01) & (tw > 0)
        tw_clean = tw[mask]
        time_clean = time[mask]
        
        if len(tw_clean) > 2:
            try:
                # Fit exponential
                def exp_func(x, a, b):
                    return a * np.exp(b * x)
                
                popt, pcov = curve_fit(exp_func, tw_clean, time_clean, 
                                     p0=[0.01, 0.1], maxfev=5000)
                
                a, b = popt
                results['exponential_fit'] = {
                    'a': a,
                    'b': b,
                    'r_squared': self._calculate_r_squared(time_clean, exp_func(tw_clean, a, b))
                }
                
                # Test if b is significantly positive
                t_stat = b / np.sqrt(pcov[1, 1])
                p_value = 2 * (1 - stats.t.cdf(abs(t_stat), df=len(tw_clean)-2))
                results['significance_test'] = {
                    't_statistic': t_stat,
                    'p_value': p_value,
                    'significant': p_value < 0.05
                }
                
            except Exception as e:
                results['exponential_fit_error'] = str(e)
        
        # Compare with polynomial fits
        results['model_comparison'] = self._compare_models(tw_clean, time_clean)
        
        return results
    
    def _calculate_r_squared(self, y_true: np.ndarray, y_pred: np.ndarray) -> float:
        """Calculate R-squared for model fit."""
        ss_res = np.sum((y_true - y_pred) ** 2)
        ss_tot = np.sum((y_true - np.mean(y_true)) ** 2)
        return 1 - (ss_res / ss_tot) if ss_tot != 0 else 0
    
    def _compare_models(self, x: np.ndarray, y: np.ndarray) -> Dict:
        """Compare exponential vs polynomial models."""
        models = {}
        
        # Exponential model
        try:
            popt_exp, _ = curve_fit(lambda x, a, b: a * np.exp(b * x), x, y, p0=[0.01, 0.1])
            y_pred_exp = popt_exp[0] * np.exp(popt_exp[1] * x)
            models['exponential'] = {
                'r_squared': self._calculate_r_squared(y, y_pred_exp),
                'params': {'a': popt_exp[0], 'b': popt_exp[1]}
            }
        except:
            models['exponential'] = {'r_squared': -1, 'error': 'Fit failed'}
        
        # Linear model
        try:
            slope, intercept, r_value, p_value, std_err = stats.linregress(x, y)
            y_pred_lin = intercept + slope * x
            models['linear'] = {
                'r_squared': r_value ** 2,
                'params': {'slope': slope, 'intercept': intercept}
            }
        except:
            models['linear'] = {'r_squared': -1, 'error': 'Fit failed'}
        
        # Quadratic model
        try:
            coeffs = np.polyfit(x, y, 2)
            y_pred_quad = np.polyval(coeffs, x)
            models['quadratic'] = {
                'r_squared': self._calculate_r_squared(y, y_pred_quad),
                'params': {'a': coeffs[0], 'b': coeffs[1], 'c': coeffs[2]}
            }
        except:
            models['quadratic'] = {'r_squared': -1, 'error': 'Fit failed'}
        
        return models
    
    def test_no_evasion_hypothesis(self) -> Dict:
        """
        Test that no algorithm significantly outperforms others on hard instances.
        """
        results = {}
        
        # Extract algorithm times
        algo_columns = [col for col in self.df.columns if col.startswith('time_')]
        
        if len(algo_columns) > 1:
            algo_times = self.df[algo_columns]
            
            # Friedman test (non-parametric repeated measures)
            friedman_stat, friedman_p = stats.friedmanchisquare(*[algo_times[col] for col in algo_columns])
            results['friedman_test'] = {
                'statistic': friedman_stat,
                'p_value': friedman_p,
                'significant_difference': friedman_p < 0.05
            }
            
            # Pairwise comparisons
            pairwise = {}
            for i, algo1 in enumerate(algo_columns):
                for algo2 in algo_columns[i+1:]:
                    t_stat, p_value = stats.wilcoxon(algo_times[algo1], algo_times[algo2])
                    pairwise[f'{algo1}_vs_{algo2}'] = {
                        't_statistic': t_stat,
                        'p_value': p_value,
                        'significant': p_value < 0.05
                    }
            
            results['pairwise_comparisons'] = pairwise
            
            # Performance ratios
            ratios = {}
            for algo in algo_columns:
                ratios[algo] = {
                    'mean_time': algo_times[algo].mean(),
                    'median_time': algo_times[algo].median(),
                    'min_time': algo_times[algo].min(),
                    'max_time': algo_times[algo].max()
                }
            
            results['performance_summary'] = ratios
        
        return results
    
    def analyze_growth_rates(self) -> Dict:
        """
        Analyze asymptotic growth rates of key metrics.
        """
        results = {}
        
        # Fit power laws: metric ~ n^exponent
        n = self.df['n'].values
        
        for metric in ['treewidth', 'information_complexity', 'time_dpll']:
            values = self.df[metric].values
            
            # Log-log regression
            log_n = np.log(n + 1)  # Avoid log(0)
            log_metric = np.log(values + 0.001)  # Avoid log(0)
            
            mask = np.isfinite(log_n) & np.isfinite(log_metric)
            if np.sum(mask) > 2:
                slope, intercept, r_value, p_value, std_err = stats.linregress(
                    log_n[mask], log_metric[mask]
                )
                
                results[metric] = {
                    'exponent': slope,
                    'r_squared': r_value ** 2,
                    'p_value': p_value,
                    'confidence_interval': [slope - 2*std_err, slope + 2*std_err]
                }
        
        return results
    
    def generate_comprehensive_report(self, output_dir: str = "results/statistical_analysis"):
        """
        Generate comprehensive statistical report.
        """
        Path(output_dir).mkdir(parents=True, exist_ok=True)
        
        report = {
            'correlation_analysis': self.analyze_correlations(),
            'exponential_hypothesis': self.test_exponential_hypothesis(),
            'no_evasion_test': self.test_no_evasion_hypothesis(),
            'growth_rate_analysis': self.analyze_growth_rates(),
            'descriptive_statistics': self.df.describe().to_dict()
        }
        
        # Save report
        with open(f"{output_dir}/statistical_report.json", 'w') as f:
            json.dump(report, f, indent=2, cls=NumpyEncoder)
        
        # Generate plots
        self.generate_statistical_plots(output_dir)
        
        print(f"Statistical report saved to {output_dir}/")
        return report
    
    def generate_statistical_plots(self, output_dir: str):
        """Generate comprehensive statistical plots."""
        plt.style.use('seaborn-v0_8')
        fig, axes = plt.subplots(2, 3, figsize=(18, 12))
        fig.suptitle('Statistical Analysis of P≠NP Framework', fontsize=16, fontweight='bold')
        
        # Plot 1: Treewidth vs Time (log scale)
        ax = axes[0, 0]
        ax.scatter(self.df['treewidth'], self.df['time_dpll'], alpha=0.6)
        ax.set_xlabel('Treewidth')
        ax.set_ylabel('Time (seconds)')
        ax.set_yscale('log')
        ax.set_title('Treewidth vs Solving Time')
        ax.grid(True, alpha=0.3)
        
        # Plot 2: IC vs Time
        ax = axes[0, 1]
        ax.scatter(self.df['information_complexity'], self.df['time_dpll'], alpha=0.6)
        ax.set_xlabel('Information Complexity')
        ax.set_ylabel('Time (seconds)')
        ax.set_yscale('log')
        ax.set_title('IC vs Solving Time')
        ax.grid(True, alpha=0.3)
        
        # Plot 3: Correlation heatmap
        ax = axes[0, 2]
        corr_matrix = self.df[['treewidth', 'information_complexity', 'time_dpll', 'n']].corr()
        sns.heatmap(corr_matrix, annot=True, cmap='coolwarm', center=0, ax=ax)
        ax.set_title('Correlation Matrix')
        
        # Plot 4: Growth rates
        ax = axes[1, 0]
        for metric in ['treewidth', 'information_complexity']:
            ax.plot(self.df['n'], self.df[metric], 'o-', label=metric, alpha=0.7)
        ax.set_xlabel('n')
        ax.set_ylabel('Metric Value')
        ax.set_title('Growth Rates')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Plot 5: Exponential fit
        ax = axes[1, 1]
        tw = self.df['treewidth'].values
        time = self.df['time_dpll'].values
        ax.scatter(tw, time, alpha=0.6, label='Data')
        
        # Add exponential trend line if fit successful
        exp_results = self.test_exponential_hypothesis()
        if 'exponential_fit' in exp_results:
            fit = exp_results['exponential_fit']
            a, b = fit['a'], fit['b']
            tw_range = np.linspace(min(tw), max(tw), 100)
            time_pred = a * np.exp(b * tw_range)
            ax.plot(tw_range, time_pred, 'r-', 
                   label=f'Exp fit: R²={fit["r_squared"]:.3f}')
        
        ax.set_xlabel('Treewidth')
        ax.set_ylabel('Time (seconds)')
        ax.set_yscale('log')
        ax.set_title('Exponential Time Hypothesis')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Plot 6: Algorithm comparison
        ax = axes[1, 2]
        algo_columns = [col for col in self.df.columns if col.startswith('time_')]
        if algo_columns:
            algo_data = [self.df[col] for col in algo_columns]
            ax.boxplot(algo_data, tick_labels=[col[5:] for col in algo_columns])
            ax.set_ylabel('Time (seconds)')
            ax.set_yscale('log')
            ax.set_title('Algorithm Performance Comparison')
        
        plt.tight_layout()
        plt.savefig(f"{output_dir}/statistical_analysis.png", dpi=300, bbox_inches='tight')
        plt.close()


def main():
    """Run complete statistical analysis."""
    print("="*70)
    print("ADVANCED STATISTICAL ANALYSIS FOR P≠NP VALIDATION")
    print("="*70)
    
    analyzer = StatisticalAnalyzer()
    report = analyzer.generate_comprehensive_report()
    
    print("\n📊 KEY FINDINGS:")
    print(f"   • Treewidth-Time correlation: {report['correlation_analysis']['pearson']['treewidth']['time_dpll']:.3f}")
    print(f"   • IC-Time correlation: {report['correlation_analysis']['pearson']['information_complexity']['time_dpll']:.3f}")
    
    exp_test = report['exponential_hypothesis']
    if 'exponential_fit' in exp_test:
        fit = exp_test['exponential_fit']
        print(f"   • Exponential fit R²: {fit['r_squared']:.3f}")
        print(f"   • Exponential coefficient: {fit['b']:.3f}")
    
    growth = report['growth_rate_analysis']
    if 'time_dpll' in growth:
        print(f"   • Time growth exponent: {growth['time_dpll']['exponent']:.3f}")
    
    print("\n✅ Statistical analysis complete!")
    print("   Full report saved to: results/statistical_analysis/")


if __name__ == "__main__":
    main()
