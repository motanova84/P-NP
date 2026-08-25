#!/usr/bin/env python3
"""
cicy_analysis.py - Complete CICY Data Analysis and κ_Π Discovery

Implements comprehensive analysis of Complete Intersection Calabi-Yau (CICY) 
varieties from Oxford database to discover emergent κ_Π constant in computational
complexity relationships.

This script performs:
- PASO 1: Download and analyze real CICY data from Oxford
- PASO 2: Exploratory data analysis with visualizations
- PASO 3: Define complexity proxy metrics
- PASO 4: Statistical modeling and hypothesis testing
- PASO 5: Search for κ_Π emergent constant
- PASO 6: Validate hypotheses

© JMMB | P vs NP Verification System
"""

import sys
import io
import numpy as np
import pandas as pd
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt
from scipy import stats
from sklearn.linear_model import LinearRegression
from sklearn.model_selection import cross_val_score
from sklearn.preprocessing import StandardScaler
from typing import Dict, Tuple, Optional
import requests


class CICYAnalyzer:
    """
    Complete Intersection Calabi-Yau (CICY) data analyzer.
    
    Downloads real CICY data from Oxford database and performs comprehensive
    statistical analysis to discover emergent patterns related to κ_Π.
    """
    
    def __init__(self, url: str = "http://www-thphys.physics.ox.ac.uk/projects/CalabiYau/cicylist/cicylist.txt"):
        """
        Initialize CICY analyzer.
        
        Args:
            url: URL to CICY database (default: Oxford database)
        """
        self.url = url
        self.cicy_data: Optional[pd.DataFrame] = None
        self.kappa_pi = 2.5773  # Target constant
        
    def download_and_parse_data(self, timeout: int = 10) -> pd.DataFrame:
        """
        PASO 1: Download and parse CICY data from Oxford database.
        
        Args:
            timeout: Request timeout in seconds
            
        Returns:
            DataFrame with CICY data (index, h11, h21, chi, N)
        """
        print("🔍 Descargando datos CICY de Oxford...")
        print(f"   URL: {self.url}")
        
        try:
            response = requests.get(self.url, timeout=timeout)
            
            if response.status_code == 200:
                # Parse data - format has comments with #
                lines = response.text.split('\n')
                data_lines = []
                
                for line in lines:
                    stripped = line.strip()
                    if stripped and not stripped.startswith('#'):
                        data_lines.append(line)
                
                # Create DataFrame
                self.cicy_data = pd.read_csv(
                    io.StringIO('\n'.join(data_lines)),
                    delim_whitespace=True,
                    header=None,
                    names=['index', 'h11', 'h21', 'chi']
                )
                
                # Calculate N = h11 + h21
                self.cicy_data['N'] = self.cicy_data['h11'] + self.cicy_data['h21']
                
                print("✅ DATOS DESCARGADOS CORRECTAMENTE")
                self._print_basic_stats()
                
                return self.cicy_data
                
            else:
                print(f"❌ Error HTTP: {response.status_code}")
                return self._create_backup_data()
                
        except Exception as e:
            print(f"❌ Error: {e}")
            print("⚠️  Usando datos de respaldo locales...")
            return self._create_backup_data()
    
    def _create_backup_data(self) -> pd.DataFrame:
        """Create backup synthetic data based on literature."""
        np.random.seed(42)
        n_samples = 100
        
        self.cicy_data = pd.DataFrame({
            'index': range(n_samples),
            'h11': np.random.randint(1, 20, n_samples),
            'h21': np.random.randint(1, 150, n_samples)
        })
        self.cicy_data['chi'] = 2 * (self.cicy_data['h11'] - self.cicy_data['h21'])
        self.cicy_data['N'] = self.cicy_data['h11'] + self.cicy_data['h21']
        
        print("✅ Datos de respaldo creados")
        return self.cicy_data
    
    def _print_basic_stats(self):
        """Print basic statistics about the data."""
        if self.cicy_data is None:
            return
            
        total_cy = len(self.cicy_data)
        count_n13 = (self.cicy_data['N'] == 13).sum()
        
        print(f"📊 Total de variedades CICY: {total_cy}")
        print(f"📈 Estadísticas de N = h¹¹ + h²¹:")
        print(f"   Mínimo: {int(self.cicy_data['N'].min())}")
        print(f"   Máximo: {int(self.cicy_data['N'].max())}")
        print(f"   Media: {self.cicy_data['N'].mean():.1f}")
        print(f"   Mediana: {self.cicy_data['N'].median():.1f}")
        print(f"   Desviación estándar: {self.cicy_data['N'].std():.1f}")
        print(f"🔢 CY con N = 13: {count_n13} ({count_n13/total_cy*100:.2f}%)")
    
    def save_data(self, filename: str = 'cicy_data_analysis.csv'):
        """Save processed data to CSV."""
        if self.cicy_data is not None:
            self.cicy_data.to_csv(filename, index=False)
            print(f"💾 Datos guardados en '{filename}'")
    
    def estimate_complexity(self, row: pd.Series) -> float:
        """
        PASO 3: Estimate computational complexity proxy.
        
        Complexity based on:
        1. N large → more moduli → more complex
        2. Ratio h11/h21 away from 1 → asymmetric structure
        3. Chi extreme → unbalanced topology
        
        Args:
            row: DataFrame row with h11, h21, chi, N
            
        Returns:
            Estimated complexity
        """
        N = row['N']
        ratio = row['h11'] / max(row['h21'], 1)  # Avoid division by 0
        chi_abs = abs(row['chi'])
        
        # Heuristic model (to be calibrated with real data)
        complexity = np.log(N) * (1 + abs(np.log(ratio))) + 0.1 * np.log(chi_abs + 1)
        return complexity
    
    def add_complexity_metrics(self):
        """Add complexity proxy metrics to data."""
        if self.cicy_data is None:
            raise ValueError("Data not loaded. Call download_and_parse_data() first.")
        
        # Proxy 1: Complexity estimation
        self.cicy_data['complexity_estimated'] = self.cicy_data.apply(
            self.estimate_complexity, axis=1
        )
        
        # Proxy 2: System size (theoretical)
        self.cicy_data['system_size'] = self.cicy_data['N'] * 10  # Heuristic factor
        
        # Add log(N) for modeling
        self.cicy_data['log_N'] = np.log(self.cicy_data['N'])
    
    def exploratory_analysis(self, save_fig: bool = True, 
                            filename: str = 'cicy_exploratory_analysis.png') -> plt.Figure:
        """
        PASO 2: Exploratory data analysis with visualizations.
        
        Args:
            save_fig: Whether to save figure to file
            filename: Output filename for figure
            
        Returns:
            Matplotlib figure
        """
        if self.cicy_data is None:
            raise ValueError("Data not loaded. Call download_and_parse_data() first.")
        
        fig, axes = plt.subplots(1, 3, figsize=(15, 4))
        
        # 1. Histogram of N
        axes[0].hist(self.cicy_data['N'], bins=30, alpha=0.7, 
                    color='steelblue', edgecolor='black')
        axes[0].axvline(13, color='red', linestyle='--', 
                       linewidth=2, label='N=13')
        axes[0].set_xlabel('N = h¹¹ + h²¹', fontsize=11)
        axes[0].set_ylabel('Frecuencia', fontsize=11)
        axes[0].set_title('Distribución de N en variedades CICY', fontsize=12, fontweight='bold')
        axes[0].legend()
        axes[0].grid(True, alpha=0.3)
        
        # 2. Scatter h11 vs h21
        axes[1].scatter(self.cicy_data['h11'], self.cicy_data['h21'], 
                       alpha=0.5, s=20, color='teal')
        axes[1].set_xlabel('h¹¹', fontsize=11)
        axes[1].set_ylabel('h²¹', fontsize=11)
        axes[1].set_title('Relación h¹¹ vs h²¹', fontsize=12, fontweight='bold')
        axes[1].grid(True, alpha=0.3)
        
        # 3. Boxplot by quartiles
        try:
            n_bins = pd.qcut(self.cicy_data['N'], q=4, duplicates='drop')
            box_data = []
            labels = []
            
            for bin_val in sorted(n_bins.unique()):
                mask = (n_bins == bin_val)
                box_data.append(self.cicy_data.loc[mask, 'N'].values)
                # Format label
                left, right = bin_val.left, bin_val.right
                labels.append(f'[{left:.0f}, {right:.0f}]')
            
            axes[2].boxplot(box_data, tick_labels=labels)
            axes[2].set_xticklabels(labels, rotation=45, ha='right')
            axes[2].set_ylabel('N', fontsize=11)
            axes[2].set_title('Distribución de N por cuartiles', fontsize=12, fontweight='bold')
            axes[2].grid(True, alpha=0.3)
        except Exception as e:
            print(f"⚠️  No se pudo crear boxplot: {e}")
            axes[2].text(0.5, 0.5, 'Boxplot no disponible', 
                        ha='center', va='center', transform=axes[2].transAxes)
        
        plt.tight_layout()
        
        if save_fig:
            plt.savefig(filename, dpi=150, bbox_inches='tight')
            print(f"📊 Gráfica guardada en '{filename}'")
        
        return fig
    
    def statistical_modeling(self) -> Dict[str, Tuple[float, float]]:
        """
        PASO 4: Statistical modeling and hypothesis testing.
        
        Tests multiple models:
        1. Linear: complexity ~ N
        2. Logarithmic: complexity ~ log(N)
        3. Full: complexity ~ N + log(N) + h11 + h21
        
        Returns:
            Dictionary with model results (name -> (mean_r2, std_r2))
        """
        if self.cicy_data is None or 'complexity_estimated' not in self.cicy_data.columns:
            raise ValueError("Complexity metrics not computed. Call add_complexity_metrics() first.")
        
        print("\n📊 ANÁLISIS ESTADÍSTICO")
        print("=" * 60)
        
        # Prepare data
        X = self.cicy_data[['N', 'log_N', 'h11', 'h21']].copy()
        y = self.cicy_data['complexity_estimated']
        
        # Standardize
        scaler = StandardScaler()
        X_scaled = scaler.fit_transform(X)
        
        results = {}
        
        # Model 1: Linear N
        model1 = LinearRegression()
        scores1 = cross_val_score(model1, X_scaled[:, [0]], y, cv=5, scoring='r2')
        results['Linear_N'] = (scores1.mean(), scores1.std())
        
        # Model 2: Logarithmic log(N)
        model2 = LinearRegression()
        scores2 = cross_val_score(model2, X_scaled[:, [1]], y, cv=5, scoring='r2')
        results['Log_N'] = (scores2.mean(), scores2.std())
        
        # Model 3: Full model
        model3 = LinearRegression()
        scores3 = cross_val_score(model3, X_scaled, y, cv=5, scoring='r2')
        results['Full_model'] = (scores3.mean(), scores3.std())
        
        # Print results
        print("📈 RESULTADOS DE MODELADO:")
        print("-" * 60)
        for name, (mean_r2, std_r2) in results.items():
            print(f"{name:15} R² = {mean_r2:.4f} ± {std_r2:.4f}")
        
        # Fit full model for coefficient analysis
        model_full = LinearRegression()
        model_full.fit(X_scaled, y)
        
        print("\n🔍 COEFICIENTES DEL MODELO COMPLETO (estandarizados):")
        coeff_names = ['N', 'log_N', 'h11', 'h21']
        for name, coeff in zip(coeff_names, model_full.coef_):
            print(f"  {name:10}: {coeff:.6f}")
        
        print(f"\n🎯 Intercepto (complejidad base): {model_full.intercept_:.6f}")
        print(f"   ¿Cerca de κ_Π = 2.5773?")
        print(f"   Diferencia: {abs(model_full.intercept_ - self.kappa_pi):.6f}")
        
        # Store model for later use
        self.full_model = model_full
        self.scaler = scaler
        
        return results
    
    def search_kappa_pi_emergence(self) -> Dict:
        """
        PASO 5: Search for κ_Π emergent constant in model parameters.
        
        Returns:
            Dictionary with emergence analysis results
        """
        if not hasattr(self, 'full_model'):
            raise ValueError("Model not fitted. Call statistical_modeling() first.")
        
        print("\n" + "=" * 60)
        print("🔬 BÚSQUEDA DE κ_Π EMERGENTE")
        print("=" * 60)
        
        results = {
            'intercept': self.full_model.intercept_,
            'kappa_pi_target': self.kappa_pi,
            'difference': abs(self.full_model.intercept_ - self.kappa_pi),
            'coefficients': dict(zip(['N', 'log_N', 'h11', 'h21'], 
                                    self.full_model.coef_))
        }
        
        # Check if any coefficient is close to κ_Π
        print("\n🔍 Análisis de emergencia:")
        print(f"   Intercepto: {results['intercept']:.6f}")
        print(f"   Objetivo κ_Π: {self.kappa_pi}")
        print(f"   Diferencia: {results['difference']:.6f}")
        
        # Check coefficients
        print("\n📊 Coeficientes cerca de κ_Π:")
        for name, coeff in results['coefficients'].items():
            diff = abs(coeff - self.kappa_pi)
            if diff < 1.0:
                print(f"   {name}: {coeff:.6f} (diff: {diff:.6f}) ✓")
            else:
                print(f"   {name}: {coeff:.6f} (diff: {diff:.6f})")
        
        return results
    
    def print_hypotheses(self):
        """
        PASO 6: Print hypotheses to be tested.
        """
        print("\n" + "=" * 60)
        print("📝 HIPÓTESIS A TESTEAR")
        print("=" * 60)
        
        hypotheses = [
            ("H1", "Existe correlación positiva entre N = h¹¹+h²¹ y complejidad computacional"),
            ("H2", "La relación es logarítmica: complejidad ~ log(N)"),
            ("H3", "h¹¹ y h²¹ contribuyen diferentemente a la complejidad"),
            ("H4", "El intercepto del modelo tiene significado físico relacionado con κ_Π")
        ]
        
        for code, hypothesis in hypotheses:
            print(f"\n{code}: {hypothesis}")
    
    def run_complete_analysis(self, save_outputs: bool = True) -> Dict:
        """
        Run complete CICY analysis pipeline (PASO 1-6).
        
        Args:
            save_outputs: Whether to save outputs (CSV, figures)
            
        Returns:
            Dictionary with all analysis results
        """
        print("=" * 60)
        print("🌟 ANÁLISIS COMPLETO DE DATOS CICY")
        print("=" * 60)
        
        # PASO 1: Download and parse
        self.download_and_parse_data()
        
        if save_outputs:
            self.save_data()
        
        # PASO 2: Exploratory analysis
        print("\n📊 PASO 2: ANÁLISIS EXPLORATORIO")
        self.exploratory_analysis(save_fig=save_outputs)
        
        # PASO 3: Add complexity metrics
        print("\n🔬 PASO 3: MÉTRICAS DE COMPLEJIDAD")
        self.add_complexity_metrics()
        print("✅ Métricas de complejidad calculadas")
        
        # PASO 4: Statistical modeling
        print("\n📈 PASO 4: MODELADO ESTADÍSTICO")
        model_results = self.statistical_modeling()
        
        # PASO 5: Search for κ_Π
        print("\n🎯 PASO 5: BÚSQUEDA DE κ_Π")
        emergence_results = self.search_kappa_pi_emergence()
        
        # PASO 6: Hypotheses
        print("\n📝 PASO 6: HIPÓTESIS")
        self.print_hypotheses()
        
        print("\n" + "=" * 60)
        print("✅ ANÁLISIS COMPLETO FINALIZADO")
        print("=" * 60)
        
        return {
            'data': self.cicy_data,
            'model_results': model_results,
            'emergence_results': emergence_results
        }


def main():
    """Main entry point for CICY analysis."""
    analyzer = CICYAnalyzer()
    results = analyzer.run_complete_analysis(save_outputs=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
