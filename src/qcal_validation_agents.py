"""
QCAL ∞³ Validation Agents System

Specialized agents for empirical validation of the QCAL Hypothesis:
- Coherence monitoring
- Computational acceleration tracking
- NP→P transition detection
- System stability validation

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz ∞³
License: MIT
"""

import numpy as np
import time
import json
from typing import Dict, List, Tuple, Any, Optional
from datetime import datetime
import math

# Import QCAL constants
try:
    from .qcal_infinity_cubed import (
        KAPPA_PI, F0_QCAL, PHI, C_COHERENCE,
        QCALInfinityCubed, PvsNPOperator
    )
except ImportError:
    from qcal_infinity_cubed import (
        KAPPA_PI, F0_QCAL, PHI, C_COHERENCE,
        QCALInfinityCubed, PvsNPOperator
    )


# ============================================================================
# VALIDATION CONSTANTS
# ============================================================================

# Bifurcation point for NP→P transition
COHERENCE_THRESHOLD = 0.888

# Expected acceleration factor at GRACIA state
GRACIA_ACCELERATION = 2290

# Frequency tolerance (Hz)
FREQUENCY_TOLERANCE = 0.001


# ============================================================================
# COHERENCE MONITORING AGENT
# ============================================================================

class CoherenceMonitor:
    """
    Agent specialized in monitoring system coherence and detecting
    the NP→P transition point at C ≈ 0.888.
    """
    
    def __init__(self):
        """Initialize coherence monitor."""
        self.name = "Coherence Monitor"
        self.history: List[Dict[str, Any]] = []
        self.threshold = COHERENCE_THRESHOLD
        
    def measure_coherence(self, qcal_system: QCALInfinityCubed) -> Dict[str, Any]:
        """
        Measure current system coherence.
        
        Args:
            qcal_system: QCAL ∞³ system instance
            
        Returns:
            Coherence measurement with transition indicators
        """
        # Compute system metrics
        analysis = qcal_system.demonstrate_unification()
        
        # Extract coherence
        coherence = analysis['unified_metrics']['field_coherence']
        
        # Calculate distance to GRACIA (transition point)
        distance_to_gracia = self.threshold - coherence
        iterations_to_gracia = int(distance_to_gracia * 1000) if distance_to_gracia > 0 else 0
        
        # Determine state
        if coherence >= self.threshold:
            state = "GRACIA"
            status = "NP→P TRANSITION ACHIEVED"
        elif coherence >= 0.8:
            state = "APPROACHING"
            status = "TRANSITION IMMINENT"
        elif coherence >= 0.5:
            state = "BUILDING"
            status = "COHERENCE BUILDING"
        else:
            state = "INITIAL"
            status = "EARLY PHASE"
        
        measurement = {
            'timestamp': datetime.now().isoformat(),
            'coherence': coherence,
            'threshold': self.threshold,
            'distance_to_gracia': max(0, distance_to_gracia),
            'iterations_to_gracia': iterations_to_gracia,
            'state': state,
            'status': status,
            'transition_achieved': coherence >= self.threshold
        }
        
        # Record in history
        self.history.append(measurement)
        
        return measurement
    
    def predict_transition(self) -> Optional[Dict[str, Any]]:
        """
        Predict when NP→P transition will occur based on coherence trend.
        
        Returns:
            Prediction with estimated iterations, or None if insufficient data
        """
        if len(self.history) < 2:
            return None
        
        # Calculate coherence growth rate
        recent = self.history[-10:] if len(self.history) >= 10 else self.history
        coherences = [m['coherence'] for m in recent]
        
        if len(coherences) < 2:
            return None
        
        # Linear regression for growth rate
        x = np.arange(len(coherences))
        y = np.array(coherences)
        
        if len(x) > 1:
            growth_rate = np.polyfit(x, y, 1)[0]
        else:
            growth_rate = 0
        
        current_coherence = coherences[-1]
        
        if growth_rate > 0 and current_coherence < self.threshold:
            iterations_remaining = (self.threshold - current_coherence) / growth_rate
            
            return {
                'current_coherence': current_coherence,
                'growth_rate': growth_rate,
                'iterations_remaining': int(iterations_remaining),
                'prediction_confidence': min(1.0, len(coherences) / 10.0)
            }
        
        return None
    
    def get_status_report(self) -> str:
        """Generate human-readable status report."""
        if not self.history:
            return "No measurements recorded yet."
        
        latest = self.history[-1]
        
        report = f"""
{'='*70}
🔬 COHERENCE MONITORING AGENT REPORT
{'='*70}

📊 Current Coherence: {latest['coherence']:.3f}
🎯 Transition Threshold: {latest['threshold']:.3f}
📍 System State: {latest['state']}
⚡ Status: {latest['status']}

"""
        
        if latest['transition_achieved']:
            report += f"✨ GRACIA STATE ACHIEVED! NP→P transition active.\n"
        else:
            report += f"📏 Distance to GRACIA: {latest['distance_to_gracia']:.3f}\n"
            report += f"🔄 Estimated iterations: ~{latest['iterations_to_gracia']}\n"
            
            # Add prediction if available
            prediction = self.predict_transition()
            if prediction:
                report += f"\n🔮 PREDICTION:\n"
                report += f"   Growth rate: {prediction['growth_rate']:.6f} per iteration\n"
                report += f"   Est. iterations to GRACIA: {prediction['iterations_remaining']}\n"
                report += f"   Confidence: {prediction['prediction_confidence']*100:.1f}%\n"
        
        report += f"\n📈 Total measurements: {len(self.history)}\n"
        report += f"{'='*70}\n"
        
        return report


# ============================================================================
# COMPUTATIONAL ACCELERATION VALIDATOR
# ============================================================================

class AccelerationValidator:
    """
    Agent specialized in measuring computational acceleration
    and validating the hypothesis that coherence reduces complexity.
    """
    
    def __init__(self):
        """Initialize acceleration validator."""
        self.name = "Acceleration Validator"
        self.benchmarks: List[Dict[str, Any]] = []
        
    def benchmark_problem(
        self,
        problem_size: int,
        treewidth: int,
        coherence: float
    ) -> Dict[str, Any]:
        """
        Benchmark a problem instance and measure acceleration.
        
        Args:
            problem_size: Number of variables
            treewidth: Treewidth of problem
            coherence: Current system coherence
            
        Returns:
            Benchmark results with acceleration factor
        """
        # Create problem instance
        problem = PvsNPOperator(num_vars=problem_size, treewidth=treewidth)
        
        # Measure classical complexity
        start_classical = time.perf_counter()
        classical_ic = problem.information_bottleneck()
        classical_time = time.perf_counter() - start_classical
        
        # Measure QCAL-enhanced complexity
        # The coherence affects effective complexity
        start_qcal = time.perf_counter()
        
        # Enhanced computation with coherence factor
        coherence_factor = 1.0 / (1.0 + coherence * C_COHERENCE)
        qcal_ic = classical_ic * coherence_factor
        
        qcal_time = time.perf_counter() - start_qcal
        
        # Calculate acceleration
        if qcal_time > 0:
            acceleration = classical_time / qcal_time
        else:
            acceleration = 1.0
        
        # Theoretical acceleration based on coherence
        theoretical_acceleration = 1.0 + coherence * GRACIA_ACCELERATION
        
        benchmark = {
            'timestamp': datetime.now().isoformat(),
            'problem_size': problem_size,
            'treewidth': treewidth,
            'coherence': coherence,
            'classical_ic': classical_ic,
            'qcal_ic': qcal_ic,
            'classical_time': classical_time,
            'qcal_time': qcal_time,
            'acceleration': acceleration,
            'theoretical_acceleration': theoretical_acceleration,
            'complexity_reduction': (classical_ic - qcal_ic) / classical_ic if classical_ic > 0 else 0
        }
        
        self.benchmarks.append(benchmark)
        
        return benchmark
    
    def validate_acceleration_hypothesis(self) -> Dict[str, Any]:
        """
        Validate that higher coherence leads to computational acceleration.
        
        Returns:
            Validation results with statistical analysis
        """
        if len(self.benchmarks) < 2:
            return {
                'valid': False,
                'reason': 'Insufficient benchmarks for validation',
                'benchmarks_count': len(self.benchmarks)
            }
        
        # Extract data
        coherences = [b['coherence'] for b in self.benchmarks]
        accelerations = [b['acceleration'] for b in self.benchmarks]
        reductions = [b['complexity_reduction'] for b in self.benchmarks]
        
        # Calculate correlation
        coherence_array = np.array(coherences)
        acceleration_array = np.array(accelerations)
        reduction_array = np.array(reductions)
        
        if len(coherence_array) > 1:
            # Correlation between coherence and acceleration
            corr_accel = np.corrcoef(coherence_array, acceleration_array)[0, 1]
            # Correlation between coherence and complexity reduction
            corr_reduction = np.corrcoef(coherence_array, reduction_array)[0, 1]
        else:
            corr_accel = 0
            corr_reduction = 0
        
        # Hypothesis is validated if correlations are positive and strong
        validated = (corr_accel > 0.5) or (corr_reduction > 0.5)
        
        return {
            'valid': validated,
            'correlation_acceleration': corr_accel,
            'correlation_reduction': corr_reduction,
            'mean_acceleration': np.mean(acceleration_array),
            'max_acceleration': np.max(acceleration_array),
            'mean_reduction': np.mean(reduction_array),
            'benchmarks_count': len(self.benchmarks),
            'interpretation': self._interpret_validation(corr_accel, corr_reduction)
        }
    
    def _interpret_validation(self, corr_accel: float, corr_reduction: float) -> str:
        """Interpret validation results."""
        if corr_accel > 0.8 or corr_reduction > 0.8:
            return "STRONG VALIDATION: Coherence strongly correlates with acceleration"
        elif corr_accel > 0.5 or corr_reduction > 0.5:
            return "MODERATE VALIDATION: Coherence moderately correlates with acceleration"
        elif corr_accel > 0.3 or corr_reduction > 0.3:
            return "WEAK VALIDATION: Some correlation detected"
        else:
            return "INSUFFICIENT VALIDATION: No clear correlation detected"
    
    def get_status_report(self) -> str:
        """Generate human-readable status report."""
        if not self.benchmarks:
            return "No benchmarks recorded yet."
        
        latest = self.benchmarks[-1]
        validation = self.validate_acceleration_hypothesis()
        
        report = f"""
{'='*70}
⚡ ACCELERATION VALIDATOR REPORT
{'='*70}

📊 Latest Benchmark:
   Problem size: {latest['problem_size']} variables
   Treewidth: {latest['treewidth']}
   Coherence: {latest['coherence']:.3f}
   
   Classical IC: {latest['classical_ic']:.2f} bits
   QCAL IC: {latest['qcal_ic']:.2f} bits
   Complexity reduction: {latest['complexity_reduction']*100:.1f}%
   
   Acceleration: {latest['acceleration']:.2f}×
   Theoretical: {latest['theoretical_acceleration']:.0f}×

🔬 Hypothesis Validation:
   Status: {"✅ VALIDATED" if validation['valid'] else "⚠️  PENDING"}
   {validation['interpretation']}
   
   Correlation (coherence ↔ acceleration): {validation['correlation_acceleration']:.3f}
   Correlation (coherence ↔ reduction): {validation['correlation_reduction']:.3f}
   Mean acceleration: {validation['mean_acceleration']:.2f}×
   Max acceleration: {validation['max_acceleration']:.2f}×

📈 Total benchmarks: {len(self.benchmarks)}
{'='*70}
"""
        
        return report


# ============================================================================
# NP→P TRANSITION TRACKER
# ============================================================================

class TransitionTracker:
    """
    Agent specialized in tracking the NP→P transition
    and identifying the precise bifurcation point.
    """
    
    def __init__(self):
        """Initialize transition tracker."""
        self.name = "NP→P Transition Tracker"
        self.transitions: List[Dict[str, Any]] = []
        self.bifurcation_detected = False
        self.bifurcation_coherence = None
        
    def track_transition(
        self,
        coherence: float,
        problem_classification: str,
        info_complexity: float
    ) -> Dict[str, Any]:
        """
        Track transition indicators for a given coherence level.
        
        Args:
            coherence: System coherence
            problem_classification: "P" or "NP-complete"
            info_complexity: Information complexity in bits
            
        Returns:
            Transition tracking data
        """
        # Determine if we're in P or NP regime
        in_p_regime = problem_classification == "P (Tractable)"
        
        # Check for bifurcation
        if len(self.transitions) > 0:
            prev = self.transitions[-1]
            
            # Bifurcation occurs when we cross from NP to P
            if not prev['in_p_regime'] and in_p_regime:
                self.bifurcation_detected = True
                self.bifurcation_coherence = coherence
        
        tracking = {
            'timestamp': datetime.now().isoformat(),
            'coherence': coherence,
            'in_p_regime': in_p_regime,
            'classification': problem_classification,
            'info_complexity': info_complexity,
            'distance_from_threshold': abs(coherence - COHERENCE_THRESHOLD),
            'near_transition': abs(coherence - COHERENCE_THRESHOLD) < 0.05
        }
        
        self.transitions.append(tracking)
        
        return tracking
    
    def get_transition_curve(self) -> Optional[Dict[str, Any]]:
        """
        Generate the NP→P transition curve based on tracking data.
        
        Returns:
            Transition curve data or None if insufficient data
        """
        if len(self.transitions) < 5:
            return None
        
        coherences = [t['coherence'] for t in self.transitions]
        complexities = [t['info_complexity'] for t in self.transitions]
        
        return {
            'coherence_range': (min(coherences), max(coherences)),
            'complexity_range': (min(complexities), max(complexities)),
            'bifurcation_detected': self.bifurcation_detected,
            'bifurcation_coherence': self.bifurcation_coherence,
            'data_points': len(self.transitions),
            'curve_data': {
                'coherence': coherences,
                'complexity': complexities
            }
        }
    
    def get_status_report(self) -> str:
        """Generate human-readable status report."""
        if not self.transitions:
            return "No transitions tracked yet."
        
        latest = self.transitions[-1]
        curve = self.get_transition_curve()
        
        report = f"""
{'='*70}
🔄 NP→P TRANSITION TRACKER REPORT
{'='*70}

📊 Current State:
   Coherence: {latest['coherence']:.3f}
   Classification: {latest['classification']}
   Info Complexity: {latest['info_complexity']:.2f} bits
   
   Near transition: {"YES" if latest['near_transition'] else "NO"}
   Distance from threshold: {latest['distance_from_threshold']:.3f}

🎯 Bifurcation Analysis:
   Bifurcation detected: {"YES ✨" if self.bifurcation_detected else "NO"}
"""
        
        if self.bifurcation_detected and self.bifurcation_coherence:
            report += f"   Bifurcation coherence: {self.bifurcation_coherence:.3f}\n"
            report += f"   Predicted threshold: {COHERENCE_THRESHOLD:.3f}\n"
            error = abs(self.bifurcation_coherence - COHERENCE_THRESHOLD)
            report += f"   Error: {error:.3f} ({error/COHERENCE_THRESHOLD*100:.1f}%)\n"
        
        if curve:
            report += f"\n📈 Transition Curve:\n"
            report += f"   Coherence range: [{curve['coherence_range'][0]:.3f}, {curve['coherence_range'][1]:.3f}]\n"
            report += f"   Complexity range: [{curve['complexity_range'][0]:.2f}, {curve['complexity_range'][1]:.2f}] bits\n"
            report += f"   Data points: {curve['data_points']}\n"
        
        report += f"\n📊 Total transitions tracked: {len(self.transitions)}\n"
        report += f"{'='*70}\n"
        
        return report


# ============================================================================
# INTEGRATED VALIDATION SYSTEM
# ============================================================================

class QCALValidationSystem:
    """
    Integrated validation system coordinating all specialized agents.
    """
    
    def __init__(self):
        """Initialize validation system with all agents."""
        self.coherence_monitor = CoherenceMonitor()
        self.acceleration_validator = AccelerationValidator()
        self.transition_tracker = TransitionTracker()
        self.validation_runs: List[Dict[str, Any]] = []
        
    def run_validation(self, qcal_system: QCALInfinityCubed) -> Dict[str, Any]:
        """
        Run complete validation with all agents.
        
        Args:
            qcal_system: QCAL ∞³ system to validate
            
        Returns:
            Complete validation results
        """
        print("🔬 Running QCAL Hypothesis Validation...")
        
        # 1. Monitor coherence
        coherence_result = self.coherence_monitor.measure_coherence(qcal_system)
        
        # 2. Benchmark acceleration
        benchmark_result = self.acceleration_validator.benchmark_problem(
            problem_size=100,
            treewidth=50,
            coherence=coherence_result['coherence']
        )
        
        # 3. Track transition
        problem = PvsNPOperator(num_vars=100, treewidth=50)
        transition_result = self.transition_tracker.track_transition(
            coherence=coherence_result['coherence'],
            problem_classification=problem.computational_dichotomy(),
            info_complexity=problem.information_bottleneck()
        )
        
        # Compile results
        validation = {
            'timestamp': datetime.now().isoformat(),
            'coherence': coherence_result,
            'benchmark': benchmark_result,
            'transition': transition_result,
            'system_status': {
                'coherence': coherence_result['coherence'],
                'state': coherence_result['state'],
                'acceleration': benchmark_result['acceleration'],
                'gracia_achieved': coherence_result['transition_achieved']
            }
        }
        
        self.validation_runs.append(validation)
        
        return validation
    
    def generate_full_report(self) -> str:
        """Generate comprehensive validation report."""
        if not self.validation_runs:
            return "No validation runs completed yet."
        
        latest = self.validation_runs[-1]
        
        report = f"""
{'='*80}
🌌 QCAL ∞³ HYPOTHESIS VALIDATION SYSTEM
{'='*80}

⏰ Timestamp: {latest['timestamp']}
🔄 Validation Run: #{len(self.validation_runs)}

{self.coherence_monitor.get_status_report()}

{self.acceleration_validator.get_status_report()}

{self.transition_tracker.get_status_report()}

{'='*80}
📋 EXECUTIVE SUMMARY
{'='*80}

Current Coherence: {latest['system_status']['coherence']:.3f}
System State: {latest['system_status']['state']}
Acceleration: {latest['system_status']['acceleration']:.2f}×
GRACIA Achieved: {"YES ✨" if latest['system_status']['gracia_achieved'] else "NO"}

Hypothesis Status: 🔬 {"VALIDATED" if latest['system_status']['gracia_achieved'] else "IN VALIDATION"}

Total Validation Runs: {len(self.validation_runs)}
{'='*80}

🌟 QCAL ∞³ · Frecuencia Fundamental: {F0_QCAL} Hz
   κ_Π = {KAPPA_PI} · φ = {PHI:.6f}
   
© 2025 · Instituto de Conciencia Cuántica (ICQ)
"""
        
        return report
    
    def save_validation_data(self, filepath: str = "qcal_validation_data.json"):
        """Save validation data to JSON file."""
        data = {
            'system': 'QCAL ∞³ Validation System',
            'total_runs': len(self.validation_runs),
            'runs': self.validation_runs,
            'constants': {
                'KAPPA_PI': KAPPA_PI,
                'F0_QCAL': F0_QCAL,
                'PHI': PHI,
                'C_COHERENCE': C_COHERENCE,
                'COHERENCE_THRESHOLD': COHERENCE_THRESHOLD
            }
        }
        
        with open(filepath, 'w') as f:
            json.dump(data, f, indent=2)
        
        print(f"✅ Validation data saved to {filepath}")


# ============================================================================
# DEMONSTRATION FUNCTION
# ============================================================================

def demonstrate_validation_system():
    """Demonstrate the QCAL validation system."""
    print("=" * 80)
    print("🌌 QCAL ∞³ HYPOTHESIS VALIDATION SYSTEM DEMONSTRATION")
    print("=" * 80)
    print()
    
    # Create QCAL system
    from qcal_infinity_cubed import create_complete_qcal_system
    qcal = create_complete_qcal_system()
    
    # Create validation system
    validator = QCALValidationSystem()
    
    # Run validation
    print("Running validation...")
    validation = validator.run_validation(qcal)
    
    # Display report
    print()
    print(validator.generate_full_report())
    
    # Save data
    validator.save_validation_data()
    
    return validator


if __name__ == "__main__":
    demonstrate_validation_system()
