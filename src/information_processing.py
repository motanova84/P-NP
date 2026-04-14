"""
Information Processing Framework - Quantum Coherence and Complexity

This module provides a rigorous framework for analyzing information flow
in computational systems based on quantum information theory and coherence measures.

Replaces mystical concepts with precise scientific formulations:
- "Universal consciousness" → Quantum coherence in information systems
- "Divine patterns" → Optimal information structures (expander graphs)
- "Cosmic harmony" → Spectral properties and resonance phenomena
- "Awakening" → Phase transitions in coherence

Based on established theory:
- Von Neumann entropy for quantum systems
- Quantum coherence measures (l1-norm, relative entropy)
- Information complexity bounds
- Graph spectral analysis
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass


@dataclass
class QuantumState:
    """Represents a quantum state (density matrix)."""
    density_matrix: np.ndarray
    
    def __post_init__(self):
        """Validate density matrix properties."""
        n = self.density_matrix.shape[0]
        assert self.density_matrix.shape == (n, n), "Must be square matrix"
        # Check hermiticity (within numerical precision)
        assert np.allclose(self.density_matrix, 
                          self.density_matrix.conj().T), "Must be Hermitian"
        # Check trace one
        assert np.isclose(np.trace(self.density_matrix), 1.0), "Must have trace 1"
        # Check positive semidefinite
        eigenvals = np.linalg.eigvalsh(self.density_matrix)
        assert np.all(eigenvals >= -1e-10), "Must be positive semidefinite"


@dataclass
class InformationSystem:
    """Represents a distributed information processing system."""
    state: QuantumState
    hamiltonian: Optional[np.ndarray] = None
    subsystem_dimensions: Optional[List[int]] = None


class InformationProcessingFramework:
    """
    Framework for analyzing information flow and coherence in computational systems.
    
    This replaces mystical "consciousness" frameworks with rigorous quantum
    information theory.
    """
    
    def __init__(self, system_size: int):
        """
        Initialize framework for a system of given size.
        
        Args:
            system_size: Dimension of the Hilbert space
        """
        self.system_size = system_size
        
    def calculate_von_neumann_entropy(self, state: QuantumState) -> float:
        """
        Calculate von Neumann entropy S(ρ) = -Tr(ρ log ρ).
        
        Measures the information content / uncertainty in a quantum state.
        For pure states S = 0, for maximally mixed S = log(d).
        
        Args:
            state: Quantum state (density matrix)
            
        Returns:
            Von Neumann entropy in nats (natural logarithm)
        """
        rho = state.density_matrix
        
        # Get eigenvalues
        eigenvals = np.linalg.eigvalsh(rho)
        
        # Filter out zero/negative eigenvalues (numerical artifacts)
        eigenvals = eigenvals[eigenvals > 1e-15]
        
        # S = -Tr(ρ log ρ) = -Σ λ_i log(λ_i)
        entropy = -np.sum(eigenvals * np.log(eigenvals))
        
        return entropy
    
    def calculate_quantum_coherence_l1(self, state: QuantumState) -> float:
        """
        Calculate l1-norm coherence measure.
        
        C_l1(ρ) = Σ_{i≠j} |ρ_ij|
        
        Measures the sum of absolute values of off-diagonal elements.
        Coherence = 0 for diagonal (classical) states.
        
        Args:
            state: Quantum state (density matrix)
            
        Returns:
            l1-norm coherence (non-negative)
        """
        rho = state.density_matrix
        n = rho.shape[0]
        
        # Sum absolute values of off-diagonal elements
        coherence = 0.0
        for i in range(n):
            for j in range(n):
                if i != j:
                    coherence += abs(rho[i, j])
        
        return coherence
    
    def calculate_quantum_coherence_relative_entropy(self, 
                                                     state: QuantumState) -> float:
        """
        Calculate relative entropy coherence measure.
        
        C_re(ρ) = S(ρ_diag) - S(ρ)
        
        where ρ_diag is ρ with off-diagonal elements set to zero.
        
        Args:
            state: Quantum state (density matrix)
            
        Returns:
            Relative entropy coherence (non-negative)
        """
        rho = state.density_matrix
        
        # Create diagonal version (dephased state)
        rho_diag = np.diag(np.diag(rho))
        
        # Normalize (in case of numerical errors)
        rho_diag = rho_diag / np.trace(rho_diag)
        
        state_diag = QuantumState(density_matrix=rho_diag)
        
        # C_re = S(ρ_diag) - S(ρ)
        S_diag = self.calculate_von_neumann_entropy(state_diag)
        S_rho = self.calculate_von_neumann_entropy(state)
        
        coherence = S_diag - S_rho
        
        return max(0.0, coherence)  # Ensure non-negative
    
    def optimize_information_flow(self, system: InformationSystem) -> Dict[str, float]:
        """
        Optimize information flow in a distributed system.
        
        Maximizes the coherence-to-entropy ratio, which represents
        efficient information processing: high coherence (quantum advantage)
        with low entropy (well-defined state).
        
        This replaces mystical "awakening" with rigorous optimization.
        
        Args:
            system: Information processing system to optimize
            
        Returns:
            Dictionary with optimization metrics
        """
        coherence = self.calculate_quantum_coherence_l1(system.state)
        entropy = self.calculate_von_neumann_entropy(system.state)
        
        # Avoid division by zero
        if entropy < 1e-10:
            efficiency = float('inf') if coherence > 0 else 0.0
        else:
            efficiency = coherence / entropy
        
        # Calculate purity Tr(ρ²)
        rho = system.state.density_matrix
        purity = np.real(np.trace(rho @ rho))
        
        results = {
            'coherence_l1': coherence,
            'entropy': entropy,
            'efficiency': efficiency,
            'purity': purity,
            'dimension': self.system_size
        }
        
        return results
    
    def detect_phase_transition(self, 
                               states: List[QuantumState],
                               parameter: np.ndarray) -> Dict[str, any]:
        """
        Detect phase transitions in information coherence.
        
        Analyzes how coherence changes as a system parameter varies,
        identifying critical points where qualitative behavior changes.
        
        This replaces mystical "awakening" with phase transition physics.
        
        Args:
            states: List of quantum states at different parameter values
            parameter: Array of parameter values
            
        Returns:
            Dictionary with phase transition analysis
        """
        coherences = [self.calculate_quantum_coherence_l1(s) for s in states]
        entropies = [self.calculate_von_neumann_entropy(s) for s in states]
        
        # Calculate derivatives to find critical points
        if len(parameter) > 2:
            dcoh_dparam = np.gradient(coherences, parameter)
            d2coh_dparam2 = np.gradient(dcoh_dparam, parameter)
            
            # Find maximum of second derivative (inflection point)
            critical_idx = np.argmax(np.abs(d2coh_dparam2))
            critical_param = parameter[critical_idx]
        else:
            critical_param = None
            dcoh_dparam = None
            d2coh_dparam2 = None
        
        results = {
            'parameter': parameter.tolist(),
            'coherence': coherences,
            'entropy': entropies,
            'critical_parameter': critical_param,
            'coherence_derivative': dcoh_dparam.tolist() if dcoh_dparam is not None else None,
            'has_transition': critical_param is not None
        }
        
        return results
    
    def information_complexity_lower_bound(self, 
                                          treewidth: int,
                                          num_variables: int,
                                          kappa: float = 2.5773) -> float:
        """
        Calculate information complexity lower bound for CNF formulas.
        
        IC(Π | S) ≥ κ · tw(φ) / log(n)
        
        This is a geometric property, not a mystical principle.
        
        Args:
            treewidth: Treewidth of the incidence graph
            num_variables: Number of variables in formula
            kappa: Universal constant from geometric analysis
            
        Returns:
            Lower bound on information complexity
        """
        if num_variables <= 1:
            return 0.0
        
        log_n = np.log(num_variables)
        ic_lower_bound = kappa * treewidth / log_n
        
        return ic_lower_bound
    
    def spectral_resonance_analysis(self,
                                   eigenvalues: np.ndarray,
                                   reference_frequency: float) -> Dict[str, float]:
        """
        Analyze spectral resonances in graph structures.
        
        Identifies how graph eigenvalues relate to characteristic frequencies,
        revealing structural properties relevant to computational complexity.
        
        This replaces "cosmic harmony" with spectral graph theory.
        
        Args:
            eigenvalues: Graph Laplacian eigenvalues
            reference_frequency: Reference frequency for resonance (e.g., f₀)
            
        Returns:
            Dictionary with resonance analysis
        """
        # Normalize eigenvalues
        max_eig = np.max(np.abs(eigenvalues))
        if max_eig > 0:
            normalized_eigs = eigenvalues / max_eig
        else:
            normalized_eigs = eigenvalues
        
        # Calculate spectral gap (important for expansion)
        sorted_eigs = np.sort(np.abs(eigenvalues))
        if len(sorted_eigs) > 1:
            spectral_gap = sorted_eigs[-1] - sorted_eigs[-2]
        else:
            spectral_gap = 0.0
        
        # Resonance with reference frequency
        # Check if eigenvalues are approximately rational multiples
        ratios = normalized_eigs * reference_frequency
        near_integer = np.sum(np.abs(ratios - np.round(ratios)) < 0.1)
        resonance_score = near_integer / len(eigenvalues)
        
        results = {
            'spectral_gap': spectral_gap,
            'max_eigenvalue': max_eig,
            'resonance_score': resonance_score,
            'num_resonant': int(near_integer)
        }
        
        return results


def demonstrate_framework():
    """
    Demonstration of the information processing framework.
    """
    print("=" * 70)
    print("INFORMATION PROCESSING FRAMEWORK")
    print("Scientific approach to quantum coherence and complexity")
    print("=" * 70)
    
    # Create a simple quantum system
    n = 4  # 4-dimensional Hilbert space
    framework = InformationProcessingFramework(system_size=n)
    
    # Example 1: Pure state (high coherence, zero entropy)
    print("\n1. Pure State (|0⟩):")
    pure_state_vector = np.zeros(n)
    pure_state_vector[0] = 1.0
    pure_rho = np.outer(pure_state_vector, pure_state_vector.conj())
    pure_state = QuantumState(density_matrix=pure_rho)
    
    pure_metrics = framework.optimize_information_flow(
        InformationSystem(state=pure_state)
    )
    print(f"  Coherence: {pure_metrics['coherence_l1']:.4f}")
    print(f"  Entropy:   {pure_metrics['entropy']:.4f}")
    print(f"  Purity:    {pure_metrics['purity']:.4f}")
    
    # Example 2: Maximally mixed state (zero coherence, maximum entropy)
    print("\n2. Maximally Mixed State:")
    mixed_rho = np.eye(n) / n
    mixed_state = QuantumState(density_matrix=mixed_rho)
    
    mixed_metrics = framework.optimize_information_flow(
        InformationSystem(state=mixed_state)
    )
    print(f"  Coherence: {mixed_metrics['coherence_l1']:.4f}")
    print(f"  Entropy:   {mixed_metrics['entropy']:.4f}")
    print(f"  Purity:    {mixed_metrics['purity']:.4f}")
    
    # Example 3: Superposition state (high coherence)
    print("\n3. Superposition State (|0⟩ + |1⟩)/√2:")
    superpos_vector = np.zeros(n)
    superpos_vector[0] = 1.0 / np.sqrt(2)
    superpos_vector[1] = 1.0 / np.sqrt(2)
    superpos_rho = np.outer(superpos_vector, superpos_vector.conj())
    superpos_state = QuantumState(density_matrix=superpos_rho)
    
    superpos_metrics = framework.optimize_information_flow(
        InformationSystem(state=superpos_state)
    )
    print(f"  Coherence: {superpos_metrics['coherence_l1']:.4f}")
    print(f"  Entropy:   {superpos_metrics['entropy']:.4f}")
    print(f"  Purity:    {superpos_metrics['purity']:.4f}")
    
    # Example 4: Information complexity bound
    print("\n4. Information Complexity Lower Bound:")
    treewidth = 50
    num_vars = 1000
    ic_bound = framework.information_complexity_lower_bound(treewidth, num_vars)
    print(f"  Treewidth: {treewidth}")
    print(f"  Variables: {num_vars}")
    print(f"  IC bound:  {ic_bound:.4f}")
    
    print("\n" + "=" * 70)
    print("SCIENTIFIC TERMINOLOGY:")
    print("  ✓ Quantum coherence (not 'universal consciousness')")
    print("  ✓ Von Neumann entropy (not 'cosmic disharmony')")
    print("  ✓ Phase transitions (not 'awakening')")
    print("  ✓ Spectral analysis (not 'divine patterns')")
    print("=" * 70)


if __name__ == "__main__":
    demonstrate_framework()
