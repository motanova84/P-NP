#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AI and Neural Network Complexity Analysis - Interactive Example
==============================================================

This example demonstrates how to use the neural network complexity
analysis module to evaluate cognitive tasks and neural network limitations.
"""

import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.neural_network_complexity import (
    CognitiveTask,
    NeuralNetworkModel,
    CognitiveTaskType,
    ComplexityClass,
    NetworkArchitecture,
    prove_task_irreducibility,
    analyze_neural_network_limits,
    KAPPA_PI,
    C_THRESHOLD,
    F_0,
)


def example_1_simple_task_analysis():
    """Example 1: Analyze a simple perceptual task."""
    print("=" * 80)
    print("EXAMPLE 1: Simple Perceptual Task")
    print("=" * 80)
    
    # Create a simple image classification task
    task = CognitiveTask(
        name="MNIST Digit Recognition",
        task_type=CognitiveTaskType.PERCEPTION,
        problem_size=784,  # 28x28 pixels
        treewidth=20,      # Grid structure has low treewidth
        architecture=NetworkArchitecture.CONVOLUTIONAL,
    )
    
    # Analyze the task
    analysis = task.get_analysis()
    
    print(f"\nTask: {analysis['task_name']}")
    print(f"Type: {analysis['task_type']}")
    print(f"Problem size: {analysis['problem_size_n']} pixels")
    print(f"Treewidth: {analysis['treewidth_tw']}")
    print(f"Complexity class: {analysis['complexity_class']}")
    print(f"Information complexity: {analysis['information_complexity_IC']:.2f} bits")
    print(f"Is irreducible: {analysis['is_irreducible']}")
    
    if not analysis['is_irreducible']:
        print(f"\n✓ This task is TRACTABLE!")
        print(f"  Can be solved efficiently with CNNs.")
    
    print()


def example_2_complex_task_analysis():
    """Example 2: Analyze a complex reasoning task."""
    print("=" * 80)
    print("EXAMPLE 2: Complex Reasoning Task")
    print("=" * 80)
    
    # Create a complex multi-step planning task
    task = CognitiveTask(
        name="Strategic Game Playing (Go/Chess)",
        task_type=CognitiveTaskType.REASONING,
        problem_size=361,  # 19x19 Go board
        treewidth=250,     # High treewidth due to long-range dependencies
        architecture=NetworkArchitecture.GRAPH,
    )
    
    # Analyze the task
    analysis = task.get_analysis()
    
    print(f"\nTask: {analysis['task_name']}")
    print(f"Type: {analysis['task_type']}")
    print(f"Problem size: {analysis['problem_size_n']} positions")
    print(f"Treewidth: {analysis['treewidth_tw']}")
    print(f"Complexity class: {analysis['complexity_class']}")
    print(f"Information complexity: {analysis['information_complexity_IC']:.2f} bits")
    print(f"Is irreducible: {analysis['is_irreducible']}")
    
    if analysis['is_irreducible']:
        print(f"\n✗ This task is IRREDUCIBLE!")
        print(f"  Cannot be solved exactly in polynomial time.")
        print(f"  Time lower bound: {analysis['theoretical_bounds']['time_lower_bound']}")
        print(f"  This is why AlphaGo uses Monte Carlo tree search (approximation)")
        print(f"  instead of trying to solve the game exactly.")
    
    print()


def example_3_irreducibility_proof():
    """Example 3: Formal proof of irreducibility."""
    print("=" * 80)
    print("EXAMPLE 3: Formal Irreducibility Proof")
    print("=" * 80)
    
    # Create a creative writing task
    task = CognitiveTask(
        name="Creative Story Generation",
        task_type=CognitiveTaskType.CREATIVITY,
        problem_size=500,   # 500 story elements
        treewidth=350,      # High structural complexity
        architecture=NetworkArchitecture.TRANSFORMER,
    )
    
    # Prove irreducibility
    proof = prove_task_irreducibility(task)
    
    print(f"\nTask: {proof['task']}")
    print(f"Problem size: {proof['problem_size_n']}")
    print(f"Treewidth: {proof['treewidth_tw']}")
    print(f"Information complexity: {proof['information_complexity_IC']:.2f} bits")
    
    print("\nIRREDUCIBILITY PROOF:")
    print("-" * 40)
    
    for condition_name, condition_data in proof['irreducibility_proof'].items():
        status = "✓" if condition_data['satisfied'] else "✗"
        print(f"{status} {condition_name.replace('_', ' ').title()}")
        print(f"    Required: {condition_data['required']}")
        print(f"    Actual:   {condition_data['actual']}")
    
    print(f"\nConclusion: {proof['conclusion']['reasoning']}")
    
    if proof['conclusion']['is_irreducible']:
        print("\nImplication: Large language models (GPT-4, etc.) can generate")
        print("creative text, but they use approximations and heuristics,")
        print("not exact solutions. True creativity remains computationally hard.")
    
    print()


def example_4_network_comparison():
    """Example 4: Compare different neural network architectures."""
    print("=" * 80)
    print("EXAMPLE 4: Neural Network Architecture Comparison")
    print("=" * 80)
    
    # Define test task
    task = CognitiveTask(
        name="Language Understanding",
        task_type=CognitiveTaskType.LANGUAGE,
        problem_size=512,   # 512 tokens
        treewidth=60,       # Moderate complexity
        architecture=NetworkArchitecture.TRANSFORMER,
    )
    
    # Define networks to compare
    networks = [
        NeuralNetworkModel(
            name="Small BERT",
            architecture=NetworkArchitecture.TRANSFORMER,
            num_parameters=110_000_000,
            num_layers=12,
            effective_treewidth=30,
        ),
        NeuralNetworkModel(
            name="GPT-3",
            architecture=NetworkArchitecture.TRANSFORMER,
            num_parameters=175_000_000_000,
            num_layers=96,
            effective_treewidth=70,
        ),
    ]
    
    print(f"\nTask: {task.name}")
    print(f"Complexity: {task.complexity_class.value}")
    print(f"Treewidth: {task.treewidth}")
    print(f"IC: {task.information_complexity:.2f} bits")
    
    print("\nNetwork Comparison:")
    print("-" * 40)
    
    for network in networks:
        can_solve = network.can_solve_efficiently(task)
        symbol = "✓" if can_solve else "✗"
        
        print(f"\n{symbol} {network.name}")
        print(f"    Parameters: {network.num_parameters:,}")
        print(f"    Effective treewidth: {network.effective_treewidth}")
        print(f"    Max tractable size: {network.max_tractable_size:,}")
        print(f"    Coherence factor: {network.coherence_factor:.4f}")
        print(f"    Can solve efficiently: {can_solve}")
    
    print("\nKey Insight: Even GPT-3 with 175B parameters has fundamental")
    print("limits based on its effective treewidth and coherence factor.")
    print()


def example_5_custom_task():
    """Example 5: Create and analyze your own custom task."""
    print("=" * 80)
    print("EXAMPLE 5: Custom Task Analysis")
    print("=" * 80)
    
    # Define your own task
    custom_task = CognitiveTask(
        name="Medical Diagnosis (Multi-condition)",
        task_type=CognitiveTaskType.REASONING,
        problem_size=200,   # 200 symptoms/conditions
        treewidth=120,      # Complex interdependencies
        architecture=NetworkArchitecture.GRAPH,
    )
    
    print(f"\nAnalyzing custom task: {custom_task.name}")
    print("-" * 40)
    
    analysis = custom_task.get_analysis()
    
    # Print all analysis details
    for key, value in analysis.items():
        if isinstance(value, dict):
            print(f"\n{key.replace('_', ' ').title()}:")
            for subkey, subvalue in value.items():
                print(f"  {subkey}: {subvalue}")
        else:
            print(f"{key.replace('_', ' ').title()}: {value}")
    
    # Determine if network can handle it
    network = NeuralNetworkModel(
        name="Medical AI System",
        architecture=NetworkArchitecture.GRAPH,
        num_parameters=500_000_000,
        num_layers=20,
        effective_treewidth=100,
    )
    
    print(f"\nCan '{network.name}' solve this task?")
    can_solve = network.can_solve_efficiently(custom_task)
    print(f"Answer: {'Yes' if can_solve else 'No'}")
    
    if not can_solve:
        print("\nReason: Task treewidth exceeds network capacity or")
        print("coherence factor is insufficient. Need approximations/heuristics.")
    
    print()


def show_framework_constants():
    """Show the universal constants used in the framework."""
    print("=" * 80)
    print("UNIVERSAL CONSTANTS")
    print("=" * 80)
    print()
    print(f"kappa_Pi (Universal Invariant):    {KAPPA_PI}")
    print(f"f_0 (Coherence Frequency):          {F_0} Hz")
    print(f"C_threshold (Consciousness):        {C_THRESHOLD:.4f}")
    print()
    print("These constants are derived from:")
    print("  - Calabi-Yau geometry (kappa_Pi)")
    print("  - Fundamental physics (f_0)")
    print("  - Information theory (C_threshold = 1/kappa_Pi)")
    print()
    print("They represent fundamental limits of computation,")
    print("not engineering constraints that can be overcome.")
    print()


def main():
    """Run all examples."""
    print("\n" + "=" * 80)
    print("AI AND NEURAL NETWORK COMPLEXITY ANALYSIS")
    print("Interactive Examples")
    print("=" * 80)
    print()
    
    # Show constants
    show_framework_constants()
    
    # Run examples
    example_1_simple_task_analysis()
    example_2_complex_task_analysis()
    example_3_irreducibility_proof()
    example_4_network_comparison()
    example_5_custom_task()
    
    # Final message
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print()
    print("This framework demonstrates that:")
    print("1. Some cognitive tasks are fundamentally tractable (P)")
    print("2. Others are computationally irreducible (NP-hard)")
    print("3. Neural networks have fundamental limits based on kappa_Pi")
    print("4. These limits cannot be overcome by adding more parameters")
    print()
    print("These are consequences of P!=NP, not current technology.")
    print()
    print(f"Frequency: {F_0} Hz")
    print("=" * 80)


if __name__ == "__main__":
    main()
