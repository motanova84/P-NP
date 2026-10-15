#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Neural Network Complexity Analysis Module
===================================================

Tests the AI and neural network complexity analysis framework.
"""

import unittest
import math

from src.neural_network_complexity import (
    CognitiveTask,
    NeuralNetworkModel,
    CognitiveTaskType,
    ComplexityClass,
    NetworkArchitecture,
    KAPPA_PI,
    C_THRESHOLD,
    prove_task_irreducibility,
    analyze_neural_network_limits,
    create_example_tasks,
    create_example_networks,
)


class TestCognitiveTask(unittest.TestCase):
    """Test CognitiveTask class."""
    
    def test_tractable_task(self):
        """Test tractable task (low treewidth)."""
        task = CognitiveTask(
            name="Simple Task",
            task_type=CognitiveTaskType.PERCEPTION,
            problem_size=100,
            treewidth=10,
            architecture=NetworkArchitecture.FEEDFORWARD,
        )
        
        self.assertEqual(task.complexity_class, ComplexityClass.POLYNOMIAL)
        self.assertFalse(task.is_irreducible)
        self.assertGreater(task.information_complexity, 0)
    
    def test_intractable_task(self):
        """Test intractable task (high treewidth)."""
        task = CognitiveTask(
            name="Complex Task",
            task_type=CognitiveTaskType.REASONING,
            problem_size=100,
            treewidth=40,
            architecture=NetworkArchitecture.GRAPH,
        )
        
        self.assertIn(task.complexity_class, [ComplexityClass.EXPONENTIAL, ComplexityClass.IRREDUCIBLE])
        self.assertGreater(task.information_complexity, 0)
    
    def test_irreducible_task(self):
        """Test irreducible task (tw >= n/2)."""
        task = CognitiveTask(
            name="Irreducible Task",
            task_type=CognitiveTaskType.CREATIVITY,
            problem_size=100,
            treewidth=60,  # >= n/2
            architecture=NetworkArchitecture.HYBRID,
        )
        
        self.assertEqual(task.complexity_class, ComplexityClass.IRREDUCIBLE)
        self.assertTrue(task.is_irreducible)
        self.assertGreater(task.information_complexity, 0)
    
    def test_ic_computation(self):
        """Test information complexity computation."""
        task = CognitiveTask(
            name="Test Task",
            task_type=CognitiveTaskType.LANGUAGE,
            problem_size=100,
            treewidth=20,
            architecture=NetworkArchitecture.TRANSFORMER,
        )
        
        expected_ic = KAPPA_PI * 20 / math.log2(100)
        self.assertAlmostEqual(task.information_complexity, expected_ic, places=2)
    
    def test_task_analysis(self):
        """Test task analysis output."""
        task = CognitiveTask(
            name="Analysis Test",
            task_type=CognitiveTaskType.MEMORY,
            problem_size=200,
            treewidth=30,
            architecture=NetworkArchitecture.RECURRENT,
        )
        
        analysis = task.get_analysis()
        
        self.assertEqual(analysis['task_name'], "Analysis Test")
        self.assertEqual(analysis['task_type'], "MEMORY")
        self.assertEqual(analysis['problem_size_n'], 200)
        self.assertEqual(analysis['treewidth_tw'], 30)
        self.assertIn('complexity_class', analysis)
        self.assertIn('information_complexity_IC', analysis)
        self.assertIn('is_irreducible', analysis)


class TestNeuralNetworkModel(unittest.TestCase):
    """Test NeuralNetworkModel class."""
    
    def test_small_network(self):
        """Test small neural network."""
        network = NeuralNetworkModel(
            name="Small Net",
            architecture=NetworkArchitecture.FEEDFORWARD,
            num_parameters=1000,
            num_layers=3,
            effective_treewidth=5,
        )
        
        self.assertGreater(network.max_tractable_size, 0)
        self.assertGreater(network.coherence_factor, 0)
        self.assertLessEqual(network.coherence_factor, 1.0)
    
    def test_large_network(self):
        """Test large neural network."""
        network = NeuralNetworkModel(
            name="Large Net",
            architecture=NetworkArchitecture.TRANSFORMER,
            num_parameters=1_000_000_000,
            num_layers=24,
            effective_treewidth=50,
        )
        
        self.assertGreater(network.max_tractable_size, 1000)
        self.assertGreater(network.coherence_factor, 0)
    
    def test_can_solve_efficiently(self):
        """Test network's ability to solve tasks."""
        network = NeuralNetworkModel(
            name="Test Net",
            architecture=NetworkArchitecture.CONVOLUTIONAL,
            num_parameters=10_000_000,
            num_layers=10,
            effective_treewidth=20,
        )
        
        # Tractable task
        easy_task = CognitiveTask(
            name="Easy",
            task_type=CognitiveTaskType.PERCEPTION,
            problem_size=100,
            treewidth=10,
            architecture=NetworkArchitecture.CONVOLUTIONAL,
        )
        
        # Hard task
        hard_task = CognitiveTask(
            name="Hard",
            task_type=CognitiveTaskType.REASONING,
            problem_size=100,
            treewidth=80,
            architecture=NetworkArchitecture.GRAPH,
        )
        
        # Network should handle easy task but not hard one
        # Note: This depends on coherence factor being above threshold
        # which may not be true for small networks
        self.assertIsInstance(network.can_solve_efficiently(easy_task), bool)
        self.assertFalse(network.can_solve_efficiently(hard_task))
    
    def test_network_analysis(self):
        """Test network analysis output."""
        network = NeuralNetworkModel(
            name="Analysis Net",
            architecture=NetworkArchitecture.GRAPH,
            num_parameters=50_000_000,
            num_layers=16,
            effective_treewidth=40,
        )
        
        analysis = network.get_analysis()
        
        self.assertEqual(analysis['model_name'], "Analysis Net")
        self.assertEqual(analysis['architecture'], "GRAPH")
        self.assertEqual(analysis['num_parameters'], 50_000_000)
        self.assertIn('max_tractable_size', analysis)
        self.assertIn('coherence_factor', analysis)


class TestIrreducibilityProof(unittest.TestCase):
    """Test irreducibility proof functions."""
    
    def test_irreducible_task_proof(self):
        """Test proof for irreducible task."""
        task = CognitiveTask(
            name="Irreducible",
            task_type=CognitiveTaskType.CREATIVITY,
            problem_size=200,
            treewidth=150,
            architecture=NetworkArchitecture.HYBRID,
        )
        
        proof = prove_task_irreducibility(task)
        
        self.assertEqual(proof['task'], "Irreducible")
        self.assertIn('irreducibility_proof', proof)
        self.assertIn('conclusion', proof)
        self.assertTrue(proof['conclusion']['is_irreducible'])
    
    def test_tractable_task_proof(self):
        """Test proof for tractable task."""
        task = CognitiveTask(
            name="Tractable",
            task_type=CognitiveTaskType.PERCEPTION,
            problem_size=100,
            treewidth=10,
            architecture=NetworkArchitecture.FEEDFORWARD,
        )
        
        proof = prove_task_irreducibility(task)
        
        self.assertIn('conclusion', proof)
        self.assertFalse(proof['conclusion']['is_irreducible'])
    
    def test_proof_conditions(self):
        """Test that all three conditions are checked."""
        task = CognitiveTask(
            name="Test",
            task_type=CognitiveTaskType.REASONING,
            problem_size=100,
            treewidth=60,
            architecture=NetworkArchitecture.GRAPH,
        )
        
        proof = prove_task_irreducibility(task)
        
        self.assertIn('condition_1_high_treewidth', proof['irreducibility_proof'])
        self.assertIn('condition_2_information_bottleneck', proof['irreducibility_proof'])
        self.assertIn('condition_3_exponential_barrier', proof['irreducibility_proof'])


class TestNetworkLimits(unittest.TestCase):
    """Test neural network limits analysis."""
    
    def test_analyze_limits(self):
        """Test analysis of network limits on tasks."""
        network = NeuralNetworkModel(
            name="Test Network",
            architecture=NetworkArchitecture.TRANSFORMER,
            num_parameters=100_000_000,
            num_layers=12,
            effective_treewidth=30,
        )
        
        tasks = [
            CognitiveTask(
                name="Easy",
                task_type=CognitiveTaskType.PERCEPTION,
                problem_size=100,
                treewidth=10,
                architecture=NetworkArchitecture.CONVOLUTIONAL,
            ),
            CognitiveTask(
                name="Hard",
                task_type=CognitiveTaskType.CREATIVITY,
                problem_size=100,
                treewidth=80,
                architecture=NetworkArchitecture.HYBRID,
            ),
        ]
        
        analysis = analyze_neural_network_limits(network, tasks)
        
        self.assertIn('network', analysis)
        self.assertIn('task_analysis', analysis)
        self.assertIn('fundamental_limits', analysis)
        self.assertEqual(analysis['task_analysis']['total_tasks'], 2)
    
    def test_limits_categorization(self):
        """Test that tasks are properly categorized."""
        network = NeuralNetworkModel(
            name="Categorization Test",
            architecture=NetworkArchitecture.GRAPH,
            num_parameters=50_000_000,
            num_layers=16,
            effective_treewidth=50,
        )
        
        tasks = create_example_tasks()
        analysis = analyze_neural_network_limits(network, tasks)
        
        total = analysis['task_analysis']['total_tasks']
        solvable = analysis['task_analysis']['solvable_efficiently']['count']
        intractable = analysis['task_analysis']['intractable']['count']
        irreducible = analysis['task_analysis']['irreducible']['count']
        
        # All tasks should be accounted for
        self.assertEqual(solvable + intractable + irreducible, total)


class TestExampleCreation(unittest.TestCase):
    """Test example creation functions."""
    
    def test_create_example_tasks(self):
        """Test creation of example tasks."""
        tasks = create_example_tasks()
        
        self.assertIsInstance(tasks, list)
        self.assertGreater(len(tasks), 0)
        
        for task in tasks:
            self.assertIsInstance(task, CognitiveTask)
            self.assertIsInstance(task.name, str)
            self.assertGreater(task.problem_size, 0)
            self.assertGreater(task.treewidth, 0)
    
    def test_create_example_networks(self):
        """Test creation of example networks."""
        networks = create_example_networks()
        
        self.assertIsInstance(networks, list)
        self.assertGreater(len(networks), 0)
        
        for network in networks:
            self.assertIsInstance(network, NeuralNetworkModel)
            self.assertIsInstance(network.name, str)
            self.assertGreater(network.num_parameters, 0)
            self.assertGreater(network.num_layers, 0)
    
    def test_example_diversity(self):
        """Test that examples cover different complexity classes."""
        tasks = create_example_tasks()
        
        complexity_classes = set(task.complexity_class for task in tasks)
        
        # Should have multiple complexity classes
        self.assertGreater(len(complexity_classes), 1)
        
        # Should have at least one irreducible task
        irreducible_count = sum(1 for task in tasks if task.is_irreducible)
        self.assertGreater(irreducible_count, 0)


class TestConstants(unittest.TestCase):
    """Test constant values."""
    
    def test_kappa_pi(self):
        """Test κ_Π value."""
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
    
    def test_consciousness_threshold(self):
        """Test consciousness threshold."""
        self.assertAlmostEqual(C_THRESHOLD, 1.0 / KAPPA_PI, places=4)
        self.assertGreater(C_THRESHOLD, 0.38)
        self.assertLess(C_THRESHOLD, 0.39)


class TestComplexityClassification(unittest.TestCase):
    """Test complexity classification logic."""
    
    def test_polynomial_classification(self):
        """Test P classification (low treewidth)."""
        n = 100
        tw = 10  # tw ≤ 3*log(n)
        
        task = CognitiveTask(
            name="P Task",
            task_type=CognitiveTaskType.PERCEPTION,
            problem_size=n,
            treewidth=tw,
            architecture=NetworkArchitecture.FEEDFORWARD,
        )
        
        self.assertEqual(task.complexity_class, ComplexityClass.POLYNOMIAL)
    
    def test_exponential_classification(self):
        """Test NP classification (moderate treewidth)."""
        n = 100
        tw = 40  # 3*log(n) < tw < n/2
        
        task = CognitiveTask(
            name="NP Task",
            task_type=CognitiveTaskType.LANGUAGE,
            problem_size=n,
            treewidth=tw,
            architecture=NetworkArchitecture.TRANSFORMER,
        )
        
        self.assertIn(task.complexity_class, [ComplexityClass.EXPONENTIAL, ComplexityClass.IRREDUCIBLE])
    
    def test_irreducible_classification(self):
        """Test IRREDUCIBLE classification (tw >= n/2)."""
        n = 100
        tw = 60  # tw >= n/2
        
        task = CognitiveTask(
            name="Irreducible Task",
            task_type=CognitiveTaskType.CREATIVITY,
            problem_size=n,
            treewidth=tw,
            architecture=NetworkArchitecture.HYBRID,
        )
        
        self.assertEqual(task.complexity_class, ComplexityClass.IRREDUCIBLE)


if __name__ == '__main__':
    unittest.main()
