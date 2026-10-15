"""
Unit tests for Gap2_IC_TimeLowerBound.lean structure validation

These tests validate that the Gap2 file exists, has correct structure,
and contains the required theorems and definitions.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
"""

import unittest
import os
import re


class TestGap2Structure(unittest.TestCase):
    """Test cases for Gap2_IC_TimeLowerBound structure."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = os.path.join(os.path.dirname(__file__), '..')
        self.gap2_file = os.path.join(self.repo_root, 'Gap2_IC_TimeLowerBound.lean')
    
    def test_gap2_file_exists(self):
        """Test that Gap2_IC_TimeLowerBound.lean exists."""
        self.assertTrue(os.path.exists(self.gap2_file),
                       f"Gap2_IC_TimeLowerBound.lean not found at {self.gap2_file}")
    
    def test_gap2_has_proper_imports(self):
        """Test that Gap2 has proper Mathlib imports."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_imports = [
            'import Mathlib.Combinatorics.SimpleGraph.Basic',
            'import Mathlib.Data.Finset.Basic',
            'import Mathlib.Data.Real.Basic',
            'import Mathlib.Analysis.SpecialFunctions.Pow.Real'
        ]
        
        for imp in required_imports:
            self.assertIn(imp, content,
                         f"Required import '{imp}' not found in Gap2_IC_TimeLowerBound.lean")
    
    def test_gap2_no_duplicate_imports(self):
        """Test that there are no duplicate import sections."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check that imports section appears only once
        import_sections = re.findall(r'import Mathlib\.Combinatorics\.SimpleGraph\.Basic', content)
        self.assertEqual(len(import_sections), 1,
                        "Duplicate import section found in Gap2_IC_TimeLowerBound.lean")
    
    def test_information_complexity_defined(self):
        """Test that InformationComplexity is defined."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('def InformationComplexity', content,
                     "InformationComplexity definition not found")
        self.assertIn('notation:max "IC("', content,
                     "IC notation not found")
    
    def test_is_expander_structure_defined(self):
        """Test that IsExpander structure is defined."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('structure IsExpander', content,
                     "IsExpander structure not found")
        self.assertIn('regular :', content,
                     "IsExpander.regular field not found")
        self.assertIn('expansion :', content,
                     "IsExpander.expansion field not found")
    
    def test_tseitin_encoding_structure_defined(self):
        """Test that TseitinEncoding structure is defined."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('structure TseitinEncoding', content,
                     "TseitinEncoding structure not found")
        self.assertIn('edge_vars :', content,
                     "TseitinEncoding.edge_vars field not found")
        self.assertIn('vertex_clauses :', content,
                     "TseitinEncoding.vertex_clauses field not found")
    
    def test_algorithm_structure_defined(self):
        """Test that Algorithm structure is defined."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('structure Algorithm', content,
                     "Algorithm structure not found")
        self.assertIn('time_complexity :', content,
                     "Algorithm.time_complexity field not found")
    
    def test_communication_protocol_structure_defined(self):
        """Test that CommunicationProtocol structure is defined."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('structure CommunicationProtocol', content,
                     "CommunicationProtocol structure not found")
        self.assertIn('communication_cost :', content,
                     "CommunicationProtocol.communication_cost field not found")
    
    def test_main_theorem_defined(self):
        """Test that the main theorem information_complexity_lower_bound_time is defined."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('theorem information_complexity_lower_bound_time', content,
                     "Main theorem information_complexity_lower_bound_time not found")
        self.assertIn('IC(G, S) ≥ α', content,
                     "IC hypothesis not found in main theorem")
        self.assertIn('Time(G) ≥ 2 ^ α', content,
                     "Time conclusion not found in main theorem")
    
    def test_kappa_pi_constant_defined(self):
        """Test that KAPPA_PI constant is defined."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('def KAPPA_PI', content,
                     "KAPPA_PI constant not found")
        self.assertIn('2.5773', content,
                     "KAPPA_PI value not found")
    
    def test_key_theorems_present(self):
        """Test that key theorems are present."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        key_theorems = [
            'theorem ic_monotone_in_components',
            'theorem ic_subadditive',
            'theorem ic_expander_lower_bound',
            'theorem protocol_communication_lower_bound',
            'theorem tseitin_expander_exponential_time',
            'theorem kappa_pi_threshold_theorem',
            'theorem yao_minimax_lemma',
            'theorem karchmer_wigderson',
            'theorem complete_chain_tw_to_time'
        ]
        
        for theorem in key_theorems:
            self.assertIn(theorem, content,
                         f"Key theorem '{theorem}' not found in Gap2_IC_TimeLowerBound.lean")
    
    def test_file_has_proper_sections(self):
        """Test that file has properly organized sections."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        sections = [
            'PARTE 1: DEFINICIONES FUNDAMENTALES',
            'PARTE 2: PROPIEDADES DE LA COMPLEJIDAD DE INFORMACIÓN',
            'PARTE 3: MODELO COMPUTACIONAL',
            'PARTE 4: REDUCCIÓN DE GRAFOS A PROBLEMAS DE COMUNICACIÓN',
            'PARTE 5: CODIFICACIÓN TSEITIN SOBRE EXPANSORES',
            'PARTE 6: TEOREMA PRINCIPAL - IC → TIEMPO EXPONENCIAL',
            'PARTE 7: COROLARIOS Y APLICACIONES',
            'PARTE 8: LEMAS AUXILIARES CRÍTICOS',
            'PARTE 9: INTEGRACIÓN CON GAP 1',
            'PARTE 10: VERIFICACIÓN Y TESTS'
        ]
        
        for section in sections:
            self.assertIn(section, content,
                         f"Section '{section}' not found in Gap2_IC_TimeLowerBound.lean")
    
    def test_examples_present(self):
        """Test that example tests are present."""
        with open(self.gap2_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Should have at least 3 example tests
        example_count = content.count('example :')
        self.assertGreaterEqual(example_count, 3,
                               f"Expected at least 3 example tests, found {example_count}")


class TestGap2TestFile(unittest.TestCase):
    """Test cases for Gap2Tests.lean file."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = os.path.join(os.path.dirname(__file__), '..')
        self.gap2_test_file = os.path.join(self.repo_root, 'tests', 'Gap2Tests.lean')
    
    def test_gap2_test_file_exists(self):
        """Test that Gap2Tests.lean exists."""
        self.assertTrue(os.path.exists(self.gap2_test_file),
                       f"Gap2Tests.lean not found at {self.gap2_test_file}")
    
    def test_gap2_test_imports_module(self):
        """Test that Gap2Tests imports the Gap2 module."""
        with open(self.gap2_test_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('import Gap2_IC_TimeLowerBound', content,
                     "Gap2Tests.lean does not import Gap2_IC_TimeLowerBound")
    
    def test_gap2_test_has_examples(self):
        """Test that Gap2Tests has example proofs."""
        with open(self.gap2_test_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        example_count = content.count('example :')
        self.assertGreaterEqual(example_count, 3,
                               f"Expected at least 3 examples in Gap2Tests, found {example_count}")


class TestLakefileIntegration(unittest.TestCase):
    """Test cases for lakefile.lean integration."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = os.path.join(os.path.dirname(__file__), '..')
        self.lakefile = os.path.join(self.repo_root, 'lakefile.lean')
    
    def test_lakefile_includes_gap2(self):
        """Test that lakefile.lean includes Gap2_IC_TimeLowerBound."""
        with open(self.lakefile, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn('lean_lib Gap2_IC_TimeLowerBound', content,
                     "lakefile.lean does not include Gap2_IC_TimeLowerBound library")
        self.assertIn('roots := #[`Gap2_IC_TimeLowerBound]', content,
                     "Gap2_IC_TimeLowerBound roots not configured correctly")


if __name__ == '__main__':
    unittest.main()
