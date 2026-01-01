#!/usr/bin/env python3
"""
Test vercel.json configuration validity.

This test ensures that the Vercel configuration follows the rules:
- If rewrites, redirects, headers, cleanUrls or trailingSlash are used,
  then routes cannot be present (routes is legacy and incompatible).
"""

import json
import os
import unittest


class TestVercelConfig(unittest.TestCase):
    """Test cases for vercel.json configuration validation."""
    
    @classmethod
    def setUpClass(cls):
        """Load vercel.json once for all tests."""
        cls.vercel_path = os.path.join(
            os.path.dirname(os.path.dirname(__file__)),
            'vercel.json'
        )
        
        with open(cls.vercel_path, 'r') as f:
            cls.config = json.load(f)
    
    def test_vercel_config_valid_json(self):
        """Verify that vercel.json is valid JSON."""
        self.assertIsInstance(self.config, dict, 
                            "vercel.json should contain a JSON object")
    
    def test_vercel_config_no_routes_with_modern_properties(self):
        """
        Verify that vercel.json does not use the legacy 'routes' property
        when modern properties like 'headers', 'rewrites', etc. are present.
        """
        # Modern properties that conflict with legacy 'routes'
        modern_properties = ['rewrites', 'redirects', 'headers', 'cleanUrls', 'trailingSlash']
        
        # Check if any modern properties are present
        has_modern_properties = any(prop in self.config for prop in modern_properties)
        
        # Check if legacy routes is present
        has_routes = 'routes' in self.config
        
        # Assert that we don't have both
        if has_modern_properties:
            self.assertFalse(has_routes,
                "vercel.json cannot have 'routes' property when using modern "
                "properties like 'rewrites', 'redirects', 'headers', 'cleanUrls', "
                "or 'trailingSlash'"
            )
    
    def test_vercel_config_has_rewrites(self):
        """Verify that vercel.json has rewrites configured correctly."""
        # Check if rewrites exist
        self.assertIn('rewrites', self.config, 
                     "vercel.json should have 'rewrites' property")
        
        # Verify rewrites structure
        rewrites = self.config['rewrites']
        self.assertIsInstance(rewrites, list, "'rewrites' should be a list")
        
        for rewrite in rewrites:
            self.assertIn('source', rewrite, 
                         "Each rewrite must have a 'source' field")
            self.assertIn('destination', rewrite, 
                         "Each rewrite must have a 'destination' field")


if __name__ == '__main__':
    unittest.main()
