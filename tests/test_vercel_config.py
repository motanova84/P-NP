#!/usr/bin/env python3
"""
Test vercel.json configuration validity.

This test ensures that the Vercel configuration follows the rules:
- If rewrites, redirects, headers, cleanUrls or trailingSlash are used,
  then routes cannot be present (routes is legacy and incompatible).
"""

import json
import os
import sys
import tempfile
import unittest

# Import the constant and function from the validation module
sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))
from validate_vercel_config import MODERN_PROPERTIES, validate_vercel_config


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
        # Check if any modern properties are present
        has_modern_properties = any(prop in self.config for prop in MODERN_PROPERTIES)
        
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


class TestValidateVercelConfigFunction(unittest.TestCase):
    """Test cases for the validate_vercel_config function itself."""
    
    def test_validate_missing_file(self):
        """Test validation with a non-existent file."""
        # Use tempfile to get a non-existent path that's guaranteed to be portable
        temp_dir = tempfile.gettempdir()
        nonexistent_file = os.path.join(temp_dir, 'nonexistent_vercel_12345.json')
        
        is_valid, message, config = validate_vercel_config(nonexistent_file)
        self.assertFalse(is_valid)
        self.assertIn("not found", message)
        self.assertIsNone(config)
    
    def test_validate_invalid_json(self):
        """Test validation with invalid JSON."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            f.write("{ invalid json }")
            temp_file = f.name
        
        try:
            is_valid, message, config = validate_vercel_config(temp_file)
            self.assertFalse(is_valid)
            self.assertIn("Invalid JSON", message)
            self.assertIsNone(config)
        finally:
            os.unlink(temp_file)
    
    def test_validate_non_object_json(self):
        """Test validation with JSON that's not an object."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(["array", "not", "object"], f)
            temp_file = f.name
        
        try:
            is_valid, message, config = validate_vercel_config(temp_file)
            self.assertFalse(is_valid)
            self.assertIn("must be a JSON object", message)
            self.assertIsNone(config)
        finally:
            os.unlink(temp_file)
    
    def test_validate_routes_with_rewrites(self):
        """Test validation fails when routes is used with rewrites."""
        config_data = {
            "version": 2,
            "routes": [{"src": "/old", "dest": "/new"}],
            "rewrites": [{"source": "/test", "destination": "/index.html"}]
        }
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(config_data, f)
            temp_file = f.name
        
        try:
            is_valid, message, config = validate_vercel_config(temp_file)
            self.assertFalse(is_valid)
            self.assertIn("routes", message)
            self.assertIn("rewrites", message)
            self.assertIsNotNone(config)
        finally:
            os.unlink(temp_file)
    
    def test_validate_routes_with_headers(self):
        """Test validation fails when routes is used with headers."""
        config_data = {
            "version": 2,
            "routes": [{"src": "/old", "dest": "/new"}],
            "headers": [{"source": "/(.*)", "headers": [{"key": "X-Test", "value": "test"}]}]
        }
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(config_data, f)
            temp_file = f.name
        
        try:
            is_valid, message, config = validate_vercel_config(temp_file)
            self.assertFalse(is_valid)
            self.assertIn("routes", message)
            self.assertIn("headers", message)
        finally:
            os.unlink(temp_file)
    
    def test_validate_routes_only(self):
        """Test validation succeeds with only routes (legacy)."""
        config_data = {
            "version": 2,
            "routes": [{"src": "/old", "dest": "/new"}]
        }
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(config_data, f)
            temp_file = f.name
        
        try:
            is_valid, message, config = validate_vercel_config(temp_file)
            self.assertTrue(is_valid)
            self.assertIn("valid", message.lower())
            self.assertIsNotNone(config)
        finally:
            os.unlink(temp_file)
    
    def test_validate_modern_properties_only(self):
        """Test validation succeeds with only modern properties."""
        config_data = {
            "version": 2,
            "rewrites": [{"source": "/test", "destination": "/index.html"}],
            "headers": [{"source": "/(.*)", "headers": [{"key": "X-Test", "value": "test"}]}]
        }
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(config_data, f)
            temp_file = f.name
        
        try:
            is_valid, message, config = validate_vercel_config(temp_file)
            self.assertTrue(is_valid)
            self.assertIn("valid", message.lower())
            self.assertIsNotNone(config)
        finally:
            os.unlink(temp_file)
    
    def test_validate_no_routing_properties(self):
        """Test validation succeeds with no routing properties."""
        config_data = {
            "version": 2,
            "name": "test-project"
        }
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(config_data, f)
            temp_file = f.name
        
        try:
            is_valid, message, config = validate_vercel_config(temp_file)
            self.assertTrue(is_valid)
            self.assertIsNotNone(config)
        finally:
            os.unlink(temp_file)
    
    def test_validate_all_modern_properties_with_routes(self):
        """Test validation fails when routes is used with all modern properties."""
        config_data = {
            "version": 2,
            "routes": [{"src": "/old", "dest": "/new"}],
            "rewrites": [{"source": "/test", "destination": "/index.html"}],
            "redirects": [{"source": "/old", "destination": "/new"}],
            "headers": [{"source": "/(.*)", "headers": []}],
            "cleanUrls": True,
            "trailingSlash": False
        }
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(config_data, f)
            temp_file = f.name
        
        try:
            is_valid, message, config = validate_vercel_config(temp_file)
            self.assertFalse(is_valid)
            self.assertIn("routes", message)
            # Should mention at least some of the modern properties
            modern_props_found = sum(1 for prop in MODERN_PROPERTIES if prop in message)
            self.assertGreater(modern_props_found, 0)
        finally:
            os.unlink(temp_file)
