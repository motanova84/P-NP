#!/usr/bin/env python3
"""
Test vercel.json configuration validity.

This test ensures that the Vercel configuration follows the rules:
- If rewrites, redirects, headers, cleanUrls or trailingSlash are used,
  then routes cannot be present (routes is legacy and incompatible).
"""

import json
import os


def test_vercel_config_no_routes_with_modern_properties():
    """
    Verify that vercel.json does not use the legacy 'routes' property
    when modern properties like 'headers', 'rewrites', etc. are present.
    """
    # Load vercel.json
    vercel_path = os.path.join(
        os.path.dirname(os.path.dirname(__file__)),
        'vercel.json'
    )
    
    with open(vercel_path, 'r') as f:
        config = json.load(f)
    
    # Modern properties that conflict with legacy 'routes'
    modern_properties = ['rewrites', 'redirects', 'headers', 'cleanUrls', 'trailingSlash']
    
    # Check if any modern properties are present
    has_modern_properties = any(prop in config for prop in modern_properties)
    
    # Check if legacy routes is present
    has_routes = 'routes' in config
    
    # Assert that we don't have both
    if has_modern_properties:
        assert not has_routes, (
            "vercel.json cannot have 'routes' property when using modern "
            "properties like 'rewrites', 'redirects', 'headers', 'cleanUrls', "
            "or 'trailingSlash'"
        )
    
    print("✓ vercel.json configuration is valid")


def test_vercel_config_valid_json():
    """Verify that vercel.json is valid JSON."""
    vercel_path = os.path.join(
        os.path.dirname(os.path.dirname(__file__)),
        'vercel.json'
    )
    
    with open(vercel_path, 'r') as f:
        config = json.load(f)
    
    assert isinstance(config, dict), "vercel.json should contain a JSON object"
    print("✓ vercel.json is valid JSON")


def test_vercel_config_has_rewrites():
    """Verify that vercel.json has rewrites configured correctly."""
    vercel_path = os.path.join(
        os.path.dirname(os.path.dirname(__file__)),
        'vercel.json'
    )
    
    with open(vercel_path, 'r') as f:
        config = json.load(f)
    
    # Check if rewrites exist
    assert 'rewrites' in config, "vercel.json should have 'rewrites' property"
    
    # Verify rewrites structure
    rewrites = config['rewrites']
    assert isinstance(rewrites, list), "'rewrites' should be a list"
    
    for rewrite in rewrites:
        assert 'source' in rewrite, "Each rewrite must have a 'source' field"
        assert 'destination' in rewrite, "Each rewrite must have a 'destination' field"
    
    print(f"✓ vercel.json has {len(rewrites)} rewrites configured correctly")


if __name__ == '__main__':
    test_vercel_config_valid_json()
    test_vercel_config_no_routes_with_modern_properties()
    test_vercel_config_has_rewrites()
    print("\nAll vercel.json tests passed!")
