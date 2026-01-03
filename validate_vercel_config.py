#!/usr/bin/env python3
"""
validate_vercel_config.py - Validate Vercel Configuration

This script validates that the vercel.json configuration follows Vercel's rules:
- If rewrites, redirects, headers, cleanUrls or trailingSlash are used,
  then routes cannot be present (routes is legacy and incompatible).

Usage:
    python validate_vercel_config.py
    
© JMMB | P vs NP Verification System
"""

import json
import os
import sys


# Modern properties that conflict with legacy 'routes'
MODERN_PROPERTIES = ['rewrites', 'redirects', 'headers', 'cleanUrls', 'trailingSlash']


def validate_vercel_config(config_path='vercel.json'):
    """
    Validate that vercel.json does not use the legacy 'routes' property
    when modern properties like 'headers', 'rewrites', etc. are present.
    
    Args:
        config_path: Path to the vercel.json file
        
    Returns:
        tuple: (is_valid, error_message, config_dict)
    """
    # Check if file exists
    if not os.path.exists(config_path):
        return False, f"Configuration file not found: {config_path}", None
    
    # Load vercel.json
    try:
        with open(config_path, 'r') as f:
            config = json.load(f)
    except json.JSONDecodeError as e:
        return False, f"Invalid JSON in {config_path}: {e}", None
    except Exception as e:
        return False, f"Error reading {config_path}: {e}", None
    
    # Verify it's a dictionary
    if not isinstance(config, dict):
        return False, "Configuration must be a JSON object", None
    
    # Check if any modern properties are present
    present_modern_properties = [prop for prop in MODERN_PROPERTIES if prop in config]
    
    # Check if legacy routes is present
    has_routes = 'routes' in config
    
    # Validate the constraint
    if present_modern_properties and has_routes:
        return False, (
            f"Configuration error: 'routes' property cannot be used with modern "
            f"properties. Found 'routes' together with: {', '.join(present_modern_properties)}. "
            f"Please remove 'routes' and use the modern routing properties instead."
        ), config
    
    return True, "Configuration is valid", config


def main():
    """Run validation and report results."""
    print()
    print("=" * 80)
    print("VERCEL CONFIGURATION VALIDATION")
    print("=" * 80)
    print()
    
    # Determine the path to vercel.json
    script_dir = os.path.dirname(os.path.abspath(__file__))
    config_path = os.path.join(script_dir, 'vercel.json')
    
    print(f"Validating: {config_path}")
    print()
    
    # Run validation (returns config to avoid re-reading)
    is_valid, message, config = validate_vercel_config(config_path)
    
    if is_valid:
        print("✓ SUCCESS")
        print("-" * 80)
        print(message)
        print()
        
        # Display config summary (config already loaded from validation)
        print("Configuration Summary:")
        print("-" * 80)
        
        # List present properties
        present_props = [prop for prop in MODERN_PROPERTIES if prop in config]
        
        if present_props:
            print(f"Modern properties in use: {', '.join(present_props)}")
        else:
            print("No modern routing properties found")
            
        if 'routes' in config:
            print("Legacy 'routes' property: PRESENT")
        else:
            print("Legacy 'routes' property: Not present (good)")
        
        print()
        print("=" * 80)
        print()
        return 0
    else:
        print("✗ VALIDATION FAILED")
        print("-" * 80)
        print(message)
        print()
        print("=" * 80)
        print()
        return 1


if __name__ == '__main__':
    sys.exit(main())
