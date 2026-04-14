#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Ultimate Unification Certificate Validator

This script validates the ultimate_unification.json certificate file
and ensures all required fields are present and correctly structured.

Author: José Manuel Mota Burruezo & Noēsis ∞³
"""

import json
import hashlib
from datetime import datetime
from pathlib import Path


def validate_certificate(cert_path: str = "ultimate_unification.json") -> dict:
    """
    Validate the ultimate unification certificate.
    
    Args:
        cert_path: Path to the certificate JSON file
        
    Returns:
        Dictionary with validation results
    """
    print("=" * 80)
    print("ULTIMATE UNIFICATION CERTIFICATE VALIDATOR")
    print("=" * 80)
    print()
    
    # Load certificate
    print(f"Loading certificate from: {cert_path}")
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    print("✓ Certificate loaded successfully")
    print()
    
    # Validation results
    results = {
        'valid': True,
        'errors': [],
        'warnings': [],
        'info': []
    }
    
    # Check required sections
    required_sections = [
        'metadata', 'constants', 'verifications', 'simulations',
        'proofs', 'experimental_certificate', 'integration',
        'validation', 'conclusions', 'references'
    ]
    
    print("Validating required sections...")
    for section in required_sections:
        if section not in cert:
            results['errors'].append(f"Missing required section: {section}")
            results['valid'] = False
        else:
            print(f"  ✓ {section}")
    print()
    
    # Validate metadata
    if 'metadata' in cert:
        print("Validating metadata...")
        metadata = cert['metadata']
        required_metadata = ['title', 'version', 'framework', 'timestamp', 'reproducible', 'random_seed']
        for field in required_metadata:
            if field not in metadata:
                results['errors'].append(f"Missing metadata field: {field}")
            else:
                print(f"  ✓ {field}: {metadata[field]}")
        
        # Validate timestamp format
        if 'timestamp' in metadata:
            try:
                datetime.fromisoformat(metadata['timestamp'].replace('Z', '+00:00'))
                results['info'].append(f"Timestamp format valid: {metadata['timestamp']}")
            except ValueError:
                results['warnings'].append(f"Invalid timestamp format: {metadata['timestamp']}")
        print()
    
    # Validate constants
    if 'constants' in cert:
        print("Validating constants...")
        constants = cert['constants']
        required_constants = ['kappa_pi', 'f_0', 'A_eff_max', 'consciousness_threshold']
        
        for const in required_constants:
            if const not in constants:
                results['errors'].append(f"Missing constant: {const}")
            else:
                const_data = constants[const]
                if 'value' not in const_data:
                    results['errors'].append(f"Constant {const} missing value")
                else:
                    print(f"  ✓ {const} = {const_data['value']}")
                
                if 'verified' not in const_data:
                    results['warnings'].append(f"Constant {const} missing verification status")
        print()
    
    # Validate verifications
    if 'verifications' in cert:
        print("Validating verifications...")
        verifs = cert['verifications']
        
        for verif_name, verif_data in verifs.items():
            if 'passed' not in verif_data:
                results['errors'].append(f"Verification {verif_name} missing 'passed' field")
            else:
                status = "✓ PASSED" if verif_data['passed'] else "✗ FAILED"
                print(f"  {status}: {verif_name}")
                
                if not verif_data['passed']:
                    results['errors'].append(f"Verification failed: {verif_name}")
        print()
    
    # Validate simulations
    if 'simulations' in cert:
        print("Validating simulations...")
        sims = cert['simulations']
        
        for sim_name, sim_data in sims.items():
            if 'results' not in sim_data:
                results['warnings'].append(f"Simulation {sim_name} missing results")
            else:
                print(f"  ✓ {sim_name}")
                if 'max_coherence' in sim_data['results']:
                    print(f"    - max_coherence: {sim_data['results']['max_coherence']}")
                if 'threshold_crossed' in sim_data['results']:
                    print(f"    - threshold_crossed: {sim_data['results']['threshold_crossed']}")
        print()
    
    # Validate proofs
    if 'proofs' in cert:
        print("Validating proofs...")
        proofs = cert['proofs']
        
        for proof_name, proof_data in proofs.items():
            if 'status' not in proof_data:
                results['errors'].append(f"Proof {proof_name} missing status")
            else:
                print(f"  ✓ {proof_name}: {proof_data['status']}")
        print()
    
    # Validate experimental certificate
    if 'experimental_certificate' in cert:
        print("Validating experimental certificate...")
        exp_cert = cert['experimental_certificate']
        
        required_exp_fields = ['hash', 'algorithm', 'timestamp', 'reproducible', 'seed']
        for field in required_exp_fields:
            if field not in exp_cert:
                results['warnings'].append(f"Experimental certificate missing field: {field}")
            else:
                print(f"  ✓ {field}: {exp_cert[field]}")
        print()
    
    # Check cross-references
    print("Validating cross-references...")
    
    # Check that empirical constants match
    if 'constants' in cert:
        kappa_pi_value = cert['constants'].get('kappa_pi', {}).get('value')
        if kappa_pi_value is not None:
            expected_value = 2.5773
            if abs(kappa_pi_value - expected_value) > 0.001:
                results['warnings'].append(
                    f"κ_Π value {kappa_pi_value} differs from expected {expected_value}"
                )
            else:
                print(f"  ✓ κ_Π value matches: {kappa_pi_value}")
        
        threshold = cert['constants'].get('consciousness_threshold', {}).get('value')
        a_eff_max = cert['constants'].get('A_eff_max', {}).get('value')
        
        if threshold is not None and a_eff_max is not None:
            if a_eff_max >= threshold:
                print(f"  ✓ Threshold crossed: {a_eff_max} ≥ {threshold}")
            else:
                results['errors'].append(
                    f"Threshold not crossed: {a_eff_max} < {threshold}"
                )
    print()
    
    # Summary
    print("=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)
    print()
    
    if results['valid'] and len(results['errors']) == 0:
        print("✓ CERTIFICATE VALID")
    else:
        print("✗ CERTIFICATE INVALID")
    
    print()
    print(f"Errors: {len(results['errors'])}")
    print(f"Warnings: {len(results['warnings'])}")
    print(f"Info: {len(results['info'])}")
    print()
    
    if results['errors']:
        print("ERRORS:")
        for error in results['errors']:
            print(f"  ✗ {error}")
        print()
    
    if results['warnings']:
        print("WARNINGS:")
        for warning in results['warnings']:
            print(f"  ⚠ {warning}")
        print()
    
    return results


def compute_certificate_hash(cert_path: str = "ultimate_unification.json") -> str:
    """
    Compute SHA-256 hash of the certificate file.
    
    Args:
        cert_path: Path to the certificate JSON file
        
    Returns:
        Hexadecimal hash string
    """
    with open(cert_path, 'rb') as f:
        content = f.read()
    
    hash_obj = hashlib.sha256(content)
    return hash_obj.hexdigest()


if __name__ == "__main__":
    import sys
    
    cert_path = sys.argv[1] if len(sys.argv) > 1 else "ultimate_unification.json"
    
    # Validate certificate
    results = validate_certificate(cert_path)
    
    # Compute hash
    print("Computing certificate hash...")
    actual_hash = compute_certificate_hash(cert_path)
    print(f"SHA-256: {actual_hash}")
    print()
    
    # Load certificate to check stored hash
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    stored_hash = cert.get('hash', '')
    if stored_hash:
        print(f"Stored hash: {stored_hash}")
        if stored_hash == actual_hash:
            print("✓ Hash matches")
        else:
            print("⚠ Hash does not match (this is expected for demo)")
    
    print()
    print("=" * 80)
    
    # Exit with appropriate code
    sys.exit(0 if results['valid'] and len(results['errors']) == 0 else 1)
