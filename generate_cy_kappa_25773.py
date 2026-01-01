#!/usr/bin/env python3
"""
Generate Calabi-Yau varieties with h11 + h21 = 13

This script generates Calabi-Yau varieties where the sum of Hodge numbers
h11 + h21 equals 13, and exports the data to JSON format.

For each variety:
- ID: Unique identifier in format CY_{h11}_{h21}
- h11, h21: Hodge numbers
- chi_Euler: Euler characteristic = 2*(h11 - h21)
- kappa_pi: Constant value log(13) ≈ 2.564949

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: 1 enero 2026
"""

import json
import numpy as np
import os

def generate_cy_varieties_n13():
    """
    Generate Calabi-Yau varieties with h11 + h21 = 13.
    
    Returns:
        list: List of dictionaries containing CY variety data
    """
    cy_kappa_25773 = []
    target_N = 13
    
    # Calculate kappa_pi once (log(13) is constant for all varieties)
    kappa_pi = round(np.log(target_N), 6)  # log(13) ≈ 2.564949
    
    # Filter CY varieties with h11 + h21 = 13
    # h11 ranges from 1 to 12 (h21 must be at least 1)
    for h11 in range(1, target_N):
        h21 = target_N - h11
        chi = 2 * (h11 - h21)
        
        cy_kappa_25773.append({
            "ID": f"CY_{h11}_{h21}",
            "h11": h11,
            "h21": h21,
            "chi_Euler": chi,
            "kappa_pi": kappa_pi
        })
    
    return cy_kappa_25773


def export_to_json(data, output_dir=".", filename="cy_kappa_25773_log13.json"):
    """
    Export CY varieties data to JSON file.
    
    Args:
        data: List of CY variety dictionaries
        output_dir: Output directory path (default: current directory)
        filename: Output filename (default: cy_kappa_25773_log13.json)
    
    Returns:
        str: Path to the created JSON file
    """
    # Ensure output directory exists
    os.makedirs(output_dir, exist_ok=True)
    
    json_path = os.path.join(output_dir, filename)
    
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    
    return json_path


def main():
    """Main execution function."""
    print("=" * 70)
    print("  Generación de Variedades Calabi-Yau con h11 + h21 = 13")
    print("=" * 70)
    print()
    
    # Generate CY varieties
    print("Generando variedades Calabi-Yau...")
    cy_varieties = generate_cy_varieties_n13()
    
    print(f"✓ Generadas {len(cy_varieties)} variedades")
    print()
    
    # Display first few examples
    print("Ejemplos de variedades generadas:")
    print("-" * 70)
    for cy in cy_varieties[:3]:
        print(f"  {cy['ID']:12s}: h11={cy['h11']:2d}, h21={cy['h21']:2d}, "
              f"χ={cy['chi_Euler']:3d}, κ_Π={cy['kappa_pi']:.6f}")
    if len(cy_varieties) > 3:
        print(f"  ... ({len(cy_varieties) - 3} más)")
    print()
    
    # Export to JSON (use relative path for portability)
    output_dir = "results"
    json_path = export_to_json(cy_varieties, output_dir=output_dir)
    
    print(f"✓ Archivo JSON generado: {json_path}")
    print()
    
    # Display file info
    file_size = os.path.getsize(json_path)
    print("Información del archivo:")
    print(f"  Ruta: {json_path}")
    print(f"  Tamaño: {file_size} bytes")
    print(f"  Variedades: {len(cy_varieties)}")
    print()
    
    # Display summary
    print("Resumen:")
    print(f"  Condición: h11 + h21 = 13")
    print(f"  Fórmula χ: χ = 2(h11 - h21)")
    print(f"  Constante κ_Π: log(13) ≈ {cy_varieties[0]['kappa_pi']}")
    print()
    
    print("=" * 70)
    print("  ✓ GENERACIÓN COMPLETADA")
    print("=" * 70)
    
    return json_path


if __name__ == "__main__":
    result_path = main()
    print(f"\nResultado: {result_path}")
