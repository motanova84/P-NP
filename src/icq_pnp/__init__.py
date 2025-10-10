"""
ICQ P-NP Framework
==================

A verifiable framework for analyzing the P vs NP problem through treewidth
and information complexity.

Author: José Manuel Mota Burruezo · Instituto de Conciencia Cuántica (ICQ)
Frecuencia de resonancia: 141.7001 Hz
"""

__version__ = "0.1.0"
__author__ = "José Manuel Mota Burruezo"

from .computational_dichotomy import (
    CNFFormula, 
    generate_low_treewidth_formula, 
    demonstrate_dichotomy,
    ic_sat_validate,
    save_results,
    plot_scaling
)
from .tseitin_generator import (
    TseitinGenerator, 
    generate_expander_tseitin,
    generate_margulis_gabber_galil_expander,
    generate_tseitin_formula
)

__all__ = [
    "CNFFormula",
    "generate_low_treewidth_formula",
    "demonstrate_dichotomy",
    "ic_sat_validate",
    "save_results",
    "plot_scaling",
    "TseitinGenerator",
    "generate_expander_tseitin",
    "generate_margulis_gabber_galil_expander",
    "generate_tseitin_formula",
]
