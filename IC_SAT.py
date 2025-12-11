#!/usr/bin/env python3
"""
IC_SAT.py - Structural SAT solver with treewidth constraints

This is a wrapper/alias for the main IC-SAT implementation.
The actual implementation is in src/ic_sat.py
"""

import sys
import os

# Add src directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

# Import the main IC-SAT module
from ic_sat import *

if __name__ == '__main__':
    # Run the main IC-SAT solver
    from ic_sat import main
    main()
