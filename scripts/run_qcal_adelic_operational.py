#!/usr/bin/env python3
"""CLI for the QCAL-Adelic operational summary."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from qcal_adelic_operational import operational_summary_json


def main() -> int:
    parser = argparse.ArgumentParser(description="Run QCAL-Adelic operational pipeline")
    parser.add_argument("n", type=int, help="Integer target N > 1")
    parser.add_argument("--k-max", type=int, default=8, help="Number of critical times")
    args = parser.parse_args()

    print(operational_summary_json(args.n, k_max=args.k_max))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
