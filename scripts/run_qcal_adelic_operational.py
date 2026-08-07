#!/usr/bin/env python3
"""CLI for the QCAL-Adelic operational summary."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from qcal_adelic_operational import (
    operational_batch_summary_json,
    operational_summary_json,
)


def _parse_values(args: argparse.Namespace) -> list[int]:
    values: list[int] = []
    if args.n is not None:
        values.append(args.n)
    if args.n_list:
        values.extend(int(part.strip()) for part in args.n_list.split(",") if part.strip())
    if args.n_file:
        for line in Path(args.n_file).read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if stripped:
                values.append(int(stripped))
    return values


def main() -> int:
    parser = argparse.ArgumentParser(description="Run QCAL-Adelic operational pipeline")
    parser.add_argument("n", nargs="?", type=int, help="Integer target N > 1")
    parser.add_argument("--k-max", type=int, default=8, help="Number of critical times")
    parser.add_argument(
        "--n-list",
        type=str,
        default="",
        help="Comma-separated integers for batch mode (e.g. 77,91,143)",
    )
    parser.add_argument(
        "--n-file",
        type=str,
        default="",
        help="Path to file containing one integer per line for batch mode",
    )
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Optional path to write JSON output",
    )
    args = parser.parse_args()

    values = _parse_values(args)
    if not values:
        parser.error("Provide n or --n-list or --n-file.")

    if len(values) == 1:
        payload = operational_summary_json(values[0], k_max=args.k_max)
    else:
        payload = operational_batch_summary_json(values, k_max=args.k_max)

    if args.output:
        Path(args.output).write_text(payload + "\n", encoding="utf-8")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
