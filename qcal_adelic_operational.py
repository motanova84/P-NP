"""QCAL-Adelic operational formalization utilities."""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple


@dataclass(frozen=True)
class QCALAdelicAnchors:
    """Anchored constants for the operational QCAL formulation."""

    f0_hz: float = 141.7001
    psi_target: float = 0.999999

    @property
    def omega0_rad_s(self) -> float:
        return 2.0 * math.pi * self.f0_hz


ANCHORS = QCALAdelicAnchors()


def critical_time(n: int, k: int, anchors: QCALAdelicAnchors = ANCHORS) -> float:
    """Return critical time t_k = (k/f0) * ln(n)."""
    if n <= 1:
        raise ValueError("n must be > 1")
    if k <= 0:
        raise ValueError("k must be > 0")
    return (k / anchors.f0_hz) * math.log(n)


def critical_times(n: int, k_max: int = 8, anchors: QCALAdelicAnchors = ANCHORS) -> List[float]:
    """Return first k_max critical times."""
    if k_max <= 0:
        raise ValueError("k_max must be > 0")
    return [critical_time(n, k, anchors=anchors) for k in range(1, k_max + 1)]


def coherence_at_time(
    n: int,
    t: float,
    anchors: QCALAdelicAnchors = ANCHORS,
    bandwidth: float = 1.0,
) -> float:
    """Gaussian coherence envelope centered at nearest critical instant."""
    if n <= 1:
        raise ValueError("n must be > 1")
    if t < 0:
        raise ValueError("t must be >= 0")
    if bandwidth <= 0:
        raise ValueError("bandwidth must be > 0")

    ln_n = math.log(n)
    k_nearest = max(1, round((t * anchors.f0_hz) / ln_n))
    t_star = critical_time(n, k_nearest, anchors=anchors)
    delta = t - t_star
    psi = math.exp(-((anchors.omega0_rad_s * delta) / bandwidth) ** 2)
    return min(psi, anchors.psi_target)


def divisor_resonance_score(n: int, d: int, anchors: QCALAdelicAnchors = ANCHORS) -> float:
    """Arithmetic-resonance score in [0, psi_target], maximal on true divisors."""
    if d <= 1 or d >= n:
        return 0.0

    remainder = n % d
    if remainder == 0:
        return anchors.psi_target

    return min(0.5 / (1.0 + remainder), anchors.psi_target)


def factorize_semiprime_operational(
    n: int, anchors: QCALAdelicAnchors = ANCHORS
) -> Dict[str, Optional[object]]:
    """Operational factorization pass with resonance scoring and exact validation."""
    if n <= 1:
        raise ValueError("n must be > 1")

    root = int(math.isqrt(n))
    best_pair: Optional[Tuple[int, int]] = None
    best_score = 0.0

    for d in range(2, root + 1):
        score = divisor_resonance_score(n, d, anchors=anchors)
        if score > best_score and n % d == 0:
            best_score = score
            best_pair = (d, n // d)

    if best_pair is None:
        return {
            "n": n,
            "factors": None,
            "verified": False,
            "coherence": 0.0,
            "message": "No non-trivial exact factors found.",
        }

    p, q = best_pair
    verified = (p * q == n) and (1 < p < n) and (1 < q < n)
    return {
        "n": n,
        "factors": (p, q),
        "verified": verified,
        "coherence": best_score,
        "message": "Exact factorization found by resonance-scored divisibility.",
    }


def operational_summary(
    n: int, k_max: int = 8, anchors: QCALAdelicAnchors = ANCHORS
) -> Dict[str, object]:
    """Full operational payload: anchors, critical clocks, coherence and factors."""
    times = critical_times(n, k_max=k_max, anchors=anchors)
    coherence_trace = [coherence_at_time(n, t, anchors=anchors) for t in times]
    factorization = factorize_semiprime_operational(n, anchors=anchors)

    return {
        "anchors": {
            "f0_hz": anchors.f0_hz,
            "omega0_rad_s": anchors.omega0_rad_s,
            "psi_target": anchors.psi_target,
        },
        "n": n,
        "critical_times": times,
        "coherence_trace": coherence_trace,
        "factorization": factorization,
    }


def operational_summary_json(
    n: int, k_max: int = 8, anchors: QCALAdelicAnchors = ANCHORS
) -> str:
    """JSON serializer helper for CLI."""
    return json.dumps(operational_summary(n, k_max=k_max, anchors=anchors), indent=2)


def operational_batch_summary(
    values: List[int], k_max: int = 8, anchors: QCALAdelicAnchors = ANCHORS
) -> Dict[str, object]:
    """Run operational summaries for a batch of integers."""
    if not values:
        raise ValueError("values must not be empty")

    items = [operational_summary(n, k_max=k_max, anchors=anchors) for n in values]
    verified_count = sum(1 for item in items if item["factorization"]["verified"])
    return {
        "anchors": {
            "f0_hz": anchors.f0_hz,
            "omega0_rad_s": anchors.omega0_rad_s,
            "psi_target": anchors.psi_target,
        },
        "count": len(items),
        "verified_count": verified_count,
        "items": items,
    }


def operational_batch_summary_json(
    values: List[int], k_max: int = 8, anchors: QCALAdelicAnchors = ANCHORS
) -> str:
    """JSON serializer helper for batch CLI mode."""
    return json.dumps(
        operational_batch_summary(values, k_max=k_max, anchors=anchors), indent=2
    )
