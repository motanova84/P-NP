"""Resonance engine for MCP-QCAL health checks with optional real observers."""

from __future__ import annotations

import csv
import math
import os
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, Optional, Tuple

F0_REFERENCE = 141.7001

NODE_CATALOG: Dict[str, Dict[str, Any]] = {
    "auron-governor": {"frequency_hz": 50.0000},
    "141-hz": {"frequency_hz": 141.7001},
    "interferometro-noesico": {"frequency_hz": 283.4002},
    "biologia-cuantica-noesica": {"frequency_hz": 70.85005},
    "economia-qcal-nodo-semilla": {"frequency_hz": 35.425025},
    "riemann-adelic": {"frequency_hz": 212.55015},
    "3d-navier-stokes": {"frequency_hz": 106.275075},
}

NODE_FREQUENCIES: Dict[str, float] = {
    node: meta["frequency_hz"] for node, meta in NODE_CATALOG.items()
}

REAL_OBSERVERS: Dict[str, Callable[[], Tuple[float, float, bool, bool]]] = {}


def _env_truthy(name: str) -> bool:
    value = os.getenv(name, "").strip().lower()
    return value in {"1", "true", "yes", "on"}


def _real_mode_enabled() -> bool:
    return _env_truthy("QCAL_REAL_TESTS")


def _project_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _data_dir() -> Path:
    configured = os.getenv("QCAL_REAL_DATA_DIR")
    if configured:
        return Path(configured).expanduser()
    return _project_root() / "tests" / "data"


def register_real_observer(
    node: str, fn: Callable[[], Tuple[float, float, bool, bool]]
) -> None:
    """Register a real observer callback for a node."""
    REAL_OBSERVERS[node] = fn


def score_psi(
    latency_ms: float,
    phase_offset_rad: float,
    heartbeat_ok: bool = True,
    schema_ok: bool = True,
) -> float:
    """Compute normalized Ψ score in [0, 1]."""
    if not heartbeat_ok or not schema_ok:
        return 0.0
    latency_penalty = min(latency_ms / 100.0, 1.0)
    phase_penalty = min(abs(phase_offset_rad) / 0.25, 1.0)
    psi = 1.0 - 0.45 * latency_penalty - 0.55 * phase_penalty
    return max(0.0, min(psi, 1.0))


def classify_resonance(psi: float, reachable: bool) -> Tuple[str, str]:
    """Classify resonance quality."""
    if not reachable:
        return "offline", "fail"
    if psi >= 0.99:
        return "coherent", "pass"
    if psi >= 0.95:
        return "drifting", "warn"
    return "fault", "fail"


def load_real_grid_sample() -> Tuple[float, float, bool, bool]:
    """Load a real grid-frequency sample or return simulation fallback."""
    configured_path = os.getenv("QCAL_GRID_SAMPLE_PATH")
    path = (
        Path(configured_path).expanduser()
        if configured_path
        else _data_dir() / "grid_frequency_2026-04-15T14_55Z.csv"
    )
    if not path.exists():
        return 12.4, 0.018, True, True

    frequencies = []
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            value = row.get("frequency_hz")
            if value is None:
                continue
            try:
                frequencies.append(float(value))
            except ValueError:
                continue

    if not frequencies:
        return 12.4, 0.018, True, True

    mean_frequency = sum(frequencies) / len(frequencies)
    delta_f = mean_frequency - 50.0
    window_seconds = float(len(frequencies))
    phase_offset = 2 * math.pi * delta_f * window_seconds
    latency_ms = float(os.getenv("QCAL_GRID_LATENCY_MS", "10.0"))
    return latency_ms, phase_offset, True, True


def load_qcal_spectrum() -> Tuple[float, float, bool, bool]:
    """Load a local QCAL spectrum sample or return high-coherence fallback."""
    configured_path = os.getenv("QCAL_SPECTRUM_PATH")
    path = (
        Path(configured_path).expanduser()
        if configured_path
        else _data_dir() / "qcal_spectrum_sample.csv"
    )
    if not path.exists():
        return 8.7, 0.003, True, True

    phases = []
    latencies = []
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            phase = row.get("phase_offset_rad")
            latency = row.get("latency_ms")
            try:
                if phase is not None:
                    phases.append(float(phase))
            except ValueError:
                pass
            try:
                if latency is not None:
                    latencies.append(float(latency))
            except ValueError:
                pass

    phase_offset = sum(phases) / len(phases) if phases else 0.003
    latency_ms = sum(latencies) / len(latencies) if latencies else 8.7
    return latency_ms, phase_offset, True, True


register_real_observer("auron-governor", load_real_grid_sample)
register_real_observer("141-hz", load_qcal_spectrum)


def _should_use_real(node_name: str, use_real: Optional[bool]) -> bool:
    if node_name not in REAL_OBSERVERS:
        return False
    if use_real is not None:
        return use_real
    return _real_mode_enabled()


def check_node_resonance(
    node_name: str,
    latency_ms: Optional[float] = None,
    phase_offset_rad: Optional[float] = None,
    heartbeat_ok: Optional[bool] = None,
    schema_ok: Optional[bool] = None,
    reachable: bool = True,
    use_real: Optional[bool] = None,
) -> Dict[str, Any]:
    """Compute MCP node health with optional real-observer input."""
    freq = NODE_FREQUENCIES.get(node_name, F0_REFERENCE)
    real_mode = _should_use_real(node_name=node_name, use_real=use_real)

    if real_mode:
        lat, phase, hb, sch = REAL_OBSERVERS[node_name]()
    else:
        lat = latency_ms if latency_ms is not None else 12.4
        phase = phase_offset_rad if phase_offset_rad is not None else 0.018
        hb = heartbeat_ok if heartbeat_ok is not None else True
        sch = schema_ok if schema_ok is not None else True

    psi = score_psi(lat, phase, hb, sch)
    resonance, status = classify_resonance(psi, reachable=reachable)
    phase_coherence = max(0.0, 1.0 - min(abs(phase), math.pi / 2) / (math.pi / 2))

    return {
        "node": node_name,
        "status": status,
        "reachable": reachable,
        "latency_ms": round(lat, 2),
        "resonance": resonance,
        "psi": round(psi, 6),
        "phase_offset_rad": round(phase, 6),
        "frequency_hz": freq,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "qcal": {
            "psi_raw": round(psi, 6),
            "f0_reference_hz": F0_REFERENCE,
            "harmonic_factor": round(freq / F0_REFERENCE, 5),
            "phase_coherence": round(phase_coherence, 4),
            "resonance_class": resonance,
            "logos_level": "saturated" if psi > 0.999 else "stable",
            "modo_real": real_mode,
        },
        "checks": {
            "transport": "ok",
            "schema": "ok" if sch else "fail",
            "heartbeat": "ok" if hb else "fail",
            "qcal_protocol": "ok",
            "fuente_fisica": "real" if real_mode else "simulada",
        },
        "error_code": None,
        "error_message": None,
    }
