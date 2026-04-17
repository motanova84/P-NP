import os
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from mcp_network.resonance import REAL_OBSERVERS, check_node_resonance


def test_check_node_resonance_defaults_in_sim_mode(monkeypatch):
    monkeypatch.delenv("QCAL_REAL_TESTS", raising=False)
    health = check_node_resonance("auron-governor")

    assert health["qcal"]["modo_real"] is False
    assert health["checks"]["fuente_fisica"] == "simulada"
    assert health["latency_ms"] == pytest.approx(12.4, abs=0.01)
    assert 0.0 <= health["psi"] <= 1.0


def test_check_node_resonance_uses_fixture_in_real_mode(monkeypatch):
    fixture_path = os.path.join(
        os.path.dirname(__file__), "data", "grid_frequency_2026-04-15T14_55Z.csv"
    )
    monkeypatch.setenv("QCAL_REAL_TESTS", "1")
    monkeypatch.setenv("QCAL_GRID_SAMPLE_PATH", fixture_path)
    monkeypatch.setenv("QCAL_GRID_LATENCY_MS", "10.0")

    health = check_node_resonance("auron-governor")

    assert health["qcal"]["modo_real"] is True
    assert health["checks"]["fuente_fisica"] == "real"
    assert health["status"] in {"pass", "warn"}
    assert health["frequency_hz"] == pytest.approx(50.0, rel=1e-9)
    assert 0.0 <= health["psi"] <= 1.0


def test_check_node_resonance_custom_observer(monkeypatch):
    monkeypatch.setenv("QCAL_REAL_TESTS", "1")
    monkeypatch.setitem(
        REAL_OBSERVERS,
        "interferometro-noesico",
        lambda: (9.0, 0.002, True, True),
    )

    health = check_node_resonance("interferometro-noesico")

    assert health["qcal"]["modo_real"] is True
    assert health["checks"]["fuente_fisica"] == "real"
    assert health["frequency_hz"] == pytest.approx(283.4002, rel=1e-9)
    assert health["status"] in {"pass", "warn"}
