import math
import os
import sys

import pandas as pd
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from mcp_network.resonance import F0_REFERENCE, check_node_resonance


pytestmark = pytest.mark.skipif(
    os.getenv("QCAL_REAL_TESTS") != "1",
    reason="Set QCAL_REAL_TESTS=1 to run physical-observer tests",
)


class TestCheckNodeResonanceRealObservers:
    def test_biologia_cuantica_psi_above_gate(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["resonance"] == "coherent"
        assert health["psi"] >= 0.85

    def test_biologia_cuantica_phase_calculation(self):
        path = os.path.join(os.path.dirname(__file__), "data", "hrv_eeg_biologia_cuantica.csv")
        df = pd.read_csv(path)
        rr_mean = df["rr_interval_ms"].mean()
        expected_rr = 1000.0 / (F0_REFERENCE / 2.0)
        expected_phase = 2.0 * math.pi * ((rr_mean - expected_rr) / 1000.0) * 60.0

        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["phase_offset_rad"] == pytest.approx(expected_phase, abs=1e-12)

    def test_biologia_cuantica_harmonic_factor(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["qcal"]["harmonic_factor"] == 0.5

    def test_biologia_cuantica_source_real(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["checks"]["fuente_fisica"] == "real"
        assert health["qcal"]["modo_real"] is True

    def test_biologia_cuantica_node_name(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["node"] == "biologia-cuantica-noesica"

    def test_biologia_cuantica_latency_positive(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["latency_ms"] > 0

    def test_biologia_cuantica_phase_gate_flag(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["checks"]["phase_within_gate"] is True

    def test_interferometro_psi_above_gate(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["resonance"] == "coherent"
        assert health["psi"] >= 0.85

    def test_interferometro_phase_from_magnetometer(self):
        path = os.path.join(os.path.dirname(__file__), "data", "magnetometer_interferometer.csv")
        df = pd.read_csv(path)
        peak_freq = df["frequency_hz"].mean()
        expected_phase = 2.0 * math.pi * (peak_freq - F0_REFERENCE * 2.0) / (F0_REFERENCE * 2.0)

        health = check_node_resonance("interferometro-noesico")
        assert health["phase_offset_rad"] == pytest.approx(expected_phase, abs=1e-12)

    def test_interferometro_harmonic_factor(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["qcal"]["harmonic_factor"] == 2.0

    def test_interferometro_source_real(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["checks"]["fuente_fisica"] == "real"
        assert health["qcal"]["modo_real"] is True

    def test_interferometro_node_name(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["node"] == "interferometro-noesico"

    def test_interferometro_latency_positive(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["latency_ms"] > 0

    def test_interferometro_phase_gate_flag(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["checks"]["phase_within_gate"] is True
