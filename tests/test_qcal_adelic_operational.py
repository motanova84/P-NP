import math

from qcal_adelic_operational import (
    ANCHORS,
    coherence_at_time,
    operational_batch_summary,
    critical_time,
    critical_times,
    factorize_semiprime_operational,
)


def test_anchor_constants():
    assert ANCHORS.f0_hz == 141.7001
    assert ANCHORS.psi_target == 0.999999
    assert math.isclose(ANCHORS.omega0_rad_s, 2 * math.pi * 141.7001)


def test_critical_times_ordered_positive():
    values = critical_times(15, k_max=5)
    assert len(values) == 5
    assert all(v > 0 for v in values)
    assert values == sorted(values)


def test_coherence_at_critical_time_hits_target():
    t1 = critical_time(21, 1)
    psi = coherence_at_time(21, t1)
    assert math.isclose(psi, ANCHORS.psi_target)


def test_factorize_semiprime_operational_success():
    out = factorize_semiprime_operational(77)
    assert out["verified"] is True
    assert out["factors"] in {(7, 11), (11, 7)}
    assert out["coherence"] >= ANCHORS.psi_target


def test_factorize_prime_returns_none():
    out = factorize_semiprime_operational(13)
    assert out["verified"] is False
    assert out["factors"] is None


def test_operational_batch_summary_counts():
    batch = operational_batch_summary([77, 13], k_max=3)
    assert batch["count"] == 2
    assert batch["verified_count"] == 1
    assert len(batch["items"]) == 2
