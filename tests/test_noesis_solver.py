from fastapi.testclient import TestClient

from noesis_solver import NOESISSolver, app


def test_solver_sat_instance():
    solver = NOESISSolver(3)
    is_sat, assignment, psi = solver.solve([[1, 2, 3], [-1, -2, 3]])
    assert is_sat is True
    assert assignment is not None
    assert psi >= 1 / 3


def test_api_solve_endpoint():
    client = TestClient(app)
    response = client.post(
        "/solve",
        json={"n": 3, "clauses": [[1, 2, 3], [-1, -2, 3]]},
    )
    assert response.status_code == 200
    data = response.json()
    assert data["is_sat"] is True
    assert data["assignment"] is not None
    assert data["psi"] >= 1 / 3
