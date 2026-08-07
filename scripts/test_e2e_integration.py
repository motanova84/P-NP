import sys

import httpx


def run_e2e_test() -> None:
    url = "http://localhost:8000/solve"
    payload = {
        "n": 3,
        "clauses": [
            [1, 2, 3],
            [-1, -2, 3],
        ],
    }

    response = httpx.post(url, json=payload, timeout=10.0)
    if response.status_code != 200:
        print(f"HTTP error {response.status_code}: {response.text}")
        sys.exit(1)

    data = response.json()
    assert data["is_sat"] is True
    assert data["psi"] >= 0.333333
    assert data["assignment"] is not None
    print("E2E OK:", data)


if __name__ == "__main__":
    run_e2e_test()
