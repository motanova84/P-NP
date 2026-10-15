import itertools
import math
import time
from typing import List, Optional, Tuple

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel, Field


class NOESISSolver:
    def __init__(self, n: int):
        if n < 1:
            raise ValueError("n must be >= 1")
        self.n = n
        self.f0 = 141.7001
        self.psi_threshold = 0.999999

    @staticmethod
    def _clause_satisfied(clause: List[int], assignment: List[int]) -> bool:
        for lit in clause:
            var = abs(lit) - 1
            val = assignment[var]
            if (lit > 0 and val == 1) or (lit < 0 and val == 0):
                return True
        return False

    def _formula_satisfied(self, clauses: List[List[int]], assignment: List[int]) -> bool:
        return all(self._clause_satisfied(clause, assignment) for clause in clauses)

    def _coherence(self, clauses: List[List[int]], assignment: List[int]) -> float:
        unsat_clauses = sum(1 for c in clauses if not self._clause_satisfied(c, assignment))
        return math.exp(-unsat_clauses)

    def solve(self, clauses: List[List[int]]) -> Tuple[bool, Optional[List[int]], float]:
        for clause in clauses:
            if len(clause) != 3:
                raise ValueError("each clause must have exactly 3 literals")
            for lit in clause:
                if lit == 0 or abs(lit) > self.n:
                    raise ValueError("literal out of range")

        for bits in itertools.product([0, 1], repeat=self.n):
            assignment = list(bits)
            if self._formula_satisfied(clauses, assignment):
                psi = self._coherence(clauses, assignment)
                return True, assignment, psi

        zero_assignment = [0] * self.n
        psi = self._coherence(clauses, zero_assignment)
        return False, None, psi


app = FastAPI(title="NOESIS API", version="1.0.0")


class SATRequest(BaseModel):
    n: int = Field(ge=1)
    clauses: List[List[int]]


class SATResponse(BaseModel):
    is_sat: bool
    assignment: Optional[List[int]]
    psi: float
    time_ms: float


@app.get("/health")
async def health():
    return {"status": "ok", "f0": 141.7001, "psi_threshold": 0.999999}


@app.post("/solve", response_model=SATResponse)
async def solve_sat(request: SATRequest):
    start = time.time()
    try:
        solver = NOESISSolver(request.n)
        is_sat, assignment, psi = solver.solve(request.clauses)
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc

    return SATResponse(
        is_sat=is_sat,
        assignment=assignment,
        psi=psi,
        time_ms=(time.time() - start) * 1000.0,
    )
