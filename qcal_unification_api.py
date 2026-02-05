"""
QCAL Unification API - REST API for QCAL Framework

This module provides a REST API for accessing the QCAL unified framework,
allowing external systems to query problem connections, verify solutions,
and access universal constants.

Author: José Manuel Mota Burruezo · JMMB Ψ✧ ∞³
Date: January 2026

Usage:
    pip install fastapi uvicorn
    python qcal_unification_api.py
    
    Or with uvicorn directly:
    uvicorn qcal_unification_api:app --reload --host 0.0.0.0 --port 8000
"""

from typing import Dict, Any, List, Optional
from pydantic import BaseModel, Field
from qcal_unified_framework import QCALUnifiedFramework

# Try to import FastAPI
try:
    from fastapi import FastAPI, HTTPException
    from fastapi.responses import JSONResponse
    FASTAPI_AVAILABLE = True
except ImportError:
    print("Warning: FastAPI not installed. Install with: pip install fastapi uvicorn")
    FASTAPI_AVAILABLE = False

# Initialize framework
framework = QCALUnifiedFramework()

# Create FastAPI app if available
if FASTAPI_AVAILABLE:
    app = FastAPI(
        title="QCAL Unified Framework API",
        description="REST API for Quantum Coherent Algebraic Logic framework unifying Millennium Problems",
        version="1.0.0"
    )


# Pydantic models for API
class ProblemRequest(BaseModel):
    """Request model for problem unification."""
    problem_name: str = Field(..., description="Name of the Millennium Problem")
    parameters: Optional[Dict[str, float]] = Field(
        default=None, 
        description="Optional parameters for the problem"
    )


class UnifiedResponse(BaseModel):
    """Response model for unified problem."""
    qcal_operator: str = Field(..., description="QCAL operator name")
    universal_constant: float = Field(..., description="Associated universal constant")
    eigenvalue: float = Field(..., description="Operator eigenvalue")
    verification_result: Dict[str, Any] = Field(..., description="Verification status")
    connected_problems: List[str] = Field(..., description="Connected problems via QCAL")
    description: str = Field(..., description="Problem description")


class ConnectionsResponse(BaseModel):
    """Response model for problem connections."""
    connections: Dict[str, List[str]] = Field(..., description="Problem connection graph")
    coherence_score: float = Field(..., description="Overall coherence score")
    verification_status: Dict[str, bool] = Field(..., description="Verification status per problem")


class ConstantsResponse(BaseModel):
    """Response model for universal constants."""
    constants: Dict[str, float] = Field(..., description="All universal constants")
    correspondences: Dict[str, Any] = Field(..., description="Constant correspondences")


# API endpoints
if FASTAPI_AVAILABLE:
    @app.get("/")
    async def root():
        """Root endpoint with API information."""
        return {
            "name": "QCAL Unified Framework API",
            "version": "1.0.0",
            "description": "REST API for accessing QCAL framework",
            "endpoints": {
                "/problems": "List all Millennium Problems",
                "/constants": "Get universal constants",
                "/unify": "Unify a problem through QCAL",
                "/connections": "Get problem connections",
                "/verify/{problem}": "Verify a specific problem"
            }
        }


    @app.get("/problems", response_model=List[str])
    async def list_problems():
        """List all Millennium Problems in the framework."""
        return list(framework.problem_descriptions.keys())


    @app.get("/constants", response_model=ConstantsResponse)
    async def get_constants():
        """Get all universal constants and their correspondences."""
        correspondences = framework.verify_constant_correspondences()
        return ConstantsResponse(
            constants=framework.constants,
            correspondences=correspondences
        )


    @app.post("/unify", response_model=UnifiedResponse)
    async def unify_problem(request: ProblemRequest):
        """
        Unify a Millennium Problem through QCAL framework.
        
        Args:
            request: Problem request with name and optional parameters
            
        Returns:
            Unified response with operator, constant, and connections
        """
        problem_name = request.problem_name.lower().replace(" ", "_").replace("-", "_")
        
        # Check if problem exists
        if problem_name not in framework.operators:
            raise HTTPException(
                status_code=404,
                detail=f"Problem '{request.problem_name}' not found. Available: {list(framework.operators.keys())}"
            )
        
        # Get operator and compute eigenvalue
        operator = framework.operators[problem_name]
        constants = request.parameters if request.parameters else framework.constants
        eigenvalue = operator(constants)
        
        # Get verification
        verification = framework.verify_problem(problem_name)
        
        # Get connections
        connections = framework.find_connections(problem_name)
        
        # Get description
        description = framework.problem_descriptions.get(problem_name, "No description")
        
        # Determine universal constant
        constant_map = {
            'p_vs_np': framework.constants['kappa_pi'],
            'riemann': framework.constants['f0'],
            'bsd': framework.constants['bsd_delta'],
            'navier_stokes': framework.constants['navier_stokes_epsilon'],
            'ramsey': framework.constants['ramsey_ratio'],
            'yang_mills': framework.constants['yang_mills_g'],
            'hodge': framework.constants['hodge_sum']
        }
        universal_constant = constant_map.get(problem_name, 0.0)
        
        return UnifiedResponse(
            qcal_operator=operator.__name__,
            universal_constant=universal_constant,
            eigenvalue=eigenvalue,
            verification_result=verification,
            connected_problems=connections,
            description=description
        )


    @app.get("/connections", response_model=ConnectionsResponse)
    async def get_problem_connections():
        """
        Get all connections between problems via QCAL.
        
        Returns:
            Connection graph, coherence score, and verification status
        """
        # Build connection graph
        connections = {}
        for problem in framework.operators.keys():
            connections[problem] = framework.find_connections(problem)
        
        # Calculate coherence score (simplified)
        # Full coherence = all problems verified and connected
        verification_status = {}
        for problem in framework.operators.keys():
            result = framework.verify_problem(problem)
            verification_status[problem] = result['status'] == 'verified'
        
        verified_count = sum(verification_status.values())
        total_count = len(verification_status)
        coherence_score = verified_count / total_count if total_count > 0 else 0.0
        
        return ConnectionsResponse(
            connections=connections,
            coherence_score=coherence_score,
            verification_status=verification_status
        )


    @app.get("/verify/{problem_name}")
    async def verify_problem_endpoint(problem_name: str):
        """
        Verify a specific problem through QCAL framework.
        
        Args:
            problem_name: Name of the problem to verify
            
        Returns:
            Verification result
        """
        problem_key = problem_name.lower().replace(" ", "_").replace("-", "_")
        
        if problem_key not in framework.operators:
            raise HTTPException(
                status_code=404,
                detail=f"Problem '{problem_name}' not found"
            )
        
        result = framework.verify_problem(problem_key)
        return JSONResponse(content=result)


    @app.get("/commutativity/{op1}/{op2}")
    async def check_commutativity(op1: str, op2: str):
        """
        Check if two operators commute.
        
        Args:
            op1: First operator name
            op2: Second operator name
            
        Returns:
            Commutativity analysis
        """
        result = framework.get_operator_commutativity(op1, op2)
        
        if 'error' in result:
            raise HTTPException(status_code=404, detail=result['error'])
        
        return JSONResponse(content=result)


def main():
    """Run the API server."""
    if not FASTAPI_AVAILABLE:
        print("Error: FastAPI not installed.")
        print("Install with: pip install fastapi uvicorn")
        return
    
    import uvicorn
    print("Starting QCAL Unification API server...")
    print("API documentation available at: http://localhost:8000/docs")
    uvicorn.run(app, host="0.0.0.0", port=8000)


if __name__ == "__main__":
    main()
