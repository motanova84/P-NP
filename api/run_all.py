"""
api/run_all.py - Vercel serverless function: Test suite status endpoint

Returns a summary of the P vs NP framework test suite status
as a Vercel serverless API route at /run_all.

Author: JMMB Ψ✧
Repository: P vs NP - Treewidth + Information Complexity Framework
License: Sovereign Noetic License 1.0
"""

import os
import json
import glob as _glob
from http.server import BaseHTTPRequestHandler


class handler(BaseHTTPRequestHandler):
    """Vercel serverless handler for the run_all test-status endpoint."""

    def do_GET(self):
        repo_root = os.path.join(os.path.dirname(__file__), '..')

        # Collect test file names without executing them
        test_pattern = os.path.join(repo_root, 'tests', 'test_*.py')
        root_test_pattern = os.path.join(repo_root, 'test_*.py')
        test_files = sorted(
            os.path.basename(p)
            for p in _glob.glob(test_pattern) + _glob.glob(root_test_pattern)
        )

        summary = {
            "project": "P vs NP - Treewidth + Information Complexity Framework",
            "theorem": "Lemma 6.24 - Structural P≠NP Dichotomy",
            "framework": "Treewidth + Information Complexity",
            "test_count": len(test_files),
            "test_files": test_files,
            "status": "available",
        }

        body = json.dumps(summary, indent=2, ensure_ascii=False).encode('utf-8')

        self.send_response(200)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)
