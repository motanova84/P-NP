"""
api/demo.py - Vercel serverless function: IC-SAT Demo endpoint

Exposes the IC-SAT information-complexity SAT dichotomy demo
as a Vercel serverless API route at /demo.

Author: JMMB Ψ✧
Repository: P vs NP - Treewidth + Information Complexity Framework
License: Sovereign Noetic License 1.0
"""

import sys
import os
from http.server import BaseHTTPRequestHandler

# Allow importing project modules
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


class handler(BaseHTTPRequestHandler):
    """Vercel serverless handler for the IC-SAT demo endpoint."""

    def do_GET(self):
        try:
            from examples.demo_ic_sat import run_demo
            output = run_demo()
            body = output.encode('utf-8') if isinstance(output, str) else output
            content_type = b'text/plain; charset=utf-8'
        except Exception as exc:
            body = (
                "IC-SAT Demo - P vs NP Treewidth Framework\n"
                "==========================================\n"
                f"Demo module loaded. Error running demo: {exc}\n"
                "\nFramework: Treewidth + Information Complexity\n"
                "Theorem: Lemma 6.24 - Structural P≠NP Dichotomy\n"
            ).encode('utf-8')
            content_type = b'text/plain; charset=utf-8'

        self.send_response(200)
        self.send_header('Content-Type', content_type.decode())
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)
