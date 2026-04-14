"""
api/simple.py - Vercel serverless function: Simple demo endpoint

Exposes the simple P vs NP demo as a Vercel serverless API route
at /simple.

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
    """Vercel serverless handler for the simple demo endpoint."""

    def do_GET(self):
        try:
            import importlib.util
            repo_root = os.path.join(os.path.dirname(__file__), '..')
            spec = importlib.util.spec_from_file_location(
                'simple_demo',
                os.path.join(repo_root, 'simple_demo.py'),
            )
            module = importlib.util.module_from_spec(spec)
            # Capture stdout
            import io
            from contextlib import redirect_stdout
            buf = io.StringIO()
            with redirect_stdout(buf):
                spec.loader.exec_module(module)
            body = buf.getvalue().encode('utf-8')
        except Exception as exc:
            body = (
                "Simple Demo - P vs NP Treewidth Framework\n"
                "==========================================\n"
                f"Module loaded. Error running demo: {exc}\n"
                "\nFramework: Treewidth + Information Complexity\n"
                "Theorem: Lemma 6.24 - Structural P≠NP Dichotomy\n"
            ).encode('utf-8')

        self.send_response(200)
        self.send_header('Content-Type', 'text/plain; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)
