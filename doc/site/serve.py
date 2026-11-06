#!/usr/bin/env python3
"""Serve the site with caching disabled: python3 doc/site/serve.py [port]  (default 8000)"""

import functools
import http.server
import os
import sys


class NoCache(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()


handler = functools.partial(NoCache, directory=os.path.dirname(os.path.abspath(__file__)))
port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
http.server.ThreadingHTTPServer(("", port), handler).serve_forever()
