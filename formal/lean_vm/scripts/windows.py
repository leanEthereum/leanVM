"""The sizes the guest's generators cut their checks at, in one place.

A module may take 7.5 GB (the gate's cap, `formal/AGENTS.md`); the windows below keep a module of the long functions'
checks at about 6.5 GB, under it. A function whose windows at these sizes would take more has its own sizes in its rule
file (`core-mode/fn/<f>.py`: `FRAME_WIN`, `CORE_WIN`, `PAIR_WIN`), by stable name, which `own()` reads.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'core-mode'))

# the frame walks (`core-mode/frame_gen.py`): instructions per module of checks, and per window of a long function
FRAME_CHUNK = int(os.environ.get('FRAME_CHUNK', 12000))
FRAME_WIN = int(os.environ.get('FRAME_WIN', 7000))
# the route's passes over a long loop helper (`core-mode/core.py`): nested statements per body window, instructions per
# code window
CORE_STMTS, CORE_CODE = 12000, 8192
# the alignment's and the pairing's windows (`bridge-cert/align.py`, `core-mode/pair.py`), in instructions
ALIGN_WIN = 4096
# the heap certificates' windows (`core-mode/heapwin.py`): a check estimated above `HEAP_BUDGET` thousand heartbeats is
# windowed, each window estimated at most `HEAP_WIN` and at most `HEAP_ATOMS` atoms (the kernel's memory grows with the
# atoms a window's pass and ghost check go through); a window's statements' share of its estimate at most
# `HEAP_WIN - HEAP_FIXW` (the rest reads the context's tries); characters of a context literal's definitions
# (`HEAP_CXPART`), of the certificate's lists one module's equations read (`HEAP_CXDEC`), of state literals
# (`HEAP_SPART`) in one module
HEAP_BUDGET, HEAP_WIN, HEAP_ATOMS, HEAP_FIXW = 90000, 100000, 15000, 40000
HEAP_CXPART, HEAP_CXDEC, HEAP_SPART = 250000, 150000, 250000
# the loop helpers' range checks (`core-mode/loopcheck.py`): thousand heartbeats per range at most
RANGE_BUDGET = 800000


def own(table):
    """A table of the functions' own window sizes (`FRAME_WIN`, `CORE_WIN` or `PAIR_WIN` of their rule files), by
    stable name."""
    import fnrules
    return fnrules.table(table) or {}
