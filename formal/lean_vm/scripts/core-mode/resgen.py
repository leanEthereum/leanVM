"""Shared by the core route's whole-program checks (`anylink.py`, `carry.py`, `termcall.py`, `monocall.py`):
where they write (`Guest/CoreMode/Gen`), the number of core functions and the ranges each check takes."""
import os, sys
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import coredata  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
OUT = os.path.join(ROOT, 'CoreMode', 'Gen')
# a whole-program check by ranges of functions, each a kernel check
RANGES = [(0, 100), (100, 300), (400, 400), (800, 400), (1200, None)]


def coreCount():
    return coredata.name_strings(os.path.join(ROOT, 'Data'))[1]

