"""Shared by the core route's whole-program checks (`anylink.py`, `carry.py`, `termcall.py`, `monocall.py`):
where they write (`Guest/CoreMode/Gen`), the number of core functions and the ranges each check takes."""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
OUT = os.path.join(ROOT, 'CoreMode', 'Gen')
# a whole-program check by ranges of functions, each a kernel check
RANGES = [(0, 100), (100, 300), (400, 400), (800, 400), (1200, None)]


def coreCount():
    t = open(os.path.join(ROOT, 'Data', 'NameStrings.lean'), encoding='utf-8').read()
    return int(re.search(r'abbrev coreCount : Nat := (\d+)', t).group(1))

