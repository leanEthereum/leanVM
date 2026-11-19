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


def coreBody(ns):
    """The core IR body of the function of stable name `ns`, as text."""
    import glob
    for path in glob.glob(os.path.join(ROOT, 'Pack', '*', 'Core.lean')):
        t = open(path, encoding='utf-8').read()
        key = '\nnamespace LeanVM.Guest.Fn.«%s»\n' % ns
        if key in t:
            blk = t[t.index(key):]
            return blk[:blk.index('\nend LeanVM.Guest.Fn.«%s»' % ns)]
    raise KeyError(ns)
