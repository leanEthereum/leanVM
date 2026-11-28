"""Shared by the core route's whole-program checks (`anylink.py`, `carry.py`, `termcall.py`, `monocall.py`, `down.py`):
where they write (`Guest/CoreMode/Gen`), the number of core functions and the ranges the facts carried to callees take."""
import os, sys
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import coredata  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
OUT = os.path.join(ROOT, 'CoreMode', 'Gen')


def coreCount():
    return coredata.name_strings(os.path.join(ROOT, 'Data'))[1]

# the facts carried to callees, every family's check in one walk (`down.py`, `Gen/Down{k}.lean`), by ranges of
# functions sized by their statements (`main_loop2`, function 40, alone, in windows): the kernel's memory grows over a
# range
DOWN_RANGES = [(0, 40), (40, 1), (41, 167), (208, 167), (375, 2), (377, 2), (379, 2), (381, 259), (640, 257), (897, 270), (1167, None)]
# a range of one function walked in windows (`down.py`, `Res.downWins`): its first function, the number of windows
DOWN_WINDOWS = {40: 2}


def down_ranges():
    """`DOWN_RANGES`, each `(first, count)`."""
    n = coreCount()
    out = [(a, (n - a) if m is None else m) for a, m in DOWN_RANGES]
    assert sum(m for _, m in out) == n and all(m > 0 for _, m in out), out
    return out


def down_mods():
    """The module of the families' range theorems over `DOWN_RANGES`."""
    return ['LeanVM.Guest.CoreMode.Gen.DownOk']
