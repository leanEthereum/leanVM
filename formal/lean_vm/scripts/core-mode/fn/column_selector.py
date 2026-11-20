"""`column_selector`'s rules: its lowest digit's read in its strided table (`CoreMode.csSub`)."""
import re


def cs_kappa(k):
    """`κ` for `column_selector__L{κ}`, `κ < 31` (`B1.Tables.lName`)."""
    m = re.fullmatch(r'column_selector__L(\d+)', k)
    return int(m.group(1)) if m and int(m.group(1)) < 31 else None


def cs_sub(kap):
    """`CoreMode.csSub κ`: the lowest digit's read `[sel_eq]·[digit₀]·g^off` in its strided table."""
    w = 4 * (kap // 4) + 4 - kap
    off = 64 * (kap // 4) + 16 * (w - 1)
    return ('sub', (((1, 1), (3, 1)), off), ((((1, 1),), off), 2 ** (4 - w), ('num', 0), ('num', 2 ** w)))


def sub(k, c):
    kap = cs_kappa(k)
    return cs_sub(kap) if kap is not None else None


def fam(k, r):
    kap = cs_kappa(k)
    return kap is not None and r == cs_sub(kap)

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/ResCs.lean',
    'LeanVM/Guest/CoreMode/Fam/CsQ.lean',
    'LeanVM/Guest/CoreMode/Fn/column_selector/*.lean',
]
