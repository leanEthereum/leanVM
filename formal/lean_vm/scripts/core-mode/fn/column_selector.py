"""`column_selector`'s rules: its contracts (`sigc.py`), its lowest digit's read in its strided table (`CoreMode.csSub`)."""
import re
from fnrules import valf, guest_const, guest_arr
from sigseed import sig, cell, num, run

# its parameter `sel_eq` and its lowest digit `digits[0]`
SEL_EQ, DIGIT0 = valf('column_selector', 'sel_eq'), valf('column_selector', 'digits[0]')
# a nibble's row of eq tables and where its level-`w` table starts in it (`B1.Tables.selEqOff`)
SEL_EQ_STRIDE, SEL_NIBBLES = guest_const('SEL_EQ_STRIDE'), guest_const('SEL_NIBBLES')
SEL_EQ_OFF = guest_arr('SEL_EQ_OFF')


def lowest(kap):
    """The lowest nibble's width `w` and where its eq table starts in `sel_eq`."""
    w = 4 * (kap // 4) + 4 - kap
    return w, SEL_EQ_STRIDE * (kap // 4) + SEL_EQ_OFF[w - 1]


def cs_contract(kap):
    """`column_selector__L{κ}(offset, sel_eq, sel_g)` reads, and leaves written, each nibble `j ≥ κ/4`'s eq table at
    `sel_eq·g^(SEL_EQ_STRIDE·j + SEL_EQ_OFF[w - 1])` (`w` the nibble's width, `4` past the lowest; entries `2^(4 - w)` apart) and its
    shares at `sel_g·g^(16j)`."""
    j0 = kap // 4
    w0, off0 = lowest(kap)
    runs = [run(cell(0, [(3, 1)]), num(0), num(2 ** w0), 2 ** (4 - w0), off0)]
    runs += [run(cell(0, [(3, 1)]), num(0), num(16), 1, SEL_EQ_STRIDE * j + SEL_EQ_OFF[3]) for j in range(j0 + 1, SEL_NIBBLES)]
    runs += [run(cell(0, [(4, 1)]), num(0), num(16), 1, 16 * j) for j in range(j0, SEL_NIBBLES)]
    return sig(range(5), None, [5], preR=runs, postR=runs)


CONTRACTS = {'column_selector__L%d' % kap: cs_contract(kap) for kap in range(31)}


def cs_kappa(k):
    """`κ` for `column_selector__L{κ}`, `κ < 31` (`B1.Tables.lName`)."""
    m = re.fullmatch(r'column_selector__L(\d+)', k)
    return int(m.group(1)) if m and int(m.group(1)) < 31 else None


def cs_sub(kap):
    """`CoreMode.csSub κ`: the lowest digit's read `[sel_eq]·[digit₀]·g^off` in its strided table."""
    w, off = lowest(kap)
    return ('sub', (((SEL_EQ, 1), (DIGIT0, 1)), off), ((((SEL_EQ, 1),), off), 2 ** (4 - w), ('num', 0), ('num', 2 ** w)))


def sub(k, c):
    kap = cs_kappa(k)
    return cs_sub(kap) if kap is not None else None


def fam(k, r):
    kap = cs_kappa(k)
    return kap is not None and r == cs_sub(kap)

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
