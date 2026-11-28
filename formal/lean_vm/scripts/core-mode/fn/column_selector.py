"""`column_selector`'s rules: its contracts (`sigc.py`), its lowest digit's read in its strided table (`CoreMode.csSub`).
Hotwire: specialized on the stack's nibbles `n` too (`column_selector__L{n}_L{κ}`), its digits and tables to nibble `n`."""
import re
from fnrules import val, valf, guest_const, guest_arr
from sigseed import sig, cell, num, run

# its parameter `sel_eq`
SEL_EQ = valf('column_selector', 'sel_eq')
# its lowest digit `digits[0]`, by specialization (its number differs with the unrolled nibbles before it)
DIGIT0 = {
    'column_selector__L4_L0': val('column_selector__L4_L0', 'digits[0]'),
    'column_selector__L4_L1': val('column_selector__L4_L1', 'digits[0]'),
    'column_selector__L4_L2': val('column_selector__L4_L2', 'digits[0]'),
    'column_selector__L4_L3': val('column_selector__L4_L3', 'digits[0]'),
    'column_selector__L4_L4': val('column_selector__L4_L4', 'digits[0]'),
    'column_selector__L4_L5': val('column_selector__L4_L5', 'digits[0]'),
    'column_selector__L4_L6': val('column_selector__L4_L6', 'digits[0]'),
    'column_selector__L4_L7': val('column_selector__L4_L7', 'digits[0]'),
    'column_selector__L4_L8': val('column_selector__L4_L8', 'digits[0]'),
    'column_selector__L4_L9': val('column_selector__L4_L9', 'digits[0]'),
    'column_selector__L4_L10': val('column_selector__L4_L10', 'digits[0]'),
    'column_selector__L4_L11': val('column_selector__L4_L11', 'digits[0]'),
    'column_selector__L4_L12': val('column_selector__L4_L12', 'digits[0]'),
    'column_selector__L4_L13': val('column_selector__L4_L13', 'digits[0]'),
    'column_selector__L4_L14': val('column_selector__L4_L14', 'digits[0]'),
    'column_selector__L4_L15': val('column_selector__L4_L15', 'digits[0]'),
    'column_selector__L5_L0': val('column_selector__L5_L0', 'digits[0]'),
    'column_selector__L5_L1': val('column_selector__L5_L1', 'digits[0]'),
    'column_selector__L5_L2': val('column_selector__L5_L2', 'digits[0]'),
    'column_selector__L5_L3': val('column_selector__L5_L3', 'digits[0]'),
    'column_selector__L5_L4': val('column_selector__L5_L4', 'digits[0]'),
    'column_selector__L5_L5': val('column_selector__L5_L5', 'digits[0]'),
    'column_selector__L5_L6': val('column_selector__L5_L6', 'digits[0]'),
    'column_selector__L5_L7': val('column_selector__L5_L7', 'digits[0]'),
    'column_selector__L5_L8': val('column_selector__L5_L8', 'digits[0]'),
    'column_selector__L5_L9': val('column_selector__L5_L9', 'digits[0]'),
    'column_selector__L5_L10': val('column_selector__L5_L10', 'digits[0]'),
    'column_selector__L5_L11': val('column_selector__L5_L11', 'digits[0]'),
    'column_selector__L5_L12': val('column_selector__L5_L12', 'digits[0]'),
    'column_selector__L5_L13': val('column_selector__L5_L13', 'digits[0]'),
    'column_selector__L5_L14': val('column_selector__L5_L14', 'digits[0]'),
    'column_selector__L5_L15': val('column_selector__L5_L15', 'digits[0]'),
    'column_selector__L5_L16': val('column_selector__L5_L16', 'digits[0]'),
    'column_selector__L5_L17': val('column_selector__L5_L17', 'digits[0]'),
    'column_selector__L5_L18': val('column_selector__L5_L18', 'digits[0]'),
    'column_selector__L5_L19': val('column_selector__L5_L19', 'digits[0]'),
    'column_selector__L6_L0': val('column_selector__L6_L0', 'digits[0]'),
    'column_selector__L6_L1': val('column_selector__L6_L1', 'digits[0]'),
    'column_selector__L6_L2': val('column_selector__L6_L2', 'digits[0]'),
    'column_selector__L6_L3': val('column_selector__L6_L3', 'digits[0]'),
    'column_selector__L6_L4': val('column_selector__L6_L4', 'digits[0]'),
    'column_selector__L6_L5': val('column_selector__L6_L5', 'digits[0]'),
    'column_selector__L6_L6': val('column_selector__L6_L6', 'digits[0]'),
    'column_selector__L6_L7': val('column_selector__L6_L7', 'digits[0]'),
    'column_selector__L6_L8': val('column_selector__L6_L8', 'digits[0]'),
    'column_selector__L6_L9': val('column_selector__L6_L9', 'digits[0]'),
    'column_selector__L6_L10': val('column_selector__L6_L10', 'digits[0]'),
    'column_selector__L6_L11': val('column_selector__L6_L11', 'digits[0]'),
    'column_selector__L6_L12': val('column_selector__L6_L12', 'digits[0]'),
    'column_selector__L6_L13': val('column_selector__L6_L13', 'digits[0]'),
    'column_selector__L6_L14': val('column_selector__L6_L14', 'digits[0]'),
    'column_selector__L6_L15': val('column_selector__L6_L15', 'digits[0]'),
    'column_selector__L6_L16': val('column_selector__L6_L16', 'digits[0]'),
    'column_selector__L6_L17': val('column_selector__L6_L17', 'digits[0]'),
    'column_selector__L6_L18': val('column_selector__L6_L18', 'digits[0]'),
    'column_selector__L6_L19': val('column_selector__L6_L19', 'digits[0]'),
    'column_selector__L6_L20': val('column_selector__L6_L20', 'digits[0]'),
    'column_selector__L6_L21': val('column_selector__L6_L21', 'digits[0]'),
    'column_selector__L6_L22': val('column_selector__L6_L22', 'digits[0]'),
    'column_selector__L6_L23': val('column_selector__L6_L23', 'digits[0]'),
    'column_selector__L7_L0': val('column_selector__L7_L0', 'digits[0]'),
    'column_selector__L7_L1': val('column_selector__L7_L1', 'digits[0]'),
    'column_selector__L7_L2': val('column_selector__L7_L2', 'digits[0]'),
    'column_selector__L7_L3': val('column_selector__L7_L3', 'digits[0]'),
    'column_selector__L7_L4': val('column_selector__L7_L4', 'digits[0]'),
    'column_selector__L7_L5': val('column_selector__L7_L5', 'digits[0]'),
    'column_selector__L7_L6': val('column_selector__L7_L6', 'digits[0]'),
    'column_selector__L7_L7': val('column_selector__L7_L7', 'digits[0]'),
    'column_selector__L7_L8': val('column_selector__L7_L8', 'digits[0]'),
    'column_selector__L7_L9': val('column_selector__L7_L9', 'digits[0]'),
    'column_selector__L7_L10': val('column_selector__L7_L10', 'digits[0]'),
    'column_selector__L7_L11': val('column_selector__L7_L11', 'digits[0]'),
    'column_selector__L7_L12': val('column_selector__L7_L12', 'digits[0]'),
    'column_selector__L7_L13': val('column_selector__L7_L13', 'digits[0]'),
    'column_selector__L7_L14': val('column_selector__L7_L14', 'digits[0]'),
    'column_selector__L7_L15': val('column_selector__L7_L15', 'digits[0]'),
    'column_selector__L7_L16': val('column_selector__L7_L16', 'digits[0]'),
    'column_selector__L7_L17': val('column_selector__L7_L17', 'digits[0]'),
    'column_selector__L7_L18': val('column_selector__L7_L18', 'digits[0]'),
    'column_selector__L7_L19': val('column_selector__L7_L19', 'digits[0]'),
    'column_selector__L7_L20': val('column_selector__L7_L20', 'digits[0]'),
    'column_selector__L7_L21': val('column_selector__L7_L21', 'digits[0]'),
    'column_selector__L7_L22': val('column_selector__L7_L22', 'digits[0]'),
    'column_selector__L7_L23': val('column_selector__L7_L23', 'digits[0]'),
    'column_selector__L7_L24': val('column_selector__L7_L24', 'digits[0]'),
    'column_selector__L7_L25': val('column_selector__L7_L25', 'digits[0]'),
    'column_selector__L7_L26': val('column_selector__L7_L26', 'digits[0]'),
    'column_selector__L7_L27': val('column_selector__L7_L27', 'digits[0]'),
    'column_selector__L8_L0': val('column_selector__L8_L0', 'digits[0]'),
    'column_selector__L8_L1': val('column_selector__L8_L1', 'digits[0]'),
    'column_selector__L8_L2': val('column_selector__L8_L2', 'digits[0]'),
    'column_selector__L8_L3': val('column_selector__L8_L3', 'digits[0]'),
    'column_selector__L8_L4': val('column_selector__L8_L4', 'digits[0]'),
    'column_selector__L8_L5': val('column_selector__L8_L5', 'digits[0]'),
    'column_selector__L8_L6': val('column_selector__L8_L6', 'digits[0]'),
    'column_selector__L8_L7': val('column_selector__L8_L7', 'digits[0]'),
    'column_selector__L8_L8': val('column_selector__L8_L8', 'digits[0]'),
    'column_selector__L8_L9': val('column_selector__L8_L9', 'digits[0]'),
    'column_selector__L8_L10': val('column_selector__L8_L10', 'digits[0]'),
    'column_selector__L8_L11': val('column_selector__L8_L11', 'digits[0]'),
    'column_selector__L8_L12': val('column_selector__L8_L12', 'digits[0]'),
    'column_selector__L8_L13': val('column_selector__L8_L13', 'digits[0]'),
    'column_selector__L8_L14': val('column_selector__L8_L14', 'digits[0]'),
    'column_selector__L8_L15': val('column_selector__L8_L15', 'digits[0]'),
    'column_selector__L8_L16': val('column_selector__L8_L16', 'digits[0]'),
    'column_selector__L8_L17': val('column_selector__L8_L17', 'digits[0]'),
    'column_selector__L8_L18': val('column_selector__L8_L18', 'digits[0]'),
    'column_selector__L8_L19': val('column_selector__L8_L19', 'digits[0]'),
    'column_selector__L8_L20': val('column_selector__L8_L20', 'digits[0]'),
    'column_selector__L8_L21': val('column_selector__L8_L21', 'digits[0]'),
    'column_selector__L8_L22': val('column_selector__L8_L22', 'digits[0]'),
    'column_selector__L8_L23': val('column_selector__L8_L23', 'digits[0]'),
    'column_selector__L8_L24': val('column_selector__L8_L24', 'digits[0]'),
    'column_selector__L8_L25': val('column_selector__L8_L25', 'digits[0]'),
    'column_selector__L8_L26': val('column_selector__L8_L26', 'digits[0]'),
    'column_selector__L8_L27': val('column_selector__L8_L27', 'digits[0]'),
    'column_selector__L8_L28': val('column_selector__L8_L28', 'digits[0]'),
    'column_selector__L8_L29': val('column_selector__L8_L29', 'digits[0]'),
    'column_selector__L8_L30': val('column_selector__L8_L30', 'digits[0]'),
}
# a nibble's row of eq tables and where its level-`w` table starts in it (`B1.Tables.selEqOff`)
SEL_EQ_STRIDE, SEL_NIBBLES = guest_const('SEL_EQ_STRIDE'), guest_const('SEL_NIBBLES')
SEL_EQ_OFF = guest_arr('SEL_EQ_OFF')


def lowest(kap):
    """The lowest nibble's width `w` and where its eq table starts in `sel_eq`."""
    w = 4 * (kap // 4) + 4 - kap
    return w, SEL_EQ_STRIDE * (kap // 4) + SEL_EQ_OFF[w - 1]


def cs_contract(n, kap):
    """`column_selector__L{n}_L{κ}(offset, sel_eq, sel_g)`, `n` the stack's nibbles, reads, and leaves written, each
    nibble `κ/4 ≤ j < n`'s eq table at `sel_eq·g^(SEL_EQ_STRIDE·j + SEL_EQ_OFF[w - 1])` (`w` the nibble's width, `4`
    past the lowest; entries `2^(4 - w)` apart) and its shares at `sel_g·g^(16j)`."""
    j0 = kap // 4
    w0, off0 = lowest(kap)
    runs = [run(cell(0, [(3, 1)]), num(0), num(2 ** w0), 2 ** (4 - w0), off0)]
    runs += [run(cell(0, [(3, 1)]), num(0), num(16), 1, SEL_EQ_STRIDE * j + SEL_EQ_OFF[3]) for j in range(j0 + 1, n)]
    runs += [run(cell(0, [(4, 1)]), num(0), num(16), 1, 16 * j) for j in range(j0, n)]
    return sig(range(5), None, [5], preR=runs, postR=runs)


def cs_shape(k):
    """`(n, κ)` for `column_selector__L{n}_L{κ}`, `κ/4 < n ≤ SEL_NIBBLES` (its specializations)."""
    m = re.fullmatch(r'column_selector__L(\d+)_L(\d+)', k)
    if not m: return None
    n, kap = int(m.group(1)), int(m.group(2))
    return (n, kap) if kap // 4 < n <= SEL_NIBBLES else None


CONTRACTS = {k: cs_contract(*cs_shape(k)) for k in DIGIT0}


def cs_kappa(k):
    """`κ` for `column_selector__L{n}_L{κ}`."""
    s = cs_shape(k)
    return s[1] if s else None


def cs_sub(k, kap):
    """`CoreMode.csSub κ`: the lowest digit's read `[sel_eq]·[digit₀]·g^off` in its strided table."""
    w, off = lowest(kap)
    return ('sub', (((SEL_EQ, 1), (DIGIT0[k], 1)), off), ((((SEL_EQ, 1),), off), 2 ** (4 - w), ('num', 0), ('num', 2 ** w)))


def sub(k, c):
    kap = cs_kappa(k)
    return cs_sub(k, kap) if kap is not None and k in DIGIT0 else None


def fam(k, r):
    kap = cs_kappa(k)
    return kap is not None and k in DIGIT0 and r == cs_sub(k, kap)

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
