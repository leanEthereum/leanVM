"""`exponent_tables`' contract (`sigc.py`): it returns `g_squares` with its `WIN_TAB_AT + WIN_TAB_LEN` cells written (the
squares, the nibble shares, the windows table), and the words of the runs `[9, 14)`, `[68, 82)`, `[83, 86)` pointers past
which the memory's first `256` cells are written: its contract as written (`contracts/P42.lean`, the bus era's), the
table's length Hotwire's."""
import re
import os
from fnrules import guest_const

N = guest_const('WIN_TAB_AT') + guest_const('WIN_TAB_LEN')


def _written():
    t = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'contracts', 'P42.lean'), encoding='utf-8').read()
    m = re.search(r'noncomputable def Fn\.«exponent_tables»\.csig\s*:\s*Mode\.Sig\s*:=\s*⟨Fn\.«exponent_tables»\.entry, '
                  r'(.*?)⟩\n(?=noncomputable|\nend)', t, re.S)
    s = ' '.join(m.group(1).split())
    old = '[⟨⟨0, 0, [((.fr 2), 1)]⟩, (.num 0), (.num 2284), 1, 0⟩]'
    assert s.count(old) == 1
    s = s.replace(old, '[⟨⟨0, 0, [((.fr 2), 1)]⟩, (.num 0), (.num %d), 1, 0⟩]' % N)
    if True:
        import compiled as C
        parts = C.split_top(s)
        parts[10] = "[]"
        s = ', '.join(parts)
    return s


CONTRACTS = {'exponent_tables': _written()}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
