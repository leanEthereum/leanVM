# Library: verify_tables' landmarks in its body (vt_ir.txt from dump.py, or $VT_IR), found by their
# shape rather than by position, so that the generators follow a renumbered body.
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symev import IR

def nums(s): return [int(x) for x in re.findall(r'\.n (\d+)', s)]

def _only(ps, what):
    assert len(ps) == 1, (what, ps)
    return ps[0]

_P = sorted(IR)

# The six `shared_selector_tables` calls: table `t`'s run length `shared_len[t]` (`SH_LEN[t]`, the
# copy the range check reads) and its two returned tables' copies (`SH_EQ[t]`, `SH_G[t]`).
SH_CALLS = [p for p in _P if IR[p].startswith('.call "shared_selector_tables"')]
assert len(SH_CALLS) == 6, SH_CALLS
SH_LEN = [nums(IR[p])[3] for p in SH_CALLS]
SH_EQ, SH_G = [], []
for _p in SH_CALLS:
    _r = nums(IR[_p])[4:]
    assert len(_r) == 2 and IR[_p + 1] == f'.atom (.copy (.n {_r[0] + 2}) (.n {_r[0]}))' \
        and IR[_p + 2] == f'.atom (.copy (.n {_r[1] + 2}) (.n {_r[1]}))', (_p, IR[_p + 1], IR[_p + 2])
    SH_EQ.append(_r[0] + 2); SH_G.append(_r[1] + 2)
# The first statement after the shared tables (the index MLE's buffer).
SH_END = SH_CALLS[-1] + 3
IDX_BUF = nums(IR[SH_END])[0]
assert IR[SH_END] == f'.atom (.hint (.alloc (.n {IDX_BUF}) 153))', IR[SH_END]

# The zero-check's `g^n = x·τ` witness (`GZN` its variable); the totals' loop ends just before it
# (its last statement the count side's total) and starts after the bytecode share's closing check.
GZN_POS = _only([p for p in _P if '"zc_tau_max"' in IR[p]], 'zc_tau_max')
GZN = nums(IR[GZN_POS])[0]
TOT_HI = GZN_POS - 1
TOT_LO = max(p for p in _P if p < GZN_POS and IR[p].startswith('.atom (.assertEq')) + 1
# `β + 1`, the totals' first sum.
LEAF_BETA1 = nums(IR[TOT_LO + 1])[0]
assert IR[TOT_LO + 1] == f'.atom (.add (.n {LEAF_BETA1}) (.n 14) (.n {nums(IR[TOT_LO])[0]}))'

# The challenge `ξ` (the KECCAK after the witness) and its powers `ξ², ξ³, ξ⁴` multiplying the
# push, pull and count totals.
_k = min(p for p in _P if p > GZN_POS and IR[p].startswith('.atom (.keccak'))
XI = tuple(nums(IR[_k + j])[0] for j in (3, 4, 5))
PUSH_TOTAL, PULL_TOTAL, COUNT_TOTAL = (nums(IR[_k + j])[2] for j in (6, 7, 9))
assert [nums(IR[_k + j])[1] for j in (6, 7, 9)] == list(XI)

# `zc_cprod`, the last argument of the zero-check's loop.
CPROD = nums(_only([IR[p] for p in _P if '"__loop9"' in IR[p]], '__loop9'))[-1]

# The forms' window: from the statement after `eq_prefix_chain` (whose first argument is `zc_peq`)
# to the final check, the last `assertEq`, against the sumcheck's claim; the cursor `CUR` read at
# the window's first statement.
EPC = _only([p for p in _P if IR[p].startswith('.call "eq_prefix_chain"')], 'eq_prefix_chain')
PEQ = nums(IR[EPC])[0]
WLO = EPC + 1
CUR = int(re.match(r'\.atom \(\.load \(\.n \d+\) \(\.n (\d+)\) 0\)$', IR[WLO]).group(1))
WHI = max(p for p in _P if IR[p].startswith('.atom (.assertEq'))
CLAIM = nums(IR[WHI])[1]
