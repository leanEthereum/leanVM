"""`keccak_layer`'s rules: its loops' and its own reads of the proof stream."""
from fnrules import val, valf, lean_def

CAPE = 2 ** 62

# its eight-round loop and its remainder loop read the stream past their cursors (`CoreMode.stLoops`), as its Lean data
# says
ST_LOOPS = {e[0]: e[1:] for e in lean_def('keccak_layer', 'Data', 'stLoops')}

# `keccak_layer__L{first}`'s last record's cursor (`CoreMode.layCur`), its stream, its pack rounds' words
LAY_CUR = {'keccak_layer__L0': val('keccak_layer__L0', 'cursor@2'), 'keccak_layer__L1': val('keccak_layer__L1', 'cursor@2')}
STREAM, PACK = valf('keccak_layer', 'stream'), (valf('keccak_layer', 'step_g'), valf('keccak_layer', 'rem_g'))


def sub(k, c):
    """`CoreMode.laySt`: a read `c` words past its last record's cursor, `c < 36`, one of its stream's
    `[stream]·[0, 8192)`."""
    if k in LAY_CUR and c[0] == ((LAY_CUR[k], 1),) and c[1] < 36:
        return ('sub', c, ((((STREAM, 1),), 0), 1, ('num', 0), ('num', 8192)))
    return None


def fam(k, r):
    """`CoreMode.layQC` (`EndExec.LayQ`): a read past its last record's cursor (`sub`), its pack rounds' words
    `e(step_g), e(rem_g) < 32`, under branch conditions."""
    if k not in LAY_CUR:
        return False
    if r[0] == 'under':
        return fam(k, r[2])
    if r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'num':
        return r[1][1] in PACK and 32 <= r[2][1] < CAPE
    return r[0] == 'sub' and sub(k, r[1]) == r

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
