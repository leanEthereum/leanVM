"""`keccak_layer`'s rules: its loops' and its own reads of the proof stream."""

CAPE = 2 ** 62

# its eight-round loop and its remainder loop read the stream past the cursors `20` and `14`, its caller's cell `17`
# the stream, `16` and `2` words an iteration (`CoreMode.stLoops`)
ST_LOOPS = {'keccak_layer__L0_loop0': (17, 20, 16), 'keccak_layer__L1_loop0': (17, 20, 16),
            'keccak_layer__L0_loop1': (17, 14, 2), 'keccak_layer__L1_loop1': (17, 14, 2)}

# `keccak_layer__L{first}`'s last record's cursor (`CoreMode.layCur`), its stream its parameter `15`
LAY_CUR = {'keccak_layer__L0': 744, 'keccak_layer__L1': 764}


def sub(k, c):
    """`CoreMode.laySt`: a read `c` words past its last record's cursor, `c < 36`, one of its stream's
    `[15]·[0, 8192)`."""
    if k in LAY_CUR and c[0] == ((LAY_CUR[k], 1),) and c[1] < 36:
        return ('sub', c, ((((15, 1),), 0), 1, ('num', 0), ('num', 8192)))
    return None


def fam(k, r):
    """`CoreMode.layQC` (`EndExec.LayQ`): a read past its last record's cursor (`sub`), its pack rounds' words
    `e(p9), e(p10) < 32`, under branch conditions."""
    if k not in LAY_CUR:
        return False
    if r[0] == 'under':
        return fam(k, r[2])
    if r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'num':
        return r[1][1] in (9, 10) and 32 <= r[2][1] < CAPE
    return r[0] == 'sub' and sub(k, r[1]) == r

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/ResStL.lean',
    'LeanVM/Guest/CoreMode/Fam/ResStP.lean',
    'LeanVM/Guest/CoreMode/Fn/keccak_layer/*.lean',
]
