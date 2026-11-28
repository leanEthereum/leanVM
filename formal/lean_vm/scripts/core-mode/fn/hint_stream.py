"""`hint_stream`'s contracts (`sigc.py`): `hint_stream(stream, n_g)` leaves the proof stream's `e(n_g)` chunks written,
`stream·g^(STREAM_CHUNK·j + d)`, `j < e(n_g)`, `d < STREAM_CHUNK`, as `STREAM_CHUNK` residue runs; its loop
`hint_stream_loop0(xc, n_g, stream)`, over `xc = g^j`, `j < e(n_g)`, hints the chunk `stream·xc^STREAM_CHUNK` and reads
nothing: its termination fact, and the chunks over its counter's range written."""
import fnrules as _R
from fnrules import guest_const
from sigseed import sig, cell, num, ex, run

CH = guest_const('STREAM_CHUNK')
CONTRACTS = {
    'hint_stream': sig(range(4), None, [], postR=[run(cell(0, [(2, 1)]), num(0), ex(3), CH, d) for d in range(CH)]),
    'hint_stream_loop0': sig(range(5), 5, [], term=['(%s, %s)' % (ex(2), ex(3))],
                             postL=[run(cell(0, [(4, 1)]), ex(2), ex(3), CH, d) for d in range(CH)]),
}

# its chunk count `n_g`'s exponent bound, carried from `verify_sub`'s range check (`Res.expFacts`, `EndExec.expOkA_hs`)
EXP_FACTS = _R.lean_def('hint_stream', 'Data', 'expFacts')

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
