"""`is_zero`'s contract (`sigc.py`)."""
from sigseed import sig

# `is_zero(word)`: no heap cell read or written, its result in frame cell `3`.
CONTRACTS = {'is_zero': sig(range(3), None, [3])}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
