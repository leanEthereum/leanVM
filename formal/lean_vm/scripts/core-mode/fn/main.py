"""`main`'s rules: its long loop `main_loop2` checked in windows of its own sizes (`windows.py`)."""

# instructions per code window (`core.py`), per pairing window (`pair.py`), per frame walk window (`frame_gen.py`)
CORE_WIN = {'main_loop2': 6144}
PAIR_WIN = {'main_loop2': 2048}
FRAME_WIN = {'main_loop2': 4000}

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = []
