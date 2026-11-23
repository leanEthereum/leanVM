"""`decode_query_windows`' contracts (`sigc.py`)."""

# `decode_query_windows__L14_L2`'s windows: its last window has four cells and the frame cell eight past it is
# not written at the return (the compiler reuses it), so that pointer's cells `[0, 8)`, the others' `[0, 9)`.
CONTRACTS = {'decode_query_windows__L14_L2': '[0, 1, 2, 3, 4, 5], none, [], [⟨⟨0, 0, [((.fr 5), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [], [], [], [⟨⟨0, 0, [((.fr 3), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 4), 1)]⟩, (.num 0), (.num 9), 1, 0⟩, ⟨⟨0, 0, [((.fr 5), 1)]⟩, (.num 0), (.num 64), 1, 0⟩], [], [], [(⟨⟨0, 0, [((.fr 4), 1)]⟩, (.num 0), (.num 8), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7, 8]), (⟨⟨0, 0, [((.fr 4), 1)]⟩, (.num 8), (.num 9), 1, 0⟩, [0, 1, 2, 3, 4, 5, 6, 7])], [], [], [], []'}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
