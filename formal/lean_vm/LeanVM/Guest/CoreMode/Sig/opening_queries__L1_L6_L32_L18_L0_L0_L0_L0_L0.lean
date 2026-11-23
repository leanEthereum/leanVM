/-
  LeanVM.Guest.CoreMode.Sig.«opening_queries__L1_L6_L32_L18_L0_L0_L0_L0_L0»

  What a caller knows of compiled functions: their contracts, the source of their
  signatures. `scripts/core-mode/sigc.py` rewrites this file keeping each contract as
  written, or a function's rule file's (`fn/<f>.py` `CONTRACTS`) in its place, and
  stops on a function with neither.
-/

module

public import LeanVM.Guest.Mode.Abs
public import LeanVM.Guest.CoreMode.GlueE.«opening_queries__L1_L6_L32_L18_L0_L0_L0_L0_L0»

set_option linter.style.nameCheck false

namespace LeanVM.Guest

@[expose] public section

noncomputable def Fn.«opening_queries__L1_L6_L32_L18_L0_L0_L0_L0_L0».csig : Mode.Sig :=
  ⟨Fn.«opening_queries__L1_L6_L32_L18_L0_L0_L0_L0_L0».entry, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    none, [⟨0, 0, [((.fr 5), 1)]⟩, ⟨0, 1, [((.fr 5), 1)]⟩, ⟨0, 2, [((.fr 5), 1)]⟩, ⟨0, 3, [((.fr
    5), 1)]⟩, ⟨0, 4, [((.fr 5), 1)]⟩, ⟨0, 5, [((.fr 5), 1)]⟩, ⟨0, 6, [((.fr 5), 1)]⟩, ⟨0, 7, [((.fr
    5), 1)]⟩, ⟨0, 8, [((.fr 5), 1)]⟩, ⟨0, 9, [((.fr 5), 1)]⟩, ⟨0, 10, [((.fr 5), 1)]⟩, ⟨0, 11,
    [((.fr 5), 1)]⟩, ⟨0, 0, [((.fr 7), 1)]⟩, ⟨0, 0, [((.fr 8), 1)]⟩, ⟨0, 0, [((.hp 8 0), 1)]⟩, ⟨0,
    1, [((.hp 8 0), 1)]⟩, ⟨0, 2, [((.hp 8 0), 1)]⟩, ⟨0, 3, [((.hp 8 0), 1)]⟩, ⟨0, 4, [((.hp 8 0),
    1)]⟩], [⟨⟨0, 0, [((.fr 7), 1), ((.fr 10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2, 0⟩, ⟨⟨0, 0,
    [((.fr 7), 1), ((.fr 10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2, 1⟩, ⟨⟨0, 0, [((.fr 8), 1), ((.fr
    10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2, 0⟩, ⟨⟨0, 0, [((.fr 8), 1), ((.fr 10), 1)]⟩, (.num 0),
    (.ex (.fr 9) 0), 2, 1⟩], [], [11], [⟨0, 0, [((.fr 7), 1)]⟩, ⟨0, 0, [((.fr 8), 1)]⟩, ⟨0, 0,
    [((.hp 8 0), 1)]⟩, ⟨0, 1, [((.hp 8 0), 1)]⟩, ⟨0, 2, [((.hp 8 0), 1)]⟩, ⟨0, 3, [((.hp 8 0),
    1)]⟩, ⟨0, 4, [((.hp 8 0), 1)]⟩], [⟨⟨0, 0, [((.fr 5), 1)]⟩, (.num 0), (.num 12), 1, 0⟩, ⟨⟨0, 0,
    [((.fr 7), 1), ((.fr 10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2, 0⟩, ⟨⟨0, 0, [((.fr 7), 1), ((.fr
    10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2, 1⟩, ⟨⟨0, 0, [((.fr 8), 1), ((.fr 10), 1)]⟩, (.num 0),
    (.ex (.fr 9) 0), 2, 0⟩, ⟨⟨0, 0, [((.fr 8), 1), ((.fr 10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2,
    1⟩], [], [(⟨⟨0, 0, [((.fr 8), 1), ((.fr 10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2, 0⟩, [0, 1, 2,
    3, 4]), (⟨⟨0, 0, [((.fr 8), 1), ((.fr 10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2, 1⟩, [0, 1, 2, 3,
    4])], [(⟨⟨0, 0, [((.fr 8), 1), ((.fr 10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2, 0⟩, [0, 1, 2, 3,
    4]), (⟨⟨0, 0, [((.fr 8), 1), ((.fr 10), 1)]⟩, (.num 0), (.ex (.fr 9) 0), 2, 1⟩, [0, 1, 2, 3,
    4])], [], [], [], []⟩

end

end LeanVM.Guest
