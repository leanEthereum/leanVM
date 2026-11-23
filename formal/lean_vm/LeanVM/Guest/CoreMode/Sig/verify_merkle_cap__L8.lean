/-
  LeanVM.Guest.CoreMode.Sig.«verify_merkle_cap__L8»

  What a caller knows of compiled functions: their contracts, the source of their
  signatures. `scripts/core-mode/sigc.py` rewrites this file keeping each contract as
  written, or a function's rule file's (`fn/<f>.py` `CONTRACTS`) in its place, and
  stops on a function with neither.
-/

module

public import LeanVM.Guest.Mode.Abs
public import LeanVM.Guest.CoreMode.GlueE.«verify_merkle_cap__L8»

set_option linter.style.nameCheck false

namespace LeanVM.Guest

@[expose] public section

noncomputable def Fn.«verify_merkle_cap__L8».csig : Mode.Sig :=
  ⟨Fn.«verify_merkle_cap__L8».entry, [0, 1, 2, 3], none, [], [⟨⟨0, 0, [((.fr 2), 1)]⟩, (.num 4),
    (.num 1024), 1, 0⟩, ⟨⟨0, 0, [((.fr 3), 1)]⟩, (.num 2), (.num 256), 1, 0⟩], [], [4, 5], [],
    [⟨⟨0, 0, [((.fr 2), 1)]⟩, (.num 4), (.num 1024), 1, 0⟩, ⟨⟨0, 0, [((.fr 3), 1)]⟩, (.num 2),
    (.num 256), 1, 0⟩], [], [], [], [], [], [], []⟩

end

end LeanVM.Guest
