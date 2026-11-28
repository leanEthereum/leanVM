/-
  LeanVM.Guest.CoreMode.Sig.«verify_sig_lean_sphincs»

  What a caller knows of compiled functions: their contracts, the source of their
  signatures. `scripts/core-mode/sigc.py` rewrites this file keeping each contract as
  written, or a function's rule file's (`fn/<f>.py` `CONTRACTS`) in its place, and
  stops on a function with neither.
-/

module

public import LeanVM.Guest.Mode.Abs
public import LeanVM.Guest.CoreMode.GlueE.«verify_sig_lean_sphincs»

set_option linter.style.nameCheck false

namespace LeanVM.Guest

@[expose] public section

noncomputable def Fn.«verify_sig_lean_sphincs».csig : Mode.Sig :=
  ⟨Fn.«verify_sig_lean_sphincs».entry, [0, 1, 2, 3], none, [⟨0, 0, [((.fr 2), 1)]⟩, ⟨0, 1, [((.fr
    2), 1)]⟩, ⟨0, 2, [((.fr 2), 1)]⟩, ⟨0, 3, [((.fr 2), 1)]⟩], [⟨⟨0, 0, [((.fr 3), 1)]⟩, (.num 0),
    (.num 256), 1, 0⟩], [], [], [⟨0, 0, [((.fr 2), 1)]⟩, ⟨0, 1, [((.fr 2), 1)]⟩, ⟨0, 2, [((.fr 2),
    1)]⟩, ⟨0, 3, [((.fr 2), 1)]⟩], [⟨⟨0, 0, [((.fr 3), 1)]⟩, (.num 0), (.num 256), 1, 0⟩], [], [],
    [], [], [], [], []⟩

end

end LeanVM.Guest
