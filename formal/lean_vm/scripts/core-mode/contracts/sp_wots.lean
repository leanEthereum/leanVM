/-
  LeanVM.Guest.CoreMode.Sig.«sp_wots»

  What a caller knows of compiled functions: their contracts, the source of their
  signatures. `scripts/core-mode/sigc.py` rewrites this file keeping each contract as
  written, or a function's rule file's (`fn/<f>.py` `CONTRACTS`) in its place, and
  stops on a function with neither.
-/

module

public import LeanVM.Guest.Mode.Abs
public import LeanVM.Guest.CoreMode.GlueE.«sp_wots»

set_option linter.style.nameCheck false

namespace LeanVM.Guest

@[expose] public section

noncomputable def Fn.«sp_wots».csig : Mode.Sig :=
  ⟨Fn.«sp_wots».entry, [0, 1, 2, 3, 4, 5], none, [], [], [], [6], [], [], [], [], [], [], [], [],
    []⟩

end

end LeanVM.Guest
