/-
  LeanVM.Guest.EndKnow

  B2 at `main` for a valid execution of the guest: `main`'s body at its frame, its calls located,
  and the public input's cells.
-/

module

public import LeanVM.Guest.EndLoc
public import LeanVM.Guest.End
public import LeanVM.Guest.DecoderProgram

/-!
# `main` on a valid execution

`mainBodyL_of`: on a valid execution of the guest, B2 (`B2SoundL`) gives `main`'s body under the
valuation of its certificate's cells at `fp = 1` (`Check.valG L 1 (certOf 1)`), each call located
(`Located.RLg`), and the memory holds the public input's digest in the two cells `main` loads
(`pub_loads`). `coreOf_one`: the compiled function `1` is `main`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The compiled function `1` is `main`. -/
theorem coreOf_one : coreOf 1 = fn% «main» := rfl

/-- **B2 at `main`, located, for a valid execution**: `main`'s body under its frame's valuation,
its calls located, and the public input's cells at `g^0`, `g^1`. -/
theorem mainBodyL_of (hb2 : B2SoundL) {input : PublicInput}
    {t : Execution guestProgram} (hv : ValidExecution guestProgram input t) :
    Stmt.HoldsList (Located.RLg t.memory) t.memory.read (valG t.memory 1 (certOf 1))
      (fn% «main»).body False (fun rs ↦ rs = []) ∧
    LoadHolds t.memory.read 1 0 (digestHalves (publicInputDigest input)).1 ∧
    LoadHolds t.memory.read 1 1 (digestHalves (publicInputDigest input)).2 :=
  ⟨coreOf_one ▸ mainBodyL_of_safe hb2 hv.1.1 hv.1.2.1 (safe_of_validExecution hv), pub_loads hv⟩

end
end LeanVM.Guest.End
