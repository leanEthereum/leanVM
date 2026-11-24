/-
  LeanVM.Guest.B1.Sig.XmssPathPops

  The hint generator's cells are the guest's: a cell of a cell's bytes, and of a 128-bit value.
-/

module

public import LeanVM.Guest.B1.Sig.XmssWinPops
public import LeanVM.Guest.B1.Sig.XmssSegPathC
public import LeanVM.Guest.B1.Sig.XmssSegCoreC
public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Guest.Hints
import LeanVM.Protocol.Verifier.Load

/-!
# The hint generator's cells

* `cellOfBytes_cellBytes`: `Hints.cellOfBytes` of a cell's bytes is the cell;
* `cell128_eq`: `Hints.cell128` is `cellOf128`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory LeanVM.Protocol.Verifier LeanVM.Guest.Value.Keccak

@[expose] public section

variable {rd : Reader}

theorem cellOfBytes_cellBytes (x : E) : Hints.cellOfBytes (cellBytes x) = x := by
  have hl : ∀ a : K, (K.toBytes a).length = 8 := fun a => by simp [K.toBytes, LeanVM.Protocol.KeccakHash.wordBytes]
  conv_rhs => rw [eq_ofLimbs x]
  rw [Hints.cellOfBytes, cellBytes, kOfBytes_kBytes_append, List.drop_left' (hl _),
    ← List.append_nil (K.toBytes (x.limb 1)), kOfBytes_kBytes_append]

/-- The hint generator's cell of a 128-bit value is the guest's. -/
theorem cell128_eq (v : BitVec 128) : Hints.cell128 v = cellOf128 v := by
  conv_lhs => rw [← cellVal_cellOf128 v]
  rw [Hints.cell128, bytesLE_cellVal, cellOfBytes_cellBytes]

end
end LeanVM.Guest.B1.Sig
