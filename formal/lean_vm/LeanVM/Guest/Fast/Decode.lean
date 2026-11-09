module

public import LeanVM.Guest.Fast.FramesN
public import LeanVM.Guest.Fast.DiscreteLog
public import LeanVM.Guest.EndFinal

/-!
# The guest's decoder, its frames by index

`decode` (`Guest/EndFinal.lean`) reads `main`'s witness through the replayed frame map
`Located.frameVFast`, keyed by the callee's name: it looks the call up in the entry table at the
name's index (`nameIndex`) and reads the frame through the certificate of that name.

* `frameVFastN pre states rd j` (`Fast/FramesN.lean`): the same lookup keyed by the index `j`;
* `decWitN_eq`: `main`'s witness off the restated readers, at the frame map re-keyed by index, is
  `decWitV`'s;
* `decode_eq_numbered`: the deployed decoder is the one reading `decWitN` (`Fast/Main.lean`, the
  restated readers) through `frameVFastN`, the cursor's length by a discrete logarithm
  (`cursorLenWith dl`, `Fast/DiscreteLog.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main LeanVM.Node
open LeanVM.Guest.Located LeanVM.Extraction.Fast

attribute [local instance] lexOrd

@[expose] public section

/-- **The witnesses are equal.** -/
theorem decWitN_eq (σ : Val) (rd : Reader) (V : FrameMap) :
    decWitN σ rd (fun k ↦ V (decoderFunctionName k)) VerifySub.cursorLen =
      decWitV σ rd V VerifySub.vsPiOf := by
  simp only [decWitN, decWitV, xmssSigOfN_eq, sphincsSigOfN_eq, dvWitN_eq, vsPiOfN_eq,
    name_loop2, name_verify_sig_lean_sphincs, name_da_verify, name_verify_sub,
    name_aggregate_claims]

/-- **The deployed decoder reads the frames by index**, through the restated readers, the
cursor's length by any discrete logarithm `dl` (`discreteLog`, `Fast/DiscreteLog.lean`). -/
theorem decode_eq_numbered {dl : K → Option ℕ} (hdl : DiscreteLogSpec dl) {κ : ℕ}
    (L : MemoryImage κ) :
    End.decode L =
      let memT := Extraction.Fast.powTable κ
      let rd := readTable memT L
      let states := statesTable memT (Extraction.Fast.powTable guestProgram.logSize) guestProgram L
        replayFuel ⟨addressOfIndex 0, 1⟩
      let σ := End.mainValWith rd
      ⟨B1.Main.decSeed σ, B1.Main.decStmt σ rd,
        decWitN σ rd (frameVFastN (preTest rd) states rd) (cursorLenWith dl)⟩ := by
  have hV (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
      frameVFastN pre states rd = fun j ↦ frameVFast pre states rd (decoderFunctionName j) :=
    funext (frameVFastN_eq pre states rd)
  simp only [End.decode, hV, cursorLenWith_eq hdl, decWitN_eq]

end
end LeanVM.Guest.Fast
