module

public import NativeRustcVmArm.Code.Vm.Decode.Names
public import NativeRustcVmArm.Code.Vm.PhaseM.Names
public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Code.Vm.ReaderWords.Names
public import NativeRustcVmArm.Wire.Decode.Tail

/-!
# `decode` meets its contract

`decode_spec`: the wire's bytes are some bytes `B` in memory (`exists_bytesAt`), the places apart
(`geo_of`); the first reads (`head_spec`), then the stream's count stored, the phase count and the
phases (`tail_spec`): `decodeM B`'s outcome (`Res`).
-/

namespace NativeRustcVmArm.Wire.Decode

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmArm.Vm.Decode

public section

variable [Host] {k : Nat}

/-- What `decode` reaches is its postcondition. -/
theorem post_of {m0 : MachineData} {B : List UInt8} (G : Geo m0 B) {st : MachineState}
    (h : Res m0 B st) : st.pc = retOf m0 ∧ DecodePost m0 st.data := by
  obtain ⟨hpc, hres, hs, hsv⟩ := h
  refine ⟨hpc, fun B' hl hb ↦ ?_, hs, hsv⟩
  have e : B = B' := NativeRustcVm.BytesAt.unique G.bytes hb (by rw [hl, G.len])
  subst e
  exact hres

/-- **`decode` meets its contract.** -/
theorem decode_spec (hp : Placed code k)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hwd : Spec (Labels.label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost)
    (hpm : Spec (Labels.label NativeRustcVmArm.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.Decode.entryLabel) DecodePre DecodePost := by
  intro m0 hpre
  obtain ⟨B, hl, hb⟩ := exists_bytesAt hpre.2.2.2.2.1.1
  have G := geo_of hpre hl hb
  rw [hp.label (j := NativeRustcVmArm.Vm.Decode.entryOffset) NativeRustcVmArm.Vm.Decode.entry_at]
  refine Eventually.bind (head_spec hp G hle hwd) fun st h ↦ ?_
  rcases h with h | ⟨n, ws, c1, hM⟩
  · exact .done _ (post_of G h)
  · exact Eventually.mono (tail_spec hp G hle hpm hM) fun _ h ↦ post_of G h

end

end NativeRustcVmArm.Wire.Decode
