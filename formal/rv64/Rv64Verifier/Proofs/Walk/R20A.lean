import Rv64Verifier.Proofs.Walk.TailG

/-!
# `walk` R20, `verify_keccak`: the contract as `walk` calls it, and the mirror's phase

`VerifyKeccakSpecE` is `Gkr.VerifyKeccakSpec` with `output`'s length the constant `25` (the caller
at `0x80003ed4` leaves `a7` as it was: the compiled `verify_keccak` never reads it) and an empty
instance's pointer unconstrained (an empty `Vec`'s dangling pointer has no bound). `kOpOf`: the
openings as the result's memory holds them. `keccakPhase_run`: `keccakPhaseRust` is the stream's
position, `verify_keccak` on the KECCAK table's point and output lanes, the position again.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus Rv64Verifier.Gkr Rv64Verifier.Model.Gkr

/-- `VerifyKeccakPre` with `output` 25 elements and an empty instance's pointer anywhere. -/
structure VerifyKeccakPreE (s : MachineState) : Prop extends TPre 96 verifyKeccakStack s where
  depth : s.getReg .x13 = 12
  checked : Checked s (s.getReg .x11)
  inst : kInstLen s = 0 ∨ Region (kInst s) (24 * kInstLen s)
  output : Region (kOutput s) (24 * 25)
  instFree : kInstLen s = 0 ∨ Outside s (kInst s) (24 * kInstLen s)
  outputFree : Outside s (kOutput s) (24 * 25)
  instStack : Apart (kInst s) (24 * kInstLen s) (stackLo s verifyKeccakStack) verifyKeccakStack
  outputStack : Apart (kOutput s) (24 * 25) (stackLo s verifyKeccakStack) verifyKeccakStack
  instOut : Apart (kInst s) (24 * kInstLen s) (s.getReg .x10) 96
  outputOut : Apart (kOutput s) (24 * 25) (s.getReg .x10) 96
  instSelf : Apart (kInst s) (24 * kInstLen s) (s.getReg .x11 + 8) 344
  outputSelf : Apart (kOutput s) (24 * 25) (s.getReg .x11 + 8) 344

/-- `VerifyKeccakPost` with `output` 25 elements. -/
structure VerifyKeccakPostE (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : ∀ T, TranscriptAt s (s.getReg .x11) T →
    match (verifyKeccakRust (shapeOf s) (eListAt s (kInst s) (kInstLen s))
        (eListAt s (kOutput s) 25)).run T with
    | some (o, T') => vecCap t (s.getReg .x10) ≠ errNiche ∧
        NewVecE s t (s.getReg .x10) o.inputs.1 ∧ NewVecE s t (s.getReg .x10 + 24) o.inputs.2 ∧
        OutputsAt s t (s.getReg .x10 + 48) o.outputs ∧ TranscriptAt t (s.getReg .x11) T'
    | none => vecCap t (s.getReg .x10) = errNiche
  frame : TFrame 96 verifyKeccakStack s t

/-- `verify_keccak`'s contract as `walk` calls it. -/
abbrev VerifyKeccakSpecE : Prop :=
  FunSpec Image.code 0x80008e34 VerifyKeccakPreE VerifyKeccakPostE

/-- The openings at `a` (96 bytes). -/
def kOpOf (v : MachineState) (a : Word) : KeccakOpenings :=
  ⟨if vecCap v (a + 48) = errNiche then none else some (vecEs v (a + 48), eAt v (a + 72)),
    (vecEs v a, vecEs v (a + 24))⟩

theorem kOpOf_eq {s t : MachineState} {a : Word} {o : KeccakOpenings}
    (h1 : NewVecE s t a o.inputs.1) (h2 : NewVecE s t (a + 24) o.inputs.2)
    (h3 : OutputsAt s t (a + 48) o.outputs) : kOpOf t a = o := by
  rcases o with ⟨out, i1, i2⟩
  simp only [kOpOf, h1.elems, h2.elems]
  congr 1
  rcases out with _ | ⟨p, x⟩
  · simp only [OutputsAt] at h3; rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
  · simp only [OutputsAt] at h3
    obtain ⟨hc, hv, hx⟩ := h3
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc), hv.elems, ← hx, show a + 48 + 24 = a + 72 by bv_omega]

/-- `keccakPhaseRust`: the position, `verify_keccak`, the position. -/
theorem keccakPhase_run (layout : LayoutMirror.LayoutRust) (evs : List (List E × List E))
    (h5 : 5 < evs.length) (h65 : 65 ≤ evs[5].2.length) (T : TState) :
    (keccakPhaseRust layout evs).run T =
      ((verifyKeccakRust ⟨layout.keccakLogSteps, 12⟩ evs[5].1
        ((evs[5].2.drop 40).take 25)).run T).bind fun r ↦
        some ((r.1, T.streamOffset, r.2.streamOffset), r.2) := by
  have hs : sliceRust evs[5].2 LayoutMirror.keccakOutRust
      (LayoutMirror.keccakOutRust + LayoutMirror.stateLanesRust) =
      some ((evs[5].2.drop 40).take 25) := by
    have e1 : LayoutMirror.keccakOutRust = 40 := by decide
    have e2 : LayoutMirror.stateLanesRust = 25 := rfl
    rw [e1, e2, sliceRust]
    split_ifs with hc
    · rfl
    · exact absurd ⟨by omega, by omega⟩ hc
  have hg : evs[LayoutMirror.opKeccakRust]? = some evs[5] := List.getElem?_eq_getElem h5
  simp only [keccakPhaseRust, hg, TM.ofOption, StateT.run_bind,
    LayoutMirror.keccakDepthRust, StateT.run_pure, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rw [hs]
  have hp : ∀ T : TState, StateT.run TM.streamPosition T = some (T.streamOffset, T) := fun _ ↦ rfl
  simp only [StateT.run_pure, Option.pure_def, Option.bind_some, hp]

end Rv64Verifier.Proofs.Walk
