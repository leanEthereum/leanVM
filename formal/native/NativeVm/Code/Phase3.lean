module

public import NativeVm.Code.Phase3.Code
public import NativeVm.Code.Phase3.Front3
public import NativeVm.Code.Phase3.Tail
public import NativeVm.Code.Phase2.Kit

/-!
# Phase 3: the bus

The code of `Model.verifyBusBalance` (`P3.code`, `NativeVm.Code.Phase3.Code`), proved against it:
`phase3_ok : Phase3Ok phase3`.

The run is a chain of the model's steps (`Refines.blk_cons`), every state holding `P3.Base` (the
model's state, the inputs, the layout, every word outside `busR`, `claimsR`, `scratchR` the start's)
and the values read so far at their parts of the scratch (`P3.F1` … `P3.FS`): the placements and
the push side's depth (`layoutCode`), the depth's check and the grind, the slot weights and `β`, the
GKR walk and the count root's check, the memory's limbs and the two final counters, the bytecode
share and its value's check (`P3.Front1` … `P3.Front3`). What the model computes from them is one
run of `tailCode` (`P3.tail_spec`): the bus at `busR`, its claims at `claimsR`.
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters P3

/-- **Phase 3**: the bus. -/
def phase3 : Stmt := P3.code

/-- **Phase 3 computes `verifyBusBalance`.** -/
theorem phase3_ok : Phase3Ok phase3 := by
  intro env inp t0 s0 layout rate hc hin hlay
  apply runs_of_refines
  have hb0 : P3.Base env inp s0 layout rate t0 s0 := ⟨hc, hin, ⟨hc.rdi, fun _ _ _ ↦ rfl⟩, hlay⟩
  refine Refines.mono (P := fun t s ↦ P3.Base env inp s0 layout rate t s ∧ True) ?_
    (by rintro t s ⟨rfl, rfl⟩; exact ⟨hb0, trivial⟩) (fun _ _ _ h ↦ h) (fun _ h ↦ h)
  unfold phase3 P3.code verifyBusBalance
  refine Refines.pre_blk layout_pre ?_
  refine Refines.blk_cons checkDepth_ref fun _ ↦ ?_
  refine Refines.blk_cons grind_ref fun _ ↦ ?_
  refine Refines.pre_blk (movi12_pre 16 (2 ^ LeanVM.Protocol.Verifier.busBits) (by decide)
    fun _ _ h ↦ h) ?_
  refine Refines.blk_cons weights_ref fun w ↦ ?_
  refine Refines.blk_cons beta_ref fun b ↦ ?_
  refine Refines.blk_cons gkr_ref fun r ↦ ?_
  obtain ⟨c, p, tv⟩ := r
  refine Refines.blk_cons checkCount_ref fun _ ↦ ?_
  refine Refines.pre_blk (movi12_pre 2 2 (by decide) fun _ _ h ↦ h) ?_
  refine Refines.blk_cons mem_ref fun m ↦ ?_
  refine Refines.blk_cons memFinal_ref fun mf ↦ ?_
  refine Refines.blk_cons bcFinal_ref fun bf ↦ ?_
  refine Refines.blk_cons share_ref fun r ↦ ?_
  obtain ⟨share, bcPoint, value⟩ := r
  refine Refines.blk_cons (bc_ref (r := (share, bcPoint, value))) fun _ ↦ ?_
  refine Refines.pure ?_
  rintro t s ⟨hb, hf, hsh⟩
  have hdep : p.size = dep layout := hf.1.2.2.1
  have hd64 : dep layout < 64 := hf.1.1.1.1.2
  refine WP.blk_cons (WP.mono (tail_spec (weights := w) (beta := b) (point := p) (trees := tv)
    (memory := m) (mf := mf) (bf := bf) (share := share) (bytecodePoint := bcPoint) hb.rdi hb.wp
    hb.hin hb.lay hf.1.1.1.1.1.1 (by rw [hdep]; exact hf.1.1.1.1.1.2) (by omega) hf.1.2.2.2.1
    hf.1.1.1.2.2 hf.1.1.1.2.1 hf.1.1.2 hf.1.2.2.2.2.2 hf.1.2.2.2.2.1 hf.2.2.1 hf.2.1 hf.2.2.2.1
    hf.2.2.2.2 hsh) ?_ fun _ h ↦ h)
  rintro s' ⟨hbus, hcl, hw⟩
  refine WP.blk_nil ⟨hb.rel.wrote3 hb.hin (fun r hr ↦ ?_) hw, ⟨hbus, hcl, Nat.le_of_eq rfl⟩,
    hb.kept.trans ((hw.step.kept hb.rdi).ok3 fun r hr ↦ ?_)⟩ <;>
  · simp only [rs3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ok3_busR
    · exact ok3_claimsR
    · exact ok3_scratchR

/-- info: 'NativeVm.Code.phase3_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase3_ok

/-- Phase 3 never writes `rsp`. -/
theorem phase3_writes_rsp : phase3.writes .rsp = false := by decide +kernel

end NativeVm.Code
