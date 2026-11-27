/-
  Rv64mc.Proof.Multilinear.EqEvalOwnT

  `eq_eval`'s second total contract (`specT`), beside `EqEvalT.specT`: the same postcondition (`EqEval.Post`), from
  slices each none or owned by the caller (`OwnSliceT.OwnSlice`) where `EqEvalT.PreT` asks them allocated before
  (`Env.Live`). `Placement::eq_above` passes `selector_point`'s vector, empty with a dangling pointer when the point
  has no coordinate above the window, and the point's suffix; `EqEvalT.PreT` implies `PreT` (`preT_of_eqEvalT`), so
  this contract gives `EqEvalT`'s (`specT.eqEvalT`). The proof is `EqEvalT.total`'s, the elements read through
  `E::mul`'s frames by `OwnSlice.load` in place of `EListAt.load`.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `body_val`, `preT_of_eqEvalT`, `specT.eqEvalT`, `total`
-/

import Rv64mc.Proof.Multilinear.EqEvalT
import Rv64mc.Proof.Multilinear.OwnSliceT

namespace Rv64mc.Proof.Multilinear.EqEvalOwnT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.EqEval Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Multilinear.EqEval
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Multilinear.OwnSliceT (OwnSlice)
open Rv64mc.Gen.Verifier.Multilinear.EqEval (Link tmpl)

/-- The total precondition: the slices' elements (`SliceArgs`), each slice none or owned by the caller, in a window
    and 8-byte aligned (`OwnSlice`). -/
def PreT (env : Env) (xs ys : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) (xs.map Model.limbs) ∧
    SliceArgs EListAt m (regs .x12) (regs .x13) (ys.map Model.limbs) ∧
    OwnSlice env m (regs .x2) (regs .x10) xs.length ∧ OwnSlice env m (regs .x2) (regs .x12) ys.length

/-- **`eq_eval`'s second total contract**: `EqEval.Post`, from `PreT`, ending the run with `a0 = 2` on slices of
    different lengths. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ xs ys, HoldsT env p i need (PreT env xs ys) (Post xs ys) (Stop := AbortStop)

/-- `EqEvalT.PreT` gives `PreT`: a slice allocated before, nonempty in a window and aligned, is owned. -/
theorem preT_of_eqEvalT {env : Env} {xs ys : List E} {regs : Reg → Word} {m : MachineState}
    (h : EqEvalT.PreT env xs ys regs m) : PreT env xs ys regs m :=
  ⟨h.1.1, h.1.2.1, OwnSlice.of_live h.1.2.2.1 h.2.1, OwnSlice.of_live h.1.2.2.2 h.2.2⟩

/-- **The second contract gives `EqEvalT`'s.** -/
theorem specT.eqEvalT {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : specT env p i need) :
    EqEvalT.specT env p i need := fun xs ys =>
  OwnSliceT.mono_pre (h xs ys) fun _ _ => preT_of_eqEvalT

/-- What one pass computes, from the elements the loop loads through the frame, the slices `OwnSlice`. -/
theorem body_val {env : Env} {top : Word} {m M : MachineState} {xs ys : List E} {regs : Reg → Word} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat)
    (hx : EListAt m (regs .x10) (xs.map Model.limbs)) (hy : EListAt m (regs .x12) (ys.map Model.limbs))
    (hox : OwnSlice env m top (regs .x10) xs.length) (hoy : OwnSlice env m top (regs .x12) ys.length)
    (hjx : j < xs.length) (hjy : j < ys.length) :
    Model.eMul ((Model.limbs (acc xs ys j)).1, (Model.limbs (acc xs ys j)).2)
        (M.getMem (regs .x10 + BitVec.ofNat 64 (16 * j)) ^^^ M.getMem (regs .x12 + BitVec.ofNat 64 (16 * j)) ^^^ 1#64,
          M.getMem (regs .x12 + BitVec.ofNat 64 (16 * j) + 8#64) ^^^
            M.getMem (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64)) =
      Model.limbs (acc xs ys (j + 1)) := by
  have ex := OwnSlice.load (j := j) (by simpa using hox) hf hnx hlim hx (by simpa using hjx)
  have ey := OwnSlice.load (j := j) (by simpa using hoy) hf hnx hlim hy (by simpa using hjy)
  simp only [List.getElem_map] at ex ey
  rw [ex.1, ex.2, ey.1, ey.2, acc_succ hjx hjy, step_limbs]

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needF : Nat} (hnM : 48 + needM ≤ need) (hnF : 48 + needF ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hfail : Aborts env p L.assertFailedUsizeUsize.idx needF) :
    specT env p i need := by
  intro xs ys
  rv_autoT hp with [hL] using [hmul, hfail]
  all_goals have hlx := hpre_7.1
  all_goals have hly := hpre_9.1
  all_goals simp only [Layouts.E.byteSize, List.length_map] at hlx hly
  all_goals have hlen : xs.length = ys.length := by simpa using len_eq (by simp; omega) (by simp; omega) hc_1
  · intro v hv
    rw [eqEvalRust_acc hlen, Option.some.injEq] at hv
    subst hv
    have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    simp [acc, h0, Model.limbs_one, Model.eOne]
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  have hox : OwnSlice env m top (regs .x10) xs.length := hpre_2 ▸ hpre_10
  have hoy : OwnSlice env m top (regs .x12) ys.length := hpre_2 ▸ hpre_11
  have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  obtain ⟨-, hwx, halx⟩ := hpre_10.resolve_left h0
  obtain ⟨-, hwy, haly⟩ := hpre_11.resolve_left (by omega)
  rw [← hlen] at hwy
  have hq : (regs .x12).toNat + 16 * (List.map Model.limbs xs).length + 8 < 2 ^ 64 := by
    have := hoy.end_lt (by omega); simp only [List.length_map]; omega
  refine Total.loop (EqEvalT.LoopInv env xs ys ret top regs m) ?_ (xs.length - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hlt, hinv, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = xs.length := ⟨xs.length - 1 - k, by omega⟩
    rw [show xs.length - 1 - k = j by omega] at hinv
    have hx0 : (regs .x10 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x10).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hwx; omega)
    have hx8 : (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64).toNat = (regs .x10).toNat + (16 * j + 8) := by
      rw [toNat_add_ofNat (by rw [hx0]; unfold InWin at hwx; omega), hx0, Nat.add_assoc]
    have hy0 : (regs .x12 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x12).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hwy; omega)
    have hy8 : (regs .x12 + BitVec.ofNat 64 (16 * j) + 8#64).toNat = (regs .x12).toNat + (16 * j + 8) := by
      rw [toNat_add_ofNat (by rw [hy0]; unfold InWin at hwy; omega), hy0, Nat.add_assoc]
    rv_introT hinv
    have hnm := hinv_16.1
    rv_symT hp with [hL] using [hmul]
    · cases k with
      | zero => exact absurd ((end_iff hq (by simp; omega)).2 (by simp; omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, by rw [hret1_18, hcode]⟩
        rw [show xs.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact step_ptr _ _
        · exact step_ptr _ _
        all_goals rw [body_val hinv_16 hpre_5 hlim hpre_7 hpre_9 hox hoy (by omega) (by omega)]
    have he := (end_iff hq (by simp; omega)).1 hc
    simp only [List.length_map] at he
    intro v hv
    rw [eqEvalRust_acc hlen, Option.some.injEq] at hv
    subst hv
    rw [← he, ← body_val hinv_16 hpre_5 hlim hpre_7 hpre_9 hox hoy (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rw [show xs.length - 1 - (xs.length - 1) = 0 by omega]
    rv_closeT
    all_goals first
      | exact start_ptr _
      | (rw [show acc xs ys 0 = 1 from rfl, Model.limbs_one]; rfl)

end Rv64mc.Proof.Multilinear.EqEvalOwnT

/-- info: 'Rv64mc.Proof.Multilinear.EqEvalOwnT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.EqEvalOwnT.total
