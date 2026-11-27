/-
  Rv64mc.Proof.Multilinear.DotOwnT

  `dot`'s second total contract (`specT`), beside `DotT.specT`: the same postcondition (`Dot.Post`), from slices
  each owned by the caller (`Env.Owned`: below `NEXT`, or in a caller's frame, at or above the stack pointer) where
  `DotT.PreT` asks them allocated before (`Env.Live`, below `NEXT`). Callers pass slices built in their frames
  (`verify_bus_balance::{closure#2}`, `verify_keccak`), which `Live` excludes. `DotT.PreT` implies `PreT`
  (`preT_of_dotT`), so this contract gives `DotT`'s (`specT.dotT`). The proof is `DotT.total`'s, the elements read
  through `E::mul`'s frames by `EListAt.load_owned` in place of `EListAt.load`.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `EListAt.load_owned`, `body_val`, `preT_of_dotT`, `specT.dotT`, `total`
-/

import Rv64mc.Proof.Multilinear.DotT

namespace Rv64mc.Proof.Multilinear.DotOwnT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.Dot Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Multilinear.Dot
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Multilinear.Dot (Link tmpl)

/-- The total precondition: the slices' elements (`SliceArgs`), each slice owned by the caller (`Owned`), and each
    nonempty slice in a window and 8-byte aligned. -/
def PreT (env : Env) (xs ys : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) (xs.map Model.limbs) ∧
    SliceArgs EListAt m (regs .x12) (regs .x13) (ys.map Model.limbs) ∧
    env.Owned m (regs .x2) (regs .x10) (Layouts.E.byteSize * xs.length) ∧
    env.Owned m (regs .x2) (regs .x12) (Layouts.E.byteSize * ys.length) ∧
    (xs.length = 0 ∨ (InWin env (regs .x10) (16 * xs.length) ∧ (regs .x10).toNat % 8 = 0)) ∧
    (ys.length = 0 ∨ (InWin env (regs .x12) (16 * ys.length) ∧ (regs .x12).toNat % 8 = 0))

/-- **`dot`'s second total contract**: `Dot.Post`, from `PreT`, ending the run with `a0 = 2` on slices of
    different lengths. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ xs ys, HoldsT env p i need (PreT env xs ys) (Post xs ys) (Stop := AbortStop)

/-- An allocated slice is owned. -/
theorem owned_of_live {env : Env} {m : MachineState} {top a : Word} {n : Nat} (h : env.Live m a n) :
    env.Owned m top a n :=
  ⟨.inl h, by have := (env.next m).isLt; unfold Env.Live at h; omega⟩

/-- `DotT.PreT` gives `PreT`: a slice allocated before is owned. -/
theorem preT_of_dotT {env : Env} {xs ys : List E} {regs : Reg → Word} {m : MachineState}
    (h : DotT.PreT env xs ys regs m) : PreT env xs ys regs m :=
  ⟨h.1.1, h.1.2.1, owned_of_live h.1.2.2.1, owned_of_live h.1.2.2.2, h.2.1, h.2.2⟩

/-- **The second contract gives `DotT`'s.** -/
theorem specT.dotT {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : specT env p i need) :
    DotT.specT env p i need := fun xs ys =>
  Isa.TContract.mono (h xs ys)
    (fun _ _ _ _ ⟨⟨he, hs, hst, hn, hP, hal⟩, hw⟩ => ⟨⟨he, hs, hst, hn, preT_of_dotT hP, hal⟩, hw⟩)
    (fun _ _ _ _ _ _ _ h => h) fun _ _ _ _ _ _ _ h => h

/-- An element of an owned slice, read through a frame that writes nothing outside its stack. -/
theorem EListAt.load_owned {env : Env} {top : Word} {m M : MachineState} {p : Word} {es : List (Word × Word)}
    {j : Nat} (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (h : EListAt m p es)
    (ho : env.Owned m top p (Layouts.E.byteSize * es.length)) (hj : j < es.length) :
    M.getMem (p + BitVec.ofNat 64 (16 * j)) = es[j].1 ∧ M.getMem (p + BitVec.ofNat 64 (16 * j) + 8#64) = es[j].2 := by
  rcases ho.1 with hl | ha
  · exact EListAt.load hf hnx h hl hj
  · have h' := (h.keep (Env.Frame.keeps_above hf hlim ha fun _ _ h => h)).2 j hj
    simpa [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize] using h'

/-- What one pass computes, from the elements the loop loads through the frame, the slices owned. -/
theorem body_val {env : Env} {top : Word} {m M : MachineState} {xs ys : List E} {regs : Reg → Word} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat)
    (hx : EListAt m (regs .x10) (xs.map Model.limbs)) (hy : EListAt m (regs .x12) (ys.map Model.limbs))
    (hox : env.Owned m top (regs .x10) (Layouts.E.byteSize * xs.length))
    (hoy : env.Owned m top (regs .x12) (Layouts.E.byteSize * ys.length)) (hjx : j < xs.length)
    (hjy : j < ys.length) :
    ((Model.eMul (M.getMem (regs .x10 + BitVec.ofNat 64 (16 * j)), M.getMem (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64))
        (M.getMem (regs .x12 + BitVec.ofNat 64 (16 * j)), M.getMem (regs .x12 + BitVec.ofNat 64 (16 * j) + 8#64))).1 ^^^
        (Model.limbs (acc xs ys j)).1,
      (Model.eMul (M.getMem (regs .x10 + BitVec.ofNat 64 (16 * j)), M.getMem (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64))
        (M.getMem (regs .x12 + BitVec.ofNat 64 (16 * j)), M.getMem (regs .x12 + BitVec.ofNat 64 (16 * j) + 8#64))).2 ^^^
        (Model.limbs (acc xs ys j)).2) =
      Model.limbs (acc xs ys (j + 1)) := by
  have ex := EListAt.load_owned (j := j) hf hnx hlim hx (by simpa using hox) (by simpa using hjx)
  have ey := EListAt.load_owned (j := j) hf hnx hlim hy (by simpa using hoy) (by simpa using hjy)
  simp only [List.getElem_map] at ex ey
  rw [ex.1, ex.2, ey.1, ey.2, acc_succ hjx hjy, step_limbs]

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needF : Nat} (hnM : 64 + needM ≤ need) (hnF : 64 + needF ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hfail : Aborts env p L.assertFailedUsizeUsize.idx needF) :
    specT env p i need := by
  intro xs ys
  rv_autoT hp with [hL] using [hmul, hfail]
  all_goals have hlx := hpre_11
  all_goals have hly := hpre_13
  all_goals simp only [Layouts.E.byteSize] at hlx hly
  all_goals have hlen : xs.length = ys.length := by simpa using len_eq (by simp; omega) (by simp; omega) hc_1
  · intro v hv
    rw [dotRust_acc hlen, Option.some.injEq] at hv
    subst hv
    have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    simp [acc, h0, Model.limbs_zero, Model.eZero]
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  have hox : env.Owned m top (regs .x10) (Layouts.E.byteSize * xs.length) := hpre_2 ▸ ⟨hpre_10, hpre_11⟩
  have hoy : env.Owned m top (regs .x12) (Layouts.E.byteSize * ys.length) := hpre_2 ▸ ⟨hpre_12, hpre_13⟩
  have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  obtain ⟨hwx, halx⟩ := hpre_14.resolve_left h0
  obtain ⟨hwy, haly⟩ := hpre_15.resolve_left (by omega)
  rw [← hlen] at hwy
  have hq : (regs .x12).toNat + 16 * (List.map Model.limbs xs).length + 8 < 2 ^ 64 := by
    have := hpre_17.heapEnd_le
    simp only [List.length_map]; unfold InWin at hwy; omega
  refine Total.loop (DotT.LoopInv env xs ys ret top regs m) ?_ (xs.length - 1) _ _ ?_
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
    have hnm := hinv_14.1
    rv_symT hp with [hL] using [hmul]
    · cases k with
      | zero => exact absurd ((end_iff hq (by simp; omega)).2 (by simp; omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, by rw [hret1_18, hcode]⟩
        rw [show xs.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact step_ptr _ _
        · exact step_ptr _ _
        all_goals rw [← body_val hinv_14 hpre_5 hlim hpre_7 hpre_9 hox hoy (by omega) (by omega)]
    have he := (end_iff hq (by simp; omega)).1 hc
    simp only [List.length_map] at he
    intro v hv
    rw [dotRust_acc hlen, Option.some.injEq] at hv
    subst hv
    rw [← he, ← body_val hinv_14 hpre_5 hlim hpre_7 hpre_9 hox hoy (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rw [show xs.length - 1 - (xs.length - 1) = 0 by omega]
    rv_closeT
    all_goals first
      | exact start_ptr _
      | (rw [show acc xs ys 0 = 0 from rfl, Model.limbs_zero]; rfl)

end Rv64mc.Proof.Multilinear.DotOwnT

/-- info: 'Rv64mc.Proof.Multilinear.DotOwnT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.DotOwnT.total
