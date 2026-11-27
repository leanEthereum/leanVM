/-
  Rv64mc.Proof.Whir.RingPsiOwnT

  `ring_psi`'s second total contract (`specT`), beside `RingPsiT.specT`: the same postcondition (`RingPsi.Post`),
  from `g` none or owned by the caller (`OwnSliceT.OwnSlice`) where `RingPsiT.PreT` asks it allocated before
  (`Env.Live`). `ring_target` passes `g`, a suffix of the challenges `next_scalars` returned, whose total contract
  says nothing of an empty vector's pointer; `RingPsiT.PreT` implies `PreT` (`preT_of_ringPsiT`), so this contract
  gives `RingPsiT`'s (`specT.ringPsiT`). The proof is `RingPsiT.total`'s, `g` read through `E::mul`'s and
  `E::square`'s frames by `OwnSlice.load` in place of `EListAt.load`.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `body_psi`, `preT_of_ringPsiT`, `specT.ringPsiT`, `total`
-/

import Rv64mc.Proof.Whir.RingPsiT
import Rv64mc.Proof.Multilinear.OwnSliceT

namespace Rv64mc.Proof.Whir.RingPsiOwnT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.RingPsi Rv64mc.Proof.Whir
open Rv64mc.Proof.Whir.RingPsi
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Multilinear.OwnSliceT (OwnSlice)
open Rv64mc.Gen.Verifier.RingSwitch.RingPsi (Link tmpl)

/-- The total precondition: the value's limbs, `g`'s elements (`SliceArgs`), `g` none or owned by the caller, in a
    window and 8-byte aligned (`OwnSlice`). -/
def PreT (env : Env) (v : E) (gs : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  regs .x10 = (Model.limbs v).1 ∧ regs .x11 = (Model.limbs v).2 ∧
    SliceArgs EListAt m (regs .x12) (regs .x13) (gs.map Model.limbs) ∧
    OwnSlice env m (regs .x2) (regs .x12) gs.length

/-- **`ring_psi`'s second total contract**: `RingPsi.Post`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ v gs, HoldsT env p i need (PreT env v gs) (Post v gs)

/-- `RingPsiT.PreT` gives `PreT`. -/
theorem preT_of_ringPsiT {env : Env} {v : E} {gs : List E} {regs : Reg → Word} {m : MachineState}
    (h : RingPsiT.PreT env v gs regs m) : PreT env v gs regs m :=
  ⟨h.1.1, h.1.2.1, h.1.2.2.1, OwnSlice.of_live h.1.2.2.2 h.2⟩

/-- **The second contract gives `RingPsiT`'s.** -/
theorem specT.ringPsiT {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : specT env p i need) :
    RingPsiT.specT env p i need := fun v gs =>
  Multilinear.OwnSliceT.mono_pre (h v gs) fun _ _ => preT_of_ringPsiT

/-- What one pass computes, from the element of `g` the loop loads through the frame, `g` `OwnSlice`. -/
theorem body_psi {env : Env} {top : Word} {m M : MachineState} {v : E} {gs : List E} {q : Word} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hg : EListAt m q (gs.map Model.limbs))
    (ho : OwnSlice env m top q gs.length) (hj : j < gs.length) :
    ((Model.eMul (M.getMem (q + BitVec.ofNat 64 (16 * j)), M.getMem (q + BitVec.ofNat 64 (16 * j) + 8#64))
        ((Model.limbs (acc v gs j).2).1, (Model.limbs (acc v gs j).2).2)).1 ^^^ (Model.limbs (acc v gs j).1).1,
      (Model.eMul (M.getMem (q + BitVec.ofNat 64 (16 * j)), M.getMem (q + BitVec.ofNat 64 (16 * j) + 8#64))
        ((Model.limbs (acc v gs j).2).1, (Model.limbs (acc v gs j).2).2)).2 ^^^ (Model.limbs (acc v gs j).1).2) =
      Model.limbs (acc v gs (j + 1)).1 := by
  have e := OwnSlice.load (j := j) (by simpa using ho) hf hnx hlim hg (by simpa using hj)
  simp only [List.getElem_map] at e
  rw [e.1, e.2, acc_succ hj, RingPsi.step, psi_limbs]

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needS : Nat} (hnM : 64 + needM ≤ need) (hnS : 64 + needS ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hsq : Field.ESquareT.specT env p L.square.idx needS) :
    specT env p i need := by
  intro v gs
  rv_autoT hp with [hL] using [hmul, hsq]
  all_goals have hb := hpre_9.1
  all_goals simp only [Layouts.E.byteSize, List.length_map] at hb
  iterate 2
    have h0 : gs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]; rfl
  have h0 : gs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  have ho : OwnSlice env m top (regs .x12) gs.length := hpre_2 ▸ hpre_10
  have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  obtain ⟨-, hw, hal⟩ := hpre_10.resolve_left h0
  have hq : (regs .x12).toNat + 16 * (List.map Model.limbs gs).length < 2 ^ 64 := by
    simp only [List.length_map]; omega
  refine Total.loop (RingPsiT.LoopInv env v gs ret top regs m) ?_ (gs.length - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hlt, hinv, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = gs.length := ⟨gs.length - 1 - k, by omega⟩
    rw [show gs.length - 1 - k = j by omega] at hinv
    have he0 : (regs .x12 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x12).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hw; omega)
    rv_introT hinv
    have hnm := hinv_14.1
    rv_symT hp with [hL] using [hmul, hsq]
    · cases k with
      | zero => exact absurd ((end_iff hq (by simp; omega)).2 (by simp; omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, by rw [hret2_18, hret1_18, hcode]⟩
        rw [show gs.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact ptr_step _ _
        · rw [← body_psi hinv_14 hpre_5 hlim hpre_9 ho (by omega)]
        · rw [← body_psi hinv_14 hpre_5 hlim hpre_9 ho (by omega)]
        all_goals rw [acc_succ (by omega), RingPsi.step, power_limbs]
    all_goals have he := (end_iff hq (by simp; omega)).1 hc
    all_goals simp only [List.length_map] at he
    all_goals rw [ringPsiRust_acc, ← he, ← body_psi hinv_14 hpre_5 hlim hpre_9 ho (by omega)]
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rw [show gs.length - 1 - (gs.length - 1) = 0 by omega]
    rv_closeT
    · exact ptr_start _
    all_goals rfl

end Rv64mc.Proof.Whir.RingPsiOwnT

/-- info: 'Rv64mc.Proof.Whir.RingPsiOwnT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.RingPsiOwnT.total
