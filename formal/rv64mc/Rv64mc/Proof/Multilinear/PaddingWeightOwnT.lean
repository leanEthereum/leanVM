/-
  Rv64mc.Proof.Multilinear.PaddingWeightOwnT

  `padding_weight`'s second total contract (`specT`), beside `PaddingWeightT.specT`: the same postcondition
  (`PaddingWeight.Post`), from a point none or owned by the caller (`OwnSliceT.OwnSlice`) where
  `PaddingWeightT.PreT` asks it allocated before (`Env.Live`). `verify_bus_balance` passes `&point[..log_rows]`, empty
  with a dangling pointer when the vector is; `PaddingWeightT.PreT` implies `PreT` (`preT_of_paddingWeightT`), so
  this contract gives `PaddingWeightT`'s (`specT.paddingWeightT`). The proof is `PaddingWeightT.total`'s, the
  coordinates read through `E::mul`'s frames by `OwnSlice.load` in place of `EListAt.load`.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `preT_of_paddingWeightT`, `specT.paddingWeightT`, `total`
-/

import Rv64mc.Proof.Multilinear.PaddingWeightT
import Rv64mc.Proof.Multilinear.OwnSliceT

namespace Rv64mc.Proof.Multilinear.PaddingWeightOwnT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.PaddingWeight
open Rv64mc.Proof.Multilinear Rv64mc.Proof.Multilinear.PaddingWeight
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Multilinear.OwnSliceT (OwnSlice)
open Rv64mc.Gen.Verifier.Multilinear.PaddingWeight (Link tmpl)

/-- The total precondition: the point's coordinates (`SliceArgs`), the slice none or owned by the caller, in a
    window and 8-byte aligned (`OwnSlice`). -/
def PreT (env : Env) (xs : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) (xs.map Model.limbs) ∧ OwnSlice env m (regs .x2) (regs .x10) xs.length

/-- **`padding_weight`'s second total contract**: `PaddingWeight.Post`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ xs, HoldsT env p i need (PreT env xs) (Post xs)

/-- `PaddingWeightT.PreT` gives `PreT`. -/
theorem preT_of_paddingWeightT {env : Env} {xs : List E} {regs : Reg → Word} {m : MachineState}
    (h : PaddingWeightT.PreT env xs regs m) : PreT env xs regs m :=
  ⟨h.1.1, OwnSlice.of_live h.1.2 h.2⟩

/-- **The second contract gives `PaddingWeightT`'s.** -/
theorem specT.paddingWeightT {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : specT env p i need) :
    PaddingWeightT.specT env p i need := fun xs =>
  OwnSliceT.mono_pre (h xs) fun _ _ => preT_of_paddingWeightT

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : 96 + needM ≤ need) (hmul : Field.EMulT.specT env p L.mul.idx needM) :
    specT env p i need := by
  intro xs
  rv_autoT hp with [hL] using [hmul]
  all_goals have hlx := hpre_7.1
  all_goals simp only [Layouts.E.byteSize, List.length_map] at hlx
  iterate 2
    have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [← post_val, h0]; rfl
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  have ho : OwnSlice env m top (regs .x10) xs.length := hpre_2 ▸ hpre_8
  have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  obtain ⟨-, hw, hal⟩ := hpre_8.resolve_left h0
  refine Total.loop (PaddingWeightT.LoopInv env xs ret top regs m) ?_ (xs.length - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hlt, hinv, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = xs.length := ⟨xs.length - 1 - k, by omega⟩
    rw [show xs.length - 1 - k = j by omega] at hinv
    have he0 : (regs .x10 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x10).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hw; omega)
    have he8 : (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64).toNat = (regs .x10).toNat + (16 * j + 8) := by
      rw [toNat_add_ofNat (by rw [he0]; unfold InWin at hw; omega), he0, Nat.add_assoc]
    have hjl : j < (List.map Model.limbs xs).length := by simp; omega
    rv_introT hinv
    have hnm := hinv_9.1
    have ex := OwnSlice.load (j := j) (by simpa using ho) hinv_9 hpre_5 hlim hpre_7 hjl
    simp only [List.getElem_map] at ex
    rv_symT hp with [hL] using [hmul]
    · cases k with
      | zero => exact absurd ((cnt_iff (by simp; omega) (by simp; omega)).2 (by simp; omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, by rw [hret2_18, hret1_18, hcode]⟩
        rw [show xs.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact cnt_step j
        · exact step_ptr _ _
        · rw [(body_val ex.1 ex.2).1, ← low_succ (by omega)]
        · rw [(body_val ex.1 ex.2).2, ← low_succ (by omega)]
    all_goals have he := (cnt_iff (by simp; omega) (by simp; omega)).1 hc
    all_goals simp only [List.length_map] at he
    all_goals rw [(body_val ex.1 ex.2).1, (body_val ex.1 ex.2).2, ← low_succ (by omega), he, post_val]
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rw [show xs.length - 1 - (xs.length - 1) = 0 by omega]
    rv_closeT
    · exact start_ptr _
    all_goals rw [show low xs (regs .x12) 0 = 1 from rfl, Model.limbs_one]; rfl

end Rv64mc.Proof.Multilinear.PaddingWeightOwnT

/-- info: 'Rv64mc.Proof.Multilinear.PaddingWeightOwnT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.PaddingWeightOwnT.total
