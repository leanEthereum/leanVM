/-
  Rv64mc.Proof.Multilinear.IndexMleOwnT

  `index_mle`'s second total contract (`specT`), beside `IndexMleT.specT`: the same postcondition (`IndexMle.Post`),
  from a point none or owned by the caller (`OwnSliceT.OwnSlice`) where `IndexMleT.PreT` asks it allocated before
  (`Env.Live`). `verify_bus_balance` passes prefixes of a vector's elements, empty with a dangling pointer when the
  vector is; `IndexMleT.PreT` implies `PreT` (`preT_of_indexMleT`), so this contract gives `IndexMleT`'s
  (`specT.indexMleT`). The proof is `IndexMleT.total`'s, the coordinates read through `E::mul`'s and
  `E::square`'s frames by `OwnSlice.load` in place of `EListAt.load`.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `preT_of_indexMleT`, `specT.indexMleT`, `total`
-/

import Rv64mc.Proof.Multilinear.IndexMleT
import Rv64mc.Proof.Multilinear.OwnSliceT

namespace Rv64mc.Proof.Multilinear.IndexMleOwnT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.IndexMle Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Multilinear.IndexMle
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Multilinear.OwnSliceT (OwnSlice)
open Rv64mc.Gen.Verifier.Multilinear.IndexMle (Link tmpl)

/-- The total precondition: the point's coordinates (`SliceArgs`), the slice none or owned by the caller, in a
    window and 8-byte aligned (`OwnSlice`). -/
def PreT (env : Env) (xs : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) (xs.map Model.limbs) ∧ OwnSlice env m (regs .x2) (regs .x10) xs.length

/-- **`index_mle`'s second total contract**: `IndexMle.Post`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ xs, HoldsT env p i need (PreT env xs) (Post xs)

/-- `IndexMleT.PreT` gives `PreT`. -/
theorem preT_of_indexMleT {env : Env} {xs : List E} {regs : Reg → Word} {m : MachineState}
    (h : IndexMleT.PreT env xs regs m) : PreT env xs regs m :=
  ⟨h.1.1, OwnSlice.of_live h.1.2 h.2⟩

/-- **The second contract gives `IndexMleT`'s.** -/
theorem specT.indexMleT {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : specT env p i need) :
    IndexMleT.specT env p i need := fun xs =>
  Isa.TContract.mono (h xs)
    (fun _ _ _ _ ⟨⟨he, hs, hst, hn, hP, hal⟩, hw⟩ => ⟨⟨he, hs, hst, hn, preT_of_indexMleT hP, hal⟩, hw⟩)
    (fun _ _ _ _ _ _ _ h => h) fun _ _ _ _ _ _ _ h => h

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needS : Nat} (hnM : 64 + needM ≤ need) (hnS : 64 + needS ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hsq : Field.ESquareT.specT env p L.square.idx needS) :
    specT env p i need := by
  intro xs
  rv_autoT hp with [hL] using [hmul, hsq]
  all_goals have hlx := hpre_7.1
  all_goals simp only [Layouts.E.byteSize, List.length_map] at hlx
  iterate 2
    have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]; rfl
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  have ho : OwnSlice env m top (regs .x10) xs.length := hpre_2 ▸ hpre_8
  have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  obtain ⟨-, hw, hal⟩ := hpre_8.resolve_left h0
  have hq : (regs .x10).toNat + 16 * (List.map Model.limbs xs).length < 2 ^ 64 := by
    simp only [List.length_map]; omega
  refine Total.loop (IndexMleT.LoopInv env xs ret top regs m) ?_ (xs.length - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hlt, hinv, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = xs.length := ⟨xs.length - 1 - k, by omega⟩
    rw [show xs.length - 1 - k = j by omega] at hinv
    have he0 : (regs .x10 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x10).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hw; omega)
    have hjl : j < xs.length := by omega
    rv_introT hinv
    have hnm := hinv_14.1
    rv_symT hp with [hL] using [hmul, hsq]
    all_goals have ex := OwnSlice.load (j := j) (by simpa using ho) hinv_14 hpre_5 hlim hpre_7 (by simpa using hjl)
    all_goals simp only [List.getElem_map] at ex
    · cases k with
      | zero => exact absurd ((end_iff0 hq (by simp; omega)).2 (by simp; omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, by rw [hret3_18, hret2_18, hret1_18, hcode]⟩
        rw [show xs.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact step_ptr0 _ _
        · rw [body_res _ ex.1 ex.2, st_succ (by omega)]
        · rw [body_res _ ex.1 ex.2, st_succ (by omega)]
        all_goals rw [body_g _ xs[j], st_succ (by omega)]
    all_goals have he := (end_iff0 hq (by simp; omega)).1 hc
    all_goals simp only [List.length_map] at he
    all_goals have hs := st_succ (xs := xs) (j := j) (by omega)
    all_goals rw [he] at hs
    all_goals rw [body_res _ ex.1 ex.2, indexMleRust_st, hs]
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rw [show xs.length - 1 - (xs.length - 1) = 0 by omega]
    rv_closeT
    · exact start_ptr0 _
    · rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_one]; rfl
    · rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_one]; rfl
    all_goals rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_gen]; rfl

end Rv64mc.Proof.Multilinear.IndexMleOwnT

/-- info: 'Rv64mc.Proof.Multilinear.IndexMleOwnT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.IndexMleOwnT.total
