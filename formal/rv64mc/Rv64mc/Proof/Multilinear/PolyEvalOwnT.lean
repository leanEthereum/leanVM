/-
  Rv64mc.Proof.Multilinear.PolyEvalOwnT

  `poly_eval`'s second total contract (`specT`), beside `PolyEvalT.specT`: the same postcondition (`PolyEval.Post`),
  from a slice none or owned by the caller (`OwnSliceT.OwnSlice`) where `PolyEvalT.PreT` asks it allocated before
  (`Env.Live`). Its callers pass vectors whose builders' total contracts give `VecT`, which says nothing of an empty
  vector's pointer; `PolyEvalT.PreT` implies `PreT` (`preT_of_polyEvalT`), so this contract gives `PolyEvalT`'s
  (`specT.polyEvalT`). The proof is `PolyEvalT.total`'s, the coefficients read through `E::mul`'s frames by
  `OwnSlice.load` in place of `EListAt.load`.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `body_val`, `preT_of_polyEvalT`, `specT.polyEvalT`, `total`
-/

import Rv64mc.Proof.Multilinear.PolyEvalT
import Rv64mc.Proof.Multilinear.OwnSliceT

namespace Rv64mc.Proof.Multilinear.PolyEvalOwnT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.PolyEval Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Multilinear.PolyEval
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Multilinear.OwnSliceT (OwnSlice)
open Rv64mc.Gen.Verifier.Multilinear.PolyEval (Link tmpl)

/-- The total precondition: the coefficients (`SliceArgs`), the slice none or owned by the caller, in a window and
    8-byte aligned (`OwnSlice`), and the point's limbs. -/
def PreT (env : Env) (cs : List E) (pt : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x10) (regs .x11) (cs.map Model.limbs) ∧ OwnSlice env m (regs .x2) (regs .x10) cs.length ∧
    regs .x12 = (Model.limbs pt).1 ∧ regs .x13 = (Model.limbs pt).2

/-- **`poly_eval`'s second total contract**: `PolyEval.Post`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ cs pt, HoldsT env p i need (PreT env cs pt) (Post cs pt)

/-- `PolyEvalT.PreT` gives `PreT`. -/
theorem preT_of_polyEvalT {env : Env} {cs : List E} {pt : E} {regs : Reg → Word} {m : MachineState}
    (h : PolyEvalT.PreT env cs pt regs m) : PreT env cs pt regs m :=
  ⟨h.1.1, OwnSlice.of_live h.1.2.1 h.2, h.1.2.2⟩

/-- **The second contract gives `PolyEvalT`'s.** -/
theorem specT.polyEvalT {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : specT env p i need) :
    PolyEvalT.specT env p i need := fun cs pt =>
  Isa.TContract.mono (h cs pt)
    (fun _ _ _ _ ⟨⟨he, hs, hst, hn, hP, hal⟩, hw⟩ => ⟨⟨he, hs, hst, hn, preT_of_polyEvalT hP, hal⟩, hw⟩)
    (fun _ _ _ _ _ _ _ h => h) fun _ _ _ _ _ _ _ h => h

/-- What one pass computes, from the coefficient the loop loads through the frame, the slice `OwnSlice`. -/
theorem body_val {env : Env} {top : Word} {m M : MachineState} {cs : List E} {pt : E} {regs : Reg → Word} {i : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hx : EListAt m (regs .x10) (cs.map Model.limbs))
    (ho : OwnSlice env m top (regs .x10) cs.length) (hi : i < cs.length) :
    ((Model.eMul ((Model.limbs (hor cs pt (i + 1))).1, (Model.limbs (hor cs pt (i + 1))).2)
        ((Model.limbs pt).1, (Model.limbs pt).2)).1 ^^^ M.getMem (regs .x10 + BitVec.ofNat 64 (16 * i)),
      (Model.eMul ((Model.limbs (hor cs pt (i + 1))).1, (Model.limbs (hor cs pt (i + 1))).2)
        ((Model.limbs pt).1, (Model.limbs pt).2)).2 ^^^ M.getMem (regs .x10 + BitVec.ofNat 64 (16 * i) + 8#64)) =
      Model.limbs (hor cs pt i) := by
  have ex := OwnSlice.load (j := i) (by simpa using ho) hf hnx hlim hx (by simpa using hi)
  simp only [List.getElem_map] at ex
  rw [ex.1, ex.2, hor_step hi, step_limbs]

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : 64 + needM ≤ need) (hmul : Field.EMulT.specT env p L.mul.idx needM) :
    specT env p i need := by
  intro cs pt
  rv_autoT hp with [hL] using [hmul]
  all_goals have hlx := hpre_7.1
  all_goals simp only [Layouts.E.byteSize, List.length_map] at hlx
  iterate 2
    have h0 : cs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]
    simp [Model.polyEvalRust, Model.limbs_zero, Model.eZero]
  have h0 : cs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  have ho : OwnSlice env m top (regs .x10) cs.length := hpre_2 ▸ hpre_8
  have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  obtain ⟨-, hw, hal⟩ := hpre_8.resolve_left h0
  refine Total.loop (PolyEvalT.LoopInv env cs pt ret top regs m) ?_ (cs.length - 1) _ _ ?_
  · intro j R M hI ih
    obtain ⟨hj, hinv, hcode⟩ := hI
    have he0 : (regs .x10 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x10).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hw; omega)
    have he8 : (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64).toNat = (regs .x10).toNat + (16 * j + 8) := by
      rw [toNat_add_ofNat (by rw [he0]; unfold InWin at hw; omega), he0, Nat.add_assoc]
    rv_introT hinv
    have hnm := hinv_14.1
    rv_symT hp with [hL] using [hmul]
    · cases j with
      | zero => exact absurd ((exit_iff (by omega)).2 rfl) hc
      | succ j =>
        refine ih j _ _ (by omega) ⟨by omega, ?_, by rw [hret1_18, hcode]⟩
        rv_closeT
        · exact back_ptr _ _
        all_goals rw [← body_val hinv_14 hpre_5 hlim hpre_7 ho hj]
    all_goals obtain rfl := (exit_iff (by omega)).1 hc
    all_goals rw [← hor_zero, ← body_val hinv_14 hpre_5 hlim hpre_7 ho hj]
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rv_closeT
    · rw [List.length_map]; exact PolyEval.start_ptr (by omega) (by omega)
    all_goals rw [show cs.length - 1 + 1 = cs.length by omega, hor_len, Model.limbs_zero]; rfl

end Rv64mc.Proof.Multilinear.PolyEvalOwnT

/-- info: 'Rv64mc.Proof.Multilinear.PolyEvalOwnT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.PolyEvalOwnT.total
