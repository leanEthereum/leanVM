/-
  Rv64mc.Proof.Whir.StackWeightEvaluate

  `StackWeight::evaluate` keeps its contract (`Spec.Whir.StackWeight.spec`), over any program holding its template,
  from the contracts of `eq_eval`, `Placement::eq_above`, `RingWeight::evaluate`, `E::mul` and `slice_index_fail`,
  one variant at a time (`ok_eq`, `ok_ring`, `ok_placed`): the niche tag decides the path, and the others are refuted
  by it (a `Vec`'s capacity is below `2^63`). `rv_auto` stops at the tag test's join (instruction 28, the target of
  a backward branch), so `ok_ring` and `ok_placed` go on with `rv_sym`. What is left by hand is the weight's words
  past the function's own stack stores (`owned_loads`, `keeps_stack`, `keeps_stack_owned`, `live_stack`), across
  `eq_above`'s frame (`keeps_owned_frame`), the prefix `x[..variables]`, and the product.
-/

import Rv64mc.Spec.Whir.StackWeight
import Rv64mc.Spec.Multilinear.EqEval
import Rv64mc.Spec.Multilinear.EqAbove
import Rv64mc.Spec.Field.EMul
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Proof.Whir.Mem
import Rv64mc.Gen.Tmpl.Verifier.StackWeight.Evaluate
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Whir.StackWeightEvaluate

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.StackWeight Rv64mc.Spec.Whir.RingWeight
open Rv64mc.Proof.Whir
open Rv64mc.Gen.Verifier.StackWeight.Evaluate (Link tmpl)

theorem add_ofNat_zero (a : Word) : a + BitVec.ofNat 64 0 = a := by simp

theorem slt_ofNat {c : Nat} (h : c < 2 ^ 63) : (BitVec.ofNat 64 c).slt 0#64 = false := by
  have : (BitVec.ofNat 64 c).toNat = c := by simp; omega
  rw [Bool.eq_false_iff]; intro h'
  rw [BitVec.slt_iff_toInt_lt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at h'
  simp only [this] at h'
  split at h' <;> simp at h' <;> omega

theorem ok_eq (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needE : Nat} (hnE : needE ≤ need) (hn : 64 ≤ need) (pt x : List E)
    (heq : Holds env p L.eqEval.idx needE (Spec.Multilinear.EqEval.Pre env pt x)
      (Spec.Multilinear.EqEval.Post pt x)) :
    Holds env p i need (Pre env (.eq pt) x) (Post (.eq pt) x) := by
  rv_auto hp with [hL] using [heq]
  all_goals have ho : env.Owned m top (regs .x10) 64 := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
  all_goals owned_loads ho hpre_5 hpre_3
  all_goals obtain ⟨htag, ptr, cap, hv, hlv⟩ := hpre_8
  all_goals simp only [Layouts.StackWeight.tagOffset, Layouts.StackWeight.Eq.tag, add_ofNat_zero] at htag
  all_goals have hf := vec_fields hv
  all_goals simp only [Layouts.StackWeight.Eq.f0, Layouts.Vec.ptr, Layouts.Vec.len, Layouts.Vec.cap,
    Nat.reduceAdd] at hf
  all_goals try (rw [htag] at hc; exact absurd hc (by decide))
  all_goals try (rw [htag] at hc_1; exact absurd hc_1 (by decide))
  · omega
  · exact hf.2.1
  · have hb : ptr.toNat + Layouts.E.byteSize * (pt.map Model.limbs).length ≤ env.stackLimit.toNat := by
      simpa using live_below hlv hpre_5
    rw [hf.1]; exact hv.elems.keep (by keeps_stack hb hpre_3)
  · have hb : (regs .x11).toNat + Layouts.E.byteSize * (x.map Model.limbs).length ≤ env.stackLimit.toNat := by
      simpa using live_below hpre_11 hpre_5
    exact hpre_10.keep (by keeps_stack hb hpre_3)
  · rw [hf.1]; live_stack hlv hpre_3
  · live_stack hpre_11 hpre_3
  · exact hret1_16

theorem ok_ring (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needR : Nat} (hnR : needR ≤ need) (hn : 64 ≤ need) (w : Model.RingWeightRust)
    (x : List E) (hrwe : Holds env p L.evaluate.idx needR (EvaluatePre env w x) (EvaluatePost w x)) :
    Holds env p i need (Pre env (.ring w) x) (Post (.ring w) x) := by
  rv_auto hp with [hL] using [hrwe]
  all_goals have ho : env.Owned m top (regs .x10) 64 := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
  all_goals owned_loads ho hpre_5 hpre_3
  all_goals obtain ⟨htag, hw⟩ := hpre_8
  all_goals simp only [Layouts.StackWeight.tagOffset, Layouts.StackWeight.Ring.tag, add_ofNat_zero] at htag
  all_goals try (rw [htag] at hc; exact absurd hc (by decide))
  all_goals try (rw [htag] at hc_1; exact absurd hc_1 (by decide))
  rv_sym hp with [hL] using [hrwe]
  all_goals try (rw [htag] at hc; exact absurd hc (by decide))
  all_goals obtain ⟨⟨pp, pc, hvp, hlp⟩, ⟨cp, cc, hvc, hlc⟩⟩ := hw
  all_goals
    have hop : env.Owned m top (regs .x10 + 8#64) 24 := by
      simpa using Owned.sub (k := 8) (n' := 24) ho (by omega)
  all_goals
    have hoc : env.Owned m top (regs .x10 + 8#64 + 24#64) 24 := by
      rw [BitVec.add_assoc]; exact Owned.sub (k := 32) (n' := 24) ho (by omega)
  · omega
  · refine ⟨pp, pc, ?_, ?_⟩
    · have hb : pp.toNat + Layouts.E.byteSize * (w.point.map Model.limbs).length ≤ env.stackLimit.toNat := by
        simpa using live_below hlp hpre_5
      exact hvp.keep (by simpa using hop.2) (by simpa using (by keeps_stack_owned hop hpre_5 hpre_3 :
        Keeps m _ (regs .x10 + 8#64) 24)) fun h => h.keep (by keeps_stack hb hpre_3)
    · live_stack hlp hpre_3
  · refine ⟨cp, cc, ?_, ?_⟩
    · have hb : cp.toNat + Layouts.E.byteSize * (w.coefficients.map Model.limbs).length ≤ env.stackLimit.toNat := by
        simpa using live_below hlc hpre_5
      exact hvc.keep (by simpa using hoc.2) (by simpa using (by keeps_stack_owned hoc hpre_5 hpre_3 :
        Keeps m _ (regs .x10 + 8#64 + 24#64) 24)) fun h => h.keep (by keeps_stack hb hpre_3)
    · live_stack hlc hpre_3
  · have hb : (regs .x11).toNat + Layouts.E.byteSize * (x.map Model.limbs).length ≤ env.stackLimit.toNat := by
      simpa using live_below hpre_11 hpre_5
    exact hpre_10.keep (by keeps_stack hb hpre_3)
  · live_stack hpre_11 hpre_3
  · exact hret2_16

theorem ok_placed (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needR needA needM needF : Nat} (hnR : 64 + needR ≤ need) (hnA : 64 + needA ≤ need)
    (hnM : needM ≤ need) (hnF : 64 + needF ≤ need) (pl : Model.PlacementRust) (w : Model.RingWeightRust)
    (x : List E)
    (hrwe : Holds env p L.evaluate.idx needR (EvaluatePre env w (x.take pl.variableCount))
      (EvaluatePost w (x.take pl.variableCount)))
    (hea : Holds env p L.eqAbove.idx needA (Spec.Multilinear.EqAbove.Pre env x)
      (Spec.Multilinear.EqAbove.Post x))
    (hmul : Spec.Field.EMul.spec env p L.mul.idx needM)
    (hfail : Spec.Runtime.NoReturn env p L.sliceIndexFail.idx needF) :
    Holds env p i need (Pre env (.placedRing pl w) x) (Post (.placedRing pl w) x) := by
  rv_auto hp with [hL] using [hrwe, hea, hmul, hfail]
  all_goals have ho : env.Owned m top (regs .x10) 64 := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
  all_goals owned_loads ho hpre_5 hpre_3
  all_goals obtain ⟨hvc, hvc', hidx, ⟨pp, pc, hvp, hlp⟩, ⟨cp, cc, hvq, hlq⟩⟩ := hpre_8
  all_goals have hf := vec_fields hvp
  all_goals simp only [Layouts.StackWeight.PlacedRing.f1, Layouts.RingWeight.point, Layouts.Vec.ptr,
    Layouts.Vec.len, Layouts.Vec.cap, Nat.reduceAdd, add_ofNat_zero] at hf
  all_goals try (rw [hf.2.2, slt_ofNat hvp.cap_lt] at hc_1; exact absurd hc_1 (by decide))
  all_goals try exact absurd hc (by decide)
  rv_sym hp with [hL] using [hrwe, hea, hmul, hfail]
  all_goals try exact absurd hc (by decide)
  all_goals try owned_loads ho hpre_5 hpre_3
  all_goals simp only [Layouts.StackWeight.PlacedRing.f0, Layouts.Placement.variables,
    Layouts.Placement.index, Nat.reduceAdd] at hvc hidx
  all_goals have hbx := live_below hpre_11 hpre_5
  all_goals have hbp := live_below hlp hpre_5
  all_goals have hbq := live_below hlq hpre_5
  all_goals rw [← List.length_map (f := Model.limbs)] at hbx hbp hbq
  · exact hpre_10.keep (by keeps_stack hbx hpre_3)
  · live_stack hpre_11 hpre_3
  all_goals
    have hlen : (x.map Model.limbs).length < 2 ^ 64 := by
      have := hpre_10.1; simp only [Layouts.E.byteSize] at this; omega
  all_goals have hle : pl.variableCount ≤ x.length := by rw [hvc] at hc; simpa using ofNat_le_ofNat hvc' hlen hc
  all_goals
    have hF1 : env.Frame top Tactic.F m m1 :=
      Tactic.frame_call (by frame_stack hpre_5 hpre_3) hret1_14
        (Nat.le_of_lt (slot_lt' hpre_3 (by simp only [BitVec.toNat_ofNat]; omega) (by decide)))
  all_goals have hop : env.Owned m top (regs .x10) 24 := by simpa using Owned.sub (k := 0) (n' := 24) ho (by decide)
  all_goals have hoq : env.Owned m top (regs .x10 + 24#64) 24 := Owned.sub (k := 24) (n' := 24) ho (by decide)
  all_goals have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  all_goals simp only [Layouts.StackWeight.PlacedRing.f1, Layouts.RingWeight.point, Layouts.RingWeight.coefficients,
    add_ofNat_zero] at hvp hvq ⊢
  · exact ⟨pp, pc, hvp.keep (by simpa using hop.2)
      (keeps_owned_frame hop hF1 (Nat.le_refl _) (Nat.le_refl _) hlim fun _ _ h => h)
      (fun h => h.keep (Env.Frame.keeps_live hF1 hpre_5 (by simpa using hlp) fun _ _ h => h)), hlp.frame hF1⟩
  · exact ⟨cp, cc, hvq.keep (by simpa using hoq.2)
      (keeps_owned_frame hoq hF1 (Nat.le_refl _) (Nat.le_refl _) hlim fun _ _ h => h)
      (fun h => h.keep (Env.Frame.keeps_live hF1 hpre_5 (by simpa using hlq) fun _ _ h => h)), hlq.frame hF1⟩
  · rw [hvc, List.length_map, List.length_take, Nat.min_eq_left hle]
  · rw [List.map_take]
    exact Rv64mc.Proof.Whir.EListAt.take
      (hpre_10.keep (Env.Frame.keeps_live hF1 hpre_5 (by simpa using hpre_11) fun _ _ h => h)) _
  · have := hpre_11.frame hF1
    unfold Env.Live at this ⊢; simp only [List.length_take]
    have : min pl.variableCount x.length ≤ x.length := Nat.min_le_right _ _
    simp only [Layouts.E.byteSize] at *; omega
  · omega
  · intro v hv
    simp only [Model.StackWeightRust.evaluate, Option.bind_eq_bind] at hv
    obtain ⟨above, ha, hv⟩ := Option.bind_eq_some_iff.1 hv
    obtain ⟨value, hval, hv⟩ := Option.bind_eq_some_iff.1 hv
    cases hv
    have h1 := hret1_16 above (by
      simpa [Spec.Multilinear.EqAbove.placement, Lprog.updReg_apply, Tactic.rf, hvc, hidx,
        Nat.mod_eq_of_lt (show pl.variableCount < 18446744073709551616 from hvc')] using ha)
    have h3 := hret3_16 value hval
    rw [h1.1, h1.2, h3.1, h3.2, Model.eMul_eq]
    exact ⟨rfl, rfl⟩

/-- **`StackWeight::evaluate` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR needE needA needM needF : Nat} (hnR : 64 + needR ≤ need) (hnE : needE ≤ need)
    (hnA : 64 + needA ≤ need) (hnM : needM ≤ need) (hnF : 64 + needF ≤ need)
    (hrwe : evaluateSpec env p L.evaluate.idx needR) (heq : Spec.Multilinear.EqEval.spec env p L.eqEval.idx needE)
    (hea : Spec.Multilinear.EqAbove.spec env p L.eqAbove.idx needA)
    (hmul : Spec.Field.EMul.spec env p L.mul.idx needM)
    (hfail : Spec.Runtime.NoReturn env p L.sliceIndexFail.idx needF) : Spec.Whir.StackWeight.spec env p i need := by
  intro w x
  cases w with
  | eq pt => exact ok_eq env p i L hp hL hnE (by omega) pt x (heq pt x)
  | ring w => exact ok_ring env p i L hp hL (by omega) (by omega) w x (hrwe w x)
  | placedRing pl w => exact ok_placed env p i L hp hL hnR hnA hnM hnF pl w x (hrwe w _) (hea x) hmul hfail

end Rv64mc.Proof.Whir.StackWeightEvaluate
