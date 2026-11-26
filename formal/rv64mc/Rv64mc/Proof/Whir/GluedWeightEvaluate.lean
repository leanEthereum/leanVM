/-
  Rv64mc.Proof.Whir.GluedWeightEvaluate

  `GluedWeight::evaluate` keeps its contract (`Spec.Whir.GluedWeightEvaluate.spec`), over any program holding its
  template, from the contracts of `eq_eval` and `induced_weight`, one weight at a time: `Ood` calls `eq_eval` and
  writes `Ok` and the value into `sret` (`ok_ood`), `Queries` tail-calls `induced_weight` with the slot
  (`ok_queries`); each runs the other's path only under a niche tag its weight cannot have. What `rv_auto` leaves is
  the slot's stores (their frame, `Proof/Whir/Mem.lean`), the loads of the weight past the function's own stack
  stores, and the result.
-/

import Rv64mc.Spec.Whir.GluedWeightEvaluate
import Rv64mc.Spec.Multilinear.EqEval
import Rv64mc.Gen.Tmpl.Verifier.Whir.GluedWeight.Evaluate
import Rv64mc.Proof.Whir.Mem
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Whir.GluedWeightEvaluate

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir Rv64mc.Spec.Whir.GluedWeightEvaluate
open Rv64mc.Proof.Whir
open Rv64mc.Gen.Verifier.Whir.GluedWeight.Evaluate (Link tmpl)

theorem cap_ne_tag {c : Nat} (h : c < 2 ^ 63) : BitVec.ofNat 64 c ≠ 18446744073709551615#64 := by
  intro h'; have := congrArg BitVec.toNat h'; simp at this; omega

theorem add_ofNat_zero (a : Word) : a + BitVec.ofNat 64 0 = a := by simp

theorem add_ofNat_add (a : Word) (i j : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem ok_ood (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needI needE : Nat} (hnI : needI ≤ need) (hnE : 16 + needE ≤ need) (pt x : List E)
    (hiw : Holds env p L.inducedWeight.idx needI (InducedWeight.Pre env [] [] x) (InducedWeight.Post [] [] x)
      (SretOut Layouts.ResultE.byteSize))
    (heq : Holds env p L.eqEval.idx needE (Spec.Multilinear.EqEval.Pre env pt x)
      (Spec.Multilinear.EqEval.Post pt x)) :
    Holds env p i need (Pre env (.ood pt) x) (Post (.ood pt) x) (SretOut Layouts.ResultE.byteSize) := by
  rv_auto hp with [hL] using [hiw, heq]
  all_goals have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  all_goals have hd16 : 16 ≤ need := by omega
  all_goals have ho10 : env.Owned m top (regs .x10) 24 := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
  all_goals have ho11 : env.Owned m top (regs .x11) 56 := ⟨by rw [← hpre_2]; exact hpre_8, hpre_9⟩
  all_goals obtain ⟨htag, ptr, cap, hv, hlv⟩ := hpre_10
  all_goals have hf := vec_fields hv
  all_goals simp only [Layouts.GluedWeight.Ood.f0, Layouts.Vec.ptr, Layouts.Vec.len, Layouts.Vec.cap,
    Nat.reduceAdd] at hf
  all_goals have n11 : ∀ k c d, k < 56 → c.toNat = 2 ^ 64 - d → d ≤ need → regs .x11 + BitVec.ofNat 64 k ≠ top + c :=
    fun k c d hk hc hd => owned_ne_slot ho11 hpre_5 hk hpre_3 hc hd
  all_goals have hs8 := slot_ge (c := 18446744073709551608#64) (d := 8) hpre_3 (by decide) (by omega)
  all_goals have hs16 := slot_ge (c := 18446744073709551600#64) (d := 16) hpre_3 (by decide) hd16
  all_goals have hb := live_below hlv hpre_5
  all_goals try exact absurd (by simpa using htag) hc
  · rw [MachineState.getMem_setMem_ne (n11 24 _ 16 (by decide) (by decide) hd16),
      MachineState.getMem_setMem_ne (n11 24 _ 8 (by decide) (by decide) (by omega)), hf.2.1]
  · rw [MachineState.getMem_setMem_ne (n11 16 _ 16 (by decide) (by decide) hd16),
      MachineState.getMem_setMem_ne (n11 16 _ 8 (by decide) (by decide) (by omega)), hf.1]
    exact hv.elems.keep ((keeps_slot (by simpa using hb) hs8).trans (keeps_slot (by simpa using hb) hs16))
  · have hb12 := live_below hpre_13 hpre_5
    exact hpre_12.keep ((keeps_slot (by simpa using hb12) hs8).trans (keeps_slot (by simpa using hb12) hs16))
  · rw [MachineState.getMem_setMem_ne (n11 16 _ 16 (by decide) (by decide) hd16),
      MachineState.getMem_setMem_ne (n11 16 _ 8 (by decide) (by decide) (by omega)), hf.1]
    exact live_setMem_stack (live_setMem_stack hlv hs8) hs16
  · exact live_setMem_stack (live_setMem_stack hpre_13 hs8) hs16
  all_goals have n10 : ∀ k c d, k < 24 → c.toNat = 2 ^ 64 - d → d ≤ need → top + c ≠ regs .x10 + BitVec.ofNat 64 k :=
    fun k c d hk hc hd => (owned_ne_slot ho10 hpre_5 hk hpre_3 hc hd).symm
  all_goals have n10z : ∀ c d, c.toNat = 2 ^ 64 - d → d ≤ need → top + c ≠ regs .x10 :=
    fun c d hc hd => (owned_ne_slot0 ho10 hpre_5 (by decide) hpre_3 hc hd).symm
  · rw [MachineState.getMem_setMem_ne (n10 16 _ 8 (by decide) (by decide) (by omega)),
      MachineState.getMem_setMem_ne (n10 8 _ 8 (by decide) (by decide) (by omega)),
      MachineState.getMem_setMem_ne (n10z _ 8 (by decide) (by omega)),
      keep1_1 _ (slot_le (d := 16) (d' := 8) hpre_3 (by decide) (by decide) hd16 (by decide)),
      MachineState.getMem_setMem_ne (slot_ne (by decide)), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (n10 16 _ 16 (by decide) (by decide) hd16),
      MachineState.getMem_setMem_ne (n10 8 _ 16 (by decide) (by decide) hd16),
      MachineState.getMem_setMem_ne (n10z _ 16 (by decide) hd16),
      keep1_1 _ (BitVec.le_refl _), MachineState.getMem_setMem_eq]
  · exact (sret_store (v := r1 .x11) ho10 hpre_5 hlim (k := 16) (by decide)
        (sret_store (v := r1 .x10) ho10 hpre_5 hlim (k := 8) (by decide)
          (sret_store0 (v := 0#64) ho10 hpre_5 hlim (by decide)
            ⟨frame_own (Tactic.frame_store (Tactic.frame_store (Tactic.frame_refl hpre_5) hs8
              (slot_lt (d := 8) hpre_3 (by decide) (by decide) (by omega))) hs16
              (slot_lt (d := 16) hpre_3 (by decide) (by decide) hd16)) hret1_14
              (Nat.le_of_lt (slot_lt (d := 16) hpre_3 (by decide) (by decide) hd16)), hret1_15⟩))).1
  · exact (sret_store (v := r1 .x11) ho10 hpre_5 hlim (k := 16) (by decide)
        (sret_store (v := r1 .x10) ho10 hpre_5 hlim (k := 8) (by decide)
          (sret_store0 (v := 0#64) ho10 hpre_5 hlim (by decide)
            ⟨frame_own (Tactic.frame_store (Tactic.frame_store (Tactic.frame_refl hpre_5) hs8
              (slot_lt (d := 8) hpre_3 (by decide) (by decide) (by omega))) hs16
              (slot_lt (d := 16) hpre_3 (by decide) (by decide) hd16)) hret1_14
              (Nat.le_of_lt (slot_lt (d := 16) hpre_3 (by decide) (by decide) hd16)), hret1_15⟩))).2
  · have hv' := Model.eqEvalRust_eq hpre_14
    obtain ⟨h1, h2⟩ := hret1_16 _ hv'
    rw [show (Model.GluedWeightRust.ood pt).evaluate x = some (LeanVM.Protocol.Verifier.eqEval pt x) from hv']
    have hw := ho10.2
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Layouts.ResultE.tagOffset, Layouts.ResultE.Ok.tag, Layouts.ResultE.Ok.f0, Layouts.E.c0,
        Layouts.E.c1, add_ofNat_zero, add_ofNat_add]
    · rw [MachineState.getMem_setMem_ne (off_ne0 (j := 16) (by omega) (by decide)).symm,
        MachineState.getMem_setMem_ne (off_ne0 (j := 8) (by omega) (by decide)).symm, MachineState.getMem_setMem_eq]
    · rw [MachineState.getMem_setMem_ne (off_ne (i := 8) (j := 16) (by omega) (by omega) (by decide)),
        MachineState.getMem_setMem_eq, h1]
    · rw [MachineState.getMem_setMem_eq, h2]

theorem ok_queries (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needI needE : Nat} (hnI : needI ≤ need) (hnE : 16 + needE ≤ need) (ml : Nat)
    (qs : List Word) (qw x : List E)
    (hiw : Holds env p L.inducedWeight.idx needI (InducedWeight.Pre env qs qw x) (InducedWeight.Post qs qw x)
      (SretOut Layouts.ResultE.byteSize))
    (heq : Holds env p L.eqEval.idx needE (Spec.Multilinear.EqEval.Pre env [] x)
      (Spec.Multilinear.EqEval.Post [] x)) :
    Holds env p i need (Pre env (.queries ml qs qw) x) (Post (.queries ml qs qw) x)
      (SretOut Layouts.ResultE.byteSize) := by
  rv_auto hp with [hL] using [hiw, heq]
  all_goals obtain ⟨hml, ⟨qptr, qcap, hq, hlq⟩, wptr, wcap, hw, hlw⟩ := hpre_10
  all_goals have hf := vec_fields hq
  all_goals have hg := vec_fields hw
  all_goals simp only [Layouts.GluedWeight.Queries.queries, Layouts.GluedWeight.Queries.query_weights, Layouts.Vec.ptr,
    Layouts.Vec.len, Layouts.Vec.cap, Nat.reduceAdd, add_ofNat_zero] at hf hg
  all_goals try exact absurd (hf.2.2.symm.trans hc) (cap_ne_tag hq.cap_lt)
  all_goals simp only [Layouts.GluedWeight.Queries.message_log] at hml
  all_goals have hml' := congrArg BitVec.toNat hml
  all_goals rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hml'
  · omega
  · rw [← hpre_2]; exact hpre_6
  · rw [hml']; exact hpre_14
  · exact hf.2.1
  · rw [hf.1]; exact hq.elems
  · rw [hf.1]; exact hlq
  · exact hg.2.1
  · rw [hg.1]; exact hw.elems
  · rw [hg.1]; exact hlw
  · exact hret2_14
  · rw [hml'] at hret2_16; exact hret2_16

/-- **`GluedWeight::evaluate` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needI needE : Nat} (hnI : needI ≤ need) (hnE : 16 + needE ≤ need)
    (hiw : InducedWeight.spec env p L.inducedWeight.idx needI)
    (heq : Spec.Multilinear.EqEval.spec env p L.eqEval.idx needE) : spec env p i need := by
  intro g x
  cases g with
  | ood pt => exact ok_ood env p i L hp hL hnI hnE pt x (hiw [] [] x) (heq pt x)
  | queries ml qs qw => exact ok_queries env p i L hp hL hnI hnE ml qs qw x (hiw qs qw x) (heq [] x)

end Rv64mc.Proof.Whir.GluedWeightEvaluate
