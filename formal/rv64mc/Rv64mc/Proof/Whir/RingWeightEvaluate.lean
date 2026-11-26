/-
  Rv64mc.Proof.Whir.RingWeightEvaluate

  `RingWeight::evaluate` keeps its contract (`Spec.Whir.RingWeight.evaluateSpec`), over any program holding its
  template, from `ring_weight`'s: it reads the two `Vec`s' pointers and lengths and tail-calls `ring_weight`.
-/

import Rv64mc.Spec.Whir.RingWeight
import Rv64mc.Proof.Whir.Mem
import Rv64mc.Gen.Tmpl.Verifier.RingSwitch.RingWeight.Evaluate
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Whir.RingWeightEvaluate

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.RingWeight Rv64mc.Proof.Whir
open Rv64mc.Gen.Verifier.RingSwitch.RingWeight.Evaluate (Link tmpl)

/-- The contract at one weight and point, the callee's contract at its slices. -/
theorem ok_at (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needR : Nat} (hnR : needR ≤ need) (w : Model.RingWeightRust) (rp : List E)
    (hrw : Holds env p L.ringWeight.idx needR (Pre env w.point rp w.coefficients)
      (Post w.point rp w.coefficients)) :
    Holds env p i need (EvaluatePre env w rp) (EvaluatePost w rp) := by
  rv_auto hp with [hL] using [hrw]
  all_goals obtain ⟨pp, pc, hvp, hlp⟩ := hpre_6
  all_goals obtain ⟨cp, cc, hvc, hlc⟩ := hpre_7
  all_goals have hp' := vec_fields hvp
  all_goals have hc' := vec_fields hvc
  all_goals simp only [Layouts.RingWeight.point, Layouts.RingWeight.coefficients, Layouts.Vec.ptr, Layouts.Vec.len,
    Layouts.Vec.cap, Nat.reduceAdd] at hp' hc'
  · omega
  · exact hp'.2.1
  · rw [hp'.1]; exact hvp.elems
  · rw [hp'.1]; exact hlp
  · exact hc'.2.1
  · rw [hc'.1]; exact hvc.elems
  · rw [hc'.1]; exact hlc
  · exact hret1_16

/-- **`RingWeight::evaluate` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR : Nat} (hnR : needR ≤ need) (hrw : spec env p L.ringWeight.idx needR) :
    evaluateSpec env p i need :=
  fun w rp => ok_at env p i L hp hL hnR w rp (hrw w.point rp w.coefficients)

end Rv64mc.Proof.Whir.RingWeightEvaluate
