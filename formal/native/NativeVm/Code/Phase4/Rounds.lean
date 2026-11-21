module

public import NativeVm.Code.Phase4.Round
public import NativeVm.Code.Phase4.MaxH

/-!
# The table sumcheck's rounds

`roundsC_refines`: `roundsC` refines `sumcheckPlain target 4 nR`, `nR` the tallest table's
log-height: `maxC`, then a round (`roundC_refines`) while rounds remain (`r14`), the challenges
landing reversed at `oPT` (the point), the final claim at `oCLM`.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env}

theorem foldl_max_le (heights : Array Nat) (hh : heights.size = 6)
    (hb : ∀ i < 6, heights.getD i 0 ≤ 30) : heights.foldl max 0 ≤ 30 := by
  rw [← pmax_size]; exact pmax_le heights (by rw [hh]; exact hb) _

/-- **The rounds.** -/
theorem roundsC_refines (h4 : Env4 env) {X : QState → Prop} (hX : RStab env X)
    (heights : Array Nat) (hh : heights.size = 6) (hb : ∀ i < 6, heights.getD i 0 ≤ 30)
    (target : EW) :
    Refines (fun t s ↦ CodeRel env t s ∧ X s ∧ WS env s ∧
        s.mem (wd env.ctx ctxWork) = some (wd env.work 0) ∧
        (∀ i < 6, s.mem (wd env.work (oL + 4 + i)) = some (heights.getD i 0).toUInt64) ∧
        EWAt s.mem (wd env.work oCLM) target)
      roundsC (sumcheckPlain target 4 (heights.foldl max 0))
      (fun r t s ↦ RInv env X (heights.foldl max 0) (heights.foldl max 0) r t s) X := by
  rw [sumcheckPlain_eq]
  have hnR := foldl_max_le heights hh hb
  unfold roundsC
  refine Refines.pre_blk (P' := RInv env X (heights.foldl max 0) 0 (#[], target))
    (fun t s ⟨hc, hx, hws, hctx, hhw, hcl⟩ ↦ ?_) ?_
  · refine WP.mono (WP.dom (maxC_spec hc.rdi hctx hws heights hh hhw hb))
      (fun s' ⟨⟨hbp, h14, hnr, w1, rf1⟩, d1⟩ ↦ ?_) fun _ h ↦ h
    have hW1 : InRs [scratchR] (fun j ↦ j = oNR) :=
      scratch_InRs fun j hj ↦ by simp only [oNR, oS] at hj; omega
    have wf1 : WF env (fun j ↦ j = oNR) s s' := WF.ofWr w1 fun j hj ↦ by simp only [oNR, oS] at hj; omega
    refine ⟨CodeRel.only hc h4 (by decide) (Only.ofWr w1 hW1) d1 (rf1 .rdi (by decide)),
      hX s s' hx (Fr.ofWr w1 hW1 d1 (rf_mono rf1) (by decide))
        (wf1.mono fun j hj ↦ .inr (.inr hj)), WS.wr hws d1, hbp, by rw [h14, Nat.sub_zero],
      Nat.zero_le _, hnR, rfl, ?_, fun i hi ↦ absurd hi (by simp), hnr⟩
    exact EWAt.wf wf1 hcl (by simp only [oCLM, oS]; omega) (by simp only [oCLM, oS]; omega)
      ⟨by simp only [oCLM, oNR, oS]; omega, by simp only [oCLM, oNR, oS]; omega⟩
  have H := Refines.foldlM (l := List.replicate (heights.foldl max 0) none) (f := roundStep)
    (cond := .test false .r14 (.reg .r14)) (body := roundC) (E := X) (init := (#[], target))
    (Inv := fun k acc t s ↦ RInv env X (heights.foldl max 0) k acc t s)
    (fun k acc t s h ↦ by rw [List.length_replicate]; exact test_count h.2.2.2.2.1 (by omega))
    (fun k hk acc ↦ by
      rw [List.getElem_replicate]
      rw [List.length_replicate] at hk
      exact roundC_refines h4 hX hk acc)
  rw [List.length_replicate] at H
  exact H

end NativeVm.Code.P4
