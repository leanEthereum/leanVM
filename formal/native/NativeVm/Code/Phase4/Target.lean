module

public import NativeVm.Code.Phase4.Glue
public import NativeVm.Code.Phase4.Model

/-!
# `ξ`'s powers and the sumcheck's target

`targetC_spec`: from `ξ` in `A`, `ξ`'s five powers at `oXP` and the target
`dot (fpOf ξ) totals` at `oCLM`.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env} {s : QState} {E : QState → Prop}

/-- **`ξ`'s powers and the target.** -/
theorem targetC_spec (h4 : Env4 env) (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s) (xi : EW)
    (h9 : s.reg .r9 = xi.c0) (h10 : s.reg .r10 = xi.c1) (totals : Array EW) (htsz : totals.size = 3)
    (htot : EWArr s.mem (wd env.work oBT) totals) :
    WP targetC s (fun s' ↦ EWArr s'.mem (wd env.work oXP) (powers xi 5) ∧
      EWAt s'.mem (wd env.work oCLM) (dot (fpOf xi) totals) ∧
      Wr env.work (fun k ↦ oXP ≤ k ∧ k < oXP + 12) s s' ∧ RegsFrame arrRegs s s') E := by
  unfold targetC
  wst; wst; wst; wst; wst
  refine WP.then (WP.dom (epowersW (w := env.work) (a := 0 + oXP) (n := 5) ?_ ?_
    (by norm_num) ?_)) fun s1 ⟨⟨hp, hm, hr⟩, hd1⟩ ↦ ?_
  · regw
  · rsimp
  · intro k hk; simp only [QState.setReg_mem]
    exact hws _ (by simp only [oXP, oS]; omega) (by simp only [oXP, oS]; omega)
  have hws1 : WS env s1 := WS.wr hws fun a ↦ hd1 a
  have eta : (⟨xi.c0, xi.c1⟩ : EW) = xi := rfl
  simp only [regB, QState.setReg_reg, reduceCtorEq, ite_true, ite_false, h9, h10, eta] at hp
  simp only [QState.setReg_mem] at hm
  have w1 : Wr env.work (fun k ↦ oXP ≤ k ∧ k < oXP + 12) s s1 :=
    Wr.ofRange (a := 0 + oXP) (n := 10) hm fun k hk ↦ by omega
  have hc1 : s1.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by
    rw [w1.ctx h4 fun k hk ↦ by simp only [oXP, oS] at hk; omega]; exact hctx
  have ht1 : EWArr s1.mem (wd env.work oBT) totals :=
    EWArr.wr w1 htot (by rw [htsz]; decide) fun k hk ↦ by
      simp only [oXP, oS, oBT, oB] at hk ⊢; omega
  have hrdi1 : s1.reg .rdi = env.ctx := by rw [hr .rdi (by decide)]; rsimp; exact hrdi
  wst; wst; wst; wst; wst
  have hx : EWArr s1.mem (wd env.work (0 + oXP + 2 * 2)) ((powers xi 5).extract 2 5) :=
    EWArr.extract hp 2 5
  refine WP.then (edotW (xs := fpOf xi) (ys := totals) (by
      rsimp
      simp only [Nat.zero_add] at hx ⊢
      exact hx) (by rsimp; simpa using ht1)
    (by rw [htsz, fpOf_size]) (by rsimp; rw [fpOf_size]; rfl) (by rw [fpOf_size]; decide)) fun s2 ⟨hd, hm2, hr2⟩ ↦ ?_
  have hc2 : s2.mem (wd env.ctx ctxWork) = some (wd env.work 0) := by rw [hm2]; exact hc1
  have hrdi2 : s2.reg .rdi = env.ctx := by rw [hr2 .rdi (by decide)]; rsimp; exact hrdi1
  have hws2 : WS env s2 := WS.wr hws1 fun a ↦ by rw [hm2]; rfl
  wst; wst; wst
  refine wp_done_gen fun s' hs' ↦ ?_
  have w3 : Wr env.work (fun k ↦ oCLM ≤ k ∧ k < oCLM + 2) s2 s' := by rw [← hs']; wr_tac
  have hd0 : s2.reg .r9 = (dot (fpOf xi) totals).c0 := congrArg EW.c0 hd
  have hd1 : s2.reg .r10 = (dot (fpOf xi) totals).c1 := congrArg EW.c1 hd
  have w2 : Wr env.work (fun _ ↦ False) s1 s2 := Wr.ofEq (by rw [hm2]; rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Nat.zero_add] at hp
    refine EWArr.wr w3 (EWArr.wr w2 hp (by rw [powers_size]; decide) fun k hk ↦ hk.elim)
      (by rw [powers_size]; decide) fun k hk ↦ ?_
    rw [powers_size]; simp only [oCLM, oXP, oS] at hk ⊢; omega
  · rw [← hs']
    exact EWAt.of (by memw; rw [hd0]) (by memw; rw [hd1])
  · exact w1.trans ((w2.mono fun _ h ↦ h.elim).trans
      (w3.mono fun k hk ↦ by simp only [oCLM, oXP, oS] at hk ⊢; omega))
  · refine rf_arr_of ?_ ?_
    · rw [← hs']; rsimp; rw [hr2 _ (by decide)]; rsimp; rw [hr _ (by decide)]; rsimp
    · rw [← hs']; rsimp; rw [hr2 _ (by decide)]; rsimp; rw [hr _ (by decide)]; rsimp

end NativeVm.Code.P4
