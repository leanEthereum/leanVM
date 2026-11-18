/-
  LeanVM.Guest.EndExecCoreRes

  The core route's residual families (`CoreMode.resFam`) sound at the honest instances: each makes
  its residual true at the instance's valuation, from its path's events holding on the reference.
-/

module

public import LeanVM.Guest.EndExecRF
public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.HeapCSound

/-!
# The residual families, sound

`resFam_sound`: on a memory of at most `2^32` words, along a returning path whose events hold, a
residual of a family holds at the valuation: a range checked value's exponent below the check's bound
(`rcBound_sound`, its atoms on every returning path, `topAtoms_on_path`), a top-level selector's below
its arms (`topSels_sound`), the same under branch conditions. `resOk_sound`: every residual of a
heap certificate whose residuals are of families (`CoreMode.resOk`), which `HonF.res` asks of the core
route's honest valuations.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam resOk idxC baseC vw)

public section

/-- An exponent bound `e(x) < n` from `σ x = g^e`, `e < n < 2^62`. -/
theorem ltF_of_pow {σ : Val} {x n e : ℕ} (hn : n < capE) (he : e < n) (hσ : σ (V.n x) = ofK (addressOfIndex e)) :
    LtF (vw σ) (idxC (.val x)) (idxC (.num n)) := by
  refine ⟨e, n, ?_, CoreMode.rep_const hn, he⟩
  simp only [idxC, CoreMode.valW_baseC, vw, hσ]
  exact rep_of (by omega)

/-- **A residual of a family holds** at a valuation along a returning path of the body whose events
hold on a memory of at most `2^32` words. -/
theorem resFam_sound {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {body : List Stmt} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ) :
    ∀ r : CRes, resFam body r = true → r.Holds σ
  | .lt (.val x) (.num n), h => by
    simp only [resFam, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true] at h
    obtain ⟨hn, h⟩ := h
    rcases h with h | ⟨p, hp, hpx⟩
    · split at h
      · rename_i N hN
        simp only [decide_eq_true_eq] at h
        have hall : ∀ a ∈ Res.topAtoms body, a.Holds Lm.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
        obtain ⟨e, he, hσ⟩ := rcBound_sound hμ Lm hall hN
        exact ltF_of_pow (e := e) hn (by omega) (by rw [hσ, Value.gen_pow_eq_ofK])
      · cases h
    · obtain ⟨h1, h2⟩ := hpx
      obtain ⟨e, he, hσ⟩ := topSels_sound hw (x := p.1) (n := p.2) hp
      rw [h1] at hσ
      exact ltF_of_pow (e := e) hn (by omega) hσ
  | .under _ r, h => fun _ ↦ resFam_sound hμ Lm hw hh r h
  | .lt (.val _) (.val _), h | .lt (.val _) (.mono _), h | .lt (.num _) _, h | .lt (.mono _) _, h
  | .nz _, h | .sub _ _, h | .subR _ _, h | .subP _ _, h => by simp [resFam] at h

/-- **The residuals of a heap certificate of families hold** at a valuation along a returning path of
its function whose events hold on a memory of at most `2^32` words. -/
theorem resOk_sound {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {Cf : CFun} (h : resOk Cf = true) {σ : Val}
    {es : List Ev} {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ) :
    ResF Cf.H σ := fun r hr ↦
  resFam_sound hμ Lm hw hh r (List.all_eq_true.mp h r hr)

end

end LeanVM.Guest.EndExec
