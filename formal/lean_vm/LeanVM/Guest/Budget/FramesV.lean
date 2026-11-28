/-
  LeanVM.Guest.Budget.FramesV

  The count's frame hypothesis on functions only: a valid tree's cost reads its weights at the
  program's functions alone, so the frame sizes need be within the certificates' only there.
-/

module

public import LeanVM.Guest.Budget.CheckerCount

/-!
# Frame sizes within the certificates', on functions

`fsW g = Data.wfsJ (coreIdx g)` is `0` at a name that is no function (`coreIdx` past the end), while
b2c's `B2C.fs` is at least `2` everywhere (a tail key's frame, a default): `∀ g, B2C.fs g ≤ fsW g` is
false. The count reads the weights only at its trees' nodes and phantoms, each a function of the
program (`Tree.Valid`, `Phantom`): `cost_mono_valid`. So the words' and the cycles' bounds hold with
the frames within the certificates' on functions (`FnWithin`): `wordsA_le_of_cost_v`,
`logMem_le_of_count_v`, `checker_bounds_v`, `checkerZero_bounds_v`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **A weight within another on the functions of `P`.** -/
def FnWithin (P : Core.Program) (ω ω' : String → ℕ) : Prop := ∀ g fn, P.find? g = some fn → ω g ≤ ω' g

section Mono

variable {P : Core.Program} {α : Bool} {ω ω' : String → ℕ} {rd : Reader}

mutual
/-- **A valid tree's cost grows with its weights on the functions.** -/
theorem cost_mono_valid (h : FnWithin P ω ω') :
    ∀ (t : Tree) (args rets : List E), t.Valid P rd args rets → t.cost P α ω ≤ t.cost P α ω'
  | .node f σ bufs kids, _, _, hv => by
      obtain ⟨fn, hf, -, es, vs, -, -, -, hk⟩ := hv
      have h1 := costKids_mono_valid h σ (calls es) kids hk
      have h2 := h f fn hf
      rw [Tree.cost, Tree.cost]
      omega
  | .phantom .., _, _, hv => hv.elim

theorem costKids_mono_valid (h : FnWithin P ω ω') (σ : Val) :
    ∀ (cs : List Call) (ks : List Tree), Tree.KidsValid P rd σ cs ks →
      Tree.costKids P α ω ks ≤ Tree.costKids P α ω' ks
  | [], [], _ => by rw [Tree.costKids, Tree.costKids]
  | c :: cs, k :: ks, hk => by
      obtain ⟨-, hk1, hks⟩ := hk
      have h2 := costKids_mono_valid h σ cs ks hks
      have h1 : k.cost P α ω ≤ k.cost P α ω' := by
        split_ifs at hk1
        · exact cost_mono_valid h k _ _ hk1
        · obtain ⟨⟨f, σ', rfl⟩, fn, hf, -⟩ := hk1
          have := h f fn hf
          rw [Tree.cost, Tree.cost]
          split <;> omega
      rw [Tree.costKids, Tree.costKids]
      omega
  | [], _ :: _, hk => hk.elim
  | _ :: _, [], hk => hk.elim
end

end Mono

/-- Frame sizes within the certificates' on functions, and aligned flags within theirs, pad within
their weights on functions. -/
theorem fsPad_le_fn {fs : String → ℕ} {al : String → Bool} (hfs : FnWithin coreProgram fs fsW)
    (hal : ∀ g, al g = true → alW g = true) : FnWithin coreProgram (fsPad fs al) (fsPad fsW alW) := by
  intro g fn hg
  unfold fsPad padOf
  have := hfs g fn hg
  by_cases h : al g = true
  · simp [h, hal g h]; omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; split <;> omega

variable {fs : String → ℕ} {lp al : String → Bool} {rd : Reader} {args rets : List E}

/-- **A valid tree's aligned words from its cost**, the frames within the certificates' on functions. -/
theorem wordsA_le_of_cost_v (hfs : FnWithin coreProgram fs fsW) (hal : ∀ g, al g = true → alW g = true)
    (htl : ∀ f, fs (tailKey f) ≤ fs f) {T : Tree} (hv : T.Valid coreProgram rd args rets)
    (hb : T.BufsOk coreProgram) {N : ℕ} (hc : T.cost coreProgram true (fsPad fsW alW) ≤ N) :
    T.wordsA fs lp al ≤ N :=
  (wordsA_le_cost htl hb).trans ((cost_mono_valid (fsPad_le_fn hfs hal) T args rets hv).trans hc)

/-- **`logMem_le_of_count`, the frames within the certificates' on functions.** -/
theorem logMem_le_of_count_v {K : ℕ} {C : Coefs}
    (hC : Coefs.Above ⟨66, K + 993, 1348, 7336, 96774, 120875, 41297⟩ C) {it : NodeItems}
    (hd : it.DeclaredFit) (hrows : ∀ n ∈ it.rows, n ≤ 32) (hB : C.budget it ≤ 2 ^ 24)
    (hfs : FnWithin coreProgram fs fsW) (hal : ∀ g, al g = true → alW g = true)
    (htl : ∀ f, fs (tailKey f) ≤ fs f) {T : Tree} (hv : T.Valid coreProgram rd args rets)
    (hb : T.BufsOk coreProgram) (hc : T.cost coreProgram true (fsPad fsW alW) ≤ nodeWordsC K it) :
    logMem (T.wordsA fs lp al) ≤ 24 :=
  logMem_le_iff.mpr ⟨by decide, (wordsA_le_of_cost_v hfs hal htl hv hb
    (hc.trans (nodeWordsC_le hC it hd hrows))).trans hB⟩

variable {C : Coefs} {it : NodeItems} {input : PublicInput} {t : Execution guestProgram} {T : Tree}

/-- **`checker_bounds`, the frames within the certificates' on functions.** -/
theorem checker_bounds_v (hC : Coefs.Above Coefs.checker C) (hd : it.DeclaredFit)
    (hrows : ∀ n ∈ it.rows, n ≤ 32) (hB : C.budget it ≤ 2 ^ 24) (hfs : FnWithin coreProgram fs fsW)
    (hal : ∀ g, al g = true → alW g = true) (htl : ∀ f, fs (tailKey f) ≤ fs f)
    (hT : T.Valid coreProgram rd args rets) (hb : T.BufsOk coreProgram)
    (hc : T.cost coreProgram true (fsPad fsW alW) ≤ nodeWordsC iterSum it)
    (hv : ValidExecution guestProgram input t) (hlog : t.logMemorySize ≤ logMem (T.wordsA fs lp al))
    (hcnt : ∀ op, t.opcodeCount op ≤ cntJ iterSumV op it) :
    t.logMemorySize ≤ 24 ∧ t.stepCount < 2 ^ 24 ∧ t.committedSize ≤ 2 ^ 30 := by
  have hm := logMem_le_of_count_v (K := iterSum) (lp := lp) hC hd hrows hB hfs hal htl hT hb hc
  exact ⟨hlog.trans hm, cycles_committed_of_count (checker_aboveRows.trans hC) iterSum_weighted hd hrows hB hv
    (hlog.trans hm) hcnt⟩

/-- **`checkerZero_bounds`, the frames within the certificates' on functions.** -/
theorem checkerZero_bounds_v (hC : Coefs.Above Coefs.checkerZero C) (hd : it.DeclaredFit)
    (hrows : ∀ n ∈ it.rows, n ≤ 32) (hB : C.budget it ≤ 2 ^ 24) (hfs : FnWithin coreProgram fs fsW)
    (hal : ∀ g, al g = true → alW g = true) (htl : ∀ f, fs (tailKey f) ≤ fs f)
    (hT : T.Valid coreProgram rd args rets) (hb : T.BufsOk coreProgram)
    (hc : T.cost coreProgram true (fsPad fsW alW) ≤ nodeWordsC iterZero it)
    (hv : ValidExecution guestProgram input t) (hlog : t.logMemorySize ≤ logMem (T.wordsA fs lp al))
    (hcnt : ∀ op, t.opcodeCount op ≤ cntJ iterZeroV op it) :
    t.logMemorySize ≤ 24 ∧ t.stepCount < 2 ^ 24 ∧ t.committedSize ≤ 2 ^ 30 := by
  have hm := logMem_le_of_count_v (K := iterZero) (lp := lp) hC hd hrows hB hfs hal htl hT hb hc
  exact ⟨hlog.trans hm, cycles_committed_of_count (checkerZero_aboveRows.trans hC) iterZero_weighted hd hrows hB
    hv (hlog.trans hm) hcnt⟩

end

end LeanVM.Guest.Budget
