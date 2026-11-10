/-
  LeanVM.Protocol.Whir.Params.Iface

  The deployed stacked opening as the interface the soundness assembly takes
  (`EndToEnd.Sound.OpeningIface`).
-/

module

public import LeanVM.Protocol.Whir.Params.Deployed
public import LeanVM.Protocol.Whir.Params.Threshold
public import LeanVM.Protocol.EndToEnd.Sound.Assemble
public import LeanVM.Protocol.EndToEnd.Sound.Runs

/-!
# The opening's interface

`openingIface` fills `EndToEnd.Sound.OpeningIface` with the deployed WHIR opening: level 0's
threshold `thr0Of` (the extractor's, `johnsonThreshold_eq_thr0Of`), its list bound `listMax₀`, the
shape `ShapeOK₀` of the stack's commitment (`shape_commitStack`), and `deployedStackedSpec`.
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front

@[expose] public section

/-- A weight that is the multilinear extension of its values is multiaffine. -/
theorem isMultiaffine_of_multilinear {μ : ℕ} {w : List E → E} (hw : IsMultilinearFn μ w) :
    IsMultiaffine μ w := by
  have hS : IsMultiaffine μ fun p ↦ ∑ x : Fin (2 ^ μ), w (boolPoint μ x) * eqEval (boolPoint μ x) p :=
    IsMultiaffine.sum _ _ fun x _ ↦ by
      have h := isMultiaffine_eqEval (boolPoint μ x)
      rw [show (boolPoint μ x).length = μ by simp [boolPoint]] at h
      exact h.const_mul _
  intro l hl k hk X
  rw [hw (l.set k X) (by simp [hl]), hw (l.set k 0) (by simp [hl]), hw (l.set k 1) (by simp [hl])]
  exact hS l hl k hk X

/-- The stack's word is the first commitment's. -/
theorem shape_word {μ R : ℕ} {cs : List (ℕ × ℕ × Word)} (h : ShapeOK₀ μ R cs) :
    firstWordC cs = some (wordOf cs 0) := by
  obtain ⟨-, W, hW, -⟩ := h
  rw [firstWordC, wordOf, List.head?_eq_getElem?, hW]
  rfl

/-- The stack's root, as `commitStack` reads it, has level 0's shape. -/
theorem shape_commitStack {μ R : ℕ} (h : Whir.Admissible μ R) {e : Ev}
    (hw : ∀ ht w W, e = Ev.commit ht w W → WellShaped w W)
    (ha : (commitStack μ R).after [e] = some (.ret ())) : ShapeOK₀ μ R (commits [e]) := by
  obtain ⟨level, rest, W, hc, he⟩ := Sound.commitStack_after_ret ha
  obtain ⟨level', rest', F⟩ := level0Facts (shapeOK_of_admissible h)
  have heq := F.hc
  rw [hc, Option.some.injEq, List.cons.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hfold := F.hℓ
  have hrate : level.logInvRate = R := by rw [F.hA.head.2, F.hR₀]
  obtain rfl : e = Ev.commit (levelShape μ level (2 ^ level.fold)).1
      (levelShape μ level (2 ^ level.fold)).2 W := by simpa using he
  refine ⟨rfl, W, ?_, ?_⟩
  · simp only [commits, List.getElem?_cons_zero, levelShape, hfold, hrate]
  · have := hw _ _ _ rfl
    rwa [levelShape, hfold] at this

/-- **The deployed opening's interface.** -/
noncomputable def openingIface : EndToEnd.Sound.OpeningIface where
  thr₀ := thr0Of
  listMax₀ := listMax₀
  ShapeOK₀ := ShapeOK₀
  word₀ cs := wordOf cs 0
  shape_word h := shape_word h
  thr₀_eq h := (johnsonThreshold_eq_thr0Of h).symm
  shape_commitStack h := shape_commitStack h
  candidates_finite W h := (candidates_facts h W).1
  card_candidates_le W h := (candidates_facts h W).2
  ood_row h := ood_row h
  lambda_row h := lambda_row h
  multiaffine_eqEval := isMultiaffine_eqEval
  multiaffine_of_multilinear hw := isMultiaffine_of_multilinear hw
  stackedSpec h claims _ hcl T := deployedStackedSpec h claims hcl T

end
end LeanVM.Protocol.Whir.Params
