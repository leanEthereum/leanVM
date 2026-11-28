/-
  LeanVM.Guest.B1.VsC.CstWordsIn

  `check_stack_terminal`'s own words lie in its buffers, pairwise apart.
-/

module

public import LeanVM.Guest.B1.VsC.CstWords

/-!
# `check_stack_terminal`'s own words, placed

`runsFrom c ss ws`: run `i` of `ws` at the base of buffer `i` of sizes `ss` laid one after another
from `c`. Each run within its buffer, the runs lie in `[c, c + Σ ss)` and are pairwise apart
(`runsFrom_in`). `cstWords` is such a layout (`cstWords_eq`), whence `cst_wordsInA`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The runs `ws` at the bases of buffers of sizes `ss` laid from `c`. -/
def runsFrom : ℕ → List ℕ → List (List E) → Words
  | c, s :: ss, w :: ws => (c, w) :: runsFrom (c + s) ss ws
  | _, _, _ => []

/-- **Consecutive buffers hold their runs apart**: each run within its buffer, all of them in
`[c, c + Σ ss)`, pairwise disjoint. -/
theorem runsFrom_in : ∀ {ss : List ℕ} {ws : List (List E)}, List.Forall₂ (fun s w => w.length ≤ s) ss ws →
    ∀ c, (∀ q ∈ runsFrom c ss ws, c ≤ q.1 ∧ q.1 + q.2.length ≤ c + ss.sum) ∧
      (runsFrom c ss ws).Pairwise fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1
  | [], [], .nil, c => by simp [runsFrom]
  | s :: ss, w :: ws, .cons hsw hrest, c => by
    obtain ⟨hin, hpw⟩ := runsFrom_in hrest (c + s)
    have hw : w.length ≤ s := hsw
    refine ⟨fun q hq => ?_, List.Pairwise.cons (fun q' hq' => Or.inl ?_) hpw⟩
    · simp only [runsFrom, List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp only [List.sum_cons]; omega
      · have := hin q hq; simp only [List.sum_cons]; omega
    · have := hin q' hq'; show c + w.length ≤ q'.1; omega

theorem runsFrom_wordsInA {ss : List ℕ} {ws : List (List E)} (h : List.Forall₂ (fun s w => w.length ≤ s) ss ws)
    (lo hi c : ℕ) : WordsInA (runsFrom c ss ws) lo hi c (c + ss.sum) :=
  ⟨fun q hq => Or.inr (( runsFrom_in h c).1 q hq), (runsFrom_in h c).2⟩

theorem rgRows_length (cs zs ps : List E) (n : ℕ) : (rgRows cs zs ps n).length = 64 * (n + 1) := by
  simp [rgRows]

theorem chainW_lengthC (as x : List E) (n : ℕ) : (chainW as x n).length = n + 1 := by
  simp [chainW]

/-- `cstWords` as consecutive runs. -/
theorem cstWords_eq (c : ℕ) (layout : Layout) (chi r qPoint kOut x z f g : List E) (rho rm : E) :
    cstWords c layout chi r qPoint kOut x z f g rho rm =
      runsFrom c (cstSizes chi.length)
        [rgRows (ringCoefficients f g) chi ((padX1 x).take chi.length) chi.length, cstMaskW layout x,
          cstRqW rho qPoint, chainW chi x chi.length, chainW kOut x kOut.length, chainW r x layout.logMemory,
          chainW (piW rm) x layout.logMemory, piW rm, tqW layout x, chainW z x z.length] := by
  simp only [cstWords, runsFrom, cstSizes, cstBase, List.take, List.sum_cons, List.sum_nil, Nat.add_zero,
    Nat.add_assoc]

/-- **`check_stack_terminal`'s own words lie in its buffers**, from the cursor `c`, pairwise apart. -/
theorem cst_wordsInA {layout : Layout} {chi r qPoint kOut x z f g : List E} {rho rm : E}
    (hchi : chi.length ≤ 41) (hk : kOut.length ≤ 41) (hlm : layout.logMemory ≤ 41) (hz : z.length ≤ 30)
    (lo hi c : ℕ) :
    WordsInA (cstWords c layout chi r qPoint kOut x z f g rho rm) lo hi c (c + (cstSizes chi.length).sum) := by
  rw [cstWords_eq]
  refine runsFrom_wordsInA ?_ lo hi c
  simp only [cstSizes, List.forall₂_cons, List.Forall₂.nil, and_true, rgRows_length, chainW_lengthC,
    cstMaskW, cstRqW, piW, tqW, List.length_map, List.length_range, List.length_cons, List.length_replicate]
  omega

end
end LeanVM.Guest.B1.VsC
