/-
  LeanVM.Guest.B1.Whir.CHead

  The head of open_stacked honestly on f128: the thirteen fixed buffers allocated at given
  pointers, the hints of the caps and their flags, the root stored into `level_roots`.
-/

module

public import LeanVM.Guest.B1.Whir.CBlk

/-!
# The head, honestly (G:1526-1560)

`headSizes c`: the fixed buffers' sizes in allocation order (`osSizesF c`'s first thirteen);
`headVals c P`: the values `10 .. 35`, each buffer's size `g^size` then its pointer `P i`.
`osHead_complete`: the head as a block at fixed values, the root's two cells (the parameters `6`,
`7`) stored at `level_roots`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- The fixed buffers' sizes, in allocation order. -/
def headSizes (c : OsCfg) : List ℕ :=
  [4 * c.capLen, c.capLen, c.yrLen + (c.levels.getD c.yrLevel default).folds, 2 * c.levels.length,
    c.nFolds, 2 * c.nFolds, c.levels.length, c.levels.length, c.levels.length * hsStride,
    c.levels.length * ligColsCap, c.levels.length, c.posLen, c.posLen]

/-- The head's values from `10`: each buffer's size word, then its pointer. -/
def headVals (c : OsCfg) (P : ℕ → E) : List E :=
  [gw (4 * c.capLen), P 0, gw c.capLen, P 1, gw (c.yrLen + (c.levels.getD c.yrLevel default).folds), P 2,
    gw (2 * c.levels.length), P 3, gw c.nFolds, P 4, gw (2 * c.nFolds), P 5, gw c.levels.length, P 6,
    gw c.levels.length, P 7, gw (c.levels.length * hsStride), P 8,
    gw (c.levels.length * ligColsCap), P 9, gw c.levels.length, P 10,
    gw c.posLen, P 11, gw c.posLen, P 12]

theorem headVals_length (c : OsCfg) (P : ℕ → E) : (headVals c P).length = 26 := rfl

theorem holds_hint {rd : Reader} {σ : Val} (h : Hint) : (Atom.hint h).Holds rd σ ↔ True := Iff.rfl

/-- The head's state's static facts. -/
theorem osHead_sf (c : OsCfg) : (osHead c).2.Sf := by
  refine ⟨rfl, ⟨fun f hf ↦ ?_, show 8 < 36 by omega, show 5 < 36 by omega,
    fun m hm ↦ absurd hm (by simp [osHead])⟩, by show 0 < u128Bound; unfold u128Bound; positivity,
    fun p hp ↦ absurd hp (by simp [osHead]), show 36 ≤ 36 from le_rfl⟩
  have hf' : f ∈ [0, 1, 2, 3, 4] := hf
  show f < 36
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
  omega

/-- **The head, honestly** (G:1526-1560): the fixed buffers at the pointers `P i`, the root's two
cells stored in `level_roots` (`P 3`). -/
theorem osHead_complete (c : OsCfg) (σ : Val) (P : ℕ → E)
    (hr : ∀ C rd, H C rd → LoadHolds rd (P 3) 0 (σ (.n 6)) ∧ LoadHolds rd (P 3) 1 (σ (.n 7))) :
    BlkA H σ 10 36 (osHead c).1 (fun σ' ↦ (osHead c).2.Ok σ' ∧
      (∀ j < 26, σ' (.n (10 + j)) = (headVals c P).getD j 0) ∧ AgreeBelow 10 σ σ') := by
  refine ⟨lstF 10 (headVals c P), fun C rd hH σ' ha hv ↦ ?_⟩
  have v : ∀ j < 26, σ' (.n (10 + j)) = (headVals c P).getD j 0 := fun j hj ↦
    lstF_at hv (by simp [headVals_length]) j (by simp [headVals_length]; omega)
  have w : ∀ j, 10 ≤ j → j < 36 → σ' (.n j) = (headVals c P).getD (j - 10) 0 := fun j h1 h2 ↦ by
    have := v (j - 10) (by omega)
    rwa [show 10 + (j - 10) = j by omega] at this
  refine ⟨?_, ⟨osHead_sf c, fun m hm ↦ absurd hm (by simp [osHead]), fun p hp ↦ absurd hp (by simp [osHead])⟩,
    v, ha⟩
  obtain ⟨l0, l1⟩ := hr C rd hH
  have er : σ' (.n osRoots) = P 3 := by rw [w 17 (by omega) (by omega)]; rfl
  simp only [osHead, osHeap, osCst, osLd, List.cons_append, List.nil_append, er,
    allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, holds_load, holds_hint, true_and]
  simp (disch := omega) only [w, Nat.reduceSub, headVals, List.getD_cons_zero, List.getD_cons_succ,
    ha 6 (by omega), ha 7 (by omega), true_and]
  exact ⟨l0, l1, trivial⟩

/-- The head's buffers: buffer `i`'s size word at `10 + 2i`, its pointer at `11 + 2i`. -/
theorem headVals_at {c : OsCfg} {P : ℕ → E} {σ' : Val}
    (h : ∀ j < 26, σ' (.n (10 + j)) = (headVals c P).getD j 0) (i : ℕ) (hi : i < 13) :
    σ' (.n (10 + 2 * i)) = gw ((headSizes c).getD i 0) ∧ σ' (.n (11 + 2 * i)) = P i := by
  rw [h (2 * i) (by omega), show 11 + 2 * i = 10 + (2 * i + 1) by omega, h (2 * i + 1) (by omega)]
  interval_cases i <;> simp [headVals, headSizes]

end
end LeanVM.Guest.B1.Whir
