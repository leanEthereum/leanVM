/-
  LeanVM.Guest.B1.Whir.CHead

  The head of open_stacked honestly: the twelve fixed buffers allocated at given pointers, the
  root stored into `level_roots`, the positions' totals by rate, the zero run.
-/

module

public import LeanVM.Guest.B1.Whir.CBlk

/-!
# The head, honestly

`headSizes c`: the fixed buffers' sizes in allocation order (`osSizesL c`'s first twelve);
`headVals c P sel pt`: the values from `11`: the nine heap buffers' sizes `g^size` and pointers
`P i`, `pos_totals`' pointer `P 9`, the totals by rate, `P 9` times the rate's selector `sel`, the
rate's total `pt`, the positions' and window pointers' buffers `P 10`, `P 11`, the zero run.
`osHead_complete`: the head as a block at fixed values, the root's two cells (the arguments `7`,
`8`) stored at `level_roots`, the totals at `pos_totals`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

/-- The fixed buffers' sizes, in allocation order (`osSizesL c`'s first twelve), `qt` the
positions' total. -/
def headSizes (c : OsCfg) (qt : ℕ) : List ℕ :=
  [c.yrLen + (c.levels.getD c.yrLevel default).folds, 2 * c.levels.length, c.nFolds, 2 * c.nFolds,
    c.levels.length, c.levels.length, c.levels.length * hsStride, c.levels.length * ligColsCap,
    c.levels.length, ligNRates, qt, qt]

/-- The head's values from `11`. -/
def headVals (c : OsCfg) (P : ℕ → E) (sel pt : E) : List E :=
  [gw (c.yrLen + (c.levels.getD c.yrLevel default).folds), P 0, gw (2 * c.levels.length), P 1,
    gw c.nFolds, P 2, gw (2 * c.nFolds), P 3, gw c.levels.length, P 4, gw c.levels.length, P 5,
    gw (c.levels.length * hsStride), P 6, gw (c.levels.length * ligColsCap), P 7,
    gw c.levels.length, P 8, P 9] ++ (List.range ligNRates).map (fun r ↦ gw (c.posTotal.getD r 0)) ++
    [P 9 * sel, pt, P 10, P 11, word 1 0, word 0 0, word 0 0, word 0 0, word 0 0]

theorem headVals_length (c : OsCfg) (P : ℕ → E) (sel pt : E) :
    (headVals c P sel pt).length = osPadV + 5 - 11 := by
  simp [headVals, osPadV, ligNRates]

theorem holds_hint {rd : Reader} {σ : Val} (h : Hint) : (Atom.hint h).Holds rd σ ↔ True := Iff.rfl

/-- The head's state's static facts. -/
theorem osHead_sf (c : OsCfg) : (osHead c).2.Sf := by
  refine ⟨rfl, ⟨fun f hf ↦ ?_, show 9 < osPadV + 5 by simp [osPadV, ligNRates], show 6 < osPadV + 5 by simp [osPadV, ligNRates],
    fun m hm ↦ absurd hm (by simp [osHead])⟩, by show 0 < u128Bound; unfold u128Bound; positivity,
    fun p hp ↦ ?_, show 43 ≤ osPadV + 5 by simp [osPadV, ligNRates]⟩
  · have hf' : f ∈ [1, 2, 3, 4, 5] := hf
    show f < osPadV + 5
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    simp only [osPadV, ligNRates]
    omega
  · have hp' : some osPadV = some p := hp
    simp only [Option.some.injEq] at hp'
    subst hp'
    show osPadV + 4 < osPadV + 5
    omega

/-- **The head, honestly**: the fixed buffers at the pointers `P i`, the root's two cells (the
arguments `7`, `8`) stored in `level_roots` (`P 1`), the totals by rate in `pos_totals` (`P 9`), the
rate's total read at its selector `σ 0 = g^ri`. -/
theorem osHead_complete (c : OsCfg) (σ : Val) (P : ℕ → E) {ri : ℕ}
    (hsel : σ (.n osRate) = gen ^ ri) (hri : ri < ligNRates)
    (hr : ∀ C rd, HM M H C rd → LoadHolds rd (P 1) 0 (σ (.n 7)) ∧ LoadHolds rd (P 1) 1 (σ (.n 8)) ∧
      ∀ r < ligNRates, LoadHolds rd (P 9) r (gw (c.posTotal.getD r 0))) :
    BlkA M H σ 11 (osPadV + 5) (osHead c).1 (fun σ' ↦ (osHead c).2.Ok σ' ∧
      (∀ j < osPadV + 5 - 11, σ' (.n (11 + j)) =
        (headVals c P (gen ^ ri) (gw (c.posTotal.getD ri 0))).getD j 0) ∧ AgreeBelow 11 σ σ') := by
  set L := headVals c P (gen ^ ri) (gw (c.posTotal.getD ri 0)) with hL
  have hlen : L.length = osPadV + 5 - 11 := headVals_length _ _ _ _
  refine blk_lst L (by rw [hlen]; simp only [osPadV, ligNRates]; omega) fun C rd hH σ' ha hv ↦ ?_
  have v : ∀ j < osPadV + 5 - 11, σ' (.n (11 + j)) = L.getD j 0 := fun j hj ↦ hv j (by omega)
  have hpv : osPadV = 38 := by simp [osPadV, ligNRates]
  have w : ∀ j, 11 ≤ j → j < 43 → σ' (.n j) = L.getD (j - 11) 0 := fun j h1 h2 ↦ by
    have := v (j - 11) (by omega)
    rwa [show 11 + (j - 11) = j by omega] at this
  refine ⟨?_, ⟨osHead_sf c, fun m hm ↦ absurd hm (by simp [osHead]), fun p hp ↦ ?_⟩, v, ha⟩
  rotate_left
  · have hp' : some osPadV = some p := hp
    simp only [Option.some.injEq] at hp'
    subst hp'
    simp only [osPadV, ligNRates, Nat.reduceAdd]
    simp (disch := omega) only [w]
    simp [hL, headVals, ligNRates, List.range_succ]
    exact word_zero
  obtain ⟨l0, l1, lt⟩ := hr C rd hH
  have e0 : σ' (.n osRate) = gen ^ ri := by rw [ha _ (by simp [osRate]), hsel]
  have lt' : LoadHolds rd (P 9 * gen ^ ri) 0 (gw (c.posTotal.getD ri 0)) := by
    rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact lt ri hri
  simp only [osHead, osHeap, osPad, osCst, osLd, osMul, List.cons_append, List.nil_append, List.append_assoc,
    allOk_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, holds_load, holds_mul,
    holds_hint, true_and, allOk_flatten, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, e0, ha 7 (by omega), ha 8 (by omega)]
  simp only [osPadV, osPosTab, osRoots, ligNRates, Nat.reduceAdd]
  simp (disch := omega) only [w]
  simp only [hL, headVals, ligNRates, List.range_succ]
  simp
  refine ⟨l0, l1, fun a ha' ↦ ?_, by simpa using lt'⟩
  rw [w (30 + a) (by omega) (by omega)]
  have e : L.getD (30 + a - 11) 0 = gw (c.posTotal.getD a 0) := by
    interval_cases a <;> simp [hL, headVals, ligNRates, List.range_succ]
  rw [e]
  exact ⟨by simp, by simpa using lt a (by simp [ligNRates]; omega)⟩

/-- The head's heap buffers: buffer `i`'s size word at `11 + 2i`, its pointer at `12 + 2i`. -/
theorem headVals_at {c : OsCfg} {P : ℕ → E} {sel pt : E} {σ' : Val} {qt : ℕ}
    (h : ∀ j < osPadV + 5 - 11, σ' (.n (11 + j)) = (headVals c P sel pt).getD j 0) (i : ℕ) (hi : i < 9) :
    σ' (.n (11 + 2 * i)) = gw ((headSizes c qt).getD i 0) ∧ σ' (.n (12 + 2 * i)) = P i := by
  rw [h (2 * i) (by simp [osPadV, ligNRates]; omega), show 12 + 2 * i = 11 + (2 * i + 1) by omega,
    h (2 * i + 1) (by simp [osPadV, ligNRates]; omega)]
  interval_cases i <;> simp [headVals, headSizes]

end
end LeanVM.Guest.B1.Whir
