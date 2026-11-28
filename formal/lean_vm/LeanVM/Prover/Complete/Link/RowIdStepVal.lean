/-
  LeanVM.Prover.Complete.Link.RowIdStepVal

  The value at a row of the terms one pointer column's step adds.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdWord

/-!
# A pointer column's terms at a row

`stepTerms_val`: at row `u`, over any tables whose entries at the step's positions are its tables'
(`stepTabs`), the step's terms sum to
`ω·c_ω·D_0·R + act·c_act·D_0·R + Σ_{shifted} η_mem·Y·μ·ω·gate·T_s·R + Σ_i e_i·(ω·D_i·D̄_i + π_i·ω)`,
`R = Π_{i ≥ 1} D_i`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset

theorem mem_foldl_shifts : ∀ (l : List (Access × E)) (ss : List ℕ),
    (∀ s ∈ ss, s ∈ l.foldl (fun ss (a, _) ↦
      if a.shift = 0 ∨ ss.contains a.shift then ss else ss ++ [a.shift]) ss) ∧
    ∀ am ∈ l, am.1.shift ≠ 0 → am.1.shift ∈ l.foldl (fun ss (a, _) ↦
      if a.shift = 0 ∨ ss.contains a.shift then ss else ss ++ [a.shift]) ss
  | [], ss => ⟨fun s hs ↦ hs, fun _ h ↦ by simp at h⟩
  | am :: l, ss => by
    obtain ⟨h1, h2⟩ := mem_foldl_shifts l
      (if am.1.shift = 0 ∨ ss.contains am.1.shift then ss else ss ++ [am.1.shift])
    have hk : ∀ s ∈ ss, s ∈ (if am.1.shift = 0 ∨ ss.contains am.1.shift then ss
        else ss ++ [am.1.shift]) := by
      intro s hs; split <;> simp [hs]
    refine ⟨fun s hs ↦ h1 s (hk s hs), fun x hx hne ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · refine h1 _ ?_
      split
      · next h =>
        rcases h with h | h
        · exact absurd h hne
        · simpa using h
      · simp
    · exact h2 x hx hne

theorem mem_shiftsAt {links : Links} {mu : List E} {p : ℕ} {am : Access × E}
    (h : am ∈ accessesAt links mu p) (hne : am.1.shift ≠ 0) :
    am.1.shift ∈ shiftsAt links mu p :=
  (mem_foldl_shifts _ []).2 am h hne

section Step

variable (W : Witness) (inp : RowInputs) (t q₀ : ℕ)

/-- The step's `R = Π_{i ≥ 1} D_i` at row `u`. -/
def stepRest (u p k : ℕ) : E :=
  ((List.range (W.chunks.d - 1)).map fun i ↦ tv (stepTabs W inp t p k) u (2 + (i + 1))).prod

theorem restAt_val (T : Array (Array E)) (u pos p k : ℕ)
    (hT : ∀ j < (stepTabs W inp t p k).size, tv T u (pos + j) = tv (stepTabs W inp t p k) u j) :
    ((restAt W.chunks.d pos).toList.map (tv T u)).prod = stepRest W inp t u p k := by
  have hsize := size_stepTabs W inp t p k
  unfold restAt stepRest
  rw [List.toList_toArray, List.map_map]
  refine congrArg _ (List.map_congr_left fun i hi ↦ ?_)
  have hi' := List.mem_range.mp hi
  simp only [Function.comp_apply]
  rw [show pos + 2 + 1 + i = pos + (2 + (i + 1)) by omega, hT _ (by omega)]

theorem stepTerms_head (T : Array (Array E)) (u pos p k : ℕ)
    (hT : ∀ j < (stepTabs W inp t p k).size, tv T u (pos + j) = tv (stepTabs W inp t p k) u j)
    (hd : 1 ≤ W.chunks.d) :
    termAt ⟨T, #[]⟩ u (1, #[0, pos, pos + 2] ++ restAt W.chunks.d pos) +
        termAt ⟨T, #[]⟩ u (1, #[1, pos + 1, pos + 2] ++ restAt W.chunks.d pos) =
      tv T u 0 * tv (stepTabs W inp t p k) u 0 * tv (stepTabs W inp t p k) u 2 *
          stepRest W inp t u p k +
        tv T u 1 * tv (stepTabs W inp t p k) u 1 * tv (stepTabs W inp t p k) u 2 *
          stepRest W inp t u p k := by
  have hsize := size_stepTabs W inp t p k
  have h0 : tv T u pos = tv (stepTabs W inp t p k) u 0 := by simpa using hT 0 (by omega)
  have h1 : tv T u (pos + 1) = tv (stepTabs W inp t p k) u 1 := hT 1 (by omega)
  have h2 : tv T u (pos + 2) = tv (stepTabs W inp t p k) u 2 := hT 2 (by omega)
  have hr := restAt_val W inp t T u pos p k hT
  rw [termAt_eq, termAt_eq]
  simp only [Array.toList_append, List.map_append, List.prod_append, hr]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, h0, h1, h2]
  ring

theorem stepTerms_shift (T : Array (Array E)) (u pos p k : ℕ)
    (hT : ∀ j < (stepTabs W inp t p k).size, tv T u (pos + j) = tv (stepTabs W inp t p k) u j)
    (am : Access × E) (ham : am ∈ accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) p)
    (hne : am.1.shift ≠ 0) :
    termAt ⟨T, #[]⟩ u (shiftTerm inp W.chunks.d pos
        (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p) am) =
      inp.ch.etaMem * inp.yMem * am.2 * (tv T u 0 *
        (am.1.gate.map fun g ↦ tv T u (3 + g)).getD 1 *
        tv (stepTabs W inp t p k) u (2 + 2 * W.chunks.d +
          (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p).idxOf am.1.shift) *
        stepRest W inp t u p k) := by
  have hsize := size_stepTabs W inp t p k
  have hidx := List.idxOf_lt_length_of_mem (mem_shiftsAt ham hne)
  have hr := restAt_val W inp t T u pos p k hT
  have hT' := hT (2 + 2 * W.chunks.d +
    (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p).idxOf am.1.shift) (by omega)
  rw [← Nat.add_assoc, ← Nat.add_assoc] at hT'
  unfold shiftTerm
  rw [termAt_eq]
  simp only [Array.toList_append, List.map_append, List.prod_append, hr]
  cases am.1.gate
  · simp only [Option.map_none, Option.getD_none, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, hT', List.toList_toArray]
    ring
  · simp only [Option.map_some, Option.getD_some, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, hT', List.toList_toArray]
    ring

theorem stepTerms_cert (T : Array (Array E)) (u pos p k : ℕ)
    (hT : ∀ j < (stepTabs W inp t p k).size, tv T u (pos + j) = tv (stepTabs W inp t p k) u j)
    {i : ℕ} (hi : i < W.chunks.d) :
    termAt ⟨T, #[]⟩ u (inp.cert * inp.ch.eps.getD (q₀ + k) 0 * inp.ch.nu.getD i 0,
        #[0, pos + 2 + i, pos + 2 + W.chunks.d + i]) +
      termAt ⟨T, #[]⟩ u (inp.cert * inp.ch.eps.getD (q₀ + k) 0 * inp.ch.nu.getD i 0 *
        inp.functionals.mirrors.getD i 0, #[0]) =
      inp.cert * inp.ch.eps.getD (q₀ + k) 0 * inp.ch.nu.getD i 0 *
        (tv T u 0 * (tv (stepTabs W inp t p k) u (2 + i) *
          tv (stepTabs W inp t p k) u (2 + (W.chunks.d + i)) + inp.functionals.mirrors.getD i 0)) := by
  have hsize := size_stepTabs W inp t p k
  have ha := hT (2 + i) (by omega)
  have hb := hT (2 + (W.chunks.d + i)) (by omega)
  rw [← Nat.add_assoc] at ha
  rw [← Nat.add_assoc, ← Nat.add_assoc] at hb
  rw [termAt_eq, termAt_eq]
  simp [ha, hb]
  ring

/-- **The value of a pointer column's step at row `u`**, over the tables `T`. -/
def stepVal (T : Array (Array E)) (u p k : ℕ) : E :=
  let ST := stepTabs W inp t p k
  let links := (tables.getD t default).links
  let mu := inp.ch.mu.getD t []
  let e := inp.cert * inp.ch.eps.getD (q₀ + k) 0
  tv T u 0 * tv ST u 0 * tv ST u 2 * stepRest W inp t u p k +
    tv T u 1 * tv ST u 1 * tv ST u 2 * stepRest W inp t u p k +
    (((accessesAt links mu p).filter (fun am ↦ !decide (am.1.shift = 0))).map fun am ↦
      inp.ch.etaMem * inp.yMem * am.2 * (tv T u 0 * (am.1.gate.map fun g ↦ tv T u (3 + g)).getD 1 *
        tv ST u (2 + 2 * W.chunks.d + (shiftsAt links mu p).idxOf am.1.shift) *
        stepRest W inp t u p k)).sum +
    ((List.range W.chunks.d).map fun i ↦ e * inp.ch.nu.getD i 0 *
      (tv T u 0 * (tv ST u (2 + i) * tv ST u (2 + (W.chunks.d + i)) +
        inp.functionals.mirrors.getD i 0))).sum

theorem sum_map_flatMap_pair {α : Type} (f : E × Array ℕ → E) (a b : α → E × Array ℕ) :
    ∀ l : List α, ((l.flatMap fun x ↦ [a x, b x]).map f).sum = (l.map fun x ↦ f (a x) + f (b x)).sum
  | [] => by simp
  | x :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_map_flatMap_pair f a b l, List.map_nil, List.sum_nil]
    ring

/-- **The step's terms at row `u`.** -/
theorem stepTerms_val (T : Array (Array E)) (u pos p k : ℕ) (hd : 1 ≤ W.chunks.d)
    (hT : ∀ j < (stepTabs W inp t p k).size, tv T u (pos + j) = tv (stepTabs W inp t p k) u j) :
    ((stepTerms W inp t q₀ pos p k).map (termAt ⟨T, #[]⟩ u)).sum = stepVal W inp t q₀ T u p k := by
  unfold stepTerms stepVal
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [stepTerms_head W inp t T u pos p k hT hd, sum_map_flatMap_pair, List.map_map]
  congr 2
  · refine congrArg _ (List.map_congr_left fun am ham ↦ ?_)
    obtain ⟨hmem, hne⟩ := List.mem_filter.mp ham
    exact stepTerms_shift W inp t T u pos p k hT am hmem (by simpa using hne)
  · refine List.map_congr_left fun i hi ↦ ?_
    exact stepTerms_cert W inp t q₀ T u pos p k hT (List.mem_range.mp hi)

/-- **The pointer columns' fold**: it appends every step's tables and terms, and the terms sum at
row `u`, over any tables extending the result, to the steps' values. -/
theorem pointerFold (hd : 1 ≤ W.chunks.d) : ∀ (L : List (ℕ × ℕ)) (tabs : Array (Array E))
    (terms : Array (E × Array ℕ)), ∃ X Y,
      L.foldl (rowPointerStep W inp t q₀) (tabs, terms, tabs.size) =
        (tabs ++ X, (terms.toList ++ Y).toArray, (tabs ++ X).size) ∧
      ∀ (u : ℕ) (C : Array (Array E)), ((Y.map (termAt ⟨tabs ++ X ++ C, #[]⟩ u)).sum =
        (L.map fun pk ↦ stepVal W inp t q₀ (tabs ++ X ++ C) u pk.1 pk.2).sum)
  | [], tabs, terms => ⟨#[], [], by simp, fun _ C ↦ by simp⟩
  | (p, k) :: L, tabs, terms => by
    obtain ⟨X, Y, hR, hY⟩ := pointerFold hd L (tabs ++ stepTabs W inp t p k)
      (terms.toList ++ stepTerms W inp t q₀ tabs.size p k).toArray
    refine ⟨stepTabs W inp t p k ++ X, stepTerms W inp t q₀ tabs.size p k ++ Y, ?_, fun u C ↦ ?_⟩
    · rw [List.foldl_cons, rowPointerStep_eq, ← Array.size_append, hR]
      simp [Array.append_assoc]
    · have hT : ∀ j < (stepTabs W inp t p k).size,
          tv (tabs ++ (stepTabs W inp t p k ++ (X ++ C))) u (tabs.size + j) =
            tv (stepTabs W inp t p k) u j := by
        intro j hj
        rw [tv_append_right, tv_append_left _ _ hj]
      have hY' := hY u C
      simp only [Array.append_assoc] at hY' ⊢
      rw [List.map_append, List.sum_append, stepTerms_val W inp t q₀ _ u tabs.size p k hd hT, hY',
        List.map_cons, List.sum_cons]

end Step

end LeanVM.Prover.Complete.RowId

end
