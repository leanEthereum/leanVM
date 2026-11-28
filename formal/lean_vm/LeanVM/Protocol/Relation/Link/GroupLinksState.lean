/-
  LeanVM.Protocol.Relation.Link.GroupLinksState

  The state link's part of the drawn group's polynomial: the index claim less the cycle pointers'
  shares is the state identity's defect at `(ζ, γ_state)`.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksRest

/-!
# The state part

`lk_state_diff`: for one-hot pointers, `indexClaim − lkStatePart` at a draw is
`−Σ_j eq(ζ, j)·⟨(1, γ), Err(j)⟩`, `StateLink.lean`'s defect of (I) at the draw's `ζ` and
`γ_state`: the index claim is the scalar identity's right side, the cycle pointers' shares its left
side (`lkStatePart_eq`, through `scalarLhs_rows`). Hence `lk_state_zero` (the state link holds: the
part vanishes) and `lk_state_ne` (it fails: a draw with `θ = 0`, so no other share, where the
polynomial is nonzero).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-! ## The scalar identity's left side, row by row -/

section Rows

variable {R : Type} [Fintype R] {W : ℕ}

omit [Fintype R] in
theorem dotAug_finsum {k : ℕ} (γ : Fin k → E) (S : Finset R) (f : R → Fin (k + 1) → E) :
    dotAug γ (∑ u ∈ S, f u) = ∑ u ∈ S, dotAug γ (f u) := by
  simp only [dotAug, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem sum_eqAt_fiber (σ : R → Fin (2 ^ W)) (e : ℕ → E) (g : R → E) :
    ∑ j ∈ range (2 ^ W), e j * ∑ u ∈ fiber σ j, g u = ∑ u, e (σ u) * g u := by
  have h : ∀ j ∈ range (2 ^ W), e j * ∑ u ∈ fiber σ j, g u = ∑ u ∈ fiber σ j, e (σ u) * g u := by
    intro j _
    rw [Finset.mul_sum]
    exact sum_congr rfl fun u hu ↦ by rw [mem_fiber.mp hu]
  rw [sum_congr rfl h]
  exact Finset.sum_fiberwise_of_maps_to (g := fun u ↦ (σ u : ℕ)) (fun u _ ↦ mem_range.mpr (σ u).2) _

/-- **The scalar identity's left side, row by row.** -/
theorem scalarLhs_rows {k : ℕ} (σ : R → Fin (2 ^ W)) (s s' : R → Fin k → E) (ζ : Fin W → E)
    (γ : Fin k → E) :
    scalarLhs σ s s' ζ γ = ∑ u, (eqAt (List.ofFn ζ) (σ u) * dotAug γ (aug (s u)) -
      (if (σ u : ℕ) + 1 < 2 ^ W then eqAt (List.ofFn ζ) ((σ u : ℕ) + 1) else 0) * dotAug γ (aug (s' u))) := by
  rw [sum_sub_distrib, scalarLhs]
  simp only [scatter, dotAug_finsum]
  rw [sum_eqAt_fiber σ (eqAt (List.ofFn ζ)) fun u ↦ dotAug γ (aug (s u))]
  congr 1
  have hW : 2 ^ W = 2 ^ W - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  have h2 : ∑ j ∈ range (2 ^ W - 1), eqAt (List.ofFn ζ) (j + 1) *
      ∑ u ∈ fiber σ j, dotAug γ (aug (s' u)) =
      ∑ j ∈ range (2 ^ W), (if j + 1 < 2 ^ W then eqAt (List.ofFn ζ) (j + 1) else 0) *
        ∑ u ∈ fiber σ j, dotAug γ (aug (s' u)) := by
    conv_rhs => rw [hW, sum_range_succ]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), zero_mul, add_zero]
    exact sum_congr rfl fun j hj ↦ by
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by have := mem_range.mp hj; omega))]
  rw [h2, sum_eqAt_fiber σ (fun j ↦ if j + 1 < 2 ^ W then eqAt (List.ofFn ζ) (j + 1) else 0)]

end Rows

/-! ## The draw's `ζ` and `γ_state` -/

/-- The draw's `ζ`, as a point. -/
def lkZeta (layout : Layout) (chunks : Chunks) (v : Fin (linkDrawn layout chunks + 1) → E) :
    Fin chunks.width → E :=
  fun i ↦ (chV layout chunks v).zeta.getD i 0

/-- The draw's `γ_state`. -/
def lkGammaS (layout : Layout) (chunks : Chunks) (v : Fin (linkDrawn layout chunks + 1) → E) : Fin 2 → E :=
  fun i ↦ (chV layout chunks v).gammaState.getD i 0

theorem ofFn_lkZeta {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (v : Fin (linkDrawn layout chunks + 1) → E) :
    List.ofFn (lkZeta layout chunks v) = (chV layout chunks v).zeta := by
  refine List.ext_getElem (by rw [List.length_ofFn, chV_zeta_length hch v]) fun i h1 h2 ↦ ?_
  rw [List.getElem_ofFn]
  simp only [lkZeta]
  rw [List.getD_eq_getElem _ _ h2]

theorem stateGamma_dotAug (ch : LinkCh) (pc fp : E) :
    ch.stateGamma pc fp = dotAug (fun i : Fin 2 ↦ ch.gammaState.getD i 0) (aug ![pc, fp]) := by
  simp [dotAug_eq, Fin.sum_univ_two, aug_zero, aug_succ, LinkCh.stateGamma]
  ring

/-- **The index claim is the scalar identity's right side.** -/
theorem indexClaim_eq_rhs {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (v : Fin (linkDrawn layout chunks + 1) → E) :
    indexClaim layout chunks (List.ofFn v).tail =
      scalarRhs (linkCycles layout) linkInit (linkFinal layout) (lkZeta layout chunks v) (lkGammaS layout chunks v) := by
  rw [indexClaim_eq_ch layout chunks ((List.ofFn v).headD 0), scalarRhs, ofFn_lkZeta hch v, CharTwo.sub_eq_add,
    stateGamma_dotAug, stateGamma_dotAug]
  rfl

/-! ## The cycle pointers' shares -/

theorem linkShiftEq_boolL {ζ : List E} {σ : ℕ} (hσ : σ < 2 ^ ζ.length) :
    linkShiftEq ζ (boolL ζ.length σ) = if σ + 1 < 2 ^ ζ.length then eqAt ζ (σ + 1) else 0 := by
  rw [linkShiftEq, linkShiftEq_eq_shiftSum _ _ (by rw [length_boolL]), shiftSum]
  rw [sum_eq_single σ]
  · rw [eqAt_boolL hσ hσ]; simp
  · intro j hj hne
    rw [eqAt_boolL (mem_range.mp hj) hσ]
    simp [hne]
  · intro h; exact absurd (mem_range.mpr hσ) h

/-- **A cycle pointer's share at an executed row**: the row's state at its cycle, its successor at
the next. -/
theorem lkPtrC_zero_row {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (v : Fin (linkDrawn layout chunks + 1) → E) {t u : ℕ} (ht : t < nTables)
    (hu : u < tableRowCount layout t) {σ : ℕ} (hσ : σ < 2 ^ chunks.width) :
    lkPtrC layout chunks q (chV layout chunks v) (boolL (linkRows layout) u)
        (honestValues layout q (boolL (linkRows layout) u)) σ t 0 =
      eqAt (List.ofFn (lkZeta layout chunks v)) σ *
          dotAug (lkGammaS layout chunks v) (aug (rowState layout q ⟨⟨t, ht⟩, ⟨u, hu⟩⟩)) +
        (if σ + 1 < 2 ^ chunks.width then eqAt (List.ofFn (lkZeta layout chunks v)) (σ + 1) else 0) *
          dotAug (lkGammaS layout chunks v) (aug (rowNext layout q ⟨⟨t, ht⟩, ⟨u, hu⟩⟩)) := by
  have hT := (announced_facts hA).2.1
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  have hrows : layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t := tableRows_le_height hA ht
  have hu2 : u < 2 ^ heightOf layout t := lt_of_lt_of_le hu hrows
  have hζ := chV_zeta_length hch v
  have hact : lessThan ((boolL (linkRows layout) u).take (heightOf layout t)) (layout.tableRows.getD t 0) = 1 := by
    rw [take_boolL (heightOf_le layout t), Nat.mod_eq_of_lt hu2, lessThan_boolL hu2 hrows]
    exact ite_eq_left_of_eq_true _ _ (eq_true hu)
  have hcols := lkt_cols t ht
  have htab : layout.tables.getD t default = tables.getD t default := by rw [hT]
  have hptr : ptrsOf layout t = (tables.getD t default).links.pointers := ptrsOf_eq hA ht
  have hcol : ∀ c, c < (tables.getD t default).width ∧ c ∉ (tables.getD t default).links.pointers →
      (lkVals layout (honestValues layout q (boolL (linkRows layout) u)) t).getD c 0 = tableValue layout q t c u := by
    intro c ⟨h1, h2⟩
    exact lkVals_bool layout q (hTlen ▸ ht) hu2 (htab ▸ h1) (hptr ▸ h2)
  obtain ⟨hpc, hfp, -, hnext, -⟩ := hcols
  have hz : (chV layout chunks v).zeta = List.ofFn (lkZeta layout chunks v) := (ofFn_lkZeta hch v).symm
  simp only [lkPtrC, lkIdxB, lkIdx, idxAt, hact, one_mul]
  rw [show (boolL chunks.width σ) = boolL (chV layout chunks v).zeta.length σ by rw [hζ], eqEval_boolL,
    linkShiftEq_boolL (by rw [hζ]; exact hσ), hζ, hz]
  rw [stateGamma_dotAug, stateGamma_dotAug, htab]
  have e1 : (lkVals layout (honestValues layout q (boolL (linkRows layout) u)) t).getD
      (tables.getD t default).links.stateLink.pc 0 = tableValue layout q t (tables.getD t default).links.stateLink.pc u :=
    hcol _ hpc
  have e2 : (lkVals layout (honestValues layout q (boolL (linkRows layout) u)) t).getD
      (tables.getD t default).links.stateLink.fp 0 = tableValue layout q t (tables.getD t default).links.stateLink.fp u :=
    hcol _ hfp
  have e3 : ∀ f ∈ [(tables.getD t default).links.stateLink.next.1, (tables.getD t default).links.stateLink.next.2],
      f.evaluate (fun c ↦ (lkVals layout (honestValues layout q (boolL (linkRows layout) u)) t).getD c 0) =
        f.evaluate fun c ↦ tableValue layout q t c u := by
    intro f hf
    refine form_evaluate_congr f fun c hc ↦ hcol c (hnext c ?_)
    rcases List.mem_pair.mp hf with rfl | rfl
    · exact List.mem_append_left _ hc
    · exact List.mem_append_right _ hc
  rw [e1, e2, e3 _ (by simp), e3 _ (by simp)]
  simp only [rowState, rowNext, tableAt, htab]
  rfl

/-- An executed row's cycle, decoded, is its cycle pointer column's index. -/
theorem rowCycle_word {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hone : PointersOneHot layout q chunks) {t u : ℕ} (ht : t < nTables) (hu : u < tableRowCount layout t) :
    (rowCycle layout q chunks ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ : ℕ) = ptrIndex chunks (wordAt layout q t 0 u) ∧
      ptrIndex chunks (wordAt layout q t 0 u) < 2 ^ chunks.width := by
  have hT := (announced_facts hA).2.1
  have h2 := two_le_ptrsOf hA ht
  obtain ⟨hw, hp⟩ := wordAt_eq hA q ht (show 0 < (ptrsOf layout t).length by omega) u
  have hc : (ptrsOf layout t).getD 0 0 = (tableAt layout t).links.stateLink.cycle := by
    have h := congrArg (fun l : List ℕ ↦ l.getD 0 0) (lkt_pointers t ht).1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take] at h
    rw [ptrsOf_eq hA ht, tableAt, hT]
    simpa [List.getD_eq_getElem?_getD] using h
  have hlt := ptrIndex_lt hch (wordAt layout q t 0 u) (by rw [hw]; exact hone t ht u hu _ hp)
  refine ⟨?_, hlt⟩
  simp only [rowCycle, rowPtr]
  rw [← hc, ← hw, Nat.mod_eq_of_lt hlt]

/-- **The cycle pointers' shares are the scalar identity's left side.** -/
theorem lkStatePart_eq {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hone : PointersOneHot layout q chunks) (v : Fin (linkDrawn layout chunks + 1) → E) :
    lkStatePart layout chunks q v = scalarLhs (rowCycle layout q chunks) (rowState layout q) (rowNext layout q)
      (lkZeta layout chunks v) (lkGammaS layout chunks v) := by
  rw [scalarLhs_rows, lkStatePart, Fintype.sum_sigma, Finset.sum_range]
  refine Fintype.sum_congr _ _ fun t ↦ ?_
  rw [Finset.sum_range]
  refine Fintype.sum_congr _ _ fun u ↦ ?_
  obtain ⟨hc, hlt⟩ := rowCycle_word hA q hch hone t.2 u.2
  rw [lkPtrC_zero_row hA q hch v t.2 u.2 hlt, hc, CharTwo.sub_eq_add]

/-- **The state part is the state identity's defect** at the draw's `ζ` and `γ_state`. -/
theorem lk_state_diff {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hT : linkCycles layout < 2 ^ chunks.width) (hone : PointersOneHot layout q chunks)
    (v : Fin (linkDrawn layout chunks + 1) → E) :
    indexClaim layout chunks (List.ofFn v).tail - lkStatePart layout chunks q v =
      -∑ j ∈ range (2 ^ chunks.width), eqAt (List.ofFn (lkZeta layout chunks v)) j *
        dotAug (lkGammaS layout chunks v) (defect (linkCycles layout) (rowCycle layout q chunks)
          (rowState layout q) (rowNext layout q) linkInit (linkFinal layout) j) := by
  rw [indexClaim_eq_rhs hch, lkStatePart_eq hA q hch hone, ← scalarLhs_sub_scalarRhs hT]
  ring

/-- **The state link holds**: the state part vanishes. -/
theorem lk_state_zero {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hT : linkCycles layout < 2 ^ chunks.width) (hone : PointersOneHot layout q chunks)
    (hs : StateHolds layout q chunks) (v : Fin (linkDrawn layout chunks + 1) → E) :
    indexClaim layout chunks (List.ofFn v).tail - lkStatePart layout chunks q v = 0 := by
  rw [lk_state_diff hA q hch hT hone v]
  have hd := linkHolds_iff_defect.mp hs
  rw [sum_eq_zero fun j hj ↦ by rw [hd j (mem_range.mp hj)]; simp [dotAug]]
  simp

/-! ## No other share at `θ = 0` -/

theorem lkRead_const_zero (p : ℕ) (m : E) : lkRead p (fun _ _ ↦ (0 : E)) m = fun _ ↦ 0 := by
  funext rd
  cases rd <;> simp [lkRead]

/-- **At `θ = 0` the rest vanishes**: every base term and every program or memory share carries `ω`. -/
theorem lkRest_zero_of_theta {layout : Layout} {chunks : Chunks} {μ : ℕ} (q : Column μ)
    (v : Fin (linkDrawn layout chunks + 1) → E) (hθ : ∀ t, (chV layout chunks v).theta.getD t 0 = 0) :
    lkRest layout chunks q v = 0 := by
  refine sum_eq_zero fun t _ ↦ sum_eq_zero fun u _ ↦ ?_
  have hom : omegaOf layout (chV layout chunks v) (boolL (linkRows layout) u) t = 0 := by
    rw [omegaOf, omegaAt, hθ t, zero_mul]
  have hb : lkBaseC layout (chV layout chunks v) (boolL (linkRows layout) u)
      (honestValues layout q (boolL (linkRows layout) u)) t = 0 := by
    rw [lkBaseC]
    simp only [hom, zero_mul]
  rw [hb, zero_add]
  refine sum_eq_zero fun k hk ↦ ?_
  have hk1 : 1 ≤ k := (mem_Ico.mp hk).1
  rcases k with _ | _ | k
  · omega
  · simp only [lkPtrC, hom, zero_mul]
  · simp only [lkPtrC, hom, zero_mul, lkRead_const_zero, List.map_const', List.sum_replicate, smul_zero,
      add_zero]

/-! ## The state link failing -/

/-- **The state link fails**: at `θ = 0`, `ζ` the failing cycle's bits and `γ_state` picking a
nonzero coordinate of its defect, the drawn group's polynomial is nonzero. -/
theorem lk_state_ne {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hT : linkCycles layout < 2 ^ chunks.width) (hone : PointersOneHot layout q chunks)
    (hs : ¬ StateHolds layout q chunks) :
    ∃ x : lkp_Vals, groupF layout chunks q (lkp_set layout chunks x) ≠ 0 := by
  unfold StateHolds at hs
  rw [linkHolds_iff_defect] at hs
  push Not at hs
  obtain ⟨m, hm, hne⟩ := hs
  set e := defect (linkCycles layout) (rowCycle layout q chunks) (rowState layout q) (rowNext layout q)
    linkInit (linkFinal layout) m
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin 2 → E, dotAug γ e ≠ 0 := by
    by_cases h0 : e 0 = 0
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      refine Fin.cases (fun h ↦ absurd h0 h) (fun l hl ↦ ⟨Pi.single l 1, ?_⟩) i hi
      simpa [dotAug_eq, h0, Pi.single_apply] using hl
    · exact ⟨0, by simpa [dotAug_eq] using h0⟩
  let x : lkp_Vals :=
    { theta := fun _ ↦ 0, gammaState := fun i ↦ if h : i < 2 then γ ⟨i, h⟩ else 0,
      gammaMem := fun _ ↦ 0, mu := fun _ _ ↦ 0, alpha := fun _ ↦ 0, etaMem := 0, etaBc := 0,
      eps := fun _ ↦ 0, tau := fun _ ↦ 0, zeta := fun i ↦ if m.testBit i then 1 else 0, nu := fun _ ↦ 0 }
  refine ⟨x, ?_⟩
  have hθ : ∀ t, (chV layout chunks (lkp_set layout chunks x)).theta.getD t 0 = 0 := by
    intro t
    rw [lkp_chV_theta hch]
    simp [x, List.getD_eq_getElem?_getD]
  have hz : lkZeta layout chunks (lkp_set layout chunks x) = bits m := by
    funext i
    simp [lkZeta, lkp_chV_zeta hch, bits, x, List.getD_eq_getElem?_getD]
  have hg : lkGammaS layout chunks (lkp_set layout chunks x) = γ := by
    funext i
    fin_cases i <;> simp [lkGammaS, lkp_chV_gammaState hch, x]
  rw [lk_groupF_split hA q hch hone, lkRest_zero_of_theta q _ hθ, sub_zero, lk_state_diff hA q hch hT hone,
    hz, hg]
  have h' := sum_eqAt_bits (F := E) hm (fun j ↦ dotAug γ (defect (linkCycles layout) (rowCycle layout q chunks)
    (rowState layout q) (rowNext layout q) linkInit (linkFinal layout) j))
  simp only [smul_eq_mul] at h'
  rw [h', neg_ne_zero]
  exact hγ

end

end LeanVM.Protocol.Relation

/-- info: 'LeanVM.Protocol.Relation.lk_state_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.lk_state_ne

/-- info: 'LeanVM.Protocol.Relation.lk_state_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.lk_state_zero
