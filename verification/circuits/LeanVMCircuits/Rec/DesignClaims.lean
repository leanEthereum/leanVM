module

public import LeanVMCircuits.Rec.Edges
public import LeanVMCircuits.Rec.DesignKind

@[expose] public section

/-!
The claims a node's design makes, for every shape: what it reads of a child's statement (`Design::carried`), the statement it exposes (`Reduced::statement`), and its fresh claims on its child tier's fixed polynomial (`Design::fixed_claim`).

`edgeLayout` is the design's statement layout with each dense polynomial's and each flock circuit's variables (`StatementLayout::edge_line`); it is a layout `checkedges` accepts (`edgeLayout_ok`), of the design's length (`edgeLayout_len`). A child's carried claims are `Edges.stmtClaims` at that layout: `checkdesign` compares `Design::carried` on a statement of labeled words with it for every summarized shape (`carriedOk`).

`stmtOf` is the statement a node exposes from its reduction's outputs (`Reduced`): its kind, its digest's halves, the dense point (zero past the reduction's rounds), each dense polynomial's value (zero when unreduced), the matrices' row and column points and values. `stmtClaims_stmtOf`: the claims a parent reads off those words are the reduction's outputs (`outClaims`), so `reduced_dense_mem` and `reduced_matrix_mem`: every claim the reduction leaves is one the statement makes. `checkdesign` compares `Reduced::statement` with `stmtOf` on labeled outputs for every summarized shape (`exposedOk`).

A tier's fixed polynomial stacks each circuit's fixed columns (`FixedLayout`): column `c` of `2 ^ taus c` words at `offset taus c`, the columns of more variables first and ties by index (`stack_offsets`), in a stack of `2 ^ kappa taus` words, the tier's circuits' stacks in order of their kind's index. `offset_aligned`, `offset_disjoint` and `offset_fits`: each column's offset is a multiple of its length, no two columns overlap and every column ends within the stack. `fixedModel` is `Design::fixed_claim`: column `c`'s term is at its prefix of the point, then its block `offset / 2 ^ tau` over `kappa - tau` bits, then the child's kind bits. `term_reads`: for any values of the circuits' columns, the multilinear extension of the tier's polynomial at that point is column `c` of the circuit the kind bits select at its prefix of the point, so a fresh fixed claim is a claim on the child's own column. `checkdesign` compares `Design::fixed_claim` on labeled hints with `fixedModel` for every summarized shape at zero heights and at heights that differ per table (`fixedOk`), and each tier's `kappa` with the summary's.

`bindState` (`NodeClaims::bind_state`) binds a verified proof's final digest as two scalars that determine it (`bindState_good`, `bindState_binds`); `digestHalves` (`digest_halves_rows`) writes a digest as the statement's two halves, which a parent's `halves_to_d` reads back (`digest_roundtrip`); `digestRows` (`Kind::digest_rows`) computes the tree statement digest of a tag and items (`digestRows_good`), and `checkdesign` compares Rust's value of a tree of outputs' node digest with the model's (`nodeDigestOk`). A child's scale is zero exactly at the first level and one at every node (`nodeScale_small`, `nodeScale_two`).
-/

namespace LeanVMCircuits.Rec.DesignClaims

open LeanVMCircuits.Rec Edges Design

variable {β : Type}

/-! The layout. -/

/-- `CircuitId::k_log` of each flock circuit, in `CircuitId::ALL` order. -/
def flockKLogs : List ℕ := [10, 10, 10, 8, 8, 10, 12, 13, 13, 14, 9, 9, 9, 9, 9, 9, 9, 9, 9, 11, 12]

theorem flockKLogs_length : flockKLogs.length = nFlocks := rfl

theorem flockKLogs_le : flockKLogs.all (· ≤ maxKLog) = true := by decide

/-- `StatementLayout::edge_line` of the design: its statement's layout, each dense polynomial's variables and each flock circuit's. -/
def edgeLayout (sh : Shape) (v0 v1 : ℕ) (kappa : ℕ → ℕ) : Edges.Layout :=
  ⟨(sh.layout v0 v1 kappa).nDense, sh.nPolys, maxKLog, nFlocks, (sh.vars v0 v1 kappa).take sh.nPolys, flockKLogs⟩

theorem nPolys_le (sh : Shape) : sh.nPolys ≤ 4 := by unfold Shape.nPolys; split_ifs <;> omega

/-- The design's layout has a prefix for each polynomial and flock circuit within its points. -/
theorem edgeLayout_ok (sh : Shape) (v0 v1 : ℕ) (kappa : ℕ → ℕ) : (edgeLayout sh v0 v1 kappa).ok = true := by
  simp only [Edges.Layout.ok, edgeLayout, Bool.and_eq_true, beq_iff_eq, List.length_take]
  refine ⟨⟨⟨?_, rfl⟩, ?_⟩, flockKLogs_le⟩
  · simp only [Shape.vars, List.length_cons, List.length_nil]
    have := nPolys_le sh
    omega
  · rw [List.all_eq_true]
    intro x hx
    exact decide_eq_true (vars_le_dense sh v0 v1 kappa x (List.mem_of_mem_take hx))

theorem edgeLayout_len (sh : Shape) (v0 v1 : ℕ) (kappa : ℕ → ℕ) :
    (edgeLayout sh v0 v1 kappa).len = (sh.layout v0 v1 kappa).len := by
  rw [len_eq]
  simp [Edges.Layout.len, Edges.Layout.matsAt, Edges.Layout.colsAt, Edges.Layout.rowsAt, Edges.Layout.dv, edgeLayout,
    Shape.layout]
  omega

/-! The statement a node exposes. -/

/-- What a node's reduction leaves (`Reduced`): the dense point, one coordinate per round; each dense polynomial's value, if reduced; the matrices' row and column points; each flock circuit's two matrices' values, in order. -/
structure Reduced (β : Type) where
  point : List β
  values : List (Option β)
  rows : List β
  cols : List β
  mats : List β
  deriving DecidableEq, Repr

/-- The same outputs, each mapped by `f`. -/
def Reduced.map {α : Type} (f : α → β) (r : Reduced α) : Reduced β :=
  ⟨r.point.map f, r.values.map (·.map f), r.rows.map f, r.cols.map f, r.mats.map f⟩

/-- `Reduced::statement`: word `i` of the statement of kind word `kind` and digest halves `d0`, `d1`, every word `z` (zero) where the reduction left none. -/
def stmtOf (L : Edges.Layout) (r : Reduced β) (kind d0 d1 z : β) (i : ℕ) : β :=
  if i = 0 then kind else if i = 1 then d0 else if i = 2 then d1
  else if i < L.dv then r.point.getD (i - 3) z
  else if i < L.rowsAt then (r.values.getD (i - L.dv) none).getD z
  else if i < L.colsAt then r.rows.getD (i - L.rowsAt) z
  else if i < L.matsAt then r.cols.getD (i - L.colsAt) z
  else r.mats.getD (i - L.matsAt) z

/-- The claim the reduction's outputs make on dense polynomial `p`: at its prefix of the point (zero past the rounds), its value (zero when unreduced), scaled by `σ` on a fixed polynomial. -/
def outDense (L : Edges.Layout) (r : Reduced β) (z σ : β) (p : ℕ) : Dense β where
  poly := p
  low := (List.range (L.vars.getD p 0)).map fun i => r.point.getD i z
  terms := [{ nLow := L.vars.getD p 0, bits := 0, bitsLen := 0, top := [],
              scale := if isFixed p then some σ else none, value := (r.values.getD p none).getD z }]

/-- The claim the reduction's outputs make on flock circuit `f`'s matrix `k`. -/
def outMatrix (L : Edges.Layout) (r : Reduced β) (z : β) (f k : ℕ) : Matrix β where
  circuit := f
  row := .point ((List.range (L.klog.getD f 0)).map fun i => r.rows.getD i z)
  col := .point ((List.range (L.klog.getD f 0)).map fun i => r.cols.getD i z)
  coefs := if k = 0 then (.one, .zero) else (.zero, .one)
  value := r.mats.getD (2 * f + k) z

/-- Every claim the reduction's outputs make, in `Design::carried`'s order. -/
def outClaims (L : Edges.Layout) (r : Reduced β) (z σ : β) : Claims β where
  dense := (List.range L.nPolys).map (outDense L r z σ)
  matrices := (List.range L.nFlocks).flatMap fun f => [outMatrix L r z f 0, outMatrix L r z f 1]

section
variable (L : Edges.Layout) (r : Reduced β) (kind d0 d1 z : β)

theorem stmtOf_point (i : ℕ) (hi : i < L.nDense) : stmtOf L r kind d0 d1 z (3 + i) = r.point.getD i z := by
  have h : ¬ 3 + i = 0 ∧ ¬ 3 + i = 1 ∧ ¬ 3 + i = 2 ∧ 3 + i < L.dv := by simp only [Edges.Layout.dv]; omega
  rw [stmtOf, if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_pos h.2.2.2, Nat.add_sub_cancel_left]

theorem stmtOf_value (p : ℕ) (hp : p < L.nPolys) :
    stmtOf L r kind d0 d1 z (L.dv + p) = (r.values.getD p none).getD z := by
  have h : ¬ L.dv + p = 0 ∧ ¬ L.dv + p = 1 ∧ ¬ L.dv + p = 2 ∧ ¬ L.dv + p < L.dv ∧ L.dv + p < L.rowsAt := by
    simp only [Edges.Layout.rowsAt, Edges.Layout.dv]; omega
  rw [stmtOf, if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2.1, if_pos h.2.2.2.2, Nat.add_sub_cancel_left]

theorem stmtOf_row (i : ℕ) (hi : i < L.nMatrix) : stmtOf L r kind d0 d1 z (L.rowsAt + i) = r.rows.getD i z := by
  have h : ¬ L.rowsAt + i = 0 ∧ ¬ L.rowsAt + i = 1 ∧ ¬ L.rowsAt + i = 2 ∧ ¬ L.rowsAt + i < L.dv ∧
      ¬ L.rowsAt + i < L.rowsAt ∧ L.rowsAt + i < L.colsAt := by
    simp only [Edges.Layout.colsAt, Edges.Layout.rowsAt, Edges.Layout.dv]; omega
  rw [stmtOf, if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2.1, if_neg h.2.2.2.2.1, if_pos h.2.2.2.2.2,
    Nat.add_sub_cancel_left]

theorem stmtOf_col (i : ℕ) (hi : i < L.nMatrix) : stmtOf L r kind d0 d1 z (L.colsAt + i) = r.cols.getD i z := by
  have h : ¬ L.colsAt + i = 0 ∧ ¬ L.colsAt + i = 1 ∧ ¬ L.colsAt + i = 2 ∧ ¬ L.colsAt + i < L.dv ∧
      ¬ L.colsAt + i < L.rowsAt ∧ ¬ L.colsAt + i < L.colsAt ∧ L.colsAt + i < L.matsAt := by
    simp only [Edges.Layout.matsAt, Edges.Layout.colsAt, Edges.Layout.rowsAt, Edges.Layout.dv]; omega
  rw [stmtOf, if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2.1, if_neg h.2.2.2.2.1, if_neg h.2.2.2.2.2.1,
    if_pos h.2.2.2.2.2.2, Nat.add_sub_cancel_left]

theorem stmtOf_mat (i : ℕ) : stmtOf L r kind d0 d1 z (L.matsAt + i) = r.mats.getD i z := by
  have h : ¬ L.matsAt + i = 0 ∧ ¬ L.matsAt + i = 1 ∧ ¬ L.matsAt + i = 2 ∧ ¬ L.matsAt + i < L.dv ∧
      ¬ L.matsAt + i < L.rowsAt ∧ ¬ L.matsAt + i < L.colsAt ∧ ¬ L.matsAt + i < L.matsAt := by
    simp only [Edges.Layout.matsAt, Edges.Layout.colsAt, Edges.Layout.rowsAt, Edges.Layout.dv]; omega
  rw [stmtOf, if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2.1, if_neg h.2.2.2.2.1, if_neg h.2.2.2.2.2.1,
    if_neg h.2.2.2.2.2.2, Nat.add_sub_cancel_left]

/-- The statement's first word is its kind and its next two its digest's halves. -/
theorem stmtOf_head : stmtOf L r kind d0 d1 z 0 = kind ∧ stmtOf L r kind d0 d1 z 1 = d0 ∧
    stmtOf L r kind d0 d1 z 2 = d1 := by
  simp [stmtOf]

/-- What a parent reads off the statement a node exposes (`stmtClaims`, the claims `Design::carried` takes) is exactly what the node's reduction left (`outClaims`). -/
theorem stmtClaims_stmtOf (hL : L.ok = true) (σ : β) :
    stmtClaims L (stmtOf L r kind d0 d1 z) σ = outClaims L r z σ := by
  simp only [Edges.Layout.ok, Bool.and_eq_true, beq_iff_eq] at hL
  obtain ⟨⟨⟨-, -⟩, hv⟩, hk⟩ := hL
  simp only [stmtClaims, outClaims, Claims.mk.injEq]
  constructor
  · apply List.map_congr_left
    intro p hp
    rw [List.mem_range] at hp
    have hvp := getD_le (i := p) hv
    simp only [stmtDense, outDense, Dense.mk.injEq, List.cons.injEq, Term.mk.injEq, and_true, true_and]
    refine ⟨List.map_congr_left fun i hi => ?_, stmtOf_value L r kind d0 d1 z p hp⟩
    rw [List.mem_range] at hi
    exact stmtOf_point L r kind d0 d1 z i (by omega)
  · apply List.flatMap_congr
    intro f hf
    have hkf := getD_le (i := f) hk
    have hm : ∀ k < 2, stmtMatrix L (stmtOf L r kind d0 d1 z) f k = outMatrix L r z f k := by
      intro k hk2
      simp only [stmtMatrix, outMatrix, Matrix.mk.injEq, RowW.point.injEq, ColW.point.injEq, true_and]
      refine ⟨List.map_congr_left fun i hi => ?_, List.map_congr_left fun i hi => ?_, by rw [Nat.add_assoc]; exact stmtOf_mat L r kind d0 d1 z _⟩
      · rw [List.mem_range] at hi; exact stmtOf_row L r kind d0 d1 z i (by omega)
      · rw [List.mem_range] at hi; exact stmtOf_col L r kind d0 d1 z i (by omega)
    rw [hm 0 (by omega), hm 1 (by omega)]

theorem map_getD_range (xs : List β) (z : β) (n : ℕ) (h : n ≤ xs.length) :
    (List.range n).map (fun i => xs.getD i z) = xs.take n := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take]; omega
  · intro i h1 _
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < xs.length by omega), Option.getD_some]

/-- A claim on dense polynomial `p` at point `low`, of its first `n` coordinates, scaled by `s`, of value `v`. -/
def denseAt (p n : ℕ) (low : List β) (s : Option β) (v : β) : Dense β :=
  ⟨p, low, [⟨n, 0, 0, [], s, v⟩]⟩

/-- A dense polynomial the reduction reduced, at a point of at least its variables: its claim, at its prefix of the point, is one the statement makes. -/
theorem reduced_dense_mem (hL : L.ok = true) (σ : β) (p : ℕ) (hp : p < L.nPolys) (v : β)
    (hv : r.values.getD p none = some v) (hlen : L.vars.getD p 0 ≤ r.point.length) :
    denseAt p (L.vars.getD p 0) (r.point.take (L.vars.getD p 0)) (if isFixed p then some σ else none) v ∈
      (stmtClaims L (stmtOf L r kind d0 d1 z) σ).dense := by
  rw [stmtClaims_stmtOf L r kind d0 d1 z hL]
  refine List.mem_map.mpr ⟨p, List.mem_range.mpr hp, ?_⟩
  simp only [outDense, denseAt, hv, Option.getD_some, map_getD_range _ _ _ hlen]

/-- A flock circuit's matrix, at row and column points of at least its variables: its claim is one the statement makes. -/
theorem reduced_matrix_mem (hL : L.ok = true) (σ : β) (f : ℕ) (hf : f < L.nFlocks) (k : ℕ) (hk : k < 2)
    (hr : L.klog.getD f 0 ≤ r.rows.length) (hc : L.klog.getD f 0 ≤ r.cols.length) :
    (⟨f, .point (r.rows.take (L.klog.getD f 0)), .point (r.cols.take (L.klog.getD f 0)),
      if k = 0 then (.one, .zero) else (.zero, .one), r.mats.getD (2 * f + k) z⟩ : Matrix β) ∈
      (stmtClaims L (stmtOf L r kind d0 d1 z) σ).matrices := by
  rw [stmtClaims_stmtOf L r kind d0 d1 z hL]
  refine List.mem_flatMap.mpr ⟨f, List.mem_range.mpr hf, ?_⟩
  have hm : outMatrix L r z f k = ⟨f, .point (r.rows.take (L.klog.getD f 0)), .point (r.cols.take (L.klog.getD f 0)),
      if k = 0 then (.one, .zero) else (.zero, .one), r.mats.getD (2 * f + k) z⟩ := by
    simp only [outMatrix, map_getD_range _ _ _ hr, map_getD_range _ _ _ hc]
  rw [← hm]
  interval_cases k <;> simp

/-- A node's statement claims are its reduction's: if the words a parent reads as a node's statement are, on the layout, those `Reduced::statement` writes from the node's reduction outputs `r`, the statement's claims hold exactly when the outputs' claims do, so the tree's step at a node (`hstep` of `Edges.tree_sound_parts`) is the reduction's soundness on `outClaims`. -/
theorem stmt_exposed {L : Edges.Layout} (hL : L.ok = true) (x : ℕ → β) (r : Reduced β) (kind d0 d1 z σ : β)
    (hx : ∀ i < L.len, x i = stmtOf L r kind d0 d1 z i) (tD : Dense β → Prop) (tM : Matrix β → Prop) :
    (stmtClaims L x σ).Holds tD tM ↔ (outClaims L r z σ).Holds tD tM := by
  rw [stmtClaims_congr hL σ hx, stmtClaims_stmtOf L r kind d0 d1 z hL]

end

/-! A tier's fixed polynomial. -/

section Fixed

/-- Whether column `j` is stacked before column `c` (`stack_offsets`' order): more variables, or as many and a lower index. -/
def before (taus : List ℕ) (j c : ℕ) : Bool :=
  taus.getD c 0 < taus.getD j 0 || (taus.getD j 0 == taus.getD c 0 && j < c)

/-- Column `c`'s offset in a circuit's stack: the lengths of the columns before it. -/
def offset (taus : List ℕ) (c : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range taus.length).filter (fun j => before taus j c = true), 2 ^ taus.getD j 0

/-- The columns' total length (`stack_offsets`' `placed`). -/
def placed (taus : List ℕ) : ℕ := ∑ j ∈ Finset.range taus.length, 2 ^ taus.getD j 0

/-- `FixedLayout::kappa`: the stack's variables. -/
def kappa (taus : List ℕ) : ℕ := Nat.clog 2 (max (placed taus) 1)

/-- `FixedLayout::block`: column `c`'s offset over its length. -/
def block (taus : List ℕ) (c : ℕ) : ℕ := offset taus c / 2 ^ taus.getD c 0

theorem before_trans {taus : List ℕ} {a b c : ℕ} (h1 : before taus a b = true) (h2 : before taus b c = true) :
    before taus a c = true := by
  simp only [before, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *
  omega

theorem before_irrefl (taus : List ℕ) (c : ℕ) : before taus c c = false := by
  simp [before]

theorem before_total {taus : List ℕ} {a b : ℕ} (h : a ≠ b) : before taus a b = true ∨ before taus b a = true := by
  simp only [before, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  omega

/-- Each column's offset is a multiple of its length. -/
theorem offset_aligned (taus : List ℕ) (c : ℕ) : 2 ^ taus.getD c 0 ∣ offset taus c := by
  refine Finset.dvd_sum fun j hj => ?_
  simp only [Finset.mem_filter, before, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hj
  exact Nat.pow_dvd_pow 2 (by omega)

/-- A column stacked before another ends where the other starts or earlier. -/
theorem offset_before {taus : List ℕ} {j c : ℕ} (hj : j < taus.length) (h : before taus j c = true) :
    offset taus j + 2 ^ taus.getD j 0 ≤ offset taus c := by
  unfold offset
  have hsub : insert j ((Finset.range taus.length).filter (fun i => before taus i j = true)) ⊆
      (Finset.range taus.length).filter (fun i => before taus i c = true) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range] at hi ⊢
    rcases hi with rfl | ⟨hi, hb⟩
    · exact ⟨hj, h⟩
    · exact ⟨hi, before_trans hb h⟩
  have hnot : j ∉ (Finset.range taus.length).filter (fun i => before taus i j = true) := by
    simp [before_irrefl]
  calc ∑ i ∈ (Finset.range taus.length).filter (fun i => before taus i j = true), 2 ^ taus.getD i 0 + 2 ^ taus.getD j 0
      = ∑ i ∈ insert j ((Finset.range taus.length).filter (fun i => before taus i j = true)), 2 ^ taus.getD i 0 := by
        rw [Finset.sum_insert hnot, add_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- No two columns overlap. -/
theorem offset_disjoint {taus : List ℕ} {c c' : ℕ} (hc : c < taus.length) (hc' : c' < taus.length) (hne : c ≠ c') :
    offset taus c + 2 ^ taus.getD c 0 ≤ offset taus c' ∨ offset taus c' + 2 ^ taus.getD c' 0 ≤ offset taus c := by
  rcases before_total (taus := taus) hne with h | h
  · exact Or.inl (offset_before hc h)
  · exact Or.inr (offset_before hc' h)

/-- Every column ends within the columns' total length, within the stack. -/
theorem offset_fits {taus : List ℕ} {c : ℕ} (hc : c < taus.length) :
    offset taus c + 2 ^ taus.getD c 0 ≤ 2 ^ kappa taus := by
  have h1 : offset taus c + 2 ^ taus.getD c 0 ≤ placed taus := by
    unfold offset placed
    have hnot : c ∉ (Finset.range taus.length).filter (fun i => before taus i c = true) := by simp [before_irrefl]
    rw [add_comm, ← Finset.sum_insert (f := fun j => 2 ^ taus.getD j 0) hnot]
    refine Finset.sum_le_sum_of_subset fun i hi => ?_
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range] at hi ⊢
    rcases hi with rfl | ⟨hi, _⟩ <;> omega
  exact h1.trans ((le_max_left _ _).trans (Nat.le_pow_clog (by norm_num) _))

theorem tau_le_kappa {taus : List ℕ} {c : ℕ} (hc : c < taus.length) : taus.getD c 0 ≤ kappa taus := by
  have h := offset_fits hc
  by_contra hn
  have : 2 ^ kappa taus < 2 ^ taus.getD c 0 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- A column's block, over the stack's variables past its own, is its offset: `block · 2 ^ tau = offset`, and it has `kappa - tau` bits. -/
theorem block_spec {taus : List ℕ} {c : ℕ} (hc : c < taus.length) :
    block taus c * 2 ^ taus.getD c 0 = offset taus c ∧ block taus c < 2 ^ (kappa taus - taus.getD c 0) := by
  have ha := offset_aligned taus c
  have hb : block taus c * 2 ^ taus.getD c 0 = offset taus c := Nat.div_mul_cancel ha
  refine ⟨hb, ?_⟩
  have hf := offset_fits hc
  have hk : 2 ^ kappa taus = 2 ^ (kappa taus - taus.getD c 0) * 2 ^ taus.getD c 0 := by
    rw [← pow_add, Nat.sub_add_cancel (tau_le_kappa hc)]
  have hpos : 0 < 2 ^ taus.getD c 0 := by positivity
  by_contra hn
  push Not at hn
  have := Nat.mul_le_mul_right (2 ^ taus.getD c 0) hn
  rw [← hk, hb] at this
  omega

/-! Multilinear extensions, lowest coordinate first. -/

variable {R : Type} [CommRing R]

/-- The multilinear extension of the table `f` at a point, its first coordinate the index's lowest bit. -/
def mle (f : ℕ → R) : List R → R
  | [] => f 0
  | x :: xs => (1 - x) * mle (fun i => f (2 * i)) xs + x * mle (fun i => f (2 * i + 1)) xs

/-- The `n` lowest bits of `m`, lowest first. -/
def bitsOf : ℕ → ℕ → List R
  | _, 0 => []
  | m, n + 1 => (if m % 2 = 1 then 1 else 0) :: bitsOf (m / 2) n

theorem bitsOf_length (m n : ℕ) : (bitsOf m n : List R).length = n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => simp [bitsOf, ih]

theorem bitsOf_getD (m n j : ℕ) (hj : j < n) : (bitsOf m n : List R).getD j 0 = if m.testBit j then 1 else 0 := by
  induction n generalizing m j with
  | zero => omega
  | succ n ih =>
    rcases j with _ | j
    · simp [bitsOf, Nat.testBit_zero]
    · simp only [bitsOf, List.getD_cons_succ]
      rw [ih (m / 2) j (by omega), Nat.testBit_div_two]

/-- A list of `n` bits read as `m`'s are `bitsOf m n`. -/
theorem bitsOf_eq {l : List R} {m n : ℕ} (hl : l.length = n) (h : ∀ j < n, l.getD j 0 = if m.testBit j then 1 else 0) :
    l = bitsOf m n := by
  apply List.ext_getElem (by rw [hl, bitsOf_length])
  intro j h1 h2
  have e1 := h j (by omega)
  have e2 := bitsOf_getD (R := R) m n j (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at e1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at e2
  rw [e1, e2]

/-- At a point of bits, the extension is the table's entry. -/
theorem mle_bitsOf (f : ℕ → R) (m n : ℕ) : mle f (bitsOf m n) = f (m % 2 ^ n) := by
  induction n generalizing f m with
  | zero => simp [mle, bitsOf, Nat.mod_one]
  | succ n ih =>
    have hm : m % 2 ^ (n + 1) = m % 2 + 2 * (m / 2 % 2 ^ n) := by rw [Nat.pow_succ', Nat.mod_mul]
    simp only [bitsOf, mle, ih]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · simp [h, hm]
    · simp [h, hm, add_comm]

/-- Bits of `m` then of `q` are bits of `m + 2 ^ n q`. -/
theorem bitsOf_append (m q n k : ℕ) (hm : m < 2 ^ n) :
    (bitsOf m n : List R) ++ bitsOf q k = bitsOf (m + 2 ^ n * q) (n + k) := by
  induction n generalizing m with
  | zero => simp only [pow_zero] at hm; simp [bitsOf, (by omega : m = 0)]
  | succ n ih =>
    rw [Nat.add_right_comm, bitsOf, bitsOf, List.cons_append, ih (m / 2) (by rw [pow_succ] at hm; omega)]
    have h1 : (m + 2 ^ (n + 1) * q) % 2 = m % 2 := by rw [pow_succ, mul_comm (2 ^ n) 2, mul_assoc]; omega
    have h2 : (m + 2 ^ (n + 1) * q) / 2 = m / 2 + 2 ^ n * q := by rw [pow_succ, mul_comm (2 ^ n) 2, mul_assoc]; omega
    rw [h1, h2]

/-- The extension at a point followed by bits is the extension of the table's block those bits select. -/
theorem mle_append_bitsOf (p : List R) (f : ℕ → R) (m n : ℕ) :
    mle f (p ++ bitsOf m n) = mle (fun i => f (i + 2 ^ p.length * (m % 2 ^ n))) p := by
  induction p generalizing f with
  | nil => simp [mle_bitsOf, mle]
  | cons x p ih =>
    simp only [List.cons_append, mle, ih, List.length_cons]
    congr 2 <;> congr 1 <;> funext i <;> congr 1 <;> ring

/-- The extension reads only the table's first `2 ^ |p|` entries. -/
theorem mle_congr (p : List R) (f g : ℕ → R) (h : ∀ i < 2 ^ p.length, f i = g i) : mle f p = mle g p := by
  induction p generalizing f g with
  | nil => exact h 0 (by simp)
  | cons x p ih =>
    simp only [mle]
    rw [ih (fun i => f (2 * i)) (fun i => g (2 * i)) fun i hi => h _ (by simp [pow_succ]; omega),
      ih (fun i => f (2 * i + 1)) (fun i => g (2 * i + 1)) fun i hi => h _ (by simp [pow_succ]; omega)]

/-- A circuit's stack (`FixedLayout::stack`): at each column's offset its values, zero between them. -/
noncomputable def stackAt (taus : List ℕ) (col : ℕ → ℕ → R) (i : ℕ) : R :=
  match (List.range taus.length).find? (fun c => decide (offset taus c ≤ i ∧ i < offset taus c + 2 ^ taus.getD c 0)) with
  | some c => col c (i - offset taus c)
  | none => 0

/-- A tier's fixed polynomial (`FixedLayout::polynomial`): its circuits' stacks in order of their index, `cols q c` column `c` of the tier's circuit `q`. -/
noncomputable def tierPoly (taus : List ℕ) (cols : ℕ → ℕ → ℕ → R) (i : ℕ) : R :=
  stackAt taus (cols (i / 2 ^ kappa taus)) (i % 2 ^ kappa taus)

theorem stackAt_read (taus : List ℕ) (col : ℕ → ℕ → R) {c x : ℕ} (hc : c < taus.length) (hx : x < 2 ^ taus.getD c 0) :
    stackAt taus col (offset taus c + x) = col c x := by
  unfold stackAt
  split
  · next c' hf =>
    have hm := List.find?_some hf
    have hc' := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    simp only [decide_eq_true_eq] at hm
    by_cases e : c' = c
    · subst e; congr 1; omega
    · rcases offset_disjoint hc' hc e with h | h <;> omega
  · next hf =>
    have := List.find?_eq_none.mp hf c (List.mem_range.mpr hc)
    simp only [decide_eq_true_eq, not_and, not_lt] at this
    have := this (by omega)
    omega

/-- A fresh fixed claim reads the child's own column: for any values of the tier's circuits' columns, the extension of the tier's fixed polynomial at a point of column `c`'s variables, then `c`'s block over `kappa - tau` bits, then the bits of the child's index `q` within its tier, is the extension of circuit `q`'s column `c` at that point. -/
theorem term_reads (taus : List ℕ) (cols : ℕ → ℕ → ℕ → R) {c : ℕ} (hc : c < taus.length) (p : List R)
    (hp : p.length = taus.getD c 0) (q kb : ℕ) (hq : q < 2 ^ kb) :
    mle (tierPoly taus cols) (p ++ bitsOf (block taus c) (kappa taus - taus.getD c 0) ++ bitsOf q kb) =
      mle (cols q c) p := by
  obtain ⟨hb, hblt⟩ := block_spec hc
  have hk := tau_le_kappa hc
  rw [List.append_assoc, bitsOf_append _ _ _ _ hblt, mle_append_bitsOf]
  have hlt : block taus c + 2 ^ (kappa taus - taus.getD c 0) * q < 2 ^ (kappa taus - taus.getD c 0 + kb) := by
    rw [pow_add]
    have : block taus c + 2 ^ (kappa taus - taus.getD c 0) * q < 2 ^ (kappa taus - taus.getD c 0) * (q + 1) := by
      rw [mul_add, mul_one]; omega
    exact this.trans_le (Nat.mul_le_mul_left _ (by omega))
  rw [Nat.mod_eq_of_lt hlt]
  refine mle_congr p _ _ fun i hi => ?_
  rw [hp] at hi
  have hpow : 2 ^ taus.getD c 0 * 2 ^ (kappa taus - taus.getD c 0) = 2 ^ kappa taus := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  have hidx : i + 2 ^ p.length * (block taus c + 2 ^ (kappa taus - taus.getD c 0) * q) =
      (offset taus c + i) + 2 ^ kappa taus * q := by
    rw [hp, mul_add, ← mul_assoc, hpow, mul_comm (2 ^ taus.getD c 0) (block taus c), hb]; ring
  have hfit := offset_fits hc
  have hpos : 0 < 2 ^ kappa taus := by positivity
  simp only [tierPoly]
  rw [hidx, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt (by omega), zero_add, Nat.mod_eq_of_lt (by omega), stackAt_read taus _ hc hi]

/-- A child's fresh fixed claim reads its own circuit's column: where its kind rows hold (`Model.KindBound`, whose `top` bits are its index's within its tier), column `c`'s term on the tier's fixed polynomial, at a point of the column's variables, its block and the `top` bits, is the extension of column `c` of the child's circuit `q` at that point. -/
theorem fresh_fixed_reads (sh : Shape) (h : sh.Accepted) (ct : ℕ) (val : Model.Val) (x : ℕ × List ℕ × ℕ)
    (hk : Model.KindBound sh ct val x) (hlen : x.2.1.length = sh.kindBits ct) (taus : List ℕ)
    (cols : ℕ → ℕ → ℕ → E) {c : ℕ} (hc : c < taus.length) (p : List E) (hp : p.length = taus.getD c 0) :
    ∃ q < sh.size, (sh.placeAt q).tier = ct ∧ Model.ev val x.1 = emb (ofWord (sh.code q)) ∧
      mle (tierPoly taus cols) (p ++ bitsOf (block taus c) (kappa taus - taus.getD c 0) ++ x.2.1.map (Model.ev val)) =
        mle (cols (q - sh.start ct) c) p := by
  obtain ⟨q, hq, ht, hkind, hbits, -⟩ := hk
  refine ⟨q, hq, ht, hkind, ?_⟩
  have hidx := index_lt sh h q hq
  rw [ht] at hidx
  have htop : x.2.1.map (Model.ev val) = bitsOf (q - sh.start ct) (sh.kindBits ct) := by
    refine bitsOf_eq (by rw [List.length_map, hlen]) fun j hj => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    have := hbits j hj
    rw [List.getD_eq_getElem?_getD] at this
    rcases e : x.2.1[j]? with _ | w
    · rw [List.getElem?_eq_none_iff] at e; omega
    · rw [e] at this; simpa using this
  rw [htop]
  exact term_reads taus cols hc p hp _ _ hidx

end Fixed

/-! A verified proof's final state, and a statement's digest. -/

section Digest

open Model

/-- `NodeClaims::bind_state`: a verified proof's final digest `d` as the two scalars the reduction binds, its first three words, then its fourth. -/
def bindState (d : ℕ) : M (ℕ × ℕ) := do
  let ws ← dToK d
  let a ← kToE (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0)
  let b ← kToE1 (ws.getD 3 0)
  pure (a, b)

/-- What `bindState` binds: the scalars are the digest's first three words and its fourth. -/
theorem bindState_good (d : ℕ) : Good (Wires [d]) (bindState d) fun _ ab s' => ∀ st val, Sat st s' val →
    Model.ev val ab.1 = toE (val d 0) (val d 1) (val d 2) ∧ Model.ev val ab.2 = emb (val d 3) := by
  unfold bindState
  refine Good.seq (dToK_good d) fun s ws s1 _ _ he1 hk => ?_
  have hw : Wires [ws.getD 0 0, ws.getD 1 0, ws.getD 2 0] s1 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hk.1 0 (by norm_num)
    · exact hk.1 1 (by norm_num)
    · exact hk.1 2 (by norm_num)
  refine Good.seq ((kToE_good _ _ _).pre fun s' hs' => hs' ▸ hw) fun s' a s2 _ hs' he2 ha => ?_
  subst hs'
  have hw3 : Wires [ws.getD 3 0] s2 := Wires.mono (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact hk.1 3 (by norm_num)) he2
  refine Good.seq ((kToE1_good _).pre fun s' hs' => hs' ▸ hw3) fun s' b s3 _ hs' he3 hb => ?_
  subst hs'
  refine Good.pure' fun s4 _ hs4 => ?_
  subst hs4
  intro st val hsat
  have h1 := hk.2 st val ((hsat.mono he3).mono he2)
  have e0 : val (ws.getD 0 0) 0 = val d 0 := h1 0
  have e1 : val (ws.getD 1 0) 0 = val d 1 := h1 1
  have e2 : val (ws.getD 2 0) 0 = val d 2 := h1 2
  have e3 : val (ws.getD 3 0) 0 = val d 3 := h1 3
  exact ⟨by rw [ha.2 st val (hsat.mono he3), e0, e1, e2], by rw [hb.2 st val hsat, e3]⟩

/-- The two scalars determine the digest: two digests binding the same scalars are one. -/
theorem bindState_binds (x y : Fin 4 → K) (h1 : toE (x 0) (x 1) (x 2) = toE (y 0) (y 1) (y 2))
    (h2 : emb (x 3) = emb (y 3)) : x = y := by
  obtain ⟨e0, e1, e2⟩ := toE_injective _ _ _ _ _ _ h1
  rw [← toE_emb, ← toE_emb] at h2
  have e3 := (toE_injective _ _ _ _ _ _ h2).1
  funext i
  fin_cases i <;> assumption

/-- `digest_halves_rows`: a digest `d` as the statement's two halves, each two of its words and a zero top limb. -/
def digestHalves (d : ℕ) : M (ℕ × ℕ) := do
  let ws ← dToK d
  let z ← kConst 0
  let lo ← kToE (ws.getD 0 0) (ws.getD 1 0) z
  let hi ← kToE (ws.getD 2 0) (ws.getD 3 0) z
  pure (lo, hi)

/-- What `digestHalves` writes: each half is two of the digest's words over a zero top limb. -/
theorem digestHalves_good (d : ℕ) : Good (Wires [d]) (digestHalves d) fun _ h s' => ∀ st val, Sat st s' val →
    Model.ev val h.1 = toE (val d 0) (val d 1) 0 ∧ Model.ev val h.2 = toE (val d 2) (val d 3) 0 := by
  unfold digestHalves
  refine Good.seq (dToK_good d) fun s ws s1 _ _ he1 hk => ?_
  refine Good.seq ((kConst_good 0).pre fun _ _ => trivial) fun s' z s2 _ hs' he2 hz => ?_
  subst hs'
  have hw : ∀ i j, i < 4 → j < 4 → Wires [ws.getD i 0, ws.getD j 0, z] s2 := by
    intro i j hi hj x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lt_of_lt_of_le (hk.1 i hi) he2.next
    · exact lt_of_lt_of_le (hk.1 j hj) he2.next
    · exact hz.1
  refine Good.seq ((kToE_good _ _ _).pre fun s' hs' => hs' ▸ hw 0 1 (by norm_num) (by norm_num))
    fun s' lo s3 _ hs' he3 hlo => ?_
  subst hs'
  refine Good.seq ((kToE_good _ _ _).pre fun s' hs' => hs' ▸ (hw 2 3 (by norm_num) (by norm_num)).mono he3)
    fun s' hi s4 _ hs' he4 hhi => ?_
  subst hs'
  refine Good.pure' fun s5 _ hs5 => ?_
  subst hs5
  intro st val hsat
  have h1 := hk.2 st val (((hsat.mono he4).mono he3).mono he2)
  have hz0 : val z 0 = 0 := by
    rw [hz.2 st val ((hsat.mono he4).mono he3)]
    simp [limbsOf, ofWord_zero]
  have e0 : val (ws.getD 0 0) 0 = val d 0 := h1 0
  have e1 : val (ws.getD 1 0) 0 = val d 1 := h1 1
  have e2 : val (ws.getD 2 0) 0 = val d 2 := h1 2
  have e3 : val (ws.getD 3 0) 0 = val d 3 := h1 3
  exact ⟨by rw [hlo.2 st val (hsat.mono he4), e0, e1, hz0], by rw [hhi.2 st val hsat, e2, e3, hz0]⟩

/-- A parent reads the digest a child exposes: if the statement words a parent reads with `halves_to_d` (`TreeStatement::digest_wire`, which `checkedges` finds per child) carry the halves `digestHalves` writes of digest `x`, the digest wire is `x` and both halves' top limbs are zero, as `halves_to_d` requires. -/
theorem digest_roundtrip (lo hi r x : Fin 4 → K) (hlo : toE (lo 0) (lo 1) (lo 2) = toE (x 0) (x 1) 0)
    (hhi : toE (hi 0) (hi 1) (hi 2) = toE (x 2) (x 3) 0)
    (hr : r 0 = lo 0 ∧ r 1 = lo 1 ∧ r 2 = hi 0 ∧ r 3 = hi 1) : r = x ∧ lo 2 = 0 ∧ hi 2 = 0 := by
  obtain ⟨a0, a1, a2⟩ := toE_injective _ _ _ _ _ _ hlo
  obtain ⟨b0, b1, b2⟩ := toE_injective _ _ _ _ _ _ hhi
  refine ⟨?_, a2, b2⟩
  funext i
  fin_cases i
  · exact hr.1.trans a0
  · exact hr.2.1.trans a1
  · exact hr.2.2.1.trans b0
  · exact hr.2.2.2.trans b1

/-- `Kind::tag` of a node of a tree of outputs: `tree-nod`'s little-endian bytes. -/
def tagNode : ℕ := 0x646f6e2d65657274

/-- `Kind::digest_rows`: the header (the kind's tag, the item count, six zeros) as `k_const`s, then `chain` over it and the items' words. -/
def digestRows (tag : ℕ) (items : List (List ℕ)) : M ℕ := do
  let header ← [tag, items.length, 0, 0, 0, 0, 0, 0].mapM kConst
  Model.chain (header ++ items.flatten)

theorem mapM_kConst_good : ∀ cs : List ℕ, Good (fun _ => True) (cs.mapM kConst) fun _ ws s' =>
    ws.length = cs.length ∧ ∀ st val, Sat st s' val → ∀ i < cs.length, val (ws.getD i 0) = limbsOf [cs.getD i 0, 0, 0, 0]
  | [] => Good.pure' fun _ _ _ => ⟨rfl, fun _ _ _ i hi => absurd hi (by simp)⟩
  | c :: cs => by
    rw [List.mapM_cons]
    refine Good.seq ((kConst_good c).pre fun _ _ => trivial) fun s w s1 _ _ he1 hw => ?_
    refine Good.seq ((mapM_kConst_good cs).pre fun _ _ => trivial) fun s' ws s2 _ hs' he2 hws => ?_
    subst hs'
    refine Good.pure' fun s3 _ hs3 => ?_
    subst hs3
    refine ⟨by simp [hws.1], fun st val hsat i hi => ?_⟩
    rcases i with _ | i
    · simpa using hw.2 st val (hsat.mono he2)
    · simpa using hws.2 st val hsat i (by simpa using hi)

theorem w64_const {val : Model.Val} {w c : ℕ} (h : val w = limbsOf [c, 0, 0, 0]) (hc : c < 2 ^ 64) :
    w64 val w = BitVec.ofNat 64 c := by
  simp only [w64, h, limbsOf]
  rw [show ([c, 0, 0, 0] : List ℕ).getD (0 : Fin 4) 0 = c from rfl, toWord_ofWord c hc]

theorem flatten_map_w64 (val : Model.Val) : ∀ items : List (List ℕ), (∀ it ∈ items, it.length = 4) →
    items.flatten.map (w64 val) = (items.map fun it (k : Fin 4) => w64 val (it.getD k 0)).flatMap fun d => List.ofFn d
  | [], _ => rfl
  | it :: items, h => by
    rw [List.flatten_cons, List.map_append, List.map_cons, List.flatMap_cons,
      flatten_map_w64 val items fun x hx => h x (List.mem_cons_of_mem _ hx)]
    congr 1
    have h4 := h it List.mem_cons_self
    apply List.ext_getElem (by simp [h4])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < it.length by simpa using h1), Option.getD_some]

/-- A node's digest in rows: in any satisfying assignment, `digestRows` of a tag and items of four words each is the tree statement digest (`treeDigest`) of the tag and the items' words. -/
theorem digestRows_good (tag : ℕ) (htag : tag < 2 ^ 64) (items : List (List ℕ)) (h4 : ∀ it ∈ items, it.length = 4)
    (hlen : 8 * (8 + 4 * items.length) < 2 ^ 64) :
    Good (fun _ => True) (digestRows tag items) fun _ r s' => ∀ st val, Sat st s' val →
      words4 (val r) = digest (treeDigest (BitVec.ofNat 64 tag) (items.map fun it (k : Fin 4) => w64 val (it.getD k 0))) := by
  unfold digestRows
  have hfl : items.flatten.length = 4 * items.length := by
    rw [List.length_flatten, List.sum_eq_card_nsmul _ 4 (fun n hn => by
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hn; exact h4 it hit)]
    simp [mul_comm]
  refine Good.seq (mapM_kConst_good _) fun s hs s1 _ _ he1 hh => ?_
  have hl : 8 * (hs ++ items.flatten).length < 2 ^ 64 := by
    rw [List.length_append, hh.1, hfl]; simpa using hlen
  refine ((chain_good _ hl).pre fun _ _ => trivial).weaken (fun _ h => h) fun s' r s2 _ hs' he2 hc => ?_
  subst hs'
  intro st val hsat
  rw [hc.2 st val hsat, List.map_append, flatten_map_w64 val items h4, treeDigest, List.length_map]
  congr 3
  have hv := hh.2 st val (hsat.mono he2)
  have hn : items.length < 2 ^ 64 := by omega
  apply List.ext_getElem (by simp [hh.1])
  intro i h1 h2
  have h8 : i < 8 := by simpa using h2
  have h1' : i < hs.length := by simpa using h1
  rw [List.getElem_map]
  have e := hv i (by simpa using h8)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1', Option.getD_some] at e
  interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at e <;>
    first
    | exact w64_const e htag
    | exact w64_const e hn
    | exact (w64_const e (by norm_num)).trans rfl

/-- The digest `Kind::Node::digest_rows` computes of `a` children's digests, child `i`'s words `4i + 1` to `4i + 4`, as its words: `treeDigest` of the node's tag and those digests. -/
def nodeDigestModel (a : ℕ) : List ℕ :=
  (List.ofFn (digest (treeDigest (BitVec.ofNat 64 tagNode)
    ((List.range a).map fun i (k : Fin 4) => BitVec.ofNat 64 (4 * i + k.val + 1))))).map BitVec.toNat

end Digest

/-! A child's scale. -/

section Scale

/-- `Edges.firstProd` of the low `b` bits of a word holding `m`: one when they are all zero, else zero. -/
theorem firstProd_bits (x : Fin 4 → K) (m : ℕ) : ∀ b, (∀ j < b, (toWord (x 0)).testBit j = m.testBit j) →
    Edges.firstProd x b = if m % 2 ^ b = 0 then 1 else 0
  | 0, _ => by simp [Edges.firstProd, Nat.mod_one]
  | b + 1, hx => by
    rw [Edges.firstProd, firstProd_bits x m b fun j hj => hx j (by omega)]
    have hb : Edges.bitK x b = if m.testBit b then 1 else 0 := by rw [Edges.bitK, hx b (by omega)]
    have hm : m % 2 ^ (b + 1) = m % 2 ^ b + 2 ^ b * (m / 2 ^ b % 2) := Nat.mod_pow_succ
    have ht : m.testBit b = decide (m / 2 ^ b % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
    rw [hb, ht]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ b) with h2 | h2
    · simp only [h2, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte, emb_zero, zero_add, mul_one, hm,
        mul_zero, add_zero]
    · have hne : m % 2 ^ (b + 1) ≠ 0 := by rw [hm, h2]; positivity
      simp only [h2, decide_true, ↓reduceIte, hne]
      have h1 : emb 1 + 1 = 0 := by rw [show emb 1 = 1 from map_one _, one_add_one_eq_two]; exact two_E
      rw [h1, mul_zero]

/-- The scale of a child of the small tier (`Design::kind_bits` with more than two kinds, `Mode.bits` of its kind bits): zero exactly at the first level, else one. -/
theorem nodeScale_small (sh : Shape) (h : sh.Accepted) (hs : sh.size < 2 ^ 62) (q : ℕ) (hq : q < sh.size)
    (ht : (sh.placeAt q).tier = 0) (x : Fin 4 → K) (hx : x 0 = ofWord (sh.code q)) :
    Edges.nodeScale (.bits (sh.kindBits 0)) x = if q = 0 then 0 else 1 := by
  have hc := code_lt sh h q hq hs
  have hmod := code_mod sh h q hq
  rw [ht] at hmod
  have hs0 : sh.start 0 = 0 := rfl
  rw [hs0, Nat.sub_zero] at hmod
  rw [Edges.nodeScale, firstProd_bits x (sh.code q) _ fun j _ => by rw [hx, toWord_ofWord _ hc], hmod]
  by_cases hq0 : q = 0
  · simp only [hq0, ↓reduceIte]
    rw [one_add_one_eq_two]; exact two_E
  · simp [hq0]

/-- The scale of a child of a tree of two kinds (`Design::kind_bits` holding the kind to a bit, `Mode.kind`): zero exactly at the first level, else one. -/
theorem nodeScale_two (sh : Shape) (h : sh.Accepted) (h2 : sh.size = 2) (q : ℕ) (hq : q < sh.size)
    (x : Fin 4 → K) (hx : x 0 = ofWord (sh.code q)) (hx1 : x 1 = 0) (hx2 : x 2 = 0) :
    Edges.nodeScale .kind x = if q = 0 then 0 else 1 := by
  have hn1 : sh.nTiers = 1 := by
    rcases hc : sh.claims with _ | ⟨large, _ | s⟩
    · simp [Shape.nTiers, hc]
    · simp [Shape.nTiers, hc]
    · have := (h.small large s hc).1
      simp [Shape.size, hc] at h2
      omega
  have hcq : sh.code q = q := by
    have ht := tier_lt sh h q hq
    have ht0 : (sh.placeAt q).tier = 0 := by omega
    rw [code_eq sh h q hq, ht0]
    simp [Shape.start]
  rw [Edges.nodeScale, hx, hx1, hx2, hcq, ← ofWord_zero]
  have e := Model.ev_code q
  rw [e]
  rcases Nat.lt_or_ge q 1 with hq1 | hq1
  · have : q = 0 := by omega
    subst this; simp [ofWord_zero, emb_zero]
  · have : q = 1 := by omega
    subst this; simp [ofWord_one]
    exact map_one _

/-- The scale mode `Design::kind_bits` gives a child of tier `ct`: the kind word itself with two kinds, one for the large tier, else the small tier's kind bits. -/
def tierMode (sh : Shape) (ct : ℕ) : Edges.Mode :=
  if sh.size = 2 then .kind else if ct = 0 then .bits (sh.kindBits 0) else .one

/-- At its tier's mode, a child's scale is zero exactly at the first level and one at every node. -/
theorem tierMode_scale (sh : Shape) (h : sh.Accepted) (hs : sh.size < 2 ^ 62) (q : ℕ) (hq : q < sh.size)
    (x : Fin 4 → K) (hx : x 0 = ofWord (sh.code q)) (hx1 : x 1 = 0) (hx2 : x 2 = 0) :
    Edges.nodeScale (tierMode sh (sh.placeAt q).tier) x = if q = 0 then 0 else 1 := by
  unfold tierMode
  by_cases h2 : sh.size = 2
  · rw [if_pos h2]; exact nodeScale_two sh h h2 q hq x hx hx1 hx2
  rw [if_neg h2]
  by_cases h0 : (sh.placeAt q).tier = 0
  · rw [if_pos h0]; exact nodeScale_small sh h hs q hq h0 x hx
  rw [if_neg h0]
  · have hst := ((tier_iff sh h q hq _).mp rfl).2.1
    have hq0 : q ≠ 0 := by
      intro e
      subst e
      have : (sh.placeAt 0).tier = 0 := by simp [Shape.placeAt]
      exact h0 this
    have hsm : 1 ≤ sh.start (sh.placeAt q).tier := by
      simp only [Shape.start, h0, ↓reduceIte, Shape.smallEnd]
      split <;> omega
    simp [Edges.nodeScale, hq0]

end Scale

/-! The design's checks, as `checkdesign` makes them on a summary. -/

/-- `Design::carried` on a statement whose word `i` is wire `i`, scaled by the wire after them, takes the layout's statement claims, in order. -/
def carriedOk (L : Edges.Layout) (c : Claims ℕ) : Bool := c == stmtClaims L id L.len

/-- Which of the reduction's outputs a polynomial's value is: the reduced ones numbered from `s`, in order. -/
def presentLabels : List Bool → ℕ → List (Option ℕ)
  | [], _ => []
  | true :: ps, s => some s :: presentLabels ps (s + 1)
  | false :: ps, s => none :: presentLabels ps s

/-- The reduction's outputs as the summary labels them: output `j` is `1000 + j`, in order the point's `rounds` coordinates, the reduced values, the row point, the column point and the matrices' values. -/
def labeled (L : Edges.Layout) (rounds : ℕ) (present : List Bool) : Reduced ℕ :=
  let nv := present.count true
  let rows := rounds + nv
  let cols := rows + L.nMatrix
  let mats := cols + L.nMatrix
  ⟨(List.range rounds).map (1000 + ·), (presentLabels present rounds).map (·.map (1000 + ·)),
    (List.range L.nMatrix).map (1000 + rows + ·), (List.range L.nMatrix).map (1000 + cols + ·),
    (List.range (2 * L.nFlocks)).map (1000 + mats + ·)⟩

/-- An `E` word as the summary writes its value: its three coefficients. -/
abbrev Word := ℕ × ℕ × ℕ

/-- `Reduced::statement` of a reduction of `rounds` rounds whose polynomials `present` were reduced, of kind 7 and digest words 1 to 4, exposes `stmtOf` of the labeled outputs. -/
def exposedOk (L : Edges.Layout) (rounds : ℕ) (present : List Bool) (ws : List Word) : Bool :=
  ws == (List.range L.len).map
    (stmtOf L ((labeled L rounds present).map fun n => (n, 0, 0)) (7, 0, 0) (1, 2, 0) (3, 4, 0) (0, 0, 0))

/-- `Design::fixed_claim` on a hint of every column, in order, at its prefix of the point `0, …, n - 1` (`n` the most variables of a column), hint `c`'s value `n + c` and the kind's `kb` bits `n + |taus| + j`: on the tier's fixed polynomial (`Fixed` for the small tier, `Wide` for the large) at that point, column `c`'s term at its prefix, its block over `kappa - tau` bits and the kind's bits, unscaled. -/
def fixedModel (tier kb : ℕ) (taus : List ℕ) : Dense ℕ :=
  ⟨if tier = 0 then 2 else 3, List.range (taus.foldr max 0), (List.range taus.length).map fun c =>
    ⟨taus.getD c 0, block taus c, kappa taus - taus.getD c 0,
      (List.range kb).map (taus.foldr max 0 + taus.length + ·), none, taus.foldr max 0 + c⟩⟩

/-- A tier's fixed claim, of `kb` kind bits, on hints of columns of variables `taus`, is `fixedModel`'s. -/
def fixedOk (tier kb : ℕ) (taus : List ℕ) (c : Claims ℕ) : Bool := c == ⟨[fixedModel tier kb taus], []⟩

/-- `Kind::Node::digest_rows` of `a` children's digests of words `4i + 1` to `4i + 4` is `nodeDigestModel a`. -/
def nodeDigestOk (a : ℕ) (ws : List ℕ) : Bool := ws == nodeDigestModel a

/-- `NodeClaims::bind_state` of a final state of words 1 to 4 binds `1 + 2y + 3y^2` and `4`, as `bindState` does. -/
def bindOk (ws : List Word) : Bool := ws == [(1, 2, 3), (4, 0, 0)]

/-- The tracked dumps' shapes, by their name: output trees `2to1` and `4to1`; signer-set trees of those arities (`aggregate-signers-...`, single-tier claim-set trees of capacity 1601 and 6401 claims in 16 groups), whose node of arity `k` below the largest is `-node<k>`, at position `k - 1`; and the two claim-set examples. -/
def dumpShape (name : String) : Option (Shape × ℕ) :=
  let pos (s : String) : Option ℕ := (s.splitOn "-circuit-").getLast?.bind String.toNat?
  let a := if (name.splitOn "-2to1-").length = 2 then 2 else 4
  if name.startsWith "aggregate-signers-" then
    let sh : Shape := ⟨a, a, some ⟨⟨if a = 2 then 1601 else 6401, 16⟩, none⟩⟩
    if name.endsWith "-first" then some (sh, 0)
    else if name.endsWith "-node" then some (sh, a - 1)
    else ((name.splitOn "-node").getLast?.bind String.toNat?).bind fun k =>
      if 2 ≤ k ∧ k < a then some (sh, k - 1) else none
  else if name.startsWith "aggregate-" then
    some (⟨a, a, none⟩, if name.endsWith "-first" then 0 else 1)
  else if name.startsWith "claimset-single-tier-circuit-" then
    (pos name).map fun p => (⟨1, 3, some ⟨⟨12, 4⟩, none⟩⟩, p)
  else if name.startsWith "claimset-two-tier-circuit-" then
    (pos name).map fun p => (⟨1, 3, some ⟨⟨12, 4⟩, some ⟨2, ⟨5, 2⟩⟩⟩⟩, p)
  else none

/-- A tracked dump's child's scale mode is its tier's (`tierMode`). -/
def modeOk (sh : Shape) (ct : ℕ) (m : Edges.Mode) : Bool := m == tierMode sh ct

/-! Mutations each check rejects, on small layouts. -/

/-- `modeOk` accepts each tracked tree's child modes and rejects the others: a tree of two kinds reads the kind word (a signer-set tree of arity 2 too), a single-tier claim-set node the small tier's two kind bits (a signer-set tree of arity 4's four kinds too), a two-tier wrap's child one. -/
theorem modeOk_mutations :
    modeOk ⟨2, 2, none⟩ 0 .kind = true ∧ modeOk ⟨2, 2, none⟩ 0 .one = false ∧
      modeOk ⟨1, 3, some ⟨⟨12, 4⟩, none⟩⟩ 0 (.bits 2) = true ∧ modeOk ⟨1, 3, some ⟨⟨12, 4⟩, none⟩⟩ 0 .kind = false ∧
      modeOk ⟨1, 3, some ⟨⟨12, 4⟩, some ⟨2, ⟨5, 2⟩⟩⟩⟩ 1 .one = true ∧
      modeOk ⟨1, 3, some ⟨⟨12, 4⟩, some ⟨2, ⟨5, 2⟩⟩⟩⟩ 1 (.bits 1) = false ∧
      modeOk ⟨2, 2, some ⟨⟨1601, 16⟩, none⟩⟩ 0 .kind = true ∧ modeOk ⟨2, 2, some ⟨⟨1601, 16⟩, none⟩⟩ 0 (.bits 1) = false ∧
      modeOk ⟨4, 4, some ⟨⟨6401, 16⟩, none⟩⟩ 0 (.bits 2) = true ∧ modeOk ⟨4, 4, some ⟨⟨6401, 16⟩, none⟩⟩ 0 .kind = false := by
  decide

/-- `bindOk` rejects the fourth word first, and its first three words without the third. -/
theorem bindOk_mutations : bindOk [(1, 2, 3), (4, 0, 0)] = true ∧ bindOk [(4, 0, 0), (1, 2, 3)] = false ∧
    bindOk [(1, 2, 0), (4, 0, 0)] = false := by
  decide

/-- A layout of a two-coordinate dense point, three polynomials, one-coordinate matrix points and one flock circuit. -/
def L0 : Edges.Layout := ⟨2, 3, 1, 1, [1, 2, 2], [1]⟩

/-- The carried claims of `L0`'s labeled words, and mutations: a fixed claim unscaled, the two matrix claims swapped, the bytecode claim at one coordinate fewer, the image's value read from the next word. -/
theorem carriedOk_mutations :
    carriedOk L0 (stmtClaims L0 id L0.len) = true ∧
      carriedOk L0 { stmtClaims L0 id L0.len with
        dense := (stmtClaims L0 id L0.len).dense.map fun d => { d with terms := d.terms.map fun t => { t with scale := none } } } = false ∧
      carriedOk L0 { stmtClaims L0 id L0.len with matrices := (stmtClaims L0 id L0.len).matrices.reverse } = false ∧
      carriedOk L0 (stmtClaims ⟨2, 3, 1, 1, [0, 2, 2], [1]⟩ id L0.len) = false ∧
      carriedOk L0 (stmtClaims L0 (fun i => if i = L0.dv + 1 then i + 1 else i) L0.len) = false := by
  decide

/-- What `L0`'s statement exposes for a reduction of two rounds that reduced the bytecode and the image. -/
def exposed0 : List Word :=
  (List.range L0.len).map
    (stmtOf L0 ((labeled L0 2 [true, true, false, false]).map fun n => (n, 0, 0)) (7, 0, 0) (1, 2, 0) (3, 4, 0) (0, 0, 0))

/-- `exposedOk` accepts it and rejects mutations: the row and column points swapped, an unreduced value written as the next output, the digest's halves swapped. -/
theorem exposedOk_mutations :
    exposedOk L0 2 [true, true, false, false] exposed0 = true ∧
      exposedOk L0 2 [true, true, false, false]
        ((List.range L0.len).map fun i => exposed0.getD (if i = L0.rowsAt then L0.colsAt else
          if i = L0.colsAt then L0.rowsAt else i) (0, 0, 0)) = false ∧
      exposedOk L0 2 [true, true, false, false] (exposed0.set (L0.dv + 2) (1004, 0, 0)) = false ∧
      exposedOk L0 2 [true, true, false, false] ((exposed0.set 1 (3, 4, 0)).set 2 (1, 2, 0)) = false := by
  decide

/-- Columns of 1, 3, 0 and 3 variables: columns 1 and 3 first, at 0 and 8, then column 0 at 16 and column 2 at 18, in a stack of 32. -/
theorem fixed_placement : (List.range 4).map (offset [1, 3, 0, 3]) = [16, 0, 18, 8] ∧ kappa [1, 3, 0, 3] = 5 ∧
    (List.range 4).map (block [1, 3, 0, 3]) = [8, 0, 18, 1] := by
  decide

/-- `fixedOk` accepts the model's claim and rejects mutations: the small tier's claim on the wide polynomial, the columns placed in index order (column 0's block zero), the kind's bits reversed. -/
theorem fixedOk_mutations :
    fixedOk 0 2 [1, 3, 0, 3] ⟨[fixedModel 0 2 [1, 3, 0, 3]], []⟩ = true ∧
      fixedOk 0 2 [1, 3, 0, 3] ⟨[fixedModel 1 2 [1, 3, 0, 3]], []⟩ = false ∧
      fixedOk 0 2 [1, 3, 0, 3] ⟨[{ fixedModel 0 2 [1, 3, 0, 3] with
        terms := (fixedModel 0 2 [1, 3, 0, 3]).terms.set 0 ⟨1, 0, 4, [7, 8], none, 3⟩ }], []⟩ = false ∧
      fixedOk 0 2 [1, 3, 0, 3] ⟨[{ fixedModel 0 2 [1, 3, 0, 3] with
        terms := (fixedModel 0 2 [1, 3, 0, 3]).terms.map fun t => { t with top := t.top.reverse } }], []⟩ = false := by
  decide

end LeanVMCircuits.Rec.DesignClaims
