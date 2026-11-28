/-
  LeanVM.Protocol.Relation.Link.GroupOneHot

  The drawn group's count when a pointer is not one-hot: the certificate's weight at a fixed index
  point is a nonzero polynomial of degree `m + 3` in the drawn challenges.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupMirror
public import LeanVM.Protocol.Relation.Link.GroupBase
public import LeanVM.Protocol.Relation.Link.GroupCh
public import LeanVM.Protocol.Relation.Link.Shape
public import LeanVM.Protocol.Relation.Link.Steps
public import LeanVM.Protocol.Relation.Link.Valid
public import LeanVM.Protocol.Relation.Placement
public import LeanVM.Protocol.Relation.Link.Facts

/-!
# A pointer that is not one-hot

Fix an index point `r*` where the failing chunk's mirror certificate is nonzero
(`exists_part_mirrorCert_ne`). At `r*`, `linkB … r* 0` (`linkB_zero_closed`) is
`Σ_t θ_t Σ_k ε_{qBase t + k} Σ_{u < rows_t} eq(τ, u)·Σ_i ν_i·c_{t,k,u,i}`, the `c` constants: a
polynomial of degree `m + 3` in the drawn challenges alone (`polyFn_linkB_zero`), nonzero at `θ`, `ε`,
`ν` the unit vectors of the failing table, column and chunk and `τ` the failing row's bits
(`linkB_zero_at_pick`). Wherever it is nonzero the draw is doomed (`groupDoom_of_B`), so at most
`(m + 3)·|E|^N` draws escape (`card_notDoom_of_not_oneHot`), within `linkGroupError`. H4's joint count
over the drawn challenges and the index point, `m + 3 + 2·w_max`, is not needed.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Protocol.Hotwire Finset

@[expose] public section

open Classical

theorem sum_length_eq_qBase (layout : Layout) :
    nPointersOf layout = qBase layout layout.tables.length := by
  have hlen : ∀ L : List (List ℕ), (L.map List.length).sum =
      ∑ t ∈ range L.length, (L.getD t []).length := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ']
      simp [add_comm]
  unfold nPointersOf qBase ptrsOf
  rw [hlen, List.length_map]

theorem le_two_pow_log2Ceil' (n : ℕ) : n ≤ 2 ^ log2Ceil n := by
  unfold log2Ceil bitLength
  split_ifs with h
  · simp; omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

theorem qBase_le_pow (layout : Layout) : qBase layout layout.tables.length ≤ 2 ^ linkQVars layout := by
  rw [← sum_length_eq_qBase]
  exact le_two_pow_log2Ceil' _

theorem heightOf_le (layout : Layout) (t : ℕ) : heightOf layout t ≤ linkRows layout :=
  getD_le_foldl_max _ _ _

theorem qBase_add_lt (layout : Layout) {t k : ℕ} (ht : t < layout.tables.length)
    (hk : k < (ptrsOf layout t).length) : qBase layout t + k < nPointersOf layout := by
  have h1 := qBase_mono layout (show t + 1 ≤ layout.tables.length by omega)
  rw [qBase_succ] at h1
  rw [sum_length_eq_qBase]
  omega

theorem ite_self_eq (a : ℕ) (x y : E) : (if a = a then x else y) = x := by simp

theorem ite_ne_eq {a b : ℕ} (h : a ≠ b) (x y : E) : (if a = b then x else y) = y := by simp [h]

theorem nTables_le_epsOff (layout : Layout) : nTables ≤ epsOff layout := by unfold epsOff; omega

section Count

variable {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
  {μ : ℕ} (q : Column μ)
include hch

/-- **The certificate's weight at a fixed index point** is a polynomial of degree `m + 3` in the
draw. -/
theorem polyFn_linkB_zero (hT : layout.tables.length = nTables)
    (hrows : ∀ t < layout.tables.length, layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t) (r : List E) :
    PolyFn (linkDrawn layout chunks + 1) (linkRows layout + 3)
      (fun v ↦ linkB layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail r 0) := by
  have hN := linkDrawn_eq layout chunks hch
  refine PolyFn.congr ?_ fun v ↦ (linkB_zero_closed layout chunks q _ _ r (qBase_le_pow layout)
    (heightOf_le layout) hrows (chV_tau_length hch v)).symm
  refine PolyFn.finsetSum _ fun t ht ↦ PolyFn.finsetSum _ fun k hk ↦ PolyFn.finsetSum _ fun u _ ↦ ?_
  have ht' : t < nTables := hT ▸ mem_range.mp ht
  have hth : PolyFn (linkDrawn layout chunks + 1) 1 fun v ↦ (chV layout chunks v).theta.getD t 0 :=
    (PolyFn.var _).congr fun v ↦ (chV_theta hch v ht').symm
  have heq : PolyFn (linkDrawn layout chunks + 1) (heightOf layout t) fun v ↦
      eqAt ((chV layout chunks v).tau.take (heightOf layout t)) u := by
    have hlen : ∀ v, ((chV layout chunks v).tau.take (heightOf layout t)).length = heightOf layout t := by
      intro v
      rw [List.length_take, chV_tau_length hch v]
      exact min_eq_left (heightOf_le layout t)
    refine polyFn_eqAt (heightOf layout t) (fun v ↦ (chV layout chunks v).tau.take (heightOf layout t))
      hlen (fun k hk ↦ ?_) u
    have hkm : k < linkRows layout := by have := heightOf_le layout t; omega
    refine (PolyFn.var ⟨tauOff layout + k, by simp only [nuOff] at hN; omega⟩).congr fun v ↦ ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_take]
    simp only [hk, ↓reduceIte]
    rw [← List.getD_eq_getElem?_getD, chV_tau hch v hkm]
  have heps : PolyFn (linkDrawn layout chunks + 1) 1 fun v ↦
      (chV layout chunks v).eps.getD (qBase layout t + k) 0 :=
    (PolyFn.var _).congr fun v ↦ (chV_eps hch v (qBase_add_lt layout (mem_range.mp ht) (mem_range.mp hk))).symm
  have hnu : PolyFn (linkDrawn layout chunks + 1) 1 fun v ↦ ((List.range chunks.d).map fun i ↦
      (chV layout chunks v).nu.getD i 0 * certAt layout chunks r (wordAt layout q t k u) i).sum := by
    refine PolyFn.congr (PolyFn.finsetSum (range chunks.d) fun i hi ↦ ?_) fun v ↦
      (list_sum_range_map _ _).symm
    refine ((PolyFn.var ⟨nuOff layout chunks + i, by have := mem_range.mp hi; omega⟩).mul_le
      (PolyFn.const (certAt layout chunks r (wordAt layout q t k u) i)) (by omega)).congr fun v ↦ ?_
    rw [chV_nu hch v (mem_range.mp hi)]
  exact (((hth.mul heq).mul heps).mul hnu).mono (by have := heightOf_le layout t; omega)

/-- The pick: `θ`, `ε`, `ν` the unit vectors at `t0`, `j0`, `i0`, and `τ` the bits of `u0`. -/
def pickV (layout : Layout) (chunks : Chunks) (t0 j0 u0 i0 : ℕ) : Fin (linkDrawn layout chunks + 1) → E :=
  fun j ↦ if j.val = t0 then 1
    else if j.val = epsOff layout + j0 then 1
    else if tauOff layout ≤ j.val ∧ j.val < tauOff layout + linkRows layout then
      (if u0.testBit (j.val - tauOff layout) then 1 else 0)
    else if j.val = nuOff layout chunks + i0 then 1 else 0

omit q in
theorem linkB_zero_at_pick (hT : layout.tables.length = nTables)
    (hrows : ∀ t < layout.tables.length, layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t)
    {t0 k0 u0 i0 : ℕ} (ht0 : t0 < nTables) (hk0 : k0 < (ptrsOf layout t0).length)
    (hu0 : u0 < layout.tableRows.getD t0 0) (hi0 : i0 < chunks.d) (q : Column μ) (r : List E) :
    linkB layout chunks q ((List.ofFn (pickV layout chunks t0 (qBase layout t0 + k0) u0 i0)).headD 0)
      (List.ofFn (pickV layout chunks t0 (qBase layout t0 + k0) u0 i0)).tail r 0 =
      certAt layout chunks r (wordAt layout q t0 k0 u0) i0 := by
  set v := pickV layout chunks t0 (qBase layout t0 + k0) u0 i0
  have hN := linkDrawn_eq layout chunks hch
  have hE := nTables_le_epsOff layout
  have hj0 := qBase_add_lt layout (hT ▸ ht0) hk0
  have hP : epsOff layout + nPointersOf layout = tauOff layout := rfl
  have hR : tauOff layout + linkRows layout + chunks.width = nuOff layout chunks := rfl
  have pθ : ∀ t < nTables, (chV layout chunks v).theta.getD t 0 = if t = t0 then 1 else 0 := by
    intro t ht
    rw [chV_theta hch v ht]
    simp only [v, pickV]
    split_ifs <;> first | rfl | omega
  have pε : ∀ j < nPointersOf layout, (chV layout chunks v).eps.getD j 0 =
      if j = qBase layout t0 + k0 then 1 else 0 := by
    intro j hj
    rw [chV_eps hch v hj]
    simp only [v, pickV]
    split_ifs <;> first | rfl | omega
  have pτ : ∀ h ≤ linkRows layout, (chV layout chunks v).tau.take h = boolL h u0 := by
    intro h hh
    refine List.ext_getElem (by rw [List.length_take, chV_tau_length hch v, length_boolL]; omega)
      fun k h1 h2 ↦ ?_
    rw [length_boolL] at h2
    rw [List.getElem_take, ← List.getD_eq_getElem _ 0, chV_tau hch v (by omega)]
    simp only [boolL, List.getElem_ofFn, boolPt, v, pickV]
    split_ifs <;> first | omega | simp_all
  have pν : ∀ i < chunks.d, (chV layout chunks v).nu.getD i 0 = if i = i0 then 1 else 0 := by
    intro i hi
    rw [chV_nu hch v hi]
    simp only [v, pickV]
    split_ifs <;> first | rfl | omega
  rw [linkB_zero_closed layout chunks q _ _ r (qBase_le_pow layout) (heightOf_le layout) hrows
    (chV_tau_length hch v)]
  rw [sum_eq_single t0]
  · rw [pθ t0 ht0, ite_self_eq, sum_eq_single k0]
    · rw [pε _ hj0, ite_self_eq, sum_eq_single u0]
      · have hu0' : u0 < 2 ^ heightOf layout t0 := hu0.trans_le (hrows t0 (hT ▸ ht0))
        rw [pτ _ (heightOf_le layout t0), eqAt_boolL hu0' hu0', ite_self_eq, list_sum_range_map,
          sum_eq_single i0]
        · rw [pν i0 hi0, ite_self_eq]; ring
        · intro i hi hne; rw [pν i (mem_range.mp hi), ite_ne_eq hne, zero_mul]
        · intro h; exact absurd (mem_range.mpr hi0) h
      · intro u hu hne
        have hu' : u < 2 ^ heightOf layout t0 := (mem_range.mp hu).trans_le (hrows t0 (hT ▸ ht0))
        have hu0' : u0 < 2 ^ heightOf layout t0 := hu0.trans_le (hrows t0 (hT ▸ ht0))
        rw [pτ _ (heightOf_le layout t0), eqAt_boolL hu' hu0', ite_ne_eq hne]; ring
      · intro h; exact absurd (mem_range.mpr hu0) h
    · intro k hk hne
      refine sum_eq_zero fun u _ ↦ ?_
      rw [pε _ (qBase_add_lt layout (hT ▸ ht0) (mem_range.mp hk)), ite_ne_eq (by omega)]; ring
    · intro h; exact absurd (mem_range.mpr hk0) h
  · intro t ht hne
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun u _ ↦ ?_
    rw [pθ t (hT ▸ mem_range.mp ht), ite_ne_eq hne]; ring
  · intro h; exact absurd (mem_range.mpr (hT ▸ ht0)) h

end Count

/-- **A pointer not one-hot**: at most `(m + 3)·|E|^N` draws escape the group's doom, within
`linkGroupError`. -/
theorem card_notDoom_of_not_oneHot {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {μ : ℕ} (q : Column μ) {chunks : Chunks}
    (hch : Chunks.new (linkWidth layout) = some chunks) (hbad : ¬ PointersOneHot layout q chunks) :
    (univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
      linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks := by
  have hch' : Chunks.new chunks.width = some chunks := by rw [Chunks.new_width hch]; exact hch
  have hT := (announced_facts hA).2.1
  have hTlen : layout.tables.length = nTables := by rw [hT, tables_length]
  have hrows : ∀ t < layout.tables.length, layout.tableRows.getD t 0 ≤ 2 ^ heightOf layout t :=
    fun t ht ↦ tableRows_le_height hA (hTlen ▸ ht)
  unfold PointersOneHot at hbad
  push Not at hbad
  obtain ⟨t0, ht0, u0, hu0, p0, hp0, i0, hi0, hbad⟩ := hbad
  have hptrs : ptrsOf layout t0 = (tableAt layout t0).links.pointers := by
    unfold ptrsOf tableAt
    rw [List.getD_eq_getElem _ _ (by simp [hTlen, ht0]), List.getElem_map,
      List.getD_eq_getElem _ _ (by simp [hTlen, ht0])]
  obtain ⟨k0, hk0, hk0e⟩ := List.mem_iff_getElem.mp hp0
  have hk0' : k0 < (ptrsOf layout t0).length := by rw [hptrs]; exact hk0
  have hword : wordAt layout q t0 k0 u0 = tableWord layout q t0 p0 u0 := by
    obtain ⟨lm, rows, hB⟩ := announced_build hA
    have htab : tableAt layout t0 = tables.getD t0 default := by rw [tableAt, hT]
    obtain ⟨hc, hk, -⟩ := pointers_placed t0 ht0 p0 (htab ▸ hp0)
    obtain ⟨pl, hpl⟩ := Option.isSome_iff_exists.mp (placement_isSome hB hc hk)
    have hget : (ptrsOf layout t0).getD k0 0 = p0 := by
      rw [List.getD_eq_getElem _ _ hk0', ← hk0e]
      simp only [hptrs]
    simp only [wordAt, placementAt, pieceRow, tableWord, columnRow, hget, hpl, Option.getD_some]
  obtain ⟨hg1, hg2⟩ := chunks_geometry hch' i0 hi0
  have hw24 : chunks.widths.getD i0 0 < 2 ^ 126 := by
    have := chunks_width_le hch'
    simp only [maxPointerWidth] at this
    omega
  obtain ⟨r, hr, hne⟩ := exists_part_mirrorCert_ne chunks (W := chunks.width) hg1 hw24 hbad
  have hcert : certAt layout chunks r (wordAt layout q t0 k0 u0) i0 ≠ 0 := by
    rw [certAt_eq_mirrorCert layout chunks r _ hi0 (part_length chunks r (by rw [hr]; exact hg1)) hg2,
      hword]
    exact hne
  refine card_not_doom_le (polyFn_linkB_zero hch' q hTlen hrows r)
    (x0 := pickV layout chunks t0 (qBase layout t0 + k0) u0 i0) ?_
    (fun v hv ↦ groupDoom_of_B 0 r hr hv) ?_
  · rw [linkB_zero_at_pick hch' hTlen hrows ht0 hk0' hu0 hi0 q r]
    exact hcert
  · unfold linkGroupError
    omega

end

end LeanVM.Protocol.Relation
