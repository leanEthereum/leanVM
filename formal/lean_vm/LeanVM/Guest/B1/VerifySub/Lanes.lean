/-
  LeanVM.Guest.B1.VerifySub.Lanes

  The output lanes among `verify_tables`' pooled claims: where they are, their point, their values.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.Tables.Interface

/-!
# The output lanes among the pooled claims

The pool's `159` claims are `claimColumns`'s; slots `105 .. 129` are the `KECCAK` table's output
lanes, in lane order, and no other slot is one (`claimColumns_*`, by the kernel).

* `filter_lanes_eq`, `filter_notLanes_eq`: the lanes are slots `105 .. 129`, the rest slots
  `0 .. 104` and `130 .. 158`.
* `lanes_facts`: the lanes' columns are `keccakOutputColumns`, each at the table sumcheck's
  point cut to the `KECCAK` table's height, their values at `col_eval_words·g^101`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem claimColumns_length : Tables.claimColumns.length = 159 := by decide +kernel

theorem claimColumns_front : ∀ x ∈ Tables.claimColumns.take 105, x ∉ keccakOutputColumns := by
  decide +kernel

theorem claimColumns_lanes : (Tables.claimColumns.drop 105).take 25 = keccakOutputColumns := by
  decide +kernel

theorem claimColumns_back : ∀ x ∈ Tables.claimColumns.drop 130, x ∉ keccakOutputColumns := by
  decide +kernel

theorem claimKappaSrc_lanes : ∀ k < 25, Tables.claimKappaSrc.getD (105 + k) 0 = 7 := by
  decide +kernel

theorem claims_split {claims : List ColumnClaim} :
    claims = claims.take 105 ++ ((claims.drop 105).take 25 ++ claims.drop 130) := by
  rw [show claims.drop 130 = (claims.drop 105).drop 25 by simp [List.drop_drop],
    List.take_append_drop, List.take_append_drop]

theorem mem_column {claims l : List ColumnClaim} {f : List ColumnClaim → List ColumnClaim}
    {g : List ℕ → List ℕ} (hf : (f claims).map (·.column) = g (claims.map (·.column)))
    (hl : l = f claims) {c : ColumnClaim} (hc : c ∈ l) :
    c.column ∈ g (claims.map (·.column)) := by
  rw [← hf, ← hl]
  exact List.mem_map_of_mem hc

/-- **The output lanes are slots `105 .. 129`.** -/
theorem filter_lanes_eq {claims : List ColumnClaim}
    (hcol : claims.map (·.column) = Tables.claimColumns) :
    claims.filter (fun c ↦ c.column ∈ keccakOutputColumns) = (claims.drop 105).take 25 := by
  conv_lhs => rw [claims_split (claims := claims)]
  rw [List.filter_append, List.filter_append, List.filter_eq_nil_iff.2, List.filter_eq_self.2,
    List.filter_eq_nil_iff.2, List.nil_append, List.append_nil]
  · intro c hc
    have := mem_column (f := (·.drop 130)) (g := (·.drop 130)) (List.map_drop ..) rfl hc
    rw [hcol] at this
    simpa using claimColumns_back _ this
  · intro c hc
    have := mem_column (f := fun l ↦ (l.drop 105).take 25) (g := fun l ↦ (l.drop 105).take 25)
      (by rw [List.map_take, List.map_drop]) rfl hc
    rw [hcol, claimColumns_lanes] at this
    simpa using this
  · intro c hc
    have := mem_column (f := (·.take 105)) (g := (·.take 105)) (List.map_take ..) rfl hc
    rw [hcol] at this
    simpa using claimColumns_front _ this

/-- **The other claims are slots `0 .. 104` and `130 .. 158`.** -/
theorem filter_notLanes_eq {claims : List ColumnClaim}
    (hcol : claims.map (·.column) = Tables.claimColumns) :
    claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) = claims.take 105 ++ claims.drop 130 := by
  conv_lhs => rw [claims_split (claims := claims)]
  rw [List.filter_append, List.filter_append, List.filter_eq_self.2, List.filter_eq_nil_iff.2,
    List.filter_eq_self.2, List.nil_append]
  · intro c hc
    have := mem_column (f := (·.drop 130)) (g := (·.drop 130)) (List.map_drop ..) rfl hc
    rw [hcol] at this
    simpa using claimColumns_back _ this
  · intro c hc
    have := mem_column (f := fun l ↦ (l.drop 105).take 25) (g := fun l ↦ (l.drop 105).take 25)
      (by rw [List.map_take, List.map_drop]) rfl hc
    rw [hcol, claimColumns_lanes] at this
    simpa using this
  · intro c hc
    have := mem_column (f := (·.take 105)) (g := (·.take 105)) (List.map_take ..) rfl hc
    rw [hcol] at this
    simpa using claimColumns_front _ this

/-- **The output lanes**: their columns, their point (the table sumcheck's, cut to the `KECCAK`
table's height `taus[5]`), and their `25` values at `col_eval_words·g^101`. -/
theorem lanes_facts {claims : List ColumnClaim} (hcl : claims.length = 159)
    (hcol : claims.map (·.column) = Tables.claimColumns) {chis : List E} {logMem : ℕ}
    {taus : List ℕ}
    (hpts : ∀ j (p : List E), (claims.map (·.point))[j]? = some p →
      (j < Tables.nPooled → p.length = Tables.claimLowDim logMem taus j) ∧
      (Tables.nBusClaims ≤ j → j < Tables.nPooled → p = chis.take p.length))
    {cew : E} (hcew : ReadsAt rd cew (((claims.drop 4).take 153).map (·.value))) :
    (claims.filter fun c ↦ c.column ∈ keccakOutputColumns).map (·.column) = keccakOutputColumns ∧
    (∀ c ∈ claims.filter (fun c ↦ c.column ∈ keccakOutputColumns),
      c.point = chis.take (taus.getD 5 0)) ∧
    ((claims.filter fun c ↦ c.column ∈ keccakOutputColumns).headD default).point =
      chis.take (taus.getD 5 0) ∧
    ((claims.filter fun c ↦ c.column ∈ keccakOutputColumns).map (·.value)).length = 25 ∧
    ReadsAt rd (cew * gen ^ 101)
      ((claims.filter fun c ↦ c.column ∈ keccakOutputColumns).map (·.value)) := by
  rw [filter_lanes_eq hcol]
  have hpt : ∀ c ∈ (claims.drop 105).take 25, c.point = chis.take (taus.getD 5 0) := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    simp only [List.length_take, List.length_drop, hcl] at hk
    simp only [List.getElem_take, List.getElem_drop]
    have hj := hpts (105 + k) claims[105 + k].point (by
      simp only [List.getElem?_map, List.getElem?_eq_getElem (show 105 + k < claims.length by omega),
        Option.map_some])
    obtain ⟨h1, h2⟩ := hj
    have hlen := h1 (by simp only [Tables.nPooled, Tables.nClaims]; omega)
    have hdim : Tables.claimLowDim logMem taus (105 + k) = taus.getD 5 0 := by
      have hadj : Tables.claimKappaAdj (105 + k) = 0 := by
        simp only [Tables.claimKappaAdj]; split <;> omega
      simp only [Tables.claimLowDim, claimKappaSrc_lanes k (by omega), hadj, add_zero]
      rfl
    have hb4 : Tables.nBusClaims ≤ 105 + k := by simp only [Tables.nBusClaims]; omega
    have hp157 : 105 + k < Tables.nPooled := by simp only [Tables.nPooled, Tables.nClaims]; omega
    rw [h2 hb4 hp157, hlen, hdim]
  have hl : ((claims.drop 105).take 25).length = 25 := by simp [hcl]
  refine ⟨by rw [List.map_take, List.map_drop, hcol, claimColumns_lanes], hpt, ?_, by simp [hcl],
    ?_⟩
  · obtain ⟨c, cs, hcs⟩ :=
      List.exists_cons_of_length_pos (show 0 < ((claims.drop 105).take 25).length by omega)
    rw [hcs]
    exact hpt c (by rw [hcs]; exact List.mem_cons_self)
  · rw [readsAt_gen_pow_mul]
    intro k hk
    simp only [List.length_map, hl] at hk
    have := hcew (101 + k) (by simp [hcl]; omega)
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop] at this ⊢
    simpa [show 4 + (101 + k) = 105 + k by omega] using this

end
end LeanVM.Guest.B1.VerifySub
