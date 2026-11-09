/-
  LeanVM.Guest.B1.VerifySub.Lanes

  The output lanes' claims of `tablesSeg` share the table sumcheck's point, cut to the `KECCAK`
  table's height.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.VerifySub.Always

/-!
# The output lanes' point

`tablesSeg_lanes`: whatever `tablesSeg` reads and samples, every claim it returns on a `KECCAK`
output lane is at `pt.take τ`, `pt` the table sumcheck's point (`max` of the heights coordinates)
and `τ` the `KECCAK` table's height. The bus's and the public input's claims are on the memory
and final-counter columns, none an output lane; the table sumcheck puts table `t`'s claims at
`point.take height_t` (`tableTerms`), and only the `KECCAK` table owns output-lane columns
(`lanes_owner`, by kernel evaluation over `tables`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The columns -/

/-- Only the `KECCAK` table owns output-lane columns. -/
theorem lanes_owner : ∀ i (hi : i < tables.length), ∀ j < tables[i].width,
    globalColumnBases.getD tables[i].opcode 0 + j ∈ keccakOutputColumns → i = opKeccak := by
  decide +kernel

/-- The framework's columns are no output lane. -/
theorem framework_not_lanes : ∀ x ∈ [memory0, memory1, memory2, memoryFinalCounters,
    bytecodeFinalCounters], x ∉ keccakOutputColumns := by decide +kernel

theorem zipWith_column {β : Type} (pt : List E) :
    ∀ (cols : List ℕ) (vals : List β) (g : β → E) (c : ColumnClaim),
      c ∈ List.zipWith (fun column value ↦ (⟨column, pt, g value⟩ : ColumnClaim)) cols vals →
        c.column ∈ cols
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | col :: cols, v :: vals, g, c, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (zipWith_column pt cols vals g c h)

/-! ## The table sumcheck -/

/-- The rows' heights: a row whose table owns an output lane is at height `hK`. -/
def RowsOk (rows : List (Table × ℕ × List Form × E)) (hK : ℕ) : Prop :=
  ∀ r ∈ rows, ∀ j < r.1.width, globalColumnBases.getD r.1.opcode 0 + j ∈ keccakOutputColumns →
    r.2.1 = hK

theorem rowsOk_tables (heights : List ℕ) (rest : List (List Form × E)) :
    RowsOk (List.zip tables (List.zip heights rest)) (heights.getD opKeccak 0) := by
  intro r hr j hj hout
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  simp only [List.length_zip] at hi
  simp only [List.getElem_zip] at hj hout ⊢
  have hi1 : i < tables.length := by omega
  have hi2 : i < heights.length := by simp at hi; omega
  have := lanes_owner i hi1 j hj hout
  subst this
  rw [List.getD_eq_getElem _ _ hi2]

theorem always_tableTerms (cP fP point : List E) (hK : ℕ) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), RowsOk rows hK →
      (∀ c ∈ claims, c.column ∈ keccakOutputColumns → c.point = point.take hK) →
      Always (tableTermsClaims cP fP point rows cursor final claims)
        fun r ↦ ∀ c ∈ r.2, c.column ∈ keccakOutputColumns → c.point = point.take hK
  | [], _, _, _, _, hc => hc
  | (table, height, forms, weight) :: rest, cursor, final, claims, hrows, hc => by
    unfold tableTermsClaims
    simp only [VerifierProgram.bind_eq]
    refine Always.bind (fun evs hevs ↦ ?_) _ (always_readN table.width)
    refine always_tableTerms cP fP point hK rest _ _ _
      (fun r hr ↦ hrows r (List.mem_cons_of_mem _ hr)) fun c hcm hout ↦ ?_
    rw [List.mem_append] at hcm
    rcases hcm with hcm | hcm
    · exact hc c hcm hout
    · obtain ⟨⟨v, col⟩, hvc, rfl⟩ := List.mem_map.1 hcm
      have hcol := List.snd_lt_of_mem_zipIdx hvc
      simp only [Nat.add_zero, hevs] at hcol
      have := hrows _ (List.mem_cons_self ..) col hcol hout
      simp only at this
      rw [this]

theorem always_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (cP fP eqPt : List E) (target : E) :
    Always (tableSumcheckClaims heights busForms cP fP eqPt target) fun claims ↦
      ∃ pt : List E, pt.length = heights.foldl max 0 ∧
        ∀ c ∈ claims, c.column ∈ keccakOutputColumns → c.point = pt.take (heights.getD opKeccak 0) := by
  unfold tableSumcheckClaims
  simp only [VerifierProgram.bind_eq]
  refine Always.bind (fun r hr ↦ ?_) _ (always_sumcheck 4 _ target)
  obtain ⟨chs, cl⟩ := r
  simp only [List.length_replicate] at hr
  dsimp only
  refine Always.bind (fun r hr2 ↦ ?_) _ (always_tableTerms cP fP chs.reverse
    (heights.getD opKeccak 0) _ 0 0 [] (rowsOk_tables heights _) fun c hc ↦ absurd hc (by simp))
  obtain ⟨fin, claims⟩ := r
  refine Always.bind (fun _ _ ↦ ?_) _ (always_true _)
  exact ⟨chs.reverse, by rw [List.length_reverse, hr], hr2⟩

/-! ## The segment -/

theorem always_busRest (ev : (List K → List E → VerifierProgram E)) (L : Layout) (alphas : List E)
    (beta : E)
    (point tv : List E) :
    Always (Tables.busRest ev L alphas beta point tv) fun bus ↦
      ∀ c ∈ bus.claims, c.column ∉ keccakOutputColumns := by
  unfold Tables.busRest
  simp only [VerifierProgram.bind_eq]
  refine Always.bind (fun memory _ ↦ ?_) _ (always_true _)
  refine Always.bind (fun mf _ ↦ ?_) _ (always_true _)
  refine Always.bind (fun bf _ ↦ ?_) _ (always_true _)
  refine Always.bind (fun bv _ ↦ ?_) _ (always_true _)
  intro c hc
  rw [List.mem_append] at hc
  refine framework_not_lanes _ ?_
  rcases hc with hc | hc
  · have := zipWith_column _ _ _ id c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    tauto
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with rfl | rfl <;> simp

theorem always_tablePhase (L : Layout) (bus : BusResult)
    (hb : ∀ c ∈ bus.claims, c.column ∉ keccakOutputColumns) :
    Always (tablePhaseClaims L bus) fun claims ↦
      ∃ pt : List E, pt.length = L.tableLogHeights.foldl max 0 ∧
        ∀ c ∈ claims, c.column ∈ keccakOutputColumns →
          c.point = pt.take (L.tableLogHeights.getD opKeccak 0) := by
  unfold tablePhaseClaims
  simp only [VerifierProgram.bind_eq]
  refine Always.bind (fun xi _ ↦ ?_) _ (always_true _)
  refine Always.bind (fun cl hcl ↦ ?_) _ (always_tableSumcheck _ _ _ _ _ _)
  obtain ⟨pt, hpt, hc⟩ := hcl
  refine ⟨pt, hpt, fun c hcm hout ↦ ?_⟩
  rw [List.mem_append] at hcm
  rcases hcm with hcm | hcm
  · exact absurd hout (hb c hcm)
  · exact hc c hcm hout

theorem always_publicInputPhase (L : Layout) (pi : Digest) :
    Always (publicInputPhase L pi) fun claims ↦ ∀ c ∈ claims, c.column ∉ keccakOutputColumns := by
  unfold publicInputPhase
  simp only [VerifierProgram.bind_eq]
  refine Always.bind (fun ch _ ↦ ?_) _ (always_true _)
  intro c hc
  refine framework_not_lanes _ ?_
  have := zipWith_column _ _ _ id c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  tauto

/-- **The output lanes' point**: every claim `tablesSeg` returns on a `KECCAK` output lane is at
the table sumcheck's point cut to the `KECCAK` table's height. -/
theorem tablesSeg_lanes (ev : (List K → List E → VerifierProgram E)) (L : Layout) (pi : Digest) (alphas : List E)
    (beta : E) (point tv : List E) :
    Always (Tables.tablesSeg ev L pi alphas beta point tv) fun bc ↦
      ∃ pt : List E, pt.length = L.tableLogHeights.foldl max 0 ∧
        ∀ c ∈ bc.2, c.column ∈ keccakOutputColumns →
          c.point = pt.take (L.tableLogHeights.getD opKeccak 0) := by
  unfold Tables.tablesSeg
  simp only [VerifierProgram.bind_eq]
  refine Always.bind (fun bus hb ↦ ?_) _ (always_busRest ev L alphas beta point tv)
  refine Always.bind (fun cl hcl ↦ ?_) _ (always_tablePhase L bus hb)
  refine Always.bind (fun pc hpc ↦ ?_) _ (always_publicInputPhase L pi)
  obtain ⟨pt, hpt, hc⟩ := hcl
  refine ⟨pt, hpt, fun c hcm hout ↦ ?_⟩
  rw [List.mem_append] at hcm
  rcases hcm with hcm | hcm
  · exact hc c hcm hout
  · exact absurd hout (hpc c hcm)

end
end LeanVM.Guest.B1.VerifySub
