/-
  LeanVM.Prover.Complete.Link.Rows

  The link's row rounds are honest: each round's polynomial is the next claim's, the claim being
  every table's cube sum, a bound table's value times its corner factor.
-/

module

public import LeanVM.Prover.Complete.Prods

/-!
# The row rounds

The row rounds run one sum-check over every table's rows at once (`rowRound`, `rowFold`,
`Statement/Prover/LinkRow.lean`): a table still bound over its rows contributes its round
polynomial, a bound one its value times its corner factor `Π (1 + x)` over the rounds past its
height, times `1 + X`. The claim after some rounds (`rowClaim`) is the sum over the tables of the
corner factor times the cube sum of the folded tables. Where every table's tables have `2^(h - b)`
entries and its terms at most `count - 1` factors (`RowOK`), a round's polynomial evaluates to the
next claim and folding at `0` and `1` splits the claim, so `sumcheckBy (rowRound count) rowFold`
wins the verifier's plain `sumcheck` from `rowClaim st` (`wins_rowSumcheck`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Prover.Complete.Keccak

/-- A table's part of the rows' claim. -/
noncomputable def rowPart (rt : RowTable) : E :=
  rt.corner * cubeSum (2 ^ (rt.height - rt.bound)) rt.prods

/-- **The rows' claim**: every table's cube sum, times its corner factor. -/
noncomputable def rowClaim (st : RowState) : E := (st.toList.map rowPart).sum

/-- A table through the row rounds is well shaped: its tables of `2^(h - b)` entries, its terms of
at most `count - 1` factors, its corner factor `1` while it is still bound over its rows. -/
def RowTableOK (count : ℕ) (rt : RowTable) : Prop :=
  rt.bound ≤ rt.height ∧ Tabs (rt.height - rt.bound) rt.prods ∧
    (∀ cf ∈ rt.prods.terms, cf.2.size + 1 ≤ count) ∧ (rt.bound < rt.height → rt.corner = 1)

/-- Every table is well shaped. -/
def RowOK (count : ℕ) (st : RowState) : Prop := ∀ rt ∈ st.toList, RowTableOK count rt

/-- A table, one row variable bound at `x`. -/
def rowTableFold (rt : RowTable) (x : E) : RowTable :=
  if rt.bound < rt.height then { rt with prods := rt.prods.fold x, bound := rt.bound + 1 }
  else { rt with corner := rt.corner * (1 + x) }

theorem rowFold_toList (st : RowState) (x : E) :
    (rowFold st x).toList = st.toList.map (rowTableFold · x) := by
  simp [rowFold, rowTableFold]

theorem RowTableOK.fold {count : ℕ} {rt : RowTable} (h : RowTableOK count rt) (x : E) :
    RowTableOK count (rowTableFold rt x) := by
  obtain ⟨hb, ht, hc, h1⟩ := h
  unfold rowTableFold
  split
  · rename_i hlt
    refine ⟨by simp only; omega, ?_, fun cf hcf ↦ hc cf (by simpa [fold_terms] using hcf),
      fun _ ↦ h1 hlt⟩
    simp only
    rw [show rt.height - rt.bound = (rt.height - (rt.bound + 1)) + 1 by omega] at ht
    exact ht.fold x
  · rename_i hge
    exact ⟨hb, ht, hc, fun h ↦ absurd h hge⟩

theorem RowOK.fold {count : ℕ} {st : RowState} (h : RowOK count st) (x : E) :
    RowOK count (rowFold st x) := by
  intro rt hrt
  rw [rowFold_toList] at hrt
  obtain ⟨rt0, h0, rfl⟩ := List.mem_map.mp hrt
  exact (h rt0 h0).fold x

/-! ## A table's polynomial -/

/-- A table's round polynomial (`rowRound`). -/
def rowTablePoly (count : ℕ) (rt : RowTable) : List E :=
  if rt.bound < rt.height then rt.prods.round count
  else
    let v := rt.prods.value * rt.corner
    v :: v :: List.replicate (count - 2) 0

theorem polyEval_replicate_zero' : ∀ (k : ℕ) (x : E), polyEval (List.replicate k 0) x = 0
  | 0, _ => rfl
  | k + 1, x => by
    show polyEval (List.replicate k 0) x * x + 0 = 0
    rw [polyEval_replicate_zero' k x]; ring

theorem rowTablePoly_spec {count : ℕ} (hcount : 2 ≤ count) {rt : RowTable}
    (h : RowTableOK count rt) (x : E) :
    (rowTablePoly count rt).length = count ∧
      polyEval (rowTablePoly count rt) x = rowPart (rowTableFold rt x) := by
  obtain ⟨hb, ht, hc, h1⟩ := h
  unfold rowTablePoly rowTableFold rowPart
  split
  · rename_i hlt
    obtain ⟨k, hk⟩ : ∃ k, rt.height - rt.bound = k + 1 := ⟨rt.height - rt.bound - 1, by omega⟩
    rw [hk] at ht
    have hs := round_spec ht.uniform (by rw [ht.2, pow_succ]; ring) count hc x
    refine ⟨hs.1, ?_⟩
    rw [hs.2]
    simp only
    rw [h1 hlt, one_mul, show rt.height - (rt.bound + 1) = k by omega]
  · rename_i hge
    have h0 : rt.height - rt.bound = 0 := by omega
    refine ⟨by simp; omega, ?_⟩
    simp only
    rw [h0, pow_zero, ← value_eq_cubeSum_one]
    show (polyEval (List.replicate (count - 2) 0) x * x + rt.prods.value * rt.corner) * x +
      rt.prods.value * rt.corner = _
    rw [polyEval_replicate_zero']
    ring

theorem rowRound_eq (count : ℕ) (st : RowState) :
    rowRound count st = st.toList.foldl (fun acc rt ↦
      List.zipWith (· + ·) acc (rowTablePoly count rt)) (List.replicate count 0) := by
  rw [rowRound, ← Array.foldl_toList]
  rfl

theorem polyEval_zipWith_add : ∀ (a b : List E), a.length = b.length → ∀ x,
    polyEval (List.zipWith (· + ·) a b) x = polyEval a x + polyEval b x
  | [], [], _, x => by simp [polyEval]
  | a :: as, b :: bs, h, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    show polyEval (List.zipWith (· + ·) as bs) x * x + (a + b) =
      (polyEval as x * x + a) + (polyEval bs x * x + b)
    rw [polyEval_zipWith_add as bs h x]
    ring

theorem foldl_rowPolys {count : ℕ} (hcount : 2 ≤ count) (x : E) :
    ∀ (L : List RowTable) (acc : List E), acc.length = count → (∀ rt ∈ L, RowTableOK count rt) →
      (L.foldl (fun acc rt ↦ List.zipWith (· + ·) acc (rowTablePoly count rt)) acc).length =
          count ∧
        polyEval (L.foldl (fun acc rt ↦ List.zipWith (· + ·) acc (rowTablePoly count rt)) acc) x =
          polyEval acc x + ((L.map (rowTableFold · x)).map rowPart).sum
  | [], acc, h, _ => ⟨h, by simp⟩
  | rt :: L, acc, h, hL => by
    obtain ⟨hl, he⟩ := rowTablePoly_spec hcount (hL rt (by simp)) x
    have hl' : (List.zipWith (· + ·) acc (rowTablePoly count rt)).length = count := by
      simp [h, hl]
    obtain ⟨h1, h2⟩ := foldl_rowPolys hcount x L _ hl' fun r hr ↦ hL r (by simp [hr])
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, polyEval_zipWith_add _ _ (by rw [h, hl]), he]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **A row round's polynomial is the next claim's.** -/
theorem rowRound_spec {count : ℕ} (hcount : 2 ≤ count) {st : RowState} (h : RowOK count st)
    (x : E) :
    (rowRound count st).length = count ∧ polyEval (rowRound count st) x = rowClaim (rowFold st x) := by
  rw [rowRound_eq]
  obtain ⟨h1, h2⟩ := foldl_rowPolys hcount x st.toList (List.replicate count 0) (by simp) h
  refine ⟨h1, ?_⟩
  rw [h2, polyEval_replicate_zero', zero_add, rowClaim, rowFold_toList, List.map_map]

/-- Folding a table at `0` and `1` splits its part. -/
theorem rowPart_fold_zero_add_one {count : ℕ} {rt : RowTable} (h : RowTableOK count rt) :
    rowPart (rowTableFold rt 0) + rowPart (rowTableFold rt 1) = rowPart rt := by
  obtain ⟨hb, ht, hc, h1⟩ := h
  unfold rowPart rowTableFold
  split
  · rename_i hlt
    obtain ⟨k, hk⟩ : ∃ k, rt.height - rt.bound = k + 1 := ⟨rt.height - rt.bound - 1, by omega⟩
    rw [hk] at ht
    simp only
    rw [show rt.height - (rt.bound + 1) = k by omega, hk, h1 hlt, one_mul, one_mul, one_mul,
      cubeSum_fold_zero_add_one ht.uniform, pow_succ, mul_comm (2 ^ k) 2]
  · simp only
    rw [show (1 : E) + 1 = 0 from CharTwo.add_self_eq_zero 1]
    ring

theorem rowClaim_fold_zero_add_one {count : ℕ} {st : RowState} (h : RowOK count st) :
    rowClaim (rowFold st 0) + rowClaim (rowFold st 1) = rowClaim st := by
  unfold rowClaim
  rw [rowFold_toList, rowFold_toList, List.map_map, List.map_map, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun rt hrt ↦ ?_
  exact rowPart_fold_zero_add_one (h rt hrt)

/-! ## The sum-check -/

/-- The claim after the challenges `pre`. -/
noncomputable def rowClaimAfter (st : RowState) (pre : List E) : E := rowClaim (pre.foldl rowFold st)

theorem RowOK.foldl {count : ℕ} {st : RowState} (h : RowOK count st) :
    ∀ pre : List E, RowOK count (pre.foldl rowFold st) := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil => exact h
  | append_singleton pre x ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ih.fold x

/-- **The honest row rounds win** the verifier's plain `sumcheck` from the rows' claim, to their
challenges and the bound tables' claim. -/
theorem wins_rowSumcheck {B : ℕ} (count n : ℕ) (hcount : 2 ≤ count) (hc' : count ≤ 2 ^ 128)
    (hB : roundBits count none ≤ B) (st : RowState) (hst : RowOK count st) (cs : List Committed) :
    Wins B (fun a s g cs' ↦ a.1 = s.1 ∧ s.1.length = n ∧ s.2 = s.1.foldl rowFold st ∧
        a.2 = rowClaim s.2 ∧ g = false ∧ cs' = cs)
      (sumcheck (rowClaim st) count (List.replicate n none))
      (sumcheckBy (rowRound count) rowFold (List.replicate n none) st) false cs := by
  have hround : ∀ pre : List E, pre.length < n →
      (rowRound count (pre.foldl rowFold st)).length = count ∧
        ∀ x, polyEval (rowRound count (pre.foldl rowFold st)) x =
          rowClaimAfter st (pre ++ [x]) := by
    intro pre _
    have hs := rowRound_spec hcount (hst.foldl pre)
    refine ⟨(hs 0).1, fun x ↦ ?_⟩
    rw [(hs x).2, rowClaimAfter, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hcorr := corr_sumcheckBy_lt count (by omega) hc' (rowClaimAfter st) (rowRound count)
    rowFold (fun pre s ↦ s = pre.foldl rowFold st) n
    (fun pre s h hl ↦ by subst h; exact hround pre hl)
    (fun pre s c h _ ↦ by subst h; rw [List.foldl_append, List.foldl_cons, List.foldl_nil])
    (List.replicate n none) [] st rfl (by simp)
  have hwin := wins_sumcheck (B := B) count hcount (rowClaimAfter st) (List.replicate n none) [] cs
    (fun m hm ↦ by rw [List.eq_of_mem_replicate hm]; exact hB)
    (fun ext hext ↦ by
      simp only [List.length_replicate] at hext
      obtain ⟨hl, hev⟩ := hround ext hext
      have := polyLE_polyEval (rowRound count (ext.foldl rowFold st))
      rw [hl] at this
      simp only [List.nil_append]
      exact PolyLE.congr this hev)
    (fun ext hext ↦ by
      simp only [List.getElem_replicate, RoundSplit, List.nil_append]
      unfold rowClaimAfter
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact rowClaim_fold_zero_add_one (hst.foldl ext))
  have := Wins.corr _ _ _ _ _ hcorr hwin
  have h0 : rowClaimAfter st [] = rowClaim st := rfl
  rw [h0] at this
  refine Wins.mono (fun a s g cs' h ↦ ?_) _ _ _ _ this
  obtain ⟨b, ⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9⟩ := h
  subst h5
  simp only [List.nil_append, List.length_replicate] at h1 h2 h3 h4 h6 h7
  refine ⟨h1.symm, h4, h2, ?_, h8, h9⟩
  rw [h7, rowClaimAfter, ← h1, ← h2]

end LeanVM.Prover.Complete

end
