/-
  LeanVM.Prover.Complete.RingSwitch

  Ring switching on the honest stack: the merged claim's description adds its weight, the weight
  is multilinear, and the merged claim holds. Hence the opening phases win.
-/

module

public import LeanVM.Prover.Complete.OpeningWins
public import LeanVM.Protocol.Whir.Params.RingSound

/-!
# Ring switching, complete

`ringSwitchHonest : RingSwitchHonest`, from the merge read piece by piece
(`LeanVM.Protocol.Whir.Params.ringMerge_weight`, `flatWeight_eq`, `pair_merge`):

* `ringPhi_eq`: the prover's map, stage by stage, is `Φ` (`Ring.frobPhi`);
* `addClaim_ring`: the opening's scatter of the ring description is a scatter per flattened
  piece (`flatPieces`), each `Φ(scale · eq(point, ·))` on its block;
* `flatWeight_cube`: a placed piece's weight on the cube is the same `Φ(scale · eq(point, u))` on
  its block, zero elsewhere;
* `sliceValue_eq`: the slices that hold of the stack are `pair_merge`'s true slices.

`commitOpenWins : CommitOpenWins` follows (`commitOpenWins_of`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
  LeanVM.Protocol.Tables LeanVM.Protocol.Whir.Complete LeanVM.Protocol.Whir.Params Finset

/-! ## The prover's map -/

theorem repeat_square (n : ℕ) (w : E) : Nat.repeat (fun v ↦ v * v) n w = w ^ 2 ^ n := by
  induction n with
  | zero => simp [Nat.repeat]
  | succ n ih => rw [Nat.repeat, ih, pow_succ, pow_mul, sq]

private theorem foldl_phi : ∀ (l : List E) (a w : E),
    (l.foldl (fun (acc : E × E) fP ↦
      (acc.1 + fP * acc.2, Nat.repeat (fun v ↦ v * v) ringMapWidth acc.2)) (a, w)).1 =
      a + ∑ p ∈ range l.length, l.getD p 0 * w ^ 2 ^ (8 * p)
  | [], a, w => by simp
  | x :: l, a, w => by
    rw [List.foldl_cons, foldl_phi l, List.length_cons, sum_range_succ']
    have h : ∀ p ∈ range l.length, l.getD p 0 *
        (Nat.repeat (fun v ↦ v * v) ringMapWidth w) ^ 2 ^ (8 * p) =
        (x :: l).getD (p + 1) 0 * w ^ 2 ^ (8 * (p + 1)) := by
      intro p _
      rw [repeat_square, ← pow_mul, ← pow_add, List.getD_cons_succ,
        show ringMapWidth + 8 * p = 8 * (p + 1) by simp only [ringMapWidth]; ring]
    rw [sum_congr rfl h]
    simp only [List.getD_cons_zero, mul_zero, pow_zero, pow_one]
    ring

/-- **The prover's map is `Φ`.** -/
theorem ringPhi_eq (f g : Fin 8 → E) (v : E) :
    ringPhi (List.ofFn f) (List.ofFn g) v = Ring.frobPhi 8 f g v := by
  unfold ringPhi
  rw [foldl_phi, zero_add, List.length_ofFn]
  have hpsi : Verifier.ringPsi v (List.ofFn g) = Ring.frobPsi g v := Ring.ringPsi_ofFn v g
  rw [hpsi, Ring.frobPhi, ← Fin.sum_univ_eq_sum_range (fun p ↦ (List.ofFn f).getD p 0 *
    Ring.frobPsi g v ^ 2 ^ (8 * p))]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

/-! ## The opening's scatter of the ring description -/

/-- One flattened piece's scatter: `Φ(scale · eq(point, i))` at its block's cell `i`. -/
def pieceAdd (s : E) (f g : List E) (table : Array E) (piece : RingPiece) : Array E :=
  Nat.fold (eqTable piece.point).size (fun i _ t ↦
    t.modify ((piece.placement.map (·.index)).getD 0 + i)
      (· + s * ringPhi f g (piece.scale * (eqTable piece.point).getD i 0))) table

private theorem foldl_ring (s : E) (f g : List E) (rho : E) : ∀ (claims : List RingClaim)
    (acc : Array E) (rhoJ : E),
    (claims.foldl (fun (state : Array E × E) claim ↦
      (claim.pieces.foldl (fun table piece ↦
        Nat.fold (eqTable piece.point).size (fun i _ table ↦
          table.modify ((piece.placement.map (·.index)).getD 0 + i)
            (· + s * ringPhi f g ((state.2 * piece.scale) * (eqTable piece.point).getD i 0)))
          table) state.1, state.2 * rho)) (acc, rhoJ)).1 =
      (flatPieces rho claims rhoJ).foldl (pieceAdd s f g) acc
  | [], _, _ => rfl
  | c :: cs, acc, rhoJ => by
    rw [List.foldl_cons, foldl_ring s f g rho cs, flatPieces, List.foldl_append, List.foldl_map]
    rfl

/-- **The ring description's scatter** is one scatter per flattened piece. -/
theorem addClaim_ring (acc : Array E) (s : E) (claims : List RingClaim) (f g : List E)
    (rho : E) :
    addClaim acc s (.ring claims f g rho) = (flatPieces rho claims 1).foldl (pieceAdd s f g) acc :=
  foldl_ring s f g rho claims acc 1

/-! ## A placed piece's weight on the cube -/

theorem length_ringCoefficients' (f g : Fin 8 → E) :
    (ringCoefficients (List.ofFn f) (List.ofFn g)).length = 64 := by
  rw [verifier_ringCoefficients, Ring.length_ringCoefficients]

/-- **A placed piece's weight on the cube** is `Φ(scale · eq(point, u))` on its block, zero
elsewhere. -/
theorem flatWeight_cube {μ : ℕ} (f g : Fin 8 → E) (piece : RingPiece) {p : Placement}
    (hp : piece.placement = some p) (hlen : piece.point.length = p.variableCount)
    (hv : p.variableCount ≤ μ) (hdvd : 2 ^ p.variableCount ∣ p.index)
    (hin : p.index + 2 ^ p.variableCount ≤ 2 ^ μ) {y : ℕ} (hy : y < 2 ^ μ) :
    flatWeight (ringCoefficients (List.ofFn f) (List.ofFn g)) (boolPoint μ y) piece =
      if p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount then
        Ring.frobPhi 8 f g
          (piece.scale * eqEval (boolPoint p.variableCount (y - p.index)) piece.point)
      else 0 := by
  rw [flatWeight_eq _ piece hp hlen hv _ (length_boolPoint μ y)]
  have hk : ∀ k, eqEval (piece.point.map (fun a ↦ (frobenius a).getD k 0) ++
      selectorPoint (p.index >>> p.variableCount) (μ - p.variableCount)) (boolPoint μ y) =
      if p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount then
        eqEval (boolPoint p.variableCount (y - p.index))
          (piece.point.map fun a ↦ (frobenius a).getD k 0)
      else 0 := fun k ↦
    eqEval_stackPoint (p := p) (by rw [List.length_map, hlen]) hv hdvd hin hy
  simp only [hk]
  by_cases hB : p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount
  · simp only [hB, and_self, ↓reduceIte]
    have hz := zipIdx_sum (fun c k (_ : Unit) ↦ c * (frobenius piece.scale).getD k 0 *
      eqEval (boolPoint p.variableCount (y - p.index))
        (piece.point.map fun a ↦ (frobenius a).getD k 0)) ()
      (ringCoefficients (List.ofFn f) (List.ofFn g)) 0
    simp only [zero_add] at hz
    rw [hz, length_ringCoefficients', frobPhi_eq_coefs]
    refine sum_congr rfl fun k hk' ↦ ?_
    have hk64 := mem_range.mp hk'
    have hmap : (piece.point.map fun a ↦ (frobenius a).getD k 0) =
        piece.point.map fun a ↦ a ^ 2 ^ k :=
      List.map_congr_left fun a _ ↦ frobenius_getD a hk64
    rw [hmap, frobenius_getD _ hk64,
      eqEval_boolPoint_frob k p.variableCount (y - p.index) piece.point hlen, mul_pow]
    ring
  · simp [hB]

/-! ## The ring description adds the merged weight -/

private theorem foldl_pieceAdd {μ : ℕ} (f g : Fin 8 → E) (s : E) : ∀ (L : List RingPiece),
    (∀ piece ∈ L, PlacedOK μ piece) → ∀ acc : Array E, acc.size = 2 ^ μ →
    (L.foldl (pieceAdd s (List.ofFn f) (List.ofFn g)) acc).size = 2 ^ μ ∧
      ∀ y < 2 ^ μ, (L.foldl (pieceAdd s (List.ofFn f) (List.ofFn g)) acc).getD y 0 =
        acc.getD y 0 + s * (L.map (flatWeight (ringCoefficients (List.ofFn f) (List.ofFn g))
          (boolPoint μ y))).sum
  | [], _, acc, hacc => ⟨hacc, fun y _ ↦ by simp⟩
  | piece :: L, hok, acc, hacc => by
    obtain ⟨p, hp, hlen, hdvd, hin⟩ := hok piece List.mem_cons_self
    have hv : p.variableCount ≤ μ := by
      have : 2 ^ p.variableCount ≤ 2 ^ μ := le_trans (Nat.le_add_left _ _) hin
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    obtain ⟨h1, h2⟩ := getD_foldModify acc p.index (fun i ↦ s * ringPhi (List.ofFn f)
      (List.ofFn g) (piece.scale * (eqTable piece.point).getD i 0)) (eqTable piece.point).size
    have hstep : pieceAdd s (List.ofFn f) (List.ofFn g) acc piece =
        Nat.fold (eqTable piece.point).size (fun i _ t ↦ t.modify (p.index + i)
          (· + s * ringPhi (List.ofFn f) (List.ofFn g)
            (piece.scale * (eqTable piece.point).getD i 0))) acc := by
      simp only [pieceAdd, hp, Option.map_some, Option.getD_some]
    obtain ⟨h3, h4⟩ := foldl_pieceAdd f g s L (fun q hq ↦ hok q (List.mem_cons_of_mem _ hq))
      (pieceAdd s (List.ofFn f) (List.ofFn g) acc piece) (by rw [hstep, h1, hacc])
    refine ⟨h3, fun y hy ↦ ?_⟩
    rw [List.foldl_cons, h4 y hy, hstep, h2 y, size_eqTable, hlen, List.map_cons, List.sum_cons,
      flatWeight_cube f g piece hp hlen hv hdvd hin hy]
    by_cases hB : p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount
    · have hB' : p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount ∧ y < acc.size :=
        ⟨hB.1, hB.2, by omega⟩
      simp only [hB', and_self, ↓reduceIte]
      rw [getD_eqTable _ _ (by rw [hlen]; omega), hlen, ringPhi_eq]
      ring
    · have hB' : ¬ (p.index ≤ y ∧ y < p.index + 2 ^ p.variableCount ∧ y < acc.size) :=
        fun h ↦ hB ⟨h.1, h.2.1⟩
      simp only [hB', hB, ↓reduceIte]
      ring

/-- **The ring description matches the merged weight.** -/
theorem descMatches_ring {μ : ℕ} (f g : Fin 8 → E) (claims : List RingClaim) (rho : E)
    (hok : ∀ piece ∈ flatPieces rho claims 1, PlacedOK μ piece) :
    DescMatches μ (.ring claims (List.ofFn f) (List.ofFn g) rho)
      (ringMerge claims (List.ofFn f) (List.ofFn g) rho).1 := fun acc s hacc ↦ by
  rw [addClaim_ring]
  obtain ⟨h1, h2⟩ := foldl_pieceAdd f g s _ hok acc hacc
  exact ⟨h1, fun y hy ↦ by rw [h2 y hy, ringMerge_weight]⟩

/-! ## The merged weight is multilinear -/

theorem isMultilinearFn_flatWeight {μ : ℕ} (coefs : List E) (piece : RingPiece) {p : Placement}
    (hp : piece.placement = some p) (hlen : piece.point.length = p.variableCount)
    (hv : p.variableCount ≤ μ) :
    IsMultilinearFn μ (fun x ↦ flatWeight coefs x piece) := by
  have h := isMultilinearFn_list_sum coefs.zipIdx
    (fun ck ↦ ck.1 * (frobenius piece.scale).getD ck.2 0)
    (fun ck x ↦ eqEval (piece.point.map (fun a ↦ (frobenius a).getD ck.2 0) ++
      selectorPoint (p.index >>> p.variableCount) (μ - p.variableCount)) x) fun ck _ ↦ by
    have := isMultilinearFn_eqEval (piece.point.map (fun a ↦ (frobenius a).getD ck.2 0) ++
      selectorPoint (p.index >>> p.variableCount) (μ - p.variableCount))
    rwa [List.length_append, List.length_map, hlen, show (selectorPoint (p.index >>>
      p.variableCount) (μ - p.variableCount)).length = μ - p.variableCount by
        simp [selectorPoint], Nat.add_sub_cancel' hv] at this
  refine isMultilinearFn_congr h fun x hx ↦ ?_
  rw [flatWeight_eq coefs piece hp hlen hv x hx]

theorem mem_flatPieces {rho : E} {piece : RingPiece} : ∀ {claims : List RingClaim} {rhoJ : E},
    piece ∈ flatPieces rho claims rhoJ →
      ∃ c ∈ claims, ∃ p0 ∈ c.pieces, piece.placement = p0.placement ∧ piece.point = p0.point
  | [], _, h => by simp [flatPieces] at h
  | c :: cs, rhoJ, h => by
    rw [flatPieces, List.mem_append, List.mem_map] at h
    rcases h with ⟨p0, hp0, rfl⟩ | h
    · exact ⟨c, List.mem_cons_self, p0, hp0, rfl, rfl⟩
    · obtain ⟨c', hc', p0, hp0, h1, h2⟩ := mem_flatPieces h
      exact ⟨c', List.mem_cons_of_mem _ hc', p0, hp0, h1, h2⟩

/-- **The merged weight is multilinear**, for placed pieces. -/
theorem isMultilinearFn_ringMerge {μ : ℕ} (claims : List RingClaim) (f g : List E) (rho : E)
    (hok : ∀ piece ∈ flatPieces rho claims 1, PlacedOK μ piece) :
    IsMultilinearFn μ (ringMerge claims f g rho).1 := by
  refine isMultilinearFn_congr (isMultilinearFn_list_sum (flatPieces rho claims 1) (fun _ ↦ 1)
    (fun piece x ↦ flatWeight (ringCoefficients f g) x piece) fun piece hpiece ↦ ?_)
    fun x _ ↦ by rw [ringMerge_weight]; simp
  obtain ⟨p, hp, hlen, -, hin⟩ := hok piece hpiece
  have : 2 ^ p.variableCount ≤ 2 ^ μ := le_trans (Nat.le_add_left _ _) hin
  exact isMultilinearFn_flatWeight _ piece hp hlen
    ((Nat.pow_le_pow_iff_right (by norm_num)).mp this)

/-! ## The merged claim holds -/

/-- The slices that hold of the stack are the true slices `pair_merge` reads. -/
theorem sliceValue_eq {μ : ℕ} (q : Column μ) (piece : RingPiece) (hok : PlacedOK μ piece)
    (i : ℕ) :
    piece.sliceValue q.values.toArray i = piece.scale * Relation.rowMle piece.point
      (fun j ↦ Relation.bitOf (Relation.pieceRow q piece.placement j) i) := by
  obtain ⟨p, hp, hlen, -, hin⟩ := hok
  simp only [RingPiece.sliceValue, RingPiece.column, hp, Relation.pieceRow, Relation.rowMle,
    mleA_eq]
  congr 2
  have hsz : q.values.toArray.size = 2 ^ μ := by simp
  have hmin : min (p.index + 2 ^ p.variableCount) (2 ^ μ) = p.index + 2 ^ p.variableCount :=
    Nat.min_eq_left hin
  apply List.ext_getElem
  · simp only [bitSlice, stackBlock, Array.toList_map, List.length_map, Array.length_toList,
      Array.size_extract, hsz, List.length_range, hlen, hmin]
    simp
  · intro j h1 h2
    simp only [List.length_map, List.length_range, hlen] at h2
    simp only [bitSlice, stackBlock, Array.toList_map, List.getElem_map, Array.getElem_toList,
      Array.getElem_extract, List.getElem_range, Relation.cell, Relation.bitOf]
    congr 2
    rw [Vector.getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz]; omega)]
    rfl

/-- A ring claim that holds of the stack has `pair_merge`'s true slices. -/
theorem slices_eq_trueSlice {μ : ℕ} (q : Column μ) (c : RingClaim)
    (hok : ∀ piece ∈ c.pieces, PlacedOK μ piece) (hc : c.HoldsOn q.values.toArray) {i : ℕ}
    (hi : i < 64) : c.slices.getD i 0 = trueSlice q c i := by
  rw [hc.2 i hi, trueSlice]
  exact congrArg sumE (List.map_congr_left fun piece hp ↦ sliceValue_eq q piece (hok piece hp) i)

/-- **The merged claim holds** of a stack its two claims hold of. -/
theorem holds_ringMerge {μ : ℕ} (f g : Fin 8 → E) (rho : E) (q : Column μ) (a b : RingClaim)
    (hok : ∀ piece ∈ a.pieces ++ b.pieces, PlacedOK μ piece) (ha : a.HoldsOn q.values.toArray)
    (hb : b.HoldsOn q.values.toArray) :
    StackClaim.Holds μ (ringMerge [a, b] (List.ofFn f) (List.ofFn g) rho) q := by
  have hpm := pair_merge f g rho q a b hok
  unfold StackClaim.Holds
  refine hpm.trans ?_
  rw [ringMerge_eq]
  dsimp only
  rw [mergeSlices_eq a b ha.1 hb.1 rho, verifier_ringTarget, Ring.ringTarget_eq]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [slices_eq_trueSlice q a (fun p hp ↦ hok p (List.mem_append_left _ hp)) ha i.isLt,
    slices_eq_trueSlice q b (fun p hp ↦ hok p (List.mem_append_right _ hp)) hb i.isLt]

/-! ## Ring switching on the honest stack -/

private theorem ofFn_getD (l : List E) (h : l.length = 8) :
    l = List.ofFn fun i : Fin 8 ↦ l.getD i 0 := by
  apply List.ext_getElem (by simp [h])
  intro j h1 h2
  rw [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    Option.getD_some]

/-- **Ring switching on the honest stack.** -/
theorem ringSwitchHonest : RingSwitchHonest := by
  intro μ q a b f g rho hf hg hab
  rw [ofFn_getD f hf, ofFn_getD g hg]
  have hplaced : ∀ rc ∈ [a, b], ∀ piece ∈ rc.pieces, PlacedOK μ piece := by
    intro rc hrc piece hpiece
    obtain ⟨p, hp, hlen, -, hdvd, hin⟩ := (hab rc hrc).2 piece hpiece
    exact ⟨p, hp, hlen, hdvd, hin⟩
  have hflat : ∀ piece ∈ flatPieces rho [a, b] 1, PlacedOK μ piece := by
    intro piece hpiece
    obtain ⟨c, hc, p0, hp0, h1, h2⟩ := mem_flatPieces hpiece
    obtain ⟨p, hp, hlen, hdvd, hin⟩ := hplaced c hc p0 hp0
    exact ⟨p, h1.trans hp, h2 ▸ hlen, hdvd, hin⟩
  refine ⟨descMatches_ring _ _ [a, b] rho hflat, isMultilinearFn_ringMerge _ _ _ rho hflat,
    holds_ringMerge _ _ rho q a b (fun piece hp ↦ ?_) (hab a (by simp)).1 (hab b (by simp)).1⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact hplaced a (by simp) piece hp
  · exact hplaced b (by simp) piece hp

end LeanVM.Prover

namespace LeanVM.Prover

/-- **The opening phases win** (`CommitOpenWins`, `Assemble.lean`). -/
theorem commitOpenWins : CommitOpenWins := commitOpenWins_of ringSwitchHonest

end LeanVM.Prover

end
