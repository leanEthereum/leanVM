module

public import LeanVM.Guest.Complete.Agg.Layout
public import LeanVM.Guest.Complete.Agg.Rows
public import LeanVM.Guest.Complete.MainWords
public import LeanVM.Guest.B1.Bits.GrindFwd
public import LeanVM.Guest.B1.Main.AggRun
public import LeanVM.Guest.B1.Whir.SqLoop

/-!
# `aggregate_claims`' honest data

On a node `w` with `m` children, its claims `aCs w` (`DeferredClaimBatched`'s), the nonce's
permutation `aN w`, the column challenges `aCols w`, `λ = aLam w` and the sumcheck's challenges
`aPt w`, from the cursor `c`:

* **The oracle** `aOrc w c`: the eleven `HeapBuf` pointers at their bases `aB c m j`
  (`bases c (aBufs m)`), `bc_star_hint`, the grind's windows of the nonce permutation's cell `1`
  (`gcWin 3`), the sumcheck's returns (the sponge's capacity after it, the final claim).
* **The own words** `aWo s w c`: the buffers' honest contents `aLists s w` (`bc_msgs` the hints'
  cells, the claims' pointer tables, `absorb`'s rows `rowW (absSt m cs c)`, `col`, `eqtree`'s levels,
  the folded values, `bc_chain`'s records, the point, the point plus one, the weights) at the bases.
* **The evaluation memory** `aRd0 al s w cover c`: the reader holding the own words, `main`'s words
  and the window table (`aTab`), nothing else.

`rd_eq_rdW`: a memory holding runs agrees with the reader of the runs at every index a run holds,
below the generator's order. `aLists_length`, `aWo_in`: the own words fill the buffers, from `c`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Main LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

/-! ## The reader of runs -/

theorem valAt_inW : ∀ {W : Words} {i : ℕ}, InW W i →
    ∃ q ∈ W, q.1 ≤ i ∧ i < q.1 + q.2.length ∧ valAt W i = q.2.getD (i - q.1) 0
  | [], _, h => by obtain ⟨q, hq, -⟩ := h; simp at hq
  | q :: W, i, h => by
    by_cases hi : q.1 ≤ i ∧ i < q.1 + q.2.length
    · exact ⟨q, List.mem_cons_self, hi.1, hi.2, by simp [valAt, hi]⟩
    · obtain ⟨q', hq', h'⟩ := h
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact (hi h').elim
      · obtain ⟨r, hr, h1, h2, h3⟩ := valAt_inW (W := W) ⟨q', hq', h'⟩
        exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2, by simp [valAt, hi, h3]⟩

/-- **The reader of runs at an index a run holds**: that run's word. -/
theorem rdW_inW {W : Words} {i : ℕ} (hi : InW W i) (hb : i < 2 ^ 64 - 1) :
    rdW W (addressOfIndex i) = some (valAt W i) := by
  have hex : ∃ j, j < 2 ^ 64 - 1 ∧ addressOfIndex i = addressOfIndex j ∧ InW W j := ⟨i, hb, rfl, hi⟩
  unfold rdW
  split
  · rename_i hex'
    obtain ⟨hlt, he, -⟩ := Classical.choose_spec hex'
    rw [← gpow_injOn (Set.mem_Iio.mpr hb) (Set.mem_Iio.mpr hlt) he]
  · exact absurd hex ‹_›

/-- **A memory holding runs agrees with their reader** at every index a run holds. -/
theorem rd_eq_rdW {rd : Reader} {W : Words} (h : HoldsWords rd W) {i : ℕ} (hi : InW W i) (hb : i < 2 ^ 64 - 1) :
    rd (addressOfIndex i) = rdW W (addressOfIndex i) := by
  rw [rdW_inW hi hb]
  obtain ⟨q, hq, h1, h2, hv⟩ := valAt_inW hi
  have := (h q hq (i - q.1) (by omega)).2
  rw [Main.addr_ofK, show q.1 + (i - q.1) = i by omega] at this
  rw [this, hv, List.getD_eq_getElem _ _ (by omega)]

theorem holdsWords_append {rd : Reader} {W W' : Words} (h : HoldsWords rd W) (h' : HoldsWords rd W') :
    HoldsWords rd (W ++ W') := fun q hq => by
  rcases List.mem_append.mp hq with hq | hq
  · exact h q hq
  · exact h' q hq

theorem inW_append_right {W W' : Words} {i : ℕ} (h : InW W' i) : InW (W ++ W') i := by
  obtain ⟨q, hq, h⟩ := h
  exact ⟨q, List.mem_append_right _ hq, h⟩

/-! ## The honest data -/

/-- **The children's claims** the batching reads (`DeferredClaimBatched`'s). -/
noncomputable def aCs (w : NodeWitness) : List ChildClaims :=
  w.children.map fun child => ⟨statementDigest guestSeed child.statement, child.freshClaim,
    child.statement.deferredClaim⟩

theorem aCs_length (w : NodeWitness) : (aCs w).length = w.children.length := List.length_map _

/-- The base of `aggregate_claims`' `j`-th `HeapBuf` from the cursor `c`, on `m` children. -/
noncomputable def aB (c m j : ℕ) : ℕ := (bases c (aBufs m)).getD j 0

/-- The nonce's permutation. -/
noncomputable def aN (w : NodeWitness) : KeccakState := aggN (aCs w) w.batchingHints.lambdaGrindNonce

/-- The column challenges. -/
noncomputable def aCols (w : NodeWitness) : List E := (aggCols (aCs w) w.batchingHints.lambdaGrindNonce).1

/-- The batching's challenge `λ`. -/
noncomputable def aLam (w : NodeWitness) : E := challengeOf (aN w)

/-- The sumcheck's challenges, the point the claim is deferred at. -/
noncomputable def aPt (w : NodeWitness) : List E := (aggRun (aCs w) w.batchingHints).1.1

/-- **The honest oracle**: the `HeapBuf` pointers, `bc_star_hint`, the grind's windows, the
sumcheck's returns. -/
noncomputable def aOrc (w : NodeWitness) (c : ℕ) (i : ℕ) : E :=
  let m := w.children.length
  let win := gcWin 3 (cellsOfState (aN w) false 1)
  let cap := (aggRun (aCs w) w.batchingHints).2.cap
  match i with
  | 6 => ptrAt (aB c m 0)
  | 7 => w.batchingHints.finalBytecodeValue
  | 8 => ptrAt (aB c m 1)
  | 9 => ptrAt (aB c m 2)
  | 30 => ptrAt (aB c m 3)
  | 91 => win 0
  | 92 => win 1
  | 93 => win 2
  | 94 => win 3
  | 95 => win 4
  | 96 => win 5
  | 156 => ptrAt (aB c m 4)
  | 235 => ptrAt (aB c m 5)
  | 440 => ptrAt (aB c m 6)
  | 449 => ptrAt (aB c m 7)
  | 458 => ptrAt (aB c m 8)
  | 461 => cap.getD 0 0
  | 462 => cap.getD 1 0
  | 463 => cap.getD 2 0
  | 464 => cap.getD 3 0
  | 465 => cap.getD 4 0
  | 466 => (aggRun (aCs w) w.batchingHints).1.2
  | 467 => ptrAt (aB c m 9)
  | 568 => ptrAt (aB c m 10)
  | _ => 0

/-- `eq_col_tree`'s words: `eqtree`'s levels `0 ..< 6` of the column challenges. -/
noncomputable def aTree (cols : List E) : List E := (List.range 6).flatMap (eqLevels fun k => cols.getD k 0)

/-- `bc_chain`'s record `c`: `λ^(2c)` and the lambdas' combination of the first `c` children's
folded and carried values (`chain_rows`). -/
noncomputable def aChain (cs : List ChildClaims) (cols : List E) (lam : E) (c : ℕ) : List E :=
  [lam ^ (2 * c), sumE (List.zipWith (fun ch l =>
    l.1 * Batch.foldColumns cols ch.freshClaim.values + l.2 * ch.carriedClaim.bytecodeValue)
    (cs.take c) (Batch.lambdaPowers lam c))]

/-- The column factor at the point `r`: `eq(col, r[19..])`. -/
noncomputable def aEqc (cols r : List E) : E := eqEval cols (r.drop 19)

/-- `bc_wsum`'s word `c`: the lambdas' combination of the first `c` children's weights at `r`
(`weight_rows`). -/
noncomputable def aWsum (cs : List ChildClaims) (cols : List E) (lam : E) (r : List E) (c : ℕ) : E :=
  sumE (List.zipWith (fun ch l =>
    l.1 * (eqEval ch.freshClaim.point (r.take 19) * aEqc cols r) + l.2 * eqEval ch.carriedClaim.bytecodePoint r)
    (cs.take c) (Batch.lambdaPowers lam c))

/-- **The buffers' honest contents**, in allocation order. -/
noncomputable def aLists (s : NodeStatement) (w : NodeWitness) : List (List E) :=
  let m := w.children.length
  let M := mainCounts s w
  let cs := aCs w
  let h := w.batchingHints
  [Batch.lambdaGrindNonceCells h ++ h.sumcheckMessages.flatMap Batch.sumcheckRoundCells,
    (List.range m).map (fun j => ptrAt (mBase M 6 + 55 * j)),
    (List.range m).map (fun j => ptrAt (mBase M 7 + 26 * j)),
    (List.range (m + 1)).flatMap (fun j => rowW (absSt m cs j)),
    aCols w,
    aTree (aCols w),
    cs.map (fun ch => Batch.foldColumns (aCols w) ch.freshClaim.values),
    (List.range (m + 1)).flatMap (aChain cs (aCols w) (aLam w)),
    aPt w,
    (aPt w).map (1 + ·),
    (List.range (m + 1)).map (aWsum cs (aCols w) (aLam w) (aPt w))]

/-- **The own words**: the honest contents at the bases from `c`. -/
noncomputable def aWo (s : NodeStatement) (w : NodeWitness) (c : ℕ) : Words := (bases c (aBufs w.children.length)).zip (aLists s w)

/-- The window table (`ExpWinTab`) at the exponent tables' index. -/
noncomputable def aTab (al : String → Bool) (s : NodeStatement) (w : NodeWitness) : ℕ × List E :=
  (mGS al (mainCounts s w) + winTabAt, (List.range (2 ^ winTabBits)).map eOfNat)

/-- The runs the evaluation memory holds: the own words, `main`'s, the window table. -/
noncomputable def aAll (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (cover : List E) (c : ℕ) : Words :=
  aWo s w c ++ mainWords s w cover ++ [aTab al s w]

/-- **The evaluation memory.** -/
noncomputable def aRd0 (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (cover : List E) (c : ℕ) : Reader :=
  rdW (aAll al s w cover c)

/-! ## The lengths -/

theorem eqLevels_flat_length (c : ℕ → E) : ((List.range 6).flatMap (eqLevels c)).length = 126 := by
  simp [List.range_succ, length_eqLevels]

/-- **The honest contents fill the buffers**, given the batching's `25` rounds and challenges. -/
theorem aLists_length {s : NodeStatement} {w : NodeWitness} (h25 : w.batchingHints.sumcheckMessages.length = 25)
    (hp : (aPt w).length = 25) : (aLists s w).map List.length = aBufs w.children.length := by
  have hn : (Batch.lambdaGrindNonceCells w.batchingHints).length = 1 := by
    simp [Batch.lambdaGrindNonceCells, show Batch.batchLambdaGrindBits ≠ 0 by decide]
  have hm : (w.batchingHints.sumcheckMessages.flatMap Batch.sumcheckRoundCells).length = 50 := by
    rw [flatMap_length_const (n := 2) (fun _ _ => rfl), h25]
  have hc : (aCols w).length = 6 := Whir.squeezeN_length splitLog _
  have h3 : ((List.range (w.children.length + 1)).flatMap fun j =>
      rowW (absSt w.children.length (aCs w) j)).length = 13 * (w.children.length + 1) := by
    rw [flatMap_length_const (n := 13) (fun j _ => rowW_length (absSt_ok _ _ j)), List.length_range]
  have h7 : ((List.range (w.children.length + 1)).flatMap (aChain (aCs w) (aCols w) (aLam w))).length =
      2 * (w.children.length + 1) := by
    rw [flatMap_length_const (n := 2) (fun j _ => rfl), List.length_range]
  have h5 : (aTree (aCols w)).length = 126 := eqLevels_flat_length _
  simp only [aLists, aBufs, List.map_cons, List.map_nil, List.length_append, hn, hm, List.length_map,
    List.length_range, aCs_length, hp, hc, h3, h5, h7]

/-- **The own words lie from `c`**, pairwise disjoint. -/
theorem aWo_in {s : NodeStatement} {w : NodeWitness} (hl : (aLists s w).map List.length = aBufs w.children.length)
    (c lo hi : ℕ) : WordsInA (aWo s w c) lo hi c (c + (aBufs w.children.length).sum) := by
  rw [aWo, ← hl]
  refine ⟨fun q hq => Or.inr (bases_zip_in c _ q hq), bases_zip_pairwise c _⟩

end
end LeanVM.Guest.Complete.Agg
