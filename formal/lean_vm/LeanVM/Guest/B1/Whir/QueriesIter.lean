/-
  LeanVM.Guest.B1.Whir.QueriesIter

  One query of `opening_queries` at its honest valuation: the loop body holds.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesComplete

/-!
# One query, honestly (TRIAGE #28, #35)

`oqIterVal`: the valuation of the loop body on one query, built region by region (the row's
hint and values, the leaf hash, the query sum, the path, the cap leaf) from the opening (its leaf
words and the path's siblings below the cap), its position, the frame run's pointer and the
memory. `oqIter_holds`: on a memory holding the weights, the query sum chain, the query's weight,
its bits, the frame run's cells, the parent's flag and the cap leaf, the body holds.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The valuation -/

/-- The row's words of a leaf. -/
def oqRowR (leaf : List K) (j : ℕ) : E := ofK (leaf.getD j 0)

/-- The row's values after its words, by level kind. -/
def oqRowsVals (base I : ℕ) (r w : ℕ → E) : List E :=
  if base = 1 then oqRows1Vals r w I else oqRows0Vals r w I

/-- The valuation after the row: the arguments, the row's words, the row's values. -/
def oqVal1 (rd : Reader) (args : List E) (base I : ℕ) (leaf : List K) : Val :=
  setl (setl (Val.ofArgs args) 8 ((List.range (oqR base I)).map (oqRowR leaf))) (8 + oqR base I)
    (oqRowsVals base I (oqRowR leaf) (memAt rd (args.getD 2 0)))

/-- The leaf hash's values from `K1`: the IV, then each block's metadata and next state. -/
def oqLeafVals (bl : ℕ → Fin 4 → E) (blocks : ℕ) : List E :=
  [(digestScalars paramIv).1, (digestScalars paramIv).2] ++
    ((List.range blocks).map fun j => [oqMd blocks j, (digestScalars (chainRun paramIv bl (oqMd blocks) (j + 1))).1,
      (digestScalars (chainRun paramIv bl (oqMd blocks) (j + 1))).2]).flatten

/-- The query sum's values from `K2`, the row's dot product `dot`. -/
def oqSumVals (rd : Reader) (x qsc qw qbp dot : E) : List E :=
  [qsc * x, memAt rd (qsc * x) 0, qw * x, memAt rd (qw * x) 0, memAt rd (qw * x) 0 * dot,
    memAt rd (qsc * x) 0 + memAt rd (qw * x) 0 * dot, qsc * x, qbp * x, memAt rd (qbp * x) 0]

/-- The path's values from `P`: the hinted children, the frame run's pointer, the run's other
cells as the memory holds them, the levels. -/
def oqPathVals (rd : Reader) (ptr : E) (D : Digest) (q pd : ℕ) (sibs : List Digest) : List E :=
  climbCells D q sibs ++ [ptr] ++
    (List.range (80 - 4 * pd)).map (fun j => (rd (ptr.limb 0 * Parameters.gpow (4 * pd + j))).getD 0) ++
    oqPath0Vals ptr D q sibs ++ ((List.range (pd - 1)).map fun l => oqPathLVals ptr D q sibs (l + 1)).flatten

/-- **The loop body's valuation on one query**: the arguments `[x, N, rew, qsc, qw, qbp, flags,
cap]`, the opening's leaf words and siblings below the cap, its position, the run's pointer. -/
def oqIterVal (rd : Reader) (args : List E) (base I blocks pd cd : ℕ) (leaf : List K) (q : ℕ)
    (sibs : List Digest) (ptr : E) : Val :=
  let σ1 := oqVal1 rd args base I leaf
  let σ2 := setl σ1 (oqK1 base I) (oqLeafVals (oqLeafBl σ1 base I) blocks)
  let σ3 := setl σ2 (oqK2 base I blocks) (oqSumVals rd (args.getD 0 0) (args.getD 3 0) (args.getD 4 0)
    (args.getD 5 0) (σ1 (.n (oqK1 base I - 1))))
  let σ4 := setl σ3 (oqP base I blocks) (oqPathVals rd ptr (hashWords leaf) q pd sibs)
  setl σ4 (oqP base I blocks + 79 + 13 * pd) (oqCapVals rd (memAt rd (args.getD 5 0 * args.getD 0 0) 0)
    (args.getD 6 0) (args.getD 7 0) (args.getD 0 0) (args.getD 1 0) pd cd)

/-! ## Lengths and positions -/

theorem oq_length_rows1Vals (r w : ℕ → E) (I : ℕ) :
    (oqRows1Vals r w I).length = 17 + 18 * (I / 4 - 1) := by
  rw [oqRows1Vals, List.length_append, List.length_append, oq_length_pack4Vals, oq_length_dot4Vals,
    oq_length_flatten_uniform (fun j => oqBlk1Vals r w (j + 1)) 18 (fun _ => oq_length_blk1Vals r w _)]

theorem oq_length_rows0Vals (r w : ℕ → E) (I : ℕ) :
    (oqRows0Vals r w I).length = 6 * (3 * I / 4) + 5 + 6 * (I - 1) := by
  rw [oqRows0Vals, List.length_append, List.length_append, oq_length_wordVals,
    oq_length_flatten_uniform (fun jb => oqPack4Vals (r (4 * jb)) (r (4 * jb + 1)) (r (4 * jb + 2))
      (r (4 * jb + 3))) 6 (fun _ => rfl),
    oq_length_flatten_uniform (fun j => oqWord0BlkVals r w (j + 1)) 6 (fun _ => oq_length_word0BlkVals r w _)]

theorem oq_length_rowsVals {base I : ℕ} (hs : base = 0 ∨ base = 1) (hI : 4 ≤ I) (r w : ℕ → E) :
    8 + oqR base I + (oqRowsVals base I r w).length = oqK1 base I := by
  rcases hs with rfl | rfl
  · simp only [oqRowsVals, oqR, oqK1, oq0W0, zero_ne_one, ↓reduceIte, oq_length_rows0Vals]; omega
  · simp only [oqRowsVals, oqR, oqK1, ↓reduceIte, oq_length_rows1Vals]
    have : 1 ≤ I / 4 := by omega
    omega

theorem oq_length_leafVals (bl : ℕ → Fin 4 → E) (blocks : ℕ) :
    (oqLeafVals bl blocks).length = 2 + 3 * blocks := by
  rw [oqLeafVals, List.length_append, oq_length_flatten_uniform (fun j => [oqMd blocks j,
    (digestScalars (chainRun paramIv bl (oqMd blocks) (j + 1))).1,
    (digestScalars (chainRun paramIv bl (oqMd blocks) (j + 1))).2]) 3 (fun _ => rfl)]
  rfl

theorem oq_length_pathVals (rd : Reader) (ptr : E) (D : Digest) (q pd : ℕ) (sibs : List Digest)
    (hsl : sibs.length = pd) (hpd : 1 ≤ pd) (hpd20 : pd ≤ 20) :
    (oqPathVals rd ptr D q pd sibs).length = 79 + 13 * pd := by
  have hc : (climbCells D q sibs).length = 4 * pd := by
    rw [climbCells, List.flatMap, ← hsl]
    exact (oq_length_flatten_uniform _ 4 (fun _ => length_lvlCells _ _ _) _).trans (by ring)
  rw [oqPathVals, List.length_append, List.length_append, List.length_append, List.length_append, hc,
    List.length_singleton, List.length_map, List.length_range,
    oq_length_flatten_uniform (fun l => oqPathLVals ptr D q sibs (l + 1)) 13 (fun _ => rfl)]
  simp only [oqPath0Vals, List.length_cons, List.length_nil]
  omega

theorem oq_length_capVals (rd : Reader) (dbp flags cap x N : E) (pd cd : ℕ) :
    (oqCapVals rd dbp flags cap x N pd cd).length = 1 + 6 * (cd - 1) + 20 := by
  rw [oqCapVals, List.length_append, List.length_append, List.length_singleton,
    oq_length_flatten_uniform (oqCapBitVals rd dbp pd cd) 6 (fun _ => rfl)]
  rfl

theorem oqPk_lt {base I j : ℕ} (hs : base = 0 ∨ base = 1) (hI : 4 ≤ I) (h4 : I % 4 = 0)
    (hj : j < oqR base I / 2) : oqPk base I j < oqK1 base I := by
  rcases hs with rfl | rfl
  · simp only [oqPk, oq0Pk, oqK1, oq0W0, oqR, zero_ne_one, ↓reduceIte] at hj ⊢; omega
  · simp only [oqPk, oqK1, oqR, ↓reduceIte] at hj ⊢
    split <;> omega

theorem oqPk_ge {base I j : ℕ} (hs : base = 0 ∨ base = 1) : 8 + oqR base I ≤ oqPk base I j := by
  rcases hs with rfl | rfl
  · simp only [oqPk, oq0Pk, oqR, zero_ne_one, ↓reduceIte]; omega
  · simp only [oqPk, oqR, ↓reduceIte]; split <;> omega

/-! ## The cap leaf's index from the bits -/

theorem oq_capPar_eq {pd cd q : ℕ} (hcd : 1 ≤ cd) (hq : q < 2 ^ (pd + cd)) {dbp : E}
    (hcb : ∀ t < cd, memAt rd dbp (pd + t) = bitE (q.testBit (pd + t))) :
    capPar rd dbp pd cd (cd - 1) = gen ^ (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) := by
  rw [capPar]
  rw [Finset.prod_congr rfl fun t ht => by
    rw [show pd + 1 + t = pd + (t + 1) by ring, hcb (t + 1) (by simp at ht; omega)]]
  rw [prod_bitE_gen_pow' (fun t => q.testBit (pd + (t + 1))) (cd - 1), ← pow_add]
  congr 2
  rw [show (fun t => q.testBit (pd + (t + 1))) = (fun t => q.testBit ((pd + 1) + t)) from
    funext fun t => by rw [show pd + (t + 1) = pd + 1 + t by ring], bitsVal_shift,
    (capLeaf_index hcd hq).1]

theorem oq_capIdx_eq {pd cd q : ℕ} (hcd : 1 ≤ cd) (hq : q < 2 ^ (pd + cd)) {dbp : E}
    (hcb : ∀ t < cd, memAt rd dbp (pd + t) = bitE (q.testBit (pd + t))) :
    capIdx rd dbp pd cd = gen ^ (2 ^ cd + q / 2 ^ pd) := by
  rw [capIdx, oq_capPar_eq hcd hq hcb, show memAt rd dbp pd = bitE (q.testBit pd) by simpa using hcb 0 hcd,
    one_add_bitE_three, ← pow_add, ← pow_add, ← (capLeaf_index hcd hq).2]
  congr 1; ring

/-! ## The body holds -/

theorem oq_leafWords_rowR {base I : ℕ} {leaf : List K} (hleaf : leaf.length = oqR base I) :
    leafWords base I (oqRowR leaf) = leaf := by
  apply List.ext_getElem (by simp [leafWords, hleaf])
  intro j h1 h2
  simp [leafWords, oqRowR, limb_ofK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **One query's body holds** at `oqIterVal`, on a memory holding the weights at `rew`, the query
sum chain's step at `qsc·x`, the weight at `qw·x`, the bit run's pointer at `qbp·x` and the bits
there, the frame run's cells at `ptr`, the parent's flag and the cap leaf. -/
theorem oqIter_holds {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) {loop : String}
    {x N rew qsc qw qbp flags cap ptr : E} {leaf : List K} (hleaf : leaf.length = oqR base I) {q : ℕ}
    (hq : q < 2 ^ (pd + cd)) {sibs : List Digest} (hsl : sibs.length = pd)
    (hw : ∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw))
    (hs0 : LoadHolds rd (qsc * x) 0 (memAt rd (qsc * x) 0))
    (hw0 : LoadHolds rd (qw * x) 0 (memAt rd (qw * x) 0))
    (hs1 : LoadHolds rd (qsc * x) 1 (memAt rd (qsc * x) 0 + memAt rd (qw * x) 0 *
      ∑ jw ∈ Finset.range I, leafRowWord base leaf jw * memAt rd rew jw))
    (hdbp : LoadHolds rd (qbp * x) 0 (memAt rd (qbp * x) 0))
    (hbits : ∀ l < pd + cd, LoadHolds rd (memAt rd (qbp * x) 0) l (bitE (q.testBit l)))
    (hptrK : IsInK ptr)
    (hcell : ∀ j < 4 * pd, LoadHolds rd ptr j ((climbCells (hashWords leaf) q sibs).getD j 0))
    (hflag : LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) 1)
    (hcap : CapCell rd cap (2 ^ cd + q / 2 ^ pd) (climb (m := Id) blake2sBytes (hashWords leaf) q sibs))
    (hK : IsInK (x * gen + N))
    (hcall : x * gen + N ≠ 0 → C loop [x * gen, N, rew, qsc, qw, qbp, flags, cap] []) :
    Stmt.HoldsList C rd (oqIterVal rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q sibs ptr)
      (oqLoopBody base I blocks pd cd loop) False (fun rs => rs = []) := by
  obtain ⟨hb, hI, h4, hbl, hfill, hpd1, hpd20, hcd1, hcd8⟩ := hs
  set args := [x, N, rew, qsc, qw, qbp, flags, cap] with hargs
  set R := oqR base I
  set K1 := oqK1 base I
  set K2 := oqK2 base I blocks
  set P := oqP base I blocks
  set r := oqRowR leaf
  set σ1 := oqVal1 rd args base I leaf with hσ1
  have hrew : args.getD 2 0 = rew := rfl
  obtain ⟨rowsV, hrowsV⟩ : ∃ l, l = oqRowsVals base I (oqRowR leaf) (memAt rd rew) := ⟨_, rfl⟩
  set bl := oqLeafBl σ1 base I
  set leafV := oqLeafVals bl blocks with hleafV
  set dot := σ1 (.n (K1 - 1))
  set sumV := oqSumVals rd x qsc qw qbp dot
  set D := hashWords leaf
  set pathV := oqPathVals rd ptr D q pd sibs with hpathV
  set dbp := memAt rd (qbp * x) 0
  set capV := oqCapVals rd dbp flags cap x N pd cd
  set σ := oqIterVal rd args base I blocks pd cd leaf q sibs ptr with hσ
  have hRlen : 8 + R + rowsV.length = K1 := by rw [hrowsV]; exact oq_length_rowsVals hb hI _ _
  have hK2 : K2 = K1 + 2 + 3 * blocks := by simp only [K2, K1, oqK2]; ring
  have hP : P = K2 + 9 := rfl
  have hlv : leafV.length = 2 + 3 * blocks := oq_length_leafVals _ _
  have hpv : pathV.length = 79 + 13 * pd := oq_length_pathVals rd ptr D q pd sibs hsl hpd1 hpd20
  have hcv : capV.length = 1 + 6 * (cd - 1) + 20 := oq_length_capVals _ _ _ _ _ _ _ _
  have hσeq : σ = setl (setl (setl (setl σ1 K1 leafV) K2 sumV) P pathV) (P + 79 + 13 * pd) capV := rfl
  -- lookups
  have l1 : ∀ i, i < K1 → σ (.n i) = σ1 (.n i) := fun i hi => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega)]
  have larg : ∀ i < 8, σ (.n i) = args.getD i 0 := fun i hi => by
    rw [l1 i (by omega), hσ1, oqVal1]; simp only [setl]
    rw [set_n_lt (by omega), set_n_lt (by omega)]; rfl
  have lrow : ∀ j < R, σ (.n (8 + j)) = r j := fun j hj => by
    rw [l1 _ (by omega), hσ1, oqVal1]; simp only [setl]
    rw [set_n_lt (by omega), set_n_in (by omega) (by simp; omega), Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_range (show j < oqR base I from hj), r]
  have lrows : ∀ k < rowsV.length, σ (.n (8 + R + k)) = rowsV.getD k 0 := fun k hk => by
    rw [l1 _ (by omega), hσ1, oqVal1]; simp only [setl, hrew, ← hrowsV]
    rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have lleaf : ∀ k < 2 + 3 * blocks, σ (.n (K1 + k)) = leafV.getD k 0 := fun k hk => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by omega),
      Nat.add_sub_cancel_left]
  have lsum : ∀ k < 9, σ (.n (K2 + k)) = sumV.getD k 0 := fun k hk => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by simp [sumV, oqSumVals]; omega),
      Nat.add_sub_cancel_left]
  have lpath : ∀ k < 79 + 13 * pd, σ (.n (P + k)) = pathV.getD k 0 := fun k hk => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have lcap : ∀ k < 1 + 6 * (cd - 1) + 20, σ (.n (P + 79 + 13 * pd + k)) = capV.getD k 0 := fun k hk => by
    rw [hσeq]; simp only [setl]
    rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have a0 : σ (.n 0) = x := larg 0 (by omega)
  have a1 : σ (.n 1) = N := larg 1 (by omega)
  have a2 : σ (.n 2) = rew := larg 2 (by omega)
  have a3 : σ (.n 3) = qsc := larg 3 (by omega)
  have a4 : σ (.n 4) = qw := larg 4 (by omega)
  have a5 : σ (.n 5) = qbp := larg 5 (by omega)
  have a6 : σ (.n 6) = flags := larg 6 (by omega)
  have a7 : σ (.n 7) = cap := larg 7 (by omega)
  rw [oqLoopBody, holdsList_append, holdsList_append, holdsList_append, holdsList_append]
  -- the row
  have hrows : Stmt.HoldsList C rd σ (oqRows base I) True (fun rs => rs = []) := by
    rcases hb with rfl | rfl
    · rw [oqRows, ite_neg' (by omega)]
      refine oqRows0_complete hI h4 (r := r) (fun j hj => lrow j hj) (fun j _ => ?_) (fun jw hjw => by
        rw [a2]; exact hw jw hjw) (fun k hk => ?_)
      · exact (isInK_iff _).mpr ⟨_, rfl⟩
      · have e := lrows k (by rw [hrowsV]; simp only [oqRowsVals, zero_ne_one, ↓reduceIte, oq_length_rows0Vals]; omega)
        rw [hrowsV] at e; simp only [oqRowsVals, zero_ne_one, ↓reduceIte] at e
        rw [a2]; exact e
    · rw [oqRows, ite_pos' rfl]
      refine oqRows1_complete hI h4 (r := r) (fun j hj => lrow j hj) (fun j _ => ?_) (fun jw hjw => by
        rw [a2]; exact hw jw hjw) (fun k hk => ?_)
      · exact (isInK_iff _).mpr ⟨_, rfl⟩
      · have e := lrows k (by rw [hrowsV]; simp only [oqRowsVals, ↓reduceIte, oq_length_rows1Vals]; omega)
        rw [hrowsV] at e; simp only [oqRowsVals, ↓reduceIte] at e
        rw [a2]; exact e
  have hrf := oqRows_sound hb hI h4 hrows
  have hlw : leafWords base I (rowv σ) = leaf := by
    rw [← oq_leafWords_rowR (base := base) (I := I) hleaf]
    exact List.map_congr_left fun j hj => by rw [rowv, lrow j (List.mem_range.mp hj)]
  -- the leaf hash
  have hpk : ∀ j < blocks, ∀ t : Fin 4, oqLeafBl σ base I j t = σ (.n (oqPk base I (4 * j + t))) := by
    intro j hj t; fin_cases t <;> rfl
  have hσbl : ∀ j < blocks, oqLeafBl σ base I j = bl j := by
    intro j hj; funext t
    rw [hpk j hj, l1 _ (oqPk_lt hb hI h4 (by simp only [R] at hfill; omega))]
    fin_cases t <;> rfl
  have hleafH : Stmt.HoldsList C rd σ (oqLeafT base I blocks) True (fun rs => rs = []) := by
    refine oqLeaf_complete hbl (fun j hj t => ?_) ?_ ?_ (fun j hj => ?_) (fun j hj => ?_) trivial
    · rw [hpk j hj, hrf.2.1 _ (by simp only [R] at hfill; omega)]
      exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
    · have := lleaf 0 (by omega); simpa [leafV, oqLeafVals] using this
    · have := lleaf 1 (by omega); simpa [leafV, oqLeafVals] using this
    · have := lleaf (2 + (3 * j + 0)) (by omega)
      rw [show K1 + (2 + (3 * j + 0)) = oqK1 base I + 3 * j + 2 by ring, hleafV, oqLeafVals,
        oq_getD_app_ge (by simp), List.length_cons, List.length_cons, List.length_nil,
        show 2 + (3 * j + 0) - (0 + 1 + 1) = 3 * j + 0 by omega,
        oq_getD_flatten_uniform _ 3 (fun _ => rfl) _ _ _ hj (by omega)] at this
      simpa using this
    · have e3 := lleaf (2 + (3 * j + 1)) (by omega)
      have e4 := lleaf (2 + (3 * j + 2)) (by omega)
      rw [show K1 + (2 + (3 * j + 1)) = oqK1 base I + 3 * j + 3 by ring, hleafV, oqLeafVals,
        oq_getD_app_ge (by simp), List.length_cons, List.length_cons, List.length_nil,
        show 2 + (3 * j + 1) - (0 + 1 + 1) = 3 * j + 1 by omega,
        oq_getD_flatten_uniform _ 3 (fun _ => rfl) _ _ _ hj (by omega)] at e3
      rw [show K1 + (2 + (3 * j + 2)) = oqK1 base I + 3 * j + 4 by ring, hleafV, oqLeafVals,
        oq_getD_app_ge (by simp), List.length_cons, List.length_cons, List.length_nil,
        show 2 + (3 * j + 2) - (0 + 1 + 1) = 3 * j + 2 by omega,
        oq_getD_flatten_uniform _ 3 (fun _ => rfl) _ _ _ hj (by omega)] at e4
      simp only [List.getD_cons_succ, List.getD_cons_zero] at e3 e4
      rw [e3, e4, chainRun_congr (j + 1) (fun i hi => (hσbl i (by omega)).symm) (fun _ _ => rfl)]
  have hlf := (oqLeaf_sound hbl hfill hrf hleafH).1
  rw [hlw] at hlf
  -- the query sum
  have hdot : σ (.n (oqK1 base I - 1)) = dot := l1 _ (by omega)
  have hdot' : dot = ∑ jw ∈ Finset.range I, leafRowWord base leaf jw * memAt rd rew jw := by
    rw [← hdot, hrf.2.2.2, a2]
    refine Finset.sum_congr rfl fun jw hjw => ?_
    rw [oqRowWord_leaf hrf.1 (Finset.mem_range.mp hjw), hlw]
  have v := fun k (hk : k < 9) => lsum k hk
  have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
  have v3 := v 3 (by omega); have v4 := v 4 (by omega); have v5 := v 5 (by omega)
  have v6 := v 6 (by omega); have v7 := v 7 (by omega); have v8 := v 8 (by omega)
  simp only [sumV, oqSumVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8
  have hsumH : Stmt.HoldsList C rd σ (oqSumT base I blocks) True (fun rs => rs = []) := by
    refine oqSumT_complete (by rw [v0, a3, a0]) (by rw [a3, a0, v1]; exact hs0) (by rw [v2, a4, a0])
      (by rw [a4, a0, v3]; exact hw0) (by rw [v4, v3, hdot]) (by rw [v5, v1, v4]) (by rw [v6, a3, a0])
      (by rw [a3, a0, v5, hdot']; exact hs1) (by rw [v7, a5, a0]) (by rw [a5, a0, v8]; exact hdbp) trivial
  -- the path
  have hcl : (climbCells D q sibs).length = 4 * pd := by
    rw [climbCells, List.flatMap, ← hsl]
    exact (oq_length_flatten_uniform _ 4 (fun _ => length_lvlCells _ _ _) _).trans (by ring)
  have hdbpv : σ (.n (P - 1)) = dbp := by rw [show P - 1 = K2 + 8 by omega]; exact v8
  have pv : ∀ k, k < 79 + 13 * pd → σ (.n (P + k)) = pathV.getD k 0 := lpath
  have hpathH : Stmt.HoldsList C rd σ (oqPathT base I blocks pd) True (fun rs => rs = []) := by
    refine oqPathT_complete hpd1 hpd20 hsl (D := D) (ptr := ptr) ?_ (fun j hj => ?_) ?_ hptrK hcell
      (fun j hj w hw => ?_) (fun l hl => ?_) (fun t ht => ?_) (fun l hl t ht => ?_) trivial
    · exact hlf
    · rw [pv j (by omega), hpathV, oqPathVals, oq_getD_app_lt (by simp [hcl]; omega),
        oq_getD_app_lt (by simp [hcl]; omega), oq_getD_app_lt (by simp [hcl]; omega),
        oq_getD_app_lt (by simp [hcl]; omega)]
    · rw [pv _ (by omega), hpathV, oqPathVals, oq_getD_app_lt (by simp [hcl]),
        oq_getD_app_lt (by simp [hcl]), oq_getD_app_lt (by simp [hcl]),
        oq_getD_app_ge (by simp [hcl])]
      simp [hcl]
    · rw [show oqP base I blocks + 4 * pd + 1 + j = P + (4 * pd + 1 + j) by ring, pv _ (by omega), hpathV,
        oqPathVals, oq_getD_app_lt (by simp [hcl]; omega),
        oq_getD_app_lt (by simp [hcl]; omega), oq_getD_app_ge (by simp [hcl])]
      simp only [List.length_append, hcl, List.length_singleton]
      rw [show 4 * pd + 1 + j - (4 * pd + 1) = j by omega, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (by omega)]
      simp [hw]
    · rw [hdbpv]; exact hbits l (by omega)
    · rw [show P + 81 + t = P + (81 + t) by ring, pv _ (by omega), hpathV, oqPathVals,
        oq_getD_app_lt (by simp [hcl, oqPath0Vals]; omega), oq_getD_app_ge (by simp [hcl]; omega)]
      simp only [List.length_append, hcl, List.length_singleton, List.length_map, List.length_range]
      congr 1; omega
    · rw [show P + 79 + 13 * (l + 1) + t = P + (92 + 13 * l + t) by ring, pv _ (by omega), hpathV, oqPathVals,
        oq_getD_app_ge (by simp [hcl, oqPath0Vals]; omega)]
      simp only [List.length_append, hcl, List.length_map, List.length_range,
        oqPath0Vals, List.length_cons, List.length_nil]
      rw [show 92 + 13 * l + t - (4 * pd + 1 + (80 - 4 * pd) + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) =
        13 * l + t by omega, oq_getD_flatten_uniform _ 13 (fun _ => rfl) _ _ _ hl ht]
  -- the cap leaf
  have htop : σ (.n (P + 77 + 13 * pd)) = (digestScalars (climb (m := Id) blake2sBytes D q sibs)).1 ∧
      σ (.n (P + 77 + 13 * pd + 1)) = (digestScalars (climb (m := Id) blake2sBytes D q sibs)).2 := by
    rw [← climbAt_length, hsl]
    rcases Nat.lt_or_ge pd 2 with h2 | h2
    · obtain rfl : pd = 1 := by omega
      have e9 := pv 90 (by omega); have e10 := pv 91 (by omega)
      rw [hpathV, oqPathVals, oq_getD_app_lt (by simp [hcl, oqPath0Vals]),
        oq_getD_app_ge (by simp [hcl])] at e9 e10
      simp only [List.length_append, hcl, List.length_singleton, List.length_map, List.length_range] at e9 e10
      simp only [oqPath0Vals, show 90 - (4 * 1 + 1 + (80 - 4 * 1)) = 9 by omega,
        show 91 - (4 * 1 + 1 + (80 - 4 * 1)) = 10 by omega, List.getD_cons_succ, List.getD_cons_zero] at e9 e10
      exact ⟨e9, e10⟩
    · have e11 := pv (92 + 13 * (pd - 2) + 11) (by omega)
      have e12 := pv (92 + 13 * (pd - 2) + 12) (by omega)
      rw [hpathV, oqPathVals, oq_getD_app_ge (by simp [hcl, oqPath0Vals]; omega)] at e11 e12
      simp only [List.length_append, hcl, List.length_map, List.length_range,
        oqPath0Vals, List.length_cons, List.length_nil] at e11 e12
      rw [show 92 + 13 * (pd - 2) + 11 - (4 * pd + 1 + (80 - 4 * pd) + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) =
        13 * (pd - 2) + 11 by omega, oq_getD_flatten_uniform _ 13 (fun _ => rfl) _ _ _ (by omega) (by omega)] at e11
      rw [show 92 + 13 * (pd - 2) + 12 - (4 * pd + 1 + (80 - 4 * pd) + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) =
        13 * (pd - 2) + 12 by omega, oq_getD_flatten_uniform _ 13 (fun _ => rfl) _ _ _ (by omega) (by omega)] at e12
      simp only [oqPathLVals, List.getD_cons_succ, List.getD_cons_zero, show pd - 2 + 1 + 1 = pd by omega] at e11 e12
      rw [show P + 77 + 13 * pd = P + (92 + 13 * (pd - 2) + 11) by omega,
        show P + (92 + 13 * (pd - 2) + 11) + 1 = P + (92 + 13 * (pd - 2) + 12) by omega]
      exact ⟨e11, e12⟩
  have hcb : ∀ t < cd, memAt rd dbp (pd + t) = bitE (q.testBit (pd + t)) := fun t ht =>
    memAt_of_load (hbits (pd + t) (by omega))
  have hcapH : Stmt.HoldsList C rd σ (oqCapT P pd cd loop) False (fun rs => rs = []) := by
    refine oqCapT_complete hcd1 hcd8 (fun k hk => ?_) (fun t ht => ?_) ?_ ?_ ?_ (by rw [a0, a1]; exact hK)
      (fun h => ?_) rfl
    · rw [lcap k hk, hdbpv, a6, a7, a0, a1]
    · rw [hdbpv, hcb t ht]; exact hbits (pd + t) (by omega)
    · rw [a6, hdbpv, oq_capPar_eq hcd1 hq hcb, loadHolds_gen_pow]; exact hflag
    · rw [a7, hdbpv, oq_capIdx_eq hcd1 hq hcb, ← pow_add, loadHolds_gen_pow, htop.1, ← two_mul]
      exact hcap.1
    · rw [a7, hdbpv, oq_capIdx_eq hcd1 hq hcb, mul_assoc, ← pow_add, ← pow_succ', loadHolds_gen_pow,
        htop.2, ← two_mul]
      exact hcap.2
    · rw [a0, a1] at h
      rw [a0, a1, a2, a3, a4, a5, a6, a7]
      exact hcall h
  refine (holdsList_noRet _ (oqRows_noRet _ _) _ _).mpr ⟨hrows, ?_⟩
  refine (holdsList_noRet _ (oqLeafT_noRet _ _ _) _ _).mpr ⟨hleafH, ?_⟩
  refine (holdsList_noRet _ rfl _ _).mpr ⟨hsumH, ?_⟩
  refine (holdsList_noRet _ (oqPathT_noRet _ _ _ _) _ _).mpr ⟨hpathH, hcapH⟩

/-- **The pointers the body loads through**, at `oqIterVal`: the weights, the query sum's steps,
the query's weight and bit run, the bits, the path's selected children in the frame run at `ptr`,
the flag and the cap leaf. -/
theorem oqIterVal_ptrs {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd)
    {x N rew qsc qw qbp flags cap ptr : E} {leaf : List K} {q : ℕ}
    (hq : q < 2 ^ (pd + cd)) {sibs : List Digest} (hsl : sibs.length = pd)
    (hbits : ∀ l < pd + cd, memAt rd (memAt rd (qbp * x) 0) l = bitE (q.testBit l)) :
    let σ := oqIterVal rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q sibs ptr
    let K7 := oqP base I blocks + 79 + 13 * pd + 6 * cd - 5
    σ (.n 2) = rew ∧ σ (.n (oqK2 base I blocks)) = qsc * x ∧ σ (.n (oqK2 base I blocks + 2)) = qw * x ∧
      σ (.n (oqK2 base I blocks + 6)) = qsc * x ∧ σ (.n (oqK2 base I blocks + 7)) = qbp * x ∧
      σ (.n (oqP base I blocks - 1)) = memAt rd (qbp * x) 0 ∧
      σ (.n (oqP base I blocks + 86)) = ptr * gen ^ (2 * (q.testBit 0).toNat) ∧
      (∀ l, 1 ≤ l → l < pd → σ (.n (oqP base I blocks + 79 + 13 * l + 7)) =
        ptr * gen ^ (4 * l + 2 * (q.testBit l).toNat)) ∧
      σ (.n (K7 + 1)) = flags * gen ^ (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) ∧
      σ (.n (K7 + 10)) = cap * gen ^ (2 * (2 ^ cd + q / 2 ^ pd)) ∧
      σ (.n (K7 + 14)) = cap * gen ^ (2 * (2 ^ cd + q / 2 ^ pd) + 1) ∧
      σ (.n (K7 + 17)) = x * gen + N ∧ σ (.n (K7 + 19)) = x * gen ∧ σ (.n (oqP base I blocks + 4 * pd)) = ptr ∧
      ∀ i < 8, σ (.n i) = [x, N, rew, qsc, qw, qbp, flags, cap].getD i 0 := by
  intro σ' K7
  simp only [σ', K7]
  obtain ⟨hb, hI, h4, hbl, hfill, hpd1, hpd20, hcd1, hcd8⟩ := hs
  set args := [x, N, rew, qsc, qw, qbp, flags, cap] with hargs
  set R := oqR base I
  set K1 := oqK1 base I
  set K2 := oqK2 base I blocks
  set P := oqP base I blocks
  set r := oqRowR leaf
  set σ1 := oqVal1 rd args base I leaf with hσ1
  have hrew : args.getD 2 0 = rew := rfl
  obtain ⟨rowsV, hrowsV⟩ : ∃ l, l = oqRowsVals base I (oqRowR leaf) (memAt rd rew) := ⟨_, rfl⟩
  set bl := oqLeafBl σ1 base I
  set leafV := oqLeafVals bl blocks with hleafV
  set dot := σ1 (.n (K1 - 1))
  set sumV := oqSumVals rd x qsc qw qbp dot
  set D := hashWords leaf
  set pathV := oqPathVals rd ptr D q pd sibs with hpathV
  set dbp := memAt rd (qbp * x) 0
  set capV := oqCapVals rd dbp flags cap x N pd cd with hcapV
  set σ := oqIterVal rd args base I blocks pd cd leaf q sibs ptr with hσ
  have hRlen : 8 + R + rowsV.length = K1 := by rw [hrowsV]; exact oq_length_rowsVals hb hI _ _
  have hK2 : K2 = K1 + 2 + 3 * blocks := by simp only [K2, K1, oqK2]; ring
  have hP : P = K2 + 9 := rfl
  have hlv : leafV.length = 2 + 3 * blocks := oq_length_leafVals _ _
  have hpv : pathV.length = 79 + 13 * pd := oq_length_pathVals rd ptr D q pd sibs hsl hpd1 hpd20
  have hcv : capV.length = 1 + 6 * (cd - 1) + 20 := oq_length_capVals _ _ _ _ _ _ _ _
  have hσeq : σ = setl (setl (setl (setl σ1 K1 leafV) K2 sumV) P pathV) (P + 79 + 13 * pd) capV := rfl
  -- lookups
  have l1 : ∀ i, i < K1 → σ (.n i) = σ1 (.n i) := fun i hi => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega)]
  have larg : ∀ i < 8, σ (.n i) = args.getD i 0 := fun i hi => by
    rw [l1 i (by omega), hσ1, oqVal1]; simp only [setl]
    rw [set_n_lt (by omega), set_n_lt (by omega)]; rfl
  have lrow : ∀ j < R, σ (.n (8 + j)) = r j := fun j hj => by
    rw [l1 _ (by omega), hσ1, oqVal1]; simp only [setl]
    rw [set_n_lt (by omega), set_n_in (by omega) (by simp; omega), Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_range (show j < oqR base I from hj), r]
  have lrows : ∀ k < rowsV.length, σ (.n (8 + R + k)) = rowsV.getD k 0 := fun k hk => by
    rw [l1 _ (by omega), hσ1, oqVal1]; simp only [setl, hrew, ← hrowsV]
    rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have lleaf : ∀ k < 2 + 3 * blocks, σ (.n (K1 + k)) = leafV.getD k 0 := fun k hk => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by omega),
      Nat.add_sub_cancel_left]
  have lsum : ∀ k < 9, σ (.n (K2 + k)) = sumV.getD k 0 := fun k hk => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by simp [sumV, oqSumVals]; omega),
      Nat.add_sub_cancel_left]
  have lpath : ∀ k < 79 + 13 * pd, σ (.n (P + k)) = pathV.getD k 0 := fun k hk => by
    rw [hσeq]; simp only [setl]
    rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have lcap : ∀ k < 1 + 6 * (cd - 1) + 20, σ (.n (P + 79 + 13 * pd + k)) = capV.getD k 0 := fun k hk => by
    rw [hσeq]; simp only [setl]
    rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have a0 : σ (.n 0) = x := larg 0 (by omega)
  have a1 : σ (.n 1) = N := larg 1 (by omega)
  have a2 : σ (.n 2) = rew := larg 2 (by omega)
  have a3 : σ (.n 3) = qsc := larg 3 (by omega)
  have a4 : σ (.n 4) = qw := larg 4 (by omega)
  have a5 : σ (.n 5) = qbp := larg 5 (by omega)
  have a6 : σ (.n 6) = flags := larg 6 (by omega)
  have a7 : σ (.n 7) = cap := larg 7 (by omega)
  have hcl : (climbCells D q sibs).length = 4 * pd := by
    rw [climbCells, List.flatMap, ← hsl]
    exact (oq_length_flatten_uniform _ 4 (fun _ => length_lvlCells _ _ _) _).trans (by ring)
  have hcb : ∀ t < cd, memAt rd dbp (pd + t) = bitE (q.testBit (pd + t)) := fun t ht => hbits (pd + t) (by omega)
  have v0 := lsum 0 (by omega); have v2 := lsum 2 (by omega); have v6 := lsum 6 (by omega)
  have v7 := lsum 7 (by omega); have v8 := lsum 8 (by omega)
  simp only [sumV, oqSumVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v2 v6 v7 v8
  refine ⟨a2, v0, v2, v6, v7, by rw [show oqP base I blocks - 1 = K2 + 8 by omega]; exact v8, ?_, fun l hl1 hl2 => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, larg⟩
  · have e := lpath 86 (by omega)
    rw [hpathV, oqPathVals, oq_getD_app_lt (by simp [hcl, oqPath0Vals]; omega),
      oq_getD_app_ge (by simp [hcl]; omega)] at e
    simp only [List.length_append, hcl, List.length_singleton, List.length_map, List.length_range,
      show 86 - (4 * pd + 1 + (80 - 4 * pd)) = 5 by omega, oqPath0Vals, List.getD_cons_succ,
      List.getD_cons_zero] at e
    rw [e, one_add_bitE_five]
  · have e := lpath (92 + 13 * (l - 1) + 7) (by omega)
    rw [hpathV, oqPathVals, oq_getD_app_ge (by simp [hcl, oqPath0Vals]; omega)] at e
    simp only [List.length_append, hcl, List.length_map, List.length_range,
      oqPath0Vals, List.length_cons, List.length_nil] at e
    rw [show 92 + 13 * (l - 1) + 7 - (4 * pd + 1 + (80 - 4 * pd) + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) =
      13 * (l - 1) + 7 by omega, oq_getD_flatten_uniform _ 13 (fun _ => rfl) _ _ _ (by omega) (by omega)] at e
    simp only [oqPathLVals, List.getD_cons_succ, List.getD_cons_zero, show l - 1 + 1 = l by omega] at e
    rw [show oqP base I blocks + 79 + 13 * l + 7 = P + (92 + 13 * (l - 1) + 7) by omega, e, one_add_bitE_five,
      mul_assoc, ← pow_add]
  · have e := lcap (6 * cd - 5 + 1) (by omega)
    rw [show P + 79 + 13 * pd + (6 * cd - 5 + 1) = K7 + 1 by simp only [K7, P]; omega] at e
    rw [e, hcapV, oqCapVals, oq_getD_app_ge (by simp [oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _)]; omega),
      List.length_append, List.length_singleton, oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _),
      show 6 * cd - 5 + 1 - (1 + 6 * (cd - 1)) = 1 by omega]
    simp only [oqCapTailVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [oq_capPar_eq hcd1 hq hcb]
  · have e := lcap (6 * cd - 5 + 10) (by omega)
    rw [show P + 79 + 13 * pd + (6 * cd - 5 + 10) = K7 + 10 by simp only [K7, P]; omega] at e
    rw [e, hcapV, oqCapVals, oq_getD_app_ge (by simp [oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _)]; omega),
      List.length_append, List.length_singleton, oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _),
      show 6 * cd - 5 + 10 - (1 + 6 * (cd - 1)) = 10 by omega]
    simp only [oqCapTailVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [oq_capIdx_eq hcd1 hq hcb, ← pow_add, ← two_mul]
  · have e := lcap (6 * cd - 5 + 14) (by omega)
    rw [show P + 79 + 13 * pd + (6 * cd - 5 + 14) = K7 + 14 by simp only [K7, P]; omega] at e
    rw [e, hcapV, oqCapVals, oq_getD_app_ge (by simp [oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _)]; omega),
      List.length_append, List.length_singleton, oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _),
      show 6 * cd - 5 + 14 - (1 + 6 * (cd - 1)) = 14 by omega]
    simp only [oqCapTailVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [oq_capIdx_eq hcd1 hq hcb, mul_assoc, ← pow_add, ← pow_succ', ← two_mul]
  · have e := lcap (6 * cd - 5 + 17) (by omega)
    rw [show P + 79 + 13 * pd + (6 * cd - 5 + 17) = K7 + 17 by simp only [K7, P]; omega] at e
    rw [e, hcapV, oqCapVals, oq_getD_app_ge (by simp [oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _)]; omega),
      List.length_append, List.length_singleton, oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _),
      show 6 * cd - 5 + 17 - (1 + 6 * (cd - 1)) = 17 by omega]
    simp only [oqCapTailVals, List.getD_cons_succ, List.getD_cons_zero]
  · have e := lcap (6 * cd - 5 + 19) (by omega)
    rw [show P + 79 + 13 * pd + (6 * cd - 5 + 19) = K7 + 19 by simp only [K7, P]; omega] at e
    rw [e, hcapV, oqCapVals, oq_getD_app_ge (by simp [oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _)]; omega),
      List.length_append, List.length_singleton, oq_length_flatten_uniform _ 6 (fun _ => oq_length_capBitVals rd dbp pd cd _),
      show 6 * cd - 5 + 19 - (1 + 6 * (cd - 1)) = 19 by omega]
    simp only [oqCapTailVals, List.getD_cons_succ, List.getD_cons_zero]
  · rw [lpath (4 * pd) (by omega), hpathV, oqPathVals, oq_getD_app_lt (by simp [hcl]),
      oq_getD_app_lt (by simp [hcl]), oq_getD_app_lt (by simp [hcl]), oq_getD_app_ge (by simp [hcl])]
    simp [hcl]

end
end LeanVM.Guest.B1
