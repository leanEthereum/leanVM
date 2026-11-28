/-
  LeanVM.Guest.B1.Main.Aggregate

  `aggregate_claims`' soundness: its core IR writes the outcome of the batching program
  (`Batch.nodeBatchingProgram`, the one `DeferredClaimBatched` runs) on the stream of the children
  whose words the memory holds.
-/

module

public import LeanVM.Guest.B1.Main.AggBody
public import LeanVM.Guest.B1.Main.AggIface
public import LeanVM.Guest.B1.Sumcheck.Batch
public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Common.MemSize
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims»

/-!
# `aggregate_claims`

`aggregate_claims_holds : AggregateClaimsSound`: at a valuation of its body, for
`n_children_g = g^m`, `aggregate_claims` writes at `defer_stmt` the sumcheck's point and
`bc_star_hint`, and for `m` children whose words the memory holds (`ChildWordsAt`) the batching
program accepts their stream with the hints `aggHints rd σ` and that claim as its outcome
(`runBatching_of_carried`), from the carried sponge:

* the absorbing rows (`aggregate_claims_loop0`, `a0_step`) carry the sponge after the count and the
  first `c` children's words (`absorb_rows`);
* the last absorbing row is permuted, the nonce absorbed with the tag `4` and permuted, the
  inlined grind on that permutation's cell `1` is its proof of work, `λ` its cell `0`;
* six permutations squeeze the column challenges into `col` (`sqChain_sound`), `eqtree` writes
  their equality table (`tree_sound`), and `aggregate_claims_loop1` folds each fresh claim's values
  against it (`foldColumns`, `fvAcc_eq_foldColumns`);
* the records of `bc_chain` (`aggregate_claims_loop2`) hold `λ^(2c)` and the lambdas'
  combination of the first `c` children's values (`chain_rows`), the last one feeding
  `batch_sumcheck__L25`;
* the weights (`aggregate_claims_loop3`) are the lambdas' combination of the claims' equality
  weights at the sumcheck's point (`weight_rows`), a fresh claim's the product of its point's and
  the column challenges' (`eqEval_fresh`, the column factor `eq_cols`), and the body checks that
  the final claim is the hint times the last.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node LeanVM.Guest.B1

@[expose] public section

variable {rd : Reader}

/-! ## Bookkeeping -/

theorem pend_absorbAll : ∀ (xs : List E) (s : Fs) (t : ℕ), 1 ≤ s.pend.length →
    s.pend.length ≤ 4 → (s.absorbAll xs t).pend.length = (s.pend.length - 1 + xs.length) % 4 + 1
  | [], s, t, h1, h4 => by
    show s.pend.length = _
    simp only [List.length_nil]
    omega
  | x :: xs, s, t, h1, h4 => by
    show ((s.absorb x t).absorbAll xs t).pend.length = _
    by_cases hf : s.pend.length = 4
    · have e : s.absorb x t = ⟨capOf s.perm, [(x, t)]⟩ := by simp [Fs.absorb, hf, rateScalars]
      rw [e, pend_absorbAll xs _ t (by simp) (by simp)]
      simp only [List.length_cons, List.length_nil]
      omega
    · have e : s.absorb x t = ⟨s.cap, s.pend ++ [(x, t)]⟩ := by
        simp [Fs.absorb, hf, rateScalars]
      rw [e, pend_absorbAll xs _ t (by simp) (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_cons]
      omega

/-- The lambdas of `λ`, child `c`'s pair. -/
theorem lambdaPowers_eq (lam : E) (n : ℕ) :
    Batch.lambdaPowers lam n = (List.range n).map fun i ↦ (lam ^ (2 * i), lam ^ (2 * i + 1)) :=
  rfl

/-- A running sum over the first `c + 1` children. -/
theorem zip_prefix {α : Type} (F : α → E × E → E) (cs : List α) (L : ℕ → E × E) {c : ℕ}
    (hc : c < cs.length) :
    sumE (List.zipWith F (cs.take (c + 1)) ((List.range (c + 1)).map L)) =
      sumE (List.zipWith F (cs.take c) ((List.range c).map L)) + F cs[c] (L c) := by
  rw [List.take_succ_eq_append_getElem hc, List.range_succ, List.map_append,
    List.zipWith_append (by simp; omega)]
  simp [sumE, List.foldl_append]

theorem memAt_of_reads {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    memAt rd p k = xs.getD k 0 := by
  rw [memAt_of_load (h k hk), List.getD_eq_getElem _ _ hk]

/-! ## A child's words -/

theorem childCells_eq (cc : ChildClaims) (h1 : cc.freshClaim.point.length = 19)
    (h1' : cc.freshClaim.values.length = 36) (h2 : cc.carriedClaim.bytecodePoint.length = 25) :
    Batch.childCells cc = cc.words ++ [0] := by
  have hl : cc.words.length = 83 := by
    simp [ChildClaims.words, FreshClaim.cells, DeferredBytecodeClaim.cells, h1, h1', h2]
  rw [Batch.childCells, padToRate, hl]
  rfl

/-- **A child's words, as the loops read them.** -/
theorem kid_words {cpi cfresh ccarried : E} {c : ℕ} {cc : ChildClaims}
    (h : ChildWordsAt rd cpi cfresh ccarried c cc) :
    (∀ j < 36, memAt rd (cfresh * (gen ^ c) ^ 55) (19 + j) = cc.freshClaim.values.getD j 0) ∧
    memAt rd (ccarried * (gen ^ c) ^ 26) 25 = cc.carriedClaim.bytecodeValue ∧
    memRun rd (cfresh * (gen ^ c) ^ 55) 19 = cc.freshClaim.point ∧
    memRun rd (ccarried * (gen ^ c) ^ 26) 25 = cc.carriedClaim.bytecodePoint ∧
    l25Words rd cpi cfresh ccarried (gen ^ c) = Batch.childCells cc := by
  obtain ⟨⟨h1, h1'⟩, h2, hp0, hp1, hf, hc⟩ := h
  have e55 : (gen ^ c) ^ 55 = gen ^ (55 * c) := by rw [← pow_mul, mul_comm]
  have e26 : (gen ^ c) ^ 26 = gen ^ (26 * c) := by rw [← pow_mul, mul_comm]
  have e2 : (gen ^ c) ^ 2 = gen ^ (2 * c) := by rw [← pow_mul, mul_comm]
  have b19 : bytecodeLog = 19 := rfl
  have b36 : nSplit = 36 := rfl
  have b25 : bytecodeVars = 25 := rfl
  rw [b19] at h1
  rw [b36] at h1'
  rw [b25] at h2
  rw [e55, e26]
  have hfl : cc.freshClaim.cells.length = 55 := by simp [FreshClaim.cells, h1, h1']
  have hcl : cc.carriedClaim.cells.length = 26 := by simp [DeferredBytecodeClaim.cells, h2]
  have pf := (readsAt_append.mp (show ReadsAt rd _ (cc.freshClaim.point ++ cc.freshClaim.values)
    from hf)).1
  have pc := (readsAt_append.mp (show ReadsAt rd _ (cc.carriedClaim.bytecodePoint ++
    [cc.carriedClaim.bytecodeValue]) from hc)).1
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [memAt_of_reads hf (by omega)]
    simp only [FreshClaim.cells]
    rw [List.getD_append_right _ _ _ _ (by omega), h1, Nat.add_sub_cancel_left]
  · rw [memAt_of_reads hc (by omega)]
    simp [DeferredBytecodeClaim.cells, List.getD_eq_getElem?_getD, h2]
  · rw [readsAt_memRun pf, h1]
  · rw [readsAt_memRun pc, h2]
  · rw [childCells_eq cc h1 h1' h2]
    have hwl : (cc.words ++ [0]).length = 84 := by
      simp [ChildClaims.words, FreshClaim.cells, DeferredBytecodeClaim.cells, h1, h1', h2]
    refine list_eq_of_getD (n := 84) (by simp [l25Words]) hwl fun w hw => ?_
    have lhs : (l25Words rd cpi cfresh ccarried (gen ^ c)).getD w 0 =
        l25Word rd cpi cfresh ccarried (gen ^ c) w := by
      simp [l25Words, List.getD_eq_getElem?_getD, hw]
    rw [lhs, l25Word, ChildClaims.words, e2, e55, e26]
    generalize hA2 : ([(digestHalves cc.publicInput).1, (digestHalves cc.publicInput).2] :
      List E) = A2
    have hA : A2.length = 2 := by rw [← hA2]; rfl
    have hAF : (A2 ++ cc.freshClaim.cells).length = 57 := by simp [hA, hfl]
    have hAFC : (A2 ++ cc.freshClaim.cells ++ cc.carriedClaim.cells).length = 83 := by
      simp [hA, hfl, hcl]
    by_cases ha : w < 83
    · rw [List.getD_append (A2 ++ cc.freshClaim.cells ++ cc.carriedClaim.cells) [0] 0 w
        (by rw [hAFC]; exact ha)]
      by_cases hb : w < 57
      · rw [List.getD_append (A2 ++ cc.freshClaim.cells) cc.carriedClaim.cells 0 w
          (by rw [hAF]; exact hb)]
        by_cases hc2 : w < 2
        · rw [ite_pos' hc2, List.getD_append A2 cc.freshClaim.cells 0 w (by rw [hA]; exact hc2),
            ← hA2]
          rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
          · exact memAt_of_load ((loadHolds_mul_gen_pow rd _ _ _ _).mpr hp0)
          · exact memAt_of_load ((loadHolds_mul_gen_pow rd _ _ _ _).mpr hp1)
        · rw [ite_neg' hc2, ite_pos' hb,
            List.getD_append_right A2 cc.freshClaim.cells 0 w (by rw [hA]; omega), hA,
            memAt_of_reads hf (by omega)]
      · rw [ite_neg' (show ¬ w < 2 by omega), ite_neg' hb, ite_pos' ha,
          List.getD_append_right (A2 ++ cc.freshClaim.cells) cc.carriedClaim.cells 0 w
            (by rw [hAF]; omega), hAF, memAt_of_reads hc (by omega)]
    · rw [ite_neg' (show ¬ w < 2 by omega), ite_neg' (show ¬ w < 57 by omega), ite_neg' ha,
        List.getD_append_right (A2 ++ cc.freshClaim.cells ++ cc.carriedClaim.cells) [0] 0 w
          (by rw [hAFC]; omega), hAFC]
      rcases (show w = 83 by omega) with rfl
      rfl

/-! ## The rows -/

/-- **The absorbing rows**: row `c` carries the sponge after the count and the first `c`
children's words. -/
theorem absorb_rows {absorb cpi cfresh lfT ccarried lcT : E} {m : ℕ} {cs : List ChildClaims}
    (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (L25 : ∀ c < m, L25Step rd absorb cfresh lfT ccarried lcT cpi (gen ^ c))
    (h0 : RowRel rd absorb (aggS0.absorbAll (Batch.childCountCells m) dsObserve))
    (hp0 : (aggS0.absorbAll (Batch.childCountCells m) dsObserve).pend.length = 4) :
    ∀ c ≤ m, RowRel rd (absorb * (gen ^ c) ^ 13)
      (aggS0.absorbAll (Batch.childCountCells m ++ (cs.take c).flatMap Batch.childCells) dsObserve) ∧
      (aggS0.absorbAll (Batch.childCountCells m ++ (cs.take c).flatMap Batch.childCells)
        dsObserve).pend.length = 4 := by
  intro c
  induction c with
  | zero => intro _; simpa using ⟨h0, hp0⟩
  | succ c ih =>
    intro hc
    obtain ⟨hr, hp⟩ := ih (by omega)
    have hcc : c < cs.length := by omega
    obtain ⟨-, -, -, -, hw⟩ := kid_words (hcw c hcc)
    obtain ⟨-, -, hstep⟩ := L25 c (by omega)
    rw [List.take_succ_eq_append_getElem hcc, List.flatMap_append, List.flatMap_singleton,
      ← List.append_assoc, absorbAll_append, ← hw]
    refine ⟨?_, ?_⟩
    · have := hstep _ hp hr
      rwa [show absorb * (gen ^ c) ^ 13 * gen ^ 13 = absorb * (gen ^ (c + 1)) ^ 13 by ring]
        at this
    · rw [pend_absorbAll, hp]
      · simp [l25Words]
      · omega
      · omega

/-- **The records of `bc_chain`**: record `c` holds `λ^(2c)` and the lambdas' combination of the
first `c` children's folded values and carried values. -/
theorem chain_rows {chainT lcT fvT lam : E} {cols : List E} {m : ℕ}
    {cs : List ChildClaims} (hcl : cs.length = m)
    (A2 : ∀ c < m, A2Step rd chainT lcT (lam * lam) fvT lam (gen ^ c))
    (hfv : ∀ c (hc : c < cs.length), memAt rd (fvT * gen ^ c) 0 =
      Batch.foldColumns cols cs[c].freshClaim.values)
    (hcv : ∀ c (hc : c < cs.length), memAt rd (memAt rd (lcT * gen ^ c) 0) 25 =
      cs[c].carriedClaim.bytecodeValue)
    (h0 : memAt rd chainT 0 = 1) (hz : memAt rd chainT 1 = 0) :
    ∀ c ≤ m, memAt rd (chainT * (gen ^ c) ^ 2) 0 = lam ^ (2 * c) ∧
      memAt rd (chainT * (gen ^ c) ^ 2) 1 = sumE (List.zipWith (fun c l ↦
        l.1 * Batch.foldColumns cols c.freshClaim.values + l.2 * c.carriedClaim.bytecodeValue)
        (cs.take c) (Batch.lambdaPowers lam c)) := by
  intro c
  induction c with
  | zero => intro _; simpa [Batch.lambdaPowers, sumE] using ⟨h0, hz⟩
  | succ c ih =>
    intro hc
    obtain ⟨hpow, hacc⟩ := ih (by omega)
    have hcc : c < cs.length := by omega
    obtain ⟨s2, s3⟩ := A2 c (by omega)
    have e2 : chainT * (gen ^ (c + 1)) ^ 2 = chainT * (gen ^ c) ^ 2 * gen ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · rw [e2, memAt_of_load ((loadHolds_mul_gen_pow rd _ 2 0 _).mpr s2), hpow]
      ring
    · rw [e2, memAt_of_load ((loadHolds_mul_gen_pow rd _ 2 1 _).mpr s3), lambdaPowers_eq,
        zip_prefix _ _ _ hcc, ← lambdaPowers_eq, ← hacc, hpow, hfv c hcc, hcv c hcc]
      ring

/-- **The weights**: `w[c]` is the lambdas' combination of the first `c` children's equality
weights at `r`, a fresh claim's the product of its point's at `r`'s first `19` coordinates and
the column factor `eqc`. -/
theorem weight_rows {lfT lcT wT chainT pt1 lam eqc : E} {r : List E} {m : ℕ}
    {cs : List ChildClaims} (hcl : cs.length = m)
    (A3 : ∀ c < m, A3Step rd lfT lcT pt1 chainT wT eqc lam (gen ^ c))
    (hpow : ∀ c < m, memAt rd (chainT * (gen ^ c) ^ 2) 0 = lam ^ (2 * c))
    (hfp : ∀ c (hc : c < cs.length), memRun rd (memAt rd (lfT * gen ^ c) 0) 19 =
      cs[c].freshClaim.point)
    (hcp : ∀ c (hc : c < cs.length), memRun rd (memAt rd (lcT * gen ^ c) 0) 25 =
      cs[c].carriedClaim.bytecodePoint)
    (hpt19 : (memRun rd pt1 19).map (1 + ·) = r.take 19)
    (hpt25 : (memRun rd pt1 25).map (1 + ·) = r) (hz : memAt rd wT 0 = 0) :
    ∀ c ≤ m, memAt rd (wT * gen ^ c) 0 = sumE (List.zipWith (fun c l ↦
      l.1 * (eqEval c.freshClaim.point (r.take 19) * eqc) + l.2 * eqEval c.carriedClaim.bytecodePoint r)
      (cs.take c) (Batch.lambdaPowers lam c)) := by
  intro c
  induction c with
  | zero => intro _; simpa [Batch.lambdaPowers, sumE] using hz
  | succ c ih =>
    intro hc
    have hcc : c < cs.length := by omega
    have hst := A3 c (by omega)
    rw [show wT * gen ^ (c + 1) = wT * gen ^ c * gen ^ 1 by ring,
      memAt_of_load ((loadHolds_mul_gen_pow rd _ 1 0 _).mpr hst), lambdaPowers_eq,
      zip_prefix _ _ _ hcc, ← lambdaPowers_eq, ih (by omega), hpow c (by omega),
      hfp c hcc, hcp c hcc, hpt19, hpt25]
    ring

/-! ## `aggregate_claims` -/

theorem headCells_eq (m : ℕ) : Batch.childCountCells m = [gen ^ m, 0, 0, 0] := rfl

theorem absorb_head (m : ℕ) : aggS0.absorbAll (Batch.childCountCells m) dsObserve =
    ⟨capOf batchSeed, [gen ^ m, 0, 0, 0].map (·, dsObserve)⟩ := by
  rw [headCells_eq, absorbAll_short aggS0 _ dsObserve (by simp [aggS0])]
  rfl

theorem pairs_getD : ∀ (l : List (E × E)) (i : ℕ),
    (l.flatMap fun g => [g.1, g.2]).getD (2 * i) 0 = (l.getD i 0).1 ∧
      (l.flatMap fun g => [g.1, g.2]).getD (2 * i + 1) 0 = (l.getD i 0).2
  | [], _ => by simp
  | p :: l, 0 => by simp
  | p :: l, i + 1 => by
    have ih := pairs_getD l i
    simp only [List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact ih

/-- Rounds read from memory one word past `p` are the memory's at `1 + 2k`, `2 + 2k`. -/
theorem rounds_of_reads {rd : Reader} {p : E} {rounds : List (E × E)} {n : ℕ}
    (hl : rounds.length = n) (h : ReadsAt rd (p * gen) (rounds.flatMap fun g => [g.1, g.2])) :
    rounds = (List.range n).map fun k => (memAt rd p (1 + 2 * k), memAt rd p (2 + 2 * k)) := by
  have hlen : (rounds.flatMap fun g => [g.1, g.2]).length = 2 * n := by
    simp [List.length_flatMap, hl, mul_comm]
  refine List.ext_getElem (by simp [hl]) fun k h1 h2 => ?_
  have hk : k < n := by omega
  obtain ⟨e0, e1⟩ := pairs_getD rounds k
  have l0 := h (2 * k) (by omega)
  have l1 := h (2 * k + 1) (by omega)
  rw [← List.getD_eq_getElem _ 0, e0, ← pow_one gen, loadHolds_mul_gen_pow] at l0
  rw [← List.getD_eq_getElem _ 0, e1, ← pow_one gen, loadHolds_mul_gen_pow,
    show 1 + (2 * k + 1) = 2 + 2 * k by omega] at l1
  simp only [List.getElem_map, List.getElem_range]
  rw [memAt_of_load l0, memAt_of_load l1, List.getD_eq_getElem _ _ h1]

/-- The cells of a nonce's permutation: the nonce's two cells, six zeros, the capacity of the
permutation of four waiting scalars. -/
theorem nonce_ins {s : Fs} (hs : s.pend.length = 4) (n : E) :
    s.nonceState n = permOf ([n, word 0 dsPowNonce, 0, 0, 0, 0, 0, 0] ++ capOf s.perm) := by
  have e : s.absorb n dsPowNonce = ⟨capOf s.perm, [(n, dsPowNonce)]⟩ := by
    simp [Fs.absorb, hs, rateScalars]
  rw [Fs.nonceState, e, perm_eq_cells _ (by simp)]
  rfl

/-- **`aggregate_claims` is sound**: at a valuation of its body, it writes the outcome of the
batching program on the stream of the children whose words the memory holds, with the hints
`aggHints rd σ`. -/
theorem aggregate_claims_holds : AggregateClaimsSound := by
  intro C rd hm hle σ args rets hpar hbC
  have hb := holdsList_mono hle _ id (fun _ h => h) hbC
  have hok := agg_ok
  simp only [aggOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hflat, hparams⟩, hseed⟩, hp0⟩, hz3⟩, hrate⟩, hg33⟩, hm42⟩, hk⟩, hrin⟩, hnA⟩, hkn⟩, hgr⟩, hm94⟩, hsq⟩, htree⟩, hc62⟩, hm62⟩, hg1⟩, hc99⟩, hl99⟩, hc100⟩, hl100⟩, hg2⟩, hm105⟩, hl106⟩, hg109⟩, hbs⟩, hpt1⟩, heqc⟩, hc189⟩, hl189⟩, hg3⟩, hm193⟩, hl194⟩, hm195⟩, hae⟩, hout⟩, hl7⟩ := hok
  rw [hparams] at hpar
  subst hpar
  rw [agg_shape, holdsList_append] at hb
  obtain ⟨hall, hret⟩ := holdsList_flat aggP hflat _ _ hb
  have hr : rets = [] := by
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at hret
    exact hret.symm
  subst hr
  have hat := atoms_of_flat hall
  simp only [List.map_cons, List.map_nil, MeaningAggregateClaimsW]
  intro hW m hm1 hm16 hN
  refine ⟨trivial, ?_⟩
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hseed hz3 hrate hpt1 hout
  -- the absorbing loop
  have L25 : ∀ c < m, L25Step rd (σ (.n (val% «aggregate_claims» "absorb"))) (σ (.n (val% «aggregate_claims» "child_fresh"))) (σ (.n (val% «aggregate_claims» "fresh_row"))) (σ (.n (val% «aggregate_claims» "child_carried"))) (σ (.n (val% «aggregate_claims» "carried_row")))
      (σ (.n (val% «aggregate_claims» "child_pi"))) (gen ^ c) :=
    loop_sound (f := name% «aggregate_claims_loop0»)
      (ps := [σ (.n (val% «aggregate_claims» "n_children_g")), σ (.n (val% «aggregate_claims» "absorb")), σ (.n (val% «aggregate_claims» "child_fresh")), σ (.n (val% «aggregate_claims» "fresh_row")), σ (.n (val% «aggregate_claims» "child_carried")), σ (.n (val% «aggregate_claims» "carried_row")), σ (.n (val% «aggregate_claims» "child_pi"))])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l25_step hy
        exact ⟨h1 _ _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg33 hall hne)
  -- the sumcheck
  have hbsm := (batch_sumcheck_holds rd _ _).mp (call_of_flat hall hbs)
  simp only [List.map_cons, List.map_nil, MeaningBatchSumcheck] at hbsm
  obtain ⟨rounds, hrl, hrd, hpt, hrets⟩ := hbsm
  rw [genMul_sound hg109 hat] at hrd
  have hrnd : rounds = aggRounds rd σ := rounds_of_reads hrl hrd
  obtain ⟨brun, hrun_def⟩ : ∃ r, r = bsRun rounds (σ (.n (val% «aggregate_claims» "bc_running@1")))
      ⟨[σ (.n (val% «aggregate_claims» "nxt[8]@8")), σ (.n (val% «aggregate_claims» "nxt[9]@8")),
        σ (.n (val% «aggregate_claims» "nxt[10]@8")), σ (.n (val% «aggregate_claims» "nxt[11]@8")),
        σ (.n (val% «aggregate_claims» "nxt[12]@8"))], []⟩ := ⟨_, rfl⟩
  have h115 : σ (.n (val% «aggregate_claims» "bc_running@2")) = brun.1.2 := by
    have := congrArg List.getLast? hrets
    rw [hrun_def]
    simpa using this
  have hptl : brun.1.1.length = 25 := by rw [hrun_def, bsRun_len, hrl]
  have hpt' : ReadsAt rd (σ (.n (val% «aggregate_claims» "bc_point"))) brun.1.1 := by
    rw [hrun_def]; exact hpt
  refine ⟨⟨brun.1.1, σ (.n (val% «aggregate_claims» "bytecode_star"))⟩, hptl, ?_, ?_⟩
  · -- the claim written
    intro k hk
    simp only [DeferredBytecodeClaim.cells, List.length_append, List.length_cons, List.length_nil,
      hptl] at hk
    by_cases hk25 : k < 25
    · rw [show (DeferredBytecodeClaim.cells ⟨brun.1.1, σ (.n (val% «aggregate_claims» "bytecode_star"))⟩)[k] = _ from
        List.getElem_append_left (by rw [hptl]; exact hk25)]
      obtain ⟨h1, h2⟩ := hout k hk25
      have e := loadHolds_unique (load_sound h1 hat) (hpt' k (by rw [hptl]; exact hk25))
      rw [← e]
      exact load_sound h2 hat
    · have hk' : k = 25 := by omega
      subst hk'
      rw [show (DeferredBytecodeClaim.cells ⟨brun.1.1, σ (.n (val% «aggregate_claims» "bytecode_star"))⟩)[25] =
          σ (.n (val% «aggregate_claims» "bytecode_star")) by
          simp only [DeferredBytecodeClaim.cells]
          rw [List.getElem_append_right (by rw [hptl])]
          simp [hptl]]
      exact load_sound hl7 hat
  -- the batching
  intro cs hcl hcw bytecode hbv
  -- row 0
  have hcap0 : rowCap rd (σ (.n (val% «aggregate_claims» "absorb"))) = capOf batchSeed := by
    refine list_eq_of_getD (n := 5) (by simp [rowCap]) (by simp [capOf]) fun i hi => ?_
    obtain ⟨hcst, hld⟩ := hseed i hi
    rw [← seed_cells i hi, ← const_sound hcst hat, ← memAt_of_load (load_sound hld hat)]
    simp [rowCap, List.getD_eq_getElem?_getD, hi]
  have hrow0 : RowRel rd (σ (.n (val% «aggregate_claims» "absorb"))) (aggS0.absorbAll (Batch.childCountCells m) dsObserve) := by
    rw [absorb_head, ← hcap0]
    refine rowRel_full (by simp) fun j hj => ?_
    obtain ⟨r1, r2⟩ := hrate j hj
    rw [memAt_of_load (load_sound r1 hat), memAt_of_load (load_sound r2 hat)]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · have := packOf_of (packIn_sound hp0 hat)
      rw [hN] at this
      exact this
    · obtain ⟨hc, hp⟩ := hz3 0 (by omega)
      have hv : σ (.n (17 + 2 * 0)) = 0 := by rw [const_sound hc hat, word_zero]
      have := packOf_of (packIn_sound hp hat)
      rw [show ([gen ^ m, 0, 0, 0] : List E).getD 1 0 = σ (.n (17 + 2 * 0)) from hv.symm]
      exact this
    · obtain ⟨hc, hp⟩ := hz3 1 (by omega)
      have hv : σ (.n (17 + 2 * 1)) = 0 := by rw [const_sound hc hat, word_zero]
      have := packOf_of (packIn_sound hp hat)
      rw [show ([gen ^ m, 0, 0, 0] : List E).getD 2 0 = σ (.n (17 + 2 * 1)) from hv.symm]
      exact this
    · obtain ⟨hc, hp⟩ := hz3 2 (by omega)
      have hv : σ (.n (17 + 2 * 2)) = 0 := by rw [const_sound hc hat, word_zero]
      have := packOf_of (packIn_sound hp hat)
      rw [show ([gen ^ m, 0, 0, 0] : List E).getD 3 0 = σ (.n (17 + 2 * 2)) from hv.symm]
      exact this
  have hpend0 : (aggS0.absorbAll (Batch.childCountCells m) dsObserve).pend.length = 4 := by
    rw [absorb_head]; rfl
  -- the absorbing rows
  obtain ⟨hrowm, hpendm⟩ := absorb_rows hcl hcw L25 hrow0 hpend0 m le_rfl
  rw [List.take_of_length_le (by omega), show Batch.childCountCells m ++ cs.flatMap Batch.childCells =
    Batch.cellsBeforeChallenge cs by rw [Batch.cellsBeforeChallenge, hcl]] at hrowm hpendm
  have hrow42 : RowRel rd (σ (.n (val% «aggregate_claims» "absorbed"))) (aggAbs cs) := by
    rw [monoIs_sound hm42 hat, hN]
    exact hrowm
  -- the last row's permutation
  have hin := rowIn_sound hrin hat
  have hout1 := DupSpec.keccak_facts (keccak_sound hk hat)
  rw [hin, ← rowRel_perm hrow42] at hout1
  have o : ∀ c (hc : c < 13), σ (.n (57 + c)) = cellsOfState (aggAbs cs).perm false ⟨c, hc⟩ :=
    fun c hc => by
      have := hout1 c hc
      rwa [show aggKo.getD c default = .n (57 + c) by
        simp [aggKo, List.getD_eq_getElem?_getD, hc]] at this
  -- the nonce's permutation
  have hnh := allIn_holds hnA hat C (fun _ => True)
  rw [aggNonceA_eq, holdsList_append, holds_fsNonceT, holds_padRunT] at hnh
  obtain ⟨⟨hl73, hpk⟩, ⟨-, h77, h78, h79, h80⟩, -⟩ := hnh
  obtain ⟨h74, h75⟩ := hpk
  have h73 : σ (.n (val% «aggregate_claims» "s16.e.s1#0")) = (aggHints rd σ).lambdaGrindNonce := (memAt_of_load hl73).symm
  have hnin : aggNi.map σ = [σ (.n (val% «aggregate_claims» "s16.e.s1#0")), word 0 dsPowNonce, 0, 0, 0, 0, 0, 0] ++
      capOf (aggAbs cs).perm := by
    simp only [aggNi, permIns, List.take, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, h74, h75, h77, h78, h79, h80, capOf, o 8 (by omega), o 9 (by omega),
      o 10 (by omega), o 11 (by omega), o 12 (by omega)]
    rfl
  have hnout := DupSpec.keccak_facts (keccak_sound hkn hat)
  rw [hnin, ← nonce_ins (s := aggAbs cs) hpendm, h73] at hnout
  have q : ∀ c (hc : c < 13), σ (.n (78 + c)) =
      cellsOfState (aggN cs (aggHints rd σ).lambdaGrindNonce) false ⟨c, hc⟩ :=
    fun c hc => by
      have := hnout c hc
      rwa [show aggNo.getD c default = .n (78 + c) by
        simp [aggNo, List.getD_eq_getElem?_getD, hc]] at this
  -- the proof of work and `λ`
  have hpow : ((σ (.n (val% «aggregate_claims» "nxt[1]@2"))).limb 0).lane.toNat % 2 ^ 3 = 0 := by
    have hgh := allIn_holds hgr hat (fun _ _ _ => True) (fun _ => True)
    rw [aggGrindA_eq] at hgh
    obtain ⟨κ, -, hκ, L, rfl⟩ := hm
    exact (gcInline_sound hκ (le_trans (by decide) (winTabBits_le_of_winTabs hκ L hW)) L (by decide)
      hW hgh).1
  have q1 : σ (.n (val% «aggregate_claims» "nxt[1]@2")) = cellsOfState (aggN cs (aggHints rd σ).lambdaGrindNonce) false 1 :=
    q 1 (by omega)
  have hpowOk : powOk Batch.batchLambdaGrindBits
      (Keccak.lane (aggN cs (aggHints rd σ).lambdaGrindNonce) 2) = true := by
    have := (grindOk_iff (s := aggAbs cs) (bits := 3) (by omega)
      (aggHints rd σ).lambdaGrindNonce).mpr (by rw [← aggN, ← q1]; exact hpow)
    exact this.resolve_left (by omega)
  have hlam : σ (.n (val% «aggregate_claims» "nxt[0]@2")) = challengeOf (aggN cs (aggHints rd σ).lambdaGrindNonce) := by
    rw [q 0 (by omega), Keccak.challengeOf_cells]
    rfl
  -- the column challenges
  have hz : aggZs.map σ = List.replicate 8 0 := by
    simp only [aggZs, List.map_cons, List.map_nil, h77, h78, h79, h80]
    rfl
  have hc0 : aggCap0.map σ = (⟨capOf (aggN cs (aggHints rd σ).lambdaGrindNonce), []⟩ : Fs).cap := by
    simp only [aggCap0, capOf, List.map_map, Function.comp_def]
    rw [show (List.range 5).map (fun i => σ (.n ((val% «aggregate_claims» "nxt[0]@2") + 8 + i))) =
      [σ (.n (78 + 8)), σ (.n (78 + 9)), σ (.n (78 + 10)), σ (.n (78 + 11)), σ (.n (78 + 12))] from rfl,
      q 8 (by omega), q 9 (by omega), q 10 (by omega), q 11 (by omega), q 12 (by omega)]
    rfl
  obtain ⟨hcolv, hcap6⟩ := sqChain_sound hsq hat hz rfl hc0
  obtain ⟨cols, hcols⟩ : ∃ c, c = (aggCols cs (aggHints rd σ).lambdaGrindNonce).1 := ⟨_, rfl⟩
  have hcl6 : cols.length = splitLog := by rw [hcols, aggCols, length_squeezeN]
  have hcolk : ∀ k < splitLog, memAt rd (σ (.n (val% «aggregate_claims» "col"))) k = cols.getD k 0 := by
    intro k hk
    rw [hcolv k hk, hcols, aggCols, squeezeN_getD _ _ _ hk]
  have hcaps : (aggCols cs (aggHints rd σ).lambdaGrindNonce).2 =
      ⟨[σ (.n (val% «aggregate_claims» "nxt[8]@8")), σ (.n (val% «aggregate_claims» "nxt[9]@8")),
        σ (.n (val% «aggregate_claims» "nxt[10]@8")), σ (.n (val% «aggregate_claims» "nxt[11]@8")),
        σ (.n (val% «aggregate_claims» "nxt[12]@8"))], []⟩ := by
    rw [aggCols, squeezeN_snd]
    have e := hcap6 (by decide)
    have hp := sqIter_pend splitLog (⟨capOf (aggN cs (aggHints rd σ).lambdaGrindNonce), []⟩ : Fs) rfl
    revert e hp
    generalize sqIter splitLog _ = S
    intro e hp
    obtain ⟨cc, pp⟩ := S
    simp only at hp e ⊢
    subst hp
    rw [← e]
    rfl
  -- the equality table
  have hlev : eqLevels (memAt rd (σ (.n (val% «aggregate_claims» "col")))) 5 = eqKernel cols := by
    rw [show eqLevels (memAt rd (σ (.n (val% «aggregate_claims» "col")))) 5 =
      eqLevels (fun k => cols.getD k 0) 5 from eqLevels_congr fun k hk => hcolk k
        (lt_of_le_of_lt hk (by decide)), eqLevels_eqKernel cols 5 (by rw [hcl6]; decide),
      List.take_of_length_le (by rw [hcl6]; decide)]
  have heqt : ∀ j < 64, memAt rd (σ (.n (val% «aggregate_claims» "s26#4"))) j = (eqKernel cols).getD j 0 := by
    intro j hj
    have := tree_sound htree hat 5 (by decide) j hj
    rw [hlev, show 2 ^ (5 + 1) - 2 + j = 62 + j by norm_num] at this
    rw [isMul_sound hm62 hat, const_sound hc62 hat, word_g62]
    exact memAt_of_load ((loadHolds_mul_gen_pow rd _ 62 j _).mpr this)
  -- the fresh claims' folded values
  have A1 : ∀ c < m, A1Step rd (σ (.n (val% «aggregate_claims» "fresh_row"))) (σ (.n (val% «aggregate_claims» "s26#4"))) (σ (.n (val% «aggregate_claims» "fresh_val"))) (gen ^ c) :=
    loop_sound (f := name% «aggregate_claims_loop1»)
      (ps := [σ (.n (val% «aggregate_claims» "n_children_g")), σ (.n (val% «aggregate_claims» "fresh_row")), σ (.n (val% «aggregate_claims» "s26#4")), σ (.n (val% «aggregate_claims» "fresh_val"))])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := a1_step hy
        exact ⟨h1 _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg1 hall hne)
  have hfv : ∀ c (hc : c < cs.length), memAt rd (σ (.n (val% «aggregate_claims» "fresh_val")) * gen ^ c) 0 =
      Batch.foldColumns cols cs[c].freshClaim.values := by
    intro c hc
    rw [memAt_of_load (A1 c (by omega))]
    obtain ⟨hfp, -⟩ := L25 c (by omega)
    rw [memAt_of_load hfp]
    obtain ⟨⟨-, hvl⟩, -⟩ := hcw c hc
    obtain ⟨hvals, -⟩ := kid_words (hcw c hc)
    exact fvAcc_eq_foldColumns hcl6 hvl (fun j hj => heqt j (lt_of_lt_of_le hj (by decide))) hvals
  -- the records
  have A2 : ∀ c < m, A2Step rd (σ (.n (val% «aggregate_claims» "bc_chain"))) (σ (.n (val% «aggregate_claims» "carried_row")))
      (σ (.n (val% «aggregate_claims» "nxt[0]@2")) * σ (.n (val% «aggregate_claims» "nxt[0]@2")))
      (σ (.n (val% «aggregate_claims» "fresh_val"))) (σ (.n (val% «aggregate_claims» "nxt[0]@2"))) (gen ^ c) := by
    have h := loop_sound (f := name% «aggregate_claims_loop2»)
      (ps := [σ (.n (val% «aggregate_claims» "n_children_g")), σ (.n (val% «aggregate_claims» "bc_chain")), σ (.n (val% «aggregate_claims» "fresh_row")), σ (.n (val% «aggregate_claims» "carried_row")), σ (.n (val% «aggregate_claims» "lam_sq")), σ (.n (val% «aggregate_claims» "fresh_val")), σ (.n (val% «aggregate_claims» "nxt[0]@2"))])
      (B := fun x => A2Step rd (σ (.n (val% «aggregate_claims» "bc_chain"))) (σ (.n (val% «aggregate_claims» "carried_row"))) (σ (.n (val% «aggregate_claims» "lam_sq"))) (σ (.n (val% «aggregate_claims» "fresh_val"))) (σ (.n (val% «aggregate_claims» "nxt[0]@2"))) x)
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := a2_step hy
        exact ⟨h1 _ _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg2 hall hne)
    rwa [isMul_sound hm94 hat] at h
  have hcv : ∀ c (hc : c < cs.length), memAt rd (memAt rd (σ (.n (val% «aggregate_claims» "carried_row")) * gen ^ c) 0) 25 =
      cs[c].carriedClaim.bytecodeValue := by
    intro c hc
    obtain ⟨-, hcp, -⟩ := L25 c (by omega)
    rw [memAt_of_load hcp]
    exact (kid_words (hcw c hc)).2.1
  have h98 : memAt rd (σ (.n (val% «aggregate_claims» "bc_chain"))) 0 = 1 := by
    rw [memAt_of_load (load_sound hl99 hat), const_sound hc99 hat, word_one]
  have h98z : memAt rd (σ (.n (val% «aggregate_claims» "bc_chain"))) 1 = 0 := by
    rw [memAt_of_load (load_sound hl100 hat), const_sound hc100 hat, word_zero]
  have CH := chain_rows (cols := cols) hcl A2 hfv hcv h98 h98z
  have p105 : σ (.n (val% «aggregate_claims» "bc_end")) = σ (.n (val% «aggregate_claims» "bc_chain")) * (gen ^ m) ^ 2 := by
    rw [monoIs_sound hm105 hat, hN]
  have hagg : aggLam cs (aggHints rd σ).lambdaGrindNonce = Batch.lambdaPowers (σ (.n (val% «aggregate_claims» "nxt[0]@2"))) m := by
    simp only [aggLam, hcl, hlam]
  have hclaim : Batch.batchedClaim cs (aggLam cs (aggHints rd σ).lambdaGrindNonce) cols =
      σ (.n (val% «aggregate_claims» "bc_running@1")) := by
    obtain ⟨-, hacc⟩ := CH m le_rfl
    rw [List.take_of_length_le (by omega)] at hacc
    rw [hagg, ← memAt_of_load (load_sound hl106 hat), p105, hacc]
    rfl
  have hrun : aggRun cs (aggHints rd σ) = brun := by
    rw [aggRun, ← hcols, hclaim, hcaps, hrun_def, hrnd]
    rfl
  -- the point
  have hpt1' : ∀ k < 25, memAt rd (σ (.n (val% «aggregate_claims» "bc_point1"))) k = 1 + memAt rd (σ (.n (val% «aggregate_claims» "bc_point"))) k := by
    intro k hk
    obtain ⟨⟨⟨c1, l1⟩, a1⟩, s1'⟩ := hpt1 k hk
    rw [memAt_of_load (load_sound s1' hat), add_sound a1 hat, const_sound c1 hat, word_one,
      memAt_of_load (load_sound l1 hat)]
  have hrpt : memRun rd (σ (.n (val% «aggregate_claims» "bc_point"))) 25 = brun.1.1 := by
    have := readsAt_memRun hpt'
    rw [hptl] at this
    exact this.symm
  have hpt25 : (memRun rd (σ (.n (val% «aggregate_claims» "bc_point1"))) 25).map (1 + ·) = brun.1.1 := by
    rw [← hrpt]; exact map_one_add_memRun hpt1'
  have hpt19 : (memRun rd (σ (.n (val% «aggregate_claims» "bc_point1"))) 19).map (1 + ·) = brun.1.1.take 19 := by
    rw [← hrpt, map_one_add_memRun (n := 19) (fun k hk => hpt1' k (by omega))]
    exact List.ext_getElem (by simp) fun k h1 h2 => by simp [memRun]
  -- the column factor
  have hdrop : brun.1.1.drop 19 = (List.range 6).map fun j =>
      memAt rd (σ (.n (val% «aggregate_claims» "bc_point"))) (19 + j) := by
    rw [← hrpt]
    refine List.ext_getElem (by simp) fun k h1 h2 => ?_
    simp [memRun]
  have heqcols : σ (.n (val% «aggregate_claims» "eq_cols@6")) = eqEval cols (brun.1.1.drop 19) := by
    have e1 : memRun rd (σ (.n (val% «aggregate_claims» "col"))) 6 = cols := by
      refine List.ext_getElem (by simp [hcl6, splitLog]) fun k h1 h2 => ?_
      simp only [memRun, List.getElem_map, List.getElem_range]
      simp only [length_memRun] at h1
      rw [hcolk k (by unfold splitLog; omega), List.getD_eq_getElem _ _ h2]
    have e2 : ((List.range 6).map fun j =>
        1 + memAt rd (σ (.n (val% «aggregate_claims» "bc_point1"))) (19 + j)) =
        (List.range 6).map fun j => memAt rd (σ (.n (val% «aggregate_claims» "bc_point"))) (19 + j) := by
      refine List.map_congr_left fun j hj => ?_
      rw [hpt1' (19 + j) (by simp at hj; omega), ← add_assoc, e_add_self, zero_add]
    rw [eqcChain_sound heqc hat, hdrop, e1, e2]
  -- the weights
  have A3 : ∀ c < m, A3Step rd (σ (.n (val% «aggregate_claims» "fresh_row"))) (σ (.n (val% «aggregate_claims» "carried_row"))) (σ (.n (val% «aggregate_claims» "bc_point1"))) (σ (.n (val% «aggregate_claims» "bc_chain"))) (σ (.n (val% «aggregate_claims» "bc_wsum")))
      (σ (.n (val% «aggregate_claims» "eq_cols@6"))) (σ (.n (val% «aggregate_claims» "nxt[0]@2"))) (gen ^ c) :=
    loop_sound (f := name% «aggregate_claims_loop3»)
      (ps := [σ (.n (val% «aggregate_claims» "n_children_g")), σ (.n (val% «aggregate_claims» "fresh_row")), σ (.n (val% «aggregate_claims» "carried_row")), σ (.n (val% «aggregate_claims» "bc_point1")), σ (.n (val% «aggregate_claims» "bc_chain")), σ (.n (val% «aggregate_claims» "bc_wsum")), σ (.n (val% «aggregate_claims» "eq_cols@6")), σ (.n (val% «aggregate_claims» "nxt[0]@2"))])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := a3_step hy
        exact ⟨h1 _ _ _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg3 hall hne)
  have hfp : ∀ c (hc : c < cs.length), memRun rd (memAt rd (σ (.n (val% «aggregate_claims» "fresh_row")) * gen ^ c) 0) 19 =
      cs[c].freshClaim.point := by
    intro c hc
    obtain ⟨hfp, -⟩ := L25 c (by omega)
    rw [memAt_of_load hfp]
    exact (kid_words (hcw c hc)).2.2.1
  have hcp : ∀ c (hc : c < cs.length), memRun rd (memAt rd (σ (.n (val% «aggregate_claims» "carried_row")) * gen ^ c) 0) 25 =
      cs[c].carriedClaim.bytecodePoint := by
    intro c hc
    obtain ⟨-, hcp, -⟩ := L25 c (by omega)
    rw [memAt_of_load hcp]
    exact (kid_words (hcw c hc)).2.2.2.1
  have hz189 : memAt rd (σ (.n (val% «aggregate_claims» "bc_wsum"))) 0 = 0 := by
    rw [memAt_of_load (load_sound hl189 hat), const_sound hc189 hat, word_zero]
  have W := weight_rows hcl A3 (fun c hc => (CH c hc.le).1) hfp hcp hpt19 hpt25 hz189 m le_rfl
  rw [List.take_of_length_le (l := cs) (by omega)] at W
  have hw : Batch.batchedBytecodeWeight cs (aggLam cs (aggHints rd σ).lambdaGrindNonce) cols brun.1.1 =
      σ (.n (val% «aggregate_claims» "s41#1")) := by
    rw [hagg, ← memAt_of_load (load_sound hl194 hat), isMul_sound hm193 hat, hN, W, heqcols]
    unfold Batch.batchedBytecodeWeight
    refine congrArg sumE (zipWith_congr_mem _ _ fun c hc l => ?_)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    obtain ⟨⟨hfl, -⟩, -⟩ := hcw i hi
    rw [eqEval_fresh hfl (by rw [hptl]; omega)]
  -- the batching program accepts
  have hrl' : (aggHints rd σ).sumcheckMessages.length = deferredVariableCount bytecode := by
    rw [hbv]
    show (aggRounds rd σ).length = bytecodeVars
    rw [aggRounds, List.length_map, List.length_range]
  have hfinv : (aggHints rd σ).finalBytecodeValue = σ (.n (val% «aggregate_claims» "bytecode_star")) := rfl
  have hfin : (aggRun cs (aggHints rd σ)).1.2 = (aggHints rd σ).finalBytecodeValue *
      Batch.batchedBytecodeWeight cs (aggLam cs (aggHints rd σ).lambdaGrindNonce)
        (aggCols cs (aggHints rd σ).lambdaGrindNonce).1 (aggRun cs (aggHints rd σ)).1.1 := by
    rw [hrun, ← hcols, hfinv, hw, ← h115, assertEq_sound hae hat, isMul_sound hm195 hat]
  have key := runBatching_of_carried hpowOk hrl' hfin
  rw [hrun, hfinv] at key
  exact key

end
end LeanVM.Guest.B1.Main
