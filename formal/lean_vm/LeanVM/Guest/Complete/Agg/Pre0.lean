module

public import LeanVM.Guest.Complete.Agg.Regs
public import LeanVM.Guest.Complete.DaPadA
public import LeanVM.Guest.Complete.DaOffA
public import LeanVM.Protocol.Relation.Link.Steps

/-!
# `aggregate_claims_loop0`'s precondition at the honest data

On a memory holding `main`'s words and the own words, each child's words are defined
(`childWords`: `ChildWordsAt` from `mainWords`' runs `5`, `6`, `7`), so the absorbing rows are
`absSt_rows`'; `absorb` holds them (`aRows`), the pointer tables point at the claims: `agg_pre0`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC
open LeanVM.Guest.Complete LeanVM.Guest.B1.Digest
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

/-- **A load from a held run**, at the run's base plus `i`, offset `o`. -/
theorem load_at {rd : Reader} {W : Words} (h : HoldsWords rd W) {b : ℕ} {xs : List E} (hq : (b, xs) ∈ W)
    {p : E} {i o : ℕ} (hp : p = ptrAt (b + i)) (hi : i + o < xs.length) {v : E} (hv : xs.getD (i + o) 0 = v) :
    LoadHolds rd p o v := by
  subst hp hv
  refine loadHolds_of_rd ?_
  rw [Nat.add_assoc]
  exact holds_run h hq hi

theorem ptr_pow (b n j : ℕ) : ptrAt b * (gen ^ j) ^ n = ptrAt (b + n * j) := by
  rw [← pow_mul, ptrAt_mul_gen_pow, Nat.mul_comm j n]

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

theorem mem_main5 : (mBase (mainCounts s w) 5,
    w.children.flatMap fun ch => Prover.digestCells (statementDigest guestSeed ch.statement)) ∈ mainWords s w cover := by
  simp [mainWords]

theorem mem_main6 : (mBase (mainCounts s w) 6, w.children.flatMap (·.freshClaim.cells)) ∈ mainWords s w cover := by
  simp [mainWords]

theorem mem_main7 : (mBase (mainCounts s w) 7, w.children.flatMap (·.statement.deferredClaim.cells)) ∈
    mainWords s w cover := by
  simp [mainWords]

theorem aCs_getElem {j : ℕ} (hj : j < (aCs w).length) :
    (aCs w)[j] = ⟨statementDigest guestSeed (w.children[j]'(by rwa [aCs_length] at hj)).statement,
      (w.children[j]'(by rwa [aCs_length] at hj)).freshClaim,
      (w.children[j]'(by rwa [aCs_length] at hj)).statement.deferredClaim⟩ := by
  simp [aCs]

/-- **Each child's words, from `main`'s.** -/
theorem childWords {rd : Reader} (hM : HoldsWords rd (mainWords s w cover)) (cc : ClaimCells s w)
    (hfp : ∀ ch ∈ w.children, ch.freshClaim.point.length = 19) :
    ∀ j (hj : j < (aCs w).length), ChildWordsAt rd (ptrAt (mBase (mainCounts s w) 5 + 0))
      (ptrAt (mBase (mainCounts s w) 6 + 0)) (ptrAt (mBase (mainCounts s w) 7 + 0)) j (aCs w)[j] := by
  intro j hj
  have hj' : j < w.children.length := by rwa [aCs_length] at hj
  rw [aCs_getElem hj]
  have hmem : w.children[j] ∈ w.children := List.getElem_mem _
  have hf := cc.fresh _ hmem
  have hc := cc.carried _ hmem
  have hp := hfp _ hmem
  have hfl : (w.children.flatMap (·.freshClaim.cells)).length = 55 * w.children.length :=
    flatMap_length_const cc.fresh
  have hcl : (w.children.flatMap (·.statement.deferredClaim.cells)).length = 26 * w.children.length :=
    flatMap_length_const cc.carried
  have hdl : (w.children.flatMap fun ch => Prover.digestCells (statementDigest guestSeed ch.statement)).length =
      2 * w.children.length := flatMap_length_const fun _ _ => rfl
  simp only [FreshClaim.cells, List.length_append] at hf
  simp only [DeferredBytecodeClaim.cells, List.length_append, List.length_singleton] at hc
  refine ⟨⟨by rw [hp], by show (w.children[j]).freshClaim.values.length = 36; omega⟩,
    by show (w.children[j]).statement.deferredClaim.bytecodePoint.length = 25; omega, ?_, ?_, ?_, ?_⟩
  · refine load_at hM mem_main5 (i := 0) rfl (by omega) ?_
    rw [Nat.zero_add, show 2 * j = j * 2 + 0 by omega,
      LeanVM.Protocol.Relation.getD_flatMap_uniform _ 2 0 w.children (fun _ _ => rfl) j 0 hj' (by norm_num)]
    rfl
  · refine load_at hM mem_main5 (i := 0) rfl (by omega) ?_
    rw [Nat.zero_add, show 2 * j + 1 = j * 2 + 1 by omega,
      LeanVM.Protocol.Relation.getD_flatMap_uniform _ 2 0 w.children (fun _ _ => rfl) j 1 hj' (by norm_num)]
    rfl
  · intro k hk
    have hk' : k < 55 := by simp only [FreshClaim.cells, List.length_append] at hk; omega
    refine load_at hM mem_main6 (i := 55 * j) (by rw [ptrAt_mul_gen_pow, Nat.add_zero]) (by omega) ?_
    rw [show 55 * j + k = j * 55 + k by omega,
      LeanVM.Protocol.Relation.getD_flatMap_uniform _ 55 0 w.children cc.fresh j k hj' hk']
    exact List.getD_eq_getElem _ _ _
  · intro k hk
    have hk' : k < 26 := by
      simp only [DeferredBytecodeClaim.cells, List.length_append, List.length_singleton] at hk; omega
    refine load_at hM mem_main7 (i := 26 * j) (by rw [ptrAt_mul_gen_pow, Nat.add_zero]) (by omega) ?_
    rw [show 26 * j + k = j * 26 + k by omega,
      LeanVM.Protocol.Relation.getD_flatMap_uniform _ 26 0 w.children cc.carried j k hj' hk']
    exact List.getD_eq_getElem _ _ _

/-- **`absorb`'s rows**: row `i ≤ m` is `rowW (absSt m cs i)`. -/
theorem aRows {rd : Reader} (hl : (aLists s w).map List.length = aBufs w.children.length)
    (hO : HoldsWords rd (aWo s w c)) {i : ℕ} (hi : i ≤ w.children.length) :
    ReadsAt rd (ptrAt (aB c w.children.length 3 + 13 * i)) (rowW (absSt w.children.length (aCs w) i)) := by
  obtain ⟨hq, hlen⟩ := aWo_get (c := c) hl (j := 3) (by norm_num)
  have hg : ∀ i, (rowW (absSt w.children.length (aCs w) i)).length = 13 := fun i => rowW_length (absSt_ok _ _ i)
  have e3 : (aLists s w).getD 3 [] = (List.range (w.children.length + 1)).flatMap
      (fun j => rowW (absSt w.children.length (aCs w) j)) := rfl
  intro k hk
  rw [hg] at hk
  refine load_at hO hq rfl (by rw [hlen]; simp [aBufs]; omega) ?_
  rw [e3, getD_flatMap_range _ hg _ _ _ (by omega) hk]
  exact List.getD_eq_getElem _ _ _

/-- `fresh_row`'s cell `j`: the child's fresh claim. -/
theorem aTab1 {rd : Reader} (hl : (aLists s w).map List.length = aBufs w.children.length)
    (hO : HoldsWords rd (aWo s w c)) {j : ℕ} (hj : j < w.children.length) :
    LoadHolds rd (ptrAt (aB c w.children.length 1) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) := by
  obtain ⟨hq, hlen⟩ := aWo_get (c := c) hl (j := 1) (by norm_num)
  refine load_at hO hq (by rw [ptrAt_mul_gen_pow]) (by rw [hlen]; simp [aBufs]; omega) ?_
  simp [aLists, hj]

/-- `carried_row`'s cell `j`: the child's carried claim. -/
theorem aTab2 {rd : Reader} (hl : (aLists s w).map List.length = aBufs w.children.length)
    (hO : HoldsWords rd (aWo s w c)) {j : ℕ} (hj : j < w.children.length) :
    LoadHolds rd (ptrAt (aB c w.children.length 2) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) := by
  obtain ⟨hq, hlen⟩ := aWo_get (c := c) hl (j := 2) (by norm_num)
  refine load_at hO hq (by rw [ptrAt_mul_gen_pow]) (by rw [hlen]; simp [aBufs]; omega) ?_
  simp [aLists, hj]

/-- **`aggregate_claims_loop0`'s precondition** at the honest data. -/
theorem agg_pre0 (hr : NodeRelation guestBytecode guestSeed s w) (hok : ChildrenOk guestBytecode guestSeed w)
    (hne : w.children ≠ []) :
    ∀ rd, APre al s w cover c rd → ∀ j < w.children.length,
      A0PreA (absSt w.children.length (aCs w)) (aB c w.children.length 3) (mBase (mainCounts s w) 5 + 0)
        (mBase (mainCounts s w) 6 + 0) (aB c w.children.length 1) (mBase (mainCounts s w) 7 + 0)
        (aB c w.children.length 2) rd j := by
  intro rd hA j hj
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have cc := claimCells_of hr hok
  have hM := hA.1.1
  have hO := hA.2
  have hcw := childWords (cover := cover) hM cc (fresh_len hok)
  obtain ⟨⟨hst, hp4⟩, hsucc⟩ := absSt_rows (rd := rd) (aCs_length w) hcw j hj
  have hfl : (w.children.flatMap (·.freshClaim.cells)).length = 55 * w.children.length :=
    flatMap_length_const cc.fresh
  have hcl : (w.children.flatMap (·.statement.deferredClaim.cells)).length = 26 * w.children.length :=
    flatMap_length_const cc.carried
  have hdl : (w.children.flatMap fun ch => Prover.digestCells (statementDigest guestSeed ch.statement)).length =
      2 * w.children.length := flatMap_length_const fun _ _ => rfl
  refine ⟨hst, hp4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ptr_pow]; exact aRows hl hO (by omega)
  · rw [ptr_pow, ptrAt_mul_gen_pow, ← hsucc, Nat.add_assoc, show 13 * j + 13 = 13 * (j + 1) by ring]
    exact aRows hl hO (by omega)
  · rw [ptr_pow, Nat.add_zero]; exact aTab1 hl hO hj
  · rw [ptr_pow, Nat.add_zero]; exact aTab2 hl hO hj
  · intro o ho
    exact ⟨_, load_at hM mem_main5 (i := 2 * j) (by rw [ptr_pow, Nat.add_zero]) (by omega) rfl⟩
  · intro o ho
    exact ⟨_, load_at hM mem_main6 (i := 55 * j) (by rw [ptr_pow, Nat.add_zero]) (by omega) rfl⟩
  · intro o ho
    exact ⟨_, load_at hM mem_main7 (i := 26 * j) (by rw [ptr_pow, Nat.add_zero]) (by omega) rfl⟩

/-- **`aggregate_claims_loop1`'s precondition** at the honest data: `fresh_val[j]` is the child's
fresh values folded by `eq_col` (`fvAcc_eq_foldColumns`). -/
theorem agg_pre1 (hr : NodeRelation guestBytecode guestSeed s w) (hok : ChildrenOk guestBytecode guestSeed w)
    (hne : w.children ≠ []) :
    ∀ rd, APre al s w cover c rd → ∀ j < w.children.length,
      LoadHolds rd (ptrAt (aB c w.children.length 1) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) ∧
      (∀ i < 36, ∃ v, LoadHolds rd (ptrAt (aB c w.children.length 5 + 62)) i v) ∧
      (∀ i < 36, ∃ v, LoadHolds rd (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) (19 + i) v) ∧
      LoadHolds rd (ptrAt (aB c w.children.length 6) * gen ^ j) 0
        (fvAcc rd (ptrAt (aB c w.children.length 5 + 62)) (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) 36) := by
  intro rd hA j hj
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have cc := claimCells_of hr hok
  have hM := hA.1.1
  have hO := hA.2
  have hmem : w.children[j] ∈ w.children := List.getElem_mem _
  have hpl := fresh_len hok _ hmem
  have hfc := cc.fresh _ hmem
  simp only [FreshClaim.cells, List.length_append] at hfc
  have hfl : (w.children.flatMap (·.freshClaim.cells)).length = 55 * w.children.length :=
    flatMap_length_const cc.fresh
  have hcols : (aCols w).length = 6 := Whir.squeezeN_length splitLog _
  obtain ⟨hq5, hlen5⟩ := aWo_get (c := c) hl (j := 5) (by norm_num)
  obtain ⟨hq6, hlen6⟩ := aWo_get (c := c) hl (j := 6) (by norm_num)
  have he : ∀ i < 36, LoadHolds rd (ptrAt (aB c w.children.length 5 + 62)) i
      ((eqKernel (aCols w)).getD i 0) := fun i hi => by
    refine load_at hO hq5 rfl (by rw [hlen5]; simp [aBufs]; omega) ?_
    have e5 : (aLists s w).getD 5 [] = aTree (aCols w) := rfl
    rw [e5, show 62 + i = 2 ^ (5 + 1) - 2 + i by norm_num, aTree_lvl _ (by norm_num) (by norm_num; omega),
      eqLevels_eqKernel _ 5 (by omega), List.take_of_length_le (by omega)]
  have hf : ∀ i < 36, LoadHolds rd (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) (19 + i)
      ((w.children[j]).freshClaim.values.getD i 0) := fun i hi => by
    refine load_at hM mem_main6 rfl (by omega) ?_
    rw [show 55 * j + (19 + i) = j * 55 + (19 + i) by omega,
      LeanVM.Protocol.Relation.getD_flatMap_uniform _ 55 0 w.children cc.fresh j (19 + i) hj (by omega), FreshClaim.cells,
      List.getD_append_right _ _ _ _ (by omega), show 19 + i - w.children[j].freshClaim.point.length = i by omega]
  have hfv : fvAcc rd (ptrAt (aB c w.children.length 5 + 62)) (ptrAt (mBase (mainCounts s w) 6 + 55 * j)) 36 =
      Batch.foldColumns (aCols w) (w.children[j]).freshClaim.values :=
    fvAcc_eq_foldColumns (by rw [hcols]; rfl) (by show _ = 36; omega)
      (fun i hi => memAt_of_load (he i hi)) (fun i hi => memAt_of_load (hf i hi))
  refine ⟨aTab1 hl hO hj, fun i hi => ⟨_, he i hi⟩, fun i hi => ⟨_, hf i hi⟩, ?_⟩
  refine load_at hO hq6 (by rw [ptrAt_mul_gen_pow]) (by rw [hlen6]; simp [aBufs]; omega) ?_
  rw [hfv]
  simp [aLists, aCs, hj]

/-- `bc_chain`'s records: record `i ≤ m` is `aChain`'s. -/
theorem aChainAt {rd : Reader} (hl : (aLists s w).map List.length = aBufs w.children.length)
    (hO : HoldsWords rd (aWo s w c)) {i : ℕ} (hi : i ≤ w.children.length) :
    ReadsAt rd (ptrAt (aB c w.children.length 7 + 2 * i)) (aChain (aCs w) (aCols w) (aLam w) i) := by
  obtain ⟨hq, hlen⟩ := aWo_get (c := c) hl (j := 7) (by norm_num)
  have hg : ∀ i, (aChain (aCs w) (aCols w) (aLam w) i).length = 2 := fun _ => rfl
  have e7 : (aLists s w).getD 7 [] = (List.range (w.children.length + 1)).flatMap
      (aChain (aCs w) (aCols w) (aLam w)) := rfl
  intro k hk
  rw [hg] at hk
  refine load_at hO hq rfl (by rw [hlen]; simp [aBufs]; omega) ?_
  rw [e7, getD_flatMap_range _ hg _ _ _ (by omega) hk]
  exact List.getD_eq_getElem _ _ _

/-- `fresh_val`'s cell `j`: the child's folded fresh values. -/
theorem aFv {rd : Reader} (hl : (aLists s w).map List.length = aBufs w.children.length)
    (hO : HoldsWords rd (aWo s w c)) {j : ℕ} (hj : j < w.children.length) :
    LoadHolds rd (ptrAt (aB c w.children.length 6) * gen ^ j) 0
      (Batch.foldColumns (aCols w) (w.children[j]).freshClaim.values) := by
  obtain ⟨hq6, hlen6⟩ := aWo_get (c := c) hl (j := 6) (by norm_num)
  refine load_at hO hq6 (by rw [ptrAt_mul_gen_pow]) (by rw [hlen6]; simp [aBufs]; omega) ?_
  simp [aLists, aCs, hj]

theorem aLam78 (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ [])
    (hd : DeployedLimits s w) (hc : c < 2 ^ 62) : aV al s w cover c (.n 78) = aLam w := by
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have := w2_nonce (al := al) (cover := cover) (c := c) hl hc hd.atMostSixteenChildren 0
  rw [aLam, challengeOf_cells]
  exact this

theorem aLam155 (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ [])
    (hd : DeployedLimits s w) (hc : c < 2 ^ 62) : aV al s w cover c (.n 155) = aLam w * aLam w := by
  rw [show aV al s w cover c (.n 155) = aV al s w cover c (.n 78) * aV al s w cover c (.n 78) from
    aGood_mul (aggArgs_length _ _) (mem_sq (by simp [w2Sq])) (by norm_num) (by norm_num), aLam78 hr hne hd hc]

/-- **`aggregate_claims_loop2`'s precondition** at the honest data: `bc_chain`'s records. -/
theorem agg_pre2 (hr : NodeRelation guestBytecode guestSeed s w) (hok : ChildrenOk guestBytecode guestSeed w)
    (hne : w.children ≠ []) (hd : DeployedLimits s w) (hc : c < 2 ^ 62) :
    ∀ rd, APre al s w cover c rd → ∀ j < w.children.length, ∃ pf fv cv pw acc : E,
      ReadsAt rd (ptrAt (aB c w.children.length 7) * (gen ^ j) ^ 2) [pw, acc] ∧
      ReadsAt rd (ptrAt (aB c w.children.length 7) * (gen ^ j) ^ 2 * gen ^ 2)
        [pw * aV al s w cover c (.n 155), acc + pw * (fv + aV al s w cover c (.n 78) * cv)] ∧
      LoadHolds rd (ptrAt (aB c w.children.length 1) * gen ^ j) 0 pf ∧
      LoadHolds rd (ptrAt (aB c w.children.length 2) * gen ^ j) 0 (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) ∧
      LoadHolds rd (ptrAt (aB c w.children.length 6) * gen ^ j) 0 fv ∧
      LoadHolds rd (ptrAt (mBase (mainCounts s w) 7 + 26 * j)) 25 cv := by
  intro rd hA j hj
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have cc := claimCells_of hr hok
  have hM := hA.1.1
  have hO := hA.2
  have hmem : w.children[j] ∈ w.children := List.getElem_mem _
  have hcc := cc.carried _ hmem
  simp only [DeferredBytecodeClaim.cells, List.length_append, List.length_singleton] at hcc
  have hcl : (w.children.flatMap (·.statement.deferredClaim.cells)).length = 26 * w.children.length :=
    flatMap_length_const cc.carried
  have hj' : j < (aCs w).length := by rw [aCs_length]; exact hj
  refine ⟨_, _, (w.children[j]).statement.deferredClaim.bytecodeValue, (aLam w) ^ (2 * j),
    sumE (List.zipWith (fun ch l => l.1 * Batch.foldColumns (aCols w) ch.freshClaim.values +
      l.2 * ch.carriedClaim.bytecodeValue) ((aCs w).take j) (Batch.lambdaPowers (aLam w) j)),
    ?_, ?_, aTab1 hl hO hj, aTab2 hl hO hj, aFv hl hO hj, ?_⟩
  · rw [ptr_pow]; exact aChainAt hl hO hj.le
  · rw [ptr_pow, ptrAt_mul_gen_pow, Nat.add_assoc, show 2 * j + 2 = 2 * (j + 1) by ring, aLam155 hr hne hd hc,
      aLam78 hr hne hd hc]
    have e : aChain (aCs w) (aCols w) (aLam w) (j + 1) = [aLam w ^ (2 * j) * (aLam w * aLam w),
        sumE (List.zipWith (fun ch l => l.1 * Batch.foldColumns (aCols w) ch.freshClaim.values +
          l.2 * ch.carriedClaim.bytecodeValue) ((aCs w).take j) (Batch.lambdaPowers (aLam w) j)) +
        aLam w ^ (2 * j) * (Batch.foldColumns (aCols w) (w.children[j]).freshClaim.values +
          aLam w * (w.children[j]).statement.deferredClaim.bytecodeValue)] := by
      rw [aChain, lambdaPowers_eq, zip_prefix _ _ _ hj', ← lambdaPowers_eq, aCs_getElem hj']
      congr 1
      · ring
      · congr 1
        dsimp only
        ring
    rw [← e]
    exact aChainAt hl hO (by omega)
  · refine load_at hM mem_main7 rfl (by omega) ?_
    rw [show 26 * j + 25 = j * 26 + 25 by omega,
      LeanVM.Protocol.Relation.getD_flatMap_uniform _ 26 0 w.children cc.carried j 25 hj (by norm_num), DeferredBytecodeClaim.cells,
      List.getD_append_right _ _ _ _ (by omega), show 25 - (w.children[j]).statement.deferredClaim.bytecodePoint.length = 0 by omega]
    rfl

theorem bsRun_cap5 : ∀ (rounds : List (E × E)) (claim : E) (s : Fs), s.cap.length = 5 →
    (bsRun rounds claim s).2.cap.length = 5
  | [], _, _, h => h
  | (_, _) :: rest, _, _, _ => by
    simp only [bsRun]
    exact bsRun_cap5 rest _ _ (by simp [Fs.squeeze, capOf_length])

theorem list5 {l : List E} (h : l.length = 5) : l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0] := by
  match l, h with
  | [_, _, _, _, _], _ => rfl

/-- **The batching sumcheck's meaning** at the honest data: its rounds are `bc_sumcheck_msgs`', its
claim the last record's, its sponge the squeezes', so its run is `aggRun`. -/
theorem agg_bs (hr : NodeRelation guestBytecode guestSeed s w) (hne : w.children ≠ []) (hd : DeployedLimits s w)
    (hc : c < 2 ^ 62) :
    ∀ rd, APre al s w cover c rd →
      MeaningBatchSumcheck 25 rd ([V.n 230, .n 231, .n 232, .n 233, .n 234, .n 460, .n 457, .n 458, .n 5].map
        (aV al s w cover c)) ([V.n 461, .n 462, .n 463, .n 464, .n 465, .n 466].map (aV al s w cover c)) := by
  intro rd hA
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have hsum := aBufs_sum w.children.length
  have hn : w.children.length ≤ 16 := hd.atMostSixteenChildren
  have hO := hA.2
  have hcap := w2_cap (al := al) (cover := cover) hl hc hd.atMostSixteenChildren
  obtain ⟨p6, -, -, -, -, -, -, p449, p458, -, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  -- `bc_msgs` after the nonce
  have v460 : aV al s w cover c (.n 460) = ptrAt (aB c w.children.length 0 + 1) := by
    rw [show aV al s w cover c (.n 460) = aV al s w cover c (.n 6) * aV al s w cover c (.n 459) from
      aGood_mul (aggArgs_length _ _) (w46_mem.2.1 _ (by simp [w6A])) (by norm_num) (by norm_num), p6,
      show aV al s w cover c (.n 459) = word 2 0 from aGood_const (aggArgs_length _ _) (w46_mem.2.1 _ (by simp [w6A])),
      word_gen, ← pow_one gen, ptrAt_mul_gen_pow]
  -- the last record's claim
  obtain ⟨-, hm6, f457⟩ := w46_mem
  have v0 : aV al s w cover c (.n 0) = gen ^ w.children.length := aV_param (by norm_num)
  have g455 : aV al s w cover c (.n 455) = aV al s w cover c (.n 0) * aV al s w cover c (.n 0) :=
    aGood_mul (aggArgs_length _ _) (hm6 _ (by simp [w6A])) (by norm_num) (by norm_num)
  have g456 : aV al s w cover c (.n 456) = aV al s w cover c (.n 449) * aV al s w cover c (.n 455) :=
    aGood_mul (aggArgs_length _ _) (hm6 _ (by simp [w6A])) (by norm_num) (by norm_num)
  have v456 : aV al s w cover c (.n 456) = ptrAt (aB c w.children.length 7 + (w.children.length + w.children.length)) := by
    rw [g456, g455, v0, p449, ← pow_add, ptrAt_mul_gen_pow]
  have h7 : w.children.length + w.children.length + 1 < (aBufs w.children.length).getD 7 0 := by
    simp [aBufs]; omega
  obtain ⟨i457, e457⟩ := valAt_own (al := al) (cover := cover) (c := c) hl (by norm_num) h7
  have L457 := aLoad_fresh (al := al) (s := s) (w := w) (cover := cover) (c := c)
    (hm6 _ (by simp [w6A])) f457 v456 (by rwa [← Nat.add_assoc] at i457)
    (by have := (aB_lt (c := c) (by norm_num) h7).2; omega)
  have hg : ∀ i, (aChain (aCs w) (aCols w) (aLam w) i).length = 2 := fun _ => rfl
  have v457 : aV al s w cover c (.n 457) = Batch.batchedClaim (aCs w)
      (aggLam (aCs w) w.batchingHints.lambdaGrindNonce) (aggCols (aCs w) w.batchingHints.lambdaGrindNonce).1 := by
    rw [L457.1, Nat.add_assoc, e457, show w.children.length + w.children.length + 1 = 2 * w.children.length + 1 by ring,
      show (aLists s w).getD 7 [] = (List.range (w.children.length + 1)).flatMap
        (aChain (aCs w) (aCols w) (aLam w)) from rfl, getD_flatMap_range _ hg _ _ _ (by omega) (by norm_num)]
    simp only [aChain, List.getD_cons_succ, List.getD_cons_zero, Batch.batchedClaim, aggLam, aCs_length]
    rw [List.take_of_length_le (by rw [aCs_length])]
    rfl
  -- the sponge after the squeezes
  have hpend : (aggCols (aCs w) w.batchingHints.lambdaGrindNonce).2.pend = [] := by
    rw [aggCols, squeezeN_snd]; exact sqIter_pend _ _ rfl
  have hs : (⟨[aV al s w cover c (.n 230), aV al s w cover c (.n 231), aV al s w cover c (.n 232),
      aV al s w cover c (.n 233), aV al s w cover c (.n 234)], []⟩ : Fs) =
      (aggCols (aCs w) w.batchingHints.lambdaGrindNonce).2 := by
    rw [hcap]
    revert hpend
    cases (aggCols (aCs w) w.batchingHints.lambdaGrindNonce).2
    intro h; simp only at h; rw [h]
  have hrun : bsRun w.batchingHints.sumcheckMessages (aV al s w cover c (.n 457))
      ⟨[aV al s w cover c (.n 230), aV al s w cover c (.n 231), aV al s w cover c (.n 232),
        aV al s w cover c (.n 233), aV al s w cover c (.n 234)], []⟩ = aggRun (aCs w) w.batchingHints := by
    rw [hs, v457, aggRun]
  have hc5 := bsRun_cap5 w.batchingHints.sumcheckMessages (aV al s w cover c (.n 457))
    ⟨[aV al s w cover c (.n 230), aV al s w cover c (.n 231), aV al s w cover c (.n 232),
        aV al s w cover c (.n 233), aV al s w cover c (.n 234)], []⟩ rfl
  rw [hrun] at hc5
  have vr : ∀ i < 5, aV al s w cover c (.n (461 + i)) = (aggRun (aCs w) w.batchingHints).2.cap.getD i 0 := by
    intro i hi
    have h := aVal_good (rd0 := aRd0 al s w cover c) (o := aOrc w c) (aggArgs_length al (mainCounts s w)) _
      agg_bs_mem (.n (461 + i)) (by simp; omega)
    interval_cases i <;> exact h.trans rfl
  have v466 : aV al s w cover c (.n 466) = (aggRun (aCs w) w.batchingHints).1.2 :=
    (aVal_good (aggArgs_length _ _) _ agg_bs_mem (.n 466) (by simp)).trans rfl
  obtain ⟨hq0, hlen0⟩ := aWo_get (c := c) hl (j := 0) (by norm_num)
  obtain ⟨hq8, hlen8⟩ := aWo_get (c := c) hl (j := 8) (by norm_num)
  have hpt : (aggRun (aCs w) w.batchingHints).1.1.length = 25 := hp25
  have hml : (w.batchingHints.sumcheckMessages.flatMap fun g => [g.1, g.2]).length = 50 := by
    rw [flatMap_length_const (n := 2) (fun _ _ => rfl), h25]
  have hn1 : (Batch.lambdaGrindNonceCells w.batchingHints).length = 1 := by
    simp [Batch.lambdaGrindNonceCells, show Batch.batchLambdaGrindBits ≠ 0 by decide]
  simp only [List.map_cons, List.map_nil, MeaningBatchSumcheck]
  refine ⟨w.batchingHints.sumcheckMessages, h25, ?_, ?_⟩
  · intro k hk
    refine load_at hO hq0 (i := 1) v460 (by rw [hlen0]; simp only [aBufs, List.getD_cons_zero]; omega) ?_
    rw [show (aLists s w).getD 0 [] = Batch.lambdaGrindNonceCells w.batchingHints ++
      w.batchingHints.sumcheckMessages.flatMap Batch.sumcheckRoundCells from rfl,
      List.getD_append_right _ _ _ _ (by omega), hn1, Nat.add_sub_cancel_left]
    exact List.getD_eq_getElem _ _ _
  · simp only [hrun]
    refine ⟨fun k hk => load_at hO hq8 (i := 0) (by rw [p458, Nat.add_zero]) (by rw [hlen8]; simp [aBufs]; omega) ?_, ?_⟩
    · rw [Nat.zero_add, show (aLists s w).getD 8 [] = aPt w from rfl, aPt]
      exact List.getD_eq_getElem _ _ _
    · rw [list5 hc5, v466, ← vr 0 (by norm_num), ← vr 1 (by norm_num), ← vr 2 (by norm_num), ← vr 3 (by norm_num),
        ← vr 4 (by norm_num)]
      rfl

end

end
end LeanVM.Guest.Complete.Agg
