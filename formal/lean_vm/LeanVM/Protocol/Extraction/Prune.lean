module

public import LeanVM.Protocol.Extraction.Defs
public import LeanVM.Protocol.Extraction.Lane

/-!
# The pruning across lanes is complete; its survivors are distinct and few (proofs)

With `n = 2^(κ+R)` columns and `commonCols κ R W cs U` the columns `v < n` at which the
encodings of `cs[0], …, cs[U−1]` agree with the word's lanes `0, …, U − 1`:

* `pruneUpTo_succ`: lane `U` is one `pruneStep` (the emptiness guard only skips work);
* `mem_pruneUpTo`: every survivor `(cs, S)` after `U` lanes has `U` arrays, `cs[u]` in lane `u`'s
  list, `S = commonCols cs U`, and `A ≤ |S|` once `U ≥ 1`;
* **`prefix_mem_pruneUpTo`** (completeness): if `cs*` has each `cs*[u]` in lane `u`'s list and
  `A ≤ |commonCols cs* 64|`, then `(cs*[0..U), commonCols cs* U)` survives every lane `U ≤ 64`:
  its common columns only shrink, and contain those of all `64` lanes;
* **`mem_decodeStacksAt`**: every candidate (`Candidates μ R A W`: the encoding agrees with the
  word on at least `A` columns) is a decoded stack, for `κ = μ − 6 ≥ 1`, `κ + R ≤ 64`, `A ≤ n`
  and `(2^κ − 1)·n < A²`; `candidates_subset_decodeStacks` at the deployed shapes and the
  Johnson threshold. Its lanes are in the lane lists (`laneCoeffs_mem_laneListAt`), its common
  columns are its agreement (`commonCols_laneCoeffs`), and `stackOf` reassembles it
  (`stackOf_laneCoeffs`).

For the running time (not needed for soundness):
* `decodeStacksAt_sound`, `nodup_decodeStacksAt`: the decoded stacks are candidates
  (`lanesOf_stackOf`: a stack's lanes are its survivor's arrays) and pairwise distinct, so their
  number is at most the number of candidates (`2^12` at the deployed shapes,
  `Sound.decodeStacks_length_le`);

* `nodup_pruneUpTo`: the survivors' prefixes are pairwise distinct (the lane lists are
  deduplicated, and children of distinct prefixes are distinct);
* `injOn_evalTuple`: a survivor is determined by its encodings on the `n` columns (`novelInv`
  inverts `novelFwd` on arrays of size `2^κ`);
* **`length_pruneUpTo_le`**: for `U ≥ 1`, the number of survivors after `U` lanes is at most the
  size of any finite set `T` of `U`-tuples of words containing the encodings of every `U`-tuple of
  coefficient arrays (of size `2^κ`) whose encodings agree with the word's first `U` lanes on at
  least `A` common columns. Such encodings are interleaved Reed–Solomon codewords close to the
  word, so `T` can be lean_vm's `iList` and the Johnson bound
  `card_iList_johnsonAgreement_le_floor` caps the survivors by `listMax ≤ 2^12`.
* `length_laneListAt_le`: the same for each lane's list (one lane, `ρ = Unit`), from the
  decoder's soundness (`laneListAt_sound`);
* `encoding_mem_code`, `evalTuple_mem_code`: every encoding is a codeword of ArkLib's
  `ReedSolomon.code (domainEmb n) (2^κ)`, so the survivors' tuples are interleaved codewords and
  lean_vm can take `T = iList (ReedSolomon.code …) A (lanes of W)`; what remains there is the
  closeness, the common columns as `agreeSet`.

Credits: `ReedSolomon.code` and `mem_code_of_polynomial_of_degree_lt_of_eval` are ArkLib's
(github.com/Verified-zkEVM/ArkLib at `4dae3acff846125521b7b3998010885071746f16`, Apache-2.0;
`Data/CodingTheory/ReedSolomon.lean`, Quang Dao, Katerina Hristova, František Silváši, Julian
Sutherland, Ilia Vlasov, Mirco Richter, Chung Thai Nguyen, Aristotle (Harmonic)); the lane
decoder's completeness rests on ArkLib's and CompPoly's GS (see `LeanVM.Protocol.Extraction.Lane`).
-/

namespace LeanVM.Extraction.PruneProofs

open LeanVM.Parameters LeanVM.Parameters.Whir LeanVM.Extraction LeanVM.Extraction.NovelProofs
open LeanVM.Extraction.LaneProofs

public section

attribute [local simp] LeanVM.Extraction.Words.ofBits_zero

/-! ## Common columns -/

/-- The columns `v < 2^(κ+R)` at which the encodings of `cs[0], …, cs[U−1]` agree with the word's
lanes `0, …, U − 1`. -/
@[expose] def commonCols (κ R : ℕ) (W : ℕ → List K) (cs : List (Array K)) (U : ℕ) : List ℕ :=
  (List.range (2 ^ (κ + R))).filter fun v ↦
    decide (∀ u < U, (novelFwd κ R (cs.getD u #[])).getD v 0 = laneSymbol W u v)

theorem commonCols_zero (κ R : ℕ) (W : ℕ → List K) (cs : List (Array K)) :
    commonCols κ R W cs 0 = List.range (2 ^ (κ + R)) := by
  simp [commonCols]

/-- One more lane filters the common columns by that lane's agreement. -/
theorem commonCols_succ (κ R : ℕ) (W : ℕ → List K) (cs : List (Array K)) (U : ℕ) :
    commonCols κ R W cs (U + 1) = (commonCols κ R W cs U).filter fun v ↦
      decide ((novelFwd κ R (cs.getD U #[])).getD v 0 = laneSymbol W U v) := by
  rw [commonCols, commonCols, List.filter_filter]
  refine List.filter_congr fun v _ ↦ ?_
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h U (by omega), fun u hu ↦ h u (by omega)⟩
  · rintro ⟨h1, h2⟩ u hu
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
    · exact h2 u hu
    · exact h1

/-- The common columns depend only on the first `U` arrays. -/
theorem commonCols_congr (κ R : ℕ) (W : ℕ → List K) {cs cs' : List (Array K)} {U : ℕ}
    (h : ∀ u < U, cs.getD u #[] = cs'.getD u #[]) :
    commonCols κ R W cs U = commonCols κ R W cs' U := by
  refine List.filter_congr fun v _ ↦ ?_
  rw [decide_eq_decide]
  constructor
  · intro h' u hu; rw [← h u hu]; exact h' u hu
  · intro h' u hu; rw [h u hu]; exact h' u hu

/-- More lanes, fewer common columns. -/
theorem commonCols_sublist (κ R : ℕ) (W : ℕ → List K) (cs : List (Array K)) {U U' : ℕ}
    (h : U ≤ U') : List.Sublist (commonCols κ R W cs U') (commonCols κ R W cs U) := by
  refine List.monotone_filter_right _ fun v hv ↦ ?_
  simp only [decide_eq_true_eq] at hv ⊢
  exact fun u hu ↦ hv u (by omega)

theorem nodup_commonCols (κ R : ℕ) (W : ℕ → List K) (cs : List (Array K)) (U : ℕ) :
    (commonCols κ R W cs U).Nodup :=
  List.nodup_range.filter _

/-! ## One step -/

theorem mem_pruneStep {A : ℕ} {sym : ℕ → K} {L : List (Array K × Array K)}
    {st : List (List (Array K) × List ℕ)} {x : List (Array K) × List ℕ} :
    x ∈ pruneStep A sym L st ↔ ∃ s ∈ st, ∃ ce ∈ L,
      A ≤ (s.2.filter fun v ↦ decide (ce.2.getD v 0 = sym v)).length ∧
        x = (s.1 ++ [ce.1], s.2.filter fun v ↦ decide (ce.2.getD v 0 = sym v)) := by
  simp only [pruneStep, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, ce, hce, h⟩
    split at h
    · exact ⟨s, hs, ce, hce, by assumption, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · rintro ⟨s, hs, ce, hce, hA, rfl⟩
    exact ⟨s, hs, ce, hce, by rw [ite_eq_left hA]⟩

theorem pruneStep_nil (A : ℕ) (sym : ℕ → K) (L : List (Array K × Array K)) :
    pruneStep A sym L [] = [] := rfl

theorem pruneUpTo_zero (κ R A : ℕ) (W : ℕ → List K) :
    pruneUpTo κ R A W 0 = [([], List.range (2 ^ (κ + R)))] := rfl

/-- **Lane `U` is one pruning step.** -/
theorem pruneUpTo_succ (κ R A : ℕ) (W : ℕ → List K) (U : ℕ) :
    pruneUpTo κ R A W (U + 1) =
      pruneStep A (laneSymbol W U) (laneEncodedAt κ R A W U) (pruneUpTo κ R A W U) := by
  rw [pruneUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← pruneUpTo]
  split
  · rename_i h
    rw [List.isEmpty_iff.mp h]
    rfl
  · rfl

/-! ## What survives -/

/-- The elements of a lane list have size `2^κ`. -/
theorem size_of_mem_laneListAt {κ R A : ℕ} {W : ℕ → List K} {u : ℕ} {c : Array K}
    (hc : c ∈ laneListAt κ R A W u) : c.size = 2 ^ κ := by
  rw [laneListAt, List.mem_mergeSort, List.mem_dedup, List.mem_map] at hc
  obtain ⟨p, _, rfl⟩ := hc
  exact size_novelInv _ Array.size_ofFn

/-- **The survivors after `U` lanes**: `U` arrays from the lanes' lists, with their common
columns, at least `A` of them. -/
theorem mem_pruneUpTo {κ R A : ℕ} {W : ℕ → List K} {U : ℕ} {x : List (Array K) × List ℕ}
    (hx : x ∈ pruneUpTo κ R A W U) :
    x.1.length = U ∧ (∀ u < U, x.1.getD u #[] ∈ laneListAt κ R A W u) ∧
      x.2 = commonCols κ R W x.1 U ∧ (0 < U → A ≤ x.2.length) := by
  induction U generalizing x with
  | zero =>
    rw [pruneUpTo_zero, List.mem_singleton] at hx
    subst hx
    exact ⟨rfl, fun _ h ↦ absurd h (by omega), (commonCols_zero ..).symm, fun h ↦ absurd h (by omega)⟩
  | succ U ih =>
    rw [pruneUpTo_succ, mem_pruneStep] at hx
    obtain ⟨s, hs, ce, hce, hA, rfl⟩ := hx
    obtain ⟨hlen, hlist, hcols, -⟩ := ih hs
    rw [laneEncodedAt, List.mem_map] at hce
    obtain ⟨c, hc, rfl⟩ := hce
    have hget : ∀ u < U, (s.1 ++ [c]).getD u #[] = s.1.getD u #[] := fun u hu ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show u < s.1.length by omega)]
    have hlast : (s.1 ++ [c]).getD U #[] = c := by
      simp [List.getD_eq_getElem?_getD, hlen]
    refine ⟨by simp [hlen], fun u hu ↦ ?_, ?_, fun _ ↦ hA⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · rw [hget u hu]; exact hlist u hu
      · rw [hlast]; exact hc
    · simp only
      rw [commonCols_succ, hlast, commonCols_congr κ R W hget, ← hcols]

/-! ## Completeness -/

/-- **A good prefix survives**: if each `cs*[u]`, `u < 64`, is in lane `u`'s list and the
encodings of all `64` agree with the word on at least `A` common columns, then
`(cs*[0..U), commonCols cs* U)` survives lanes `0, …, U − 1`, for `U ≤ 64`. -/
theorem prefix_mem_pruneUpTo {κ R A : ℕ} {W : ℕ → List K} {cs : List (Array K)}
    (hlen : cs.length = 2 ^ initialFold)
    (hlist : ∀ u < 2 ^ initialFold, cs.getD u #[] ∈ laneListAt κ R A W u)
    (hA : A ≤ (commonCols κ R W cs (2 ^ initialFold)).length) {U : ℕ}
    (hU : U ≤ 2 ^ initialFold) :
    (cs.take U, commonCols κ R W cs U) ∈ pruneUpTo κ R A W U := by
  induction U with
  | zero => rw [pruneUpTo_zero, commonCols_zero]; simp
  | succ U ih =>
    rw [pruneUpTo_succ, mem_pruneStep]
    refine ⟨_, ih (by omega), (cs.getD U #[], novelFwd κ R (cs.getD U #[])), ?_, ?_, ?_⟩
    · rw [laneEncodedAt, List.mem_map]
      exact ⟨_, hlist U (by omega), rfl⟩
    · rw [← commonCols_succ]
      exact hA.trans (commonCols_sublist κ R W cs (by omega)).length_le
    · rw [← commonCols_succ, List.take_add_one]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show U < cs.length by omega)]

/-! ## Candidates are decoded -/

/-- The lanes of a stack. -/
@[expose] def lanesOf {μ : ℕ} (q : Vector K (2 ^ μ)) : List (Array K) :=
  (List.range (2 ^ initialFold)).map (laneCoeffs q)

theorem getD_lanesOf {μ : ℕ} (q : Vector K (2 ^ μ)) {u : ℕ} (hu : u < 2 ^ initialFold) :
    (lanesOf q).getD u #[] = laneCoeffs q u := by
  simp [lanesOf, List.getD_eq_getElem?_getD, List.getElem?_range hu]

theorem length_lanesOf {μ : ℕ} (q : Vector K (2 ^ μ)) : (lanesOf q).length = 2 ^ initialFold := by
  simp [lanesOf]

/-- A stack's common columns over all lanes are its agreement with the word. -/
theorem commonCols_laneCoeffs {μ R : ℕ} (hκ : μ - initialFold ≤ 64) (W : ℕ → List K)
    (q : Vector K (2 ^ μ)) :
    (commonCols (μ - initialFold) R W (lanesOf q) (2 ^ initialFold)).length =
      (agreement R W q).card := by
  rw [← List.toFinset_card_of_nodup (nodup_commonCols ..)]
  congr 1
  ext v
  simp only [List.mem_toFinset, commonCols, List.mem_filter, List.mem_range, decide_eq_true_eq,
    agreement, Finset.mem_filter, Finset.mem_range]
  refine and_congr_right fun hv ↦ ?_
  constructor
  · intro h u
    rw [encode_eq_novelFwd hκ q u hv, ← getD_lanesOf q u.isLt, h u u.isLt, laneSymbol]
  · intro h u hu
    rw [getD_lanesOf q hu, ← encode_eq_novelFwd hκ q u hv, laneSymbol]
    exact (h ⟨u, hu⟩).symm

/-- `stackOf` reassembles a stack from its lanes. -/
theorem stackOf_laneCoeffs {μ : ℕ} (hμ : initialFold ≤ μ) (q : Vector K (2 ^ μ)) :
    stackOf μ (lanesOf q) = q := by
  have hsplit : 2 ^ μ = 2 ^ (μ - initialFold) * 2 ^ initialFold := by
    rw [← pow_add, Nat.sub_add_cancel hμ]
  apply Vector.ext
  intro i hi
  have hpos : 0 < 2 ^ (μ - initialFold) := Nat.two_pow_pos _
  have hdiv : i / 2 ^ (μ - initialFold) < 2 ^ initialFold := by
    rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm, ← hsplit]; exact hi
  rw [stackOf, Vector.getElem_ofFn, getD_lanesOf q hdiv, laneCoeffs,
    getD_ofFn _ (Nat.mod_lt _ hpos), Nat.mod_add_div]
  simp [Vector.getD, Array.getD_eq_getD_getElem?, hi]

/-- **Every candidate is a decoded stack**, for `κ = μ − 6 ≥ 1`, `κ + R ≤ 64`, `A ≤ 2^(κ+R)` and
`(2^κ − 1)·2^(κ+R) < A²`. -/
theorem mem_decodeStacksAt {μ R A : ℕ} (hμ : 7 ≤ μ) (hn : μ - initialFold + R ≤ 64)
    (hA : A ≤ 2 ^ (μ - initialFold + R))
    (hcap : (2 ^ (μ - initialFold) - 1) * 2 ^ (μ - initialFold + R) < A * A)
    (W : ℕ → List K) {q : Vector K (2 ^ μ)} (hq : q ∈ Candidates μ R A W) :
    q ∈ decodeStacksAt μ R A W := by
  have hκ : μ - initialFold ≤ 64 := by omega
  have hmem := prefix_mem_pruneUpTo (U := 2 ^ initialFold) (length_lanesOf q)
    (fun u hu ↦ by rw [getD_lanesOf q hu]; exact laneCoeffs_mem_laneListAt hμ hn hA hcap W hq hu)
    (by rw [commonCols_laneCoeffs hκ]; exact hq) le_rfl
  rw [List.take_of_length_le (length_lanesOf q).le] at hmem
  rw [decodeStacksAt, List.mem_map]
  exact ⟨_, hmem, stackOf_laneCoeffs (by simp only [initialFold]; omega) q⟩

/-- **At the deployed shapes, the candidates at the Johnson threshold are decoded**:
`Candidates μ R (johnsonThreshold μ R) W ⊆ decodeStacks μ R W`. -/
theorem candidates_subset_decodeStacks {μ R : ℕ} (hμ : 15 ≤ μ ∧ μ ≤ 28) (hR : 1 ≤ R ∧ R ≤ 4)
    (W : ℕ → List K) :
    Candidates μ R (johnsonThreshold μ R) W ⊆ {q | q ∈ decodeStacks μ R W} := fun q hq ↦ by
  obtain ⟨hA, hcap⟩ := johnsonThreshold_bounds hμ hR
  change q ∈ decodeStacksAt μ R (johnsonThreshold μ R) W
  exact mem_decodeStacksAt (by omega) (by simp only [initialFold]; omega) hA hcap W hq

/-- The same, at the statement's real-valued threshold (`johnsonThreshold_eq_real`). -/
theorem candidates_real_subset_decodeStacks {μ R : ℕ} (hμ : 15 ≤ μ ∧ μ ≤ 28)
    (hR : 1 ≤ R ∧ R ≤ 4) (W : ℕ → List K) :
    Candidates μ R (johnsonThresholdReal μ R) W ⊆ {q | q ∈ decodeStacks μ R W} := by
  rw [johnsonThreshold_eq_real]
  exact candidates_subset_decodeStacks hμ hR W

/-! ## Distinct survivors -/

/-- **The survivors' prefixes are pairwise distinct.** -/
theorem nodup_pruneUpTo (κ R A : ℕ) (W : ℕ → List K) (U : ℕ) :
    ((pruneUpTo κ R A W U).map Prod.fst).Nodup := by
  induction U with
  | zero => simp [pruneUpTo_zero]
  | succ U ih =>
    rw [pruneUpTo_succ, pruneStep, List.map_flatMap]
    refine List.nodup_flatMap.mpr ⟨fun s _ ↦ ?_, ?_⟩
    · rw [List.map_filterMap, laneEncodedAt, List.filterMap_map]
      refine ((List.mergeSort_perm _ _).nodup_iff.2 (List.nodup_dedup _)).filterMap fun c c' b hb hb' ↦ ?_
      simp only [Function.comp_apply, Option.mem_def, Option.map_eq_some_iff] at hb hb'
      obtain ⟨x, hx, rfl⟩ := hb
      obtain ⟨x', hx', hxx⟩ := hb'
      split at hx <;> split at hx' <;> simp only [Option.some.injEq, reduceCtorEq] at hx hx'
      subst hx hx'
      simpa using hxx.symm
    · have hp := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp ih)
      refine hp.imp fun {s s'} hne ↦ ?_
      rw [Function.onFun, List.disjoint_left]
      intro b hb hb'
      simp only [List.mem_map, List.mem_filterMap] at hb hb'
      obtain ⟨y, ⟨ce, -, hce⟩, rfl⟩ := hb
      obtain ⟨y', ⟨ce', -, hce'⟩, hyy⟩ := hb'
      split at hce <;> split at hce' <;> simp only [Option.some.injEq, reduceCtorEq] at hce hce'
      subst hce hce'
      exact hne (List.append_inj_left' (show s.1 ++ [ce.1] = s'.1 ++ [ce'.1] from hyy.symm) rfl)

/-! ## The number of survivors -/

/-- The encodings of `U` arrays on the `2^(κ+R)` columns. -/
@[expose] def evalTuple (κ R U : ℕ) (cs : List (Array K)) : Fin U → Fin (2 ^ (κ + R)) → K :=
  fun u v ↦ (novelFwd κ R (cs.getD u #[])).getD v 0

/-- An array of size `2^κ` is determined by its encoding. -/
theorem eq_of_novelFwd_eq {κ R : ℕ} (hκ : κ ≤ 64) {c c' : Array K} (hc : c.size = 2 ^ κ)
    (hc' : c'.size = 2 ^ κ)
    (h : ∀ v < 2 ^ (κ + R), (novelFwd κ R c).getD v 0 = (novelFwd κ R c').getD v 0) :
    c = c' := by
  have hle : 2 ^ κ ≤ 2 ^ (κ + R) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have key : ∀ d : Array K, d.size = 2 ^ κ →
      novelInv κ (Array.ofFn fun v : Fin (2 ^ κ) ↦ (novelFwd κ R d).getD v.val 0) = d := by
    intro d hd
    rw [novelInv_eval hκ (fun j ↦ d.getD j 0) _ Array.size_ofFn fun v hv ↦ by
      rw [getD_ofFn _ hv, novelFwd_getD hκ _ (by omega)]]
    exact array_ext_getD (by simp [hd]) fun p hp ↦ by
      simp only [Array.size_ofFn] at hp
      rw [getD_ofFn _ hp]
  rw [← key c hc, ← key c' hc']
  exact congrArg (novelInv κ) (congrArg Array.ofFn (funext fun v ↦ h v.val (by omega)))

/-- Survivors with the same encodings are the same. -/
theorem injOn_evalTuple {κ R A : ℕ} (hκ : κ ≤ 64) (W : ℕ → List K) (U : ℕ) :
    Set.InjOn (evalTuple κ R U) {cs | ∃ S, (cs, S) ∈ pruneUpTo κ R A W U} := by
  rintro cs ⟨S, hS⟩ cs' ⟨S', hS'⟩ h
  obtain ⟨hlen, hlist, -⟩ := mem_pruneUpTo hS
  obtain ⟨hlen', hlist', -⟩ := mem_pruneUpTo hS'
  apply List.ext_getElem (by simp [hlen, hlen'])
  intro u hu hu'
  have hu0 : u < U := by simpa [hlen] using hu
  have e := eq_of_novelFwd_eq (R := R) hκ (size_of_mem_laneListAt (hlist u hu0))
    (size_of_mem_laneListAt (hlist' u hu0)) fun v hv ↦
      congrFun (congrFun h ⟨u, hu0⟩) ⟨v, hv⟩
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu,
    List.getElem?_eq_getElem hu'] using e

/-- **The number of survivors after `U ≥ 1` lanes** is at most the size of any set of `U`-tuples
of words that contains the encodings of every `U` arrays of size `2^κ` whose encodings agree with
the word's first `U` lanes on at least `A` common columns. -/
theorem length_pruneUpTo_le {κ R A : ℕ} (hκ : κ ≤ 64) (W : ℕ → List K) {U : ℕ} (hU : 0 < U)
    (T : Finset (Fin U → Fin (2 ^ (κ + R)) → K))
    (hT : ∀ cs : List (Array K), cs.length = U → (∀ u < U, (cs.getD u #[]).size = 2 ^ κ) →
      A ≤ (commonCols κ R W cs U).length → evalTuple κ R U cs ∈ T) :
    (pruneUpTo κ R A W U).length ≤ T.card := by
  classical
  have hnd := nodup_pruneUpTo κ R A W U
  have hinj : ∀ x ∈ (pruneUpTo κ R A W U).map Prod.fst,
      ∀ y ∈ (pruneUpTo κ R A W U).map Prod.fst, evalTuple κ R U x = evalTuple κ R U y → x = y := by
    intro x hx y hy hxy
    simp only [List.mem_map] at hx hy
    obtain ⟨⟨x1, x2⟩, hx, rfl⟩ := hx
    obtain ⟨⟨y1, y2⟩, hy, rfl⟩ := hy
    exact injOn_evalTuple hκ W U ⟨x2, hx⟩ ⟨y2, hy⟩ hxy
  have hnd' := hnd.map_on hinj
  rw [← List.length_map (f := Prod.fst), ← List.length_map (f := evalTuple κ R U),
    ← List.toFinset_card_of_nodup hnd']
  refine Finset.card_le_card fun t ht ↦ ?_
  simp only [List.mem_toFinset, List.mem_map] at ht
  obtain ⟨cs, ⟨⟨cs', S⟩, hx, rfl⟩, rfl⟩ := ht
  obtain ⟨hlen, hlist, hcols, hA⟩ := mem_pruneUpTo hx
  exact hT cs' hlen (fun u hu ↦ size_of_mem_laneListAt (hlist u hu)) (hcols ▸ hA hU)

/-- **The size of a lane's list** is at most the size of any set of words that contains the
encodings of every array of size `2^κ` whose encoding agrees with lane `u` on at least `A`
columns (with lean_vm's `iList` at `ρ = Unit`, the Johnson bound). -/
theorem length_laneListAt_le {κ R A : ℕ} (hκ : 1 ≤ κ) (hn : κ + R ≤ 64) (hA : A ≤ 2 ^ (κ + R))
    (hcap : (2 ^ κ - 1) * 2 ^ (κ + R) < A * A) (W : ℕ → List K) (u : ℕ)
    (T : Finset (Fin (2 ^ (κ + R)) → K))
    (hT : ∀ c : Array K, c.size = 2 ^ κ → A ≤ ((Finset.range (2 ^ (κ + R))).filter fun v ↦
      (novelFwd κ R c).getD v 0 = laneSymbol W u v).card →
        (fun v : Fin (2 ^ (κ + R)) ↦ (novelFwd κ R c).getD v.val 0) ∈ T) :
    (laneListAt κ R A W u).length ≤ T.card := by
  classical
  let e : Array K → Fin (2 ^ (κ + R)) → K := fun c v ↦ (novelFwd κ R c).getD v.val 0
  have hnd : (laneListAt κ R A W u).Nodup := (List.mergeSort_perm _ _).nodup_iff.2 (List.nodup_dedup _)
  have hinj : ∀ x ∈ laneListAt κ R A W u, ∀ y ∈ laneListAt κ R A W u, e x = e y → x = y :=
    fun x hx y hy hxy ↦ eq_of_novelFwd_eq (R := R) (by omega)
      (laneListAt_sound hκ hn hA hcap W u hx).1 (laneListAt_sound hκ hn hA hcap W u hy).1
      fun v hv ↦ congrFun hxy ⟨v, hv⟩
  rw [← List.length_map (f := e), ← List.toFinset_card_of_nodup (hnd.map_on hinj)]
  refine Finset.card_le_card fun t ht ↦ ?_
  simp only [List.mem_toFinset, List.mem_map] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  obtain ⟨hsize, hagree⟩ := laneListAt_sound hκ hn hA hcap W u hc
  exact hT c hsize hagree

/-! ## Encodings are Reed–Solomon codewords -/

/-- **The encoding of any array is a Reed–Solomon codeword** of message length `2^κ` on the
points `x_v`, `v < 2^(κ+R)` (ArkLib's `ReedSolomon.code`): it is the evaluation of
`Σ_{j<2^κ} c_j·X_j`, of degree `< 2^κ`. With this, the tuples `evalTuple` of the survivors are
interleaved codewords, as `iList` requires. -/
theorem encoding_mem_code {κ R : ℕ} (hn : κ + R ≤ 64) (c : Array K) :
    (fun v : Fin (2 ^ (κ + R)) ↦ (novelFwd κ R c).getD v.val 0) ∈
      ReedSolomon.code (domainEmb (2 ^ (κ + R)) (Nat.pow_le_pow_right (by norm_num) hn)) (2 ^ κ) := by
  refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    (∑ j ∈ Finset.range (2 ^ κ), Polynomial.C (c.getD j 0) * novelPoly j)
    (degree_novelSum_lt (by omega) _) fun v ↦ ?_
  rw [novelFwd_getD (by omega) _ v.isLt]
  simp [Polynomial.eval_finsetSum, eval_novelPoly]
  rfl

/-- Every row of `evalTuple` is a Reed–Solomon codeword. -/
theorem evalTuple_mem_code {κ R U : ℕ} (hn : κ + R ≤ 64) (cs : List (Array K)) (u : Fin U) :
    evalTuple κ R U cs u ∈
      ReedSolomon.code (domainEmb (2 ^ (κ + R)) (Nat.pow_le_pow_right (by norm_num) hn)) (2 ^ κ) :=
  encoding_mem_code hn _

/-! ## The decoded stacks are distinct candidates -/

/-- The lanes of the stack of `2^6` arrays of size `2^κ` are the arrays. -/
theorem lanesOf_stackOf {μ : ℕ} (hμ : initialFold ≤ μ) {cs : List (Array K)}
    (hlen : cs.length = 2 ^ initialFold)
    (hsize : ∀ u < 2 ^ initialFold, (cs.getD u #[]).size = 2 ^ (μ - initialFold)) :
    lanesOf (stackOf μ cs) = cs := by
  have hsplit : 2 ^ μ = 2 ^ (μ - initialFold) * 2 ^ initialFold := by
    rw [← pow_add, Nat.sub_add_cancel hμ]
  have hpos : 0 < 2 ^ (μ - initialFold) := Nat.two_pow_pos _
  suffices key : ∀ u < 2 ^ initialFold, (lanesOf (stackOf μ cs)).getD u #[] = cs.getD u #[] by
    refine List.ext_getElem (by rw [length_lanesOf, hlen]) fun u h1 h2 ↦ ?_
    rw [← List.getD_eq_getElem _ #[] h1, ← List.getD_eq_getElem _ #[] h2]
    exact key u (by rwa [length_lanesOf] at h1)
  intro u hu
  rw [getD_lanesOf _ hu]
  refine array_ext_getD (by rw [laneCoeffs, Array.size_ofFn, hsize u hu]) fun j hj ↦ ?_
  rw [laneCoeffs, Array.size_ofFn] at hj
  rw [laneCoeffs, getD_ofFn _ hj]
  have hlt : j + 2 ^ (μ - initialFold) * u < 2 ^ μ := by
    rw [hsplit]
    have : 2 ^ (μ - initialFold) * u + 2 ^ (μ - initialFold) ≤ 2 ^ (μ - initialFold) * 2 ^ initialFold := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hu
    omega
  have hdiv : (j + 2 ^ (μ - initialFold) * u) / 2 ^ (μ - initialFold) = u := by
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (j + 2 ^ (μ - initialFold) * u) % 2 ^ (μ - initialFold) = j := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [Vector.getD, stackOf]
  simp [hlt, hdiv, hmod]


/-- **Every decoded stack is a candidate**: its lanes are the survivor's arrays, whose common
columns over all `2^6` lanes, at least `A` of them, are its agreement with the word. -/
theorem decodeStacksAt_sound {μ R A : ℕ} (hμ : initialFold ≤ μ) (hκ : μ - initialFold ≤ 64)
    (W : ℕ → List K) {q : Vector K (2 ^ μ)} (hq : q ∈ decodeStacksAt μ R A W) :
    q ∈ Candidates μ R A W := by
  rw [decodeStacksAt, List.mem_map] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  obtain ⟨hlen, hlist, hcols, hA⟩ := mem_pruneUpTo hs
  have hl : lanesOf (stackOf μ s.1) = s.1 :=
    lanesOf_stackOf hμ hlen fun u hu ↦ size_of_mem_laneListAt (hlist u hu)
  show A ≤ (agreement R W (stackOf μ s.1)).card
  rw [← commonCols_laneCoeffs hκ, hl, ← hcols]
  exact hA (Nat.two_pow_pos _)

/-- **The decoded stacks are pairwise distinct**: distinct survivors have distinct arrays, and a
stack's lanes are its survivor's arrays. -/
theorem nodup_decodeStacksAt {μ R A : ℕ} (hμ : initialFold ≤ μ) (W : ℕ → List K) :
    (decodeStacksAt μ R A W).Nodup := by
  rw [decodeStacksAt]
  refine List.Nodup.map_on (fun s hs s' hs' he ↦ ?_)
    (List.Nodup.of_map _ (nodup_pruneUpTo (μ - initialFold) R A W (2 ^ initialFold)))
  obtain ⟨hlen, hlist, hcols, -⟩ := mem_pruneUpTo hs
  obtain ⟨hlen', hlist', hcols', -⟩ := mem_pruneUpTo hs'
  have e1 : s.1 = s'.1 := calc
    s.1 = lanesOf (stackOf μ s.1) :=
      (lanesOf_stackOf hμ hlen fun u hu ↦ size_of_mem_laneListAt (hlist u hu)).symm
    _ = lanesOf (stackOf μ s'.1) := congrArg lanesOf he
    _ = s'.1 := lanesOf_stackOf hμ hlen' fun u hu ↦ size_of_mem_laneListAt (hlist' u hu)
  exact Prod.ext e1 (by rw [hcols, hcols', e1])

/-- Stacks of `n` words of `K` are finitely many. -/
theorem finite_vector_K (n : ℕ) : Finite (Vector K n) :=
  Finite.of_injective (fun v : Vector K n ↦ fun i : Fin n ↦ v[i]) fun _ _ h ↦
    Vector.ext fun i hi ↦ congrFun h ⟨i, hi⟩

/-- **The decoded stacks are at most the candidates.** -/
theorem length_decodeStacksAt_le {μ R A : ℕ} (hμ : initialFold ≤ μ) (hκ : μ - initialFold ≤ 64)
    (W : ℕ → List K) : (decodeStacksAt μ R A W).length ≤ (Candidates μ R A W).ncard := by
  have hnd := nodup_decodeStacksAt (R := R) (A := A) hμ W
  rw [← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset]
  have := finite_vector_K (2 ^ μ)
  exact Set.ncard_le_ncard (fun q hq ↦ decodeStacksAt_sound hμ hκ W (List.mem_toFinset.mp hq))
    (Set.toFinite _)

end
end LeanVM.Extraction.PruneProofs
