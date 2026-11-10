/-
  LeanVM.Wire.ReadDet

  The bytes a pruned proof encodes to (`encodePhase`, `encodePruned`) and the reader's determinism:
  bytes `readPhase` / `readProof` accept are the encoding of what they read.
-/

module

public import LeanVM.Wire.Spec
import LeanVM.Wire.ReadWrite
import Mathlib.Data.List.GetD

/-!
# The reader's determinism

`encodePhase ph` is what `Prover.phaseToBytes` writes, computed from the pruned form `ph` instead of
the paths: the queries' count and positions, the height, the leaf width and the row width (the leaf
width less the zero words common to the fronts of the leaves, `zeroPrefix`, as `phaseToBytes`
computes them), each leaf without that prefix, and the carried siblings' digests level by level, in
order. `encodePruned` is `Proof.toBytes` from the pruned form: the stream's length and elements, the
phase count and each phase.

The reader is deterministic: bytes `readPhase` accepts are `encodePhase` of the phase read, then
the rest (`eq_encodePhase_of_readPhase`), and bytes `readProof` accepts are `encodePruned` of what
it reads (`toBytes_of_readProof`). A phase `readPhase` accepts satisfies `PhaseRead`
(`phaseRead_of_readPhase`): the bounds, the positions, the leaves' shape and minimal row width, and
the carried siblings' keys level by level. The basic readers' converse forms are
`LeanVM.Wire.ReadWrite`'s.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- The number of zero words common to the fronts of the leaves, as `Prover.phaseToBytes`
computes it: the least, over the leaves, of the length of the leaf's leading run of zeros; `0` for
no leaf. -/
def zeroPrefix (leaves : List (List K)) : ℕ :=
  ((leaves.map fun leaf ↦ (leaf.takeWhile fun word ↦ decide (word = 0)).length).min?).getD 0

/-- The bytes of a pruned phase: the queries' count and positions; the height, the leaf width and
the row width `leafWords - zeroPrefix leaves`; each leaf without the common zero prefix; then the
carried siblings' digests, level by level, in order. -/
def encodePhase (ph : PrunedPhase) : Bytes :=
  let zeros := zeroPrefix ph.leaves
  Prover.u32Bytes ph.queries.length ++ ph.queries.flatMap Prover.u32Bytes ++
    Prover.u32Bytes ph.height ++ Prover.u32Bytes ph.leafWords ++
    Prover.u32Bytes (ph.leafWords - zeros) ++
    ph.leaves.flatMap (fun leaf ↦ (leaf.drop zeros).flatMap K.toBytes) ++
    ph.carried.flatMap fun level ↦ level.flatMap fun carried ↦ digestBytes carried.2

/-- The bytes of a pruned proof, as `Proof.toBytes` writes them: the stream's length, then each
element as its two words; the number of phases, then each phase (`encodePhase`). -/
def encodePruned (x : List E × List PrunedPhase) : Bytes :=
  Prover.u32Bytes x.1.length ++ x.1.flatMap E.toBytes ++
    Prover.u32Bytes x.2.length ++ x.2.flatMap encodePhase

/-! ## What `readPhase` guarantees -/

/-- **Everything `readPhase` guarantees about the phase it reads** (`phaseRead_of_readPhase`): at
most `wireMaxQueries` queries, each below `2 ^ 32`; height at most `wireMaxHeight`, leaf width at
most `wireMaxLeafWords`; the positions the queries' distinct ones ascending, at least one, all
below `2 ^ height`; one leaf per position, each of the leaf width; the row width minimal (some
`rowWords ≤ leafWords` with every leaf `rowWords` words after `leafWords - rowWords` zeros, and
`rowWords = 0` or some leaf's word at `leafWords - rowWords` nonzero; hence
`zeroPrefix leaves = leafWords - rowWords`, `PhaseRead.zeroPrefix_eq`); and, level by level, the
carried siblings keyed by `carriedSiblings (levelNodes positions level)`, one list per level. -/
structure PhaseRead (ph : PrunedPhase) : Prop where
  queries_length_le : ph.queries.length ≤ wireMaxQueries
  queries_lt : ∀ query ∈ ph.queries, query < 2 ^ 32
  height_le : ph.height ≤ wireMaxHeight
  leafWords_le : ph.leafWords ≤ wireMaxLeafWords
  positions_eq : ph.positions = distinctPositions ph.queries
  positions_ne_nil : ph.positions ≠ []
  positions_lt : ∀ position ∈ ph.positions, position < 2 ^ ph.height
  leaves_length : ph.leaves.length = ph.positions.length
  leaf_length : ∀ leaf ∈ ph.leaves, leaf.length = ph.leafWords
  rowWidth : ∃ rowWords ≤ ph.leafWords,
    (∀ leaf ∈ ph.leaves, ∃ row, row.length = rowWords ∧ leaf = paddedLeaf row ph.leafWords) ∧
    (rowWords = 0 ∨ ∃ leaf ∈ ph.leaves, leaf.getD (ph.leafWords - rowWords) 0 ≠ 0)
  carried_keys : ph.carried.map (·.map Prod.fst) =
    (List.range ph.height).map fun level ↦ carriedSiblings (levelNodes ph.positions level)

/-! ## List facts -/

/-- `dedupByKey` keeps a sublist. -/
theorem dedupByKey_sublist {α β : Type} [DecidableEq β] (key : α → β) :
    ∀ l : List α, (dedupByKey key l).Sublist l
  | [] => by simp [dedupByKey]
  | a :: rest => by
    have ih := dedupByKey_sublist key rest
    rw [dedupByKey]
    split
    · exact (List.nil_sublist rest).cons_cons a
    · rename_i b kept heq
      rw [heq] at ih
      split
      · exact ((List.sublist_cons_self b kept).trans ih).cons_cons a
      · exact ih.cons_cons a

/-- The distinct positions are ascending. -/
theorem pairwise_le_distinctPositions (queries : List ℕ) :
    (distinctPositions queries).Pairwise (· ≤ ·) := by
  have hsorted := List.pairwise_mergeSort (le := fun a b : ℕ ↦ decide (a ≤ b))
    (by intro a b c; simp only [decide_eq_true_eq]; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) queries
  exact ((hsorted.sublist (dedupByKey_sublist id _)).imp (by simp))

/-- Every element of an ascending list is at most its last. -/
theorem le_of_getLast?_eq {l : List ℕ} {last : ℕ} (hsorted : l.Pairwise (· ≤ ·))
    (hlast : l.getLast? = some last) : ∀ x ∈ l, x ≤ last := by
  obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.1 hlast
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact (List.pairwise_append.1 hsorted).2.2 x hx last (List.mem_singleton_self _)
  · simp_all

/-- A leaf's leading zeros: those of the padding, then the row's. -/
theorem takeWhile_zero_paddedLeaf (row : List K) (leafWords : ℕ) :
    ((paddedLeaf row leafWords).takeWhile fun word ↦ decide (word = 0)).length =
      (leafWords - row.length) + (row.takeWhile fun word ↦ decide (word = 0)).length := by
  unfold paddedLeaf
  rw [List.takeWhile_append_of_pos (fun a ha ↦ by simp [(List.mem_replicate.1 ha).2])]
  simp

/-- The zero prefix of padded rows of one width, the least width (`readPhase`'s guard), is the
padding. -/
theorem zeroPrefix_map_paddedLeaf (rows : List (List K)) (leafWords rowWords : ℕ)
    (hne : rows ≠ []) (hlength : ∀ row ∈ rows, row.length = rowWords)
    (hmin : ¬ (0 < rowWords ∧
      ∀ leaf ∈ rows.map (fun row ↦ paddedLeaf row leafWords),
        leaf.getD (leafWords - rowWords) 0 = 0)) :
    zeroPrefix (rows.map fun row ↦ paddedLeaf row leafWords) = leafWords - rowWords := by
  have hmin? : ((rows.map fun row ↦ paddedLeaf row leafWords).map fun leaf ↦
      (leaf.takeWhile fun word ↦ decide (word = 0)).length).min? = some (leafWords - rowWords) := by
    rw [List.min?_eq_some_iff]
    simp only [List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, takeWhile_zero_paddedLeaf]
    refine ⟨?_, fun row hrow ↦ by rw [hlength row hrow]; omega⟩
    by_cases hzero : rowWords = 0
    · obtain ⟨row, hrow⟩ := List.exists_mem_of_ne_nil rows hne
      have : row = [] := List.eq_nil_of_length_eq_zero (by rw [hlength row hrow, hzero])
      subst this
      exact ⟨[], hrow, by simp [hzero]⟩
    · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_and,
        not_forall] at hmin
      obtain ⟨row, hrow, hnz⟩ := hmin (by omega)
      refine ⟨row, hrow, ?_⟩
      have hrl := hlength row hrow
      unfold paddedLeaf at hnz
      rw [hrl, List.getD_append_right _ _ _ _ (by simp)] at hnz
      match row, hrl with
      | a :: tail, hrl' =>
        simp only [List.length_replicate, Nat.sub_self, List.getD_cons_zero] at hnz
        simp only [List.length_cons] at hrl'
        simp [hnz]
        omega
  unfold zeroPrefix
  rw [hmin?]
  rfl

/-- A padded row without the padding is the row. -/
theorem drop_paddedLeaf (row : List K) (leafWords : ℕ) :
    (paddedLeaf row leafWords).drop (leafWords - row.length) = row :=
  List.drop_left' (by simp)

/-- The stream's words, regrouped by two into elements as `readProof` does, are written back as
the same words (as `LeanVM.Wire.flatMap_toBytes_regroup`, rtglue's). -/
theorem stream_flatMap_toBytes (count : ℕ) (words : List K) (hlength : words.length = 2 * count) :
    ((List.range count).map fun i ↦ E.ofLimbs (words.getD (2 * i) 0)
        (words.getD (2 * i + 1) 0)).flatMap E.toBytes = words.flatMap K.toBytes := by
  induction count generalizing words with
  | zero =>
    cases words with
    | nil => rfl
    | cons => simp at hlength
  | succ count ih =>
    match words, hlength with
    | c0 :: c1 :: rest, hlength =>
      have hrest : rest.length = 2 * count := by simp at hlength; omega
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.flatMap_cons]
      rw [← ih rest hrest]
      have hshift : ∀ i j, (c0 :: c1 :: rest).getD (2 * (i + 1) + j) 0 =
          rest.getD (2 * i + j) 0 := fun i j ↦ by
        rw [show 2 * (i + 1) + j = (2 * i + j) + 1 + 1 by omega]
        simp only [List.getD_cons_succ]
      have hshift0 := fun i ↦ hshift i 0
      simp only [Nat.add_zero] at hshift0
      simp only [Function.comp_def, hshift0, List.getD_cons_zero,
        List.getD_cons_succ, Nat.mul_zero, Nat.zero_add, E.toBytes, List.append_assoc]
      rfl

/-- What `PhaseRead`'s row width gives: the zero prefix of the leaves is the leaf width less the
row width, every leaf being that row width's words after the prefix. -/
theorem PhaseRead.exists_zeroPrefix {ph : PrunedPhase} (hp : PhaseRead ph) :
    ∃ rowWords ≤ ph.leafWords, zeroPrefix ph.leaves = ph.leafWords - rowWords ∧
      ∀ leaf ∈ ph.leaves, ∃ row, row.length = rowWords ∧ leaf = paddedLeaf row ph.leafWords := by
  obtain ⟨rowWords, hle, hrows, hmin⟩ := hp.rowWidth
  refine ⟨rowWords, hle, ?_, hrows⟩
  have hleaves : ph.leaves = (ph.leaves.map (·.drop (ph.leafWords - rowWords))).map
      (paddedLeaf · ph.leafWords) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id ph.leaves]
    refine List.map_congr_left fun leaf hleaf ↦ ?_
    obtain ⟨row, hrl, rfl⟩ := hrows leaf hleaf
    simp only [id, Function.comp_apply]
    rw [← hrl, drop_paddedLeaf]
  have hne : ph.leaves ≠ [] := by
    intro hnil
    exact hp.positions_ne_nil (List.eq_nil_of_length_eq_zero (hp.leaves_length ▸ hnil ▸ rfl))
  rw [hleaves]
  refine zeroPrefix_map_paddedLeaf _ _ _ (by simpa using hne) ?_ ?_
  · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro leaf hleaf
    obtain ⟨row, hrl, rfl⟩ := hrows leaf hleaf
    rw [← hrl, drop_paddedLeaf]
  · rw [← hleaves]
    rintro ⟨hpos, hall⟩
    rcases hmin with hzero | ⟨leaf, hleaf, hnz⟩
    · omega
    · exact hnz (hall leaf hleaf)

/-! ## The reader's determinism -/

theorem carriedSiblings_eq (positions : List ℕ) : ∀ level remaining bytes carried rest,
    readCarriedSiblings positions level remaining bytes = some (carried, rest) →
      carried.map (·.map Prod.fst) =
          (List.range' level remaining).map (fun l ↦ carriedSiblings (levelNodes positions l)) ∧
        bytes = carried.flatMap (fun lvl ↦ lvl.flatMap fun x ↦ digestBytes x.2) ++ rest
  | _, 0, bytes, carried, rest, h => by
    simp only [readCarriedSiblings, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | level, remaining + 1, bytes, carried, rest, h => by
    simp only [readCarriedSiblings, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨digests, input, hdigests, above, input', habove, rfl, rfl⟩ := h
    obtain ⟨hlength, rfl⟩ := readDigests_eq_some_iff.1 hdigests
    obtain ⟨hkeys, rfl⟩ := carriedSiblings_eq positions (level + 1) remaining _ _ _ habove
    refine ⟨?_, ?_⟩
    · rw [List.range'_succ, List.map_cons, List.map_cons, hkeys,
        List.map_fst_zip (by omega)]
    · have hsnd := List.map_snd_zip (l₁ := carriedSiblings (levelNodes positions level))
        (l₂ := digests) (by omega)
      have : (List.zip (carriedSiblings (levelNodes positions level)) digests).flatMap
          (fun x ↦ digestBytes x.2) = digests.flatMap digestBytes := by
        conv_rhs => rw [← hsnd]
        rw [List.flatMap_map]
      simp only [List.flatMap_cons, this, List.append_assoc]

theorem readPhase_eq {bytes : Bytes} {ph : PrunedPhase} {rest : Bytes}
    (h : readPhase bytes = some (ph, rest)) : bytes = encodePhase ph ++ rest ∧ PhaseRead ph := by
  simp only [readPhase, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
    Option.guard_eq_some', Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨count, input₁, hcount, -, hcountLe, queries, input₂, hqueries, height, input₃, hheight,
    leafWords, input₄, hleafWords, rowWords, input₅, hrowWords, -, ⟨hheightLe, hleafWordsLe,
    hrowLe, last, hlast, hlastShift⟩, rows, input₆, hrows, -, hmin, carried, input₇, hcarried,
    rfl, rfl⟩ := h
  obtain ⟨-, rfl⟩ := readU32_eq_some_iff.1 hcount
  obtain ⟨rfl, hqueriesLt, rfl⟩ := readU32s_eq_some_iff.1 hqueries
  obtain ⟨-, rfl⟩ := readU32_eq_some_iff.1 hheight
  obtain ⟨-, rfl⟩ := readU32_eq_some_iff.1 hleafWords
  obtain ⟨-, rfl⟩ := readU32_eq_some_iff.1 hrowWords
  obtain ⟨hrowsLength, hrowLength, rfl⟩ := readRows_eq_some_iff.1 hrows
  obtain ⟨hkeys, rfl⟩ := carriedSiblings_eq _ _ _ _ _ _ hcarried
  have hlast' : (distinctPositions queries).getLast? = some last := hlast
  have hne : distinctPositions queries ≠ [] := by
    intro hnil; rw [hnil] at hlast'; cases hlast'
  have hrowsNe : rows ≠ [] := by
    intro hnil; rw [hnil] at hrowsLength; exact hne (List.eq_nil_of_length_eq_zero hrowsLength.symm)
  have hzero := zeroPrefix_map_paddedLeaf rows leafWords rowWords hrowsNe hrowLength hmin
  refine ⟨?_, ?_⟩
  · have hleaves : (rows.map fun row ↦ paddedLeaf row leafWords).flatMap
        (fun leaf ↦ (leaf.drop (leafWords - rowWords)).flatMap K.toBytes) =
          rows.flatMap (·.flatMap K.toBytes) := by
      rw [List.flatMap_map]
      refine List.flatMap_congr fun row hrow ↦ ?_
      rw [← hrowLength row hrow, drop_paddedLeaf]
    simp only [encodePhase, hzero, hleaves, Nat.sub_sub_self hrowLe, List.append_assoc]
  · have hlastLt : last < 2 ^ height := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at hlastShift
      rcases hlastShift with h | h
      · exact absurd h (by positivity : 0 < 2 ^ height).ne'
      · exact h
    refine ⟨hcountLe, hqueriesLt, hheightLe, hleafWordsLe, rfl, hne,
      fun position hposition ↦ lt_of_le_of_lt (le_of_getLast?_eq
        (pairwise_le_distinctPositions queries) hlast' position hposition) hlastLt,
      by simp [hrowsLength], ?_, ?_, ?_⟩
    · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro row hrow
      simp [paddedLeaf, hrowLength row hrow]
      omega
    · refine ⟨rowWords, hrowLe, ?_, ?_⟩
      · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        exact fun row hrow ↦ ⟨row, hrowLength row hrow, rfl⟩
      · by_cases hzero : rowWords = 0
        · exact Or.inl hzero
        · right
          simpa [not_and, not_forall, hzero, Nat.pos_iff_ne_zero] using hmin
    · rw [hkeys, List.range_eq_range']

/-- **The phase's bytes are its encoding**: bytes `readPhase` accepts are `encodePhase` of the
phase it reads, then the rest. -/
theorem eq_encodePhase_of_readPhase {bytes : Bytes} {ph : PrunedPhase} {rest : Bytes}
    (h : readPhase bytes = some (ph, rest)) : bytes = encodePhase ph ++ rest :=
  (readPhase_eq h).1

/-- **What `readPhase` guarantees** about the phase it reads. -/
theorem phaseRead_of_readPhase {bytes : Bytes} {ph : PrunedPhase} {rest : Bytes}
    (h : readPhase bytes = some (ph, rest)) : PhaseRead ph :=
  (readPhase_eq h).2

theorem readPhases_eq : ∀ count bytes phases rest, readPhases count bytes = some (phases, rest) →
    phases.length = count ∧ (∀ ph ∈ phases, PhaseRead ph) ∧
      bytes = phases.flatMap encodePhase ++ rest
  | 0, bytes, phases, rest, h => by
    simp only [readPhases, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | count + 1, bytes, phases, rest, h => by
    simp only [readPhases, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨ph, input, hph, phases', input', hphases, rfl, rfl⟩ := h
    obtain ⟨rfl, hread⟩ := readPhase_eq hph
    obtain ⟨hlength, hall, rfl⟩ := readPhases_eq count _ _ _ hphases
    refine ⟨by simp [hlength], ?_, by simp⟩
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    exacts [hread, hall q hq]

/-- **The bytes `readProof` accepts are the encoding of what it reads**, and every phase read is
one `readPhase` accepted (`PhaseRead`), at most `wireMaxPhases`, with fewer than `2 ^ 32` stream
elements. -/
theorem readProof_eq {bytes : Bytes} {x : List E × List PrunedPhase}
    (h : readProof bytes = some x) :
    encodePruned x = bytes ∧ x.1.length < 2 ^ 32 ∧ x.2.length ≤ wireMaxPhases ∧
      ∀ ph ∈ x.2, PhaseRead ph := by
  obtain ⟨stream, phases⟩ := x
  simp only [readProof, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
    Option.guard_eq_some', Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨length, input₁, hlength, words, input₂, hwords, phaseCount, input₃, hcount, -, hcountLe,
    phases', input₄, hphases, -, hempty, rfl, rfl⟩ := h
  obtain ⟨hlengthLt, rfl⟩ := readU32_eq_some_iff.1 hlength
  obtain ⟨hwordsLength, rfl⟩ := readWords_eq_some_iff.1 hwords
  obtain ⟨-, rfl⟩ := readU32_eq_some_iff.1 hcount
  obtain ⟨rfl, hall, rfl⟩ := readPhases_eq _ _ _ _ hphases
  have hempty' : input₄ = [] := by simpa using hempty
  subst hempty'
  refine ⟨?_, by simpa using hlengthLt, hcountLe, hall⟩
  simp only [encodePruned, List.length_map, List.length_range, List.append_nil, List.append_assoc,
    stream_flatMap_toBytes length words hwordsLength]

/-- **`readProof` is deterministic**: the bytes it accepts are `encodePruned` of what it reads. -/
theorem toBytes_of_readProof {bytes : Bytes} {x : List E × List PrunedPhase}
    (h : readProof bytes = some x) : encodePruned x = bytes :=
  (readProof_eq h).1


end LeanVM.Wire

end
