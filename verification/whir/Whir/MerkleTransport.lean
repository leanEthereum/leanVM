import Whir.ByteCodec
import Whir.MerkleBinding
import Whir.MerkleLevels
import Mathlib.Data.Nat.Bitwise

/-! Baseline `fiat_shamir/src/merkle.rs:164-236` transport at
`69f5499304a6957f6780c8998999d783bae13302`. The Merkle file is byte-identical
in conditional #552 (`ff6a275304a3b577118b066ddcff83bfafa5998d`); this module
makes no claim about either transcript's Fiat–Shamir mode.

The hash primitive is an explicit executable parameter. Leaves are untagged
little-endian words and pairs are precisely 64 bytes. The source's flat
bottom-up loop is `MerkleLevels.foldLevel`; reconstruction and refanout use
verified binary searches. `open_acceptance_iff` proves reconstruction adds no
rejection, and `open_refines` authenticates each occurrence's exact padded row
at fixed depth. `open_batch_to_ideal` instantiates commitment-time extraction
without assuming a full preimage tree, decoder correctness, or hash injectivity. -/
namespace Whir.MerkleTransport
open Concrete FiatShamirGame MerkleBinding

abbrev Primitive := List Byte → Digest32

def hashing (hash : Primitive) : Hashing (List K) Digest32 (List Byte) where
  hash := hash
  leaf := ByteCodec.wordsBytes
  pair := fun p => List.ofFn (ByteCodec.pairBytes p)
  leaf_injective := ByteCodec.wordsBytes_injective
  pair_injective := fun _ _ h => ByteCodec.pairBytes_injective (List.ofFn_injective h)

abbrev right := MerkleLevels.right
abbrev sibling := MerkleLevels.sibling
abbrev orient := @MerkleLevels.orient
/-- Raw paths list siblings from the leaf upward, unlike the root-first address
index on `MerkleBinding.Opening`. -/
def addressAbove (index : Nat) : Nat → List Bool → List Bool
  | 0, below => below
  | n + 1, below => addressAbove (index / 2) n (right index :: below)

theorem addressAbove_length (index n : Nat) (below : List Bool) :
    (addressAbove index n below).length = n + below.length := by
  induction n generalizing index below with
  | zero => simp [addressAbove]
  | succ n ih => simp [addressAbove, ih]; omega

def wrap {Row D : Type} (index : Nat) : (siblings : List D) →
    {below : List Bool} → Opening Row D below →
      Opening Row D (addressAbove index siblings.length below)
  | [], _, p => p
  | s :: ss, _, p => wrap (index / 2) ss (.node (right index) s p)

def climb {D : Type} (pair : D × D → D) (index : Nat) (current : D) : List D → D
  | [] => current
  | s :: ss => climb pair (index / 2) (pair (orient index current s)) ss

theorem wrap_digest {Row D Bytes : Type} (H : Hashing Row D Bytes)
    (index : Nat) (siblings : List D) {below : List Bool} (p : Opening Row D below) :
    (wrap index siblings p).digest H =
      climb (fun pair => H.hash (H.pair pair)) index (p.digest H) siblings := by
  induction siblings generalizing index below with
  | nil => rfl
  | cons s ss ih =>
    have h := ih (index / 2) (.node (right index) s p)
    change (wrap (index / 2) ss (.node (right index) s p)).digest H = climb _ (index / 2) _ ss
    rw [h]
    congr 2
    simp only [Opening.digest, orient, MerkleLevels.orient, right, MerkleLevels.right]
    by_cases he : index % 2 = 0
    · simp [he]
    · have ho : index % 2 = 1 := by omega
      simp [ho]

theorem wrap_row {Row D : Type} (index : Nat) (siblings : List D)
    {below : List Bool} (p : Opening Row D below) : (wrap index siblings p).row = p.row := by
  induction siblings generalizing index below with
  | nil => rfl
  | cons s ss ih => exact ih (index / 2) (.node (right index) s p)

structure RawPath where
  leafIndex : Nat
  leafData : List K
  path : List Digest32

def RawPath.opening (p : RawPath) :
    Opening (List K) Digest32 (addressAbove p.leafIndex p.path.length []) :=
  wrap p.leafIndex p.path (.leaf p.leafData)

def RawPath.root (hash : Primitive) (p : RawPath) : Digest32 :=
  climb (fun pair => hash (List.ofFn (ByteCodec.pairBytes pair))) p.leafIndex
    (hash (ByteCodec.wordsBytes p.leafData)) p.path

theorem RawPath.opening_digest (hash : Primitive) (p : RawPath) :
    p.opening.digest (hashing hash) = p.root hash :=
  wrap_digest (hashing hash) p.leafIndex p.path (.leaf p.leafData)

theorem RawPath.opening_row (p : RawPath) : p.opening.row = p.leafData :=
  wrap_row p.leafIndex p.path (.leaf p.leafData)

open MerkleLevels

def collect {A B : Type} (f : A → Option B) : List A → Option (List B)
  | [] => some []
  | x :: xs => do
    let y ← f x
    let ys ← collect f xs
    return y :: ys

theorem collect_spec {A B : Type} (f : A → Option B) (xs : List A) (ys : List B) :
    collect f xs = some ys ↔ List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => simp [collect]
  | cons x xs ih =>
    cases ys with
    | nil => simp [collect, Option.bind_eq_some_iff]
    | cons y ys => simp [collect, Option.bind_eq_some_iff, ih, List.forall₂_cons]

def runLevels {D : Type} (pair : D × D → D) :
    Nat → Level D → List D → Option (Level D × List (Level D) × List D)
  | 0, nodes, supplied => some (nodes, [], supplied)
  | n + 1, nodes, supplied => do
    let (parents, known, rest) ← foldLevel pair nodes supplied
    let (final, levels, remainder) ← runLevels pair n parents rest
    return (final, known :: levels, remainder)

def reconstruct {D : Type} (index : Nat) : List (Level D) → Option (List D)
  | [] => some []
  | level :: levels => do
    let s ← binaryLookup (sibling index) level
    let ss ← reconstruct (index / 2) levels
    return s :: ss

theorem reconstruct_length {D : Type} (index : Nat) (levels : List (Level D))
    (siblings : List D) (h : reconstruct index levels = some siblings) :
    siblings.length = levels.length := by
  induction levels generalizing index siblings with
  | nil => simp [reconstruct] at h; subst siblings; rfl
  | cons l ls ih =>
    simp [reconstruct, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, ss, hss, he⟩ := h
    cases he
    simp [ih _ _ hss]

theorem runLevels_length {D : Type} (pair : D × D → D) (n : Nat)
    (nodes : Level D) (supplied : List D) (final : Level D)
    (levels : List (Level D)) (rest : List D)
    (h : runLevels pair n nodes supplied = some (final, levels, rest)) :
    levels.length = n := by
  induction n generalizing nodes supplied final levels rest with
  | zero => simp [runLevels] at h; rcases h with ⟨rfl,rfl,rfl⟩; rfl
  | succ n ih =>
    simp [runLevels, Option.bind_eq_some_iff] at h
    obtain ⟨parents, known, remain, hf, ls, hr, rfl⟩ := h
    simp [ih _ _ _ _ _ hr]

def sortedUnique (queries : List Nat) : List Nat := queries.toFinset.sort (· ≤ ·)

theorem sortedUnique_strict (queries : List Nat) :
    (sortedUnique queries).Pairwise (· < ·) :=
  (Finset.sortedLT_sort queries.toFinset).pairwise

structure PrunedMerklePaths where
  leafData : List (List K)
  siblingHashes : List Digest32

def leafTable (queries : List Nat) (rows : List (List K)) : Level (List K) :=
  (sortedUnique queries).zip rows

def leafNodes (hash : Primitive) (leafWords : Nat) (table : Level (List K)) :
    Level Digest32 :=
  table.map fun (i, row) => (i, hash (ByteCodec.wordsBytes (leafImage 0 leafWords row)))

def distinctPaths (leafWords : Nat) (levels : List (Level Digest32))
    (table : Level (List K)) : Option (Level RawPath) :=
  collect (fun (i, row) => do
    let path ← reconstruct i levels
    return (i, ⟨i, leafImage 0 leafWords row, path⟩)) table

/-- Actual octopus transport: sorted unique leaves, bottom-up adjacent pairing,
one sibling only for a missing child, exact exhaustion and root comparison,
then known-level path lookup followed by original-order refanout. -/
def PrunedMerklePaths.open (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) : Option (List RawPath) := do
  if numLeaves = 0 ∨ 2 ^ numLeaves.log2 ≠ numLeaves ∨ queries = [] then none
  else if (sortedUnique queries).length ≠ proof.leafData.length ∨ rowWords > leafWords then none
  else if ¬ ∀ row ∈ proof.leafData, row.length = rowWords then none
  else if ∃ q ∈ queries, numLeaves ≤ q then none
  else do
    let table := leafTable queries proof.leafData
    let nodes := leafNodes hash leafWords table
    let (final, levels, rest) ← runLevels
      (fun p => hash (List.ofFn (ByteCodec.pairBytes p))) numLeaves.log2 nodes proof.siblingHashes
    if rest ≠ [] then none
    else do
      let (_, computed) ← final.head?
      if computed ≠ root then none
      else do
        let distinct ← distinctPaths leafWords levels table
        collect (fun q => binaryLookup q distinct) queries

theorem collect_mem {A B : Type} (f : A → Option B) (xs : List A) (ys : List B)
    (h : collect f xs = some ys) {y : B} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  have hr := (collect_spec f xs ys).mp h
  clear h
  induction hr with
  | nil => simp at hy
  | @cons x y xs ys hxy hrest ih =>
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨x, by simp, hxy⟩
    · obtain ⟨z, hz, hf⟩ := ih hy
      exact ⟨z, by simp [hz], hf⟩

theorem leafTable_sorted (queries : List Nat) (rows : List (List K))
    (count : (sortedUnique queries).length = rows.length) :
    Sorted (leafTable queries rows) := by
  have he : (leafTable queries rows).map Prod.fst = sortedUnique queries := by
    simp [leafTable, List.map_fst_zip, count]
  have hp := sortedUnique_strict queries
  rw [← he, List.pairwise_map] at hp
  exact hp

theorem leafNodes_sorted (hash : Primitive) (leafWords : Nat) (table : Level (List K))
    (hs : Sorted table) : Sorted (leafNodes hash leafWords table) := by
  simpa [Sorted, leafNodes, List.pairwise_map] using hs

theorem leafTable_mem {queries : List Nat} {rows : List (List K)}
    {q : Nat} {row : List K} (h : (q,row) ∈ leafTable queries rows) :
    q ∈ queries ∧ row ∈ rows := by
  have hp := List.of_mem_zip h
  simpa [sortedUnique] using hp

structure OpenConditions (proof : PrunedMerklePaths) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) : Prop where
  positive : numLeaves ≠ 0
  power : 2 ^ numLeaves.log2 = numLeaves
  queries_nonempty : queries ≠ []
  count : (sortedUnique queries).length = proof.leafData.length
  fits : rowWords ≤ leafWords
  widths : ∀ row ∈ proof.leafData, row.length = rowWords
  range : ∀ q ∈ queries, q < numLeaves

theorem open_spec (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath) :
    proof.open hash root numLeaves queries rowWords leafWords = some output ↔
      OpenConditions proof numLeaves queries rowWords leafWords ∧
      ∃ final levels index distinct,
        runLevels (fun p => hash (List.ofFn (ByteCodec.pairBytes p)))
          numLeaves.log2 (leafNodes hash leafWords (leafTable queries proof.leafData))
          proof.siblingHashes = some (final, levels, []) ∧
        final.head? = some (index, root) ∧
        distinctPaths leafWords levels (leafTable queries proof.leafData) = some distinct ∧
        collect (fun q => binaryLookup q distinct) queries = some output := by
  simp only [PrunedMerklePaths.open]
  simp [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨h0, hp, hq⟩, ⟨hc, hf⟩, hw, hr, h⟩
    exact ⟨⟨h0, hp, hq, hc, hf, hw, hr⟩, h⟩
  · rintro ⟨h, rest⟩
    exact ⟨⟨h.positive, h.power, h.queries_nonempty⟩, ⟨h.count, h.fits⟩,
      h.widths, h.range, rest⟩

theorem runLevels_range {D : Type} (pair : D × D → D) (n bound : Nat)
    (nodes : Level D) (supplied : List D) (final : Level D)
    (levels : List (Level D)) (rest : List D)
    (h : runLevels pair n nodes supplied = some (final, levels, rest))
    (bounded : ∀ x ∈ nodes, x.1 < 2 ^ n * bound) :
    ∀ x ∈ final, x.1 < bound := by
  induction n generalizing nodes supplied final levels rest with
  | zero =>
    simp [runLevels] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    simpa using bounded
  | succ n ih =>
    simp [runLevels, Option.bind_eq_some_iff] at h
    obtain ⟨parents, known, remain, hf, ls, hr, rfl⟩ := h
    apply ih _ _ _ _ _ hr
    intro p hp
    obtain ⟨x, hx, he⟩ := (foldLevel_spec pair nodes supplied hf).parent_source p hp
    have hb := bounded x hx
    rw [pow_succ, Nat.mul_right_comm, Nat.mul_comm _ 2] at hb
    rw [he]
    omega

theorem runLevels_nonempty {D : Type} (pair : D × D → D) (n : Nat)
    (nodes : Level D) (supplied : List D) (final : Level D)
    (levels : List (Level D)) (rest : List D)
    (h : runLevels pair n nodes supplied = some (final, levels, rest))
    (nonempty : nodes ≠ []) : final ≠ [] := by
  induction n generalizing nodes supplied final levels rest with
  | zero =>
    simp [runLevels] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    exact nonempty
  | succ n ih =>
    simp [runLevels, Option.bind_eq_some_iff] at h
    obtain ⟨parents, known, remain, hf, ls, hr, rfl⟩ := h
    exact ih _ _ _ _ _ hr ((foldLevel_spec pair nodes supplied hf).nonempty nonempty)

theorem runLevels_sorted {D : Type} (pair : D × D → D) (n : Nat)
    (nodes : Level D) (supplied : List D) (final : Level D)
    (levels : List (Level D)) (rest : List D)
    (h : runLevels pair n nodes supplied = some (final, levels, rest))
    (sorted : Sorted nodes) : Sorted final ∧ ∀ level ∈ levels, Sorted level := by
  induction n generalizing nodes supplied final levels rest with
  | zero =>
    simp [runLevels] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    exact ⟨sorted, by simp⟩
  | succ n ih =>
    simp [runLevels, Option.bind_eq_some_iff] at h
    obtain ⟨parents, known, remain, hf, ls, hr, rfl⟩ := h
    have hfacts := foldLevel_invariant pair sorted hf
    obtain ⟨hs, hl⟩ := ih _ _ _ _ _ hr hfacts.parents_sorted
    exact ⟨hs, by simpa using And.intro hfacts.known_sorted hl⟩

/-- Every initial node has the exact known-table siblings, and their bottom-up
fold is a node of the final level. This also proves reconstruction cannot fail. -/
theorem runLevels_path {D : Type} (pair : D × D → D) (n : Nat)
    (nodes : Level D) (supplied : List D) (final : Level D)
    (levels : List (Level D)) (rest : List D)
    (h : runLevels pair n nodes supplied = some (final, levels, rest))
    (sorted : Sorted nodes) (index : Nat) (digest : D)
    (start : lookup index nodes = some digest) :
    ∃ path lastIndex, reconstruct index levels = some path ∧
      lookup lastIndex final = some (climb pair index digest path) := by
  induction n generalizing nodes supplied final levels rest index digest with
  | zero =>
    simp [runLevels] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    exact ⟨[], index, rfl, start⟩
  | succ n ih =>
    simp [runLevels, Option.bind_eq_some_iff] at h
    obtain ⟨parents, known, remain, hf, ls, hr, rfl⟩ := h
    have hfacts := foldLevel_invariant pair sorted hf
    obtain ⟨s, hs, hp⟩ := hfacts.edge start
    obtain ⟨path, last, hpath, hlast⟩ :=
      ih _ _ _ _ _ hr hfacts.parents_sorted (index / 2) _ hp
    exact ⟨s :: path, last, by
      simp [reconstruct, binaryLookup_eq_lookup _ _ hfacts.known_sorted, hs, hpath], hlast⟩

theorem sorted_singleton_of_range {D : Type} (nodes : Level D)
    (sorted : Sorted nodes) (bounded : ∀ x ∈ nodes, x.1 < 1)
    (nonempty : nodes ≠ []) : ∃ digest, nodes = [(0, digest)] := by
  cases nodes with
  | nil => contradiction
  | cons x xs =>
    have hx := bounded x (by simp)
    have hx0 : x.1 = 0 := by omega
    cases xs with
    | nil => exact ⟨x.2, by cases x; simp_all⟩
    | cons y ys =>
      have hy := bounded y (by simp)
      have hxy := (List.pairwise_cons.mp sorted).1 y (by simp)
      omega

theorem root_level (hash : Primitive) (proof : PrunedMerklePaths)
    (numLeaves : Nat) (queries : List Nat) (rowWords leafWords : Nat)
    (conditions : OpenConditions proof numLeaves queries rowWords leafWords)
    (final : Level Digest32) (levels : List (Level Digest32)) (rest : List Digest32)
    (run : runLevels (fun p => hash (List.ofFn (ByteCodec.pairBytes p)))
      numLeaves.log2 (leafNodes hash leafWords (leafTable queries proof.leafData))
      proof.siblingHashes = some (final, levels, rest))
    (index : Nat) (root : Digest32) (head : final.head? = some (index, root)) :
    final = [(0,root)] ∧ ∀ level ∈ levels, Sorted level := by
  have hs := leafNodes_sorted hash leafWords _ (leafTable_sorted _ _ conditions.count)
  obtain ⟨hf, hl⟩ := runLevels_sorted _ _ _ _ _ _ _ run hs
  have hb : ∀ x ∈ final, x.1 < 1 := by
    apply runLevels_range _ _ 1 _ _ _ _ _ run
    intro x hx
    obtain ⟨⟨q,row⟩, hmem, rfl⟩ := List.mem_map.mp hx
    have hq := conditions.range q (leafTable_mem hmem).1
    simpa [conditions.power] using hq
  have hn : final ≠ [] := by intro he; simp [he] at head
  obtain ⟨digest, he⟩ := sorted_singleton_of_range final hf hb hn
  subst final
  simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at head
  exact ⟨by rw [head.2], hl⟩

theorem leafNodes_lookup (hash : Primitive) (leafWords : Nat) (table : Level (List K))
    (index : Nat) (row : List K) (h : lookup index table = some row) :
    lookup index (leafNodes hash leafWords table) =
      some (hash (ByteCodec.wordsBytes (leafImage 0 leafWords row))) := by
  change lookup index (table.map (fun x =>
    (x.1, hash (ByteCodec.wordsBytes (leafImage 0 leafWords x.2))))) = _
  rw [lookup_map (fun row => hash (ByteCodec.wordsBytes (leafImage 0 leafWords row))) index table, h]
  rfl

theorem distinctPaths_mem (leafWords : Nat) (levels : List (Level Digest32))
    (table : Level (List K)) (distinct : Level RawPath)
    (decoded : distinctPaths leafWords levels table = some distinct)
    (index : Nat) (p : RawPath) (member : (index,p) ∈ distinct) :
    ∃ row, (index,row) ∈ table ∧ p.leafIndex = index ∧
      p.leafData = leafImage 0 leafWords row ∧ reconstruct index levels = some p.path := by
  obtain ⟨⟨i,row⟩, hm, he⟩ := collect_mem _ table distinct decoded member
  simp [Option.bind_eq_some_iff] at he
  obtain ⟨path, hpath, hi, hp⟩ := he
  subst index
  subst p
  exact ⟨row, hm, rfl, rfl, hpath⟩

theorem collect_map {A B C : Type} (f : A → Option B) (g : A → C) (k : B → C)
    (xs : List A) (ys : List B) (h : collect f xs = some ys)
    (preserves : ∀ x y, f x = some y → g x = k y) : xs.map g = ys.map k := by
  have hr := (collect_spec _ _ _).mp h
  clear h
  induction hr with
  | nil => rfl
  | cons hxy _ ih => simp [preserves _ _ hxy, ih]

theorem distinctPaths_keys (leafWords : Nat) (levels : List (Level Digest32))
    (table : Level (List K)) (distinct : Level RawPath)
    (decoded : distinctPaths leafWords levels table = some distinct) :
    distinct.map Prod.fst = table.map Prod.fst := by
  symm
  apply collect_map _ Prod.fst Prod.fst _ _ decoded
  intro x y h
  simp [Option.bind_eq_some_iff] at h
  obtain ⟨path, hp, he⟩ := h
  exact congrArg Prod.fst he

theorem distinctPaths_sorted (leafWords : Nat) (levels : List (Level Digest32))
    (table : Level (List K)) (distinct : Level RawPath)
    (decoded : distinctPaths leafWords levels table = some distinct)
    (sorted : Sorted table) : Sorted distinct := by
  have hk := distinctPaths_keys leafWords levels table distinct decoded
  change distinct.Pairwise (fun x y => x.1 < y.1)
  rw [← List.pairwise_map]
  rw [hk, List.pairwise_map]
  exact sorted

/-- Occurrence-indexed refinement: returned order and duplicates are unchanged;
the row is precisely the row at this sorted-unique slot, with the announced
zero prefix; every raw path has the fixed tree height and hashes to the root. -/
def Refines (hash : Primitive) (proof : PrunedMerklePaths) (root : Digest32)
    (numLeaves : Nat) (queries : List Nat) (rowWords leafWords : Nat)
    (index : Nat) (p : RawPath) : Prop :=
  ∃ row, lookup index (leafTable queries proof.leafData) = some row ∧
    row.length = rowWords ∧ p.leafIndex = index ∧
    p.leafData = leafImage 0 leafWords row ∧ p.leafData.length = leafWords ∧
    p.path.length = numLeaves.log2 ∧ p.root hash = root

theorem open_refines (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath)
    (accepted : proof.open hash root numLeaves queries rowWords leafWords = some output) :
    List.Forall₂ (Refines hash proof root numLeaves queries rowWords leafWords) queries output := by
  obtain ⟨conditions, final, levels, index, distinct, run, head, hd, hout⟩ :=
    (open_spec hash proof root numLeaves queries rowWords leafWords output).mp accepted
  obtain ⟨hroot, hlevels⟩ := root_level hash proof _ _ _ _ conditions _ _ _ run index root head
  have ht := leafTable_sorted queries proof.leafData conditions.count
  have hn := leafNodes_sorted hash leafWords _ ht
  apply ((collect_spec _ _ _).mp hout).imp
  intro q p hp
  rw [binaryLookup_eq_lookup _ _ (distinctPaths_sorted _ _ _ _ hd ht)] at hp
  obtain ⟨row, hm, hindex, hdata, hpath⟩ :=
    distinctPaths_mem leafWords levels _ distinct hd q p (lookup_mem hp)
  have hrow := lookup_of_mem ht hm
  have hwidth := conditions.widths row (leafTable_mem hm).2
  have hlength := (reconstruct_length q levels p.path hpath).trans
    (runLevels_length _ _ _ _ _ _ _ run)
  obtain ⟨path, last, hrec, hlast⟩ := runLevels_path _ _ _ _ _ _ _ run hn q _
    (leafNodes_lookup hash leafWords _ q row hrow)
  have hsame : path = p.path := Option.some.inj (hrec.symm.trans hpath)
  rw [hsame, hroot] at hlast
  simp only [lookup] at hlast
  split at hlast
  · have ha := Option.some.inj hlast
    refine ⟨row, hrow, hwidth, hindex, hdata, ?_, hlength, ?_⟩
    · rw [hdata]; exact leafImage_length 0 leafWords row (hwidth ▸ conditions.fits)
    · simpa [RawPath.root, hindex, hdata] using ha.symm
  · contradiction

theorem leafTable_nonempty (queries : List Nat) (rows : List (List K))
    (nonempty : queries ≠ []) (count : (sortedUnique queries).length = rows.length) :
    leafTable queries rows ≠ [] := by
  have hsort : sortedUnique queries ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp [sortedUnique] at hlen
    exact nonempty hlen
  intro h
  rcases List.zip_eq_nil_iff.mp h with he | he
  · exact hsort he
  · have : (sortedUnique queries).length = 0 := by simpa [he] using count
    exact hsort (List.length_eq_zero_iff.mp this)

/-- The root-level nonemptiness/index fact is derived before accessing the head;
the optional head access in `open` adds no acceptance restriction. -/
theorem levels_singleton (hash : Primitive) (proof : PrunedMerklePaths)
    (numLeaves : Nat) (queries : List Nat) (rowWords leafWords : Nat)
    (conditions : OpenConditions proof numLeaves queries rowWords leafWords)
    (final : Level Digest32) (levels : List (Level Digest32)) (rest : List Digest32)
    (run : runLevels (fun p => hash (List.ofFn (ByteCodec.pairBytes p)))
      numLeaves.log2 (leafNodes hash leafWords (leafTable queries proof.leafData))
      proof.siblingHashes = some (final, levels, rest)) :
    ∃ root, final = [(0,root)] := by
  have hs := leafNodes_sorted hash leafWords _ (leafTable_sorted _ _ conditions.count)
  have hn : leafNodes hash leafWords (leafTable queries proof.leafData) ≠ [] := by
    simpa [leafNodes] using
      leafTable_nonempty queries proof.leafData conditions.queries_nonempty conditions.count
  have hf := runLevels_nonempty _ _ _ _ _ _ _ run hn
  apply sorted_singleton_of_range final (runLevels_sorted _ _ _ _ _ _ _ run hs).1 _ hf
  apply runLevels_range _ _ 1 _ _ _ _ _ run
  intro x hx
  obtain ⟨⟨q,row⟩, hmem, rfl⟩ := List.mem_map.mp hx
  simpa [conditions.power] using conditions.range q (leafTable_mem hmem).1

/-- Exact Rust raw sibling coordinate: level `j`, index `(leaf >> j) ^ 1`.
`sibling` is parity arithmetic for xor-one and division by `2^j` is right shift. -/
theorem reconstruct_get {D : Type} (index : Nat) (levels : List (Level D))
    (siblings : List D) (h : reconstruct index levels = some siblings) (j : Nat) :
    siblings[j]? = (levels[j]?).bind
      (fun level => binaryLookup (sibling (index / 2 ^ j)) level) := by
  induction levels generalizing index siblings j with
  | nil => simp [reconstruct] at h; subst siblings; simp
  | cons l ls ih =>
    simp [reconstruct, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, ss, hss, rfl⟩ := h
    cases j with
    | zero => simpa using hs.symm
    | succ j =>
      have he := ih (index / 2) ss hss j
      simpa [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using he

theorem collect_total {A B : Type} (f : A → Option B) (xs : List A)
    (total : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, collect f xs = some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨y,hy⟩ := total x (by simp)
    obtain ⟨ys,hys⟩ := ih (fun z hz => total z (by simp [hz]))
    exact ⟨y::ys, by simp [collect,hy,hys]⟩

/-- Once the baseline guards, exact sibling exhaustion, and root test pass,
known-level reconstruction and duplicate refanout cannot reject. There is no
extra independent-path verification or stricter acceptance set. -/
theorem open_complete (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat)
    (conditions : OpenConditions proof numLeaves queries rowWords leafWords)
    (final : Level Digest32) (levels : List (Level Digest32))
    (run : runLevels (fun p => hash (List.ofFn (ByteCodec.pairBytes p)))
      numLeaves.log2 (leafNodes hash leafWords (leafTable queries proof.leafData))
      proof.siblingHashes = some (final, levels, []))
    (index : Nat) (head : final.head? = some (index,root)) :
    ∃ output, proof.open hash root numLeaves queries rowWords leafWords = some output := by
  have ht := leafTable_sorted queries proof.leafData conditions.count
  have hn := leafNodes_sorted hash leafWords _ ht
  have total : ∀ x ∈ leafTable queries proof.leafData, ∃ path,
      reconstruct x.1 levels = some path := by
    intro x hx
    obtain ⟨path,last,hp,hl⟩ := runLevels_path _ _ _ _ _ _ _ run hn x.1 _
      (leafNodes_lookup hash leafWords _ x.1 x.2 (lookup_of_mem ht hx))
    exact ⟨path,hp⟩
  have hd : ∃ distinct,
      distinctPaths leafWords levels (leafTable queries proof.leafData) = some distinct := by
    apply collect_total
    intro x hx
    obtain ⟨path,hp⟩ := total x hx
    exact ⟨(x.1,⟨x.1,leafImage 0 leafWords x.2,path⟩), by simp [hp]⟩
  obtain ⟨distinct,hd⟩ := hd
  have hs := distinctPaths_sorted _ _ _ _ hd ht
  have hk := distinctPaths_keys _ _ _ _ hd
  have hkeys : distinct.map Prod.fst = sortedUnique queries := by
    rw [hk]
    exact List.map_fst_zip (Nat.le_of_eq conditions.count)
  obtain ⟨output,hout⟩ := collect_total (fun q => binaryLookup q distinct) queries (by
    intro q hq
    have hmem : q ∈ distinct.map Prod.fst := by simpa [hkeys, sortedUnique] using hq
    obtain ⟨⟨i,p⟩,hm,he⟩ := List.mem_map.mp hmem
    dsimp at he
    subst i
    exact ⟨p, (binaryLookup_eq_lookup _ _ hs).trans (lookup_of_mem hs hm)⟩)
  refine ⟨output, (open_spec _ _ _ _ _ _ _ _).mpr ?_⟩
  exact ⟨conditions,final,levels,index,distinct,run,head,hd,hout⟩

theorem open_acceptance_iff (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) :
    (∃ output, proof.open hash root numLeaves queries rowWords leafWords = some output) ↔
      OpenConditions proof numLeaves queries rowWords leafWords ∧
      ∃ final levels index,
        runLevels (fun p => hash (List.ofFn (ByteCodec.pairBytes p)))
          numLeaves.log2 (leafNodes hash leafWords (leafTable queries proof.leafData))
          proof.siblingHashes = some (final, levels, []) ∧
        final.head? = some (index,root) := by
  constructor
  · rintro ⟨output,accepted⟩
    obtain ⟨conditions,final,levels,index,distinct,run,head,hd,hout⟩ :=
      (open_spec _ _ _ _ _ _ _ _).mp accepted
    exact ⟨conditions,final,levels,index,run,head⟩
  · rintro ⟨conditions,final,levels,index,run,head⟩
    exact open_complete _ _ _ _ _ _ _ conditions final levels run index head

theorem forall₂_mem_right {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (h : List.Forall₂ R xs ys) {y : B} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => simp at hy
  | @cons x y xs ys hxy hrest ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x,by simp,hxy⟩
    · obtain ⟨z,hz,hr⟩ := ih hy
      exact ⟨z,by simp [hz],hr⟩

/-- Commitment-time extraction for the executable flat decoder. The ideal
oracle depends only on the commitment-time hash-input table and root, not the
later query batch. A failure is an actual collision or fresh targeted preimage.
No semantic-decoder or codec bridge is assumed. -/
theorem open_batch_to_ideal (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath)
    (accepted : proof.open hash root numLeaves queries rowWords leafWords = some output)
    (table : Finset (List Byte)) (fallback : List K) :
    (∀ p ∈ output, p.leafData = idealRow (hashing hash) table root fallback
      (addressAbove p.leafIndex numLeaves.log2 [])) ∨
    Collision (hashing hash) table ∨
      ∃ p ∈ output, FreshHit (hashing hash) table root (p.opening.inputs (hashing hash)) := by
  classical
  have refined := open_refines _ _ _ _ _ _ _ _ accepted
  have auth : ∀ p ∈ output, p.path.length = numLeaves.log2 ∧ p.root hash = root := by
    intro p hp
    obtain ⟨q,hq,row,hr,hw,hi,hd,hl,hdepth,hroot⟩ := forall₂_mem_right refined hp
    exact ⟨hdepth,hroot⟩
  let I := {p : RawPath // p ∈ output}
  have batch := batch_to_ideal (hashing hash) table root fallback
    (fun p : I => addressAbove p.val.leafIndex p.val.path.length [])
    (fun p => p.val.opening)
    (fun p => (p.val.opening_digest hash).trans (auth p.val p.property).2)
  rcases batch with hi | hc | hf
  · left
    intro p hp
    have he := hi ⟨p,hp⟩
    simpa only [RawPath.opening_row, (auth p hp).1] using he
  · exact Or.inr (Or.inl hc)
  · obtain ⟨p,hp⟩ := hf
    exact Or.inr (Or.inr ⟨p.val,p.property,hp⟩)

theorem power_guard_iff (n : Nat) :
    (n ≠ 0 ∧ 2 ^ n.log2 = n) ↔ n.isPowerOfTwo := by
  constructor
  · intro h; exact ⟨n.log2,h.2.symm⟩
  · rintro ⟨k,rfl⟩
    simp

theorem sibling_eq_xor (index : Nat) : sibling index = index ^^^ 1 := by
  by_cases he : index % 2 = 0
  · simp [sibling, MerkleLevels.sibling, he, Nat.xor_one_of_even (Nat.even_iff.mpr he)]
  · have ho : Odd index := Nat.odd_iff.mpr (by omega)
    simp [sibling, MerkleLevels.sibling, he, Nat.xor_one_of_odd ho]

theorem reconstruct_rust_coordinate {D : Type} (index : Nat) (levels : List (Level D))
    (siblings : List D) (h : reconstruct index levels = some siblings) (j : Nat) :
    siblings[j]? = (levels[j]?).bind
      (fun level => binaryLookup ((index >>> j) ^^^ 1) level) := by
  simpa [Nat.shiftRight_eq_div_pow, sibling_eq_xor] using reconstruct_get index levels siblings h j

/-- The range guard is exactly Rust's sorted-last check, not a stricter test. -/
theorem range_guard_iff (queries : List Nat) (n : Nat) :
    (∀ q ∈ queries, q < n) ↔ ∀ q ∈ (sortedUnique queries).getLast?, q < n := by
  constructor
  · intro h q hq
    exact h q (by simpa [sortedUnique] using List.mem_of_mem_getLast? hq)
  · intro h q hq
    have hm : q ∈ sortedUnique queries := by simpa [sortedUnique] using hq
    have le := (Finset.pairwise_sort queries.toFinset (· ≤ ·)).rel_getLast hm
    exact lt_of_le_of_lt le (h _ (List.getLast_mem_getLast? (List.ne_nil_of_mem hm)))

/-- The returned list follows one sorted-unique lookup table. Equal queries
therefore return literally the same raw path, not just equal authenticated rows. -/
theorem open_refanout (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath)
    (accepted : proof.open hash root numLeaves queries rowWords leafWords = some output) :
    ∃ distinct : Level RawPath, Sorted distinct ∧
      distinct.map Prod.fst = sortedUnique queries ∧
      List.Forall₂ (fun q p => binaryLookup q distinct = some p) queries output := by
  obtain ⟨conditions,final,levels,index,distinct,run,head,hd,hout⟩ :=
    (open_spec _ _ _ _ _ _ _ _).mp accepted
  refine ⟨distinct,distinctPaths_sorted _ _ _ _ hd (leafTable_sorted _ _ conditions.count), ?_,
    (collect_spec _ _ _).mp hout⟩
  rw [distinctPaths_keys _ _ _ _ hd]
  exact List.map_fst_zip (Nat.le_of_eq conditions.count)

theorem open_repeated_query (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath)
    (accepted : proof.open hash root numLeaves queries rowWords leafWords = some output)
    (i j : Nat) (hi : i < queries.length) (hj : j < queries.length)
    (hi' : i < output.length) (hj' : j < output.length)
    (same : queries[i] = queries[j]) : output[i] = output[j] := by
  obtain ⟨distinct,hs,hkeys,hr⟩ := open_refanout _ _ _ _ _ _ _ _ accepted
  have a := hr.get hi hi'
  have b := hr.get hj hj'
  simp only [List.get_eq_getElem] at a b
  rw [same] at a
  exact Option.some.inj (a.symm.trans b)

def RawPath.fixedOpening (p : RawPath) (height : Nat) (depth : p.path.length = height) :
    Opening (List K) Digest32 (addressAbove p.leafIndex height []) :=
  depth ▸ p.opening

theorem RawPath.fixedOpening_row (p : RawPath) (height : Nat)
    (depth : p.path.length = height) : (p.fixedOpening height depth).row = p.leafData := by
  subst height
  exact p.opening_row

theorem RawPath.fixedOpening_digest (hash : Primitive) (p : RawPath) (height : Nat)
    (depth : p.path.length = height) :
    (p.fixedOpening height depth).digest (hashing hash) = p.root hash := by
  subst height
  exact p.opening_digest hash

/-- Successful flat decoding supplies the semantic `Opening` itself, at exactly
the commitment's fixed depth. This is a checked output of the parser, not an
assumed correctness bridge. -/
theorem open_authenticated (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath)
    (accepted : proof.open hash root numLeaves queries rowWords leafWords = some output) :
    ∀ p ∈ output, ∃ path : Opening (List K) Digest32
        (addressAbove p.leafIndex numLeaves.log2 []),
      path.row = p.leafData ∧ path.digest (hashing hash) = root := by
  intro p hp
  obtain ⟨q,hq,row,hr,hw,hi,hd,hl,hdepth,hroot⟩ :=
    forall₂_mem_right (open_refines _ _ _ _ _ _ _ _ accepted) hp
  exact ⟨p.fixedOpening _ hdepth, p.fixedOpening_row _ hdepth,
    (p.fixedOpening_digest hash _ hdepth).trans hroot⟩

namespace Commitments

/-- The exposed primitive-input table is captured on the root's first
registration. Repeated roots never replace this snapshot with a later table. -/
structure Snapshot where
  table : Finset (List Byte)
  fallback : List K

abbrev Registry := List (Digest32 × Snapshot)

def lookup (root : Digest32) : Registry → Option Snapshot
  | [] => none
  | (r,s) :: rest => if root = r then some s else lookup root rest

def register (registry : Registry) (root : Digest32) (snapshot : Snapshot) : Registry :=
  match lookup root registry with
  | some _ => registry
  | none => (root,snapshot) :: registry

def registerMany (registry : Registry) (announcements : Registry) : Registry :=
  announcements.foldl (fun registry entry => register registry entry.1 entry.2) registry

theorem register_first (registry : Registry) (root : Digest32) (snapshot : Snapshot)
    (fresh : lookup root registry = none) :
    lookup root (register registry root snapshot) = some snapshot := by
  simp [register, fresh, lookup]

theorem register_repeat (registry : Registry) (root : Digest32) (old new : Snapshot)
    (known : lookup root registry = some old) : register registry root new = registry := by
  simp [register,known]

/-- Any already registered root keeps the exact original table and fallback,
including when the same root is seen from another cloned transcript. -/
theorem register_preserves (registry : Registry) (root other : Digest32)
    (snapshot proposed : Snapshot) (known : lookup root registry = some snapshot) :
    lookup root (register registry other proposed) = some snapshot := by
  unfold register
  cases h : lookup other registry with
  | some s => exact known
  | none =>
    have ne : root ≠ other := by intro he; subst other; simp [known] at h
    simp [lookup,ne,known]

theorem registerMany_preserves (registry announcements : Registry) (root : Digest32)
    (snapshot : Snapshot) (known : lookup root registry = some snapshot) :
    lookup root (registerMany registry announcements) = some snapshot := by
  induction announcements generalizing registry with
  | nil => exact known
  | cons entry rest ih =>
    exact ih _ (register_preserves registry root entry.1 snapshot entry.2 known)

/-- One immutable oracle indexed by the whole root-first address. Depth is
part of the address: untagged leaf/pair hashing does not justify identifying
different-depth openings of the same digest. -/
noncomputable def oracle (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (address : List Bool) : List K :=
  idealRow (hashing hash) snapshot.table root snapshot.fallback address

noncomputable def row (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height index : Nat) : List K := oracle hash snapshot root (addressAbove index height [])

/-- Total shape-normalized *ideal* row, not an additional verifier check.
An inadmissibly sized extracted row receives the fixed zero default. An
accepted opening has the announced width, so its row is never changed here
outside the explicit collision/fresh-hit games. Initial rows stay RAW: the
protocol's first-level fold, not this registry, performs the lane reversal. -/
noncomputable def baseRow (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height index width : Nat) : List K :=
  let raw := row hash snapshot root height index
  if raw.length = width then raw else List.replicate width 0

theorem baseRow_length (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height index width : Nat) : (baseRow hash snapshot root height index width).length = width := by
  dsimp only [baseRow]
  split <;> simp_all

noncomputable def intermediateRow (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height index width : Nat) : List E :=
  (ByteCodec.wordsToFields (baseRow hash snapshot root height index (3 * width))).getD
    (List.replicate width E.zero)

theorem intermediateRow_decoded (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height index width : Nat) :
    ByteCodec.wordsToFields (baseRow hash snapshot root height index (3 * width)) =
      some (intermediateRow hash snapshot root height index width) ∧
    (intermediateRow hash snapshot root height index width).length = width := by
  obtain ⟨fields,hf,hlen⟩ := ByteCodec.wordsToFields_total
    (baseRow hash snapshot root height index (3 * width)) width
    (baseRow_length hash snapshot root height index (3 * width))
  simp [intermediateRow,hf,hlen]

noncomputable def baseOracle (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width : Nat) : Array (Array K) :=
  Array.ofFn (fun q : Fin numRows => (baseRow hash snapshot root height q.val width).toArray)

noncomputable def intermediateOracle (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width : Nat) : Array (Array E) :=
  Array.ofFn (fun q : Fin numRows => (intermediateRow hash snapshot root height q.val width).toArray)

theorem baseOracle_size (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width : Nat) : (baseOracle hash snapshot root height numRows width).size = numRows := by
  simp [baseOracle]

theorem intermediateOracle_size (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width : Nat) :
    (intermediateOracle hash snapshot root height numRows width).size = numRows := by
  simp [intermediateOracle]

theorem baseOracle_get (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width index : Nat) (bound : index < numRows) :
    (baseOracle hash snapshot root height numRows width)[index]! =
      (baseRow hash snapshot root height index width).toArray := by
  simp [baseOracle, bound]

theorem intermediateOracle_get (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width index : Nat) (bound : index < numRows) :
    (intermediateOracle hash snapshot root height numRows width)[index]! =
      (intermediateRow hash snapshot root height index width).toArray := by
  simp [intermediateOracle, bound]

theorem baseOracle_row_size (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width index : Nat) (bound : index < numRows) :
    ((baseOracle hash snapshot root height numRows width)[index]!).size = width := by
  rw [baseOracle_get _ _ _ _ _ _ _ bound]
  simpa using baseRow_length hash snapshot root height index width

theorem intermediateOracle_row_size (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width index : Nat) (bound : index < numRows) :
    ((intermediateOracle hash snapshot root height numRows width)[index]!).size = width := by
  rw [intermediateOracle_get _ _ _ _ _ _ _ bound]
  simpa using (intermediateRow_decoded hash snapshot root height index width).2

def OpenBad (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (output : List RawPath) : Prop :=
  Collision (hashing hash) snapshot.table ∨
    ∃ p ∈ output, FreshHit (hashing hash) snapshot.table root (p.opening.inputs (hashing hash))

/-- Later accepted actual flat openings are bound to the frozen snapshot.
The registry may have grown arbitrarily; no equality between independently
extracted full oracles or later exposed tables is assumed. -/
theorem open_frozen (hash : Primitive) (registry announcements : Registry)
    (root : Digest32) (snapshot : Snapshot)
    (committed : lookup root registry = some snapshot)
    (proof : PrunedMerklePaths) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath)
    (accepted : proof.open hash root numLeaves queries rowWords leafWords = some output) :
    lookup root (registerMany registry announcements) = some snapshot ∧
      ((∀ p ∈ output, p.leafData = row hash snapshot root numLeaves.log2 p.leafIndex) ∨
        OpenBad hash snapshot root output) := by
  refine ⟨registerMany_preserves registry announcements root snapshot committed, ?_⟩
  exact open_batch_to_ideal hash proof root numLeaves queries rowWords leafWords output
    accepted snapshot.table snapshot.fallback

/-- All later batches (including transcript clones) use the SAME frozen
commitment-time oracle. A failure is a collision in that snapshot or a fresh
query hitting one of its fixed root/child targets. -/
theorem batches_frozen {I : Type} (hash : Primitive) (registry : Registry)
    (announcements : I → Registry) (root : Digest32) (snapshot : Snapshot)
    (committed : lookup root registry = some snapshot)
    (proof : I → PrunedMerklePaths) (numLeaves : I → Nat) (queries : I → List Nat)
    (rowWords leafWords : I → Nat) (output : I → List RawPath)
    (accepted : ∀ i, (proof i).open hash root (numLeaves i) (queries i)
      (rowWords i) (leafWords i) = some (output i)) :
    (∀ i, lookup root (registerMany registry (announcements i)) = some snapshot) ∧
      ((∀ i, ∀ p ∈ output i,
          p.leafData = row hash snapshot root (numLeaves i).log2 p.leafIndex) ∨
        Collision (hashing hash) snapshot.table ∨
          ∃ i, ∃ p ∈ output i,
            FreshHit (hashing hash) snapshot.table root (p.opening.inputs (hashing hash))) := by
  classical
  refine ⟨fun i => registerMany_preserves registry _ root snapshot committed, ?_⟩
  by_cases hc : Collision (hashing hash) snapshot.table
  · exact Or.inr (Or.inl hc)
  by_cases hf : ∃ i, ∃ p ∈ output i,
      FreshHit (hashing hash) snapshot.table root (p.opening.inputs (hashing hash))
  · exact Or.inr (Or.inr hf)
  left
  intro i
  have h := (open_frozen hash registry (announcements i) root snapshot committed
    (proof i) (numLeaves i) (queries i) (rowWords i) (leafWords i) (output i) (accepted i)).2
  rcases h with hi | hi | hi
  · exact hi
  · exact (hc hi).elim
  · obtain ⟨p,hp,hfresh⟩ := hi
    exact (hf ⟨i,p,hp,hfresh⟩).elim

theorem open_base_rows (hash : Primitive) (snapshot : Snapshot)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath)
    (accepted : proof.open hash root numLeaves queries rowWords leafWords = some output) :
    List.Forall₂ (fun q p => p.leafData.toArray =
      (baseOracle hash snapshot root numLeaves.log2 numLeaves leafWords)[q]!) queries output ∨
      OpenBad hash snapshot root output := by
  have refined := open_refines _ _ _ _ _ _ _ _ accepted
  have conditions := ((open_spec _ _ _ _ _ _ _ _).mp accepted).1
  rcases open_batch_to_ideal hash proof root numLeaves queries rowWords leafWords output
      accepted snapshot.table snapshot.fallback with good | bad
  · left
    apply List.forall₂_of_length_eq_of_get refined.length_eq
    intro i hi ho
    obtain ⟨stored,hs,hw,hindex,hdata,hlen,hdepth,hroot⟩ := refined.get hi ho
    have hq := conditions.range (queries.get ⟨i,hi⟩) (List.get_mem _ _)
    have hraw := good (output.get ⟨i,ho⟩) (List.get_mem _ _)
    rw [baseOracle_get _ _ _ _ _ _ _ hq]
    congr 1
    rw [← hindex]
    dsimp only [baseRow]
    change (output.get ⟨i,ho⟩).leafData = row hash snapshot root _ _ at hraw
    rw [← hraw, ite_eq_left hlen]
  · exact Or.inr bad

/-- The source's `chunks(3)` conversion is total on accepted intermediate
rows and agrees with the shape-total frozen E oracle, in original query order. -/
theorem open_intermediate_rows (hash : Primitive) (snapshot : Snapshot)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (width : Nat) (output : List RawPath)
    (accepted : proof.open hash root numLeaves queries (3 * width) (3 * width) = some output) :
    List.Forall₂ (fun q p => ByteCodec.wordsToFields p.leafData =
      some ((intermediateOracle hash snapshot root numLeaves.log2 numLeaves width)[q]!).toList)
      queries output ∨ OpenBad hash snapshot root output := by
  have conditions := ((open_spec _ _ _ _ _ _ _ _).mp accepted).1
  rcases open_base_rows hash snapshot proof root numLeaves queries (3*width) (3*width)
      output accepted with good | bad
  · left
    apply List.forall₂_of_length_eq_of_get good.length_eq
    intro i hi ho
    have hq := conditions.range (queries.get ⟨i,hi⟩) (List.get_mem _ _)
    have hb := good.get hi ho
    rw [baseOracle_get _ _ _ _ _ _ _ hq] at hb
    have hw := congrArg Array.toList hb
    change (output.get ⟨i,ho⟩).leafData =
      baseRow hash snapshot root numLeaves.log2 (queries.get ⟨i,hi⟩) (3*width) at hw
    rw [hw, intermediateOracle_get _ _ _ _ _ _ _ hq]
    simpa using (intermediateRow_decoded hash snapshot root numLeaves.log2
      (queries.get ⟨i,hi⟩) width).1
  · exact Or.inr bad

/-- Extraction locality is unconditional, including for a collisionful table:
it compares the entire recorded-path predicate, rather than assuming that
classical choice selected the same path because an opening was unique. -/
theorem opening_locality (hash other : Primitive) (table : Finset (List Byte))
    (agree : ∀ x ∈ table, hash x = other x) {address : List Bool}
    (path : Opening (List K) Digest32 address)
    (recorded : path.inputs (hashing hash) ⊆ table) :
    path.inputs (hashing hash) = path.inputs (hashing other) ∧
      path.digest (hashing hash) = path.digest (hashing other) := by
  induction path with
  | leaf words =>
    refine ⟨rfl, ?_⟩
    exact agree (ByteCodec.wordsBytes words) (recorded (by simp [Opening.inputs,hashing]))
  | node direction sibling child ih =>
    have childRecorded : child.inputs (hashing hash) ⊆ table := by
      intro x hx
      exact recorded (Finset.mem_insert_of_mem hx)
    obtain ⟨hi,hd⟩ := ih childRecorded
    have hp : (hashing hash).pair
        (if direction then (sibling,child.digest (hashing hash))
          else (child.digest (hashing hash),sibling)) ∈ table :=
      recorded (Finset.mem_insert_self _ _)
    constructor
    · simp only [Opening.inputs,hi,hd]
      rfl
    · simp only [Opening.digest]
      rw [← hd]
      exact agree _ hp

theorem recorded_predicate_locality (hash other : Primitive) (table : Finset (List Byte))
    (root : Digest32) (address : List Bool)
    (agree : ∀ x ∈ table, hash x = other x) :
    (fun path : Opening (List K) Digest32 address =>
      path.inputs (hashing hash) ⊆ table ∧ path.digest (hashing hash) = root) =
    (fun path : Opening (List K) Digest32 address =>
      path.inputs (hashing other) ⊆ table ∧ path.digest (hashing other) = root) := by
  funext path
  apply propext
  constructor
  · rintro ⟨recorded,accepted⟩
    obtain ⟨hi,hd⟩ := opening_locality hash other table agree path recorded
    exact ⟨hi ▸ recorded, hd ▸ accepted⟩
  · rintro ⟨recorded,accepted⟩
    obtain ⟨hi,hd⟩ := opening_locality other hash table
      (fun x hx => (agree x hx).symm) path recorded
    exact ⟨hi ▸ recorded, hd ▸ accepted⟩

theorem idealRow_locality (hash other : Primitive) (table : Finset (List Byte))
    (root : Digest32) (fallback : List K) (address : List Bool)
    (agree : ∀ x ∈ table, hash x = other x) :
    idealRow (hashing hash) table root fallback address =
      idealRow (hashing other) table root fallback address := by
  classical
  let select (predicate : Opening (List K) Digest32 address → Prop) : List K :=
    if h : ∃ path, predicate path then h.choose.row else fallback
  change select _ = select _
  apply congrArg select
  exact recorded_predicate_locality hash other table root address agree

theorem oracle_locality (hash other : Primitive) (snapshot : Snapshot) (root : Digest32)
    (agree : ∀ x ∈ snapshot.table, hash x = other x) :
    oracle hash snapshot root = oracle other snapshot root := by
  funext address
  exact idealRow_locality hash other snapshot.table root snapshot.fallback address agree

theorem baseOracle_locality (hash other : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width : Nat) (agree : ∀ x ∈ snapshot.table, hash x = other x) :
    baseOracle hash snapshot root height numRows width =
      baseOracle other snapshot root height numRows width := by
  simp only [baseOracle,baseRow,row,oracle_locality hash other snapshot root agree]
  rfl

theorem intermediateOracle_locality (hash other : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width : Nat) (agree : ∀ x ∈ snapshot.table, hash x = other x) :
    intermediateOracle hash snapshot root height numRows width =
      intermediateOracle other snapshot root height numRows width := by
  simp only [intermediateOracle,intermediateRow,baseRow,row,
    oracle_locality hash other snapshot root agree]
  rfl

/-- Finite primitive queries and their already exposed answers. This is data
in the causal interpreter state, not a function closing over future answers. -/
abbrev Records := List (List Byte × Digest32)

def recordLookup (input : List Byte) : Records → Option Digest32
  | [] => none
  | (x,d) :: rest => if input = x then some d else recordLookup input rest

def recordDomain (records : Records) : Finset (List Byte) :=
  (records.map Prod.fst).toFinset

/-- A total *extraction view*, not a cryptographic hash implementation.
Unrecorded inputs receive a fixed public answer; locality proves that answer
cannot affect extraction from a covered snapshot. -/
def recordedHash (records : Records) (absent : Digest32) : Primitive :=
  fun input => (recordLookup input records).getD absent

def Authentic (hash : Primitive) (records : Records) : Prop :=
  ∀ input digest, (input,digest) ∈ records → hash input = digest

theorem recordLookup_mem (records : Records) (input : List Byte) (digest : Digest32)
    (found : recordLookup input records = some digest) : (input,digest) ∈ records := by
  induction records with
  | nil => simp [recordLookup] at found
  | cons entry rest ih =>
    rcases entry with ⟨x,d⟩
    by_cases he : input = x
    · simp [recordLookup,he] at found
      simp [he,found]
    · simp [recordLookup,he] at found
      exact List.mem_cons_of_mem _ (ih found)

theorem recordLookup_exists (records : Records) (input : List Byte)
    (member : input ∈ recordDomain records) : ∃ digest, recordLookup input records = some digest := by
  induction records with
  | nil => simp [recordDomain] at member
  | cons entry rest ih =>
    rcases entry with ⟨x,d⟩
    by_cases he : input = x
    · exact ⟨d,by simp [recordLookup,he]⟩
    · have hm : input ∈ recordDomain rest := by
        simpa [recordDomain,he] using member
      obtain ⟨digest,hd⟩ := ih hm
      exact ⟨digest,by simp [recordLookup,he,hd]⟩

theorem recordedHash_agrees (hash : Primitive) (records : Records) (absent : Digest32)
    (authentic : Authentic hash records) :
    ∀ input ∈ recordDomain records, hash input = recordedHash records absent input := by
  intro input member
  obtain ⟨digest,hd⟩ := recordLookup_exists records input member
  have ha := authentic input digest (recordLookup_mem records input digest hd)
  simpa [recordedHash,hd] using ha

theorem recordedHash_agrees_on_snapshot (hash : Primitive) (records : Records)
    (absent : Digest32) (snapshot : Snapshot) (authentic : Authentic hash records)
    (covered : snapshot.table ⊆ recordDomain records) :
    ∀ input ∈ snapshot.table, hash input = recordedHash records absent input :=
  fun input hi => recordedHash_agrees hash records absent authentic input (covered hi)

/-- The full-primitive oracle equals extraction through only finite exposed
records. Neither absence of collisions nor an assumed codec/decoder bridge is
needed; later primitive answers are absent from the right-hand definition. -/
theorem oracle_eq_recorded (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (records : Records) (absent : Digest32) (authentic : Authentic hash records)
    (covered : snapshot.table ⊆ recordDomain records) :
    oracle hash snapshot root = oracle (recordedHash records absent) snapshot root :=
  oracle_locality hash _ snapshot root
    (recordedHash_agrees_on_snapshot hash records absent snapshot authentic covered)

theorem baseOracle_eq_recorded (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width : Nat) (records : Records) (absent : Digest32)
    (authentic : Authentic hash records) (covered : snapshot.table ⊆ recordDomain records) :
    baseOracle hash snapshot root height numRows width =
      baseOracle (recordedHash records absent) snapshot root height numRows width :=
  baseOracle_locality hash _ snapshot root height numRows width
    (recordedHash_agrees_on_snapshot hash records absent snapshot authentic covered)

theorem intermediateOracle_eq_recorded (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width : Nat) (records : Records) (absent : Digest32)
    (authentic : Authentic hash records) (covered : snapshot.table ⊆ recordDomain records) :
    intermediateOracle hash snapshot root height numRows width =
      intermediateOracle (recordedHash records absent) snapshot root height numRows width :=
  intermediateOracle_locality hash _ snapshot root height numRows width
    (recordedHash_agrees_on_snapshot hash records absent snapshot authentic covered)

/-- Changing the fixed answer outside the exposed finite table has no effect
on the extractor. This includes changing every as-yet-unqueried hash value. -/
theorem recorded_oracle_absent_irrelevant (snapshot : Snapshot) (root : Digest32)
    (records : Records) (absent otherAbsent : Digest32)
    (covered : snapshot.table ⊆ recordDomain records) :
    oracle (recordedHash records absent) snapshot root =
      oracle (recordedHash records otherAbsent) snapshot root := by
  apply oracle_locality
  intro input hi
  obtain ⟨digest,hd⟩ := recordLookup_exists records input (covered hi)
  simp [recordedHash,hd]

end Commitments

end Whir.MerkleTransport
