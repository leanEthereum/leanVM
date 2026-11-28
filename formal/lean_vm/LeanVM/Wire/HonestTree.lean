/-
  LeanVM.Wire.HonestTree

  The openings of one Merkle tree the honest prover builds over a hash `h` are a phase the wire
  decoding recovers: they agree on the tree (`PhaseDecodable`), each node the tree's.
-/

module

public import LeanVM.Wire.Spec
public import LeanVM.Protocol.WithHash

/-!
# One tree's openings are decodable

The honest prover commits a word by building its tree (`buildTreeWithHash h ht word`: the leaf
digests, then each level's parents, `Statement/Prover/Run.lean`) and opens it at the queried
positions (`Tree.opening`). The tree's node at level `l` and position `j` is
`honestNode h word l j` (the leaves at level `0`): the built tree holds it there
(`getD_buildTree`). Climbing an opening at `q < 2^ht` for `l` levels reaches
`honestNode h word l (q / 2^l)` (`climbTo_opening`), and its `l`-th sibling is
`honestNode h word l (sibling (q / 2^l))` (`getD_opening`); so two openings through one node carry
the same sibling and climb to the same digest there, and an opening's sibling at a node another
opening passes through is that opening's digest (`phaseDecodable_opening`).

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open LeanVM.Prover (Tree sibling buildTreeWithHash leafDigestsWithHash parentsWithHash
  levelsWithHash)

variable (h : Bytes → Digest)

/-- The node at level `l` and position `j` of the tree of `word` over `h` (leaves at level
`0`). -/
def honestNode (word : Word) : ℕ → ℕ → Digest
  | 0, j => h ((word j).flatMap K.toBytes)
  | l + 1, j => h (digestBytes (honestNode word l (2 * j)) ++
      digestBytes (honestNode word l (2 * j + 1)))

variable {h}

theorem getD_parents {word : Word} {l n : ℕ} {level : Array Digest}
    (hl : ∀ j < 2 * n, level.getD j default = honestNode h word l j) :
    ∀ j < n, (Id.run (parentsWithHash (m := Id) h level n)).getD j default =
      honestNode h word (l + 1) j := by
  intro j hj
  unfold parentsWithHash
  rw [Array.idRun_mapM, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range, ite_eq_left hj]
  simp only [Option.map_some, Option.getD_some, Id.run]
  rw [hl _ (by omega), hl _ (by omega)]
  rfl

theorem getD_levels {word : Word} :
    ∀ (k : ℕ) (level : Array Digest) (l : ℕ),
      (∀ j < 2 ^ k, level.getD j default = honestNode h word l j) →
      ∀ m ≤ k, ∀ j < 2 ^ (k - m),
        ((Id.run (levelsWithHash (m := Id) h k level)).getD m #[]).getD j default =
          honestNode h word (l + m) j
  | 0, level, l, hl, m, hm, j, hj => by
    obtain rfl : m = 0 := by omega
    exact hl j hj
  | k + 1, level, l, hl, m, hm, j, hj => by
    unfold levelsWithHash
    rcases m with _ | m
    · exact hl j hj
    · have hp := getD_parents (n := 2 ^ k) (fun j hj ↦ hl j (by rw [pow_succ]; omega))
      have := getD_levels k _ (l + 1) hp m (by omega) j (by
        rw [show k + 1 - (m + 1) = k - m by omega] at hj; exact hj)
      rw [show l + (m + 1) = l + 1 + m by omega, ← this]
      rfl

/-- **The built tree holds the tree's nodes.** -/
theorem getD_buildTree {ht : ℕ} {word : Word} {l j : ℕ} (hl : l ≤ ht) (hj : j < 2 ^ (ht - l)) :
    ((Id.run (buildTreeWithHash (m := Id) h ht word)).levels.getD l #[]).getD j default =
      honestNode h word l j := by
  have hleaves : ∀ j < 2 ^ ht,
      (Id.run (leafDigestsWithHash (m := Id) h ht word)).getD j default =
        honestNode h word 0 j := by
    intro j hj
    unfold leafDigestsWithHash
    rw [Array.idRun_mapM, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_range, ite_eq_left hj]
    rfl
  have := getD_levels ht _ 0 hleaves l hl j hj
  rw [Nat.zero_add] at this
  have e : (Id.run (buildTreeWithHash (m := Id) h ht word)).levels =
      (Id.run (levelsWithHash (m := Id) h ht (Id.run (leafDigestsWithHash (m := Id) h ht
        word)))).toArray := rfl
  have e2 : ∀ (L : List (Array Digest)) (l : ℕ), L.toArray.getD l #[] = L.getD l #[] := by
    intro L l; simp [List.getD_eq_getElem?_getD]
  rw [← this, e, e2]

theorem height_buildTree (ht : ℕ) (word : Word) :
    (Id.run (buildTreeWithHash (m := Id) h ht word)).height = ht := rfl

theorem word_buildTree (ht : ℕ) (word : Word) :
    (Id.run (buildTreeWithHash (m := Id) h ht word)).word = word := rfl

theorem sibling_lt {x n : ℕ} (hx : x < 2 ^ (n + 1)) : sibling x < 2 ^ (n + 1) := by
  unfold sibling
  split
  · rw [pow_succ] at hx ⊢; omega
  · omega

theorem div_pow_lt {q ht l : ℕ} (hq : q < 2 ^ ht) (hl : l ≤ ht) : q / 2 ^ l < 2 ^ (ht - l) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel hl]
  exact hq

/-- **An honest opening's siblings** are the tree's nodes. -/
theorem getD_opening {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) {l : ℕ} (hl : l < ht) :
    ((Id.run (buildTreeWithHash (m := Id) h ht word)).opening q).path.getD l default =
      honestNode h word l (sibling (q / 2 ^ l)) := by
  have hmod : q % 2 ^ ht = q := Nat.mod_eq_of_lt hq
  simp only [Tree.opening, height_buildTree, hmod]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, Option.map_some,
    Option.getD_some]
  refine getD_buildTree hl.le ?_
  have h1 := div_pow_lt hq hl.le
  obtain ⟨n, hn⟩ : ∃ n, ht - l = n + 1 := ⟨ht - l - 1, by omega⟩
  rw [hn] at h1 ⊢
  exact sibling_lt h1

theorem leafIndex_opening (ht : ℕ) (word : Word) (q : ℕ) :
    ((Id.run (buildTreeWithHash (m := Id) h ht word)).opening q).leafIndex = q := rfl

theorem leaf_opening {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) :
    ((Id.run (buildTreeWithHash (m := Id) h ht word)).opening q).leaf = word q := by
  simp only [Tree.opening, height_buildTree, word_buildTree, Nat.mod_eq_of_lt hq]

theorem length_path_opening (ht : ℕ) (word : Word) (q : ℕ) :
    ((Id.run (buildTreeWithHash (m := Id) h ht word)).opening q).path.length = ht := by
  simp [Tree.opening, height_buildTree]

/-- **An honest opening's climb** reaches the tree's node. -/
theorem climbTo_opening {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) :
    ∀ {l : ℕ}, l ≤ ht →
      climbTo h ((Id.run (buildTreeWithHash (m := Id) h ht word)).opening q) l =
        honestNode h word l (q / 2 ^ l)
  | 0, _ => by
    simp only [climbTo, leaf_opening hq, honestNode, pow_zero, Nat.div_one]
  | l + 1, hl => by
    simp only [climbTo]
    rw [climbTo_opening hq (by omega), getD_opening hq (by omega), leafIndex_opening,
      Nat.shiftRight_eq_div_pow, honestNode, pow_succ, ← Nat.div_div_eq_div_mul]
    generalize q / 2 ^ l = x
    unfold sibling
    split
    · rw [show 2 * (x / 2) = x by omega]
    · rw [show 2 * (x / 2) = x - 1 by omega, show x - 1 + 1 = x by omega]

theorem sibling_eq_xor_one (x : ℕ) : sibling x = x ^^^ 1 := by
  unfold sibling
  split
  · exact (Nat.xor_one_of_even (Nat.even_iff.2 (by assumption))).symm
  · exact (Nat.xor_one_of_odd (Nat.odd_iff.2 (by omega))).symm

/-- **One tree's openings are a decodable phase**: at positions below `2^ht`, nonempty and within
the decoding's bounds, of a word whose rows are `w` words. -/
theorem phaseDecodable_opening {ht w : ℕ} {word : Word} {ps : List ℕ}
    (hw : ∀ p, (word p).length = w) (hne : ps ≠ []) (hlen : ps.length ≤ wireMaxQueries)
    (hht : ht ≤ wireMaxHeight) (hwl : w ≤ wireMaxLeafWords) (hps : ∀ q ∈ ps, q < 2 ^ ht) :
    PhaseDecodable h (ps.map (Id.run (buildTreeWithHash (m := Id) h ht word)).opening) ht w where
  nonempty := by simpa using hne
  queries_le := by simpa using hlen
  height_le := hht
  leafWords_le := hwl
  shape := by
    intro path hpath
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpath
    exact ⟨length_path_opening _ _ _, by rw [leaf_opening (hps q hq)]; exact hw _⟩
  position_lt := by
    intro path hpath
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpath
    exact hps q hq
  same_position := by
    intro a ha b hb hab
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q', -, rfl⟩ := List.mem_map.mp hb
    simp only [leafIndex_opening] at hab
    rw [hab]
  same_node := by
    intro a ha b hb level hlevel hab
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
    simp only [leafIndex_opening, Nat.shiftRight_eq_div_pow] at hab
    rw [climbTo_opening (hps q hq) hlevel.le, climbTo_opening (hps q' hq') hlevel.le,
      getD_opening (hps q hq) hlevel, getD_opening (hps q' hq') hlevel, hab]
    exact ⟨rfl, rfl⟩
  sibling_node := by
    intro a ha b hb level hlevel hab
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
    simp only [leafIndex_opening, Nat.shiftRight_eq_div_pow] at hab
    rw [climbTo_opening (hps q' hq') hlevel.le, getD_opening (hps q hq) hlevel,
      sibling_eq_xor_one, hab]

end LeanVM.Wire

end
