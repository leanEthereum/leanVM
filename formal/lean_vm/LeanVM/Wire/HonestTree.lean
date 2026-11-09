/-
  LeanVM.Wire.HonestTree

  The openings of one Merkle tree over a hash `h` are a phase the wire decoding recovers: they
  agree on the tree (`PhaseDecodable`), each node the tree's.
-/

module

public import LeanVM.Wire.Spec
public import LeanVM.Protocol.Compile.Prover

/-!
# One tree's openings are decodable

The honest prover opens a committed word's tree at the queried positions,
`ps.map (openingAt h ht word)` (`LeanVM.Protocol.Compile.openingAt`). The tree's node at level `l`
and position `j` is `honestNode h word l j` (the leaves at level `0`). Climbing an opening at
`q < 2^ht` for `l` levels reaches `honestNode h word l (q / 2^l)` (`climbTo_openingAt`), and its
`l`-th sibling is `honestNode h word l (sibling (q / 2^l))` (`getD_openingAt`); so two openings
through one node carry the same sibling and climb to the same digest there, and an opening's
sibling at a node another opening passes through is that opening's digest
(`phaseDecodable_openingAt`).

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.MerkleTree

section Generic

variable {D : Type} (hp : D → D → D) (N : ℕ → ℕ → D)
  (hN : ∀ l j, N (l + 1) j = hp (N l (2 * j)) (N l (2 * j + 1)))
include hN

theorem getElem_parents_honest {k l : ℕ} (level : Vector D (2 ^ (k + 1)))
    (hl : ∀ j (hj : j < 2 ^ (k + 1)), level[j] = N l j) :
    ∀ j (hj : j < 2 ^ k), (parents hp level)[j] = N (l + 1) j := by
  intro j hj
  rw [getElem_parents, hl, hl, hN]

/-- The path's `m`-th sibling is the tree's node at level `l + m`, next to the path's. -/
theorem getD_pathOfLevel_honest (d0 : D) :
    ∀ (k : ℕ) (level : Vector D (2 ^ k)) (l : ℕ) (i : Fin (2 ^ k)),
      (∀ j (hj : j < 2 ^ k), level[j] = N l j) → ∀ m < k,
        (pathOfLevel hp k level i).getD m d0 = N (l + m) (sibling (i.val / 2 ^ m))
  | 0, _, _, _, _, m, hm => absurd hm (Nat.not_lt_zero _)
  | k + 1, level, l, i, hl, 0, _ => by
    simp only [pathOfLevel, List.getD_cons_zero, Nat.add_zero, pow_zero, Nat.div_one]
    exact hl _ _
  | k + 1, level, l, i, hl, m + 1, hm => by
    simp only [pathOfLevel, List.getD_cons_succ]
    rw [getD_pathOfLevel_honest d0 k (parents hp level) (l + 1) _
      (getElem_parents_honest hp N hN level hl) m (by omega)]
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
    congr 1
    omega

end Generic

variable (h : Bytes → Digest)

/-- The node at level `l` and position `j` of the tree of `word` over `h` (leaves at level
`0`). -/
def honestNode (word : Word) : ℕ → ℕ → Digest
  | 0, j => leafHash h (word j)
  | l + 1, j => nodeHash h (honestNode word l (2 * j)) (honestNode word l (2 * j + 1))

theorem honestNode_succ (word : Word) (l j : ℕ) :
    honestNode h word (l + 1) j =
      nodeHash h (honestNode h word l (2 * j)) (honestNode h word l (2 * j + 1)) := rfl

variable {h}

/-- **An honest opening's siblings** are the tree's nodes. -/
theorem getD_openingAt {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) {l : ℕ} (hl : l < ht) :
    (openingAt h ht word q).path.getD l default =
      honestNode h word l (sibling (q / 2 ^ l)) := by
  have hmod : q % 2 ^ ht = q := Nat.mod_eq_of_lt hq
  have := getD_pathOfLevel_honest (nodeHash h) (honestNode h word) (honestNode_succ h word)
    default ht ((leavesOf ht word).map (leafHash h)) 0 ⟨q, hq⟩
    (fun j hj ↦ by simp [leavesOf, honestNode]) l hl
  simp only [Nat.zero_add] at this
  simp only [openingAt, path, hmod]
  exact this

/-- **An honest opening's climb** reaches the tree's node. -/
theorem climbTo_openingAt {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) :
    ∀ {l : ℕ}, l ≤ ht → climbTo h (openingAt h ht word q) l = honestNode h word l (q / 2 ^ l)
  | 0, _ => by
    simp [climbTo, openingAt, honestNode, leafHash, Nat.mod_eq_of_lt hq]
  | l + 1, hl => by
    simp only [climbTo]
    rw [climbTo_openingAt hq (by omega), getD_openingAt hq (by omega),
      show (openingAt h ht word q).leafIndex = q from rfl, Nat.shiftRight_eq_div_pow,
      honestNode_succ, nodeHash, pow_succ, ← Nat.div_div_eq_div_mul]
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
theorem phaseDecodable_openingAt {ht w : ℕ} {word : Word} {ps : List ℕ}
    (hw : WellShaped w word) (hne : ps ≠ []) (hlen : ps.length ≤ wireMaxQueries)
    (hht : ht ≤ wireMaxHeight) (hwl : w ≤ wireMaxLeafWords) (hps : ∀ q ∈ ps, q < 2 ^ ht) :
    PhaseDecodable h (ps.map (openingAt h ht word)) ht w where
  nonempty := by simpa using hne
  queries_le := by simpa using hlen
  height_le := hht
  leafWords_le := hwl
  shape := by
    intro path hpath
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hpath
    exact ⟨length_path _ _ _ _, hw _⟩
  position_lt := by
    intro path hpath
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpath
    exact hps q hq
  same_position := by
    intro a ha b hb hab
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q', -, rfl⟩ := List.mem_map.mp hb
    cases hab
    rfl
  same_node := by
    intro a ha b hb level hlevel hab
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
    simp only [show ∀ x, (openingAt h ht word x).leafIndex = x from fun _ ↦ rfl,
      Nat.shiftRight_eq_div_pow] at hab
    rw [climbTo_openingAt (hps q hq) hlevel.le, climbTo_openingAt (hps q' hq') hlevel.le,
      getD_openingAt (hps q hq) hlevel, getD_openingAt (hps q' hq') hlevel, hab]
    exact ⟨rfl, rfl⟩
  sibling_node := by
    intro a ha b hb level hlevel hab
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
    simp only [show ∀ x, (openingAt h ht word x).leafIndex = x from fun _ ↦ rfl,
      Nat.shiftRight_eq_div_pow] at hab
    rw [climbTo_openingAt (hps q' hq') hlevel.le, getD_openingAt (hps q hq) hlevel,
      sibling_eq_xor_one, hab]

end LeanVM.Wire

end
