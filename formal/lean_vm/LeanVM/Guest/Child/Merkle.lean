/-
  LeanVM.Guest.Child.Merkle

  Honest openings of one Merkle tree agree wherever they meet: every node an honest opening gives
  a digest is a node of the tree, at the heap index of its level and position.
-/

module

public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.Child.Queries
public import LeanVM.Guest.AcceptableChild

/-!
# Honest openings agree

The tree's node at level `l` and position `j` is `nodeAt l j` (leaves at level `0`). Climbing an
honest path from leaf `q` for `l` levels reaches `nodeAt l (q / 2^l)` (`climb_take`), and the
path's `l`-th sibling is `nodeAt l (sibling (q / 2^l))` (`getD_path`). Both are at heap index
`2^(ht - l) + j` for their position `j < 2^(ht - l)` (`nodeIs_honest`), and a heap index fixes
the level and the position (`heap_inj`), so two honest openings giving the same heap index a
digest give the same digest (`batchAgrees_honest`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.MerkleTree

@[expose] public section

section Generic

variable {D : Type} (hp : D → D → D) (N : ℕ → ℕ → D)
  (hN : ∀ l j, N (l + 1) j = hp (N l (2 * j)) (N l (2 * j + 1)))
include hN

theorem getElem_parents_N {k l : ℕ} (level : Vector D (2 ^ (k + 1)))
    (hl : ∀ j (hj : j < 2 ^ (k + 1)), level[j] = N l j) :
    ∀ j (hj : j < 2 ^ k), (parents hp level)[j] = N (l + 1) j := by
  intro j hj
  rw [getElem_parents, hl, hl, hN]

/-- The path's `m`-th sibling is the tree's node at level `l + m`, next to the path's. -/
theorem getD_pathOfLevel (d0 : D) :
    ∀ (k : ℕ) (level : Vector D (2 ^ k)) (l : ℕ) (i : Fin (2 ^ k)),
      (∀ j (hj : j < 2 ^ k), level[j] = N l j) → ∀ m < k,
        (pathOfLevel hp k level i).getD m d0 = N (l + m) (sibling (i.val / 2 ^ m))
  | 0, _, _, _, _, m, hm => absurd hm (Nat.not_lt_zero _)
  | k + 1, level, l, i, hl, 0, _ => by
    simp only [pathOfLevel, List.getD_cons_zero, Nat.add_zero, pow_zero, Nat.div_one]
    exact hl _ _
  | k + 1, level, l, i, hl, m + 1, hm => by
    simp only [pathOfLevel, List.getD_cons_succ]
    rw [getD_pathOfLevel d0 k (parents hp level) (l + 1) _ (getElem_parents_N hp N hN level hl)
      m (by omega)]
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
    congr 1
    omega

/-- Climbing `m` levels of the path reaches the tree's node at level `l + m`. -/
theorem climb_pathOfLevel_take :
    ∀ (k : ℕ) (level : Vector D (2 ^ k)) (l : ℕ) (i : Fin (2 ^ k)),
      (∀ j (hj : j < 2 ^ k), level[j] = N l j) → ∀ m ≤ k,
        MerkleTree.climb hp (N l i.val) i.val ((pathOfLevel hp k level i).take m) =
          N (l + m) (i.val / 2 ^ m)
  | k, level, l, i, _, 0, _ => by simp [MerkleTree.climb]
  | 0, _, _, _, _, m + 1, hm => absurd hm (by omega)
  | k + 1, level, l, i, hl, m + 1, hm => by
    simp only [pathOfLevel, List.take_succ_cons, MerkleTree.climb]
    have hsib := hl (sibling i.val) (sibling_lt i.isLt)
    have hnode : (if i.val % 2 = 0 then hp (N l i.val) (level[sibling i.val]'(sibling_lt i.isLt))
        else hp (level[sibling i.val]'(sibling_lt i.isLt)) (N l i.val)) =
          N (l + 1) (i.val / 2) := by
      rw [hsib, hN]
      unfold sibling
      split
      · rename_i h
        congr 2 <;> omega
      · rename_i h
        congr 2 <;> omega
    rw [hnode]
    have := climb_pathOfLevel_take k (parents hp level) (l + 1) ⟨i.val / 2, div_two_lt i.isLt⟩
      (getElem_parents_N hp N hN level hl) m (by omega)
    simp only at this
    rw [this, Nat.div_div_eq_div_mul, ← pow_succ']
    congr 1
    omega

end Generic

/-- The node at level `l` and position `j` of the tree of `word` (leaves at level `0`). -/
def nodeAt (word : Word) : ℕ → ℕ → Digest
  | 0, j => leafHash keccak256 (word j)
  | l + 1, j => nodeHash keccak256 (nodeAt word l (2 * j)) (nodeAt word l (2 * j + 1))

theorem nodeAt_succ (word : Word) (l j : ℕ) :
    nodeAt word (l + 1) j =
      nodeHash keccak256 (nodeAt word l (2 * j)) (nodeAt word l (2 * j + 1)) := rfl

theorem leaves_nodeAt (ht : ℕ) (word : Word) :
    ∀ j (hj : j < 2 ^ ht), ((leavesOf ht word).map (leafHash keccak256))[j] = nodeAt word 0 j := by
  intro j hj
  simp [leavesOf, nodeAt]

/-- **An honest opening's climb** reaches the tree's node. -/
theorem climbTo_openingAt {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) {l : ℕ} (hl : l ≤ ht) :
    Limits.climbTo (merkleLeafDigest (openingAt keccak256 ht word q).leaf) q
      ((openingAt keccak256 ht word q).path.take l) = nodeAt word l (q / 2 ^ l) := by
  have hmod : q % 2 ^ ht = q := Nat.mod_eq_of_lt hq
  have := climb_pathOfLevel_take (nodeHash keccak256) (nodeAt word) (nodeAt_succ word) ht
    ((leavesOf ht word).map (leafHash keccak256)) 0 ⟨q, hq⟩ (leaves_nodeAt ht word) l hl
  simp only [Nat.zero_add] at this
  rw [Limits.climbTo_eq_withHash, climb_eq_merkleClimb]
  simp only [openingAt, hmod]
  exact this

/-- **An honest opening's siblings** are the tree's nodes. -/
theorem getD_openingAt {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) {l : ℕ} (hl : l < ht) :
    (openingAt keccak256 ht word q).path.getD l default =
      nodeAt word l (sibling (q / 2 ^ l)) := by
  have hmod : q % 2 ^ ht = q := Nat.mod_eq_of_lt hq
  have := getD_pathOfLevel (nodeHash keccak256) (nodeAt word) (nodeAt_succ word) default ht
    ((leavesOf ht word).map (leafHash keccak256)) 0 ⟨q, hq⟩ (leaves_nodeAt ht word) l hl
  simp only [Nat.zero_add] at this
  simp only [openingAt, path, hmod]
  exact this

/-- A heap index fixes the level and the position. -/
theorem heap_inj {a b j j' : ℕ} (hj : j < 2 ^ a) (hj' : j' < 2 ^ b)
    (h : 2 ^ a + j = 2 ^ b + j') : a = b ∧ j = j' := by
  have hab : a = b := by
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hlt
      rw [pow_succ] at this
      omega
    · exact heq
    · have : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hgt
      rw [pow_succ] at this
      omega
  subst hab
  exact ⟨rfl, by omega⟩

/-- **Every node an honest opening gives a digest** is the tree's node at its heap index. -/
theorem nodeIs_honest {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) {v : ℕ} {d : Digest}
    (h : Limits.OpeningGivesNode ht (q, openingAt keccak256 ht word q) v d) :
    ∃ l ≤ ht, ∃ j < 2 ^ (ht - l), v = 2 ^ (ht - l) + j ∧ d = nodeAt word l j := by
  rcases h with ⟨l, hl, rfl, rfl⟩ | ⟨l, hl, rfl, rfl⟩
  · refine ⟨l, hl, q / 2 ^ l, ?_, rfl, climbTo_openingAt hq hl⟩
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos l), ← pow_add, Nat.sub_add_cancel hl]
    exact hq
  · have hlt : q / 2 ^ l < 2 ^ (ht - l) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos l), ← pow_add, Nat.sub_add_cancel hl.le]
      exact hq
    have h2 : 2 ^ (ht - l) = 2 * 2 ^ (ht - (l + 1)) := by
      rw [← pow_succ']; congr 1; omega
    have hdiv : q / 2 ^ (l + 1) = q / 2 ^ l / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have hbit : (!q.testBit l).toNat = if q / 2 ^ l % 2 = 0 then 1 else 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      split <;> simp_all
    refine ⟨l, hl.le, sibling (q / 2 ^ l), ?_, ?_, getD_openingAt hq hl⟩
    · rw [h2] at hlt ⊢
      generalize q / 2 ^ l = x at hlt ⊢
      generalize 2 ^ (ht - (l + 1)) = e at hlt ⊢
      unfold sibling
      split <;> omega
    · simp only [Limits.siblingHeapIndex, Limits.merkleHeapIndex]
      rw [hbit, hdiv, h2]
      generalize q / 2 ^ l = x
      generalize 2 ^ (ht - (l + 1)) = e
      unfold sibling
      split <;> omega

theorem mem_zip_map {ps : List ℕ} {f : ℕ → Opening} {x : ℕ × Opening}
    (h : x ∈ ps.zip (ps.map f)) : x = (x.1, f x.1) ∧ x.1 ∈ ps := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, List.mem_cons_self⟩
    · exact ⟨(ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

/-- **One tree's honest openings agree** wherever they meet, at positions below its leaf count. -/
theorem batchAgrees_honest {ht : ℕ} {word : Word} {ps : List ℕ} (hps : ∀ q ∈ ps, q < 2 ^ ht) :
    Limits.OpeningsAgree ht (ps.zip (ps.map (openingAt keccak256 ht word))) := by
  intro a ha b hb v d d' hd hd'
  have hzip : ∀ x ∈ ps.zip (ps.map (openingAt keccak256 ht word)),
      x = (x.1, openingAt keccak256 ht word x.1) ∧ x.1 ∈ ps := fun x hx ↦ mem_zip_map hx
  obtain ⟨ea, hqa⟩ := hzip a ha
  obtain ⟨eb, hqb⟩ := hzip b hb
  rw [ea] at hd
  rw [eb] at hd'
  obtain ⟨l, hl, j, hj, rfl, rfl⟩ := nodeIs_honest (hps _ hqa) hd
  obtain ⟨l', hl', j', hj', hv, rfl⟩ := nodeIs_honest (hps _ hqb) hd'
  obtain ⟨hll, rfl⟩ := heap_inj hj hj' hv
  have : l = l' := by omega
  subst this
  rfl

end
end LeanVM.Guest.Child
