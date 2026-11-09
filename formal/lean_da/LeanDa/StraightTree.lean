module

public import LeanDa.RpmWagner
public import LeanDa.MerkleM
public import LeanDa.WithHash

@[expose] public section

/-!
# The commitment's tree, read off the hash calls

For the straight-line proof of code binding (`LeanDa.Straight`): the hash inputs of a commitment
(`commitIn`, the cells' bytes, the blob trees' nodes and the nodes of the tree over the blob roots)
and of an opening's check (`verifyIn`, the cell's bytes and its climb), for a hash function `f`,
and what they give when `f` is injective on a set holding them.

* **Every input but the root's hashes to a digest the commitment's inputs carry**
  (`commitIn_parent`): a node's digest is a 32-byte block (`chunks`) of its parent's input.
* **The commitment depends on `f` only on its inputs** (`commitIn_congr`).
* **One root, one matrix** (`commit_unique`), and **an opening that verifies against a root opens
  the matrix's cell** (`verifyCell_agree`), when `f` is injective on a set holding the inputs.
* **Over a partial hash** (`Option`, a cache's lookups), a commitment or a check that returns
  has its inputs in the hash's domain and its pure value (`commitCellsM_some`,
  `verifyCellM_some`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA; the
straight-line proof it serves replaces his forking step and keeps his framework and games.
-/

set_option linter.unusedSectionVars false

namespace LeanDa

/-! ## The digests an input carries -/

/-- Block `t` of a string: its bytes `32 t … 32 t + 31`, as a digest. -/
def chunkAt (b : List UInt8) (t : ℕ) : Common.DigestBytes := Vector.ofFn fun i : Fin 32 ↦ b.getD (32 * t + i) 0

/-- **The digests a hash input carries**: its 32-byte blocks, for the inputs of `64` bytes (a
node's two children) and `2048` bytes (a row's leaf, its `64` cell digests). -/
def chunks (b : List UInt8) : Finset Common.DigestBytes :=
  if b.length = 64 ∨ b.length = 2048 then (Finset.range (b.length / 32)).image (chunkAt b) else ∅

theorem card_chunks_le (b : List UInt8) : (chunks b).card ≤ 64 := by
  unfold chunks
  split
  · next h =>
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_range]
    omega
  · simp

theorem chunkAt_append_left (a : Common.DigestBytes) (l : List UInt8) : chunkAt (a.toList ++ l) 0 = a := by
  apply Vector.ext
  intro i hi
  simp only [chunkAt, Vector.getElem_ofFn, Nat.mul_zero, Nat.zero_add]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simpa using hi),
    Vector.getElem_toList]

theorem chunkAt_append_succ (a : Common.DigestBytes) (l : List UInt8) (t : ℕ) :
    chunkAt (a.toList ++ l) (t + 1) = chunkAt l t := by
  apply Vector.ext
  intro i hi
  simp only [chunkAt, Vector.getElem_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp; omega)]
  congr 2
  simp only [Vector.length_toList]
  omega

theorem chunkAt_pairBytes_zero (a b : Common.DigestBytes) : chunkAt (pairBytes a b) 0 = a :=
  chunkAt_append_left a _

theorem chunkAt_pairBytes_one (a b : Common.DigestBytes) : chunkAt (pairBytes a b) 1 = b := by
  rw [pairBytes, chunkAt_append_succ, ← List.append_nil b.toList, chunkAt_append_left]

theorem mem_chunks_pairBytes_left (a b : Common.DigestBytes) : a ∈ chunks (pairBytes a b) := by
  unfold chunks
  rw [ite_eq_left (Or.inl (length_pairBytes a b))]
  exact Finset.mem_image.mpr ⟨0, by simp [length_pairBytes], chunkAt_pairBytes_zero a b⟩

theorem mem_chunks_pairBytes_right (a b : Common.DigestBytes) : b ∈ chunks (pairBytes a b) := by
  unfold chunks
  rw [ite_eq_left (Or.inl (length_pairBytes a b))]
  exact Finset.mem_image.mpr ⟨1, by simp [length_pairBytes], chunkAt_pairBytes_one a b⟩

/-! ## The inputs of a Merkle tree -/

variable (f : List UInt8 → Common.DigestBytes)

/-- **The inputs a Merkle tree of depth `d` over the leaves `L` hashes**, level by level. -/
def merkleIn : ℕ → (ℕ → Common.DigestBytes) → Set (List UInt8)
  | 0, _ => ∅
  | d + 1, L => {a | ∃ i < 2 ^ d, a = pairBytes (L (2 * i)) (L (2 * i + 1))} ∪ merkleIn d (upWithHash f L)

theorem merkleIn_succ (d : ℕ) (L : ℕ → Common.DigestBytes) :
    merkleIn f (d + 1) L =
      {a | ∃ i < 2 ^ d, a = pairBytes (L (2 * i)) (L (2 * i + 1))} ∪ merkleIn f d (upWithHash f L) := rfl

theorem pair_mem_merkleIn (d : ℕ) (L : ℕ → Common.DigestBytes) (i : ℕ) (hi : i < 2 ^ d) :
    pairBytes (L (2 * i)) (L (2 * i + 1)) ∈ merkleIn f (d + 1) L :=
  Or.inl ⟨i, hi, rfl⟩

/-- **The tree depends on the hash only on its inputs**, and on the leaves only on its own. -/
theorem merkleIn_congr (f' : List UInt8 → Common.DigestBytes) (d : ℕ) :
    ∀ L L' : ℕ → Common.DigestBytes, (∀ i < 2 ^ d, L i = L' i) → (∀ a ∈ merkleIn f d L, f a = f' a) →
      merkleIn f' d L' = merkleIn f d L ∧ merkleRootWithHash f' d L' = merkleRootWithHash f d L := by
  induction d with
  | zero =>
    intro L L' hL _
    exact ⟨rfl, (hL 0 (by norm_num)).symm⟩
  | succ d ih =>
    intro L L' hL hf
    have hL2 : ∀ i < 2 ^ d, L (2 * i) = L' (2 * i) ∧ L (2 * i + 1) = L' (2 * i + 1) :=
      fun i hi ↦ ⟨hL _ (by rw [pow_succ]; omega), hL _ (by rw [pow_succ]; omega)⟩
    have hup : ∀ i < 2 ^ d, upWithHash f L i = upWithHash f' L' i := fun i hi ↦ by
      simp only [upWithHash]
      rw [hf _ (pair_mem_merkleIn f d L i hi), (hL2 i hi).1, (hL2 i hi).2]
    obtain ⟨h1, h2⟩ := ih (upWithHash f L) (upWithHash f' L') hup fun a ha ↦ hf a (Or.inr ha)
    refine ⟨?_, h2⟩
    rw [merkleIn_succ, merkleIn_succ, h1]
    congr 1
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, by rw [(hL2 i hi).1, (hL2 i hi).2]⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, by rw [(hL2 i hi).1, (hL2 i hi).2]⟩

/-- **A leaf is the root or a digest an input carries.** -/
theorem leaf_mem (d : ℕ) (L : ℕ → Common.DigestBytes) (i : ℕ) (hi : i < 2 ^ d) :
    L i = merkleRootWithHash f d L ∨ ∃ b ∈ merkleIn f d L, L i ∈ chunks b := by
  rcases d with _ | d
  · obtain rfl : i = 0 := by simpa using hi
    exact Or.inl rfl
  · refine Or.inr ⟨_, pair_mem_merkleIn f d L (i / 2) (by rw [pow_succ] at hi; omega), ?_⟩
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [show 2 * (i / 2) = i by omega]; exact mem_chunks_pairBytes_left _ _
    · rw [show 2 * (i / 2) + 1 = i by omega]; exact mem_chunks_pairBytes_right _ _

/-- **An input hashes to the root or to a digest an input carries.** -/
theorem merkleIn_parent (d : ℕ) :
    ∀ (L : ℕ → Common.DigestBytes) (a : List UInt8), a ∈ merkleIn f d L →
      f a = merkleRootWithHash f d L ∨ ∃ b ∈ merkleIn f d L, f a ∈ chunks b := by
  induction d with
  | zero => intro L a ha; exact ha.elim
  | succ d ih =>
    intro L a ha
    rcases ha with ⟨i, hi, rfl⟩ | ha
    · rcases leaf_mem f d (upWithHash f L) i hi with h | ⟨b, hb, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, Or.inr hb, h⟩
    · rcases ih (upWithHash f L) a ha with h | ⟨b, hb, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, Or.inr hb, h⟩

variable {f}

/-- **Two trees of one root over an injective hash have the same leaves.** -/
theorem merkleRoot_inj {S : Set (List UInt8)} (hinj : Set.InjOn f S) (d : ℕ) :
    ∀ L L' : ℕ → Common.DigestBytes, merkleIn f d L ⊆ S → merkleIn f d L' ⊆ S →
      merkleRootWithHash f d L = merkleRootWithHash f d L' → ∀ i < 2 ^ d, L i = L' i := by
  induction d with
  | zero =>
    intro L L' _ _ he i hi
    obtain rfl : i = 0 := by simpa using hi
    exact he
  | succ d ih =>
    intro L L' h1 h2 he i hi
    have hup := ih (upWithHash f L) (upWithHash f L') (fun a ha ↦ h1 (Or.inr ha)) (fun a ha ↦ h2 (Or.inr ha)) he
      (i / 2) (by rw [pow_succ] at hi; omega)
    have hp := pairBytes_injective (hinj (h1 (pair_mem_merkleIn f d L (i / 2)
      (by rw [pow_succ] at hi; omega))) (h2 (pair_mem_merkleIn f d L' (i / 2)
      (by rw [pow_succ] at hi; omega))) hup)
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [show i = 2 * (i / 2) by omega]; exact hp.1
    · rw [show i = 2 * (i / 2) + 1 by omega]; exact hp.2

variable (f)

/-- The inputs a climb hashes, as a set. -/
def walkIn : ℕ → Common.DigestBytes → List Common.DigestBytes → Set (List UInt8)
  | _, _, [] => ∅
  | idx, node, s :: rest =>
    insert (if idx % 2 = 0 then pairBytes node s else pairBytes s node)
      (walkIn (idx / 2) (f (if idx % 2 = 0 then pairBytes node s else pairBytes s node)) rest)

variable {f}

/-- **A climb that reaches a tree's root over an injective hash starts at the tree's leaf.** -/
theorem walk_eq_leaf {S : Set (List UInt8)} (hinj : Set.InjOn f S) (path : List Common.DigestBytes) :
    ∀ (d : ℕ) (L : ℕ → Common.DigestBytes) (idx : ℕ) (leaf : Common.DigestBytes), path.length = d → idx < 2 ^ d →
      walkIn f idx leaf path ⊆ S → merkleIn f d L ⊆ S → walk f idx leaf path = merkleRootWithHash f d L →
        leaf = L idx := by
  induction path with
  | nil =>
    intro d L idx leaf hd hi _ _ he
    subst hd
    obtain rfl : idx = 0 := by simpa using hi
    exact he
  | cons s rest ih =>
    intro d L idx leaf hd hi hw hm he
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp at hd; omega⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hd
    rw [walk_cons] at he
    have hlt : idx / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    have h := ih d (upWithHash f L) (idx / 2) _ hd hlt (fun a ha ↦ hw (Set.mem_insert_of_mem _ ha))
      (fun a ha ↦ hm (Or.inr ha)) he
    have hp := hinj (hw (Set.mem_insert _ _)) (hm (pair_mem_merkleIn f d L (idx / 2) hlt)) h
    rcases Nat.mod_two_eq_zero_or_one idx with h2 | h2
    · simp only [h2, ↓reduceIte] at hp
      rw [(pairBytes_injective hp).1, show 2 * (idx / 2) = idx by omega]
    · have h2' : ¬ idx % 2 = 0 := by omega
      simp only [h2', ↓reduceIte] at hp
      rw [(pairBytes_injective hp).2, show 2 * (idx / 2) + 1 = idx by omega]

variable (f)

/-- A climb's inputs along two paths in turn. -/
theorem walkIn_append : ∀ (l₁ l₂ : List Common.DigestBytes) (idx : ℕ) (node : Common.DigestBytes),
    walkIn f idx node (l₁ ++ l₂) =
      walkIn f idx node l₁ ∪ walkIn f (idx / 2 ^ l₁.length) (walk f idx node l₁) l₂
  | [], l₂, idx, node => by simp [walkIn, walk]
  | s :: rest, l₂, idx, node => by
    rw [List.cons_append, walkIn, walkIn, walkIn_append rest l₂, walk_cons, List.length_cons,
      pow_succ', Nat.div_div_eq_div_mul, Set.insert_union]

/-- A climb's inputs read the index's low bits only, one per sibling. -/
theorem walkIn_mod : ∀ (path : List Common.DigestBytes) (idx : ℕ) (node : Common.DigestBytes),
    walkIn f idx node path = walkIn f (idx % 2 ^ path.length) node path
  | [], _, _ => rfl
  | s :: rest, idx, node => by
    have h2 : idx % 2 ^ (rest.length + 1) % 2 = idx % 2 := by
      rw [pow_succ, Nat.mod_mul_left_mod]
    have hd : idx % 2 ^ (rest.length + 1) / 2 % 2 ^ rest.length = idx / 2 % 2 ^ rest.length := by
      rw [pow_succ', Nat.mod_mul_right_div_self, Nat.mod_mod]
    rw [List.length_cons, walkIn, walkIn, h2, walkIn_mod rest (idx / 2),
      walkIn_mod rest (idx % _ / 2), hd]

/-! ## The inputs of a commitment -/

section Commit

variable {r : ℕ}

/-- The padded matrix's cells' bytes. -/
def cellIn (c : Fin (r * 128) → Cell) : Set (List UInt8) :=
  {a | ∃ i < paddedRowCount r, ∃ j < 128, a = cellBytes (paddedCell c i j)}

/-- The blob trees' inputs: the nodes of each padded row's tree over its cell digests. -/
def blobIn (c : Fin (r * 128) → Cell) : Set (List UInt8) :=
  {a | ∃ i < paddedRowCount r, a ∈ merkleIn f 7 (cellLeavesWithHash f c i)}

/-- **The inputs a commitment hashes**: the cells', the blob trees' and the tree's over the blob
roots. -/
def commitIn (c : Fin (r * 128) → Cell) : Set (List UInt8) :=
  cellIn c ∪ blobIn f c ∪ merkleIn f (logPaddedRowCount r) (blobRootWithHash f c)

theorem nPad_eq : paddedRowCount r = 2 ^ logPaddedRowCount r := rfl

theorem cellIn_sub (c : Fin (r * 128) → Cell) : cellIn c ⊆ commitIn f c :=
  fun _ h ↦ Or.inl (Or.inl h)

theorem blobTree_sub (c : Fin (r * 128) → Cell) {i : ℕ} (hi : i < paddedRowCount r) :
    merkleIn f 7 (cellLeavesWithHash f c i) ⊆ commitIn f c :=
  fun _ h ↦ Or.inl (Or.inr ⟨i, hi, h⟩)

theorem topTree_sub (c : Fin (r * 128) → Cell) :
    merkleIn f (logPaddedRowCount r) (blobRootWithHash f c) ⊆ commitIn f c :=
  fun _ h ↦ Or.inr h

theorem cellLeaves_eq (c : Fin (r * 128) → Cell) (i j : ℕ) :
    cellLeavesWithHash f c i j = f (cellBytes (paddedCell c i j)) := rfl

/-- **The commitment depends on the hash only on its inputs.** -/
theorem commitIn_congr (f' : List UInt8 → Common.DigestBytes) (c : Fin (r * 128) → Cell)
    (h : ∀ a ∈ commitIn f c, f a = f' a) :
    commitIn f' c = commitIn f c ∧ commitCellsWithHash f' c = commitCellsWithHash f c := by
  have hblob : ∀ i < paddedRowCount r,
      merkleIn f' 7 (cellLeavesWithHash f' c i) = merkleIn f 7 (cellLeavesWithHash f c i) ∧
        blobRootWithHash f' c i = blobRootWithHash f c i := fun i hi ↦
    merkleIn_congr f f' 7 _ _
      (fun j hj ↦ h _ (cellIn_sub f c ⟨i, hi, j, by simpa using hj, rfl⟩))
      fun a ha ↦ h a (blobTree_sub f c hi ha)
  have htop := merkleIn_congr f f' (logPaddedRowCount r) (blobRootWithHash f c)
    (blobRootWithHash f' c) (fun i hi ↦ (hblob i hi).2.symm) fun a ha ↦ h a (topTree_sub f c ha)
  have hblobIn : blobIn f' c = blobIn f c := by
    ext a
    simp only [blobIn, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, ha⟩; exact ⟨i, hi, (hblob i hi).1 ▸ ha⟩
    · rintro ⟨i, hi, ha⟩; exact ⟨i, hi, (hblob i hi).1.symm ▸ ha⟩
  exact ⟨by simp only [commitIn, hblobIn, htop.1], htop.2⟩

/-- **A cell's digest is its blob root or a digest an input carries; a blob root is the
commitment or a digest an input carries.** -/
theorem blobRoot_parent (c : Fin (r * 128) → Cell) {i : ℕ} (hi : i < paddedRowCount r) :
    blobRootWithHash f c i = commitCellsWithHash f c ∨
      ∃ b ∈ commitIn f c, blobRootWithHash f c i ∈ chunks b := by
  rcases leaf_mem f _ (blobRootWithHash f c) i hi with h | ⟨b, hb, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨b, topTree_sub f c hb, h⟩

/-- **Every input of a commitment but the root's hashes to a digest one of its inputs carries.** -/
theorem commitIn_parent (c : Fin (r * 128) → Cell) (a : List UInt8) (ha : a ∈ commitIn f c) :
    f a = commitCellsWithHash f c ∨ ∃ b ∈ commitIn f c, f a ∈ chunks b := by
  have hblobT : ∀ i < paddedRowCount r, ∀ v, (v = merkleRootWithHash f 7 (cellLeavesWithHash f c i) ∨
      ∃ b ∈ merkleIn f 7 (cellLeavesWithHash f c i), v ∈ chunks b) →
        v = commitCellsWithHash f c ∨ ∃ b ∈ commitIn f c, v ∈ chunks b := by
    rintro i hi v (rfl | ⟨b, hb, h⟩)
    · exact blobRoot_parent f c hi
    · exact Or.inr ⟨b, blobTree_sub f c hi hb, h⟩
  rcases ha with ((⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, ha⟩) | ha)
  · exact hblobT i hi _ (leaf_mem f 7 (cellLeavesWithHash f c i) j (by simpa using hj))
  · exact hblobT i hi _ (merkleIn_parent f 7 _ a ha)
  · rcases merkleIn_parent f _ _ a ha with h | ⟨b, hb, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨b, topTree_sub f c hb, h⟩

variable {f}

theorem paddedCell_pos (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    paddedCell c (positionRow p) (positionCell p) = c p := by
  have h1 : (positionRow p : ℕ) < r := (positionRow p).isLt
  have h2 : (positionCell p : ℕ) < 128 := (positionCell p).isLt
  simp only [paddedCell, h1, h2, and_self, ↓reduceDIte]
  congr 1
  apply Fin.ext
  simp only [cellPosition, positionRow, positionCell]
  omega

/-- **One root, one matrix**, over a hash injective on a set holding both commitments' inputs. -/
theorem commit_unique {S : Set (List UInt8)} (hinj : Set.InjOn f S) {c c' : Fin (r * 128) → Cell}
    (h1 : commitIn f c ⊆ S) (h2 : commitIn f c' ⊆ S) (he : commitCellsWithHash f c = commitCellsWithHash f c') :
    c = c' := by
  have hb := merkleRoot_inj hinj (logPaddedRowCount r) _ _ (fun a ha ↦ h1 (topTree_sub f c ha))
    (fun a ha ↦ h2 (topTree_sub f c' ha)) he
  funext p
  have hrow : (positionRow p : ℕ) < paddedRowCount r := lt_of_lt_of_le (positionRow p).isLt (le_nPad r)
  have hl := merkleRoot_inj hinj 7 _ _ (fun a ha ↦ h1 (blobTree_sub f c hrow ha))
    (fun a ha ↦ h2 (blobTree_sub f c' hrow ha)) (hb _ hrow) (positionCell p)
    (by simp)
  rw [cellLeaves_eq, cellLeaves_eq] at hl
  have hc := cellBytes_injective (hinj (h1 (cellIn_sub f c ⟨_, hrow, _, (positionCell p).isLt, rfl⟩))
    (h2 (cellIn_sub f c' ⟨_, hrow, _, (positionCell p).isLt, rfl⟩)) hl)
  rwa [paddedCell_pos, paddedCell_pos] at hc

variable (f)

/-- **The inputs an opening's check hashes**: the cell's bytes and the climb's. -/
def verifyIn (p : Fin (r * 128)) (x : Cell) (τ : CellOpening) : Set (List UInt8) :=
  insert (cellBytes x) (walkIn f p (cellDigestWithHash f x) τ.path)

variable {f}

/-- **An opening that verifies against a matrix's root opens the matrix's cell**, over a hash
injective on a set holding the commitment's and the check's inputs: its climb meets the tree
over the blob roots at the cell's blob root, and the cell's blob tree at the cell's digest. -/
theorem verifyCell_agree {S : Set (List UInt8)} (hinj : Set.InjOn f S)
    {c : Fin (r * 128) → Cell} {p : Fin (r * 128)} {x : Cell} {τ : CellOpening}
    (hc : commitIn f c ⊆ S) (hv : verifyIn f p x τ ⊆ S)
    (hver : verifyCell f r (commitCellsWithHash f c) p x τ = true) : x = c p := by
  simp only [verifyCell, Bool.and_eq_true, decide_eq_true_eq] at hver
  obtain ⟨hlen, hroot⟩ := hver
  have hrow : (positionRow p : ℕ) < paddedRowCount r := lt_of_lt_of_le (positionRow p).isLt (le_nPad r)
  have hl1 : (τ.path.take 7).length = 7 := by rw [List.length_take]; omega
  have hl2 : (τ.path.drop 7).length = logPaddedRowCount r := by rw [List.length_drop]; omega
  have hin := walkIn_append f (τ.path.take 7) (τ.path.drop 7) p (cellDigestWithHash f x)
  rw [List.take_append_drop, hl1] at hin
  rw [← List.take_append_drop 7 τ.path, walk_append, hl1] at hroot
  have hblob := walk_eq_leaf hinj (τ.path.drop 7) (logPaddedRowCount r) (blobRootWithHash f c)
    ((p : ℕ) / 2 ^ 7) _ hl2 hrow
    (fun a ha ↦ hv (Set.mem_insert_of_mem _ (hin ▸ Or.inr ha)))
    (fun a ha ↦ hc (topTree_sub f c ha)) hroot
  rw [walk_mod, hl1] at hblob
  have hin1 := walkIn_mod f (τ.path.take 7) p (cellDigestWithHash f x)
  rw [hl1] at hin1
  have hleaf := walk_eq_leaf hinj (τ.path.take 7) 7 (cellLeavesWithHash f c (positionRow p))
    ((p : ℕ) % 2 ^ 7) _ hl1 (Nat.mod_lt _ (by norm_num))
    (fun a ha ↦ hv (Set.mem_insert_of_mem _ (hin ▸ Or.inl (hin1 ▸ ha))))
    (fun a ha ↦ hc (blobTree_sub f c hrow ha)) hblob
  rw [show (p : ℕ) % 2 ^ 7 = positionCell p from rfl, cellLeaves_eq] at hleaf
  have hx := cellBytes_injective (hinj (hv (Set.mem_insert _ _))
    (hc (cellIn_sub f c ⟨_, hrow, _, (positionCell p).isLt, rfl⟩)) hleaf)
  rwa [paddedCell_pos] at hx

end Commit

/-! ## Over a partial hash -/

section Partial

variable {g : List UInt8 → Option Common.DigestBytes} (hg : ∀ a u, g a = some u → u = f a)
include hg

theorem upM_some (Lm : ℕ → Option Common.DigestBytes) (L : ℕ → Common.DigestBytes) (hL : ∀ i u, Lm i = some u → u = L i)
    (i : ℕ) (v : Common.DigestBytes) (hv : upMWithHash g Lm i = some v) :
    v = upWithHash f L i ∧ Lm (2 * i) ≠ none ∧ Lm (2 * i + 1) ≠ none ∧
      g (pairBytes (L (2 * i)) (L (2 * i + 1))) ≠ none := by
  simp only [upMWithHash, Option.bind_eq_bind', Option.bind_eq_some_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  rw [hL _ _ ha, hL _ _ hb] at hab
  exact ⟨hg _ _ hab, by simp [ha], by simp [hb], by simp [hab]⟩

theorem merkleRootM_some (d : ℕ) :
    ∀ (Lm : ℕ → Option Common.DigestBytes) (L : ℕ → Common.DigestBytes), (∀ i u, Lm i = some u → u = L i) →
      ∀ v, merkleRootMWithHash g d Lm = some v →
        v = merkleRootWithHash f d L ∧ (∀ i < 2 ^ d, Lm i ≠ none) ∧ ∀ a ∈ merkleIn f d L, g a ≠ none := by
  induction d with
  | zero =>
    intro Lm L hL v hv
    refine ⟨hL 0 v hv, fun i hi ↦ ?_, fun a ha ↦ ha.elim⟩
    obtain rfl : i = 0 := by simpa using hi
    change Lm 0 = some v at hv
    rw [hv]
    simp
  | succ d ih =>
    intro Lm L hL v hv
    have hL' : ∀ i u, upMWithHash g Lm i = some u → u = upWithHash f L i :=
      fun i u hu ↦ (upM_some f hg Lm L hL i u hu).1
    obtain ⟨h1, h2, h3⟩ := ih (upMWithHash g Lm) (upWithHash f L) hL' v hv
    have hup : ∀ i < 2 ^ d, ∃ u, upMWithHash g Lm i = some u := fun i hi ↦
      Option.ne_none_iff_exists'.mp (h2 i hi)
    refine ⟨h1, fun i hi ↦ ?_, fun a ha ↦ ?_⟩
    · obtain ⟨u, hu⟩ := hup (i / 2) (by rw [pow_succ] at hi; omega)
      obtain ⟨-, ha, hb, -⟩ := upM_some f hg Lm L hL _ u hu
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · rwa [show 2 * (i / 2) = i by omega] at ha
      · rwa [show 2 * (i / 2) + 1 = i by omega] at hb
    · rcases ha with ⟨i, hi, rfl⟩ | ha
      · obtain ⟨u, hu⟩ := hup i hi
        exact (upM_some f hg Lm L hL _ u hu).2.2.2
      · exact h3 a ha

theorem mapM_some {β : Type} (F : β → Option Common.DigestBytes) (F' : β → Common.DigestBytes)
    (hF : ∀ b u, F b = some u → u = F' b) (l : List β) (ds : List Common.DigestBytes)
    (h : l.mapM F = some ds) : ds = l.map F' ∧ ∀ b ∈ l, F b ≠ none := by
  induction l generalizing ds with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    exact ⟨h.symm, by simp⟩
  | cons b l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind', Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨u, hu, ds', hds', rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih ds' hds'
    refine ⟨by rw [h1, hF _ _ hu]; rfl, fun b' hb' ↦ ?_⟩
    rcases List.mem_cons.mp hb' with rfl | hb'
    · simp [hu]
    · exact h2 b' hb'

/-- **A commitment over a partial hash that returns** returns the pure commitment, its inputs in
the hash's domain. -/
theorem commitCellsM_some {r : ℕ} (c : Fin (r * 128) → Cell) (v : Common.DigestBytes)
    (hv : commitCellsMWithHash g c = some v) :
    v = commitCellsWithHash f c ∧ ∀ a ∈ commitIn f c, g a ≠ none := by
  have hblob : ∀ i u, blobRootMWithHash g c i = some u →
      u = blobRootWithHash f c i ∧ (∀ j < 2 ^ 7, cellLeavesMWithHash g c i j ≠ none) ∧
        ∀ a ∈ merkleIn f 7 (cellLeavesWithHash f c i), g a ≠ none := fun i u hu ↦
    merkleRootM_some f hg 7 (cellLeavesMWithHash g c i) (cellLeavesWithHash f c i)
      (fun j u hu ↦ hg _ _ hu) u hu
  obtain ⟨hv', hbl, htop⟩ := merkleRootM_some f hg (logPaddedRowCount r) (blobRootMWithHash g c)
    (blobRootWithHash f c) (fun i u hu ↦ (hblob i u hu).1) v hv
  have hblob' : ∀ i < paddedRowCount r, (∀ j < 2 ^ 7, cellLeavesMWithHash g c i j ≠ none) ∧
      ∀ a ∈ merkleIn f 7 (cellLeavesWithHash f c i), g a ≠ none := fun i hi ↦ by
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp (hbl i hi)
    exact (hblob i u hu).2
  refine ⟨hv', fun a ha ↦ ?_⟩
  rcases ha with ((⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, ha⟩) | ha)
  · exact (hblob' i hi).1 j (by simpa using hj)
  · exact (hblob' i hi).2 a ha
  · exact htop a ha

theorem walkM_some (path : List Common.DigestBytes) :
    ∀ (idx : ℕ) (node v : Common.DigestBytes), walkMWithHash g idx node path = some v →
      v = walk f idx node path ∧ ∀ a ∈ walkIn f idx node path, g a ≠ none := by
  induction path with
  | nil =>
    intro idx node v hv
    simp only [walkMWithHash, Option.pure_def, Option.some.injEq] at hv
    exact ⟨hv.symm, fun a ha ↦ ha.elim⟩
  | cons s rest ih =>
    intro idx node v hv
    simp only [walkMWithHash, Option.bind_eq_bind', Option.bind_eq_some_iff] at hv
    obtain ⟨u, hu, hv⟩ := hv
    have hu' : u = f (if idx % 2 = 0 then pairBytes node s else pairBytes s node) := hg _ _ hu
    obtain ⟨h1, h2⟩ := ih _ u v hv
    rw [hu'] at h1 h2
    refine ⟨by rw [walk_cons]; exact h1, fun a ha ↦ ?_⟩
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · simp [hu]
    · exact h2 a ha

/-- **An opening's check over a partial hash that returns** returns the pure check, its inputs
in the hash's domain. -/
theorem verifyCellM_some {r : ℕ} (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening)
    (b : Bool) (hb : verifyCellMWithHash g r com p x τ = some b) :
    b = verifyCell f r com p x τ ∧ ∀ a ∈ verifyIn f p x τ, g a ≠ none := by
  simp only [verifyCellMWithHash, Option.bind_eq_bind', Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at hb
  obtain ⟨d, hd, w, hw, rfl⟩ := hb
  have hd' : d = cellDigestWithHash f x := hg _ _ hd
  subst hd'
  obtain ⟨hw1, hw2⟩ := walkM_some f hg τ.path _ _ w hw
  subst hw1
  refine ⟨rfl, fun a ha ↦ ?_⟩
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · simp [cellDigestWithHash] at hd; simp [hd]
  · exact hw2 a ha

end Partial

end LeanDa
