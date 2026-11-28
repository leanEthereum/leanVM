/-
  LeanVM.Guest.Packed.PTree

  A finite map `ℕ → ℕ` as a binary tree of small packed maps, for maps too large for one `ℕ`.
-/

module

public import LeanVM.Guest.Packed.PMap

/-!
# Trees of packed maps

The kernel keeps every intermediate number of a reduction in its caches, so a lookup in one
packed map of megabits (a shift of the whole number) costs time and memory in proportion to its
size. A `PTree` cuts the map into small `PMap` leaves under a binary tree routed by the key's low
bits: at a node, an even key goes left and an odd one right, as `k / 2`; at a leaf, the key left
is the leaf's own key. The leaves of a tree of depth `d` hold the keys of each residue modulo
`2^d`, at `k >>> d`, so a generator sizes `d` for leaves of a few kilobits.

The tree's shape is any (`full d` is the empty tree of depth `d`): `get` and `set` route a key
through the same path, so `get_set_eq` and `get_set_ne` hold whatever it is. Both are written with
the recursors, which the kernel reduces directly; they are `noncomputable`, for the kernel only.
-/

namespace LeanVM.Guest.Packed

/-- A map `ℕ → ℕ` as a binary tree of `PMap`s, routed by the key's low bits. -/
public inductive PTree where
  | leaf (m : ℕ)
  | node (l r : PTree)

namespace PTree

@[expose] public section

/-- The empty tree of depth `d`. -/
def full (d : ℕ) : PTree := Nat.rec (motive := fun _ ↦ PTree) (leaf PMap.empty) (fun _ t ↦ node t t) d

/-- The value at key `k`, slots of `w` bits. -/
noncomputable def get (w : ℕ) (t : PTree) : ℕ → Option ℕ :=
  PTree.rec (motive := fun _ ↦ ℕ → Option ℕ) (fun m k ↦ PMap.get w m k)
    (fun _ _ gl gr k ↦ Bool.rec (gr (Nat.shiftRight k 1)) (gl (Nat.shiftRight k 1)) (Nat.beq (Nat.land k 1) 0)) t

/-- `t` with the value `v` at key `k`. -/
noncomputable def set (w : ℕ) (t : PTree) (k v : ℕ) : PTree :=
  PTree.rec (motive := fun _ ↦ ℕ → PTree) (fun m k ↦ leaf (PMap.set w m k v))
    (fun l r sl sr k ↦ Bool.rec (node l (sr (Nat.shiftRight k 1))) (node (sl (Nat.shiftRight k 1)) r)
      (Nat.beq (Nat.land k 1) 0)) t k

end

variable {w : ℕ}

/-- The branch a key takes: `true` for the left child (an even key). -/
theorem even_test (k : ℕ) : Nat.beq (Nat.land k 1) 0 = decide (k % 2 = 0) := by
  have : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k
  rw [this]; rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> rfl

public theorem get_leaf (w m k : ℕ) : get w (leaf m) k = PMap.get w m k := rfl

public theorem get_node (w : ℕ) (l r : PTree) (k : ℕ) :
    get w (node l r) k = if k % 2 = 0 then get w l (k >>> 1) else get w r (k >>> 1) := by
  show @Bool.rec (fun _ ↦ Option ℕ) (get w r (k >>> 1)) (get w l (k >>> 1)) (Nat.beq (Nat.land k 1) 0) = _
  rw [even_test]; by_cases h : k % 2 = 0 <;> simp [h]

public theorem set_leaf (w m k v : ℕ) : set w (leaf m) k v = leaf (PMap.set w m k v) := rfl

public theorem set_node (w : ℕ) (l r : PTree) (k v : ℕ) :
    set w (node l r) k v =
      if k % 2 = 0 then node (set w l (k >>> 1) v) r else node l (set w r (k >>> 1) v) := by
  show @Bool.rec (fun _ ↦ PTree) (node l (set w r (k >>> 1) v)) (node (set w l (k >>> 1) v) r)
    (Nat.beq (Nat.land k 1) 0) = _
  rw [even_test]; by_cases h : k % 2 = 0 <;> simp [h]

@[simp] public theorem get_full (w d k : ℕ) : get w (full d) k = none := by
  induction d generalizing k with
  | zero => exact PMap.get_empty w k
  | succ d ih =>
    show get w (node (full d) (full d)) k = none
    rw [get_node]; split_ifs <;> exact ih _

public theorem get_set_eq (t : PTree) (k v : ℕ) (h : v + 1 < 2 ^ w) : get w (set w t k v) k = some v := by
  induction t generalizing k with
  | leaf m => rw [set_leaf, get_leaf, PMap.get_set_eq _ _ _ _ h]
  | node l r ihl ihr =>
    rw [set_node]; by_cases hk : k % 2 = 0 <;> simp only [hk, ↓reduceIte, get_node, ihl, ihr]

public theorem get_set_ne (t : PTree) (k v : ℕ) {k' : ℕ} (h : k' ≠ k) :
    get w (set w t k v) k' = get w t k' := by
  induction t generalizing k k' with
  | leaf m => rw [set_leaf, get_leaf, get_leaf, PMap.get_set_ne _ _ _ _ h]
  | node l r ihl ihr =>
    have hk : k' % 2 = k % 2 → k' >>> 1 ≠ k >>> 1 := fun e e' ↦ by
      simp only [Nat.shiftRight_one] at e'; omega
    rw [set_node, get_node]
    by_cases h1 : k % 2 = 0 <;> by_cases h2 : k' % 2 = 0 <;> simp only [h1, h2, ↓reduceIte, get_node]
    · exact ihl _ (hk (by omega))
    · exact ihr _ (hk (by omega))

end PTree

end LeanVM.Guest.Packed
