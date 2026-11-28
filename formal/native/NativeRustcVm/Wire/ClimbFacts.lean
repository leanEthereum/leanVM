module

public import NativeRustcVm.Wire.Rep
public import NativeRustcVm.MemLemmas
public import NativeRustcVm.Wire.WordsFacts
public import NativeRustcVm.Wire.ReaderFacts
import NativeVm.Equiv.Transcript

/-!
# A level of the climb, node by node

`sibsM` one node more at a time (`sibsM_snoc`, one node's sibling `sibStep`), `parentsOf` too
(`parentsOf_snoc`, at most a parent a node: `parentsOf_length_le`); the first node of a key
(`lookup_first`, `lookup_none`); the scan's test (`xor_eq_one_iff`); a parent's digest the
model's `hashPair` (`keccak_pair`); nodes in memory kept, unique, and one more
(`NodesAt.of_sameOutside`, `NodesAt.unique`, `NodesAt.snoc`).
-/

namespace NativeRustcVm.Wire

open NativeVm NativeVm.Wire LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- Node `x`'s sibling: the level's node beside it, else a digest read at `c`. -/
def sibStep (B : List UInt8) (ns : List (Nat × Digest)) (x : Nat × Digest) (c : Nat) :
    Option ((Nat × Digest × Bool) × Nat) :=
  match ns.lookup (x.1 ^^^ 1) with
  | some d => some ((x.1, d, true), c)
  | none => (rdDigest B c).map fun p ↦ ((x.1, p.1, false), p.2)

end

public section

theorem sibsM_cons (B : List UInt8) (ns : List (Nat × Digest)) (x : Nat × Digest)
    (l : List (Nat × Digest)) (c : Nat) :
    sibsM B ns (x :: l) c = (sibStep B ns x c).bind fun q ↦
      (sibsM B ns l q.2).map fun p ↦ (q.1 :: p.1, p.2) := by
  obtain ⟨v, d0⟩ := x
  rw [sibsM, sibStep]
  cases ns.lookup (v ^^^ 1) with
  | some d =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases sibsM B ns l c <;> rfl
  | none =>
    simp only [Option.bind_eq_bind]
    cases rdDigest B c with
    | none => rfl
    | some p =>
      simp only [Option.bind_some, Option.map_some]
      cases sibsM B ns l p.2 <;> rfl

theorem sibsM_append (B : List UInt8) (ns : List (Nat × Digest)) :
    ∀ (l1 l2 : List (Nat × Digest)) (c : Nat),
    sibsM B ns (l1 ++ l2) c = (sibsM B ns l1 c).bind fun p ↦
      (sibsM B ns l2 p.2).map fun q ↦ (p.1 ++ q.1, q.2)
  | [], l2, c => by
    simp only [List.nil_append, sibsM, Option.bind_some]
    cases sibsM B ns l2 c <;> rfl
  | x :: l1, l2, c => by
    rw [List.cons_append, sibsM_cons, sibsM_cons]
    cases sibStep B ns x c with
    | none => rfl
    | some q =>
      simp only [Option.bind_some]
      rw [sibsM_append B ns l1 l2 q.2]
      cases sibsM B ns l1 q.2 with
      | none => rfl
      | some p =>
        simp only [Option.bind_some, Option.map_some]
        cases sibsM B ns l2 p.2 <;> rfl

/-- **One node more.** -/
theorem sibsM_snoc (B : List UInt8) (ns l : List (Nat × Digest)) (x : Nat × Digest) (c : Nat) :
    sibsM B ns (l ++ [x]) c = (sibsM B ns l c).bind fun p ↦
      (sibStep B ns x p.2).map fun q ↦ (p.1 ++ [q.1], q.2) := by
  rw [sibsM_append]
  cases sibsM B ns l c with
  | none => rfl
  | some p =>
    simp only [Option.bind_some, sibsM_cons]
    cases sibStep B ns x p.2 with
    | none => rfl
    | some q => rfl

theorem sibsM_length (B : List UInt8) (ns : List (Nat × Digest)) :
    ∀ (l : List (Nat × Digest)) (c : Nat) {sl : List (Nat × Digest × Bool)} {c' : Nat},
    sibsM B ns l c = some (sl, c') → sl.length = l.length
  | [], c, sl, c', h => by cases h; rfl
  | x :: l, c, sl, c', h => by
    rw [sibsM_cons] at h
    cases hq : sibStep B ns x c with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      simp only [Option.bind_some] at h
      cases hp : sibsM B ns l q.2 with
      | none => rw [hp] at h; cases h
      | some p =>
        rw [hp] at h
        cases h
        simp [sibsM_length B ns l q.2 hp]

theorem sibStep_key {B : List UInt8} {ns : List (Nat × Digest)} {x : Nat × Digest} {c : Nat}
    {q : (Nat × Digest × Bool) × Nat} (h : sibStep B ns x c = some q) : q.1.1 = x.1 := by
  unfold sibStep at h
  split at h
  · cases h; rfl
  · cases hd : rdDigest B c with
    | none => rw [hd] at h; cases h
    | some p => rw [hd] at h; cases h; rfl

theorem parentsOf_snoc {l : List (Nat × Digest)} {sl : List (Nat × Digest × Bool)}
    (h : l.length = sl.length) (x : Nat × Digest) (s : Nat × Digest × Bool) :
    parentsOf (l ++ [x]) (sl ++ [s]) = parentsOf l sl ++ parentOf x s := by
  simp only [parentsOf]
  rw [List.zip_append h, List.flatMap_append]
  simp

/-- At most a parent a node. -/
theorem parentsOf_length_le : ∀ (l : List (Nat × Digest)) (sl : List (Nat × Digest × Bool)),
    (parentsOf l sl).length ≤ l.length
  | [], _ => by simp [parentsOf]
  | _ :: _, [] => by simp [parentsOf]
  | x :: l, s :: sl => by
    have ih := parentsOf_length_le l sl
    have h1 : (parentOf x s).length ≤ 1 := by unfold parentOf; split <;> simp
    simp only [parentsOf, List.zip_cons_cons, List.flatMap_cons, List.length_append,
      List.length_cons] at ih ⊢
    omega

/-- **The first node of key `a`** is node `i`. -/
theorem lookup_first {α : Type} : ∀ (l : List (Nat × α)) (a i : Nat) (hi : i < l.length),
    (∀ j (hj : j < i), (l[j]'(by omega)).1 ≠ a) → l[i].1 = a → l.lookup a = some l[i].2
  | [], _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | (k, v) :: l, a, 0, _, _, h => by
    simp only [List.getElem_cons_zero] at h ⊢
    subst h
    simp [List.lookup]
  | (k, v) :: l, a, i + 1, hi, hb, h => by
    have hk : k ≠ a := hb 0 (by omega)
    simp only [List.lookup, show (a == k) = false from beq_false_of_ne (Ne.symm hk)]
    exact lookup_first l a i (by simpa using hi) (fun j hj ↦ hb (j + 1) (by omega)) h

/-- **No node of key `a`.** -/
theorem lookup_none {α : Type} : ∀ (l : List (Nat × α)) (a : Nat),
    (∀ j (hj : j < l.length), l[j].1 ≠ a) → l.lookup a = none
  | [], _, _ => rfl
  | (k, v) :: l, a, h => by
    have hk : k ≠ a := h 0 (by simp)
    simp only [List.lookup, show (a == k) = false from beq_false_of_ne (Ne.symm hk)]
    exact lookup_none l a fun j hj ↦ h (j + 1) (by simpa using hj)

theorem xor_eq_one_iff (a b : Nat) : a ^^^ b = 1 ↔ b = a ^^^ 1 := by
  constructor
  · intro h; rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro h; rw [h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- **A parent's digest** is the model's `hashPair`. -/
theorem keccak_pair (a b : Digest) :
    keccak256 (digestBytes a ++ digestBytes b) = NativeVm.Model.hashPair a b := by
  rw [keccak256]
  exact congrArg Id.run (Equiv.hashPair_eq a b)

/-! ## Nodes in memory -/

theorem NodeAt.of_sameOutside {d d' : Mem 64} {a : BitVec 64} {x : Nat × Digest}
    {R : BitVec 64 → Prop} (h : NodeAt d a x) (hs : SameOutside d d' R)
    (hR : ∀ i < 40, ¬R (a + BitVec.ofNat 64 i)) : NodeAt d' a x := by
  refine ⟨h.1, h.2.1.of_sameOutside hs fun i hi ↦ hR i (by rw [length_wordBytes] at hi; omega),
    h.2.2.of_sameOutside hs fun i hi ↦ ?_⟩
  have : i < 32 := by rw [length_wordsBytes] at hi; simpa using hi
  rw [addr_add_add]
  exact hR _ (by omega)

/-- **Nodes kept** by a change outside them. -/
theorem NodesAt.of_sameOutside {d d' : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)}
    {R : BitVec 64 → Prop} (h : NodesAt d a l) (hs : SameOutside d d' R)
    (hR : ∀ i < 40 * l.length, ¬R (a + BitVec.ofNat 64 i)) : NodesAt d' a l := fun j hj ↦
  (h j hj).of_sameOutside hs fun i hi ↦ by
    rw [addr_add_add]; exact hR _ (by omega)

/-- A node at an address is the one. -/
theorem NodeAt.unique {d : Mem 64} {a : BitVec 64} {x y : Nat × Digest} (h : NodeAt d a x)
    (h' : NodeAt d a y) : x = y := by
  obtain ⟨hx, hk, hw⟩ := h
  obtain ⟨hy, hk', hw'⟩ := h'
  have e1 := congrArg UInt64.toNat (hk.unique hk')
  rw [toNat_toUInt64_of_lt hx, toNat_toUInt64_of_lt hy] at e1
  exact Prod.ext e1 (Vector.toList_inj.mp (wordsAt_unique hw hw' (by simp)))

/-- **Nodes at an address** are the ones, given their count. -/
theorem NodesAt.unique {d : Mem 64} {a : BitVec 64} {l l' : List (Nat × Digest)}
    (h : NodesAt d a l) (h' : NodesAt d a l') (hl : l.length = l'.length) : l = l' :=
  List.ext_getElem hl fun i hi hi' ↦ (h i hi).unique (h' i hi')

/-- **One node more**, written after them. -/
theorem NodesAt.snoc {d d' : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)} {x : Nat × Digest}
    (h : NodesAt d a l) (hx : NodeAt d' (a + BitVec.ofNat 64 (40 * l.length)) x)
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 (40 * l.length)) 40))
    (hnw : NoWrap a (40 * (l.length + 1))) : NodesAt d' a (l ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]
    refine (h j hj).of_sameOutside hs fun i hi ↦ ?_
    rw [addr_add_add]
    exact not_inRange_sub hnw (by omega) (by omega) (.inl (by omega))
  · rw [List.getElem_append_right (le_refl _)]
    simpa using hx

end

end NativeRustcVm.Wire
