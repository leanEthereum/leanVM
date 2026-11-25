module

public import LeanVM.Guest.ExecCore

/-!
# Sets of frame offsets as the bits of a number

The frame walk's written and nonzero frame cells (`FSt.w`, `FSt.nz`) are sets of offsets. As a
`Trie Unit`, a test or an insertion walks a path of the trie, which the kernel reduces node by
node; as the bits of a natural number, each is one of the `Nat` operations the kernel computes on
binary numbers (`Nat.land`, `Nat.lor`, `Nat.shiftRight`, `Nat.pow`), and so are a join's
intersection (`inter`) and a cut's inclusion (`sub`). A set keeps the keys below `lim`, those a
trie of depth `Exec.envDepth` keeps.
-/

namespace LeanVM.Guest.CoreMode.Bits

open LeanVM.Guest.Exec

@[expose] public section

/-- The keys a set keeps: those `Trie.set` at depth `envDepth` stores. -/
def lim : ℕ := 2 ^ envDepth - 1

/-- Key `o` is in the set `s`. -/
def has (s o : ℕ) : Bool := s.testBit o

/-- Key `o` added (dropped from `lim` on). -/
def add (s o : ℕ) : ℕ := if o < lim then s ||| 2 ^ o else s

/-- Keys `base` to `base + n - 1` added (those below `lim`). -/
def addRun (s base n : ℕ) : ℕ := s ||| (2 ^ (min (base + n) lim - base) - 1) <<< base

/-- The keys of both sets. -/
def inter (a b : ℕ) : ℕ := a &&& b

/-- Every key of `a` is one of `b`. -/
def sub (a b : ℕ) : Bool := Nat.beq (a &&& b) a

/-- The keys `l` as a set. -/
def ofList (l : List ℕ) : ℕ := l.foldl add 0

/-- The numbers `l` as a set, of any size (an oracle's offsets in a function). -/
def ofNats (l : List ℕ) : ℕ := l.foldl (fun s o ↦ s ||| 2 ^ o) 0

/-- The keys a trie of units stores, by its layout (`Trie`: `0` at the root, `2m + 1` and
`2m + 2` at key `m` of the left and right children). -/
def keys : Trie Unit → List ℕ
  | .nil => []
  | .node v l r => (match v with
      | some () => [0]
      | none => []) ++ ((keys l).map fun m ↦ 2 * m + 1) ++ (keys r).map fun m ↦ 2 * m + 2

/-- The keys a trie of units stores, as a set. -/
def ofTrie (t : Trie Unit) : ℕ := ofList (keys t)

end

public section

theorem has_zero (o : ℕ) : has 0 o = false := Nat.zero_testBit o

private theorem has_or_pow {s o m : ℕ} (h : has (s ||| 2 ^ o) m = true) : m = o ∨ has s m = true := by
  simp only [has, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h.symm.imp Eq.symm id

theorem has_add {s o m : ℕ} (h : has (add s o) m = true) : m = o ∨ has s m = true := by
  unfold add at h
  split_ifs at h
  exacts [has_or_pow h, .inr h]

theorem has_addRun {s base n j : ℕ} (h : has (addRun s base n) j = true) :
    has s j = true ∨ (base ≤ j ∧ j < base + n ∧ j < lim) := by
  simp only [has, addRun, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.imp_right fun ⟨h1, h2⟩ ↦ ⟨h1, by omega, by omega⟩

theorem has_inter {a b n : ℕ} (h : has (inter a b) n = true) : has a n = true ∧ has b n = true := by
  simpa [has, inter] using h

theorem has_of_sub {a b n : ℕ} (hs : sub a b = true) (h : has a n = true) : has b n = true := by
  rw [has, ← Nat.eq_of_beq_eq_true hs, Nat.testBit_and, Bool.and_eq_true] at h
  exact h.2

theorem sub_refl (a : ℕ) : sub a a = true := by simp [sub, Nat.and_self]

/-- A fold of insertions, each adding at most its key, adds at most the list's keys. -/
private theorem has_foldl (f : ℕ → ℕ → ℕ) (hf : ∀ {s o m}, has (f s o) m = true → m = o ∨ has s m = true) :
    ∀ (l : List ℕ) (s : ℕ) {n : ℕ}, has (l.foldl f s) n = true → n ∈ l ∨ has s n = true
  | [], _, _, h => .inr h
  | _ :: l, _, _, h => (has_foldl f hf l _ h).elim (.inl ∘ List.mem_cons_of_mem _)
      fun h ↦ (hf h).imp (List.mem_cons.2 ∘ .inl) id

theorem has_ofList {l : List ℕ} {n : ℕ} (h : has (ofList l) n = true) : n ∈ l :=
  (has_foldl add has_add l 0 h).resolve_right (by simp [has_zero])

theorem has_ofNats {l : List ℕ} {n : ℕ} (h : has (ofNats l) n = true) : n ∈ l :=
  (has_foldl _ has_or_pow l 0 h).resolve_right (by simp [has_zero])

theorem get_of_mem_keys : ∀ {t : Trie Unit} {n : ℕ}, n ∈ keys t → t.get n = some ()
  | .nil, _, h => by simp [keys] at h
  | .node v l r, n, h => by
    rw [Trie.get_node]
    simp only [keys, List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨m, hm, rfl⟩) | ⟨m, hm, rfl⟩
    · rcases v with _ | ⟨⟩ <;> simp at h
      simp [h]
    · rw [ite_eq_right (by omega : ¬2 * m + 1 = 0), ite_eq_left (by omega : (2 * m + 1) % 2 = 1),
        show (2 * m + 1) / 2 = m by omega]
      exact get_of_mem_keys hm
    · rw [ite_eq_right (by omega : ¬2 * m + 2 = 0), ite_eq_right (by omega : ¬(2 * m + 2) % 2 = 1),
        show (2 * m + 2) / 2 - 1 = m by omega]
      exact get_of_mem_keys hm

theorem get_of_has_ofTrie {t : Trie Unit} {n : ℕ} (h : has (ofTrie t) n = true) : t.get n = some () :=
  get_of_mem_keys (has_ofList h)

end

end LeanVM.Guest.CoreMode.Bits
