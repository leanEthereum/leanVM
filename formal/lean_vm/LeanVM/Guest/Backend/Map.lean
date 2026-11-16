/-
  LeanVM.Guest.Backend.Map

  The back end's maps and sequences, written so that the kernel evaluates them: tries keyed by
  `ℕ`, maps of values and of names over them, and sequences built at their end.
-/

module

public import LeanVM.Guest.Core

/-!
# Maps the kernel evaluates

The back end runs compiled (`guest-backend`) and in the kernel (`decide +kernel`, `kernel_rfl`, on
the guest), so its state is in structures the kernel reduces quickly: `Std.HashMap` does not
reduce there, `Std.TreeMap` does but slowly, an `Array` is a list (an index, a push and a size are
linear), and comparing two strings decodes both.

* `Trie α`, keyed by `ℕ`: key `0` at the root, `2m+1` at key `m` of the left child, `2m+2` at key
  `m` of the right one. `get` and `set` are written with the recursors and raw `Nat` operations,
  which the kernel reduces fastest; compiled code runs their structural twins (`getC`, `setC`,
  `@[csimp]`). `set` keeps its result evaluated (`seq`), the kernel sharing no evaluation between
  the copies of a term.
* `NMap α` (keys `ℕ`), `PMap α` (keys `ℕ × ℕ`, a trie of tries), and the bucketed `VMap α` (keys
  `Core.V`, by `vKey`) and `SMap α` (keys `String`, by `nameKey`): a bucket holds the keys of
  one number, the last inserted first.
* `Rev α`: a sequence built at its end, as a reversed list with its length.

Each map's lemmas are its reads after a write (`get?_insert`, `get?_insertIfNew`), which is all the
back end's proofs use.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Guest.Core (V)

@[expose] public section

/-! ## Tries keyed by `ℕ` -/

/-- A map from `ℕ`: key `0` at the root, `2m+1` at key `m` of the left child, `2m+2` at key `m`
of the right one. -/
inductive Trie (α : Type) where
  | nil
  | node (v : Option α) (l r : Trie α)
  deriving Inhabited

namespace Trie

variable {α β : Type}

/-- `k t`, `t` evaluated first. -/
def seq (t : Trie α) (k : Trie α → β) : β :=
  match t with
  | nil => k nil
  | node v l r => k (node v l r)

theorem seq_eq (t : Trie α) (k : Trie α → β) : t.seq k = k t := by cases t <;> rfl

/-- The value at key `n`. -/
noncomputable def get (t : Trie α) : ℕ → Option α :=
  Trie.rec (motive := fun _ ↦ ℕ → Option α) (fun _ ↦ none)
    (fun v _ _ gl gr n ↦ Nat.rec (motive := fun _ ↦ Option α) v
      (fun m _ ↦ Bool.rec (gr (Nat.div m 2)) (gl (Nat.div m 2)) (Nat.beq (Nat.mod m 2) 0)) n) t

/-- Store `a` at key `n`, within `d` levels (a deeper key is dropped). -/
noncomputable def setD (a : α) (d : ℕ) : Trie α → ℕ → Trie α :=
  Nat.rec (motive := fun _ ↦ Trie α → ℕ → Trie α) (fun t _ ↦ t)
    (fun _ s t n ↦ Trie.casesOn (motive := fun _ ↦ Trie α) t
      (Nat.rec (motive := fun _ ↦ Trie α) (.node (some a) .nil .nil)
        (fun m _ ↦ Bool.rec ((s .nil (Nat.div m 2)).seq fun r ↦ .node none .nil r)
          ((s .nil (Nat.div m 2)).seq fun l ↦ .node none l .nil) (Nat.beq (Nat.mod m 2) 0)) n)
      (fun v l r ↦ Nat.rec (motive := fun _ ↦ Trie α) (.node (some a) l r)
        (fun m _ ↦ Bool.rec ((s r (Nat.div m 2)).seq fun r ↦ .node v l r)
          ((s l (Nat.div m 2)).seq fun l ↦ .node v l r) (Nat.beq (Nat.mod m 2) 0)) n)) d

/-- Store `a` at key `n`. -/
noncomputable def set (t : Trie α) (n : ℕ) (a : α) : Trie α := setD a (n + 1) t n

/-! ### The compiled twins -/

/-- `get` by structural recursion. -/
def getC : Trie α → ℕ → Option α
  | nil, _ => none
  | node v l r, n => if n = 0 then v else if n % 2 = 1 then getC l (n / 2) else getC r (n / 2 - 1)

/-- `setD` by structural recursion. -/
def setDC (a : α) : ℕ → Trie α → ℕ → Trie α
  | 0, t, _ => t
  | d + 1, nil, n =>
      if n = 0 then node (some a) nil nil
      else if n % 2 = 1 then (setDC a d nil (n / 2)).seq fun l ↦ node none l nil
      else (setDC a d nil (n / 2 - 1)).seq fun r ↦ node none nil r
  | d + 1, node v l r, n =>
      if n = 0 then node (some a) l r
      else if n % 2 = 1 then (setDC a d l (n / 2)).seq fun l ↦ node v l r
      else (setDC a d r (n / 2 - 1)).seq fun r ↦ node v l r

theorem nat_beq_mod (m : ℕ) : Nat.beq (Nat.mod m 2) 0 = decide ((m + 1) % 2 = 1) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
  change m % 2 = 0 ↔ _
  omega

theorem div_odd {m : ℕ} (h : (m + 1) % 2 = 1) : Nat.div m 2 = (m + 1) / 2 := by
  change m / 2 = _
  omega

theorem div_even {m : ℕ} (h : ¬(m + 1) % 2 = 1) : Nat.div m 2 = (m + 1) / 2 - 1 := by
  change m / 2 = _
  omega

@[csimp] theorem get_eq_getC : @get = @getC := by
  funext α t n
  induction t generalizing n with
  | nil => rfl
  | node v l r ihl ihr =>
    cases n with
    | zero => rfl
    | succ m =>
      change @Bool.rec (fun _ => Option α) (get r (Nat.div m 2)) (get l (Nat.div m 2))
        (Nat.beq (Nat.mod m 2) 0) = _
      rw [nat_beq_mod, getC, ite_eq_right (Nat.succ_ne_zero m)]
      by_cases h : (m + 1) % 2 = 1
      · rw [decide_eq_true h, ite_eq_left h, div_odd h, ihl]
      · rw [decide_eq_false h, ite_eq_right h, div_even h, ihr]

theorem setD_eq_setDC : @setD = @setDC := by
  funext α a d t n
  induction d generalizing t n with
  | zero => rfl
  | succ d ih =>
    cases t with
    | nil =>
      cases n with
      | zero => rfl
      | succ m =>
        change @Bool.rec (fun _ => Trie α) _ _ (Nat.beq (Nat.mod m 2) 0) = _
        rw [nat_beq_mod, setDC, ite_eq_right (Nat.succ_ne_zero m)]
        by_cases h : (m + 1) % 2 = 1
        · rw [decide_eq_true h, ite_eq_left h, div_odd h]
          exact congrArg (fun x => Trie.seq x _) (ih _ _)
        · rw [decide_eq_false h, ite_eq_right h, div_even h]
          exact congrArg (fun x => Trie.seq x _) (ih _ _)
    | node v l r =>
      cases n with
      | zero => rfl
      | succ m =>
        change @Bool.rec (fun _ => Trie α) _ _ (Nat.beq (Nat.mod m 2) 0) = _
        rw [nat_beq_mod, setDC, ite_eq_right (Nat.succ_ne_zero m)]
        by_cases h : (m + 1) % 2 = 1
        · rw [decide_eq_true h, ite_eq_left h, div_odd h]
          exact congrArg (fun x => Trie.seq x _) (ih _ _)
        · rw [decide_eq_false h, ite_eq_right h, div_even h]
          exact congrArg (fun x => Trie.seq x _) (ih _ _)

/-- `set` by structural recursion. -/
def setC (t : Trie α) (n : ℕ) (a : α) : Trie α := setDC a (n + 1) t n

@[csimp] theorem set_eq_setC : @set = @setC := by
  funext α t n a
  rw [set, setC, setD_eq_setDC]

/-! ### Reads after a write -/

@[simp] theorem getC_nil (n : ℕ) : (nil : Trie α).getC n = none := by
  rw [getC]

/-- The root value. -/
def val : Trie α → Option α
  | nil => none
  | node v _ _ => v

/-- The left child. -/
def left : Trie α → Trie α
  | nil => nil
  | node _ l _ => l

/-- The right child. -/
def right : Trie α → Trie α
  | nil => nil
  | node _ _ r => r

theorem getC_node (v : Option α) (l r : Trie α) (n : ℕ) :
    (node v l r).getC n =
      if n = 0 then v else if n % 2 = 1 then l.getC (n / 2) else r.getC (n / 2 - 1) := by
  rw [getC]

/-- Every trie reads as a node. -/
theorem getC_eq_node (t : Trie α) (n : ℕ) : t.getC n = (node t.val t.left t.right).getC n := by
  cases t with
  | nil => simp [getC_node, val, left, right]
  | node v l r => rfl

theorem setDC_succ (a : α) (d : ℕ) (t : Trie α) (n : ℕ) :
    setDC a (d + 1) t n =
      if n = 0 then node (some a) t.left t.right
      else if n % 2 = 1 then node t.val (setDC a d t.left (n / 2)) t.right
      else node t.val t.left (setDC a d t.right (n / 2 - 1)) := by
  cases t <;> simp only [setDC, seq_eq, val, left, right]

theorem getC_setDC (a : α) : ∀ (d : ℕ) (t : Trie α) (n m : ℕ), n < d →
    (setDC a d t n).getC m = if m = n then some a else t.getC m
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | d + 1, t, n, m, h => by
    rw [setDC_succ, getC_eq_node t m]
    by_cases h0 : n = 0
    · subst h0
      rw [ite_eq_left rfl, getC_node, getC_node]
      by_cases hm : m = 0 <;> simp [hm]
    · rw [ite_eq_right h0]
      by_cases h1 : n % 2 = 1
      · rw [ite_eq_left h1, getC_node, getC_node, getC_setDC a d _ _ _ (by omega)]
        by_cases hm : m = 0
        · simp [hm, Ne.symm h0]
        · by_cases hm1 : m % 2 = 1
          · have : (m / 2 = n / 2) ↔ m = n := by omega
            simp [hm, hm1, this]
          · have : m ≠ n := by omega
            simp [hm, hm1, this]
      · rw [ite_eq_right h1, getC_node, getC_node, getC_setDC a d _ _ _ (by omega)]
        by_cases hm : m = 0
        · simp [hm, Ne.symm h0]
        · by_cases hm1 : m % 2 = 1
          · have : m ≠ n := by omega
            simp [hm, hm1, this]
          · have : (m / 2 - 1 = n / 2 - 1) ↔ m = n := by omega
            simp [hm, hm1, this]

@[simp] theorem get_nil (n : ℕ) : (nil : Trie α).get n = none := rfl

theorem get_set (t : Trie α) (n : ℕ) (a : α) (m : ℕ) :
    (t.set n a).get m = if m = n then some a else t.get m := by
  rw [get_eq_getC, set_eq_setC, setC, getC_setDC a _ _ _ _ (Nat.lt_succ_self n)]

end Trie

/-! ## Maps -/

/-- A map keyed by `ℕ`. -/
structure NMap (α : Type) where
  t : Trie α := .nil
  deriving Inhabited

namespace NMap

variable {α : Type}

/-- The value at key `k`. -/
def get? (m : NMap α) (k : ℕ) : Option α := m.t.get k

/-- Store `a` at key `k`. -/
def insert (m : NMap α) (k : ℕ) (a : α) : NMap α := ⟨m.t.set k a⟩

/-- Whether key `k` has a value. -/
def contains (m : NMap α) (k : ℕ) : Bool := (m.get? k).isSome

/-- Store `a` at key `k` unless it has a value. -/
def insertIfNew (m : NMap α) (k : ℕ) (a : α) : NMap α :=
  match m.get? k with
  | some _ => m
  | none => m.insert k a

@[simp] theorem get?_empty (k : ℕ) : ({} : NMap α).get? k = none := rfl

theorem get?_insert (m : NMap α) (k : ℕ) (a : α) (k' : ℕ) :
    (m.insert k a).get? k' = if k' = k then some a else m.get? k' :=
  Trie.get_set _ _ _ _

theorem get?_insertIfNew (m : NMap α) (k : ℕ) (a : α) (k' : ℕ) :
    (m.insertIfNew k a).get? k' = if k' = k ∧ m.get? k = none then some a else m.get? k' := by
  unfold insertIfNew
  split
  · next h => simp [h]
  · next h =>
    rw [get?_insert]
    by_cases e : k' = k <;> simp [e, h]

end NMap

/-- A map keyed by pairs of `ℕ`: a trie of tries. -/
structure PMap (α : Type) where
  t : Trie (Trie α) := .nil
  deriving Inhabited

namespace PMap

variable {α : Type}

/-- The value at key `k`. -/
def get? (m : PMap α) (k : ℕ × ℕ) : Option α := (m.t.get k.1).bind (·.get k.2)

/-- Store `a` at key `k`. -/
def insert (m : PMap α) (k : ℕ × ℕ) (a : α) : PMap α :=
  ⟨m.t.set k.1 (((m.t.get k.1).getD .nil).set k.2 a)⟩

/-- Whether key `k` has a value. -/
def contains (m : PMap α) (k : ℕ × ℕ) : Bool := (m.get? k).isSome

/-- Store `a` at key `k` unless it has a value. -/
def insertIfNew (m : PMap α) (k : ℕ × ℕ) (a : α) : PMap α :=
  match m.get? k with
  | some _ => m
  | none => m.insert k a

@[simp] theorem get?_empty (k : ℕ × ℕ) : ({} : PMap α).get? k = none := rfl

theorem get?_insert (m : PMap α) (k : ℕ × ℕ) (a : α) (k' : ℕ × ℕ) :
    (m.insert k a).get? k' = if k' = k then some a else m.get? k' := by
  obtain ⟨k1, k2⟩ := k
  obtain ⟨k1', k2'⟩ := k'
  simp only [get?, insert, Trie.get_set, Prod.mk.injEq]
  by_cases h1 : k1' = k1
  · subst h1
    cases m.t.get k1' <;> by_cases h2 : k2' = k2 <;> simp [h2, Trie.get_set]
  · simp [h1]

theorem get?_insertIfNew (m : PMap α) (k : ℕ × ℕ) (a : α) (k' : ℕ × ℕ) :
    (m.insertIfNew k a).get? k' = if k' = k ∧ m.get? k = none then some a else m.get? k' := by
  unfold insertIfNew
  split
  · next h => simp [h]
  · next h =>
    rw [get?_insert]
    by_cases e : k' = k <;> simp [e, h]

end PMap

/-- A key's number: the bucket of a `KMap` it is in. -/
class Keyed (κ : Type) where
  key : κ → ℕ

/-- A map keyed by `κ`, each key in the bucket of its number, the last inserted first. -/
structure KMap (κ α : Type) where
  t : Trie (List (κ × α)) := .nil
  deriving Inhabited

namespace KMap

variable {κ α : Type} [DecidableEq κ] [Keyed κ]

/-- The value at key `k`. -/
def get? (m : KMap κ α) (k : κ) : Option α :=
  ((m.t.get (Keyed.key k)).getD []).lookup k

/-- Store `a` at key `k`. -/
def insert (m : KMap κ α) (k : κ) (a : α) : KMap κ α :=
  ⟨m.t.set (Keyed.key k) ((k, a) :: (m.t.get (Keyed.key k)).getD [])⟩

/-- Whether key `k` has a value. -/
def contains (m : KMap κ α) (k : κ) : Bool := (m.get? k).isSome

/-- The value at key `k`, or `d`. -/
def getD (m : KMap κ α) (k : κ) (d : α) : α := (m.get? k).getD d

instance : GetElem? (KMap κ α) κ α (fun m k => m.contains k = true) where
  getElem m k h := (m.get? k).get (by simpa [contains] using h)
  getElem? m k := m.get? k

theorem getElem?_eq (m : KMap κ α) (k : κ) : m[k]? = m.get? k := rfl

@[simp] theorem get?_empty (k : κ) : ({} : KMap κ α).get? k = none := rfl

@[simp] theorem getElem?_empty (k : κ) : ({} : KMap κ α)[k]? = none := rfl

@[simp] theorem getD_empty (k : κ) (d : α) : ({} : KMap κ α).getD k d = d := rfl

theorem get?_insert (m : KMap κ α) (k : κ) (a : α) (k' : κ) :
    (m.insert k a).get? k' = if k' = k then some a else m.get? k' := by
  simp only [get?, insert, Trie.get_set]
  by_cases hk : Keyed.key k' = Keyed.key k
  · rw [ite_eq_left hk, Option.getD_some, List.lookup_cons, hk]
    by_cases e : k' = k
    · simp [e]
    · have : (k' == k) = false := beq_false_of_ne e
      simp [e, this]
  · rw [ite_eq_right hk]
    have : k' ≠ k := fun e => hk (e ▸ rfl)
    simp [this]

@[simp] theorem getElem?_insert (m : KMap κ α) (k : κ) (a : α) (k' : κ) :
    (m.insert k a)[k']? = if k' = k then some a else m[k']? :=
  get?_insert m k a k'

theorem getElem?_eq_none_of_contains_eq_false {m : KMap κ α} {k : κ} (h : m.contains k = false) :
    m[k]? = none := by
  rw [getElem?_eq]
  simpa [contains] using h

theorem getD_eq_getD_getElem? (m : KMap κ α) (k : κ) (d : α) : m.getD k d = (m[k]?).getD d := rfl

theorem contains_eq_isSome (m : KMap κ α) (k : κ) : m.contains k = (m[k]?).isSome := rfl

end KMap

/-- A value's number: twice its index for a value of no path and tag `0` (every value of the
guest's renumbered input, `V.n`), else odd, by its hash modulo a prime below `2^20`, which keeps
the trie shallow. Values of one number share a bucket. -/
def vKey (v : V) : ℕ :=
  if v.path.isEmpty && v.tag == 0 then 2 * v.idx else 2 * ((hash v).toNat % 1048573) + 1

instance : Keyed V := ⟨vKey⟩

/-- The places of values, by `vKey`. -/
abbrev VMap (α : Type) := KMap V α

/-- A name's number: its bytes folded modulo a prime past `2^20`. Names of one number share a
bucket. -/
def nameKey (s : String) : ℕ :=
  s.toByteArray.data.toList.foldl (fun n b => (n * 257 + b.toNat) % 1048583) 0

instance : Keyed String := ⟨nameKey⟩

/-- A map keyed by names. -/
abbrev SMap (α : Type) := KMap String α

/-! ## Sequences built at their end -/

/-- A sequence built at its end: its elements in reverse, and its length. -/
structure Rev (α : Type) where
  rev : List α := []
  size : ℕ := 0
  size_eq : size = rev.length := by rfl

namespace Rev

variable {α : Type}

instance : Inhabited (Rev α) := ⟨{}⟩

/-- The elements in order. -/
def toList (r : Rev α) : List α := r.rev.reverse

/-- Add `a` at the end. -/
def push (r : Rev α) (a : α) : Rev α := ⟨a :: r.rev, r.size + 1, by rw [r.size_eq]; rfl⟩

/-- The last element. -/
def back? (r : Rev α) : Option α := r.rev.head?

/-- Without its last element. -/
def pop (r : Rev α) : Rev α := ⟨r.rev.tail, r.size - 1, by rw [r.size_eq, List.length_tail]⟩

/-- Whether it is empty. -/
def isEmpty (r : Rev α) : Bool := r.rev.isEmpty

/-- Add the elements of `l` at the end, in order. -/
def appendList (r : Rev α) (l : List α) : Rev α := l.foldl push r

@[simp] theorem toList_empty : ({} : Rev α).toList = [] := rfl

@[simp] theorem size_push (r : Rev α) (a : α) : (r.push a).size = r.size + 1 := rfl

@[simp] theorem size_empty : ({} : Rev α).size = 0 := rfl

@[simp] theorem toList_push (r : Rev α) (a : α) : (r.push a).toList = r.toList ++ [a] := by
  simp [toList, push]

@[simp] theorem toList_appendList (r : Rev α) (l : List α) :
    (r.appendList l).toList = r.toList ++ l := by
  induction l generalizing r with
  | nil => simp [appendList]
  | cons a l ih =>
    simp only [appendList, List.foldl_cons] at ih ⊢
    rw [ih, toList_push, List.append_assoc, List.singleton_append]

theorem size_eq_length (r : Rev α) : r.size = r.toList.length := by
  rw [r.size_eq, toList, List.length_reverse]

theorem back?_eq (r : Rev α) : r.back? = r.toList.getLast? := by
  simp [back?, toList, List.getLast?_reverse]

theorem toList_pop (r : Rev α) : r.pop.toList = r.toList.dropLast := by
  simp [pop, toList, List.dropLast_reverse]

theorem isEmpty_eq (r : Rev α) : r.isEmpty = r.toList.isEmpty := by
  simp [isEmpty, toList]

end Rev

end
end LeanVM.Guest.Backend
