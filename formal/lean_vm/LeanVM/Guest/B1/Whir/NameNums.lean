/-
  LeanVM.Guest.B1.Whir.NameNums

  The specializations' names are their numbers in decimal, each after `_L`: a name determines its
  numbers, so a table of named entries is looked up by numbers.
-/

module

public import LeanVM.Guest.B1.Whir.Config
public import Mathlib.Tactic.IntervalCases

/-!
# Names of numbers

A specialization's name is a base and its numbers, the others each after `_L` (`keyStr`,
`numsStr`, `natStr`): `level_positions__L28_L15_L3` is `keyStr "level_positions__L" [28, 15, 3]`.
The digits are no separator, so the numbers are read back (`keyStr_inj`, through `natStr_inj`:
`natStr` is decimal). Hence in a table whose every name is its base and its entry's numbers, the entry found by
a name is the entry found by the name's numbers (`find_name_key`): the kernel compares numbers,
not strings.
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- Numbers, each after `_L`. -/
def numsStr : List ℕ → String
  | [] => ""
  | n :: ns => "_L" ++ natStr n ++ numsStr ns

/-- A decimal digit's value. -/
def digitV (c : Char) : ℕ := c.toNat - 48

/-- Decimal digits' value. -/
def decV (cs : List Char) : ℕ := cs.foldl (fun a c => 10 * a + digitV c) 0

theorem digitLit_isDigit (d : ℕ) : (digitLit d).isDigit = true := by
  unfold digitLit; split <;> decide

theorem digitV_digitLit {d : ℕ} (h : d < 10) : digitV (digitLit d) = d := by
  interval_cases d <;> rfl

theorem natStrAux_digits : ∀ (f n : ℕ), ∀ c ∈ (natStrAux f n).toList, c.isDigit = true
  | 0, _, c, h => by simp [natStrAux] at h
  | f + 1, n, c, h => by
    unfold natStrAux at h
    split at h
    · simp only [String.toList_singleton, List.mem_singleton] at h
      exact h ▸ digitLit_isDigit n
    · simp only [String.toList_append, String.toList_singleton, List.mem_append,
        List.mem_singleton] at h
      rcases h with h | rfl
      · exact natStrAux_digits f _ c h
      · exact digitLit_isDigit _

theorem decV_natStrAux : ∀ (f n : ℕ), n < f → decV (natStrAux f n).toList = n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, n, h => by
    unfold natStrAux
    split
    · rename_i hn
      simp only [String.toList_singleton, decV, List.foldl_cons, List.foldl_nil, Nat.mul_zero,
        Nat.zero_add, digitV_digitLit hn]
    · rename_i hn
      have ih := decV_natStrAux f (n / 10) (by omega)
      simp only [decV, String.toList_append, String.toList_singleton, List.foldl_append,
        List.foldl_cons, List.foldl_nil] at ih ⊢
      rw [ih, digitV_digitLit (Nat.mod_lt _ (by omega))]
      omega

theorem natStr_digits (n : ℕ) : ∀ c ∈ (natStr n).toList, c.isDigit = true :=
  natStrAux_digits _ _

theorem natStr_inj {a b : ℕ} (h : natStr a = natStr b) : a = b := by
  have ha := decV_natStrAux (a + 1) a (Nat.lt_succ_self a)
  have hb := decV_natStrAux (b + 1) b (Nat.lt_succ_self b)
  unfold natStr at h
  rw [← ha, ← hb, h]

/-- Digits then a list not starting with a digit: the digits are read off. -/
theorem digits_append_cancel {u v r r' : List Char} (hu : ∀ c ∈ u, c.isDigit = true)
    (hv : ∀ c ∈ v, c.isDigit = true) (hr : ∀ c ∈ r.head?, c.isDigit = false)
    (hr' : ∀ c ∈ r'.head?, c.isDigit = false) (h : u ++ r = v ++ r') : u = v ∧ r = r' := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact ⟨rfl, h⟩
    | cons d v =>
      simp only [List.nil_append, List.cons_append] at h
      subst h
      have := hr d (by simp)
      rw [hv d (by simp)] at this
      exact absurd this (by decide)
  | cons c u ih =>
    cases v with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      subst h
      have := hr' c (by simp)
      rw [hu c (by simp)] at this
      exact absurd this (by decide)
    | cons d v =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨e, e'⟩ := ih (fun x hx => hu x (List.mem_cons_of_mem _ hx))
        (fun x hx => hv x (List.mem_cons_of_mem _ hx)) h
      exact ⟨e ▸ rfl, e'⟩

theorem numsStr_head : ∀ (ns : List ℕ), ∀ c ∈ (numsStr ns).toList.head?, c.isDigit = false
  | [], c, h => by simp [numsStr] at h
  | n :: ns, c, h => by
    simp only [numsStr, String.toList_append, List.head?_append] at h
    have : ("_L" : String).toList.head? = some '_' := by decide
    rw [this] at h
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at h
    subst h
    decide

theorem numsStr_inj : ∀ {a b : List ℕ}, numsStr a = numsStr b → a = b
  | [], [], _ => rfl
  | [], n :: ns, h | n :: ns, [], h => by
    have := congrArg (fun s : String => s.toList.length) h
    simp only [numsStr, String.toList_append, List.length_append] at this
    have h2 : ("_L" : String).toList.length = 2 := by decide
    simp only [h2] at this
    have : ("" : String).toList.length = 0 := by decide
    omega
  | n :: ns, m :: ms, h => by
    rw [← String.toList_inj] at h
    simp only [numsStr, String.toList_append, List.append_assoc] at h
    have h2 := List.append_cancel_left h
    obtain ⟨e1, e2⟩ := digits_append_cancel (natStr_digits n) (natStr_digits m) (numsStr_head ns)
      (numsStr_head ms) h2
    rw [natStr_inj (String.toList_inj.mp e1), numsStr_inj (String.toList_inj.mp e2)]

theorem natStr_ne_nil (n : ℕ) : (natStr n).toList ≠ [] := by
  unfold natStr natStrAux
  split
  · simp
  · simp

/-- A name: the base `pre`, the first number, then the others each after `_L`, appended left to
right as the templates write their names (so a template's name is `keyStr` by `rfl`). -/
def keyStr (pre : String) : List ℕ → String
  | [] => pre
  | n :: ns => ns.foldl (fun s m => s ++ "_L" ++ natStr m) (pre ++ natStr n)

theorem foldl_numsStr (x : String) : ∀ ns : List ℕ,
    (ns.foldl (fun s m => s ++ "_L" ++ natStr m) x).toList = x.toList ++ (numsStr ns).toList
  | [] => by simp [numsStr]
  | m :: ms => by
    simp only [List.foldl_cons, foldl_numsStr _ ms, numsStr, String.toList_append, List.append_assoc]

theorem keyStr_inj {pre : String} : ∀ {a b : List ℕ}, keyStr pre a = keyStr pre b → a = b
  | [], [], _ => rfl
  | [], n :: ns, h | n :: ns, [], h => by
    have := congrArg (fun s : String => s.toList.length) h
    simp only [keyStr, foldl_numsStr, String.toList_append, List.length_append] at this
    have := List.length_pos_iff.mpr (natStr_ne_nil n)
    omega
  | n :: ns, m :: ms, h => by
    rw [← String.toList_inj] at h
    simp only [keyStr, foldl_numsStr, String.toList_append, List.append_assoc] at h
    obtain ⟨e1, e2⟩ := digits_append_cancel (natStr_digits n) (natStr_digits m) (numsStr_head ns)
      (numsStr_head ms) (List.append_cancel_left h)
    rw [natStr_inj (String.toList_inj.mp e1), numsStr_inj (String.toList_inj.mp e2)]

/-- **A table of named entries, looked up by numbers**: when every entry's name is its numbers'
(by a name function that determines them), the entry of a name is the entry of its numbers. -/
theorem find_name_key {α : Type} (T : List (String × α)) (name : List ℕ → String)
    (hinj : ∀ {a b}, name a = name b → a = b) (key : α → List ℕ)
    (hT : ∀ e ∈ T, e.1 = name (key e.2)) (ns : List ℕ) :
    T.find? (fun e => e.1 == name ns) = T.find? (fun e => key e.2 == ns) := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    have he : (e.1 == name ns) = (key e.2 == ns) := by
      rw [hT e List.mem_cons_self]
      by_cases hk : key e.2 = ns
      · simp [hk]
      · have : name (key e.2) ≠ name ns := fun h => hk (hinj h)
        simp [hk, this]
    rw [List.find?_cons, List.find?_cons, he, ih fun x hx => hT x (List.mem_cons_of_mem _ hx)]

/-- `find_name_key`, the names compared by `decide`. -/
theorem find_name_key_dec {α : Type} (T : List (String × α)) (name : List ℕ → String)
    (hinj : ∀ {a b}, name a = name b → a = b) (key : α → List ℕ)
    (hT : ∀ e ∈ T, e.1 = name (key e.2)) (ns : List ℕ) :
    T.find? (fun e => decide (e.1 = name ns)) = T.find? (fun e => key e.2 == ns) := by
  rw [← find_name_key T name hinj key hT ns]
  congr 1

/-- **Membership by numbers**: when every entry's name is its numbers', an entry with the name of
`x`'s numbers is in the table exactly when `x` is among its entries' numbers. -/
theorem mem_name_key {α : Type} (T : List (String × α)) (name : List ℕ → String) (key : α → List ℕ)
    (hT : ∀ e ∈ T, e.1 = name (key e.2)) (x : α) : (name (key x), x) ∈ T ↔ x ∈ T.map (·.2) := by
  constructor
  · intro h; exact List.mem_map.mpr ⟨_, h, rfl⟩
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    rw [← hT e he]
    exact he

end
end LeanVM.Guest.B1.Whir
