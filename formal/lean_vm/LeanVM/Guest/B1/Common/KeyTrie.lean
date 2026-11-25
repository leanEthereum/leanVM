/-
  LeanVM.Guest.B1.Common.KeyTrie

  A check that every element of one list has a match in another, reading the matches from a trie
  by a numeric key instead of scanning the list once per element.
-/

module

public import Mathlib.Data.List.Basic
public import LeanVM.Guest.Core

/-!
# Matching by key

A kernel check `xs.all fun x ↦ ys.any (ok x)` scans `ys` once per element of `xs`. `allMatch`
builds a binary trie of `ys` by the low bits of a key once (`KeyTrie.build`) and scans, for each
`x`, only the values under `x`'s key. `all_any_of_allMatch` proves the scan's statement from it,
whatever the keys: a wrong key can only make the check fail.
-/

@[expose] public section

namespace LeanVM.Guest.B1

/-- A binary trie of values, branching on a key's bits from the low end. -/
inductive KeyTrie (α : Type) where
  | leaf (vs : List α)
  | node (lo hi : KeyTrie α)

namespace KeyTrie

variable {α β : Type}

/-- The values of a trie. -/
def vals : KeyTrie α → List α
  | leaf vs => vs
  | node lo hi => lo.vals ++ hi.vals

/-- The trie of `l` by `key`, branching on `d` bits from bit `s`. -/
def build (key : α → ℕ) : ℕ → ℕ → List α → KeyTrie α
  | 0, _, l => leaf l
  | _ + 1, _, [] => leaf []
  | d + 1, s, a :: l =>
    node (build key d (s + 1) ((a :: l).filter fun b ↦ !(key b).testBit s))
      (build key d (s + 1) ((a :: l).filter fun b ↦ (key b).testBit s))

/-- The values under key `k`, branching from bit `s`. -/
def find (k : ℕ) : KeyTrie α → ℕ → List α
  | leaf vs, _ => vs
  | node lo hi, s => if k.testBit s then hi.find k (s + 1) else lo.find k (s + 1)

theorem mem_vals_of_mem_find {k : ℕ} {a : α} : ∀ {t : KeyTrie α} {s : ℕ}, a ∈ t.find k s → a ∈ t.vals
  | leaf _, _, h => h
  | node lo hi, s, h => by
    unfold find at h
    split_ifs at h
    · exact List.mem_append_right _ (mem_vals_of_mem_find h)
    · exact List.mem_append_left _ (mem_vals_of_mem_find h)

theorem mem_of_mem_build (key : α → ℕ) {a : α} :
    ∀ {d s : ℕ} {l : List α}, a ∈ (build key d s l).vals → a ∈ l
  | 0, _, _, h => h
  | _ + 1, _, [], h => h
  | d + 1, s, b :: l, h => by
    rcases List.mem_append.1 h with h | h <;> exact (List.mem_filter.1 (mem_of_mem_build key h)).1

end KeyTrie

/-- Every `x ∈ xs` is skipped or has a `y ∈ ys` with `ok x y`, `y` read from the trie of `ys` by
`ky` (depth `d`) under `x`'s key `kx x`. -/
def allMatch {α β : Type} (skip : β → Bool) (kx : β → ℕ) (ky : α → ℕ) (d : ℕ) (ok : β → α → Bool)
    (xs : List β) (ys : List α) : Bool :=
  let t := KeyTrie.build ky d 0 ys
  xs.all fun x ↦ skip x || (t.find (kx x) 0).any (ok x)

theorem all_any_of_allMatch {α β : Type} {skip : β → Bool} {kx : β → ℕ} {ky : α → ℕ} {d : ℕ}
    {ok : β → α → Bool} {xs : List β} {ys : List α} (h : allMatch skip kx ky d ok xs ys = true) :
    xs.all (fun x ↦ skip x || ys.any (ok x)) = true := by
  simp only [allMatch, List.all_eq_true, Bool.or_eq_true, List.any_eq_true] at h ⊢
  refine fun x hx ↦ (h x hx).imp_right fun ⟨y, hy, hok⟩ ↦ ⟨y, ?_, hok⟩
  exact KeyTrie.mem_of_mem_build ky (KeyTrie.mem_vals_of_mem_find hy)

/-- `all_any_of_allMatch` with nothing skipped. -/
theorem all_any_of_allMatch' {α β : Type} {kx : β → ℕ} {ky : α → ℕ} {d : ℕ}
    {ok : β → α → Bool} {xs : List β} {ys : List α}
    (h : allMatch (fun _ ↦ false) kx ky d ok xs ys = true) :
    xs.all (fun x ↦ ys.any (ok x)) = true := by
  simpa using all_any_of_allMatch h

/-- An atom's first value's index: its key in a `KeyTrie`. -/
def atomKey : Core.Atom → ℕ
  | .const d _ | .add d .. | .mul d .. | .copy d _ | .load d .. => d.idx
  | .assertEq a _ | .assertNe a .. | .rangeCheck a .. | .assertInK a _ | .frameAddr a _ => a.idx
  | _ => 0

end LeanVM.Guest.B1
