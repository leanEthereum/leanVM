/-
  LeanVM.Guest.B1.Fwd.Canon

  An evaluated straight-line body holds, its side conditions (loads, assertions) given; and a
  body of such statements then a `ret` holds as a block.
-/

module

public import LeanVM.Guest.B1.Fwd.Eval

/-!
# Holding an evaluated body

* `needsSide a`: the atoms whose side condition is not automatic (loads, assertions, a quotient,
  `frameAddr`); `atoms_holds`: with the equations of every atom (`Good`), and for each atom
  needing it its relation or its side condition, every atom holds.
* `holdsList_straight`: atoms and calls holding, then a `ret`, make the block hold.
-/

namespace LeanVM.Guest.B1.Fwd

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak

@[expose] public section

variable {rd : Reader} {S : List Atom} {w : Nat → E}

/-! ## Side conditions -/

/-- The atoms whose side condition is not automatic. -/
def needsSide : Atom → Bool
  | .load .. | .assertEq .. | .assertInK .. | .assertNe .. | .rangeCheck .. | .frameAddr .. => true
  | .mul d x y => !(decide (x.idx < d.idx) && decide (y.idx < d.idx))
  | _ => false

/-- **An evaluated block of atoms holds**: its equations, and the relation or the side condition
of each atom that needs one. -/
theorem atoms_holds {σ : Val} {atoms : List Atom} (hg : ∀ a ∈ atoms, Good rd S w σ a)
    (hn : ∀ a ∈ atoms, needsSide a = true → a.Holds rd σ ∨ Side rd S σ a) :
    ∀ a ∈ atoms, a.Holds rd σ := by
  intro a ha
  cases hns : needsSide a
  · refine holds_of_good (hg a ha) ?_
    cases a with
    | mul d x y =>
      simp only [needsSide, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at hns
      simp only [Side]
      rw [ite_pos' hns]
      trivial
    | load | assertEq | assertInK | assertNe | rangeCheck | frameAddr => simp [needsSide] at hns
    | _ => trivial
  · rcases hn a ha hns with h | h
    · exact h
    · exact holds_of_good (hg a ha) h

/-! ## Pure atoms, and stores after the rest -/

/-- The atoms whose equations are their relations: constants, sums, copies, products. -/
def pureB : Atom → Bool
  | .const .. | .add .. | .copy .. => true
  | .mul d x y => decide (x.idx < d.idx) && decide (y.idx < d.idx)
  | _ => false

theorem holds_of_pure {σ : Val} {a : Atom} (hp : pureB a = true) (hg : Good rd S w σ a) :
    a.Holds rd σ := by
  cases a with
  | const => exact hg
  | add => exact hg
  | copy => exact hg
  | mul d x y =>
    simp only [pureB, Bool.and_eq_true, decide_eq_true_eq] at hp
    simp only [Good] at hg
    rwa [ite_pos' hp] at hg
  | _ => simp [pureB] at hp

theorem pure_holds {σ : Val} {atoms : List Atom} (hg : ∀ a ∈ atoms, Good rd S w σ a) :
    ∀ a ∈ atoms.filter pureB, a.Holds rd σ := fun a ha =>
  holds_of_pure (List.mem_filter.mp ha).2 (hg a (List.mem_filter.mp ha).1)

/-- **An evaluated block with stores holds**: the atoms but the stores `S` hold as in
`atoms_holds`, then the stores, given the rest. -/
theorem atoms_holds_stores {σ : Val} {atoms : List Atom} (hg : ∀ a ∈ atoms, Good rd S w σ a)
    (hn : ∀ a ∈ atoms, a ∉ S → needsSide a = true → a.Holds rd σ ∨ Side rd S σ a)
    (hs : (∀ a ∈ atoms, a ∉ S → a.Holds rd σ) → ∀ a ∈ atoms, a ∈ S → a.Holds rd σ) :
    ∀ a ∈ atoms, a.Holds rd σ := by
  have h1 : ∀ a ∈ atoms, a ∉ S → a.Holds rd σ := by
    intro a ha hS
    exact atoms_holds (atoms := [a]) (fun b hb => by rw [List.mem_singleton.mp hb]; exact hg a ha)
      (fun b hb hns => by rw [List.mem_singleton.mp hb] at hns ⊢; exact hn a ha hS hns) a
      List.mem_cons_self
  intro a ha
  by_cases hS : a ∈ S
  · exact hs h1 a ha hS
  · exact h1 a ha hS

/-! ## Blocks -/

/-- A statement's relation, its continuation aside (`False` for a branch or a `ret`). -/
def SHolds (C : CallRel) (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .call f args rets => C f (args.map σ) (rets.map σ)
  | .callIf c f args => IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) [])
  | .dispatch x fs args rets =>
      ∃ (j : Nat) (h : j < fs.length), σ x = ofK (addressOfIndex j) ∧ C fs[j] (args.map σ)
          (rets.map σ)
  | _ => False

/-- **A straight block then a `ret` holds.** -/
theorem holdsList_straight {C : CallRel} {σ : Val} :
    ∀ (ss : List Stmt) (vs : List V) (next : Prop) (kret : List E → Prop),
      (∀ s ∈ ss, SHolds C rd σ s) → kret (vs.map σ) →
        Stmt.HoldsList C rd σ (ss ++ [.ret vs]) next kret
  | [], vs, next, kret, _, hr => by
    simp only [List.nil_append, Stmt.HoldsList, Stmt.Holds]
    exact hr
  | s :: ss, vs, next, kret, hs, hr => by
    have ih := holdsList_straight ss vs next kret (fun t ht => hs t (List.mem_cons_of_mem _ ht)) hr
    have h0 := hs s List.mem_cons_self
    simp only [List.cons_append, Stmt.HoldsList]
    cases s with
    | atom a => exact ⟨h0, ih⟩
    | call f args rets => exact ⟨h0, ih⟩
    | callIf c f args => exact ⟨h0.1, h0.2, ih⟩
    | dispatch x fs args rets => exact ⟨h0, ih⟩
    | _ => exact h0.elim

end
end LeanVM.Guest.B1.Fwd
