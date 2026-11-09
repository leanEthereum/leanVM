/-
  LeanVM.Guest.B1.Fwd.Canon

  An evaluated straight-line body holds: canonical `KECCAK` inputs tracked by kernel evaluation,
  the remaining side conditions (loads, assertions) given; and a body of such statements then a
  `ret` holds as a block.
-/

module

public import LeanVM.Guest.B1.Fwd.Eval

/-!
# Holding an evaluated body

* `canonChk A atoms`: walking the atoms, the values known canonical (`A`, then every `KECCAK`
  output, a constant without `y²` limb, a sum of two known ones, a copy of one) include every
  `KECCAK` input; `canonGo_sound`: then every `KECCAK` input is canonical once the values `A`
  are.
* `needsSide a`: the atoms whose side condition is not automatic (loads, assertions, a quotient,
  `frameAddr`); `atoms_holds`: with the equations of every atom (`Good`), the canonical values
  `A`, and for each atom needing it its relation or its side condition, every atom holds.
* `holdsList_straight`: atoms and calls holding, then a `ret`, make the block hold.
-/

namespace LeanVM.Guest.B1.Fwd

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak

@[expose] public section

/-! ## Canonical values -/

/-- The walk: `K` the values known canonical. -/
def canonGo : List Nat → List Atom → Bool
  | _, [] => true
  | K, .keccak ins outs _ _ :: as => ins.all (fun v => K.contains v.idx) && canonGo (outs.map V.idx ++ K) as
  | K, .add d x y :: as => canonGo (if K.contains x.idx && K.contains y.idx then d.idx :: K else K) as
  | K, .copy d s :: as => canonGo (if K.contains s.idx then d.idx :: K else K) as
  | K, .const d e :: as => canonGo (if decide (e.limb 2 = 0) then d.idx :: K else K) as
  | K, _ :: as => canonGo K as

/-- **The canonical-input checker**, from the values `A`. -/
def canonChk (A : List Nat) (atoms : List Atom) : Bool := canonGo A atoms

theorem canon_add' {a b : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b) :
    IsCanonical128 (a + b) := by
  unfold IsCanonical128 at *
  rw [limb_add, ha, hb, add_zero]

theorem canon_cellsOfState (S : KeccakState) (odd : Bool) (c : Fin 13) :
    IsCanonical128 (cellsOfState S odd c) := by
  unfold IsCanonical128 cellsOfState
  rw [ofLimbs_limb2]

variable {rd : Reader} {S : List Atom} {w : Nat → E}

theorem canonGo_sound {σ : Val} (hσ : ∀ v, σ v = σ (.n v.idx)) :
    ∀ (K : List Nat) (atoms : List Atom), canonGo K atoms = true →
      (∀ a ∈ atoms, Good rd S w σ a) → (∀ i ∈ K, IsCanonical128 (σ (.n i))) →
      ∀ ins outs i o, Atom.keccak ins outs i o ∈ atoms → ∀ v ∈ ins, IsCanonical128 (σ v)
  | _, [], _, _, _, _, _, _, _, hm => absurd hm (by simp)
  | K, a :: as, h, hg, hK, ins, outs, i, o, hm => by
    have hg' : ∀ b ∈ as, Good rd S w σ b := fun b hb => hg b (List.mem_cons_of_mem _ hb)
    cases a with
    | keccak ins' outs' i' o' =>
      simp only [canonGo, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
      obtain ⟨hin, h⟩ := h
      have hK' : ∀ j ∈ outs'.map V.idx ++ K, IsCanonical128 (σ (.n j)) := by
        intro j hj
        rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hj
          obtain ⟨-, hlo, hk⟩ := (hg _ List.mem_cons_self : Good rd S w σ (.keccak ins' outs' i' o'))
          obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hu
          have := hk ⟨k, by omega⟩ hk'
          rw [← hσ, this]
          exact canon_cellsOfState _ _ _
        · exact hK j hj
      rcases List.mem_cons.mp hm with e | hm
      · cases e
        intro v hv
        rw [hσ]
        exact hK _ (by simpa using hin v hv)
      · exact canonGo_sound hσ _ as h hg' hK' ins outs i o hm
    | add d x y =>
      simp only [canonGo] at h
      rcases List.mem_cons.mp hm with e | hm
      · cases e
      refine canonGo_sound hσ _ as h hg' ?_ ins outs i o hm
      split
      · rename_i hc
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · have hd : σ d = σ x + σ y := hg _ List.mem_cons_self
          rw [← hσ, hd, hσ x, hσ y]
          exact canon_add' (hK _ (by simpa using hc.1)) (hK _ (by simpa using hc.2))
        · exact hK j hj
      · exact hK
    | copy d s =>
      simp only [canonGo] at h
      rcases List.mem_cons.mp hm with e | hm
      · cases e
      refine canonGo_sound hσ _ as h hg' ?_ ins outs i o hm
      split
      · rename_i hc
        simp only [List.contains_iff_mem] at hc
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · have hd : σ d = σ s := hg _ List.mem_cons_self
          rw [← hσ, hd, hσ s]
          exact hK _ (by simpa using hc)
        · exact hK j hj
      · exact hK
    | const d e =>
      simp only [canonGo] at h
      rcases List.mem_cons.mp hm with e' | hm
      · cases e'
      refine canonGo_sound hσ _ as h hg' ?_ ins outs i o hm
      split
      · rename_i hc
        simp only [decide_eq_true_eq] at hc
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · have hd : σ d = e := hg _ List.mem_cons_self
          rw [← hσ, hd]
          exact hc
        · exact hK j hj
      · exact hK
    | _ =>
      simp only [canonGo] at h
      rcases List.mem_cons.mp hm with e | hm
      · cases e
      exact canonGo_sound hσ _ as h hg' hK ins outs i o hm

/-! ## Side conditions -/

/-- The atoms whose side condition is not automatic. -/
def needsSide : Atom → Bool
  | .load .. | .assertEq .. | .assertInK .. | .assertNe .. | .rangeCheck .. | .frameAddr .. => true
  | .mul d x y => !(decide (x.idx < d.idx) && decide (y.idx < d.idx))
  | _ => false

/-- **An evaluated block of atoms holds**: its equations, its canonical values `A`, and the
relation or the side condition of each atom that needs one. -/
theorem atoms_holds {σ : Val} (hσ : ∀ v, σ v = σ (.n v.idx)) {A : List Nat} {atoms : List Atom}
    (hk : canonChk A atoms = true) (hg : ∀ a ∈ atoms, Good rd S w σ a)
    (hA : ∀ i ∈ A, IsCanonical128 (σ (.n i)))
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
    | keccak ins outs i o =>
      intro c
      obtain ⟨hl, -, -⟩ := (hg _ ha : Good rd S w σ (.keccak ins outs i o))
      have := canonGo_sound hσ A atoms hk hg hA ins outs i o ha
      simp only [cells13, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (show c.val < ins.length by omega), Option.map_some,
        Option.getD_some]
      exact this _ (List.getElem_mem _)
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
`atoms_holds` (their canonical inputs checked without the stores), then the stores, given the
rest. The membership test is any decision procedure (`Sig.Decide`'s `Atom` equality reaches some
importers as an instance). -/
theorem atoms_holds_stores {σ : Val} (hσ : ∀ v, σ v = σ (.n v.idx)) {A : List Nat}
    {atoms : List Atom} {dec : ∀ a : Atom, Decidable (a ∉ S)}
    (hk : canonChk A (atoms.filter (fun a => @decide (a ∉ S) (dec a))) = true)
    (hg : ∀ a ∈ atoms, Good rd S w σ a) (hA : ∀ i ∈ A, IsCanonical128 (σ (.n i)))
    (hn : ∀ a ∈ atoms, a ∉ S → needsSide a = true → a.Holds rd σ ∨ Side rd S σ a)
    (hs : (∀ a ∈ atoms, a ∉ S → a.Holds rd σ) → ∀ a ∈ atoms, a ∈ S → a.Holds rd σ) :
    ∀ a ∈ atoms, a.Holds rd σ := by
  have h1 : ∀ a ∈ atoms, a ∉ S → a.Holds rd σ := by
    have := atoms_holds hσ hk (fun a ha => hg a (List.mem_filter.mp ha).1) hA
      (fun a ha hns => hn a (List.mem_filter.mp ha).1
        (by simpa using (List.mem_filter.mp ha).2) hns)
    exact fun a ha hS => this a (List.mem_filter.mpr ⟨ha, by simpa using hS⟩)
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
