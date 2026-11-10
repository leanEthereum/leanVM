/-
  LeanVM.Guest.B1.KeccakGkr.LayerCBlock

  A block of atoms on an evaluated valuation holds: its canonical `KECCAK` inputs and its `K`
  assertions checked by kernel evaluation, the remaining atoms (`resid`) given.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.FsComplete
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# Blocks, completely

On a valuation satisfying every atom's equations (`Fwd.Good`), an atom holds by them alone unless
it needs a side condition (`needsSide`): a load, an assertion, a quotient. Of those, an
`assertInK` of two values known in `K` (`inKVals`: a hinted limb, a constant without `y` limbs)
holds by the equations too. `resid as`: the atoms left, which `block_holds` takes as given, with
the canonical `KECCAK` inputs checked by `canonChk`.

`side_loadVia`: a load that is not a store, through a pointer whose words the memory holds, has
its side condition.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- The atoms of a list of statements. -/
def atomsL (B : List Stmt) : List Atom := B.filterMap fun s ↦ match s with
  | .atom a => some a
  | _ => none

theorem mem_atomsL {B : List Stmt} {a : Atom} : a ∈ atomsL B ↔ Stmt.atom a ∈ B := by
  simp only [atomsL, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, h⟩
    cases s <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

/-- The values known in `K` by their equations: hinted limbs, constants without `y` limbs. -/
def inKVals (as : List Atom) : List ℕ := as.flatMap fun a ↦ match a with
  | .hint (.limbs _ ds) => ds.map V.idx
  | .const d e => if e.limb 1 = 0 then [d.idx] else []
  | _ => []

/-- An `assertInK` of two values known in `K`. -/
def inkB (K : List ℕ) : Atom → Bool
  | .assertInK x y => K.contains x.idx && K.contains y.idx
  | _ => false

/-- The atoms whose relation the equations do not give. -/
def resid (as : List Atom) : List Atom :=
  as.filter fun a ↦ needsSide a && !inkB (inKVals as) a

theorem inK_of_inKVals (hσ : ∀ v, σ v = σ (.n v.idx)) {as : List Atom}
    (hg : ∀ a ∈ as, Good rd S w σ a) {i : ℕ} (hi : i ∈ inKVals as) : IsInK (σ (.n i)) := by
  simp only [inKVals, List.mem_flatMap] at hi
  obtain ⟨a, ha, hi⟩ := hi
  have hga := hg a ha
  cases a with
  | hint h =>
    cases h with
    | limbs v ds =>
      simp only [List.mem_map] at hi
      obtain ⟨u, hu, rfl⟩ := hi
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      rw [← hσ, hga j hj, limbAt]
      split
      · exact (isInK_iff _).mpr ⟨_, rfl⟩
      · exact (isInK_iff _).mpr ⟨0, by rw [ofK_zero]⟩
    | _ => simp at hi
  | const d e =>
    simp only at hi
    split at hi
    · rename_i he
      simp only [List.mem_singleton] at hi
      subst hi
      rw [← hσ, hga]
      exact he
    · simp at hi
  | _ => simp at hi

/-- **`block_holds` after a prefix `P`**: the canonical `KECCAK` inputs checked along `P ++ B`,
whose atoms satisfy their equations. -/
theorem block_holdsP {P B : List Stmt} (hall : B.all isAtom = true)
    (hσ : ∀ v, σ v = σ (.n v.idx)) {A : List ℕ} (hk : canonChk A (atomsL (P ++ B)) = true)
    (hg : ∀ s ∈ P ++ B, GoodS rd S w σ s) (hA : ∀ i ∈ A, IsCanonical128 (σ (.n i)))
    (hR : ∀ a ∈ resid (atomsL B), a.Holds rd σ ∨ Side rd S σ a) :
    ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ B next kret := by
  intro next kret hn
  have hgA : ∀ a ∈ atomsL (P ++ B), Good rd S w σ a := fun a ha ↦ hg _ (mem_atomsL.mp ha)
  have hgB : ∀ a ∈ atomsL B, Good rd S w σ a :=
    fun a ha ↦ hg _ (List.mem_append_right _ (mem_atomsL.mp ha))
  have H : ∀ a ∈ atomsL B, a.Holds rd σ := by
    intro a ha
    cases hns : needsSide a
    · refine holds_of_good (hgB a ha) ?_
      cases a with
      | mul d x y =>
        simp only [needsSide, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at hns
        simp only [Side]
        rw [ite_pos' hns]
        trivial
      | keccak ins outs i o =>
        intro c
        obtain ⟨hl, -, -⟩ := (hgB _ ha : Good rd S w σ (.keccak ins outs i o))
        have := canonGo_sound hσ A _ hk hgA hA ins outs i o
          (mem_atomsL.mpr (List.mem_append_right _ (mem_atomsL.mp ha)))
        simp only [cells13, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (show c.val < ins.length by omega), Option.map_some,
          Option.getD_some]
        exact this _ (List.getElem_mem _)
      | load | assertEq | assertInK | assertNe | rangeCheck | frameAddr => simp [needsSide] at hns
      | _ => trivial
    · cases hik : inkB (inKVals (atomsL B)) a
      · rcases hR a (List.mem_filter.mpr ⟨ha, by simp [hns, hik]⟩) with h | h
        · exact h
        · exact holds_of_good (hgB a ha) h
      · cases a with
        | assertInK x y =>
          simp only [inkB, Bool.and_eq_true, List.contains_iff_mem] at hik
          show IsInK (σ x) ∧ IsInK (σ y)
          rw [hσ x, hσ y]
          exact ⟨inK_of_inKVals hσ hgB hik.1, inK_of_inKVals hσ hgB hik.2⟩
        | _ => simp [inkB] at hik
  exact (holdsList_atoms (allAtoms_of_all hall) next kret).2
    ⟨fun a ha ↦ H a (mem_atomsL.mpr ha), hn⟩

/-- A load that is not a store, through a pointer whose word the memory holds: its side
condition. -/
theorem side_load {d p : V} {off : ℕ} (hS : Atom.load d p off ∉ S) {v : E}
    (h : LoadHolds rd (σ p) off v) : Side rd S σ (.load d p off) := by
  simp only [Side, hS, ↓reduceIte]
  exact ⟨h.1, by rw [h.2]; rfl⟩

/-- `side_load` through a pointer whose words `W` the memory holds. -/
theorem side_loadVia {d p : V} {off : ℕ} (hS : Atom.load d p off ∉ S) {W : List E}
    (hW : ReadsAt rd (σ p) W) (hoff : off < W.length) : Side rd S σ (.load d p off) :=
  side_load hS (hW off hoff)

/-- A load that is not a store reads the memory's word. -/
theorem load_val {d p : V} {off : ℕ} (hg : Good rd S w σ (.load d p off))
    (hS : Atom.load d p off ∉ S) {v : E} (h : LoadHolds rd (σ p) off v) : σ d = v := by
  rcases hg with h' | h'
  · exact absurd h' hS
  · rw [h', rdAt_load h]

/-! ## Small facts -/

theorem good_mul {d x y : V} (h : x.idx < d.idx ∧ y.idx < d.idx) (hg : Good rd S w σ (.mul d x y)) :
    σ d = σ x * σ y := by
  simp only [Good, h.1, h.2, and_self, ↓reduceIte] at hg
  exact hg

theorem holds_mul {d x y : V} (h : x.idx < d.idx ∧ y.idx < d.idx) (hg : Good rd S w σ (.mul d x y)) :
    (Atom.mul d x y).Holds rd σ :=
  holds_of_good hg (by simp only [Side, h.1, h.2, and_self, ↓reduceIte])

theorem holds_store {d p : V} {off : ℕ} (hS : Atom.load d p off ∈ S)
    (hg : Good rd S w σ (.load d p off)) (h : LoadHolds rd (σ p) off (σ d)) :
    (Atom.load d p off).Holds rd σ :=
  holds_of_good hg (by simp only [Side, hS, ↓reduceIte]; exact h)

theorem holds_read {d p : V} {off : ℕ} (hS : Atom.load d p off ∉ S)
    (hg : Good rd S w σ (.load d p off)) {v : E} (h : LoadHolds rd (σ p) off v) :
    (Atom.load d p off).Holds rd σ :=
  holds_of_good hg (side_load hS h)

theorem idx_lt {a b : ℕ} (h : a < b) : (V.n a).idx < (V.n b).idx := h

theorem canon_zero : IsCanonical128 (0 : E) := by
  have cz : IsCanonical128 (word 0 0) := by
    rw [word_zero]; unfold IsCanonical128; exact limb_zero 2
  rwa [word_zero] at cz

end
end LeanVM.Guest.B1.VerifySub
