/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDefs

  Polynomial tuples against interleaved words, the affine combiner `f + (α + β x) g`, witnesses
  with agreement loss one, exceptional coefficient pairs, and the lists of close tuples.
  Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerJohnson
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Affine combiners: definitions

The objects of [CWYZ26], Section 1.1 and Definition 3.1, for interleaved words, as Annex B
of the leanVM specification (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`)
uses them in `thm:mca-affine` and `lem:fold-list`. Fix a field `F`, a domain `dom : ι ↪ F` of
`n = |ι|` points and a finite lane index `ρ`.

* A *tuple* is `P : ρ → F[X]`, of degree at most `d` (`DegLE d P`) when every lane is.
* `agree dom P w`: the coordinates where every lane of `P` agrees with the word `w : ρ → ι → F`.
* `comb dom f g α β`: the affine combination `f + (α + β x) g`, lane by lane.
* `IsWitness dom f g d α β P U V`: `deg U ≤ d`, `deg V ≤ d - 1`, `P = U + (α + β X) V`, and
  `U = f`, `V = g` on all but at most one coordinate of `agree P (comb f g α β)` (agreement loss
  one).
* `IsExceptional dom f g d A α β`: some tuple of degree at most `d` agrees with the combination on
  at least `A` coordinates and has no witness. `excSet` is the set of these pairs, and
  `[CWYZ26, Thm. 4.10]` bounds its size (`thm:mca-affine` in counting form).
* `pairList dom f g A d`: the pairs of tuples of degree at most `d` agreeing with `(f, g)` on a
  common set of at least `A` coordinates (the Annex's `lst(orc; A, d)` for the interleaved word
  with halves `f` and `g`), and `tupleList dom w A d` the tuples close to one word.

`card_pairList_le_jl` is the Johnson bound for `pairList`: two distinct pairs of degree at most
`d` agree on at most `d` coordinates.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {F : Type*} [Field F] {ι ρ : Type*}

/-- Every lane of `P` has degree at most `d`. -/
def DegLE (d : ℕ) (P : ρ → F[X]) : Prop := ∀ r, (P r).natDegree ≤ d

/-- The affine combiner `α + β X`. -/
noncomputable def lin (α β : F) : F[X] := C α + C β * X

@[simp] theorem eval_lin (α β x : F) : (lin α β).eval x = α + β * x := by simp [lin]

/-- The affine combination `f + (α + β x) g` of two words, lane by lane. -/
def comb (dom : ι ↪ F) (f g : ρ → ι → F) (α β : F) : ρ → ι → F :=
  fun r x ↦ f r x + (α + β * dom x) * g r x

variable [Fintype ι] [DecidableEq ι] [Fintype ρ]

open Classical in
/-- The coordinates where every lane of `P` agrees with the word `w`. -/
noncomputable def agree (dom : ι ↪ F) (P : ρ → F[X]) (w : ρ → ι → F) : Finset ι :=
  univ.filter fun x ↦ ∀ r, (P r).eval (dom x) = w r x

omit [DecidableEq ι] in
@[simp] theorem mem_agree (dom : ι ↪ F) (P : ρ → F[X]) (w : ρ → ι → F) (x : ι) :
    x ∈ agree dom P w ↔ ∀ r, (P r).eval (dom x) = w r x := by
  classical
  simp [agree]

open Classical in
/-- **A witness with agreement loss one** ([CWYZ26, Section 1.1]): `deg U ≤ d`, `deg V ≤ d - 1`,
`P = U + (α + β X) V`, and at most one coordinate where `P` agrees with `f + (α + β x) g` has
`U ≠ f` or `V ≠ g` in some lane. -/
def IsWitness (dom : ι ↪ F) (f g : ρ → ι → F) (d : ℕ) (α β : F) (P U V : ρ → F[X]) : Prop :=
  DegLE d U ∧ DegLE (d - 1) V ∧ (∀ r, P r = U r + lin α β * V r) ∧
    ((agree dom P (comb dom f g α β)).filter fun x ↦
      ∃ r, (U r).eval (dom x) ≠ f r x ∨ (V r).eval (dom x) ≠ g r x).card ≤ 1

/-- **An exceptional pair** ([CWYZ26, Definition 3.1]): some tuple of degree at most `d` agrees
with `f + (α + β x) g` on at least `A` coordinates and has no witness with agreement loss one. -/
def IsExceptional (dom : ι ↪ F) (f g : ρ → ι → F) (d A : ℕ) (α β : F) : Prop :=
  ∃ P : ρ → F[X], DegLE d P ∧ A ≤ (agree dom P (comb dom f g α β)).card ∧
    ¬ ∃ U V, IsWitness dom f g d α β P U V

open Classical in
/-- The exceptional pairs. `[CWYZ26, Thm. 4.10]` bounds their number; divided by `|F|²` it is the
affine MCA error `ε_aff` of Annex B, `def:epsaff`. -/
noncomputable def excSet [Fintype F] (dom : ι ↪ F) (f g : ρ → ι → F) (d A : ℕ) :
    Finset (F × F) :=
  univ.filter fun p ↦ IsExceptional dom f g d A p.1 p.2

omit [DecidableEq ι] in
@[simp] theorem mem_excSet [Fintype F] (dom : ι ↪ F) (f g : ρ → ι → F) (d A : ℕ) (p : F × F) :
    p ∈ excSet dom f g d A ↔ IsExceptional dom f g d A p.1 p.2 := by
  classical
  simp [excSet]

/-! ## Root counting -/

omit [Fintype ι] [DecidableEq ι] [Fintype ρ] in
/-- A nonzero polynomial vanishes at no more domain points than its degree. -/
theorem card_filter_eval_eq_zero_le (dom : ι ↪ F) {D : F[X]} (hD : D ≠ 0) (S : Finset ι)
    (hS : ∀ x ∈ S, D.eval (dom x) = 0) : S.card ≤ D.natDegree := by
  classical
  calc S.card ≤ D.roots.toFinset.card :=
        Finset.card_le_card_of_injOn dom (fun x hx ↦ by
          rw [Finset.mem_coe, Multiset.mem_toFinset]
          exact (mem_roots hD).mpr (hS x hx)) (dom.injective.injOn)
    _ ≤ D.roots.card := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := card_roots' D

/-- Two tuples of degree at most `d` that differ agree on at most `d` coordinates. -/
theorem card_inter_agree_le (dom : ι ↪ F) {d : ℕ} {P P' : ρ → F[X]} (hP : DegLE d P)
    (hP' : DegLE d P') (hne : P ≠ P') (w : ρ → ι → F) (S : Finset ι)
    (hS : S ⊆ agree dom P w ∩ agree dom P' w) : S.card ≤ d := by
  obtain ⟨r, hr⟩ : ∃ r, P r ≠ P' r := by
    by_contra h
    exact hne (funext fun r ↦ not_not.mp ((not_exists.mp h) r))
  refine (card_filter_eval_eq_zero_le dom (sub_ne_zero.mpr hr) S fun x hx ↦ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hP r) (hP' r)))
  have h := Finset.mem_inter.mp (hS hx)
  rw [eval_sub, (mem_agree dom P w x).mp h.1 r, (mem_agree dom P' w x).mp h.2 r, sub_self]

/-! ## Finiteness of bounded-degree tuples -/

omit [Fintype ι] [DecidableEq ι] [Fintype ρ] in
/-- Over a finite field, there are finitely many polynomials of degree at most `d`. -/
theorem finite_natDegree_le [Finite F] (d : ℕ) : {P : F[X] | P.natDegree ≤ d}.Finite := by
  refine Set.Finite.of_finite_image (f := fun P : F[X] ↦ fun i : Fin (d + 1) ↦ P.coeff i)
    (Set.toFinite _) fun P hP Q hQ h ↦ Polynomial.ext fun i ↦ ?_
  by_cases hi : i ≤ d
  · exact congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt ((show P.natDegree ≤ d from hP).trans_lt (not_le.mp hi)),
      coeff_eq_zero_of_natDegree_lt ((show Q.natDegree ≤ d from hQ).trans_lt (not_le.mp hi))]

omit [Fintype ι] [DecidableEq ι] in
/-- Over a finite field, there are finitely many tuples of degree at most `d`. -/
theorem finite_degLE [Finite F] (d : ℕ) : {P : ρ → F[X] | DegLE d P}.Finite := by
  have : {P : ρ → F[X] | DegLE d P} = Set.pi Set.univ fun _ ↦ {P : F[X] | P.natDegree ≤ d} := by
    ext P; simp [DegLE]
  rw [this]
  exact Set.Finite.pi fun _ ↦ finite_natDegree_le d

/-! ## Lists -/

section Lists

variable [Finite F] (dom : ι ↪ F)

/-- The pairs of tuples of degree at most `d` agreeing with `(f, g)` on a common set of at least
`A` coordinates. -/
noncomputable def pairList (f g : ρ → ι → F) (A d : ℕ) : Finset ((ρ → F[X]) × (ρ → F[X])) :=
  Set.Finite.toFinset
    (s := {p : (ρ → F[X]) × (ρ → F[X]) |
      DegLE d p.1 ∧ DegLE d p.2 ∧ A ≤ (agree dom p.1 f ∩ agree dom p.2 g).card})
    (((finite_degLE d).prod (finite_degLE d)).subset
      fun p (hp : DegLE d p.1 ∧ DegLE d p.2 ∧ _) ↦ ⟨hp.1, hp.2.1⟩)

@[simp] theorem mem_pairList (f g : ρ → ι → F) (A d : ℕ) (p : (ρ → F[X]) × (ρ → F[X])) :
    p ∈ pairList dom f g A d ↔
      DegLE d p.1 ∧ DegLE d p.2 ∧ A ≤ (agree dom p.1 f ∩ agree dom p.2 g).card := by
  simp [pairList]

/-- The tuples of degree at most `d` agreeing with `w` on at least `A` coordinates. -/
noncomputable def tupleList (w : ρ → ι → F) (A d : ℕ) : Finset (ρ → F[X]) :=
  Set.Finite.toFinset (s := {P : ρ → F[X] | DegLE d P ∧ A ≤ (agree dom P w).card})
    ((finite_degLE d).subset fun P (hP : DegLE d P ∧ _) ↦ hP.1)

omit [DecidableEq ι] in
@[simp] theorem mem_tupleList (w : ρ → ι → F) (A d : ℕ) (P : ρ → F[X]) :
    P ∈ tupleList dom w A d ↔ DegLE d P ∧ A ≤ (agree dom P w).card := by
  simp [tupleList]

/-- **Johnson bound for pairs of tuples** (Annex B, `thm:johnson-interleaved`): with `A² > n d`,
at most `jl n A d` pairs of tuples of degree at most `d` agree with `(f, g)` on a common set of
`A` coordinates. -/
theorem card_pairList_le_jl (f g : ρ → ι → F) (A d : ℕ) (hgap : Fintype.card ι * d < A * A) :
    (pairList dom f g A d).card ≤ jl (Fintype.card ι) A d := by
  have key : ∀ p ∈ pairList dom f g A d, ∀ p' ∈ pairList dom f g A d, p ≠ p' →
      ((agree dom p.1 f ∩ agree dom p.2 g) ∩ (agree dom p'.1 f ∩ agree dom p'.2 g)).card ≤ d := by
    intro p hp p' hp' hne
    rw [mem_pairList] at hp hp'
    by_cases h1 : p.1 = p'.1
    · have h2 : p.2 ≠ p'.2 := fun h2 ↦ hne (Prod.ext h1 h2)
      exact card_inter_agree_le dom hp.2.1 hp'.2.1 h2 g _ fun x hx ↦ by
        simp only [Finset.mem_inter] at hx ⊢
        exact ⟨hx.1.2, hx.2.2⟩
    · exact card_inter_agree_le dom hp.1 hp'.1 h1 f _ fun x hx ↦ by
        simp only [Finset.mem_inter] at hx ⊢
        exact ⟨hx.1.1, hx.2.1⟩
  classical
  exact card_le_jl (pairList dom f g A d) (fun p ↦ agree dom p.1 f ∩ agree dom p.2 g) A d
    (fun p hp ↦ ((mem_pairList dom f g A d p).mp hp).2.2) key hgap

end Lists

end
end LeanVM.Protocol.Whir.AffineCombiner
