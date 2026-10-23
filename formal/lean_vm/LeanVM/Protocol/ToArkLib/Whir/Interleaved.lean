/-
  LeanVM.Protocol.ToArkLib.Whir.Interleaved

  Interleaved words and codewords of a linear code, agreement on a set of coordinates, and the
  list of interleaved codewords close to an interleaved word. Candidate for ArkLib.
-/

module

public import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Interleaved words and their lists

The objects of Annex B, `def:interleaved`, of the leanVM specification (leanVM `127510d1`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), for an arbitrary linear code
`C : Submodule F (ι → F)` over a field and a finite row index `ρ`.

* An *interleaved word* is a matrix `O : ρ → ι → F`, rows by columns; it is an *interleaved
  codeword* of `C` (`IsInterleavedCodeword`) when every row lies in `C`.
* `AgreeOn O U S`: every row of `O` equals the same row of `U` at every coordinate of `S`.
  `agreeSet O U` is the largest such set, the coordinates where all rows agree.
* `IsClose A O U`: `O` and `U` agree on some set of at least `A` coordinates
  (`isClose_iff_le_card_agreeSet`: the agreement set itself has at least `A` elements).
* `iList C A O`: the finite set of interleaved codewords close to `O` at threshold `A`. The
  Annex's list `Λ_γ(O)` at relative radius `γ` is `iListRad C γ O`, the threshold
  `⌈(1 - γ) n⌉₊` with `n = |ι|` (`mem_iListRad`: agreement on at least `(1 - γ) n` coordinates).

The list is counted by an integer threshold, the form in which ArkLib states its exceptional-set
bounds and in which the round-by-round analysis counts.

## Uniqueness for Reed-Solomon codes

`eq_of_mem_code_of_agreeOn`: two codewords of `ReedSolomon.code domain k` (polynomials of degree
below `k`) that agree on `k` coordinates are equal, since a nonzero polynomial of degree below
`k` has fewer than `k` roots and `domain` is injective. Its interleaved form is
`eq_of_isInterleavedCodeword_of_agreeOn`, and `card_agreeSet_lt` states it as the agreement bound
of distinct interleaved codewords that the Johnson bound consumes.
-/

namespace LeanVM.Protocol.Whir

open Finset

@[expose] public section

variable {F : Type*} {ι ρ : Type*}

/-! ## Agreement -/

/-- The interleaved words `O` and `U` agree on `S`: every row of `O` equals the same row of `U`
at every coordinate of `S`. -/
def AgreeOn (O U : ρ → ι → F) (S : Finset ι) : Prop :=
  ∀ r, ∀ x ∈ S, O r x = U r x

/-- The coordinates at which all rows of `O` and `U` agree. -/
def agreeSet [Fintype ι] [Fintype ρ] [DecidableEq F] (O U : ρ → ι → F) : Finset ι :=
  univ.filter fun x ↦ ∀ r, O r x = U r x

@[simp] theorem mem_agreeSet [Fintype ι] [Fintype ρ] [DecidableEq F] (O U : ρ → ι → F) (x : ι) :
    x ∈ agreeSet O U ↔ ∀ r, O r x = U r x := by
  simp [agreeSet]

/-- Agreement on `S` is containment of `S` in the agreement set. -/
theorem agreeOn_iff_subset_agreeSet [Fintype ι] [Fintype ρ] [DecidableEq F] (O U : ρ → ι → F)
    (S : Finset ι) : AgreeOn O U S ↔ S ⊆ agreeSet O U := by
  constructor
  · intro h x hx
    exact (mem_agreeSet O U x).mpr fun r ↦ h r x hx
  · intro h r x hx
    exact (mem_agreeSet O U x).mp (h hx) r

/-- Agreement is symmetric. -/
theorem AgreeOn.symm {O U : ρ → ι → F} {S : Finset ι} (h : AgreeOn O U S) : AgreeOn U O S :=
  fun r x hx ↦ (h r x hx).symm

/-- Agreement on `S` is agreement on every subset. -/
theorem AgreeOn.mono {O U : ρ → ι → F} {S T : Finset ι} (h : AgreeOn O U S) (hTS : T ⊆ S) :
    AgreeOn O U T :=
  fun r x hx ↦ h r x (hTS hx)

/-- Agreement is transitive on a common set. -/
theorem AgreeOn.trans {O U V : ρ → ι → F} {S : Finset ι} (h₁ : AgreeOn O U S)
    (h₂ : AgreeOn U V S) : AgreeOn O V S :=
  fun r x hx ↦ (h₁ r x hx).trans (h₂ r x hx)

/-! ## Interleaved codewords and lists -/

section Code

variable [Field F]

/-- `U` is an interleaved codeword of `C`: every row lies in `C`. -/
def IsInterleavedCodeword (C : Submodule F (ι → F)) (U : ρ → ι → F) : Prop :=
  ∀ r, U r ∈ C

end Code

/-- `U` is close to `O` at threshold `A`: they agree on some set of at least `A` coordinates. -/
def IsClose (A : ℕ) (O U : ρ → ι → F) : Prop :=
  ∃ S : Finset ι, A ≤ S.card ∧ AgreeOn O U S

/-- Closeness is witnessed by the full agreement set. -/
theorem isClose_iff_le_card_agreeSet [Fintype ι] [Fintype ρ] [DecidableEq F] (A : ℕ)
    (O U : ρ → ι → F) : IsClose A O U ↔ A ≤ (agreeSet O U).card := by
  constructor
  · rintro ⟨S, hS, hagree⟩
    exact hS.trans (card_le_card ((agreeOn_iff_subset_agreeSet O U S).mp hagree))
  · intro h
    exact ⟨agreeSet O U, h, (agreeOn_iff_subset_agreeSet O U _).mpr subset_rfl⟩

/-- A larger threshold is a stronger closeness. -/
theorem IsClose.mono {A A' : ℕ} {O U : ρ → ι → F} (h : IsClose A O U) (hA : A' ≤ A) :
    IsClose A' O U :=
  let ⟨S, hS, hagree⟩ := h
  ⟨S, hA.trans hS, hagree⟩

section List

variable [Field F] [Fintype F] [Fintype ι] [Fintype ρ]

open Classical in
/-- **The list** `Λ(O)` at agreement threshold `A`: the interleaved codewords of `C` that agree
with `O` on a common set of at least `A` coordinates. -/
noncomputable def iList (C : Submodule F (ι → F)) (A : ℕ) (O : ρ → ι → F) :
    Finset (ρ → ι → F) :=
  univ.filter fun U ↦ IsInterleavedCodeword C U ∧ IsClose A O U

@[simp] theorem mem_iList (C : Submodule F (ι → F)) (A : ℕ) (O U : ρ → ι → F) :
    U ∈ iList C A O ↔ IsInterleavedCodeword C U ∧ IsClose A O U := by
  classical
  simp [iList]

/-- A lower threshold gives a larger list. -/
theorem iList_anti (C : Submodule F (ι → F)) {A A' : ℕ} (hA : A' ≤ A) (O : ρ → ι → F) :
    iList C A O ⊆ iList C A' O := by
  intro U hU
  rw [mem_iList] at hU ⊢
  exact ⟨hU.1, hU.2.mono hA⟩

/-- The agreement threshold of the relative radius `γ` on `n` coordinates: `⌈(1 - γ) n⌉₊`. -/
noncomputable def radiusThreshold (n : ℕ) (γ : ℝ) : ℕ :=
  ⌈(1 - γ) * n⌉₊

/-- A set reaches the threshold of `γ` exactly when it has at least `(1 - γ) n` elements. -/
theorem radiusThreshold_le_iff (n : ℕ) (γ : ℝ) (m : ℕ) :
    radiusThreshold n γ ≤ m ↔ (1 - γ) * n ≤ m :=
  Nat.ceil_le

/-- **The list `Λ_γ(O)` at relative radius `γ`** (Annex B, `def:interleaved`): the interleaved
codewords `γ`-close to `O`, agreeing with it on at least `(1 - γ) |ι|` coordinates. -/
noncomputable def iListRad (C : Submodule F (ι → F)) (γ : ℝ) (O : ρ → ι → F) :
    Finset (ρ → ι → F) :=
  iList C (radiusThreshold (Fintype.card ι) γ) O

theorem mem_iListRad (C : Submodule F (ι → F)) (γ : ℝ) (O U : ρ → ι → F) :
    U ∈ iListRad C γ O ↔ IsInterleavedCodeword C U ∧
      ∃ S : Finset ι, (1 - γ) * Fintype.card ι ≤ S.card ∧ AgreeOn O U S := by
  simp only [iListRad, mem_iList, IsClose, radiusThreshold_le_iff]

end List

/-! ## Uniqueness for Reed-Solomon codes -/

section Uniqueness

variable [Field F]

/-- **Uniqueness.** Two codewords of the Reed-Solomon code of polynomials of degree below `k`
that agree on a set of `k` coordinates are equal. -/
theorem eq_of_mem_code_of_agreeOn (domain : ι ↪ F) {k : ℕ} {u v : ι → F}
    (hu : u ∈ ReedSolomon.code domain k) (hv : v ∈ ReedSolomon.code domain k) (S : Finset ι)
    (hS : k ≤ S.card) (h : ∀ x ∈ S, u x = v x) : u = v := by
  obtain ⟨P, hP, hPu⟩ := ReedSolomon.mem_code_iff_eval.mp hu
  obtain ⟨Q, hQ, hQv⟩ := ReedSolomon.mem_code_iff_eval.mp hv
  have hk : ((k : ℕ) : WithBot ℕ) ≤ (S.card : WithBot ℕ) := by exact_mod_cast hS
  have hPQ : P = Q :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq S (domain.injective.injOn)
      (hP.trans_le hk) (hQ.trans_le hk) fun x hx ↦ by rw [hPu, hQv, h x hx]
  funext x
  rw [← hPu, ← hQv, hPQ]

/-- **Interleaved uniqueness.** Two interleaved codewords of the Reed-Solomon code of degree
below `k` that agree on a common set of `k` coordinates are equal. -/
theorem eq_of_isInterleavedCodeword_of_agreeOn (domain : ι ↪ F) {k : ℕ} {U V : ρ → ι → F}
    (hU : IsInterleavedCodeword (ReedSolomon.code domain k) U)
    (hV : IsInterleavedCodeword (ReedSolomon.code domain k) V) (S : Finset ι)
    (hS : k ≤ S.card) (h : AgreeOn U V S) : U = V :=
  funext fun r ↦ eq_of_mem_code_of_agreeOn domain (hU r) (hV r) S hS (h r)

/-- **Distinct interleaved codewords agree on fewer than `k` coordinates** of the Reed-Solomon
code of degree below `k`: the agreement bound the Johnson bound consumes. -/
theorem card_agreeSet_lt [Fintype ι] [Fintype ρ] [DecidableEq F] (domain : ι ↪ F) {k : ℕ}
    {U V : ρ → ι → F} (hU : IsInterleavedCodeword (ReedSolomon.code domain k) U)
    (hV : IsInterleavedCodeword (ReedSolomon.code domain k) V) (hne : U ≠ V) :
    (agreeSet U V).card < k := by
  by_contra hk
  exact hne (eq_of_isInterleavedCodeword_of_agreeOn domain hU hV _ (not_lt.mp hk)
    ((agreeOn_iff_subset_agreeSet U V _).mpr subset_rfl))

end Uniqueness

end
end LeanVM.Protocol.Whir
