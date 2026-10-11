module

public import Whir.Soundness
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.OfFn

/-!
Same-set mutual correlated agreement and row-interleaving transfer.
The finite-subspace counting argument and projection proof adapt ArkLib commit
35ddcaa83f683011f944f58904be779495a5709a, files
ToMathlib/LinearAlgebra/Submodule/Union.lean and
Data/CodingTheory/InterleavedCode/{Projection,ExactAgreement}.lean
(Apache-2.0, copyright 2026 ArkLib Contributors, author Quang Dao).
No Reed-Solomon Johnson exceptional-set estimate is assumed or proved here.
-/
@[expose] public section

namespace Whir.MutualAgreement

open scoped BigOperators
open Polynomial

/-- The sharp finite-field avoidance bound includes equality with the field size. -/
theorem exists_avoiding_submodules {I F V : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (s : Finset I) (p : I → Submodule F V)
    (hp : ∀ i ∈ s, p i ≠ ⊤) (hs : s.card ≤ Fintype.card F) :
    ∃ v : V, ∀ i ∈ s, v ∉ p i := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, fun i hi => (hp i hi (Subsingleton.elim _ _)).elim⟩
  let b := Module.finBasis F V
  let _ : Finite V :=
    Finite.of_equiv (Fin (Module.finrank F V) → F) b.equivFun.toEquiv.symm
  let _ := Fintype.ofFinite V
  let q := Fintype.card F
  let d := Module.finrank F V
  let nonzero (i : I) := Finset.univ.filter fun x : V => x ∈ p i ∧ x ≠ 0
  let covered := insert (0 : V) (s.biUnion nonzero)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 0 < d := Module.finrank_pos
  have hnonzero (i : I) (hi : i ∈ s) :
      (nonzero i).card ≤ q ^ (d - 1) - 1 := by
    let all := Finset.univ.filter fun x : V => x ∈ p i
    have hzero : (0 : V) ∈ all := by simp [all]
    have heq : nonzero i = all.erase 0 := by
      ext x
      simp [nonzero, all, and_comm]
    rw [heq, Finset.card_erase_of_mem hzero]
    have hcard : all.card = Fintype.card (p i) := by
      symm
      exact Fintype.card_ofFinset all (by simp [all])
    have hpow : Fintype.card (p i) = q ^ Module.finrank F (p i) := by
      simpa [q] using (Module.card_eq_pow_finrank (K := F) (V := p i))
    rw [hcard, hpow]
    exact Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq)
        (Nat.le_sub_one_of_lt (Submodule.finrank_lt (hp i hi)))) 1
  have hcovered : covered.card < Fintype.card V := by
    have hbiUnion : (s.biUnion nonzero).card ≤ s.card * (q ^ (d - 1) - 1) := by
      calc
        _ ≤ ∑ i ∈ s, (nonzero i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ s, (q ^ (d - 1) - 1) :=
          Finset.sum_le_sum fun i hi => hnonzero i hi
        _ = _ := by simp
    have hmul : s.card * (q ^ (d - 1) - 1) ≤ q * (q ^ (d - 1) - 1) :=
      Nat.mul_le_mul_right _ hs
    have hpow : q ^ d = q * q ^ (d - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hd]
      simp [pow_succ, Nat.mul_comm]
    have hcard : Fintype.card V = q ^ d := by
      simpa [q, d] using (Module.card_eq_pow_finrank (K := F) (V := V))
    rw [hcard, hpow]
    calc
      covered.card ≤ (s.biUnion nonzero).card + 1 := Finset.card_insert_le _ _
      _ ≤ s.card * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hbiUnion 1
      _ ≤ q * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hmul 1
      _ < q * q ^ (d - 1) := by
        have hpos : 0 < q ^ (d - 1) := pow_pos (Nat.zero_lt_of_lt hq) _
        have hqmul : q ≤ q * q ^ (d - 1) := by
          simpa using Nat.mul_le_mul_left q hpos
        rw [Nat.mul_sub_left_distrib]
        simp only [mul_one]
        omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := covered) (t := Finset.univ) (by simpa using hcovered)
  refine ⟨x, fun i hi hxi => hx ?_⟩
  by_cases hx0 : x = 0
  · simp [covered, hx0]
  · exact Finset.mem_insert.mpr (Or.inr
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp [nonzero, hxi, hx0]⟩))

variable {F I J R S : Type*} [Field F]

/-- Restricting actual codewords to a fixed agreement set gives a linear code. -/
def projectedCode (C : Submodule F (I → F)) (T : Finset I) : Submodule F (T → F) :=
  C.map ({ toFun := fun w i => w i
           map_add' := by intros; rfl
           map_smul' := by intros; rfl } : (I → F) →ₗ[F] (T → F))

/-- Membership means extension to a codeword on this very set, not another set. -/
theorem mem_projectedCode (C : Submodule F (I → F)) (T : Finset I) (w : I → F) :
    (fun i : T => w i) ∈ projectedCode C T ↔
      ∃ c ∈ C, ∀ i ∈ T, c i = w i := by
  change (∃ c, c ∈ C ∧ (fun i : T => c i) = fun i : T => w i) ↔ _
  constructor
  · rintro ⟨c, hc, heq⟩
    exact ⟨c, hc, fun i hi => congrFun heq ⟨i, hi⟩⟩
  · rintro ⟨c, hc, heq⟩
    exact ⟨c, hc, funext fun i => heq i i.2⟩

/-- Same-set MCA for an arbitrary coefficient generator and integer threshold. -/
def Bad [Fintype J] (G : S → J → F) (C : Submodule F (I → F))
    (a : ℕ) (U : J → I → F) (x : S) : Prop :=
  ∃ T : Finset I, a ≤ T.card ∧
    (fun i : T => ∑ j, G x j * U j i) ∈ projectedCode C T ∧
    ∃ j, (fun i : T => U j i) ∉ projectedCode C T

/-- All rows use one agreement set; a different set for each row is not MCA. -/
def RowBad [Fintype J] (G : S → J → F) (C : Submodule F (I → F))
    (a : ℕ) (U : J → R → I → F) (x : S) : Prop :=
  ∃ T : Finset I, a ≤ T.card ∧
    (∀ r, (fun i : T => ∑ j, G x j * U j r i) ∈ projectedCode C T) ∧
    ∃ j r, (fun i : T => U j r i) ∉ projectedCode C T

/-- Row combinations are linear in their coefficient functional. -/
noncomputable def rowMap [Fintype R] (U : R → I → F) (T : Finset I) :
    (R → F) →ₗ[F] (T → F) :=
  Fintype.linearCombination F (fun r i => U r i)

/-- Functionals which hide all input failures on the selected agreement set. -/
noncomputable def goodFunctionals [Fintype R] (C : Submodule F (I → F))
    (U : J → R → I → F) (T : Finset I) : Submodule F (R → F) :=
  ⨅ j, (projectedCode C T).comap (rowMap (U j) T)

theorem mem_goodFunctionals [Fintype R] (C : Submodule F (I → F))
    (U : J → R → I → F) (T : Finset I) (l : R → F) :
    l ∈ goodFunctionals C U T ↔
      ∀ j, (fun i : T => ∑ r, l r * U j r i) ∈ projectedCode C T := by
  simp only [goodFunctionals, Submodule.mem_iInf, Submodule.mem_comap,
    rowMap, Fintype.linearCombination_apply]
  have heq (j : J) : (∑ r, l r • fun i : T => U j r i) =
      (fun i : T => ∑ r, l r * U j r i) := by
    funext i
    simp
  simp only [heq]

/-- A failed row makes the submodule of hiding functionals proper. -/
theorem goodFunctionals_ne_top [Fintype R] (C : Submodule F (I → F))
    (U : J → R → I → F) (T : Finset I)
    (h : ∃ j r, (fun i : T => U j r i) ∉ projectedCode C T) :
    goodFunctionals C U T ≠ ⊤ := by
  classical
  rintro htop
  obtain ⟨j, r, hr⟩ := h
  have hmem : Pi.single r (1 : F) ∈ goodFunctionals C U T := htop ▸ Submodule.mem_top
  simp only [goodFunctionals, Submodule.mem_iInf, Submodule.mem_comap, rowMap,
    Fintype.linearCombination_apply_single, one_smul] at hmem
  exact hr (hmem j)

/-- A single row functional preserves every bad seed, with no row-count loss. -/
theorem row_bad_transfer [Fintype F] [Fintype J] [Fintype R]
    (G : S → J → F) (C : Submodule F (I → F)) (a : ℕ)
    (U : J → R → I → F) (s : Finset S) (hs : s.card ≤ Fintype.card F)
    (hbad : ∀ x ∈ s, RowBad G C a U x) :
    ∃ V : J → I → F, ∀ x ∈ s, Bad G C a V x := by
  classical
  choose! T hT using hbad
  obtain ⟨l, hl⟩ := exists_avoiding_submodules s (fun x => goodFunctionals C U (T x))
    (fun x hx => goodFunctionals_ne_top C U (T x) (hT x hx).2.2) hs
  refine ⟨fun j i => ∑ r, l r * U j r i, fun x hx => ⟨T x, (hT x hx).1, ?_, ?_⟩⟩
  · have hm := (projectedCode C (T x)).sum_mem
      (fun r (_ : r ∈ Finset.univ) =>
        (projectedCode C (T x)).smul_mem (l r) ((hT x hx).2.1 r))
    convert hm using 1
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro r _
    ring
  · exact not_forall.mp fun hall => hl x hx ((mem_goodFunctionals C U (T x) l).mpr hall)

open Classical in
/-- A proved scalar bound transfers to arbitrarily many rows without a union bound. -/
theorem row_bad_probability_le [Fintype F] [Fintype J] [Fintype R] [Fintype S]
    (G : S → J → F) (C : Submodule F (I → F)) (a : ℕ) (error : ℚ)
    (hS : Fintype.card S ≤ Fintype.card F)
    (hscalar : ∀ V : J → I → F,
      Soundness.uniformProb (Finset.univ.filter (Bad G C a V)) ≤ error)
    (U : J → R → I → F) :
    Soundness.uniformProb (Finset.univ.filter (RowBad G C a U)) ≤ error := by
  classical
  let s := Finset.univ.filter (RowBad G C a U)
  obtain ⟨V, hV⟩ := row_bad_transfer G C a U s ((Finset.card_le_univ s).trans hS)
    (fun x hx => (Finset.mem_filter.mp hx).2)
  apply le_trans _ (hscalar V)
  unfold Soundness.uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show s ⊆ Finset.univ.filter (Bad G C a V) from
    fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV x hx⟩)

/-- The actual binary fold coefficients, without a characteristic assumption. -/
def foldGenerator (z : F) : Fin 2 → F := ![1 - z, z]

/-- The integer event is exactly the real-radius event, including the same set. -/
theorem bad_iff_radius [Fintype I] [Fintype J] (G : S → J → F)
    (C : Submodule F (I → F)) (radius : ℝ) (U : J → I → F) (x : S) :
    Bad G C ⌈(Fintype.card I : ℝ) * (1 - radius)⌉₊ U x ↔
      ∃ T : Finset I, (Fintype.card I : ℝ) * (1 - radius) ≤ T.card ∧
        (∃ c ∈ C, ∀ i ∈ T, c i = ∑ j, G x j * U j i) ∧
        ∃ j, ¬ ∃ c ∈ C, ∀ i ∈ T, c i = U j i := by
  unfold Bad
  apply exists_congr
  intro T
  rw [Nat.ceil_le, mem_projectedCode C T (fun i => ∑ j, G x j * U j i)]
  simp only [mem_projectedCode]

/-- Outside the same-set row MCA event, every folded candidate lifts on its
original agreement set. Linearity suffices; no distance or uniqueness premise
is required, because the lifted codewords can be corrected outside the set. -/
theorem fold_candidate_lifts (C : Submodule F (I → F)) (a : ℕ)
    (U₀ U₁ V : R → I → F) (z : F)
    (hV : ∀ r, V r ∈ C) (T : Finset I) (hT : a ≤ T.card)
    (hagree : ∀ r i, i ∈ T → V r i = (1 - z) * U₀ r i + z * U₁ r i)
    (hgood : ¬ RowBad foldGenerator C a ![U₀, U₁] z) :
    ∃ P₀ P₁ : R → I → F,
      (∀ r, P₀ r ∈ C ∧ P₁ r ∈ C) ∧
      (∀ r i, i ∈ T → P₀ r i = U₀ r i ∧ P₁ r i = U₁ r i) ∧
      ∀ r i, V r i = (1 - z) * P₀ r i + z * P₁ r i := by
  classical
  have hcomb : ∀ r, (fun i : T =>
      ∑ j, foldGenerator z j * (![U₀, U₁] j) r i) ∈ projectedCode C T := by
    intro r
    apply (mem_projectedCode C T (fun i => ∑ j, foldGenerator z j * (![U₀, U₁] j) r i)).mpr
    refine ⟨V r, hV r, ?_⟩
    intro i hi
    simpa [foldGenerator, Fin.sum_univ_two] using hagree r i hi
  have hrows : ∀ j : Fin 2, ∀ r,
      (fun i : T => (![U₀, U₁] j) r i) ∈ projectedCode C T := by
    by_contra! hn
    exact hgood ⟨T, hT, hcomb, hn⟩
  have h₀ : ∀ r, ∃ p ∈ C, ∀ i ∈ T, p i = U₀ r i :=
    fun r => (mem_projectedCode C T _).mp (hrows 0 r)
  have h₁ : ∀ r, ∃ p ∈ C, ∀ i ∈ T, p i = U₁ r i :=
    fun r => (mem_projectedCode C T _).mp (hrows 1 r)
  choose p₀ hp₀ heq₀ using h₀
  choose p₁ hp₁ heq₁ using h₁
  let b : R → I → F := fun r => p₁ r - p₀ r
  let P₀ : R → I → F := fun r => V r - z • b r
  let P₁ : R → I → F := fun r => P₀ r + b r
  have hb : ∀ r, b r ∈ C := fun r => C.sub_mem (hp₁ r) (hp₀ r)
  have hP₀ : ∀ r, P₀ r ∈ C := fun r => C.sub_mem (hV r) (C.smul_mem z (hb r))
  refine ⟨P₀, P₁, fun r => ⟨hP₀ r, C.add_mem (hP₀ r) (hb r)⟩, ?_, ?_⟩
  · intro r i hi
    dsimp [P₀, P₁, b]
    rw [hagree r i hi, heq₀ r i hi, heq₁ r i hi]
    constructor <;> ring
  · intro r i
    dsimp [P₀, P₁, b]
    ring

/-- Reed-Solomon words are evaluations of polynomials of degree below dimension.
Injectivity of the domain is needed for distance estimates, not for linearity. -/
noncomputable def rsCode (domain : I → F) (dimension : ℕ) : Submodule F (I → F) :=
  (Polynomial.degreeLT F dimension).map
    ({ toFun := fun p i => p.eval (domain i)
       map_add' := by intros; ext; simp
       map_smul' := by intros; ext; simp } : F[X] →ₗ[F] (I → F))

theorem mem_rsCode (domain : I → F) (dimension : ℕ) (w : I → F) :
    w ∈ rsCode domain dimension ↔
      ∃ p : F[X], p.degree < dimension ∧ ∀ i, p.eval (domain i) = w i := by
  change (∃ p, p ∈ Polynomial.degreeLT F dimension ∧
    (fun i => p.eval (domain i)) = w) ↔ _
  simp only [Polynomial.mem_degreeLT, funext_iff]

open Classical in
/-- This is the same coefficient-table encoding used by CodingBounds, not
a separate polynomial-code model. It includes zero-dimensional tables. -/
theorem mem_rsCode_iff_coefficients (domain : I → F) (dimension : ℕ) (w : I → F) :
    w ∈ rsCode domain dimension ↔
      ∃ v : Fin dimension → F, ∀ i, (Polynomial.ofFn dimension v).eval (domain i) = w i := by
  rw [mem_rsCode]
  constructor
  · rintro ⟨p, hp, hword⟩
    let v : Fin dimension → F := fun j => p.coeff j
    have heq : Polynomial.ofFn dimension v = p := by
      ext j
      by_cases hj : j < dimension
      · simp [Polynomial.ofFn_coeff_eq_val_of_lt v hj, v]
      · have hge : dimension ≤ j := Nat.le_of_not_gt hj
        rw [Polynomial.ofFn_coeff_eq_zero_of_ge v hge]
        exact (Polynomial.coeff_eq_zero_of_degree_lt
          (hp.trans_le (by exact_mod_cast hge))).symm
    exact ⟨v, fun i => by rw [heq]; exact hword i⟩
  · rintro ⟨v, hword⟩
    exact ⟨Polynomial.ofFn dimension v, Polynomial.ofFn_degree_lt v, hword⟩

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- An explicit positive-degree RS example separating ordinary correlated
agreement from same-set MCA. Over F₅ on {0,1,2}, both rows (0,0,1) and
(0,0,-1) agree with the zero linear polynomial on {0,1}. At fold challenge
3 their fold is zero everywhere, but neither row is a linear codeword on
the full set. Thus ordinary correlated agreement cannot replace the MCA
event, even when an ordinary common agreement set already exists. -/
theorem ordinary_agreement_does_not_rule_out_mca :
    let C := rsCode (fun i : Fin 3 => (i.val : ZMod 5)) 2
    let u : Fin 3 → ZMod 5 := ![0, 0, 1]
    (∃ T : Finset (Fin 3), 2 ≤ T.card ∧
      (fun i : T => u i) ∈ projectedCode C T ∧
      (fun i : T => -u i) ∈ projectedCode C T) ∧
    Bad foldGenerator C 2 ![u, -u] 3 := by
  classical
  dsimp only
  let C := rsCode (fun i : Fin 3 => (i.val : ZMod 5)) 2
  let u : Fin 3 → ZMod 5 := ![0, 0, 1]
  have hnot : u ∉ C := by
    intro hu
    obtain ⟨p, hp, heval⟩ := (mem_rsCode _ _ _).mp hu
    have hp0 : p.eval 0 = 0 := by simpa [u] using heval 0
    have hp1 : p.eval 1 = 0 := by simpa [u] using heval 1
    have hp2 : p.eval 2 = 1 := by simpa [u] using heval 2
    have hpne : p ≠ 0 := by intro hz; simp [hz] at hp2
    have hdegree : p.natDegree ≤ 1 := by
      have hlt : p.natDegree < 2 := (Polynomial.natDegree_lt_iff_degree_lt hpne).mpr hp
      omega
    have hcount := Soundness.evaluation_agreement ({0, 1} : Finset (ZMod 5))
      p 0 hpne 1 hdegree (by simp)
    norm_num [Finset.filter_insert, Finset.filter_singleton, hp0, hp1] at hcount
  constructor
  · refine ⟨{0, 1}, by decide, ?_, ?_⟩
    · apply (mem_projectedCode C _ u).mpr
      refine ⟨0, C.zero_mem, ?_⟩
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> rfl
    · apply (mem_projectedCode C _ (-u)).mpr
      refine ⟨0, C.zero_mem, ?_⟩
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp [u]
  · refine ⟨Finset.univ, by decide, ?_, 0, ?_⟩
    · have hz : (fun i : (Finset.univ : Finset (Fin 3)) =>
          ∑ j, foldGenerator (3 : ZMod 5) j * (![u, -u] j) i) = 0 := by
        funext i
        fin_cases i <;> norm_num [foldGenerator, Fin.sum_univ_two, u]
        decide
      rw [hz]
      exact (projectedCode C _).zero_mem
    · intro hm
      obtain ⟨c, hc, heq⟩ := (mem_projectedCode C Finset.univ u).mp hm
      apply hnot
      have hcu : c = u := funext fun i => heq i (Finset.mem_univ _)
      rwa [← hcu]

/-- BCHKS25 Theorem 4.6 uses degree ratio, not message dimension divided by
length. This is the claimed numerator only, not an exceptional-set bound.
The meaningful theorem needs positive rate and positive Johnson slack. -/
noncomputable def johnsonNumerator (length dimension : ℕ) (radius : ℝ) : ℝ :=
  let rate : ℝ := (dimension - 1 : ℕ) / length
  let slack := 1 - Real.sqrt rate - radius
  let m : ℕ := max ⌈Real.sqrt rate / slack⌉₊ 3
  let t : ℝ := m + 1 / 2
  ((2 * t ^ 5 + 3 * t * radius * rate) / (3 * Real.sqrt rate ^ 3)) * length +
    t / Real.sqrt rate

end Whir.MutualAgreement
