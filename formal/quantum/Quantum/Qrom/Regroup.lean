module

public import VCVio.Quantum.Oracle.Model
public import VCVio.Quantum.Oracle.Emulated

@[expose] public section

/-!
# Regrouping random-oracle inputs into cells with pair answers

A random function `F : X → Y × Y` answers the inputs of a random function `X → Y` two at a time:
a permutation `τ` of `X × Bool` sends `x` to the cell `c` and slot `b` with `τ (x, false) = (c, b)`,
and `regroup τ F x` is component `b` of `F c`. Every function `X → Y` is the regrouping of exactly
`|Y|^|X|` functions `X → Y × Y` (`sum_regroup`, `card_regroup_fiber`), so uniform `F` regroups to
uniform `H`.

One call of `H` is one call of `F` (`regroupCalls`): the isometry `regroupIso` moves the input `x`
to its cell `c`, the response into slot `b` and the flag `b` into a fresh register, and prepares
the other slot in the uniform superposition, on which adding an answer acts as the identity; after
the call of `F`, the adjoint of the isometry reads the result back. On every call with any
workspace this is the call of `regroup τ F` (`queryStep_regroup`), so the run of a program is the
same (`run_regroup_eq`) and so is its law in the quantum random-oracle model
(`qromEvalDistMap_regroup`).
-/

open MeasureTheory
open scoped ENNReal Kronecker Matrix ComplexOrder

universe v w

namespace Quantum.Qrom

/-! ## Pairs and regrouped functions -/

section regroup

variable {X Y : Type}

/-- The component of a pair in slot `b`: the second for `true`, the first for `false`. -/
def pairPart (b : Bool) (a : Y × Y) : Y :=
  cond b a.2 a.1

/-- The pair holding `y` in slot `b` and `y'` in the other slot. -/
def placePair (b : Bool) (y y' : Y) : Y × Y :=
  cond b (y', y) (y, y')

/-- The function `X → Y` read off `F : X → Y × Y` through `τ`: the input `x` is answered by the
component `b` of `F c`, where `τ (x, false) = (c, b)`. -/
def regroup (τ : Equiv.Perm (X × Bool)) (F : X → Y × Y) : X → Y :=
  fun x ↦ pairPart (τ (x, false)).2 (F (τ (x, false)).1)

/-- The component of `F c` that `regroup τ F` leaves unused at `x`, for `τ (x, false) = (c, b)`. -/
def regroupSpare (τ : Equiv.Perm (X × Bool)) (F : X → Y × Y) : X → Y :=
  fun x ↦ pairPart (!(τ (x, false)).2) (F (τ (x, false)).1)

theorem regroup_apply_of_eq {τ : Equiv.Perm (X × Bool)} {x c : X} {b : Bool}
    (h : τ (x, false) = (c, b)) (F : X → Y × Y) : regroup τ F x = pairPart b (F c) := by
  rw [regroup, h]

/-- An input that `τ` leaves in place is answered by the first component of its own cell. -/
theorem regroup_apply_of_fixed {τ : Equiv.Perm (X × Bool)} {x : X} (h : τ (x, false) = (x, false))
    (F : X → Y × Y) : regroup τ F x = (F x).1 :=
  regroup_apply_of_eq h F

/-- An input that `τ` sends to the second slot of the cell `c` is answered by `(F c).2`. -/
theorem regroup_apply_of_second {τ : Equiv.Perm (X × Bool)} {x c : X}
    (h : τ (x, false) = (c, true)) (F : X → Y × Y) : regroup τ F x = (F c).2 :=
  regroup_apply_of_eq h F

/-- Pair-valued functions are pairs of functions: the regrouped function and the function of the
inputs `τ⁻¹ (c, b)` with flag `true`. -/
def regroupEquiv (τ : Equiv.Perm (X × Bool)) : (X → Y × Y) ≃ (X → Y) × (X → Y) where
  toFun F := (regroup τ F, fun x ↦ pairPart (τ (x, true)).2 (F (τ (x, true)).1))
  invFun P c :=
    (cond (τ.symm (c, false)).2 (P.2 (τ.symm (c, false)).1) (P.1 (τ.symm (c, false)).1),
      cond (τ.symm (c, true)).2 (P.2 (τ.symm (c, true)).1) (P.1 (τ.symm (c, true)).1))
  left_inv F := by
    have h : ∀ p : X × Bool, cond p.2 (pairPart (τ (p.1, true)).2 (F (τ (p.1, true)).1))
        (pairPart (τ (p.1, false)).2 (F (τ (p.1, false)).1)) = pairPart (τ p).2 (F (τ p).1) := by
      rintro ⟨x, _ | _⟩ <;> rfl
    funext c
    refine Prod.ext ?_ ?_
    · refine (h (τ.symm (c, false))).trans ?_
      rw [Equiv.apply_symm_apply]
      rfl
    · refine (h (τ.symm (c, true))).trans ?_
      rw [Equiv.apply_symm_apply]
      rfl
  right_inv P := by
    have h : ∀ (b : Bool) (c : X), pairPart b
        (cond (τ.symm (c, false)).2 (P.2 (τ.symm (c, false)).1) (P.1 (τ.symm (c, false)).1),
          cond (τ.symm (c, true)).2 (P.2 (τ.symm (c, true)).1) (P.1 (τ.symm (c, true)).1)) =
        cond (τ.symm (c, b)).2 (P.2 (τ.symm (c, b)).1) (P.1 (τ.symm (c, b)).1) := by
      rintro (_ | _) c <;> rfl
    refine Prod.ext (funext fun x ↦ ?_) (funext fun x ↦ ?_)
    · refine (h _ _).trans ?_
      rw [Prod.mk.eta, Equiv.symm_apply_apply]
      rfl
    · refine (h _ _).trans ?_
      rw [Prod.mk.eta, Equiv.symm_apply_apply]
      rfl

theorem regroupEquiv_fst (τ : Equiv.Perm (X × Bool)) (F : X → Y × Y) :
    (regroupEquiv τ F).1 = regroup τ F :=
  rfl

theorem regroup_regroupEquiv_symm (τ : Equiv.Perm (X × Bool)) (P : (X → Y) × (X → Y)) :
    regroup τ ((regroupEquiv τ).symm P) = P.1 :=
  congrArg Prod.fst ((regroupEquiv τ).apply_symm_apply P)

/-- **Uniform pushforward.** Summing over pair-valued functions a quantity that depends only on
the regrouped function counts every function `X → Y` exactly `|X → Y|` times. -/
theorem sum_regroup [Fintype X] [DecidableEq X] [Fintype Y] {M : Type*} [AddCommMonoid M]
    (τ : Equiv.Perm (X × Bool))
    (g : (X → Y) → M) :
    ∑ F : X → Y × Y, g (regroup τ F) = Fintype.card (X → Y) • ∑ H : X → Y, g H := by
  rw [← (regroupEquiv τ).symm.sum_comp]
  simp only [regroup_regroupEquiv_symm, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ]
  rw [Finset.smul_sum]

/-- **Equal fibers.** Every function `X → Y` is the regrouping of exactly `|X → Y|` functions
`X → Y × Y`. -/
theorem card_regroup_fiber [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (τ : Equiv.Perm (X × Bool)) (H : X → Y) :
    (Finset.univ.filter fun F : X → Y × Y ↦ regroup τ F = H).card = Fintype.card (X → Y) := by
  rw [Finset.card_filter, sum_regroup τ fun H' ↦ if H' = H then 1 else 0,
    Finset.sum_ite_eq' Finset.univ H, ite_eq_left (Finset.mem_univ H), smul_eq_mul, mul_one]

end regroup

/-! ## Matrices of a regrouped call -/

section matrix

/-- Multiplying by the basis matrix of a bijection on the left relabels the rows. -/
private theorem basisMatrix_equiv_mul_eq_submatrix {l m n : Type*} [Fintype m]
    [DecidableEq l] (e : m ≃ l) (M : Matrix m n ℂ) :
    basisMatrix e * M = M.submatrix e.symm id := by
  ext a b
  simp only [Matrix.mul_apply, basisMatrix_apply, ite_mul, one_mul, zero_mul,
    Matrix.submatrix_apply, id]
  rw [Finset.sum_eq_single (e.symm a) (fun c _ hc ↦ ite_eq_right fun h ↦ hc (by simp [h]))
    (fun h ↦ absurd (Finset.mem_univ _) h), ite_eq_left (by simp)]

/-- Multiplying by a basis matrix on the right relabels the columns. -/
private theorem mul_basisMatrix_eq_submatrix {l m n : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix l m ℂ) (g : n → m) : M * basisMatrix g = M.submatrix id g := by
  ext a b
  simp [Matrix.mul_apply, basisMatrix_apply]

/-- The matrix of a call against a stateless step `P` beside a runtime register `D` is the call
of `P` beside the remainder, beside the identity on `D`. -/
private theorem basisMatrix_queryEquivOut_mul_kronecker {O I A E D : Type*} [Fintype O]
    [Fintype I] [Fintype A] [Fintype E] [Fintype D] [DecidableEq O] [DecidableEq I]
    [DecidableEq A] [DecidableEq E] [DecidableEq D] (P : Matrix O I ℂ) (ℓ : A ≃ I × E) :
    basisMatrix (QuantumRuntime.queryEquivOut O D E) *
        ((P ⊗ₖ (1 : Matrix D D ℂ)) ⊗ₖ (1 : Matrix E E ℂ)) *
        basisMatrix (QuantumRuntime.queryEquivIn ℓ D) =
      ((P ⊗ₖ (1 : Matrix E E ℂ)) * basisMatrix ℓ) ⊗ₖ (1 : Matrix D D ℂ) := by
  rw [basisMatrix_equiv_eq_conjTranspose (QuantumRuntime.queryEquivOut O D E),
    conjTranspose_basisMatrix_mul_mul_basisMatrix, mul_basisMatrix_eq_submatrix]
  ext ⟨⟨o, e⟩, d⟩ ⟨a, d'⟩
  have hs : (QuantumRuntime.queryEquivOut O D E).symm ((o, e), d) = ((o, d), e) := rfl
  simp only [Matrix.submatrix_apply, hs, QuantumRuntime.queryEquivIn_apply,
    Matrix.kroneckerMap_apply, id]
  ring

variable {X Y : Type}

/-- The amplitude `|Y|^(-1/2)` of the uniform superposition over `Y`. -/
noncomputable def uniformAmp (Y : Type) [Fintype Y] : ℂ :=
  ((Real.sqrt (Fintype.card Y))⁻¹ : ℝ)

theorem card_mul_star_uniformAmp_mul_self [Fintype Y] [Nonempty Y] :
    (Fintype.card Y : ℂ) * (star (uniformAmp Y) * uniformAmp Y) = 1 := by
  have hn : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h : (Real.sqrt (Fintype.card Y))⁻¹ * (Real.sqrt (Fintype.card Y))⁻¹ =
      ((Fintype.card Y : ℝ))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [uniformAmp, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, h,
    Complex.ofReal_inv, Complex.ofReal_natCast,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- Preparing a fresh register `Y` in the uniform superposition beside `R`. -/
noncomputable def prepUniform (R Y : Type) [DecidableEq R] [Fintype Y] : Matrix (R × Y) R ℂ :=
  Matrix.of fun p r ↦ if p.1 = r then uniformAmp Y else 0

theorem conjTranspose_prepUniform_mul_self [Fintype Y] [Nonempty Y] (R : Type) [Fintype R]
    [DecidableEq R] :
    (prepUniform R Y)ᴴ * prepUniform R Y = 1 := by
  ext r r'
  rw [Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single r (fun x _ hx ↦ Finset.sum_eq_zero fun y _ ↦ by simp [prepUniform, hx])
      (fun h ↦ absurd (Finset.mem_univ r) h)]
  by_cases h : r = r'
  · subst h
    simp only [Matrix.conjTranspose_apply, prepUniform, Matrix.of_apply, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Matrix.one_apply_eq]
    exact card_mul_star_uniformAmp_mul_self
  · simp [prepUniform, h]

/-- The basis map of a regrouped call, beside the remainder `E` and the prepared register `y'`:
the input `x` goes to the cell `c`, the response `y` into slot `b` and `y'` into the other slot,
the flag `b` beside the remainder, where `τ (x, false) = (c, b)`. -/
def regroupRoute (τ : Equiv.Perm (X × Bool)) (E : Type) (p : ((X × Y) × E) × Y) :
    (X × (Y × Y)) × (Bool × E) :=
  (((τ (p.1.1.1, false)).1, placePair (τ (p.1.1.1, false)).2 p.1.1.2 p.2),
    ((τ (p.1.1.1, false)).2, p.1.2))

theorem regroupRoute_injective (τ : Equiv.Perm (X × Bool)) (E : Type) :
    Function.Injective (regroupRoute (Y := Y) τ E) := by
  rintro ⟨⟨⟨x, y⟩, e⟩, y'⟩ ⟨⟨⟨x', z⟩, e'⟩, z'⟩ h
  simp only [regroupRoute, Prod.mk.injEq] at h
  obtain ⟨⟨hc, hp⟩, hb, rfl⟩ := h
  obtain rfl : x = x' := congrArg Prod.fst (τ.injective (Prod.ext hc hb))
  revert hp
  rcases τ (x, false) with ⟨c, _ | _⟩ <;>
    simp only [placePair, Bool.cond_false, Bool.cond_true, Prod.mk.injEq] <;>
    rintro ⟨rfl, rfl⟩ <;> simp

/-- The isometry of a regrouped call: prepare the uniform superposition, then route. -/
noncomputable def regroupIso [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (τ : Equiv.Perm (X × Bool)) (E : Type) [Fintype E]
    [DecidableEq E] : Matrix ((X × (Y × Y)) × (Bool × E)) ((X × Y) × E) ℂ :=
  basisMatrix (regroupRoute τ E) * prepUniform ((X × Y) × E) Y

theorem conjTranspose_regroupIso_mul_self [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] (τ : Equiv.Perm (X × Bool)) (E : Type) [Fintype E]
    [DecidableEq E] : (regroupIso (Y := Y) τ E)ᴴ * regroupIso (Y := Y) τ E = 1 := by
  rw [regroupIso, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (basisMatrix (regroupRoute τ E))ᴴ,
    conjTranspose_basisMatrix_mul_self (regroupRoute_injective τ E), Matrix.one_mul,
    conjTranspose_prepUniform_mul_self]

/-- The answer of `regroup τ F` added into the response and that of `regroupSpare τ F` into the
prepared register. -/
def regroupShift [AddCommGroup Y] (τ : Equiv.Perm (X × Bool)) (F : X → Y × Y) (E : Type) :
    ((X × Y) × E) × Y ≃ ((X × Y) × E) × Y where
  toFun p := (((p.1.1.1, p.1.1.2 + regroup τ F p.1.1.1), p.1.2), p.2 + regroupSpare τ F p.1.1.1)
  invFun p := (((p.1.1.1, p.1.1.2 - regroup τ F p.1.1.1), p.1.2), p.2 - regroupSpare τ F p.1.1.1)
  left_inv p := by simp
  right_inv p := by simp

theorem regroupRoute_regroupShift [AddCommGroup Y] (τ : Equiv.Perm (X × Bool)) (F : X → Y × Y)
    (E : Type) :
    Prod.map (oracleEquiv F) id ∘ regroupRoute τ E = regroupRoute τ E ∘ regroupShift τ F E := by
  funext ⟨⟨⟨x, y⟩, e⟩, y'⟩
  simp only [Function.comp_apply, Prod.map_apply, regroupRoute, regroupShift, Equiv.coe_fn_mk,
    oracleEquiv_apply, id, regroup, regroupSpare]
  rcases τ (x, false) with ⟨c, _ | _⟩ <;> rfl

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Adding an answer into the uniform superposition leaves it unchanged. -/
theorem basisMatrix_regroupShift_mul_prepUniform (τ : Equiv.Perm (X × Bool)) (F : X → Y × Y)
    (E : Type) [Fintype E] [DecidableEq E] :
    basisMatrix (regroupShift τ F E) * prepUniform ((X × Y) × E) Y =
      prepUniform ((X × Y) × E) Y * (oracleUnitary (regroup τ F) ⊗ₖ (1 : Matrix E E ℂ)) := by
  rw [basisMatrix_equiv_mul_eq_submatrix,
    show oracleUnitary (regroup τ F) = basisMatrix (oracleEquiv (regroup τ F)) from rfl,
    basisMatrix_kronecker_one, mul_basisMatrix_eq_submatrix]
  ext ⟨⟨⟨x, y⟩, e⟩, y'⟩ ⟨⟨x₀, y₀⟩, e₀⟩
  simp only [Matrix.submatrix_apply, prepUniform, Matrix.of_apply, id, Prod.map_apply,
    oracleEquiv_apply, regroupShift, Equiv.coe_fn_symm_mk, Prod.mk.injEq]
  by_cases hx : x = x₀
  · subst hx
    simp only [true_and, sub_eq_iff_eq_add]
  · simp only [hx, false_and]

/-- **The oracle of `F` on the regrouped register is the oracle of `regroup τ F`.** -/
theorem oracleUnitary_kronecker_mul_regroupIso (τ : Equiv.Perm (X × Bool)) (F : X → Y × Y)
    (E : Type) [Fintype E] [DecidableEq E] :
    (oracleUnitary F ⊗ₖ (1 : Matrix (Bool × E) (Bool × E) ℂ)) * regroupIso τ E =
      regroupIso τ E * (oracleUnitary (regroup τ F) ⊗ₖ (1 : Matrix E E ℂ)) := by
  rw [regroupIso, show oracleUnitary F = basisMatrix (oracleEquiv F) from rfl,
    basisMatrix_kronecker_one, ← Matrix.mul_assoc, ← basisMatrix_comp,
    regroupRoute_regroupShift, basisMatrix_comp, Matrix.mul_assoc, Matrix.mul_assoc,
    basisMatrix_regroupShift_mul_prepUniform]

/-- The matrix identity behind one regrouped call, beside the remainder `E` and the runtime
register `D`. -/
theorem regroupCall_matrix (τ : Equiv.Perm (X × Bool)) (F : X → Y × Y) {A E D : Type}
    [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
    (ℓ : A ≃ (X × Y) × E) :
    ((regroupIso (Y := Y) τ E)ᴴ ⊗ₖ (1 : Matrix D D ℂ)) *
        (basisMatrix (QuantumRuntime.queryEquivOut (X × (Y × Y)) D (Bool × E)) *
            ((oracleUnitary F ⊗ₖ (1 : Matrix D D ℂ)) ⊗ₖ
              (1 : Matrix (Bool × E) (Bool × E) ℂ)) *
            basisMatrix
              (QuantumRuntime.queryEquivIn (Equiv.refl ((X × (Y × Y)) × (Bool × E))) D) *
          ((regroupIso (Y := Y) τ E * basisMatrix ℓ) ⊗ₖ (1 : Matrix D D ℂ))) =
      basisMatrix (QuantumRuntime.queryEquivOut (X × Y) D E) *
        ((oracleUnitary (regroup τ F) ⊗ₖ (1 : Matrix D D ℂ)) ⊗ₖ (1 : Matrix E E ℂ)) *
        basisMatrix (QuantumRuntime.queryEquivIn ℓ D) := by
  rw [basisMatrix_queryEquivOut_mul_kronecker, basisMatrix_queryEquivOut_mul_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
    Equiv.coe_refl, basisMatrix_id, Matrix.mul_one, ← Matrix.mul_assoc (_ ⊗ₖ _),
    oracleUnitary_kronecker_mul_regroupIso, Matrix.mul_assoc, ← Matrix.mul_assoc (_ᴴ),
    conjTranspose_regroupIso_mul_self, Matrix.one_mul]

end matrix

/-! ## Regrouped calls -/

section calls

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {W : QReg → Type w}

/-- Before a regrouped call: the isometry `regroupIso` on the input exposed by `ℓ`. -/
noncomputable def regroupEmbed (τ : Equiv.Perm (X × Bool)) (E : QReg) {A : QReg}
    (ℓ : A ≃ (X × Y) × E) :
    SubInstrument A (QReg.of (X × (Y × Y)) × QReg.of (Bool × E)) PUnit.{v + 1} :=
  SubInstrument.ofMap (MatrixMap.conj (regroupIso (Y := Y) τ E * basisMatrix ℓ))
    (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (regroupIso (Y := Y) τ E)ᴴ,
        conjTranspose_regroupIso_mul_self, Matrix.one_mul,
        conjTranspose_basisMatrix_mul_self ℓ.injective, sub_self]
      exact Matrix.PosSemidef.zero))

/-- After a regrouped call: the adjoint of `regroupIso`, a contraction. -/
noncomputable def regroupProject (τ : Equiv.Perm (X × Bool)) (E : QReg) :
    SubInstrument (QReg.of (X × (Y × Y)) × QReg.of (Bool × E)) (QReg.of (X × Y) × E)
      PUnit.{v + 1} :=
  SubInstrument.ofMap (MatrixMap.conj (regroupIso (Y := Y) τ E)ᴴ) (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (posSemidef_one_sub_conjTranspose_mul_self (by
      rw [Matrix.conjTranspose_conjTranspose, conjTranspose_regroupIso_mul_self])))

/-- Local operations are kept; a call of `H` on `X × Y` with remainder `E` becomes the isometry
`regroupEmbed`, a call of `F` on `X × (Y × Y)` with remainder `Bool × E`, and `regroupProject`. -/
noncomputable def regroupSubstitution (τ : Equiv.Perm (X × Bool)) :
    IPFunctor.CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{v} (qromSpec X Y))
      (QuantumComp.toIPFunctor LocalSig.instruments.{v} (qromSpec X (Y × Y)))
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query _ E ℓ =>
      QuantumComp.primBind (L := LocalSig.instruments.{v})
        ⟨PUnit, fun _ ↦ QReg.of (QReg.of (X × (Y × Y)) × QReg.of (Bool × E)), regroupEmbed τ E ℓ⟩
        fun _ ↦ QuantumComp.queryBind (A := QReg.of (QReg.of (X × (Y × Y)) × QReg.of (Bool × E)))
          () (QReg.of (Bool × E)) (Equiv.refl _) fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{v})
            ⟨PUnit, fun _ ↦ QReg.of (QReg.of (X × Y) × E), regroupProject τ E⟩ fun _ ↦
            QuantumComp.pure ⟨ULift.up (), rfl⟩

/-- **Regrouped calls.** The program `x` over the oracle `X → Y`, with each call made through
one call of the oracle `X → Y × Y` (`regroupSubstitution`). -/
noncomputable def regroupCalls (τ : Equiv.Perm (X × Bool)) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (qromSpec X Y) W A) :
    QuantumComp LocalSig.instruments.{v} (qromSpec X (Y × Y)) W A :=
  IPFunctor.IFreeM.substitute (regroupSubstitution τ) x

variable (τ : Equiv.Perm (X × Bool))

@[simp]
theorem regroupCalls_pure {A : QReg} (y : W A) :
    regroupCalls τ (QuantumComp.pure (L := LocalSig.instruments.{v}) (spec := qromSpec X Y) y) =
      QuantumComp.pure y :=
  rfl

@[simp]
theorem regroupCalls_primBind {A : QReg} (o : LocalSig.instruments.{v}.Op A)
    (k : (b : LocalSig.instruments.{v}.Outcome o) →
      QuantumComp LocalSig.instruments.{v} (qromSpec X Y) W (LocalSig.instruments.{v}.next o b)) :
    regroupCalls τ (QuantumComp.primBind o k) =
      QuantumComp.primBind o fun b ↦ regroupCalls τ (k b) :=
  rfl

theorem regroupCalls_queryBind {A : QReg} (i : Unit) (E : QReg) (ℓ : A ≃ (X × Y) × E)
    (k : Unit → QuantumComp LocalSig.instruments.{v} (qromSpec X Y) W
      (QReg.of (QReg.of (X × Y) × E))) :
    regroupCalls τ (QuantumComp.queryBind (spec := qromSpec X Y) i E ℓ k) =
      QuantumComp.primBind (L := LocalSig.instruments.{v})
        ⟨PUnit, fun _ ↦ QReg.of (QReg.of (X × (Y × Y)) × QReg.of (Bool × E)), regroupEmbed τ E ℓ⟩
        fun _ ↦ QuantumComp.queryBind (A := QReg.of (QReg.of (X × (Y × Y)) × QReg.of (Bool × E)))
          () (QReg.of (Bool × E)) (Equiv.refl _) fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{v})
            ⟨PUnit, fun _ ↦ QReg.of (QReg.of (X × Y) × E), regroupProject τ E⟩ fun _ ↦
            regroupCalls τ (k ()) :=
  rfl

/-- **One call of `H` is one call of `F`.** -/
theorem isQueryBound_regroupCalls {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} (qromSpec X Y) W A} {b : Unit → ℕ}
    (hx : x.IsQueryBound b) : (regroupCalls τ x).IsQueryBound b := by
  intro i
  change IPFunctor.IFreeM.IsChargeBound (regroupCalls τ x) (QuantumComp.queryCharge i) (b i)
  refine IPFunctor.IFreeM.IsChargeBound.substitute (regroupSubstitution τ)
    (c := QuantumComp.queryCharge (L := LocalSig.instruments.{v}) (spec := qromSpec X Y) i) ?_
    (show IPFunctor.IFreeM.IsChargeBound x
      (QuantumComp.queryCharge (L := LocalSig.instruments.{v}) (spec := qromSpec X Y) i) (b i)
      from hx i)
  intro A c
  change QuantumComp.IsQueryBoundAt (regroupSubstitution τ A c) i _
  cases c with
  | prim o =>
    simp [regroupSubstitution, QuantumComp.queryCharge, QuantumComp.isQueryBoundAt_primBind_iff]
  | query j E ℓ =>
    cases i
    cases j
    simp [regroupSubstitution, QuantumComp.queryCharge, QuantumComp.isQueryBoundAt_primBind_iff,
      QuantumComp.isQueryBoundAt_queryBind_iff]

/-- The step of the oracle runtime of `H` is the Kraus map of its unitary. -/
private theorem additiveOracleRuntime_step_branch {Z : Type} [Fintype Z] [DecidableEq Z]
    [AddCommGroup Z] (H : X → Z) (i r : Unit) :
    ((additiveOracleRuntime H).step i).branch r =
      MatrixMap.conj (oracleUnitary H ⊗ₖ
        (1 : Matrix (additiveOracleRuntime H).D (additiveOracleRuntime H).D ℂ)) := by
  change (((oracleQuery H).frame Unit).branch r) = _
  rw [DSubInstrument.branch_frame_apply, branch_oracleQuery_apply, MatrixMap.amplify_conj]
  rfl

/-- **One regrouped call**, with any workspace `E`: the isometry, the call of `F` and the
contraction act as the call of `regroup τ F`. -/
theorem queryStep_regroup (F : X → Y × Y) (E : QReg) {A : QReg} (ℓ : A ≃ (X × Y) × E) :
    ((regroupProject.{v} τ E).frame (additiveOracleRuntime F).D).branch PUnit.unit ∘ₗ
      (((additiveOracleRuntime F).queryStep
          (A := QReg.of (QReg.of (X × (Y × Y)) × QReg.of (Bool × E))) () (QReg.of (Bool × E))
          (Equiv.refl _)).branch () ∘ₗ
        ((regroupEmbed.{v} τ E ℓ).frame (additiveOracleRuntime F).D).branch PUnit.unit) =
      ((additiveOracleRuntime (regroup τ F)).queryStep () E ℓ).branch () := by
  rw [(additiveOracleRuntime F).queryStep_branch_eq_conj
      (additiveOracleRuntime_step_branch F () ()),
    (additiveOracleRuntime (regroup τ F)).queryStep_branch_eq_conj
      (additiveOracleRuntime_step_branch (regroup τ F) () ()),
    DSubInstrument.branch_frame_apply, DSubInstrument.branch_frame_apply]
  change LinearMap.comp ((MatrixMap.conj _).amplify _)
    (LinearMap.comp _ ((MatrixMap.conj _).amplify _)) = _
  rw [MatrixMap.amplify_conj, MatrixMap.amplify_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
  exact congrArg MatrixMap.conj (regroupCall_matrix τ F ℓ)

/-- **Regrouping preserves runs.** The program with regrouped calls, against the oracle of `F`,
runs as the program against the oracle of `regroup τ F`. -/
theorem run_regroup_eq (F : X → Y × Y) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (qromSpec X Y) W A) :
    (additiveOracleRuntime F).run .instruments (regroupCalls τ x) =
      (additiveOracleRuntime (regroup τ F)).run .instruments x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    exact congrArg (((LocalSig.Interp.instruments o).frame (additiveOracleRuntime F).D).bind)
      (funext ih)
  | queryBind _ i E ℓ k ih =>
    cases i
    simp only [regroupCalls_queryBind, QuantumRuntime.run_primBind,
      QuantumRuntime.run_queryBind]
    refine DSubInstrument.ext (funext fun p ↦ ?_)
    simp only [LocalSig.Interp.instruments_apply, DSubInstrument.branch_bind_apply_univ,
      Fintype.sum_unique, LinearMap.comp_assoc]
    rw [queryStep_regroup τ F E ℓ, ih]
    rfl

/-- A lossless program runs losslessly with regrouped calls. -/
theorem lossless_run_regroupCalls {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} (qromSpec X Y) W A}
    (hx : x.Lossless .instruments) (F : X → Y × Y) :
    ((additiveOracleRuntime F).run .instruments (regroupCalls τ x)).Lossless := by
  rw [run_regroup_eq]
  exact lossless_run_additiveOracleRuntime _ hx _

theorem evalDistMap_regroup_eq {β : Type*} [MeasurableSpace β] (F : X → Y × Y) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (qromSpec X Y) W A) (ρ : SubState A)
    (g : (Σ u, W u) → β) :
    (additiveOracleRuntime F).evalDistMap .instruments (regroupCalls τ x) ρ g =
      (additiveOracleRuntime (regroup τ F)).evalDistMap .instruments x ρ g := by
  unfold QuantumRuntime.evalDistMap QuantumRuntime.jointPost
  rw [run_regroup_eq]
  rfl

/-- **Regrouping in the quantum random-oracle model.** Running the program with regrouped calls
against a uniform `F : X → Y × Y` and observing `regroup τ F` has the law of running the program
against a uniform `H : X → Y` and observing `H`. -/
theorem qromEvalDistMap_regroup {β : Type*} [MeasurableSpace β] {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (qromSpec X Y) W A) (ρ : SubState A)
    (f : (X → Y) → (Σ u, W u) → β) :
    qromEvalDistMap .instruments (regroupCalls τ x) ρ (fun F ↦ f (regroup τ F)) =
      qromEvalDistMap .instruments x ρ f := by
  have hn : (Fintype.card (X → Y) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum := sum_regroup (M := Measure β) τ fun H ↦
    (additiveOracleRuntime H).evalDistMap LocalSig.Interp.instruments x ρ (f H)
  beta_reduce at hsum
  rw [qromEvalDistMap, qromEvalDistMap, sampledEvalDistMap_eq_sum, sampledEvalDistMap_eq_sum,
    Fintype.card_congr (regroupEquiv τ), Fintype.card_prod]
  simp only [evalDistMap_regroup_eq]
  rw [hsum, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl hn) (Or.inl (ENNReal.natCast_ne_top _)), mul_assoc,
    ENNReal.inv_mul_cancel hn (ENNReal.natCast_ne_top _), mul_one]

/-- **Regrouping in the quantum random-oracle model**, for the distribution of the leaf. -/
theorem qromEvalDist_regroup [MeasurableSpace (Σ u, W u)] {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (qromSpec X Y) W A) (ρ : SubState A) :
    qromEvalDist .instruments (regroupCalls τ x) ρ = qromEvalDist .instruments x ρ :=
  qromEvalDistMap_regroup τ x ρ fun _ p ↦ p

/-- **Regrouping in the quantum random-oracle model**, for the value of a fixed-register
program. -/
theorem qromEvalDistMap₂_regroup {β : Type*} [MeasurableSpace β] {A B : QReg} {α : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} (qromSpec X Y) A B α) (ρ : SubState A)
    (f : (X → Y) → α → β) :
    qromEvalDistMap₂ .instruments (regroupCalls τ x) ρ (fun F ↦ f (regroup τ F)) =
      qromEvalDistMap₂ .instruments x ρ f :=
  qromEvalDistMap_regroup τ x ρ fun H p ↦ f H ((QuantumComp₂.leafEquiv B α).symm p)

end calls

end Quantum.Qrom
