module

public import Quantum.Qrom.Sphincs.DepthRegroup

@[expose] public section

/-!
# The interleaved and the batched rounds run alike

Against every runtime of runtime 2's signature with record ports, a round of `w` regrouped calls
of `H` run as `w` interleaved triples (`regRoundR`: embed, call `h`, project) is the batched round
(`batRoundR`: embed every slot, the `w` calls of `h`, project every slot): `roundsCommute`.

Every map involved acts on disjoint tensor factors of one canonical layout
`((slot 0 × other slots) × remainder) × runtime register`:

* `act0`, `actW`: a map on slot 0, or on the other slots;
* `actP`, `actQ`: a map on the call register of slot 0, or of the other slots, beside the runtime
  register;
* `batched_eq_interleaved`: maps on disjoint factors commute
  (`MatrixMap.amplify_comp_amplifyLeft`), so the batched order is the interleaved one.

The isometry of `w + 1` slots is the isometry of slot 0 beside that of the others
(`isoAll_succ_eq`), and the round step of `w + 1` calls is the step of the first call, then the
round of the others. Both rounds of width `w + 1` are therefore the relabellings `eIn`, `eOut`
around the two orders of `batched_eq_interleaved` (`batRoundR_succ_branch`,
`interleaved_succ_branch`), and induction on `w` closes the proof.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Sphincs

open Quantum Quantum.Par Quantum.SubInstrument
open Quantum.Xmss.Assembly (recHwSpec)

/-! ## Maps on disjoint parts -/

section parts

/-- Relabelling rows and columns along a bijection, as a matrix map. -/
def relM {A B : Type*} (e : A ≃ B) : MatrixMap A B where
  toFun ρ := ρ.submatrix e.symm e.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem relM_apply {A B : Type*} (e : A ≃ B) (ρ : Matrix A A ℂ) :
    relM e ρ = ρ.submatrix e.symm e.symm :=
  rfl

variable {S0 S0' Sw Sw' P P' Q Q' B F E D : Type*}

/-- A map on the first part of `((S0 × Sw) × E) × D`. -/
def act0 (V : MatrixMap S0 S0') (Sw E D : Type*) :
    MatrixMap (((S0 × Sw) × E) × D) (((S0' × Sw) × E) × D) :=
  ((V.amplify Sw).amplify E).amplify D

/-- A map on the second part of `((S0 × Sw) × E) × D`. -/
def actW (V : MatrixMap Sw Sw') (S0 E D : Type*) :
    MatrixMap (((S0 × Sw) × E) × D) (((S0 × Sw') × E) × D) :=
  ((V.amplifyLeft S0).amplify E).amplify D

/-- Bring the first component of the first part next to the last factor. -/
def eqP (P B Sw E D : Type*) : (((P × B) × Sw) × E) × D ≃ (P × D) × ((B × Sw) × E) where
  toFun x := ((x.1.1.1.1, x.2), ((x.1.1.1.2, x.1.1.2), x.1.2))
  invFun y := ((((y.1.1, y.2.1.1), y.2.1.2), y.2.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Bring the first component of the second part next to the last factor. -/
def eqQ (S0 Q F E D : Type*) : (((S0 × (Q × F)) × E) × D) ≃ (Q × D) × ((S0 × F) × E) where
  toFun x := ((x.1.1.2.1, x.2), ((x.1.1.1, x.1.1.2.2), x.1.2))
  invFun y := (((y.2.1.1, (y.1.1, y.2.1.2)), y.2.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A map on the first component of the first part and the last factor. -/
def actP (Φ : MatrixMap (P × D) (P' × D)) (B Sw E : Type*) :
    MatrixMap ((((P × B) × Sw) × E) × D) ((((P' × B) × Sw) × E) × D) :=
  relM (eqP P' B Sw E D).symm ∘ₗ Φ.amplify ((B × Sw) × E) ∘ₗ relM (eqP P B Sw E D)

/-- A map on the first component of the second part and the last factor. -/
def actQ (Ψ : MatrixMap (Q × D) (Q' × D)) (S0 F E : Type*) :
    MatrixMap (((S0 × (Q × F)) × E) × D) (((S0 × (Q' × F)) × E) × D) :=
  relM (eqQ S0 Q' F E D).symm ∘ₗ Ψ.amplify ((S0 × F) × E) ∘ₗ relM (eqQ S0 Q F E D)

theorem act0_comp_actW [Finite S0] (V : MatrixMap S0 S0') (U : MatrixMap Sw Sw') :
    act0 V Sw' E D ∘ₗ actW U S0 E D = actW U S0' E D ∘ₗ act0 V Sw E D :=
  congrArg (fun T : MatrixMap (S0 × Sw) (S0' × Sw') ↦ MatrixMap.amplify (T.amplify E) D)
    (MatrixMap.amplify_comp_amplifyLeft V U)

theorem act0_comp_actW_assoc [Finite S0] {T : Type*} (V : MatrixMap S0 S0')
    (U : MatrixMap Sw Sw') (L : MatrixMap T (((S0 × Sw) × E) × D)) :
    act0 V Sw' E D ∘ₗ actW U S0 E D ∘ₗ L = actW U S0' E D ∘ₗ act0 V Sw E D ∘ₗ L := by
  rw [← LinearMap.comp_assoc, act0_comp_actW, LinearMap.comp_assoc]

theorem actW_eq_amplifyLeft (U : MatrixMap Sw Sw') :
    actW U (P × B) E D = relM (eqP P B Sw' E D).symm ∘ₗ
      ((U.amplifyLeft B).amplify E).amplifyLeft (P × D) ∘ₗ relM (eqP P B Sw E D) :=
  LinearMap.ext fun _ ↦ rfl

theorem act0_eq_amplifyLeft (V : MatrixMap S0 S0') :
    act0 V (Q × F) E D = relM (eqQ S0' Q F E D).symm ∘ₗ
      ((V.amplify F).amplify E).amplifyLeft (Q × D) ∘ₗ relM (eqQ S0 Q F E D) :=
  LinearMap.ext fun _ ↦ rfl

theorem actP_comp_actW [Finite P] [Finite D] (Φ : MatrixMap (P × D) (P' × D))
    (U : MatrixMap Sw Sw') :
    actP Φ B Sw' E ∘ₗ actW U (P × B) E D = actW U (P' × B) E D ∘ₗ actP Φ B Sw E := by
  rw [actW_eq_amplifyLeft, actW_eq_amplifyLeft]
  calc _ = relM (eqP P' B Sw' E D).symm ∘ₗ (Φ.amplify ((B × Sw') × E) ∘ₗ
        ((U.amplifyLeft B).amplify E).amplifyLeft (P × D)) ∘ₗ relM (eqP P B Sw E D) := rfl
    _ = relM (eqP P' B Sw' E D).symm ∘ₗ (((U.amplifyLeft B).amplify E).amplifyLeft (P' × D) ∘ₗ
        Φ.amplify ((B × Sw) × E)) ∘ₗ relM (eqP P B Sw E D) := by
      rw [MatrixMap.amplify_comp_amplifyLeft]
    _ = _ := rfl

theorem actP_comp_actW_assoc [Finite P] [Finite D] {T : Type*} (Φ : MatrixMap (P × D) (P' × D))
    (U : MatrixMap Sw Sw') (L : MatrixMap T ((((P × B) × Sw) × E) × D)) :
    actP Φ B Sw' E ∘ₗ actW U (P × B) E D ∘ₗ L = actW U (P' × B) E D ∘ₗ actP Φ B Sw E ∘ₗ L := by
  rw [← LinearMap.comp_assoc, actP_comp_actW, LinearMap.comp_assoc]

theorem act0_comp_actQ [Finite Q] [Finite D] (V : MatrixMap S0 S0')
    (Ψ : MatrixMap (Q × D) (Q' × D)) :
    act0 V (Q' × F) E D ∘ₗ actQ Ψ S0 F E = actQ Ψ S0' F E ∘ₗ act0 V (Q × F) E D := by
  rw [act0_eq_amplifyLeft, act0_eq_amplifyLeft]
  calc _ = relM (eqQ S0' Q' F E D).symm ∘ₗ (((V.amplify F).amplify E).amplifyLeft (Q' × D) ∘ₗ
        Ψ.amplify ((S0 × F) × E)) ∘ₗ relM (eqQ S0 Q F E D) := rfl
    _ = relM (eqQ S0' Q' F E D).symm ∘ₗ (Ψ.amplify ((S0' × F) × E) ∘ₗ
        ((V.amplify F).amplify E).amplifyLeft (Q × D)) ∘ₗ relM (eqQ S0 Q F E D) := by
      rw [MatrixMap.amplify_comp_amplifyLeft]
    _ = _ := rfl

theorem act0_comp_actQ_assoc [Finite Q] [Finite D] {T : Type*} (V : MatrixMap S0 S0')
    (Ψ : MatrixMap (Q × D) (Q' × D)) (L : MatrixMap T (((S0 × (Q × F)) × E) × D)) :
    act0 V (Q' × F) E D ∘ₗ actQ Ψ S0 F E ∘ₗ L = actQ Ψ S0' F E ∘ₗ act0 V (Q × F) E D ∘ₗ L := by
  rw [← LinearMap.comp_assoc, act0_comp_actQ, LinearMap.comp_assoc]

/-- **The abstract commutation.** Embedding both parts, the two calls, projecting both parts is
embedding, calling and projecting the first part, then the second. -/
theorem batched_eq_interleaved {I I' W W' : Type*} [Finite I] [Finite P] [Finite P'] [Finite Q]
    [Finite D] [Finite B] (V0 : MatrixMap I (P × B)) (V0' : MatrixMap (P' × B) I')
    (Vw : MatrixMap W (Q × F)) (Vw' : MatrixMap (Q' × F) W') (Φ : MatrixMap (P × D) (P' × D))
    (Ψ : MatrixMap (Q × D) (Q' × D)) :
    act0 V0' W' E D ∘ₗ actW Vw' (P' × B) E D ∘ₗ actQ Ψ (P' × B) F E ∘ₗ actP Φ B (Q × F) E ∘ₗ
        act0 V0 (Q × F) E D ∘ₗ actW Vw I E D =
      actW Vw' I' E D ∘ₗ actQ Ψ I' F E ∘ₗ actW Vw I' E D ∘ₗ act0 V0' W E D ∘ₗ actP Φ B W E ∘ₗ
        act0 V0 W E D := by
  rw [act0_comp_actW V0 Vw, actP_comp_actW_assoc, act0_comp_actW_assoc,
    act0_comp_actQ_assoc, act0_comp_actW_assoc]

end parts

/-! ## The isometries slot by slot -/

section cores

/-- The entries of a basis map after a uniform preparation. -/
theorem basisMatrix_mul_prepUniform_apply {R Yp : Type} {O : Type*} [Fintype R] [DecidableEq R]
    [Fintype Yp] [DecidableEq O] (g : R × Yp → O) (o : O) (r : R) :
    (basisMatrix g * prepUniform R Yp) o r = ∑ y, if o = g (r, y) then uniformAmp Yp else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single r]
  · simp [prepUniform]
  · intro r' _ hr'
    simp [prepUniform, hr']
  · simp

theorem basisMatrix_equiv_mul_apply {l m n : Type*} [Fintype m] [DecidableEq l] (e : m ≃ l)
    (M : Matrix m n ℂ) (a : l) (b : n) : (basisMatrix e * M) a b = M (e.symm a) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm a)]
  · simp
  · intro c _ hc
    simp [show a ≠ e c from fun h ↦ hc (by simp [h])]
  · simp

theorem mul_basisMatrix_apply {l m n : Type*} [Fintype m] [DecidableEq m] (M : Matrix l m ℂ)
    (g : n → m) (a : l) (b : n) : (M * basisMatrix g) a b = M a (g b) := by
  simp [Matrix.mul_apply, basisMatrix_apply]

theorem mul_kronecker_one {l m n o : Type*} [Fintype m] [Fintype o] [DecidableEq o]
    (X : Matrix l m ℂ)
    (Y : Matrix m n ℂ) :
    (X * Y) ⊗ₖ (1 : Matrix o o ℂ) = (X ⊗ₖ (1 : Matrix o o ℂ)) * (Y ⊗ₖ (1 : Matrix o o ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- **A preparation beside a remainder** that the basis map carries along is the preparation
without the remainder, beside the identity on it. -/
theorem basisMatrix_mul_prepUniform_prod {R E Yp : Type} {O O' : Type*} [Fintype R]
    [DecidableEq R] [Fintype E] [DecidableEq E] [Fintype Yp] [Fintype O] [DecidableEq O]
    [DecidableEq O'] (g0 : R × Yp → O) (σ : O × E ≃ O') (g : (R × E) × Yp → O')
    (hg : ∀ r e y, g ((r, e), y) = σ (g0 (r, y), e)) :
    basisMatrix g * prepUniform (R × E) Yp =
      basisMatrix σ * ((basisMatrix g0 * prepUniform R Yp) ⊗ₖ (1 : Matrix E E ℂ)) := by
  ext o ⟨r, e⟩
  obtain ⟨⟨o₀, e₀⟩, rfl⟩ := σ.surjective o
  rw [basisMatrix_mul_prepUniform_apply, basisMatrix_equiv_mul_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, basisMatrix_mul_prepUniform_apply]
  simp only [hg, σ.injective.eq_iff, Prod.mk.injEq, Matrix.one_apply]
  by_cases h : e₀ = e
  · simp [h]
  · simp [h]

variable {Z Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  (τ : Equiv.Perm (Z × Bool))

/-- The basis map of one regrouped slot, without remainder. -/
def routeOne (p : (Z × Y) × Y) : (Z × (Y × Y)) × Bool :=
  (((τ (p.1.1, false)).1, placePair (τ (p.1.1, false)).2 p.1.2 p.2), (τ (p.1.1, false)).2)

/-- The basis map of `w` regrouped slots, without remainder. -/
def routeSlots (w : ℕ) (p : (Fin w → Z × Y) × (Fin w → Y)) :
    (Fin w → Z × (Y × Y)) × (Fin w → Bool) :=
  (fun i ↦ (routeOne τ (p.1 i, p.2 i)).1, fun i ↦ (routeOne τ (p.1 i, p.2 i)).2)

/-- The isometry of one regrouped slot, without remainder. -/
noncomputable def slotIso : Matrix ((Z × (Y × Y)) × Bool) (Z × Y) ℂ :=
  basisMatrix (routeOne (Y := Y) τ) * prepUniform (Z × Y) Y

/-- The isometry of `w` regrouped slots, without remainder. -/
noncomputable def slotsIso (w : ℕ) :
    Matrix ((Fin w → Z × (Y × Y)) × (Fin w → Bool)) (Fin w → Z × Y) ℂ :=
  basisMatrix (routeSlots (Y := Y) τ w) * prepUniform (Fin w → Z × Y) (Fin w → Y)

theorem regroupIso_eq (E : Type) [Fintype E] [DecidableEq E] :
    regroupIso (Y := Y) τ E =
      basisMatrix (Equiv.prodAssoc _ _ E) * (slotIso (Y := Y) τ ⊗ₖ (1 : Matrix E E ℂ)) :=
  basisMatrix_mul_prepUniform_prod (routeOne τ) _ _ fun _ _ _ ↦ rfl

theorem isoAll_eq (w : ℕ) (E : Type) [Fintype E] [DecidableEq E] :
    isoAll (Y := Y) τ w E =
      basisMatrix (Equiv.prodAssoc _ _ E) * (slotsIso (Y := Y) τ w ⊗ₖ (1 : Matrix E E ℂ)) :=
  basisMatrix_mul_prepUniform_prod (routeSlots τ w) _ _ fun _ _ _ ↦ rfl

theorem regroupIso_conjTranspose_eq (E : Type) [Fintype E] [DecidableEq E] :
    (regroupIso (Y := Y) τ E)ᴴ =
      ((slotIso (Y := Y) τ)ᴴ ⊗ₖ (1 : Matrix E E ℂ)) * (basisMatrix (Equiv.prodAssoc _ _ E))ᴴ := by
  rw [regroupIso_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

theorem isoAll_conjTranspose_eq (w : ℕ) (E : Type) [Fintype E] [DecidableEq E] :
    (isoAll (Y := Y) τ w E)ᴴ =
      ((slotsIso (Y := Y) τ w)ᴴ ⊗ₖ (1 : Matrix E E ℂ)) *
        (basisMatrix (Equiv.prodAssoc _ _ E))ᴴ := by
  rw [isoAll_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

omit [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
variable (Z Y) in
/-- The slots of a round of width zero. -/
def finZeroSlots : (Fin 0 → Z × Y) ≃ (Fin 0 → Z × (Y × Y)) × (Fin 0 → Bool) where
  toFun _ := (finZeroElim, finZeroElim)
  invFun _ := finZeroElim
  left_inv _ := funext fun i ↦ i.elim0
  right_inv _ := Prod.ext (funext fun i ↦ i.elim0) (funext fun i ↦ i.elim0)

/-- A round of width zero has nothing to regroup. -/
theorem slotsIso_zero : slotsIso (Y := Y) τ 0 = basisMatrix (finZeroSlots Z Y) := by
  have hamp : uniformAmp (Fin 0 → Y) = 1 := by simp [uniformAmp]
  ext o v
  rw [slotsIso, basisMatrix_mul_prepUniform_apply, basisMatrix_apply, Fintype.sum_unique,
    ite_eq_left (Subsingleton.elim _ _), ite_eq_left (Subsingleton.elim _ _), hamp]

/-- Splitting the first slot off a tuple of slots. -/
abbrev consSplit (X : Type) (w : ℕ) : (Fin (w + 1) → X) ≃ X × (Fin w → X) :=
  (Fin.consEquiv fun _ ↦ X).symm

/-- Joining the first regrouped slot to the others. -/
def slotJoin (X B : Type) (w : ℕ) : (X × B) × ((Fin w → X) × (Fin w → B)) ≃
    (Fin (w + 1) → X) × (Fin (w + 1) → B) where
  toFun p := (Fin.cons p.1.1 p.2.1, Fin.cons p.1.2 p.2.2)
  invFun q := ((q.1 0, q.2 0), (Fin.tail q.1, Fin.tail q.2))
  left_inv _ := rfl
  right_inv q := Prod.ext (Fin.cons_self_tail q.1) (Fin.cons_self_tail q.2)

omit [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
theorem routeSlots_cons (w : ℕ) (v : Fin (w + 1) → Z × Y) (y₀ : Y) (y : Fin w → Y) :
    routeSlots τ (w + 1) (v, Fin.cons y₀ y) =
      slotJoin _ _ w (routeOne τ (v 0, y₀), routeSlots τ w (Fin.tail v, y)) := by
  refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

omit [DecidableEq Y] in
theorem uniformAmp_succ (w : ℕ) :
    uniformAmp (Fin (w + 1) → Y) = uniformAmp Y * uniformAmp (Fin w → Y) := by
  have h : Fintype.card (Fin (w + 1) → Y) = Fintype.card Y * Fintype.card (Fin w → Y) := by
    rw [Fintype.card_congr (Fin.consEquiv fun _ ↦ Y).symm, Fintype.card_prod]
  rw [uniformAmp, uniformAmp, uniformAmp, h, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
    mul_inv, Complex.ofReal_mul]

/-- **The isometry of `w + 1` slots** is that of the first slot beside that of the others. -/
theorem slotsIso_succ (w : ℕ) :
    slotsIso (Y := Y) τ (w + 1) = basisMatrix (slotJoin _ _ w) *
      (slotIso (Y := Y) τ ⊗ₖ slotsIso (Y := Y) τ w) * basisMatrix (consSplit (Z × Y) w) := by
  ext o v
  obtain ⟨⟨o₁, o₂⟩, rfl⟩ := (slotJoin _ _ w).surjective o
  rw [mul_basisMatrix_apply, basisMatrix_equiv_mul_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, slotsIso, slotIso, slotsIso, basisMatrix_mul_prepUniform_apply,
    basisMatrix_mul_prepUniform_apply, basisMatrix_mul_prepUniform_apply, Finset.sum_mul_sum,
    ← (Fin.consEquiv fun _ ↦ Y).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y₀ _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  have h : routeSlots τ (w + 1) (v, (Fin.consEquiv fun _ ↦ Y) (y₀, y)) =
      slotJoin _ _ w (routeOne τ (v 0, y₀), routeSlots τ w (Fin.tail v, y)) :=
    routeSlots_cons τ w v y₀ y
  rw [h]
  simp only [(slotJoin _ _ w).injective.eq_iff, Prod.mk.injEq, uniformAmp_succ]
  change (if o₁ = routeOne τ (v 0, y₀) ∧ o₂ = routeSlots τ w (Fin.tail v, y) then _ else 0) =
    (if o₁ = routeOne τ (v 0, y₀) then _ else 0) *
      (if o₂ = routeSlots τ w (Fin.tail v, y) then _ else 0)
  by_cases h₁ : o₁ = routeOne τ (v 0, y₀) <;> by_cases h₂ : o₂ = routeSlots τ w (Fin.tail v, y) <;>
    simp [h₁, h₂]

/-- **The isometry of `w + 1` slots beside a remainder.** -/
theorem isoAll_succ_eq (w : ℕ) (E : Type) [Fintype E] [DecidableEq E] :
    isoAll (Y := Y) τ (w + 1) E =
      basisMatrix (((slotJoin _ _ w).prodCongr (Equiv.refl E)).trans (Equiv.prodAssoc _ _ E)) *
        ((slotIso (Y := Y) τ ⊗ₖ slotsIso (Y := Y) τ w) ⊗ₖ (1 : Matrix E E ℂ)) *
        basisMatrix ((consSplit (Z × Y) w).prodCongr (Equiv.refl E)) := by
  rw [isoAll_eq, slotsIso_succ, mul_kronecker_one, mul_kronecker_one, basisMatrix_kronecker_one,
    basisMatrix_kronecker_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← basisMatrix_comp]
  rfl

/-- **The adjoint of the isometry of `w + 1` slots beside a remainder.** -/
theorem isoAll_succ_conjTranspose (w : ℕ) (E : Type) [Fintype E] [DecidableEq E] :
    (isoAll (Y := Y) τ (w + 1) E)ᴴ =
      (basisMatrix ((consSplit (Z × Y) w).prodCongr (Equiv.refl E)))ᴴ *
        (((slotIso (Y := Y) τ)ᴴ ⊗ₖ (slotsIso (Y := Y) τ w)ᴴ) ⊗ₖ (1 : Matrix E E ℂ)) *
        (basisMatrix (((slotJoin _ _ w).prodCongr (Equiv.refl E)).trans
          (Equiv.prodAssoc _ _ E)))ᴴ := by
  rw [isoAll_succ_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.mul_assoc]

end cores

/-! ## Branches of the rounds -/

section branches

theorem branch_bind_unique {A : Type*} [Fintype A] {ι κ : Type*} [Unique ι] {Bf : ι → Type*}
    [∀ i, Fintype (Bf i)] {C : κ → Type*} [∀ c, Fintype (C c)] (p : DSubInstrument A ι Bf)
    (k : (i : ι) → DSubInstrument (Bf i) κ C) (c : κ) :
    (p.bind k).branch c = (k default).branch c ∘ₗ p.branch default := by
  rw [DSubInstrument.branch_bind_apply_univ, Fintype.sum_unique]

theorem branch_pure_unique {A : Type*} [Fintype A] {α : Type*} [Subsingleton α] (a b : α) :
    (SubInstrument.pure a : SubInstrument A A α).branch b = LinearMap.id := by
  rw [Subsingleton.elim b a]
  exact SubInstrument.branch_pure_self a

theorem branch_relabel_eq {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (u : Unit) : (relabel e).branch u = relM e :=
  LinearMap.ext (relabel_branch_apply e u)

theorem conj_basisMatrix_eq {A B : Type*} [Fintype A] [DecidableEq B] (e : A ≃ B) :
    MatrixMap.conj (basisMatrix e) = relM e :=
  LinearMap.ext (conj_basisMatrix_equiv e)

theorem conj_conjTranspose_basisMatrix {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) : MatrixMap.conj (basisMatrix e)ᴴ = relM e.symm := by
  classical
  rw [conjTranspose_basisMatrix_equiv, conj_basisMatrix_eq]

theorem amplify_relM {A B : Type*} (e : A ≃ B) (D : Type*) :
    (relM e).amplify D = relM (e.prodCongr (Equiv.refl D)) :=
  LinearMap.ext fun _ ↦ rfl

variable {Z Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Nonempty Y] {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  (τ : Equiv.Perm (Z × Bool))

instance : Unique ((recHwSpec (Y × Y) Z S M').Result (hPortR S M')) :=
  inferInstanceAs (Unique Unit)

omit [AddCommGroup Y] [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem batRoundR_branch (R : QuantumRuntime (recHwSpec (Y × Y) Z S M')) (w : ℕ) (E : QReg)
    {A B : QReg} (ℓ : A ≃ hRound Z Y w × E) (post : hRound Z Y w × E ≃ B) (rs : Fin w → Unit) :
    (R.run₂ .instruments (batRoundR S M' τ w E ℓ post)).branch rs =
      (MatrixMap.conj (basisMatrix post * (isoAll (Y := Y) τ w E)ᴴ)).amplify R.D ∘ₗ
        relM (QuantumRuntime.queryEquivOut
          (roundOut (recHwSpec (Y × Y) Z S M') (fun _ : Fin w ↦ hPortR S M')) R.D
          (QReg.of ((Fin w → Bool) × E))) ∘ₗ
        ((R.roundStep (fun _ : Fin w ↦ hPortR S M')).branch rs).amplify
          (QReg.of ((Fin w → Bool) × E)) ∘ₗ
        relM (QuantumRuntime.queryEquivIn (Equiv.refl _) R.D) ∘ₗ
        (MatrixMap.conj (isoAll (Y := Y) τ w E * basisMatrix ℓ)).amplify R.D := by
  have h : batRoundR S M' τ w E ℓ post = (QComp.act (embAll S M' τ w E ℓ)).bind fun _ ↦
      (seqCalls (spec := recHwSpec (Y × Y) Z S M') (fun _ : Fin w ↦ hPortR S M')
        (QReg.of ((Fin w → Bool) × E))
        (B := QReg.of (roundOut (recHwSpec (Y × Y) Z S M') (fun _ : Fin w ↦ hPortR S M') ×
          QReg.of ((Fin w → Bool) × E))) (Equiv.refl _) (Equiv.refl _)).bind fun _ ↦
        (QComp.act (projAll S M' τ w E post)).map fun _ ↦ (default : Fin w → Unit) := by
    unfold batRoundR
    congr 1
  obtain rfl : rs = default := Subsingleton.elim _ _
  rw [h, QuantumRuntime.run₂_act_bind]
  simp only [QuantumRuntime.run₂_bind, QuantumRuntime.run₂_seqCalls, QuantumRuntime.run₂_map,
    QuantumRuntime.run₂_act, SubInstrument.map_eq_bind_pure, SubInstrument.bind_assoc,
    SubInstrument.pure_bind]
  simp only [branch_bind_unique, DSubInstrument.branch_frame_apply, branch_relabel_eq,
    branch_pure_unique, embAll, projAll, SubInstrument.branch_ofMap, LinearMap.id_comp,
    LinearMap.comp_assoc]
  rfl

omit [Nonempty Y] [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem regRoundR_succ_branch (R : QuantumRuntime (recHwSpec (Y × Y) Z S M')) (w : ℕ)
    (E : QReg) {A B : QReg} (ℓ : A ≃ hRound Z Y (w + 1) × E)
    (post : hRound Z Y (w + 1) × E ≃ B)
    (rs : Fin (w + 1) → Unit) :
    (R.run₂ .instruments (regRoundR S M' τ E ℓ post)).branch rs =
      (R.run₂ .instruments (regRoundR S M' τ (QReg.of (QReg.of (Z × Y) × E))
          (seqShift (spec := qromSpec Z Y) (fun _ : Fin (w + 1) ↦ ()) E)
          (seqPost (spec := qromSpec Z Y) (fun _ : Fin (w + 1) ↦ ()) E post))).branch default ∘ₗ
        ((regroupProject.{0} τ (QReg.of (hRound Z Y w × E))).frame R.D).branch PUnit.unit ∘ₗ
        (R.queryStep (hPortR S M') (QReg.of (Bool × QReg.of (hRound Z Y w × E)))
          (A := QReg.of (QReg.of (Z × (Y × Y)) × QReg.of (Bool × QReg.of (hRound Z Y w × E))))
          (Equiv.refl _)).branch () ∘ₗ
        ((regroupEmbed.{0} τ (QReg.of (hRound Z Y w × E))
          (seqSplitIn (spec := qromSpec Z Y) (fun _ : Fin (w + 1) ↦ ()) E ℓ)).frame R.D).branch
          PUnit.unit := by
  obtain rfl : rs = default := Subsingleton.elim _ _
  rw [regRoundR, QuantumRuntime.run₂_primBind]
  simp only [branch_bind_unique, LocalSig.Interp.instruments_apply]
  erw [QuantumRuntime.run₂_queryBind]
  simp only [branch_bind_unique]
  erw [QuantumRuntime.run₂_primBind]
  simp only [branch_bind_unique, LocalSig.Interp.instruments_apply]
  erw [QuantumRuntime.run₂_map]
  simp only [SubInstrument.map_eq_bind_pure, branch_bind_unique, branch_pure_unique,
    LinearMap.id_comp, LinearMap.comp_assoc]
  rfl

omit [AddCommGroup Y] [Nonempty Y] [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem queryStep_branch_eq (R : QuantumRuntime (recHwSpec (Y × Y) Z S M'))
    (i : (recHwSpec (Y × Y) Z S M').Port) (E : QReg) {A : QReg}
    (ℓ : A ≃ (recHwSpec (Y × Y) Z S M').In i × E) (r : (recHwSpec (Y × Y) Z S M').Result i) :
    (R.queryStep i E ℓ).branch r =
      relM (QuantumRuntime.queryEquivOut ((recHwSpec (Y × Y) Z S M').Out i) R.D E) ∘ₗ
        ((R.step i).branch r).amplify E ∘ₗ relM (QuantumRuntime.queryEquivIn ℓ R.D) :=
  LinearMap.ext fun ρ ↦ by
    rw [QuantumRuntime.queryStep_branch_apply]
    simp only [relabel_branch_apply, DSubInstrument.branch_frame_apply]
    rfl

omit [AddCommGroup Y] [Nonempty Y] [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem roundStep_succ_branch (R : QuantumRuntime (recHwSpec (Y × Y) Z S M')) (w : ℕ)
    (rs : Fin (w + 1) → Unit) :
    (R.roundStep (fun _ : Fin (w + 1) ↦ hPortR S M')).branch rs =
      relM (R.roundJoin (fun _ : Fin (w + 1) ↦ hPortR S M')) ∘ₗ
        ((R.roundStep (fun _ : Fin w ↦ hPortR S M')).branch default).amplify
          ((recHwSpec (Y × Y) Z S M').Out (hPortR S M')) ∘ₗ
        relM (R.roundShift (fun _ : Fin (w + 1) ↦ hPortR S M')) ∘ₗ
        ((R.step (hPortR S M')).branch default).amplify
          (roundIn (recHwSpec (Y × Y) Z S M') (fun _ : Fin w ↦ hPortR S M')) ∘ₗ
        relM (R.roundSplit (fun _ : Fin (w + 1) ↦ hPortR S M')) := by
  obtain rfl : rs = default := Subsingleton.elim _ _
  rw [QuantumRuntime.roundStep_succ]
  erw [branch_bind_unique, branch_bind_unique, branch_bind_unique, branch_bind_unique,
    branch_bind_unique, branch_pure_unique]
  simp only [DSubInstrument.branch_frame_apply, branch_relabel_eq, LinearMap.id_comp,
    LinearMap.comp_assoc]

theorem conj_kronecker {A B C G : Type*} [Fintype A] [DecidableEq A] [Fintype B] [Fintype C]
    [Fintype G] [DecidableEq G] (X : Matrix B A ℂ) (W : Matrix G C ℂ) :
    MatrixMap.conj (X ⊗ₖ W) = (MatrixMap.conj X).amplify G ∘ₗ (MatrixMap.conj W).amplifyLeft A := by
  rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem conj_kronecker_one {A B G : Type*} [Fintype A] [Fintype B] [Fintype G] [DecidableEq G]
    (X : Matrix B A ℂ) : MatrixMap.conj (X ⊗ₖ (1 : Matrix G G ℂ)) = (MatrixMap.conj X).amplify G :=
  (MatrixMap.amplify_conj X).symm

/-- The relabelling into the canonical layout before the round. -/
def eIn (w : ℕ) (E : QReg) {A : QReg} (ℓ : A ≃ hRound Z Y (w + 1) × E) (D : Type) :
    A × D ≃ (((Z × Y) × (Fin w → Z × Y)) × E) × D :=
  (ℓ.trans ((consSplit (Z × Y) w).prodCongr (Equiv.refl E))).prodCongr (Equiv.refl D)

/-- The relabelling out of the canonical layout after the round. -/
def eOut (w : ℕ) (E : QReg) {B : QReg} (post : hRound Z Y (w + 1) × E ≃ B) (D : Type) :
    (((Z × Y) × (Fin w → Z × Y)) × E) × D ≃ B × D :=
  (((consSplit (Z × Y) w).prodCongr (Equiv.refl E)).symm.trans post).prodCongr (Equiv.refl D)

omit [AddCommGroup Y] [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem batRoundR_succ_branch (R : QuantumRuntime (recHwSpec (Y × Y) Z S M')) (w : ℕ)
    (E : QReg) {A B : QReg} (ℓ : A ≃ hRound Z Y (w + 1) × E) (post : hRound Z Y (w + 1) × E ≃ B)
    (rs : Fin (w + 1) → Unit) :
    (R.run₂ .instruments (batRoundR S M' τ (w + 1) E ℓ post)).branch rs =
      relM (eOut w E post R.D) ∘ₗ
        (act0 (MatrixMap.conj (slotIso (Y := Y) τ)ᴴ) (Fin w → Z × Y) E R.D ∘ₗ
          actW (MatrixMap.conj (slotsIso (Y := Y) τ w)ᴴ) ((Z × (Y × Y)) × Bool) E R.D ∘ₗ
          actQ ((R.roundStep (fun _ : Fin w ↦ hPortR S M')).branch default)
            ((Z × (Y × Y)) × Bool) (Fin w → Bool) E ∘ₗ
          actP ((R.step (hPortR S M')).branch default) Bool
            ((Fin w → Z × (Y × Y)) × (Fin w → Bool)) E ∘ₗ
          act0 (MatrixMap.conj (slotIso (Y := Y) τ))
            ((Fin w → Z × (Y × Y)) × (Fin w → Bool)) E R.D ∘ₗ
          actW (MatrixMap.conj (slotsIso (Y := Y) τ w)) (Z × Y) E R.D) ∘ₗ
        relM (eIn w E ℓ R.D) := by
  rw [batRoundR_branch, roundStep_succ_branch, isoAll_succ_conjTranspose, isoAll_succ_eq]
  simp only [MatrixMap.conj_mul, conj_basisMatrix_eq, conj_conjTranspose_basisMatrix,
    conj_kronecker_one]
  simp only [conj_kronecker, MatrixMap.amplify_comp, amplify_relM, LinearMap.comp_assoc]
  refine LinearMap.ext fun ρ ↦ ?_
  ext x y
  set_option maxRecDepth 20000 in rfl

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem interleaved_succ_branch (R : QuantumRuntime (recHwSpec (Y × Y) Z S M')) (w : ℕ)
    (E : QReg) {A B : QReg} (ℓ : A ≃ hRound Z Y (w + 1) × E) (post : hRound Z Y (w + 1) × E ≃ B) :
    (R.run₂ .instruments (batRoundR S M' τ w (QReg.of (QReg.of (Z × Y) × E))
          (seqShift (spec := qromSpec Z Y) (fun _ : Fin (w + 1) ↦ ()) E)
          (seqPost (spec := qromSpec Z Y) (fun _ : Fin (w + 1) ↦ ()) E post))).branch default ∘ₗ
        ((regroupProject.{0} τ (QReg.of (hRound Z Y w × E))).frame R.D).branch PUnit.unit ∘ₗ
        (R.queryStep (hPortR S M') (QReg.of (Bool × QReg.of (hRound Z Y w × E)))
          (A := QReg.of (QReg.of (Z × (Y × Y)) × QReg.of (Bool × QReg.of (hRound Z Y w × E))))
          (Equiv.refl _)).branch () ∘ₗ
        ((regroupEmbed.{0} τ (QReg.of (hRound Z Y w × E))
          (seqSplitIn (spec := qromSpec Z Y) (fun _ : Fin (w + 1) ↦ ()) E ℓ)).frame R.D).branch
          PUnit.unit =
      relM (eOut w E post R.D) ∘ₗ
        (actW (MatrixMap.conj (slotsIso (Y := Y) τ w)ᴴ) (Z × Y) E R.D ∘ₗ
          actQ ((R.roundStep (fun _ : Fin w ↦ hPortR S M')).branch default) (Z × Y)
            (Fin w → Bool) E ∘ₗ
          actW (MatrixMap.conj (slotsIso (Y := Y) τ w)) (Z × Y) E R.D ∘ₗ
          act0 (MatrixMap.conj (slotIso (Y := Y) τ)ᴴ) (Fin w → Z × Y) E R.D ∘ₗ
          actP ((R.step (hPortR S M')).branch default) Bool (Fin w → Z × Y) E ∘ₗ
          act0 (MatrixMap.conj (slotIso (Y := Y) τ)) (Fin w → Z × Y) E R.D) ∘ₗ
        relM (eIn w E ℓ R.D) := by
  rw [batRoundR_branch, isoAll_conjTranspose_eq, isoAll_eq]
  erw [queryStep_branch_eq]
  simp only [DSubInstrument.branch_frame_apply, regroupProject, regroupEmbed,
    SubInstrument.branch_ofMap]
  rw [regroupIso_conjTranspose_eq, regroupIso_eq]
  simp only [MatrixMap.conj_mul, conj_basisMatrix_eq, conj_conjTranspose_basisMatrix,
    conj_kronecker_one, MatrixMap.amplify_comp, amplify_relM, LinearMap.comp_assoc]
  refine LinearMap.ext fun ρ ↦ ?_
  ext x y
  set_option maxRecDepth 20000 in rfl

omit [AddCommGroup Y] [Nonempty Y] [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem roundStep_zero_branch (R : QuantumRuntime (recHwSpec (Y × Y) Z S M'))
    (rs : Fin 0 → Unit) :
    (R.roundStep (fun _ : Fin 0 ↦ hPortR S M')).branch rs =
      relM ((roundZeroEquiv (fun _ : Fin 0 ↦ hPortR S M')).prodCongr (Equiv.refl R.D)) := by
  rw [QuantumRuntime.roundStep_zero, SubInstrument.map_eq_bind_pure]
  erw [branch_bind_unique, branch_pure_unique, LinearMap.id_comp, branch_relabel_eq]

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
/-- **Width zero**: both rounds are the relabelling. -/
theorem roundsCommute_zero (R : QuantumRuntime (recHwSpec (Y × Y) Z S M')) (E : QReg)
    {A B : QReg} (ℓ : A ≃ hRound Z Y 0 × E) (post : hRound Z Y 0 × E ≃ B) :
    R.run₂ .instruments (regRoundR S M' τ E ℓ post) =
      R.run₂ .instruments (batRoundR S M' τ 0 E ℓ post) := by
  refine DSubInstrument.ext (funext fun rs ↦ ?_)
  rw [batRoundR_branch, roundStep_zero_branch, isoAll_conjTranspose_eq, isoAll_eq,
    slotsIso_zero, regRoundR, QuantumRuntime.run₂_act]
  simp only [SubInstrument.map_eq_bind_pure, SubInstrument.frame_bind, SubInstrument.frame_pure,
    SubInstrument.bind_assoc, SubInstrument.pure_bind, branch_bind_unique, branch_pure_unique,
    DSubInstrument.branch_frame_apply, branch_relabel_eq, LinearMap.id_comp, amplify_relM,
    MatrixMap.conj_mul, conj_basisMatrix_eq, conj_conjTranspose_basisMatrix, conj_kronecker_one,
    MatrixMap.amplify_comp, LinearMap.comp_assoc]
  refine LinearMap.ext fun ρ ↦ ?_
  ext x y
  set_option maxRecDepth 20000 in rfl

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
/-- **The interleaved and the batched rounds run alike** against every runtime. -/
theorem roundsCommute (R : QuantumRuntime (recHwSpec (Y × Y) Z S M')) :
    RoundsCommute S M' τ R := by
  intro w
  induction w with
  | zero => exact roundsCommute_zero τ R
  | succ w ih =>
    intro E A B ℓ post
    refine DSubInstrument.ext (funext fun rs ↦ ?_)
    rw [regRoundR_succ_branch, batRoundR_succ_branch]
    erw [ih]
    rw [interleaved_succ_branch]
    exact congrArg (fun T ↦ relM (eOut w E post R.D) ∘ₗ T ∘ₗ relM (eIn w E ℓ R.D))
      (batched_eq_interleaved _ _ _ _ _ _).symm

end branches

end Quantum.Qrom.Sphincs

end
