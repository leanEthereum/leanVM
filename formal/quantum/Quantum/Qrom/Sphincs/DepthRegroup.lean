module

public import Quantum.Qrom.Regroup
public import Quantum.Par.Spec
public import Quantum.Xmss.Assembly.Template

@[expose] public section

/-!
# Regrouped rounds of calls

leanSPHINCS's QROM chain answers each call of `H` by one call of the pair-valued `F` on a
regrouped register (`Qrom.regroupCalls`): the isometry `regroupEmbed`, the call of port `h`, the
contraction `regroupProject`. A round of `w` calls of `H` therefore runs, after the challenger, as
`w` such triples one after the other (`regRoundR`), while the depth-aware bounds need the `w`
calls of `h` adjacent, as a round. The batched form (`batRoundR`) embeds every slot first
(`embAll`, the product of the `w` isometries), makes the `w` calls of `h`, then projects every
slot back (`projAll`).

* `isoAll w E`: the product isometry of `w` regrouped slots beside the remainder `E`.
* `embAll`, `projAll`: the subinstruments before and after the batched calls.
* `regRoundR`, `batRoundR`: the interleaved and the batched round, over runtime 2's signature with
  record ports, port `h`.
* `RoundsCommute R`: the two rounds run alike against the runtime `R`.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Sphincs

open Quantum Quantum.Par Quantum.SubInstrument
open Quantum.Xmss.Assembly (recHwSpec)

variable {Z Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Nonempty Y] {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']

/-! ## The product isometry -/

section iso

variable (τ : Equiv.Perm (Z × Bool))

/-- The basis map of `w` regrouped slots beside the remainder `E` and the prepared registers
`y'`: slot `i` as `regroupRoute`, its flag in the flags' register. -/
def routeAll (w : ℕ) (E : Type) (p : ((Fin w → Z × Y) × E) × (Fin w → Y)) :
    (Fin w → Z × (Y × Y)) × ((Fin w → Bool) × E) :=
  (fun i ↦ ((τ ((p.1.1 i).1, false)).1, placePair (τ ((p.1.1 i).1, false)).2 (p.1.1 i).2 (p.2 i)),
    (fun i ↦ (τ ((p.1.1 i).1, false)).2, p.1.2))

omit [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty Y] in
theorem routeAll_injective (w : ℕ) (E : Type) :
    Function.Injective (routeAll (Y := Y) τ w E) := by
  rintro ⟨⟨v, e⟩, y'⟩ ⟨⟨v', e'⟩, z'⟩ h
  simp only [routeAll, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have hi : ∀ i, (v i, y' i) = (v' i, z' i) := fun i ↦ by
    have h := regroupRoute_injective (Y := Y) τ Unit
      (a₁ := (((v i), ()), y' i)) (a₂ := (((v' i), ()), z' i))
      (Prod.ext (congrFun h1 i) (Prod.ext (congrFun h2 i) rfl))
    simpa using h
  have hv : v = v' := funext fun i ↦ congrArg Prod.fst (hi i)
  have hy : y' = z' := funext fun i ↦ congrArg Prod.snd (hi i)
  subst hv hy
  rfl

/-- **The isometry of `w` regrouped slots**: prepare the `w` spare halves in the uniform
superposition, then route every slot. -/
noncomputable def isoAll (w : ℕ) (E : Type) [Fintype E] [DecidableEq E] :
    Matrix ((Fin w → Z × (Y × Y)) × ((Fin w → Bool) × E)) ((Fin w → Z × Y) × E) ℂ :=
  basisMatrix (routeAll τ w E) * prepUniform ((Fin w → Z × Y) × E) (Fin w → Y)

omit [AddCommGroup Y] in
theorem conjTranspose_isoAll_mul_self (w : ℕ) (E : Type) [Fintype E] [DecidableEq E] :
    (isoAll (Y := Y) τ w E)ᴴ * isoAll (Y := Y) τ w E = 1 := by
  rw [isoAll, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (basisMatrix (routeAll τ w E))ᴴ,
    conjTranspose_basisMatrix_mul_self (routeAll_injective τ w E), Matrix.one_mul,
    conjTranspose_prepUniform_mul_self]

omit [AddCommGroup Y] in
theorem posSemidef_one_sub_isoAll_mul (w : ℕ) (E : Type) [Fintype E] [DecidableEq E]
    {A : Type} [Fintype A] [DecidableEq A] (ℓ : A ≃ (Fin w → Z × Y) × E) :
    (1 - (isoAll (Y := Y) τ w E * basisMatrix ℓ)ᴴ *
      (isoAll (Y := Y) τ w E * basisMatrix ℓ)).PosSemidef := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (isoAll (Y := Y) τ w E)ᴴ, conjTranspose_isoAll_mul_self,
    Matrix.one_mul, conjTranspose_basisMatrix_mul_self ℓ.injective, sub_self]
  exact Matrix.PosSemidef.zero

omit [AddCommGroup Y] in
theorem basisMatrix_mul_isoAll_conjTranspose (w : ℕ) (E : Type) [Fintype E] [DecidableEq E]
    {B : Type} [Fintype B] [DecidableEq B] (post : (Fin w → Z × Y) × E ≃ B) :
    basisMatrix post * (isoAll (Y := Y) τ w E)ᴴ *
      (basisMatrix post * (isoAll (Y := Y) τ w E)ᴴ)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (isoAll (Y := Y) τ w E)ᴴ, conjTranspose_isoAll_mul_self,
    Matrix.one_mul, conjTranspose_basisMatrix_equiv, ← basisMatrix_comp]
  simp

end iso

/-! ## The rounds -/

section rounds

variable (S M') (τ : Equiv.Perm (Z × Bool))

/-- Port `h` of runtime 2 with record ports. -/
abbrev hPortR : (recHwSpec (Y × Y) Z S M').Port :=
  .inl (.inl (.inl .h))

/-- The register of a round of `H`: `w` inputs of `H`. -/
abbrev hRound (Z Y : Type) [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] (w : ℕ) :
    QReg :=
  roundIn (qromSpec Z Y) (fun _ : Fin w ↦ ())

/-- **Before the batched calls**: the isometry of every slot, after the relabelling `ℓ`. -/
noncomputable def embAll (w : ℕ) (E : QReg) {A : QReg} (ℓ : A ≃ hRound Z Y w × E) :
    SubInstrument A (QReg.of (roundIn (recHwSpec (Y × Y) Z S M') (fun _ : Fin w ↦ hPortR S M') ×
      QReg.of ((Fin w → Bool) × E))) PUnit :=
  SubInstrument.ofMap (MatrixMap.conj (isoAll (Y := Y) τ w E * basisMatrix ℓ))
    (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (posSemidef_one_sub_isoAll_mul τ w E ℓ))

/-- **After the batched calls**: the adjoint of the isometry of every slot, then the relabelling
`post`. -/
noncomputable def projAll (w : ℕ) (E : QReg) {B : QReg} (post : hRound Z Y w × E ≃ B) :
    SubInstrument (QReg.of (roundOut (recHwSpec (Y × Y) Z S M') (fun _ : Fin w ↦ hPortR S M') ×
      QReg.of ((Fin w → Bool) × E))) B PUnit :=
  SubInstrument.ofMap (MatrixMap.conj (basisMatrix post * (isoAll (Y := Y) τ w E)ᴴ))
    (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (posSemidef_one_sub_conjTranspose_mul_self
      (basisMatrix_mul_isoAll_conjTranspose τ w E post)))

/-- **The batched round**: every slot embedded, the `w` calls of `h` in order on the regrouped
inputs, every slot projected back along `post`. -/
noncomputable def batRoundR (w : ℕ) (E : QReg) {A B : QReg} (ℓ : A ≃ hRound Z Y w × E)
    (post : hRound Z Y w × E ≃ B) :
    QComp (recHwSpec (Y × Y) Z S M') A B (Fin w → Unit) :=
  (QComp.act (embAll S M' τ w E ℓ)).bind fun _ ↦
    (seqCalls (spec := recHwSpec (Y × Y) Z S M') (fun _ : Fin w ↦ hPortR S M')
      (QReg.of ((Fin w → Bool) × E))
      (B := QReg.of (roundOut (recHwSpec (Y × Y) Z S M') (fun _ : Fin w ↦ hPortR S M') ×
        QReg.of ((Fin w → Bool) × E))) (Equiv.refl _) (Equiv.refl _)).bind fun rs ↦
      (QComp.act (projAll S M' τ w E post)).map fun _ ↦ rs

/-- **The interleaved round**: the `w` calls of `H` on the components exposed by `ℓ`, each as
`regroupEmbed`, the call of `h`, `regroupProject`, in order (as `seqCalls`), the outputs
relabelled along `post` at the end. -/
noncomputable def regRoundR : {w : ℕ} → (E : QReg) → {A B : QReg} →
    (ℓ : A ≃ hRound Z Y w × E) → (post : roundOut (qromSpec Z Y) (fun _ : Fin w ↦ ()) × E ≃ B) →
    QComp (recHwSpec (Y × Y) Z S M') A B (Fin w → Unit)
  | 0, E, _, _, ℓ, post =>
    QComp.act ((relabel (ℓ.trans (((roundZeroEquiv (spec := qromSpec Z Y)
      (fun _ : Fin 0 ↦ ())).prodCongr (Equiv.refl E)).trans post))).map
        fun _ ↦ (finZeroElim : Fin 0 → Unit))
  | w + 1, E, _, _, ℓ, post =>
    QuantumComp₂.primBind (L := LocalSig.instruments)
      ⟨PUnit, fun _ ↦ QReg.of (QReg.of (Z × (Y × Y)) ×
        QReg.of (Bool × QReg.of (hRound Z Y w × E))),
        regroupEmbed τ (QReg.of (hRound Z Y w × E))
          (seqSplitIn (spec := qromSpec Z Y) (fun _ : Fin (w + 1) ↦ ()) E ℓ)⟩ fun _ ↦
    QuantumComp₂.queryBind (hPortR S M') (QReg.of (Bool × QReg.of (hRound Z Y w × E)))
      (Equiv.refl _) fun _ ↦
    QuantumComp₂.primBind (L := LocalSig.instruments)
      ⟨PUnit, fun _ ↦ QReg.of (QReg.of (Z × Y) × QReg.of (hRound Z Y w × E)),
        regroupProject τ (QReg.of (hRound Z Y w × E))⟩ fun _ ↦
    (regRoundR (QReg.of (QReg.of (Z × Y) × E))
      (seqShift (spec := qromSpec Z Y) (fun _ : Fin (w + 1) ↦ ()) E)
      (seqPost (spec := qromSpec Z Y) (fun _ : Fin (w + 1) ↦ ()) E post)).map (Fin.cons ())

/-- **The interleaved and the batched rounds run alike** against `R`, for every width, remainder
and relabellings. -/
def RoundsCommute (R : QuantumRuntime (recHwSpec (Y × Y) Z S M')) : Prop :=
  ∀ (w : ℕ) (E : QReg) {A B : QReg} (ℓ : A ≃ hRound Z Y w × E) (post : hRound Z Y w × E ≃ B),
    R.run₂ .instruments (regRoundR S M' τ E ℓ post) =
      R.run₂ .instruments (batRoundR S M' τ w E ℓ post)

end rounds

end Quantum.Qrom.Sphincs

end
