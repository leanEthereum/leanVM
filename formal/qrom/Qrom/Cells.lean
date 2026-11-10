module

public import Qrom.Assembly

@[expose] public section

/-!
# Search for a predicate on several hash values

`Qrom.OvGame.search_withVerifier_le` bounds the probability of reading an input `z` with
`good z (G z)`, a predicate on one hash value. Here the inputs are grouped into cells: an
injection `cellOf : X → C × K` places each input at a component of a cell, and `good c v` reads the
whole value `v : K → Y` of the cell `c`. The oracle on `X` is simulated by one on cells,
`G' : C → K → Y`, read back by `Qrom.unpair`: a call on `|x, z⟩` with `cellOf x = (c, k)`
becomes one call on `|c, w⟩`, where `w` holds `z` at the component `k` and the uniform
superposition at every other component, which no addition changes (`Qrom.cellIso`). The
translation `Qrom.OvGame.cellCalls` runs as the original program (`Qrom.OvGame.run_cellCalls`) and
keeps the call budget, so the one-cell bound for the game on cells gives the bound with
`λ = sb / |K → Y|` (`Qrom.OvGame.search_withVerifier_cells_le`).
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

variable {X Y C K : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K]

/-- The function on inputs read off a function on cells. -/
def unpair (cellOf : X → C × K) (G' : C → K → Y) : X → Y :=
  fun x ↦ G' (cellOf x).1 (cellOf x).2

/-! ## The isometry into a cell -/

section iso

/-- The number of cell values with the value `z` at the component `k`. -/
noncomputable def compCount (k : K) (z : Y) : ℕ :=
  Fintype.card {w : K → Y // w k = z}

theorem compCount_add (k : K) (z a : Y) : compCount k (z + a) = compCount k z :=
  (Fintype.card_congr (Equiv.subtypeEquiv (Equiv.addRight fun _ ↦ a) fun w ↦ by simp)).symm

theorem compCount_pos (k : K) (z : Y) : 0 < compCount k z :=
  Fintype.card_pos_iff.mpr ⟨⟨fun _ ↦ z, rfl⟩⟩

/-- The amplitude of each cell value with the value `z` at the component `k`. -/
noncomputable def ancAmp (k : K) (z : Y) : ℂ :=
  ((Real.sqrt (compCount k z))⁻¹ : ℝ)

theorem star_ancAmp (k : K) (z : Y) : star (ancAmp k z) = ancAmp k z :=
  Complex.conj_ofReal _

theorem ancAmp_mul_self (k : K) (z : Y) : ancAmp k z * ancAmp k z = (compCount k z : ℂ)⁻¹ := by
  rw [ancAmp, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

theorem ancAmp_add (k : K) (z a : Y) : ancAmp k (z + a) = ancAmp k z := by
  rw [ancAmp, ancAmp, compCount_add]

/-- The isometry that moves an input into its cell: `|x, z⟩|f⟩` goes to the uniform superposition
of `|c, w⟩|k, f⟩` over the cell values `w` with `w k = z`, for `cellOf x = (c, k)`. The other
components of `w` hold the uniform superposition. -/
noncomputable def cellIso (cellOf : X → C × K) (F : Type) [DecidableEq F] :
    Matrix ((C × (K → Y)) × (K × F)) ((X × Y) × F) ℂ :=
  Matrix.of fun r q ↦ if (r.1.1, r.2.1) = cellOf q.1.1 ∧ r.2.2 = q.2 ∧ r.1.2 r.2.1 = q.1.2 then
    ancAmp (cellOf q.1.1).2 q.1.2 else 0

theorem cellIso_apply (cellOf : X → C × K) (F : Type) [DecidableEq F] (c : C) (w : K → Y) (k : K)
    (f' : F) (x : X) (z : Y) (f : F) :
    cellIso cellOf F ((c, w), (k, f')) ((x, z), f) =
      if (c, k) = cellOf x ∧ f' = f ∧ w k = z then ancAmp (cellOf x).2 z else 0 :=
  rfl

/-- The cell values that `cellIso` reaches from one input. -/
def cellFiberEquiv (cellOf : X → C × K) (F : Type) (x : X) (z : Y) (f : F) :
    {r : (C × (K → Y)) × (K × F) // (r.1.1, r.2.1) = cellOf x ∧ r.2.2 = f ∧ r.1.2 r.2.1 = z} ≃
      {w : K → Y // w (cellOf x).2 = z} where
  toFun r := ⟨r.1.1.2, by
    obtain ⟨h1, -, h3⟩ := r.2
    rw [← congrArg Prod.snd h1]
    exact h3⟩
  invFun w := ⟨(((cellOf x).1, w.1), ((cellOf x).2, f)), rfl, rfl, w.2⟩
  left_inv := by
    rintro ⟨⟨⟨c, w⟩, k, f'⟩, h1, h2, -⟩
    refine Subtype.ext ?_
    simp only at h1 h2
    subst h2
    show (((cellOf x).1, w), ((cellOf x).2, f')) = ((c, w), (k, f'))
    rw [← h1]
  right_inv _ := rfl

variable (Y) in
theorem conjTranspose_cellIso_mul_self {cellOf : X → C × K} (hinj : Function.Injective cellOf)
    (F : Type) [Fintype F] [DecidableEq F] :
    (cellIso (Y := Y) cellOf F)ᴴ * cellIso (Y := Y) cellOf F = 1 := by
  ext ⟨⟨x, z⟩, f⟩ ⟨⟨x', z'⟩, f'⟩
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hq : ((x, z), f) = ((x', z'), f')
  · rw [ite_eq_left hq]
    simp only [Prod.mk.injEq] at hq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hq
    have hterm : ∀ r : (C × (K → Y)) × (K × F),
        (cellIso cellOf F)ᴴ ((x, z), f) r * cellIso cellOf F r ((x, z), f) =
          if (r.1.1, r.2.1) = cellOf x ∧ r.2.2 = f ∧ r.1.2 r.2.1 = z then
            (compCount (cellOf x).2 z : ℂ)⁻¹ else 0 := by
      intro r
      simp only [conjTranspose_apply, cellIso, of_apply]
      split_ifs
      · rw [star_ancAmp, ancAmp_mul_self]
      · rw [star_zero, zero_mul]
    simp only [hterm]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype,
      Fintype.card_congr (cellFiberEquiv cellOf F x z f)]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (compCount_pos _ _).ne')
  · rw [ite_eq_right hq]
    refine Finset.sum_eq_zero fun r _ ↦ ?_
    simp only [conjTranspose_apply, cellIso, of_apply]
    by_cases h1 : (r.1.1, r.2.1) = cellOf x ∧ r.2.2 = f ∧ r.1.2 r.2.1 = z
    · by_cases h2 : (r.1.1, r.2.1) = cellOf x' ∧ r.2.2 = f' ∧ r.1.2 r.2.1 = z'
      · refine absurd ?_ hq
        rw [hinj (h1.1.symm.trans h2.1), ← h1.2.1, h2.2.1, ← h1.2.2, h2.2.2]
      · rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, star_zero, zero_mul]

end iso

/-! ## Calls through the cell oracle -/

section embed

variable {cellOf : X → C × K} (hinj : Function.Injective cellOf)

/-- Before a hash call made through the cell oracle: the isometry `cellIso` after `ℓ`. -/
noncomputable def cellEmbed (F : QReg) {A : QReg} (ℓ : A ≃ (X × Y) × F) :
    SubInstrument A ((C × (K → Y)) × QReg.of (K × F)) PUnit.{v + 1} :=
  SubInstrument.ofMap (MatrixMap.conj (cellIso cellOf F * basisMatrix ℓ)) (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cellIso cellOf F)ᴴ,
        conjTranspose_cellIso_mul_self Y hinj, Matrix.one_mul,
        conjTranspose_basisMatrix_mul_self ℓ.injective, sub_self]
      exact PosSemidef.zero))

/-- After a hash call made through the cell oracle: the contraction that reads the input back. -/
noncomputable def cellProject (F : QReg) :
    SubInstrument ((C × (K → Y)) × QReg.of (K × F)) ((X × Y) × F) PUnit.{v + 1} :=
  SubInstrument.ofMap (MatrixMap.conj (cellIso cellOf F)ᴴ) (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (posSemidef_one_sub_conjTranspose_mul_self (by
      rw [conjTranspose_conjTranspose]
      exact conjTranspose_cellIso_mul_self Y hinj F)))

end embed

/-! ## Averaging over functions on cells -/

/-- The average over functions on cells of a quantity read through `unpair` is its average over
functions on inputs: `unpair` is onto, with fibers of equal size, since `cellOf` is injective. -/
theorem sum_unpair [Nonempty Y] {cellOf : X → C × K} (hinj : Function.Injective cellOf)
    (Φ : (X → Y) → ℝ≥0∞) :
    ∑ G' : C → K → Y, (Fintype.card (C → K → Y) : ℝ≥0∞)⁻¹ * Φ (unpair cellOf G') =
      ∑ G : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * Φ G := by
  classical
  let R := {p : C × K // p ∉ Set.range cellOf}
  let e : (C → K → Y) ≃ (X → Y) × (R → Y) :=
    (Equiv.curry C K Y).symm.trans
      ((Equiv.piEquivPiSubtypeProd (· ∈ Set.range cellOf) fun _ ↦ Y).trans
        (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective cellOf hinj).symm (Equiv.refl Y))
          (Equiv.refl _)))
  have hsum : ∑ G' : C → K → Y, Φ (unpair cellOf G') = ∑ q : (X → Y) × (R → Y), Φ q.1 :=
    e.sum_comp fun q ↦ Φ q.1
  have hcard : Fintype.card (C → K → Y) = Fintype.card (X → Y) * Fintype.card (R → Y) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hR : (Fintype.card (R → Y) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc, hcard, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inr hR),
    mul_assoc _ (Fintype.card (R → Y) : ℝ≥0∞)⁻¹,
    ENNReal.inv_mul_cancel hR (ENNReal.natCast_ne_top _), mul_one]

namespace OvGame

variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]

/-- The game on cells: the initial side state and the transitions of `g`, with the overrides
`ov'` of whole cells. -/
def cellGame (g : OvGame X Y S P Res) (ov' : S → C → Option (K → Y)) :
    OvGame C (K → Y) S P Res where
  init := g.init
  ov := ov'
  trans := g.trans

/-- The input of a call of the cell oracle beside the rest `K × F`. -/
def cellSplit (F : QReg) :
    QReg.of ((C × (K → Y)) × QReg.of (K × F)) ≃
      (ovSpec C (K → Y) S P Res).In (.inl ()) × QReg.of (K × F) :=
  Equiv.refl _

variable {cellOf : X → C × K} (hinj : Function.Injective cellOf)

/-- Each command of a program on inputs, as a program on cells: a hash call goes through
`cellEmbed`, the cell oracle and `cellProject`; side calls and local operations are kept. -/
noncomputable def cellSubst :
    IPFunctor.CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{v} (ovSpec X Y S P Res))
      (QuantumComp.toIPFunctor LocalSig.instruments.{v} (ovSpec C (K → Y) S P Res))
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (.inl _) F ℓ =>
      QuantumComp.primBind (L := LocalSig.instruments.{v})
        ⟨PUnit, fun _ ↦ QReg.of ((C × (K → Y)) × QReg.of (K × F)), cellEmbed hinj F ℓ⟩
        fun _ ↦ QuantumComp.queryBind (A := QReg.of ((C × (K → Y)) × QReg.of (K × F)))
          (spec := ovSpec C (K → Y) S P Res) (.inl ()) (QReg.of (K × F)) (cellSplit F) fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{v})
            ⟨PUnit, fun _ ↦ QReg.of ((ovSpec X Y S P Res).Out (.inl ()) × F), cellProject hinj F⟩
            fun _ ↦ QuantumComp.pure ⟨ULift.up (), rfl⟩
  | _, .query (.inr j) F ℓ =>
      QuantumComp.queryBind (spec := ovSpec C (K → Y) S P Res) (.inr j) F ℓ fun r ↦
        QuantumComp.pure ⟨ULift.up r, rfl⟩

/-- **Calls through the cell oracle.** The program on cells that simulates a program on inputs. -/
noncomputable def cellCalls {W : QReg → Type w} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (ovSpec X Y S P Res) W A) :
    QuantumComp LocalSig.instruments.{v} (ovSpec C (K → Y) S P Res) W A :=
  IPFunctor.IFreeM.substitute (cellSubst hinj) x

variable {W : QReg → Type w}

theorem cellCalls_primBind {A : QReg} (o : LocalSig.instruments.{v}.Op A)
    (k : (b : LocalSig.instruments.{v}.Outcome o) →
      QuantumComp LocalSig.instruments.{v} (ovSpec X Y S P Res) W
        (LocalSig.instruments.{v}.next o b)) :
    cellCalls hinj (QuantumComp.primBind o k) =
      QuantumComp.primBind o fun b ↦ cellCalls hinj (k b) :=
  rfl

theorem cellCalls_queryBind_inl {A : QReg} (F : QReg)
    (ℓ : A ≃ (ovSpec X Y S P Res).In (.inl ()) × F)
    (k : (ovSpec X Y S P Res).Result (.inl ()) →
      QuantumComp LocalSig.instruments.{v} (ovSpec X Y S P Res) W
        (QReg.of ((ovSpec X Y S P Res).Out (.inl ()) × F))) :
    cellCalls hinj (QuantumComp.queryBind (.inl ()) F ℓ k) =
      QuantumComp.primBind (L := LocalSig.instruments.{v})
        ⟨PUnit, fun _ ↦ QReg.of ((C × (K → Y)) × QReg.of (K × F)), cellEmbed hinj F ℓ⟩
        fun _ ↦ QuantumComp.queryBind (A := QReg.of ((C × (K → Y)) × QReg.of (K × F)))
          (spec := ovSpec C (K → Y) S P Res) (.inl ()) (QReg.of (K × F)) (cellSplit F) fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{v})
            ⟨PUnit, fun _ ↦ QReg.of ((ovSpec X Y S P Res).Out (.inl ()) × F), cellProject hinj F⟩
            fun _ ↦ cellCalls hinj (k ()) :=
  rfl

theorem cellCalls_queryBind_inr {A : QReg} (j : P) (F : QReg)
    (ℓ : A ≃ (ovSpec X Y S P Res).In (.inr j) × F)
    (k : (ovSpec X Y S P Res).Result (.inr j) →
      QuantumComp LocalSig.instruments.{v} (ovSpec X Y S P Res) W
        (QReg.of ((ovSpec X Y S P Res).Out (.inr j) × F))) :
    cellCalls hinj (QuantumComp.queryBind (.inr j) F ℓ k) =
      QuantumComp.queryBind (spec := ovSpec C (K → Y) S P Res) (.inr j) F ℓ fun r ↦
        cellCalls hinj (k r) :=
  rfl

/-- **The translation keeps the call budget.** -/
theorem isTotalQueryBound_cellCalls {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} (ovSpec X Y S P Res) W A} {n : ℕ}
    (hx : x.IsTotalQueryBound n) : (cellCalls hinj x).IsTotalQueryBound n := by
  refine IPFunctor.IFreeM.IsChargeBound.substitute (cellSubst hinj) (fun A c ↦ ?_) hx
  change QuantumComp.IsTotalQueryBound (cellSubst hinj A c) (QuantumComp.Cmd.queryCharge c)
  cases c with
  | prim o => simp [cellSubst, QuantumComp.Cmd.queryCharge]
  | query i F ℓ =>
    rcases i with ⟨⟩ | j
    · refine (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ ?_
      refine (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr ⟨Nat.one_pos, fun _ ↦ ?_⟩
      exact (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦
        QuantumComp.isTotalQueryBound_pure _ _
    · exact (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _⟩

/-! ## The calls through the cell oracle run as the original calls -/

section run

variable (g : OvGame X Y S P Res) (ov' : S → C → Option (K → Y))
  (hov : ∀ s x, g.ov s x = (ov' s (cellOf x).1).map fun v ↦ v (cellOf x).2)

include hov in
/-- The hash read off a function on cells is the component of the cell hash. -/
theorem answer_unpair (G' : C → K → Y) (s : S) (x : X) :
    g.answer s (unpair cellOf G') x = (cellGame g ov').answer s G' (cellOf x).1 (cellOf x).2 := by
  simp only [answer, cellGame, hov]
  cases ov' s (cellOf x).1 <;> rfl

/-- The basis permutation of a call of the cell oracle, regrouped beside the rest `K × F`. -/
def cellCallEquiv (G' : C → K → Y) (F : Type) :
    ((C × (K → Y)) × (K × F)) × (S × Unit) ≃ ((C × (K → Y)) × (K × F)) × (S × Unit) :=
  (QuantumRuntime.queryEquivIn (Equiv.refl ((C × (K → Y)) × (K × F))) (S × Unit)).trans
    ((Equiv.prodCongr (tableOracleEquiv fun t : S × Unit ↦ (cellGame g ov').answer t.1 G')
      (Equiv.refl (K × F))).trans (QuantumRuntime.queryEquivOut (C × (K → Y)) (S × Unit) (K × F)))

/-- The basis map of a hash call on inputs, regrouped beside the rest `F`. -/
def inputCallMap (G : X → Y) (F : Type) :
    ((X × Y) × F) × (S × Unit) → ((X × Y) × F) × (S × Unit) :=
  fun q ↦ (((q.1.1.1, q.1.1.2 + g.answer q.2.1 G q.1.1.1), q.1.2), q.2)

omit [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C] in
theorem basisMatrix_equiv_mul_apply {l m n : Type*} [Fintype m] [DecidableEq n] (e : m ≃ n)
    (M : Matrix m l ℂ) (i : n) (j : l) : (basisMatrix e * M) i j = M (e.symm i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm i)]
  · simp
  · intro b _ hb
    rw [basisMatrix_apply, ite_eq_right fun h ↦ hb (by rw [h, Equiv.symm_apply_apply]), zero_mul]
  · simp

include hov in
/-- A call of the cell oracle on the image of `cellIso` is the image of the hash call. -/
theorem cellCallEquiv_mul_cellIso (G' : C → K → Y) (F : Type) [Fintype F] [DecidableEq F] :
    basisMatrix (cellCallEquiv g ov' G' F) *
        (cellIso cellOf F ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ)) =
      (cellIso cellOf F ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ)) *
        basisMatrix (inputCallMap g (unpair cellOf G') F) := by
  ext i j
  obtain ⟨i, rfl⟩ := (cellCallEquiv g ov' G' F).surjective i
  rw [basisMatrix_equiv_mul_apply, Equiv.symm_apply_apply, mul_basisMatrix_apply]
  obtain ⟨⟨⟨c, w⟩, k, f'⟩, d'⟩ := i
  obtain ⟨⟨⟨x, z⟩, f⟩, d⟩ := j
  simp only [cellCallEquiv, inputCallMap, Equiv.trans_apply, QuantumRuntime.queryEquivIn_apply,
    QuantumRuntime.queryEquivOut_apply, Equiv.prodCongr_apply, Prod.map, tableOracleEquiv_apply,
    oracleEquiv_apply, Equiv.refl_apply, kroneckerMap_apply, cellIso_apply, Matrix.one_apply]
  by_cases hd : d' = d
  · subst hd
    by_cases hc : (c, k) = cellOf x
    · have hH : g.answer d'.1 (unpair cellOf G') x = (cellGame g ov').answer d'.1 G' c k := by
        rw [answer_unpair g ov' hov, ← hc]
      simp only [hH, Pi.add_apply, add_left_inj, ancAmp_add]
    · simp [hc]
  · simp [hd]

include hov hinj in
/-- The matrix identity behind a hash call made through the cell oracle. -/
theorem cellCall_matrix (G' : C → K → Y) (F : Type) [Fintype F] [DecidableEq F] {A : Type}
    [Fintype A] [DecidableEq A] (ℓ : A ≃ (X × Y) × F) :
    ((cellIso cellOf F)ᴴ ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ)) *
        (basisMatrix (QuantumRuntime.queryEquivOut (C × (K → Y)) (S × Unit) (K × F)) *
          (tableOracle (fun t : S × Unit ↦ (cellGame g ov').answer t.1 G') ⊗ₖ
            (1 : Matrix (K × F) (K × F) ℂ)) *
          basisMatrix (QuantumRuntime.queryEquivIn (Equiv.refl ((C × (K → Y)) × (K × F)))
            (S × Unit))) *
        ((cellIso cellOf F * basisMatrix ℓ) ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ)) =
      basisMatrix (QuantumRuntime.queryEquivOut (X × Y) (S × Unit) F) *
        (tableOracle (fun t : S × Unit ↦ g.answer t.1 (unpair cellOf G')) ⊗ₖ
          (1 : Matrix F F ℂ)) * basisMatrix (QuantumRuntime.queryEquivIn ℓ (S × Unit)) := by
  set V := cellIso (Y := Y) cellOf F ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ)
  have hQ' : basisMatrix (QuantumRuntime.queryEquivOut (C × (K → Y)) (S × Unit) (K × F)) *
      (tableOracle (fun t : S × Unit ↦ (cellGame g ov').answer t.1 G') ⊗ₖ
        (1 : Matrix (K × F) (K × F) ℂ)) *
      basisMatrix (QuantumRuntime.queryEquivIn (Equiv.refl ((C × (K → Y)) × (K × F))) (S × Unit)) =
      basisMatrix (cellCallEquiv g ov' G' F) := by
    rw [tableOracle, basisMatrix_kronecker_one, ← basisMatrix_comp, ← basisMatrix_comp]
    rfl
  have hQ : basisMatrix (QuantumRuntime.queryEquivOut (X × Y) (S × Unit) F) *
      (tableOracle (fun t : S × Unit ↦ g.answer t.1 (unpair cellOf G')) ⊗ₖ (1 : Matrix F F ℂ)) *
      basisMatrix (QuantumRuntime.queryEquivIn ℓ (S × Unit)) =
      basisMatrix (inputCallMap g (unpair cellOf G') F) *
        (basisMatrix ℓ ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ)) := by
    rw [tableOracle, basisMatrix_kronecker_one, basisMatrix_kronecker_one, ← basisMatrix_comp,
      ← basisMatrix_comp, ← basisMatrix_comp]
    rfl
  have h1 : (cellIso cellOf F * basisMatrix ℓ) ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ) =
      V * (basisMatrix ℓ ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ)) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
  have h2 : (cellIso cellOf F)ᴴ ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ) = Vᴴ := by
    rw [conjTranspose_kronecker, conjTranspose_one]
  have hiso : Vᴴ * V = 1 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      conjTranspose_cellIso_mul_self Y hinj, Matrix.one_mul, one_kronecker_one]
  rw [hQ', hQ, h1, h2, ← Matrix.mul_assoc, Matrix.mul_assoc Vᴴ, cellCallEquiv_mul_cellIso g ov' hov,
    ← Matrix.mul_assoc, hiso, Matrix.one_mul]

include hov in
/-- **One hash call through the cell oracle.** Embedding the input into its cell, calling the cell
oracle and projecting back is the hash call. -/
theorem branch_cellProject_comp_queryStep_comp_cellEmbed (G' : C → K → Y) (F : QReg) {A : QReg}
    (ℓ : A ≃ (X × Y) × F) :
    ((cellProject.{v} hinj F).frame (S × Unit)).branch PUnit.unit ∘ₗ
      ((((cellGame g ov').sampled G').queryStep (A := QReg.of ((C × (K → Y)) × QReg.of (K × F)))
          (.inl ()) (QReg.of (K × F)) (cellSplit F)).branch () ∘ₗ
        ((cellEmbed.{v} hinj F ℓ).frame (S × Unit)).branch PUnit.unit) =
      ((g.sampled (unpair cellOf G')).queryStep (.inl ()) F ℓ).branch () := by
  rw [QuantumRuntime.queryStep_branch_eq_conj _ ((cellGame g ov').sampled_branch G' (.inl ()) ())
      (QReg.of (K × F)) (cellSplit F),
    QuantumRuntime.queryStep_branch_eq_conj _ (g.sampled_branch (unpair cellOf G') (.inl ()) ())
      F ℓ,
    DSubInstrument.branch_frame_apply, DSubInstrument.branch_frame_apply]
  change LinearMap.comp ((MatrixMap.conj _).amplify _)
    (LinearMap.comp _ ((MatrixMap.conj _).amplify _)) = _
  rw [MatrixMap.amplify_conj, MatrixMap.amplify_conj]
  change MatrixMap.conj ((cellIso cellOf F)ᴴ ⊗ₖ (1 : Matrix (S × Unit) (S × Unit) ℂ)) ∘ₗ
      (MatrixMap.conj (basisMatrix (QuantumRuntime.queryEquivOut (C × (K → Y)) (S × Unit) (K × F)) *
          (tableOracle (fun t : S × Unit ↦ (cellGame g ov').answer t.1 G') ⊗ₖ
            (1 : Matrix (K × F) (K × F) ℂ)) *
          basisMatrix (QuantumRuntime.queryEquivIn (Equiv.refl ((C × (K → Y)) × (K × F)))
            (S × Unit))) ∘ₗ
        MatrixMap.conj ((cellIso cellOf F * basisMatrix ℓ) ⊗ₖ
          (1 : Matrix (S × Unit) (S × Unit) ℂ))) =
    MatrixMap.conj (basisMatrix (QuantumRuntime.queryEquivOut (X × Y) (S × Unit) F) *
        (tableOracle (fun t : S × Unit ↦ g.answer t.1 (unpair cellOf G')) ⊗ₖ
          (1 : Matrix F F ℂ)) * basisMatrix (QuantumRuntime.queryEquivIn ℓ (S × Unit)))
  rw [← MatrixMap.conj_mul, ← MatrixMap.conj_mul, ← Matrix.mul_assoc,
    cellCall_matrix hinj g ov' hov G' F ℓ]

include hov in
/-- **Calls through the cell oracle run as the original program.** -/
theorem run_cellCalls (G' : C → K → Y) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (ovSpec X Y S P Res) W A) :
    ((cellGame g ov').sampled G').run .instruments (cellCalls hinj x) =
      (g.sampled (unpair cellOf G')).run .instruments x := by
  let _ : Unique ((ovSpec C (K → Y) S P Res).Result (Sum.inl ())) := inferInstanceAs (Unique Unit)
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    exact congrArg (((LocalSig.Interp.instruments o).frame _).bind) (funext ih)
  | queryBind _ i F ℓ k ih =>
    rcases i with u | j
    · cases u
      rw [cellCalls_queryBind_inl]
      simp only [QuantumRuntime.run_primBind, QuantumRuntime.run_queryBind]
      refine DSubInstrument.ext (funext fun p ↦ ?_)
      simp only [DSubInstrument.branch_bind_apply_univ, Fintype.sum_unique,
        LinearMap.comp_assoc]
      erw [ih]
      exact congrArg (LinearMap.comp _)
        (branch_cellProject_comp_queryStep_comp_cellEmbed.{v} hinj g ov' hov G' F ℓ)
    · rw [cellCalls_queryBind_inr]
      exact congrArg (DSubInstrument.bind ((g.sampled (unpair cellOf G')).queryStep (.inr j) F ℓ))
        (funext ih)

include hov in
/-- **Calls through the cell oracle change no observed law.** -/
theorem evalDistMap_cellCalls (G' : C → K → Y) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (ovSpec X Y S P Res) W A) {γ : Type*}
    [MeasurableSpace γ] (ρ : SubState A) (f : (Σ u, W u) → γ) :
    ((cellGame g ov').sampled G').evalDistMap .instruments (cellCalls hinj x) ρ f =
      (g.sampled (unpair cellOf G')).evalDistMap .instruments x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.jointPost,
    run_cellCalls hinj g ov' hov G' x]
  rfl

end run

/-- A larger event of the leaf has a larger weight. -/
theorem evalDistMap_true_mono {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}}
    (R : QuantumRuntime spec) (I : L.Interp) {A : QReg} (x : QuantumComp L spec W A)
    (ρ : SubState A) {f f' : (Σ u, W u) → Bool} (h : ∀ p, f p = true → f' p = true) :
    R.evalDistMap I x ρ f {true} ≤ R.evalDistMap I x ρ f' {true} := by
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true),
    QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true)]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  gcongr
  by_cases hp : f p = true
  · simp [hp, h p hp]
  · simp [hp]

/-- **The search bound for a predicate on cells, with a classical verifier.** A program making at
most `n` calls is followed by a verifier making at most `m` queries, and at most `k` cells are picked
from their outputs. In the side state the run ends in, one of these cells has only good completions
with probability at most `λ (√6 (n + m) + 2 k)²`, where every cell has a fraction at most `λ` of good
values. The inputs sit in the cells by the injection `cellOf`, and the overrides of `g` are components of
overrides of whole cells. -/
theorem search_withVerifier_cells_le (g : OvGame X Y S P Res) [Nonempty Y] (cellOf : X → C × K)
    (hinj : Function.Injective cellOf) (ov' : S → C → Option (K → Y))
    (hov : ∀ s x, g.ov s x = (ov' s (cellOf x).1).map fun v ↦ v (cellOf x).2)
    (good : C → (K → Y) → Prop) [∀ c, DecidablePred (good c)] (sb : ℕ)
    (hs : ∀ c, (Finset.univ.filter (good c)).card ≤ sb)
    {A : QReg} {α β : Type} [DecidableEq α] [DecidableEq β]
    (adv : QComp (ovSpec X Y S P Res) A (QReg.of Unit) α) (ver : α → OracleComp (X →ₒ Y) β)
    (out : α × β → Finset C) (k : ℕ) (hout : ∀ ab, (out ab).card ≤ k) (n m : ℕ)
    (hadv : adv.IsTotalQueryBound n) (hver : ∀ a, OracleComp.IsTotalQueryBound (ver a) m)
    (ρ : SubState A) :
    ∑ G : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * sideW g G .instruments adv ρ (fun p s ↦
        decide (∃ c ∈ out (p.2.2, evalWithAnswerFn (QueryImpl.ofFn (g.answer s G)) (ver p.2.2)),
          ∀ v : K → Y, (∀ x, (cellOf x).1 = c → v (cellOf x).2 = G x) → good c v)) ≤
      ENNReal.ofReal (((sb : ℝ) / Fintype.card (K → Y)) * (√6 * (n + m : ℕ) + 2 * k) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  set x := withVerifier adv ver
  let ev : (X → Y) → C → Prop := fun G c ↦
    ∀ v : K → Y, (∀ x, (cellOf x).1 = c → v (cellOf x).2 = G x) → good c v
  have h := ov_search_le (cellGame g ov') good .instruments sb hs (n + m) k (cellCalls hinj x)
    (isTotalQueryBound_cellCalls hinj (isTotalQueryBound_withVerifier hadv hver)) ρ
    (fun p ↦ out p.2.2) fun p ↦ hout _
  erw [sampledEvalDistMap_apply _ _ _ _ _ (measurableSet_singleton true)] at h
  have hG : ∀ G : X → Y, sideW g G .instruments adv ρ (fun p s ↦
      decide (∃ c ∈ out (p.2.2, evalWithAnswerFn (QueryImpl.ofFn (g.answer s G)) (ver p.2.2)),
        ev G c)) =
      (g.sampled G).evalDistMap .instruments x ρ
        (fun p ↦ decide (∃ c ∈ out p.2.2, ev G c)) {true} := fun G ↦
    (sideW_withVerifier g G adv ver ρ fun ab _ ↦ decide (∃ c ∈ out ab, ev G c)).symm.trans
      (sideW_const g G .instruments x ρ fun p ↦ decide (∃ c ∈ out p.2.2, ev G c))
  calc _ = ∑ G' : C → K → Y, (Fintype.card (C → K → Y) : ℝ≥0∞)⁻¹ *
          (g.sampled (unpair cellOf G')).evalDistMap .instruments x ρ
            (fun p ↦ decide (∃ c ∈ out p.2.2, ev (unpair cellOf G') c)) {true} :=
        (Finset.sum_congr rfl fun G _ ↦ congrArg _ (hG G)).trans
          (sum_unpair hinj fun G ↦ (g.sampled G).evalDistMap .instruments x ρ
            (fun p ↦ decide (∃ c ∈ out p.2.2, ev G c)) {true}).symm
    _ ≤ ∑ G' : C → K → Y, (Fintype.card (C → K → Y) : ℝ≥0∞)⁻¹ *
          ((cellGame g ov').sampled G').evalDistMap .instruments (cellCalls hinj x) ρ
            (fun p ↦ decide (∃ c ∈ out p.2.2, good c (G' c))) {true} := by
        refine Finset.sum_le_sum fun G' _ ↦ ?_
        rw [evalDistMap_cellCalls hinj g ov' hov G' x]
        gcongr _ * ?_
        refine evalDistMap_true_mono _ _ _ _ fun p hp ↦ ?_
        obtain ⟨c, hc, hgood⟩ := of_decide_eq_true hp
        refine decide_eq_true ⟨c, hc, hgood (G' c) fun y hy ↦ ?_⟩
        rw [← hy]
        rfl
    _ ≤ _ := h

end OvGame

end Qrom
