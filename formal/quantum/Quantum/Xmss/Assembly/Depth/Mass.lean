module

public import Quantum.Par.LockLift
public import Quantum.Par.LockMass
public import Quantum.Xmss.Assembly.Depth.Hybrid

@[expose] public section

/-!
# Hidden masses of the parallel game

The hidden masses of a parallel program over the hardwired ports, whose permutation rounds are
lifted lockstep rounds (`lockRoundR`), are those of its serialization, whose permutation rounds
are the lifted simulations of their calls (`simulate` of `seqCalls`): a round of the lockstep
program weighs the summed masses of its slots (Hybrid's `parSpongeMassR`), a call of the
serialization its hidden mass (`spongeMass`).

* **Pairs of equal weights** (`MassPair`): a sequential and a parallel program whose summed
  weights agree before every pair of continuations of equal weights, from positive semidefinite
  states. Closed under sequencing (`MassPair.bind`) and substitution (`massPair_substitute`);
  `massPair_liftOrdinary` (a program over the single ports), `massPair_bind_leaf` (two one-path
  programs with the same branch and equal weights).
* **The lockstep round** (`massPair_lockRoundR`): against a runtime whose sponge part reads its
  functions in the basis of a unitary `U`, for weights that are counts kept by `U` (LockMass's
  `totalWeight_lockRoundR_eq`).
* **The game** (`massPair_lockRoundR_runtimeR`, `totalWeight_parSpongeMassR_eq`): against
  `runtimeR`, with `spongeMass` and `parSpongeMassR`; for any substitutions whose commands are
  such pairs, the parallel program's `parSpongeMassR` mass is the serialization's `spongeMass`
  mass.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v

namespace Quantum.Par

open Quantum Quantum.Sponge QuantumRuntime Quantum.Xmss.Hybrid

/-! ## Programs with one path, any weight -/

section thin

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}} {N : spec.Port → Prop}
  (R : QuantumRuntime spec) (I : L.Interp)

/-- **The weight of a program with one path, then a continuation**: the path's weight plus the
continuation's from the path's leaf. -/
theorem exists_totalWeight_bind_add_of_isThin
    (W : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞) {X : QReg → Type}
    {A : QReg} (x : QuantumComp L spec X A) (hx : IsThin N x) :
    ∃ p : Σ u, X u, ∀ {Y : QReg → Type} (k : ∀ u, X u → QuantumComp L spec Y u)
      (ρ : Matrix (A × R.D) (A × R.D) ℂ),
      R.totalWeight I W (x.bind k) ρ =
        R.totalWeight I W x ρ + R.totalWeight I W (k p.1 p.2) ((R.run I x).branch p ρ) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    refine ⟨⟨_, y⟩, fun k ρ ↦ ?_⟩
    rw [QuantumComp.pure_bind, totalWeight_pure, zero_add, run_pure,
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
  | primBind _ o k' ih =>
    obtain ⟨⟨b₀⟩, hs⟩ := thinCmd_of_thinCharge (N := N) (c := .prim o) hx.1
    have h2 : IFreeM.IsChargeBound (k' b₀) (thinCharge (L := L) N)
        (0 - thinCharge N _ (.prim o)) := hx.2 (ULift.up b₀)
    obtain ⟨p, hp⟩ := ih b₀ (h2.mono (Nat.sub_le 0 _))
    refine ⟨p, fun k ρ ↦ ?_⟩
    rw [QuantumComp.primBind_bind, totalWeight_primBind, totalWeight_primBind, run_primBind,
      DSubInstrument.branch_bind_apply, tsum_eq_single b₀ fun b hb ↦ absurd (hs.elim b b₀) hb,
      tsum_eq_single b₀ fun b hb ↦ absurd (hs.elim b b₀) hb,
      tsum_eq_single b₀ fun b hb ↦ absurd (hs.elim b b₀) hb, hp]
  | queryBind _ i E ℓ k' ih =>
    obtain ⟨hN, ⟨r₀⟩, hs⟩ := thinCmd_of_thinCharge (N := N) (c := .query i E ℓ) hx.1
    have h2 : IFreeM.IsChargeBound (k' r₀) (thinCharge (L := L) N)
        (0 - thinCharge N _ (.query i E ℓ)) := hx.2 (ULift.up r₀)
    obtain ⟨p, hp⟩ := ih r₀ (h2.mono (Nat.sub_le 0 _))
    refine ⟨p, fun k ρ ↦ ?_⟩
    rw [QuantumComp.queryBind_bind, totalWeight_queryBind, totalWeight_queryBind, run_queryBind,
      DSubInstrument.branch_bind_apply, tsum_eq_single r₀ fun r hr ↦ absurd (hs.elim r r₀) hr,
      tsum_eq_single r₀ fun r hr ↦ absurd (hs.elim r r₀) hr,
      tsum_eq_single r₀ fun r hr ↦ absurd (hs.elim r r₀) hr, hp, add_assoc]

/-- **Weights of a program with one path** depend only on the weights of the ports it calls, on
positive semidefinite operators. -/
theorem totalWeight_congr_of_isThin
    {W₁ W₂ : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (hW : ∀ i, N i → ∀ σ, σ.PosSemidef → W₁ i σ = W₂ i σ) {X : QReg → Type} {A : QReg}
    (x : QuantumComp L spec X A) (hx : IsThin N x) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) : R.totalWeight I W₁ x ρ = R.totalWeight I W₂ x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ y => exact (R.totalWeight_pure I y ρ).trans (R.totalWeight_pure I y ρ).symm
  | primBind _ o k ih =>
    rw [totalWeight_primBind, totalWeight_primBind]
    refine tsum_congr fun b ↦ ?_
    have h2 : IFreeM.IsChargeBound (k b) (thinCharge (L := L) N)
        (0 - thinCharge N _ (.prim o)) := hx.2 (ULift.up b)
    exact ih b (h2.mono (Nat.sub_le 0 _)) (((I o).frame R.D).posSemidef_branch_apply b hρ)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hN, -⟩ := thinCmd_of_thinCharge (N := N) (c := .query i E ℓ) hx.1
    rw [totalWeight_queryBind, totalWeight_queryBind, hW i hN _ (posSemidef_callInput ℓ hρ)]
    refine congrArg _ (tsum_congr fun r ↦ ?_)
    have h2 : IFreeM.IsChargeBound (k r) (thinCharge (L := L) N)
        (0 - thinCharge N _ (.query i E ℓ)) := hx.2 (ULift.up r)
    exact ih r (h2.mono (Nat.sub_le 0 _)) ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ)

end thin

/-! ## Pairs of programs of equal weights -/

section pair

variable {spec : QuantumOracleSpec.{0, 0}} {Q : Type} (port : Q → spec.Port)
  (R : QuantumRuntime spec) (W : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
  (W' : ∀ i, Matrix ((parSpec spec port).In i × R.D) ((parSpec spec port).In i × R.D) ℂ →
    ℝ≥0∞)

/-- **A pair of programs of equal weights**: from every positive semidefinite state, the summed
weight `W` of `x₁` against `R` and `W'` of `x₂` against `R.par port` agree, followed by any
continuations whose weights agree from every positive semidefinite state. -/
def MassPair {X : QReg → Type} {A : QReg} (x₁ : QuantumComp LocalSig.instruments.{0} spec X A)
    (x₂ : QuantumComp LocalSig.instruments.{0} (parSpec spec port) X A) : Prop :=
  ∀ (Y : QReg → Type) (k₁ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec Y u)
    (k₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} (parSpec spec port) Y u),
    (∀ (u : QReg) (y : X u) (ρ : Matrix (u × R.D) (u × R.D) ℂ), ρ.PosSemidef →
      R.totalWeight .instruments W (k₁ u y) ρ =
        (R.par port).totalWeight .instruments W' (k₂ u y) ρ) →
    ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
      R.totalWeight .instruments W (x₁.bind k₁) ρ =
        (R.par port).totalWeight .instruments W' (x₂.bind k₂) ρ

variable {port R W W'}

/-- The weights of a pair. -/
theorem MassPair.totalWeight_eq {X : QReg → Type} {A : QReg}
    {x₁ : QuantumComp LocalSig.instruments.{0} spec X A}
    {x₂ : QuantumComp LocalSig.instruments.{0} (parSpec spec port) X A}
    (h : MassPair port R W W' x₁ x₂) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight .instruments W x₁ ρ = (R.par port).totalWeight .instruments W' x₂ ρ := by
  have e := h _ (fun _ y ↦ QuantumComp.pure y) (fun _ y ↦ QuantumComp.pure y)
    (fun _ y ρ' _ ↦ (R.totalWeight_pure _ y ρ').trans ((R.par port).totalWeight_pure _ y ρ').symm)
    ρ hρ
  rwa [QuantumComp.bind_pure, QuantumComp.bind_pure] at e

theorem massPair_pure {X : QReg → Type} {A : QReg} (y : X A) :
    MassPair port R W W' (QuantumComp.pure y) (QuantumComp.pure y) := fun _ k₁ k₂ hk ρ hρ ↦ by
  rw [QuantumComp.pure_bind, QuantumComp.pure_bind]
  exact hk _ y ρ hρ

/-- **Sequencing pairs.** -/
theorem MassPair.bind {X Y : QReg → Type} {A : QReg}
    {x₁ : QuantumComp LocalSig.instruments.{0} spec X A}
    {x₂ : QuantumComp LocalSig.instruments.{0} (parSpec spec port) X A}
    {k₁ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec Y u}
    {k₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} (parSpec spec port) Y u}
    (hx : MassPair port R W W' x₁ x₂) (hk : ∀ u y, MassPair port R W W' (k₁ u y) (k₂ u y)) :
    MassPair port R W W' (x₁.bind k₁) (x₂.bind k₂) := fun _ m₁ m₂ hm ρ hρ ↦ by
  rw [QuantumComp.bind_assoc, QuantumComp.bind_assoc]
  exact hx _ _ _ (fun u y ρ' hρ' ↦ hk u y _ m₁ m₂ hm ρ' hρ') ρ hρ

/-- **Substitutions of commandwise pairs give pairs.** -/
theorem massPair_substitute {P : IPFunctor.Endo QReg}
    {σ₁ : IPFunctor.CommandSubstitution P (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec)}
    {σ₂ : IPFunctor.CommandSubstitution P
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (parSpec spec port))}
    (h : ∀ A a, MassPair port R W W' (σ₁ A a) (σ₂ A a)) {X : QReg → Type} {A : QReg}
    (y : IFreeM P X A) : MassPair port R W W' (y.substitute σ₁) (y.substitute σ₂) := by
  induction y using IFreeM.inductionOn with
  | pure _ x => exact massPair_pure x
  | liftBind A a next ih =>
    rw [IFreeM.substitute_liftBind, IFreeM.substitute_liftBind]
    refine (h A a).bind fun u b ↦ ?_
    obtain ⟨b, e⟩ := b
    subst e
    exact ih b

/-- **A program over the single ports** pairs with itself, for weights agreeing on the single
calls. -/
theorem massPair_liftOrdinary (hW' : ∀ i σ, W' (.inl i) σ = W i σ) {X : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} spec X A) :
    MassPair port R W W' x (x.liftOrdinary (t := roundSpec spec port)) := by
  intro Y k₁ k₂ hk ρ hρ
  induction x using QuantumComp.inductionOn with
  | pure _ y => exact hk _ y ρ hρ
  | primBind _ o k ih =>
    exact (R.totalWeight_primBind .instruments o _ ρ).trans ((tsum_congr fun b ↦ ih b _
      (((LocalSig.Interp.instruments o).frame R.D).posSemidef_branch_apply b hρ)).trans
      ((R.par port).totalWeight_primBind .instruments (w := W') o _ ρ).symm)
  | queryBind _ i E ℓ k ih =>
    exact (R.totalWeight_queryBind .instruments i E ℓ _ ρ).trans
      ((congrArg₂ (· + ·) (hW' i _).symm (tsum_congr fun r ↦ ih r _
        ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ))).trans
        ((R.par port).totalWeight_queryBind .instruments (w := W') (.inl i) E ℓ _ ρ).symm)

/-- **Two one-path, one-valued programs with the same branch and equal weights**, each returning
one leaf, form a pair. -/
theorem massPair_bind_leaf {N₁ : spec.Port → Prop} {N₂ : (parSpec spec port).Port → Prop}
    {A B : QReg} {α₁ α₂ : Type} [Unique α₁] [Unique α₂] {Y : QReg → Type} (g : ∀ u, B = u → Y u)
    (x₁ : QuantumComp₂ LocalSig.instruments.{0} spec A B α₁)
    (x₂ : QuantumComp₂ LocalSig.instruments.{0} (parSpec spec port) A B α₂)
    (hx₁ : IsThin N₁ x₁) (hx₂ : IsThin N₂ x₂)
    (h : (R.run₂ .instruments x₁).branch default =
      ((R.par port).run₂ .instruments x₂).branch default)
    (hw : ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
      R.totalWeight .instruments W x₁ ρ = (R.par port).totalWeight .instruments W' x₂ ρ) :
    MassPair port R W W' (QuantumComp.bind x₁ fun u l ↦ QuantumComp.pure (g u l.1.symm))
      (QuantumComp.bind x₂ fun u l ↦ QuantumComp.pure (g u l.1.symm)) := by
  intro Y' k₁ k₂ hk ρ hρ
  obtain ⟨p₁, hp₁⟩ := exists_totalWeight_bind_add_of_isThin R .instruments W x₁ hx₁
  obtain ⟨p₂, hp₂⟩ := exists_totalWeight_bind_add_of_isThin (R.par port) .instruments W' x₂ hx₂
  refine (congrArg (fun z ↦ R.totalWeight .instruments W z ρ)
    (QuantumComp.bind_assoc x₁ _ k₁)).trans ((hp₁ _ ρ).trans (Eq.trans ?_ ((hp₂ _ ρ).symm.trans
      (congrArg (fun z ↦ (R.par port).totalWeight .instruments W' z ρ)
        (QuantumComp.bind_assoc x₂ _ k₂)).symm)))
  refine congrArg₂ (· + ·) (hw ρ hρ) ?_
  obtain ⟨u₁, e₁, a₁⟩ := p₁
  obtain ⟨u₂, e₂, a₂⟩ := p₂
  subst e₁ e₂
  obtain rfl := Subsingleton.elim a₁ default
  obtain rfl := Subsingleton.elim a₂ default
  exact (congrArg (R.totalWeight .instruments W (k₁ _ (g _ rfl))) (LinearMap.congr_fun h ρ)).trans
    (hk _ _ _ (((R.par port).run₂ .instruments x₂).posSemidef_branch_apply _ hρ))

end pair

/-! ## Lifted programs -/

section lift

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M]
  [DecidableEq M] (t : QuantumOracleSpec.{0, 0}) (R : QuantumRuntime ((hwSpec X Z M).sum t))
  {L : LocalSig.{u, v}} (I : L.Interp)

/-- A weight of the sponge ports, single or in rounds, from a weight of the lifted ports. -/
def liftParW {D : QReg}
    (W' : ∀ i, Matrix ((parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t)).In i × D)
      ((parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t)).In i × D) ℂ → ℝ≥0∞) :
    ∀ i, Matrix ((parSpec (spongeSpec X Z) id).In i × D)
      ((parSpec (spongeSpec X Z) id).In i × D) ℂ → ℝ≥0∞
  | .inl p => W' (.inl (hwSpongePort X Z M t p))
  | .inr (.round w f) => W' (.inr (.round w f))

omit [Fintype M] [DecidableEq M] in
/-- **Weights of a lifted program** are those against the sponge part. -/
theorem totalWeight_mapLens_hwLens
    (W : ∀ i, Matrix (((hwSpec X Z M).sum t).In i × R.D) (((hwSpec X Z M).sum t).In i × R.D) ℂ →
      ℝ≥0∞) {Xf : QReg → Type} {A : QReg} (z : QuantumComp L (spongeSpec X Z) Xf A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I W (IFreeM.mapLens (hwLens X Z M t) z) ρ =
      (hwPart t R).totalWeight I (fun p ↦ W (hwSpongePort X Z M t p)) z ρ := by
  induction z using QuantumComp.inductionOn with
  | pure _ y => exact (R.totalWeight_pure I y ρ).trans ((hwPart t R).totalWeight_pure I y ρ).symm
  | primBind _ o k ih =>
    exact (R.totalWeight_primBind I o _ ρ).trans ((tsum_congr fun b ↦ ih b _).trans
      ((hwPart t R).totalWeight_primBind I o _ ρ).symm)
  | queryBind _ i E ℓ k ih =>
    exact (R.totalWeight_queryBind I (hwSpongePort X Z M t i) E ℓ _ ρ).trans
      ((congrArg (_ + ·) (tsum_congr fun r ↦ ih r _)).trans
        ((hwPart t R).totalWeight_queryBind I (w := fun p ↦ W (hwSpongePort X Z M t p)) i E ℓ k
          ρ).symm)

omit [Fintype M] [DecidableEq M] in
/-- **Weights of a lifted parallel program** are those against the sponge part, rounds
included. -/
theorem totalWeight_mapLens_hwParLens
    (W' : ∀ i, Matrix ((parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t)).In i × R.D)
      ((parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t)).In i × R.D) ℂ → ℝ≥0∞)
    {Xf : QReg → Type} {A : QReg} (y : QuantumComp L (parSpec (spongeSpec X Z) id) Xf A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    (R.par (hwSpongePort X Z M t)).totalWeight I W' (IFreeM.mapLens (hwParLens X Z M t) y) ρ =
      ((hwPart t R).par id).totalWeight I (liftParW t W') y ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ y =>
    exact ((R.par _).totalWeight_pure I y ρ).trans
      (((hwPart t R).par id).totalWeight_pure I y ρ).symm
  | primBind _ o k ih =>
    exact ((R.par _).totalWeight_primBind I o _ ρ).trans ((tsum_congr fun b ↦ ih b _).trans
      (((hwPart t R).par id).totalWeight_primBind I o _ ρ).symm)
  | queryBind _ i E ℓ k ih =>
    rcases i with p | ⟨w, f⟩
    · exact ((R.par _).totalWeight_queryBind I (.inl (hwSpongePort X Z M t p)) E ℓ _ ρ).trans
        ((congrArg (_ + ·) (tsum_congr fun r ↦ ih r _)).trans
          (((hwPart t R).par id).totalWeight_queryBind I (w := liftParW t W') (.inl p) E ℓ k
            ρ).symm)
    · refine ((R.par (hwSpongePort X Z M t)).totalWeight_queryBind I (w := W')
        (.inr (.round w f)) E ℓ (fun r ↦ IFreeM.mapLens (hwParLens X Z M t) (k r)) ρ).trans
        (Eq.trans ?_ (((hwPart t R).par id).totalWeight_queryBind I (w := liftParW t W')
          (.inr (.round w f)) E ℓ k ρ).symm)
      exact congrArg (_ + ·) (tsum_congr fun r ↦ (ih r _).trans (congrArg (fun S ↦
        ((hwPart t R).par id).totalWeight I (liftParW t W') (k r) (DSubInstrument.branch S r ρ))
        (queryStep_par_hwPart_round t R f E ℓ).symm))

end lift

/-! ## The lockstep round has one path, with rounds of one port -/

section lockThin

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] {w : ℕ} {E : QReg}

/-- Single calls, and rounds of one port. -/
def ConstRound {spec : QuantumOracleSpec.{0, 0}} {Q : Type} {port : Q → spec.Port} :
    (parSpec spec port).Port → Prop
  | .inl _ => True
  | .inr (.round _ f) => ∀ j j', f j = f j'

omit [AddCommGroup X] [AddCommGroup Z] in
theorem isThin_subRound_const (p : SpongePort) (e : (X × Z) ≃ spongeIn X Z p) (P : Fin w → Prop)
    [DecidablePred P] : IsThin ConstRound (subRound (E := E) p e P) := by
  unfold subRound
  exact isThin_queryBind (L := LocalSig.instruments.{0}) _ _ _
    ⟨fun _ _ ↦ rfl, ⟨fun _ ↦ ()⟩, inferInstanceAs (Subsingleton (Fin _ → Unit))⟩
    fun _ ↦ isThin_isoGate _ _

omit [AddCommGroup X] [AddCommGroup Z] in
theorem isThin_gateAll_const (g : Fin w → Equiv.Perm (SlotT X Z)) :
    IsThin (ConstRound (spec := spongeSpec X Z) (port := id)) (gateAll (E := E) g) :=
  isThin_isoGate _ _

/-- **The lockstep round has one path**, with rounds of one port. -/
theorem isThin_lockRoundR_const (π : Equiv.Perm (X × Z)) (dir : Fin w → PermutationPort)
    {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) :
    IsThin ConstRound (lockRoundR π dir ℓ post) := by
  unfold lockRoundR
  refine IsThin.bind₂ ?_ fun _ ↦ isThin_coGate _ _
  repeat' first
    | exact isThin_gateAll_const _
    | exact isThin_subRound_const _ _ _
    | exact isThin_isoGate _ _
    | refine IsThin.bind₂ ?_ fun _ ↦ ?_

end lockThin

/-! ## The lifted lockstep round pairs with the lifted serialized simulation -/

section lockPair

variable {X Z M : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] (t : QuantumOracleSpec.{0, 0})
  (R : QuantumRuntime ((hwSpec X Z M).sum t)) (U : Matrix R.D R.D ℂ)
  (hU : U ∈ unitaryGroup R.D ℂ) (rd : R.D → SpongeKeys X Z) (hR : IsReadRuntime (hwPart t R) U rd)
  (c : ∀ p, spongeIn X Z p × R.D → ℕ)
  (hcU : ∀ d' d, U d' d ≠ 0 → ∀ p y, c p (y, d') = c p (y, d))
  (W : ∀ i, Matrix (((hwSpec X Z M).sum t).In i × R.D) (((hwSpec X Z M).sum t).In i × R.D) ℂ →
    ℝ≥0∞)
  (W' : ∀ i, Matrix ((parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t)).In i × R.D)
    ((parSpec ((hwSpec X Z M).sum t) (hwSpongePort X Z M t)).In i × R.D) ℂ → ℝ≥0∞)
  (hW : ∀ p σ, σ.PosSemidef → W (hwSpongePort X Z M t p) σ = diagW (c p) σ)
  (hW₁ : ∀ p σ, σ.PosSemidef → W' (.inl (hwSpongePort X Z M t p)) σ = diagW (c p) σ)
  (hWr : ∀ w (f : Fin w → SpongePort), (∀ j j', f j = f j') → ∀ σ, σ.PosSemidef →
    W' (.inr (.round w f)) σ = diagW (roundCount (spec := spongeSpec X Z) (D := R.D) c f) σ)

include hU hR hcU hW hW₁ hWr in
/-- **The lifted lockstep round pairs with the lifted serialized simulation of the round**, against
a runtime whose sponge part reads its functions in the basis of `U`, for weights that are counts
kept by `U` on the sponge ports, single or in rounds of one port. -/
theorem massPair_lockRoundR (π : Equiv.Perm (X × Z)) {w : ℕ} (dir : Fin w → PermutationPort)
    (E : QReg) {A B : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E)
    (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) {Y : QReg → Type} (g : ∀ u, B = u → Y u) :
    MassPair (hwSpongePort X Z M t) R W W'
      (QuantumComp.bind (IFreeM.mapLens (hwLens X Z M t)
        (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post)))
          fun u l ↦ QuantumComp.pure (g u l.1.symm))
      (QuantumComp.bind (IFreeM.mapLens (hwParLens X Z M t) (lockRoundR π dir ℓ post))
        fun u l ↦ QuantumComp.pure (g u l.1.symm)) := by
  have : Unique (RoundResult (qrpmSpec (X × Z)) dir) := inferInstanceAs (Unique (Fin w → Unit))
  refine massPair_bind_leaf g _ _
    (isThin_mapLens_hwLens t (isThin_simulate _ π (isThin_seqCalls (spec := qrpmSpec (X × Z))
      (N := fun _ ↦ True) dir (fun _ ↦ ⟨trivial, ⟨()⟩, inferInstanceAs (Subsingleton Unit)⟩) E
        ℓ post)))
    (isThin_mapLens_hwParLens t (isChargeBound_of_charge_le (fun _ a ↦ thinCharge_le_of (by
      rcases a with o | ⟨i, E, ℓ⟩
      · exact id
      · exact fun h ↦ ⟨trivial, h.2⟩)) (isThin_lockRoundR_const π dir ℓ post)))
    ((congrArg (fun P ↦ DSubInstrument.branch P default) (run₂_mapLens_hwLens t R .instruments
      _)).trans ((branch_run₂_simulate_seqCalls_eq_lockRoundR (hwPart t R) U hU rd hR π dir E ℓ
        post default).trans (congrArg (fun P ↦ DSubInstrument.branch P ())
          (run₂_mapLens_hwParLens t R .instruments _).symm))) fun ρ hρ ↦ ?_
  refine (totalWeight_mapLens_hwLens t R .instruments W _ ρ).trans ?_
  refine (tsum_congr fun j ↦ (hwPart t R).queryWeight_congr .instruments
    (w' := fun p ↦ diagW (c p)) (fun p σ hσ ↦ hW p σ hσ) _ hρ j).trans ?_
  refine (totalWeight_lockRoundR_eq (hwPart t R) U hU rd hR c hcU π dir E ℓ post hρ).symm.trans ?_
  refine (totalWeight_congr_of_isThin ((hwPart t R).par id) .instruments ?_ _
    (isThin_lockRoundR_const π dir ℓ post) hρ).trans
      (totalWeight_mapLens_hwParLens t R .instruments W' _ ρ).symm
  rintro (p | ⟨w', f⟩) hi σ hσ
  · exact (hW₁ p σ hσ).symm
  · exact (hWr w' f hi σ hσ).symm

end lockPair

end Quantum.Par

/-! ## The game: hidden masses against `runtimeR` -/

namespace Quantum.Xmss.Hybrid

open Quantum Quantum.Par Quantum.Sponge QuantumRuntime Quantum.Xmss.Assembly

section game

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] [Nonempty X] [Nonempty Z] {S : Type} [Fintype S] [DecidableEq S] {M' : Type}
  [Fintype M'] [DecidableEq M'] (m₀ : Finset S × M') (Hh : Set Z) (Hk Hk' : Set X)

variable (M') in
/-- The hidden inputs of the calls of the sponge ports, as counts. -/
noncomputable def slotCount (p : SpongePort) : spongeIn X Z p × HwReg X Z (Finset S × M') → ℕ :=
  (slotHid M' Hh Hk Hk' p).indicator 1

omit [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z] [Fintype S] [Fintype M'] in
/-- The compression keeps the hardwired part, hence the hidden inputs. -/
theorem slotCount_compressReg (d' d : HwReg X Z (Finset S × M'))
    (h : compressReg X Z (Finset S × M') d' d ≠ 0) (p : SpongePort) (y : spongeIn X Z p) :
    slotCount M' Hh Hk Hk' p (y, d') = slotCount M' Hh Hk Hk' p (y, d) := by
  obtain ⟨a', b'⟩ := d'
  obtain ⟨a, b⟩ := d
  have hb : b' = b := by
    by_contra hne
    exact h (by rw [compressReg, kroneckerMap_apply, Matrix.one_apply_ne hne, mul_zero])
  subst hb
  have hm := mem_slotHid_congr (M' := M') Hh Hk Hk' p (y, (a', b')) (y, (a, b')) rfl rfl
  by_cases hy : (y, (a, b')) ∈ slotHid M' Hh Hk Hk' p
  · rw [slotCount, Set.indicator_of_mem hy, Set.indicator_of_mem (hm.2 hy)]
    rfl
  · rw [slotCount, Set.indicator_of_notMem hy, Set.indicator_of_notMem fun h' ↦ hy (hm.1 h')]

omit [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z] in
theorem spongeMass_portR (p : SpongePort)
    (σ : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ) :
    spongeMass (S := S) (M' := M') Hh Hk Hk' (portR X Z S M' p) σ =
      diagW (slotCount M' Hh Hk Hk' p) σ := by
  rw [spongeMass_eq]
  exact (congrFun (hiddenMass_portR Hh Hk Hk' p) σ).trans (diagMass_eq_diagW _ σ)

omit [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z] in
/-- A round of one port weighs the summed hidden masses of its slots, as counts. -/
theorem parSpongeMassR_round_eq_diagW {w : ℕ} (f : Fin w → SpongePort) (hf : ∀ j j', f j = f j')
    (σ : Matrix ((parSpec (recHwSpec X Z S M') (portR X Z S M')).In (.inr (.round w f)) ×
      HwReg X Z (Finset S × M')) ((parSpec (recHwSpec X Z S M') (portR X Z S M')).In
        (.inr (.round w f)) × HwReg X Z (Finset S × M')) ℂ) :
    parSpongeMassR Hh Hk Hk' (.inr (.round w f)) σ =
      diagW (roundCount (spec := spongeSpec X Z) (D := QReg.of (HwReg X Z (Finset S × M')))
        (slotCount M' Hh Hk Hk') f) σ := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp only [parSpongeMassR, hybClsR, decide_true, ↓reduceIte]
    exact ((diagW_congr (fun _ ↦ Fin.sum_univ_zero _) σ).trans (diagW_zero σ)).symm
  · obtain ⟨p, rfl⟩ : ∃ p, f = fun _ ↦ p := ⟨f ⟨0, hw⟩, funext fun j ↦ hf j _⟩
    rw [parSpongeMassR_round Hh Hk Hk' hw.ne']
    refine (Finset.sum_congr rfl fun j _ ↦ diagMass_eq_diagW _ σ).trans
      ((sum_diagW _ _ σ).trans (diagW_congr (fun x ↦ Finset.sum_congr rfl fun j _ ↦ ?_) σ))
    by_cases hx : (x.1 j, x.2) ∈ slotHid M' Hh Hk Hk' p
    · exact (Set.indicator_of_mem (show x ∈ {x | (x.1 j, x.2) ∈ slotHid M' Hh Hk Hk' p} from hx)
        1).trans (Set.indicator_of_mem hx 1).symm
    · exact (Set.indicator_of_notMem (show x ∉ {x | (x.1 j, x.2) ∈ slotHid M' Hh Hk Hk' p} from
        hx) 1).trans (Set.indicator_of_notMem hx 1).symm

/-- **A lifted program over the single ports** pairs with itself against `runtimeR`. -/
theorem massPair_liftOrdinary_runtimeR {Xf : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M') Xf A) :
    MassPair (portR X Z S M') (runtimeR m₀) (spongeMass Hh Hk Hk') (parSpongeMassR Hh Hk Hk') x
      (x.liftOrdinary (t := roundSpec (recHwSpec X Z S M') (portR X Z S M'))) :=
  massPair_liftOrdinary (fun i σ ↦ congrFun (parSpongeMassR_inl Hh Hk Hk' i) σ) x

/-- **The lifted lockstep round pairs with the lifted serialized simulation against `runtimeR`**:
the masses `parSpongeMassR` of `lockRoundR`'s rounds (the summed hidden masses of their slots) are
the hidden masses `spongeMass` of the calls of the serialized simulation. -/
theorem massPair_lockRoundR_runtimeR (π : Equiv.Perm (X × Z)) {w : ℕ}
    (dir : Fin w → PermutationPort) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B)
    {Y : QReg → Type} (g : ∀ u, B = u → Y u) :
    MassPair (portR X Z S M') (runtimeR m₀) (spongeMass Hh Hk Hk') (parSpongeMassR Hh Hk Hk')
      (QuantumComp.bind (IFreeM.mapLens (hwLens X Z (Finset S × M') (recSpec S M'))
        (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post)))
          fun u l ↦ QuantumComp.pure (g u l.1.symm))
      (QuantumComp.bind (IFreeM.mapLens (hwParLens X Z (Finset S × M') (recSpec S M'))
        (lockRoundR π dir ℓ post)) fun u l ↦ QuantumComp.pure (g u l.1.symm)) :=
  massPair_lockRoundR (recSpec S M') (runtimeR m₀) (compressReg X Z (Finset S × M'))
    compressReg_mem_unitaryGroup (hwKeys X Z (Finset S × M'))
    (isReadRuntime_spongeHardwired (hwEmpty X Z) m₀) (slotCount M' Hh Hk Hk')
    (fun d' d h p y ↦ slotCount_compressReg Hh Hk Hk' d' d h p y) (spongeMass Hh Hk Hk')
    (parSpongeMassR Hh Hk Hk') (fun p σ _ ↦ spongeMass_portR Hh Hk Hk' p σ)
    (fun p σ _ ↦ (congrFun (parSpongeMassR_inl Hh Hk Hk' _) σ).trans
      (spongeMass_portR Hh Hk Hk' p σ))
    (fun _ f hf σ _ ↦ parSpongeMassR_round_eq_diagW Hh Hk Hk' f hf σ) π dir E ℓ post g

/-- **The hidden masses of the parallel game are those of the serialized game**: for substitutions
of the same commands into the ports of `runtimeR` and into its parallel ports whose commands pair
(`massPair_liftOrdinary_runtimeR`, `massPair_lockRoundR_runtimeR`, `MassPair.bind`), the summed
masses `parSpongeMassR` of the parallel program against `(runtimeR m₀).par (portR ..)` (a round:
the summed hidden masses of its slots) are the summed hidden masses `spongeMass` of the
sequential program against `runtimeR m₀`. -/
theorem totalWeight_parSpongeMassR_eq {P : IPFunctor.Endo QReg}
    {σ₁ : IPFunctor.CommandSubstitution P
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z S M'))}
    {σ₂ : IPFunctor.CommandSubstitution P (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (parSpec (recHwSpec X Z S M') (portR X Z S M')))}
    (h : ∀ A a, MassPair (portR X Z S M') (runtimeR m₀) (spongeMass Hh Hk Hk')
      (parSpongeMassR Hh Hk Hk') (σ₁ A a) (σ₂ A a))
    {Xf : QReg → Type} {A : QReg} (y : IFreeM P Xf A)
    {ρ : Matrix (A × HwReg X Z (Finset S × M')) (A × HwReg X Z (Finset S × M')) ℂ}
    (hρ : ρ.PosSemidef) :
    ((runtimeR m₀).par (portR X Z S M')).totalWeight .instruments (parSpongeMassR Hh Hk Hk')
        (y.substitute σ₂) ρ =
      (runtimeR m₀).totalWeight .instruments (spongeMass Hh Hk Hk') (y.substitute σ₁) ρ :=
  ((massPair_substitute h y).totalWeight_eq hρ).symm

end game

end Quantum.Xmss.Hybrid

end
