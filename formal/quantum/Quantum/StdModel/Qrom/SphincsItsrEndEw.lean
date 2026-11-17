module

public import Quantum.StdModel.Qrom.SphincsItsrCalls

@[expose] public section

/-!
# The event weight at the end of the ITSR game of leanSPHINCS's B3

The weight of the event `BadRQ (pkQ θ) (honQ θ) S` at the end of the realized ITSR game
`gameIQ strPol A θ` (`SphincsItsrGame`), as End's `ewGameQ_le` bounds it at the end of the
verification game, and its average over the hidden values.

* **Sequences with free continuations** (`totalWeight_bind_of_eq_zero`,
  `totalWeight_bind₂_of_eq_zero`): a continuation of total weight `0` from every positive
  semidefinite operator adds nothing to the total weight.
* **The data costs nothing** (`totalWeight_foldIQ_eq_zero`, `totalWeight_prefixIQ_eq`): the
  realized `foldT` calls record ports (weight `0`) and programs of `H_msg` call-0 cells, which are
  cells of the canonical table, hence exempt (`exemptCell_digestCell`); so the classical costs of
  the prefix with the data are the prefix's, `twPQ`.
* **The event bound at the end of the prefix with the data** (`ewPrefixIQ_le`):
  `(advTermQ q S + √twPQ)²` (Assembly's `eventWeight_runtimeR_le`).
* **The event bound over the game** (`ewGameIQ_le`): the tail's two reads graded like adversary
  calls (EventSqrt's `rpow_inv_two_eventWeight_keepReads_le`),
  `ew ≤ (advTermQ q S + verTermI S + √(twPQ + verLinI S))²`.
* **Averaged** (`uavg_ewGameIQ_le`): Minkowski over the hidden values, with the prefix's averaged
  classical cost at most `T`: `E ew ≤ (advBarQ q + verBarI + √(T + verLinBarI))²`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.Qrom.Sphincs
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen extWeight
  extCls realizeT_bind₂ eventWeight_runtimeR_le
  noBot_runtimeR querySupportedOn_runtimeR_step' rpow_inv_two_eventWeight_keepReads_le keepCost
  isChargeBound_mono_charge eventWeight_bind₂ eventWeight_eq_tsum_run₂ tsum_rpow_inv_two_ite
  rpow_inv_two_add_le_of_le_sq uavg_const RevealVals)

attribute [local irreducible] sphincsRom
attribute [local irreducible] Quantum.Qrom.hashQ LeanSphincsOver.messageDigest

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

local notation "hashChargeQ" => Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge
local notation "signChargeQ" => Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge

/-! ## Sequences with free continuations -/

section free

universe u v w w₁ w₂ u₁ v₁

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)

/-- **A free continuation adds no weight**: if every `k t y` has total weight `0` from every
positive semidefinite operator, `x.bind k` has the total weight of `x`. -/
theorem totalWeight_bind_of_eq_zero {X : QReg → Type w} {Y : QReg → Type w₁} {A : QReg}
    (x : QuantumComp L spec X A) (k : ∀ t, X t → QuantumComp L spec Y t)
    (hk : ∀ (t : QReg) (y : X t) (σ : Matrix (t × R.D) (t × R.D) ℂ), σ.PosSemidef →
      R.totalWeight I w (k t y) σ = 0)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I w (x.bind k) ρ = R.totalWeight I w x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    rw [QuantumComp.pure_bind, totalWeight_pure]
    exact hk _ y ρ hρ
  | primBind _ o k' ih =>
    rw [QuantumComp.primBind_bind, totalWeight_primBind, totalWeight_primBind]
    exact tsum_congr fun b ↦ ih b (((I o).frame R.D).posSemidef_branch_apply b hρ)
  | queryBind _ i E ℓ k' ih =>
    rw [QuantumComp.queryBind_bind, totalWeight_queryBind, totalWeight_queryBind]
    exact congrArg _ (tsum_congr fun r ↦ ih r ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ))

/-- `totalWeight_bind_of_eq_zero` for programs with fixed final registers. -/
theorem totalWeight_bind₂_of_eq_zero {A B C : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B C β)
    (hk : ∀ a (σ : Matrix (B × R.D) (B × R.D) ℂ), σ.PosSemidef →
      R.totalWeight I w (k a) σ = 0)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I w (x.bind k) ρ = R.totalWeight I w x ρ :=
  totalWeight_bind_of_eq_zero R I w x _ (fun u p σ hσ ↦ by
    rcases p with ⟨rfl, a⟩
    exact hk a σ hσ) hρ

/-- A call of weight `0` followed by continuations of weight `0` has weight `0`. -/
theorem totalWeight_queryBind_eq_zero {X : QReg → Type w} {A : QReg} (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E) (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hi : ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ, σ.PosSemidef → w i σ = 0)
    (hk : ∀ r (σ : Matrix (QReg.of (spec.Out i × E) × R.D) (QReg.of (spec.Out i × E) × R.D) ℂ),
      σ.PosSemidef → R.totalWeight I w (k r) σ = 0) :
    R.totalWeight I w (QuantumComp.queryBind i E ℓ k) ρ = 0 := by
  rw [totalWeight_queryBind, hi _ (posSemidef_callInput ℓ hρ), zero_add]
  exact ENNReal.tsum_eq_zero.2 fun r ↦ hk r _ ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ)

/-- A local operation followed by continuations of weight `0` has weight `0`. -/
theorem totalWeight_primBind_eq_zero {X : QReg → Type w} {A : QReg} (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hk : ∀ b (σ : Matrix (L.next o b × R.D) (L.next o b × R.D) ℂ), σ.PosSemidef →
      R.totalWeight I w (k b) σ = 0) :
    R.totalWeight I w (QuantumComp.primBind o k) ρ = 0 := by
  rw [totalWeight_primBind]
  exact ENNReal.tsum_eq_zero.2 fun b ↦ hk b _ (((I o).frame R.D).posSemidef_branch_apply b hρ)

end free

/-! ## The data costs nothing -/

section data

/-- **The classical weights of runtime 2** for the event `BadRQ pk hon S`: the refined read cost
and the program flip cost (record ports free), as in `twPQ`. -/
noncomputable def costWI (pk : PublicKey) (hon : HonestCells) (S : Quantum.Sphincs.Disclosures) :
    ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
      Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
          (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
        ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
          (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (fun c σ ↦ readCostT (BadRQ pk hon S) c σ)
    fun c σ ↦ flipCost (BadRQ pk hon S) (hwProgKraus c) 0 σ)

/-- **An `H_msg` call-0 cell of the canonical table is exempt**: it is the cell of the message's
digest position. -/
theorem exemptCell_digestCell (θ : TVals) (msg : Message) :
    ExemptCell (pkQ θ) (honQ θ) (digestCell (tabOf θ).publicSeed (tabOf θ).root
      ((tabOf θ).randomizer msg) msg 0) := by
  rw [← cellOf_digPos (seedOf θ)]
  exact exemptCell_cellOf (seedOf θ) (tabOf θ) (digPos msg)

/-- **The digest port, realized, costs nothing** at the canonical public key and honest cells. -/
theorem costWI_digPort (S : Quantum.Sphincs.Disclosures) (pol : DigestPolicy) (L : Finset TPos)
    (msg : Message) (θ : TVals) {σ : Matrix _ _ ℂ} (hσ : σ.PosSemidef) :
    costWI (pkQ θ) (honQ θ) S (.inl (.inr ((digPort pol L msg).realize θ))) σ = 0 := by
  show flipCost (BadRQ (pkQ θ) (honQ θ) S) (hwProgKraus ((digPort pol L msg).realize θ)) 0 σ = 0
  rw [realize_digPort]
  exact flipCost_programH_badRQ_eq_zero (exemptCell_digestCell θ msg) _ hσ

section template

variable (pk : PublicKey) (hon : HonestCells) (S : Quantum.Sphincs.Disclosures) (θ : TVals)
  {B C : QReg} {α β : Type}

/-- A realized reveal: the record port of `T`, then the continuation at the values of `θ` on
`T`. -/
theorem realizeT_revealThenI (T : Finset TPos)
    (k : RevealVals TVal T × QMem → QComp (SSpecQ SelMem) B C α) :
    realizeT θ (revealThen goodQ T k) =
      QuantumComp.queryBind (L := LocalSig.instruments.{0})
        (spec := recHwSpec PairOut Qrom.HashDomain TPos SelMem) (.inr T) B
        (Equiv.uniqueProd B Unit).symm fun r ↦
          QuantumComp.primBind (L := LocalSig.instruments.{0})
            ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦
              realizeT θ (k (restrictTo T θ, r)) :=
  rfl

/-- A realized program port: the program port it realizes at `θ`, then the continuation. -/
theorem realizeT_progThenI (p : LazyProg PairOut Qrom.HashDomain TPos TVal) (hp : goodQ p)
    (k : QComp (SSpecQ SelMem) B C α) :
    realizeT θ (progThen p hp k) =
      QuantumComp.queryBind (L := LocalSig.instruments.{0})
        (spec := recHwSpec PairOut Qrom.HashDomain TPos SelMem) (.inl (.inr (p.realize θ))) B
        (Equiv.uniqueProd B Unit).symm fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{0})
            ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦
              realizeT θ k := by
  cases p <;> rfl

/-- **A realized reveal is free**: it is a record port. -/
theorem totalWeight_revealThen_eq_zero (T : Finset TPos)
    (k : RevealVals TVal T × QMem → QComp (SSpecQ SelMem) B C α)
    {ρ : Matrix (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ} (hρ : ρ.PosSemidef)
    (hk : ∀ v r (σ : Matrix (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ), σ.PosSemidef →
        (runtimeR m0Q).totalWeight .instruments (costWI pk hon S) (realizeT θ (k (v, r))) σ =
          0) :
    (runtimeR m0Q).totalWeight .instruments (costWI pk hon S)
      (realizeT θ (revealThen goodQ T k)) ρ = 0 := by
  rw [realizeT_revealThenI]
  exact totalWeight_queryBind_eq_zero _ _ _ _ _ _ _ hρ (fun _ _ ↦ rfl) fun r _ hσ ↦
    totalWeight_primBind_eq_zero _ _ _ _ _ hσ fun _ _ hσ' ↦ hk _ r _ hσ'

/-- **A realized program port of weight `0`** followed by a free continuation is free. -/
theorem totalWeight_progThen_eq_zero (p : LazyProg PairOut Qrom.HashDomain TPos TVal)
    (hp : goodQ p) (k : QComp (SSpecQ SelMem) B C α)
    {ρ : Matrix (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ} (hρ : ρ.PosSemidef)
    (hp0 : ∀ σ : Matrix _ _ ℂ, σ.PosSemidef →
      costWI pk hon S (.inl (.inr (p.realize θ))) σ = 0)
    (hk : ∀ σ : Matrix (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ, σ.PosSemidef →
        (runtimeR m0Q).totalWeight .instruments (costWI pk hon S) (realizeT θ k) σ = 0) :
    (runtimeR m0Q).totalWeight .instruments (costWI pk hon S)
      (realizeT θ (progThen p hp k)) ρ = 0 := by
  rw [realizeT_progThenI]
  exact totalWeight_queryBind_eq_zero _ _ _ _ _ _ _ hρ hp0 fun _ _ hσ ↦
    totalWeight_primBind_eq_zero _ _ _ _ _ hσ fun _ _ hσ' ↦ hk _ hσ'

/-- **A realized sequence with a free continuation** costs what its first part costs. -/
theorem totalWeight_realizeT_bind_of_eq_zero {A : QReg} (x : QComp (SSpecQ SelMem) A B α)
    (k : α → QComp (SSpecQ SelMem) B C β)
    {ρ : Matrix (A × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      (A × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ} (hρ : ρ.PosSemidef)
    (hk : ∀ a (σ : Matrix (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ), σ.PosSemidef →
        (runtimeR m0Q).totalWeight .instruments (costWI pk hon S) (realizeT θ (k a)) σ = 0) :
    (runtimeR m0Q).totalWeight .instruments (costWI pk hon S) (realizeT θ (x.bind k)) ρ =
      (runtimeR m0Q).totalWeight .instruments (costWI pk hon S) (realizeT θ x) ρ := by
  rw [realizeT_bind₂]
  exact totalWeight_bind₂_of_eq_zero _ _ _ _ _ hk hρ

/-- A realized `pure` is free. -/
theorem totalWeight_realizeT_pure (a : α)
    (σ : Matrix (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ) :
    (runtimeR m0Q).totalWeight .instruments (costWI pk hon S)
      (realizeT θ (QuantumComp₂.pure a : QComp (SSpecQ SelMem) B B α)) σ = 0 :=
  (runtimeR m0Q).totalWeight_pure .instruments _ σ

end template

/-- **The realized data cost nothing**: the reveals are record ports, the programs those of
exempt digest cells. -/
theorem totalWeight_foldIQ_eq_zero (S : Quantum.Sphincs.Disclosures) (pol : DigestPolicy)
    (θ : TVals) (B : QReg) (msgs : List Message)
    {ρ : Matrix (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      (B × (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ}
    (hρ : ρ.PosSemidef) :
    (runtimeR m0Q).totalWeight .instruments (costWI (pkQ θ) (honQ θ) S)
      (realizeT θ (foldT SelMem pol B msgs)) ρ = 0 := by
  induction msgs generalizing ρ with
  | nil => exact totalWeight_realizeT_pure _ _ S θ _ ρ
  | cons msg ms ih =>
    rw [foldT]
    refine totalWeight_revealThen_eq_zero _ _ S θ _ _ hρ fun r₁ _ σ₁ hσ₁ ↦ ?_
    refine totalWeight_revealThen_eq_zero _ _ S θ _ _ hσ₁ fun r₂ _ σ₂ hσ₂ ↦ ?_
    refine totalWeight_progThen_eq_zero _ _ S θ _ _ _ hσ₂
      (fun _ hσ ↦ costWI_digPort S pol _ msg θ hσ) fun σ₃ hσ₃ ↦ ?_
    exact (totalWeight_realizeT_bind_of_eq_zero _ _ S θ _ _ hσ₃
      fun _ σ _ ↦ totalWeight_realizeT_pure _ _ S θ _ σ).trans (ih hσ₃)

/-- **The classical costs of the prefix with the data are the prefix's**, `twPQ`. -/
theorem totalWeight_prefixIQ_eq (S : Quantum.Sphincs.Disclosures) (pol : DigestPolicy)
    (A : SAdversary) (θ : TVals) :
    (runtimeR m0Q).totalWeight .instruments (costWI (pkQ θ) (honQ θ) S) (prefixIQ pol A θ)
        initQ =
      twPQ (pkQ θ) (honQ θ) S pol A θ := by
  rw [prefixIQ, prefixIT]
  exact (totalWeight_realizeT_bind_of_eq_zero _ _ S θ _ _ initQ_posSemidef fun x σ hσ ↦
    (totalWeight_realizeT_bind_of_eq_zero _ _ S θ _ _ hσ
      fun _ σ' _ ↦ totalWeight_realizeT_pure _ _ S θ _ σ').trans
      (totalWeight_foldIQ_eq_zero S pol θ _ _ hσ)).trans rfl

/-- **The event bound at the end of the prefix with the data**: with at most `q` adversary calls
and `K` classical calls, `ew ≤ (advTermQ q S + √twPQ)²`. -/
theorem ewPrefixIQ_le (S : Quantum.Sphincs.Disclosures) (pol : DigestPolicy) (A : SAdversary)
    (θ : TVals) {q K : ℕ}
    (hq : IFreeM.IsChargeBound (prefixIQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) q)
    (hK : IFreeM.IsChargeBound (prefixIQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ (pkQ θ) (honQ θ) S))
        (prefixIQ pol A θ) initQ ≤
      (advTermQ q S + twPQ (pkQ θ) (honQ θ) S pol A θ ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ (pkQ θ) (honQ θ) S))
        (prefixIQ pol A θ) initQ ≤
      (advTermQ q S + (runtimeR m0Q).totalWeight .instruments (costWI (pkQ θ) (honQ θ) S)
        (prefixIQ pol A θ) initQ ^ (2⁻¹ : ℝ)) ^ 2 :=
    eventWeight_runtimeR_le (q := q) (K := K) (BadRQ (pkQ θ) (honQ θ) S)
      (labelFree_badRQ (pkQ θ) (honQ θ) S) (fun W m ↦ upClosed_slice_badRQ W m) m0Q
      (empty_not_mem_badRQ m0Q) (fun _ ↦ epsQ S) (fun _ _ ↦ epsQ_ne_top S)
      (fun _ _ W m ↦ freshBound_slice_badRQ W m _)
      (fun c σ ↦ readCostT (BadRQ (pkQ θ) (honQ θ) S) c σ)
      (fun c σ ↦ flipCost (BadRQ (pkQ θ) (honQ θ) S) (hwProgKraus c) 0 σ)
      (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadRQ (pkQ θ) (honQ θ) S) c σ hσ)
      (fun c σ hσ ↦ potential_hwProgKraus_le (BadRQ (pkQ θ) (honQ θ) S) (fun _ ↦ 0)
        (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
      .instruments (prefixIQ pol A θ) hq hK (SubState.basis ())
  rwa [totalWeight_prefixIQ_eq] at h

end data

/-! ## The event bound over the game -/

section event

/-- **The tail term**: `2 · √(2^-128 + price S)`, the tail's two reads graded like adversary
calls. -/
noncomputable def verTermI (S : Quantum.Sphincs.Disclosures) : ℝ≥0∞ :=
  2 * epsQ S ^ (2⁻¹ : ℝ)

/-- **The tail's linear term**: `2 (ε + 2/|Y| + 2/|D|)`. -/
noncomputable def verLinI (S : Quantum.Sphincs.Disclosures) : ℝ≥0∞ :=
  2 * keepCost PairOut Qrom.HashDomain (epsQ S)

variable (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) hashChargeQ q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) signChargeQ signatureLimit)
include hhash hsign

/-- **The calls of the prefix with the data**: at most `q + clsCapI`. -/
theorem calls_prefixIQ (θ : TVals) :
    IFreeM.IsChargeBound (prefixIQ strPol A θ) (portCharge fun _ ↦ 1) (q + clsCapI) := by
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    ((advCalls_prefixIQ strPol A hhash hsign θ).add (clsCalls_prefixIQ strPol A hhash hsign θ))
  rcases a with o | ⟨i, E, ℓ⟩
  · exact le_rfl
  · show 1 ≤ (if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) +
      (if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0)
    split_ifs <;> omega

/-- **The event bound over the ITSR game**: from the bound at the end of the prefix with the data,
each of the tail's two reads costs `√(epsQ S)` in the square root and its linear terms
(`verLinI`): `ew ≤ (advTermQ q S + verTermI S + √(twPQ + verLinI S))²`. -/
theorem ewGameIQ_le (S : Quantum.Sphincs.Disclosures) (θ : TVals) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ (pkQ θ) (honQ θ) S))
        (gameIQ strPol A θ) initQ ≤
      (advTermQ q S + verTermI S +
        (twPQ (pkQ θ) (honQ θ) S strPol A θ + verLinI S) ^ (2⁻¹ : ℝ)) ^ 2 := by
  set pk := pkQ θ
  set hon := honQ θ
  have hpreT := ewPrefixIQ_le S strPol A θ (advCalls_prefixIQ strPol A hhash hsign θ)
    (clsCalls_prefixIQ strPol A hhash hsign θ)
  have hρa := fun a ↦ ((runtimeR m0Q).run₂ .instruments
    (prefixIQ strPol A θ)).posSemidef_branch_apply a initQ_posSemidef
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step
    (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q) (fun s ↦ dbGrade s.1) (fun _ ↦ 1)
    (querySupportedOn_runtimeR_step' (X := PairOut) (Z := Qrom.HashDomain) m0Q) .instruments
    (calls_prefixIQ A hhash hsign θ) querySupportedOn_dbGrade_initQ ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q .instruments
    (prefixIQ strPol A θ) (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le (BadRQ pk hon S)
    (fun W m ↦ upClosed_slice_badRQ W m) m0Q (N := q + clsCapI + 2) (ε := epsQ S)
    (epsQ_ne_top S) (fun W m ↦ freshBound_slice_badRQ W m _) .instruments
    (realizeT θ (tailIT SelMem a)) (chg_tailIQ_oneQ θ a) (chg_tailIQ_nonKeepQ θ a)
    (t := 0 + (q + clsCapI)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments
      (prefixIQ strPol A θ)).branch a initQ).trace.re ≤ 1 :=
    (((runtimeR m0Q).run₂ .instruments
      (prefixIQ strPol A θ)).isCPTNIFamily.tsum_ofReal_trace_re_le
        initQ_posSemidef).trans ofReal_trace_initQ_le_one
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0Q) .instruments
    (hwProjector (BadRQ pk hon S)) (prefixIQ strPol A θ) initQ
  have hm : ∑' j, (∑' a, (if j < 2 then epsQ S else 0) *
      ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixIQ strPol A θ)).branch a
        initQ).trace.re) ^ (2⁻¹ : ℝ) ≤ verTermI S := by
    calc _ ≤ ∑' j, ((if j < 2 then epsQ S else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTermI S := by
          unfold verTermI
          rw [tsum_rpow_inv_two_ite, mul_one, Nat.cast_ofNat]
  have ht : ∑' a, (potential (hwProjector (BadRQ pk hon S))
      (((runtimeR m0Q).run₂ .instruments (prefixIQ strPol A θ)).branch a initQ) +
      ((2 : ℕ) : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S) *
        ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixIQ strPol A θ)).branch a
          initQ).trace.re) ≤
      (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
        (prefixIQ strPol A θ) initQ + verLinI S := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc ((2 : ℕ) : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S) * _
        ≤ ((2 : ℕ) : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S) * 1 := by
          gcongr
      _ = verLinI S := by rw [mul_one, Nat.cast_ofNat]; rfl
  have hpre' : ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (prefixIQ strPol A θ) initQ + verLinI S) ^ (2⁻¹ : ℝ) ≤
      advTermQ q S + (twPQ pk hon S strPol A θ + verLinI S) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := advTermQ q S ^ 2) (δ := 0) (C := verLinI S)
      (b := twPQ pk hon S strPol A θ) (a := (runtimeR m0Q).eventWeight .instruments
        (hwProjector (BadRQ pk hon S)) (prefixIQ strPol A θ) initQ) (by
          rw [Quantum.Qrom.Xmss.sq_rpow_inv_two_eq, add_zero]
          exact hpreT.trans_eq (by rw [add_comm (advTermQ q S)]))
    rwa [Quantum.Qrom.Xmss.sq_rpow_inv_two_eq, zero_add] at h
  have hew : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (gameIQ strPol A θ) initQ = ∑' a, (runtimeR m0Q).eventWeight .instruments
        (hwProjector (BadRQ pk hon S)) (realizeT θ (tailIT SelMem a))
        (((runtimeR m0Q).run₂ .instruments (prefixIQ strPol A θ)).branch a initQ) := by
    rw [gameIQ, gameIT_eq, realizeT_bind₂]
    exact eventWeight_bind₂ (runtimeR m0Q) .instruments (hwProjector (BadRQ pk hon S))
      (prefixIQ strPol A θ) _ initQ_posSemidef
  have hfin : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (gameIQ strPol A θ) initQ ^ (2⁻¹ : ℝ) ≤
      advTermQ q S + verTermI S + (twPQ pk hon S strPol A θ + verLinI S) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
          (prefixIQ strPol A θ) initQ + verLinI S) ^ (2⁻¹ : ℝ) + verTermI S :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ advTermQ q S + (twPQ pk hon S strPol A θ + verLinI S) ^ (2⁻¹ : ℝ) + verTermI S :=
          add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

end event

/-! ## Averaged over the hidden values -/

section average

/-- **The averaged tail term**: `√(2² epsBarQ)`. -/
noncomputable def verBarI : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ 2 * epsBarQ) ^ (2⁻¹ : ℝ)

/-- **The averaged tail's linear term**: `2 (epsBarQ + 2/|Y| + 2/|D|)`. -/
noncomputable def verLinBarI : ℝ≥0∞ :=
  2 * keepCost PairOut Qrom.HashDomain epsBarQ

theorem verTermI_eq (S : Quantum.Sphincs.Disclosures) :
    verTermI S = ((2 : ℝ≥0∞) ^ 2 * epsQ S) ^ (2⁻¹ : ℝ) := by
  have h := natCast_mul_rpow_inv_two 2 (epsQ S)
  rwa [Nat.cast_ofNat] at h

variable (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) hashChargeQ q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) signChargeQ signatureLimit)
include hhash hsign

/-- **The event weight at the end of the ITSR game, averaged** (Minkowski over the hidden values):
with the prefix's averaged classical cost at most `T`,
`E ew ≤ (advBarQ q + verBarI + √(T + verLinBarI))²`. -/
theorem uavg_ewGameIQ_le {T : ℝ≥0∞}
    (hcost : uavg (fun θ : TVals ↦ twPQ (pkQ θ) (honQ θ) (starQ θ) strPol A θ) ≤ T) :
    uavg (fun θ : TVals ↦ (runtimeR m0Q).eventWeight .instruments
      (hwProjector (BadRQ (pkQ θ) (honQ θ) (starQ θ))) (gameIQ strPol A θ) initQ) ≤
      (advBarQ q + verBarI + (T + verLinBarI) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (uavg_mono fun θ ↦ ewGameIQ_le A hhash hsign (starQ θ) θ).trans ?_
  simp only [advTermQ_eq, verTermI_eq]
  refine (uavg_sq_rpow_add3_le _ _ _).trans (pow_le_pow_left₀ zero_le
    (add_le_add (add_le_add ?_ ?_) ?_) 2)
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_const_mul, uavg_const_mul]
    gcongr
    exact uavg_epsQ_le
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_const_mul]
    gcongr
    exact uavg_epsQ_le
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_add]
    refine add_le_add hcost ?_
    unfold verLinI verLinBarI keepCost
    rw [uavg_const_mul, uavg_add, uavg_add, uavg_const, uavg_const]
    gcongr
    exact uavg_epsQ_le

end average

end Quantum.StdModel.Sphincs.SphItsr

end
