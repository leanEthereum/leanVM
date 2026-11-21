module

public import Quantum.Xmss.Assembly.CostLift
public import Quantum.Xmss.Assembly.Masses
public import Quantum.Xmss.Hybrid.Mismatch
public import Quantum.Sponge.Oracle.Hardwired.Potential

@[expose] public section

/-!
# The joint count of the selecting reads, by a diagonal potential

Security's debt `encJoint` bounds the state-weighted counts `cntW` of the selecting reads of all
trials of all keys, summed along the event-bound program. The proof is a potential argument
(design §4): a diagonal potential `Φ = diag φ` on the register of runtime 2 with record ports,
`φ` the codeword counts `msgCwCount` of the unselected keys (at most the message-slot cells,
`sum_msgCwCount_le`), grows by at most one per sponge and program call and drops at a trial read
by `ρ_c` times its count.

* **Telescoping on an invariant** (`totalWeight_le_potential_of_forallQueries`): the drops of a
  potential along a run, asked only on the call inputs supported on an invariant.
* **On `runtimeR`** (`totalWeight_le_diagPotential_runtimeR`): a diagonal potential that does not
  read the memory label is kept by the record ports (`tsum_potential_recStep_diag`); the charges
  of the other ports are `portCh cS cR cP`. A one-cell Lipschitz potential gives the sponge
  charge `tr σ` (`tsum_potential_sponge_le`); the trace charges of the sponge and program ports
  sum to `(q + P) tr ρ` (`totalWeight_portCh_trace_le`).
* **The joint count** (`totalWeight_le_jointPotential`, `totalWeight_le_jointPotential_init`):
  if every read `c` lowers the potential by `2^-22 cnt c` up to a charge `cR c`, and every sponge
  call raises it by at most `tr σ + cS`, then `Σ cnt ≤ 2^22 (q + P) + 2^22 Σ (cS + cR)`.
* **A trial read, weighted** (`survive_readH_weighted_le`, `drop_of_survive`): EncCost's survival
  bound applied to `N σ N`, `N = diag √n` for a count `n` that sees neither the read cell nor the
  memory (`OffCell`, so `N` commutes with the read): the `n`-weighted survival
  `w_n - ρ e_n + p_n + 2 √(ρ e_n p_n)`, hence the drop `2^-22 e_n` up to `3 p_n` for
  `ρ_c ≥ 2^-21`; `p_n ≤ C tr (P σ)` where `n ≤ C` (`sum_not_weighted_le`).
* **Averages** (`uavg_ite_le_add_mul`, `uavg_ite_const_mul_le`, `uavg_ite_cost_le`): an Enc term
  `cnt ≤ a + b m` linear in the recorded mass `m` averages over the good tables without Jensen;
  the classical costs `(√E + √m)² + p` average to `(√(E₀ + β mc) + √mc)² + pc`.
-/

universe u v w u₁ v₁

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid

/-! ## Telescoping a potential on the calls of an invariant -/

section generic

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {Λ : LocalSig.{u, v}}
  (I : Λ.Interp) {Ω : QReg → Type w} {A : QReg} {Zp : Type*} [Fintype Zp]

/-- **The drops of a potential along a run, on an invariant.** If on every positive semidefinite
input `σ` of a port `i` satisfying `Inv i` the drop `w i σ` and the potentials of the outputs are
at most the potential of `σ` plus the charge `c i σ`, and the inputs of all calls of `x` satisfy
`Inv` (`ForallQueries` of `P`), then the drops along the run are at most the initial potential
plus the charges. -/
theorem totalWeight_le_potential_of_forallQueries (K : Matrix Zp R.D ℂ)
    (P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop)
    (Inv : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → Prop)
    (hP : ∀ i E σ, P i E σ → Inv i (MatrixMap.traceRight (spec.In i × R.D) E σ))
    (w c : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (h : ∀ i σ, σ.PosSemidef → Inv i σ →
      w i σ + ∑' r, potential K ((R.step i).branch r σ) ≤ potential K σ + c i σ)
    (x : QuantumComp Λ spec Ω A) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hx : R.ForallQueries I P x ρ) :
    R.totalWeight I w x ρ ≤ potential K ρ + R.totalWeight I c x ρ := by
  classical
  have hw : R.totalWeight I w x ρ =
      R.totalWeight I (fun i σ ↦ if Inv i σ then w i σ else 0) x ρ :=
    totalWeight_congr_of_forallQueries R I (fun i E σ hσ ↦ by rw [ite_eq_left (hP i E σ hσ)]) x ρ hx
  have hc : R.totalWeight I c x ρ =
      R.totalWeight I (fun i σ ↦ if Inv i σ then c i σ else ⊤) x ρ :=
    totalWeight_congr_of_forallQueries R I (fun i E σ hσ ↦ by rw [ite_eq_left (hP i E σ hσ)]) x ρ hx
  rw [hw, hc]
  refine ENNReal.tsum_le_of_sum_range_le fun N ↦
    (R.sum_range_queryWeight_le_potential I x N (fun _ ↦ K)
      (fun _ i σ ↦ if Inv i σ then w i σ else 0) (fun _ i σ ↦ if Inv i σ then c i σ else ⊤)
      (fun _ _ i σ hσ ↦ ?_) hρ).trans (add_le_add le_rfl (ENNReal.sum_le_tsum _))
  by_cases hi : Inv i σ
  · simp only [ite_eq_left hi]
    exact h i σ hσ hi
  · simp only [ite_eq_right hi, zero_add, add_top]
    exact le_top

end generic

/-! ## Diagonal potentials on the register of runtime 2 with record ports -/

section runtimeR

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']

/-- An operator on `α × β` has no diagonal weight outside `Inv` on `β`. -/
def DiagOn {α β : Type*} (Inv : β → Prop) (σ : Matrix (α × β) (α × β) ℂ) : Prop :=
  ∀ a, ¬Inv a.2 → σ a a = 0

/-- The Gram operator of the diagonal square root of `φ ≥ 0` is `diag φ`. -/
theorem diagPot_sqrt_gram {β : Type*} [DecidableEq β] [Fintype β] {φ : β → ℝ}
    (hφ : ∀ s, 0 ≤ φ s) :
    (diagPot fun s ↦ √(φ s))ᴴ * diagPot (fun s ↦ √(φ s)) = diagPot φ := by
  simp only [diagPot, diagonal_conjTranspose, diagonal_mul_diagonal]
  congr 1
  funext s
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hφ s)]

/-- `diag φ` beside an identity is the diagonal of `φ` on the second coordinate. -/
theorem one_kronecker_diagPot {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (φ : β → ℝ) :
    (1 : Matrix α α ℂ) ⊗ₖ diagPot φ = diagonal fun q : α × β ↦ (φ q.2 : ℂ) := by
  simp only [diagPot, ← diagonal_one, diagonal_kronecker_diagonal, one_mul]

/-- **A diagonal potential is the `φ`-weighted diagonal**: `tr ((1 ⊗ diag φ) σ) = ∑ φ σ_qq`. -/
theorem potential_diagPot_sqrt {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {φ : β → ℝ} (hφ : ∀ s, 0 ≤ φ s) (σ : Matrix (α × β) (α × β) ℂ) :
    potential (diagPot fun s ↦ √(φ s)) σ = ENNReal.ofReal (∑ q, φ q.2 * (σ q q).re) := by
  rw [potential_eq, diagPot_sqrt_gram hφ, one_kronecker_diagPot, Matrix.trace, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Matrix.diag_apply, diagonal_mul, Complex.re_ofReal_mul]

/-- An operator whose nonzero entries keep `f` commutes with `diagonal f`. -/
theorem diagonal_mul_comm_of {n : Type*} [Fintype n] [DecidableEq n] (f : n → ℂ)
    (K : Matrix n n ℂ) (h : ∀ a a', K a' a ≠ 0 → f a' = f a) :
    diagonal f * K = K * diagonal f := by
  ext a' a
  rw [diagonal_mul, mul_diagonal]
  by_cases hK : K a' a = 0
  · rw [hK, mul_zero, zero_mul]
  · rw [h a a' hK, mul_comm]

/-- A potential that does not read the memory label: the recorded coordinates are ignored. -/
def PotLabelFree (φ : HwReg X Z (Finset S × M') → ℝ) : Prop :=
  ∀ (D : DbReg X Z) (W : Hw X Z) (T T' : Finset S) (m : M'), φ (D, W, (T, m)) = φ (D, W, (T', m))

/-- **A record port keeps a label-free diagonal potential.** -/
theorem tsum_potential_recStep_diag {φ : HwReg X Z (Finset S × M') → ℝ} (hφ0 : ∀ s, 0 ≤ φ s)
    (hφ : PotLabelFree φ) (T : Finset S)
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' r, potential (diagPot fun s ↦ √(φ s)) ((recStep (X := X) (Z := Z) T).branch r σ) ≤
      potential (diagPot fun s ↦ √(φ s)) σ := by
  simp only [recStep_branch]
  set K := diagPot fun s : HwReg X Z (Finset S × M') ↦ √(φ s)
  have hΦ : (1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K) =
      diagonal fun q : Unit × HwReg X Z (Finset S × M') ↦ (φ q.2 : ℂ) := by
    rw [diagPot_sqrt_gram hφ0, one_kronecker_diagPot]
  have hcomm : ∀ m, (1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K) * recKraus T m =
      recKraus T m * ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K)) := fun m ↦ by
    rw [hΦ]
    refine diagonal_mul_comm_of _ _ fun a a' h ↦ ?_
    rw [eq_of_recKraus_ne_zero (u := a.1) (u' := a'.1) (s := a.2) (s' := a'.2) h]
    exact congrArg _ (hφ a.2.1 a.2.2.1 (a.2.2.2.1 ∪ T) a.2.2.2.1 a.2.2.2.2)
  have hsum : ∑ m, (recKraus (X := X) (Z := Z) T m)ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K)) * recKraus T m =
      (1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K) := by
    rw [Finset.sum_congr rfl fun m _ ↦ show (recKraus (X := X) (Z := Z) T m)ᴴ *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K)) * recKraus T m =
        (recKraus T m)ᴴ * recKraus T m * ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K)) by
      rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc], ← Finset.sum_mul, sum_recKraus,
      Matrix.one_mul]
  have hd := drop_of_posSemidef (recKraus (X := X) (Z := Z) T) K K 0 hσ (by
    rw [add_zero, hsum, sub_self]
    exact PosSemidef.zero)
  rw [Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero, add_zero,
    add_zero] at hd
  exact le_add_self.trans hd

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]

omit [Nonempty X] [Nonempty Z] in
/-- **A sponge port raises a one-cell Lipschitz diagonal potential by at most the trace**
(`posSemidef_diagonalPotential_drop`). -/
theorem tsum_potential_sponge_le {M : Type} [Fintype M] [DecidableEq M] {φ : HwReg X Z M → ℝ}
    (hφ0 : ∀ s, 0 ≤ φ s) (hφ : OneCellLipschitz φ) (W₀ : Hw X Z) (m₀ : M) (p : SpongePort)
    {σ : Matrix (spongeIn X Z p × HwReg X Z M) (spongeIn X Z p × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' _r : Unit, potential (diagPot fun s ↦ √(φ s))
        (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U p) σ) ≤
      potential (diagPot fun s ↦ √(φ s)) σ + ENNReal.ofReal σ.trace.re := by
  have hd := drop_of_posSemidef (fun _ : Unit ↦ (spongeHardwired X Z W₀ m₀).U p)
    (diagPot fun s ↦ √(φ s)) (diagPot fun s ↦ √(φ s)) 1 hσ (by
      rw [Fintype.sum_unique, diagPot_sqrt_gram hφ0]
      exact posSemidef_diagonalPotential_drop hφ W₀ m₀ p)
  rw [Matrix.one_mul] at hd
  exact le_add_self.trans hd

/-- The program ports of runtime 2 with record ports. -/
def progPort : (recHwSpec X Z S M').Port → Bool
  | .inl (.inr _) => true
  | _ => false

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] [AddCommGroup X] [AddCommGroup Z]
  [Nonempty X] [Nonempty Z] in
/-- The program charge of runtime 2 with record ports counts the program ports. -/
theorem extProgCharge_eq_progPort :
    extProgCharge X Z (Finset S × M') (recSpec S M') =
      fun i ↦ if progPort (X := X) (Z := Z) (S := S) (M' := M') i = true then 1 else 0 := by
  funext i
  rcases i with ((_ | _) | _) | _ <;> rfl

variable (X Z S M') in
/-- The trace at the sponge ports. -/
noncomputable def spongeTr (i : (recHwSpec X Z S M').Port)
    (σ : Matrix ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M')))
      ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M'))) ℂ) : ℝ≥0∞ :=
  if extCls X Z (Finset S × M') (recSpec S M') i then 0 else ENNReal.ofReal σ.trace.re

variable (X Z S M') in
/-- The trace at the program ports. -/
noncomputable def progTr (i : (recHwSpec X Z S M').Port)
    (σ : Matrix ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M')))
      ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M'))) ℂ) : ℝ≥0∞ :=
  if progPort i then ENNReal.ofReal σ.trace.re else 0

variable (X Z S M') in
/-- **Charges on the ports of runtime 2 with record ports**: `cS` at the sponge ports, `cR` at the
read ports, `cP` at the program ports, nothing at the record ports. -/
noncomputable def portCh
    (cS : ∀ p : SpongePort, Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cP : HwProg X Z → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞) :
    ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M')))
        ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M'))) ℂ → ℝ≥0∞
  | .inl (.inl (.inl p)) => cS p
  | .inl (.inl (.inr c)) => cR c
  | .inl (.inr c) => cP c
  | .inr _ => fun _ ↦ 0

variable {Λ : LocalSig.{u, v}} {Ω : QReg → Type w} {A : QReg}

/-- **The drops of a diagonal potential along a run of `runtimeR`.** Let `φ ≥ 0` not read the
memory label, let every sponge, read and program call raise the potential `diag φ` by at most its
charge (`cS`, `cR`, `cP`), a read `c` also paying its drop `dR c`, on the inputs supported on
`Inv`, which the inputs of all calls of `x` are (record ports keep the potential). Then the drops
along the run are at most the initial potential plus the charges along the run. -/
theorem totalWeight_le_diagPotential_runtimeR (m₀ : Finset S × M')
    {φ : HwReg X Z (Finset S × M') → ℝ} (hφ0 : ∀ s, 0 ≤ φ s) (hlab : PotLabelFree φ)
    (Inv : HwReg X Z (Finset S × M') → Prop)
    (dR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cS : ∀ p : SpongePort, Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cP : HwProg X Z → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (hS : ∀ p (σ : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
        (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → DiagOn Inv σ →
      ∑' _r : Unit, potential (diagPot fun s ↦ √(φ s))
          (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + cS p σ)
    (hR : ∀ c σ, σ.PosSemidef → DiagOn Inv σ →
      dR c σ + ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + cR c σ)
    (hP : ∀ c σ, σ.PosSemidef → DiagOn Inv σ →
      ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwProgKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + cP c σ)
    (I : Λ.Interp) (x : QuantumComp Λ (recHwSpec X Z S M') Ω A)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M'))) (A × QReg.of (HwReg X Z (Finset S × M')))
      ℂ} (hρ : ρ.PosSemidef)
    (hx : (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) (fun _ ↦ True) Inv) x ρ) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost dR fun _ _ ↦ 0)) x ρ ≤
      potential (diagPot fun s ↦ √(φ s)) ρ +
        (runtimeR m₀).totalWeight I (portCh X Z S M' cS cR cP) x ρ := by
  refine totalWeight_le_potential_of_forallQueries (runtimeR m₀) I
    (diagPot fun s ↦ √(φ s)) (invSupp (runtimeR m₀) (fun _ ↦ True) Inv)
    (fun _ σ ↦ DiagOn Inv σ)
    (fun _ _ σ hσ b hb ↦ traceRight_diag_eq_zero fun e ↦ hσ trivial (b, e) hb)
    (extWeight (hwCost dR fun _ _ ↦ 0)) (portCh X Z S M' cS cR cP) (fun i σ hσ hI ↦ ?_) x hρ hx
  rcases i with ((p | c) | c) | T
  · have hb : ∀ r : Unit, ((runtimeR m₀).step (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ p r) σ
    simp only [portCh, extWeight, sumWeight, hwCost, zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans (hS p σ hσ hI)
  · have hb : ∀ r, ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) σ
    simp only [portCh, extWeight, sumWeight, hwCost]
    exact (le_of_eq (congrArg (dR c σ + ·) (tsum_congr fun r ↦ congrArg _ (hb r)))).trans
      (hR c σ hσ hI)
  · have hb : ∀ r, ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
    simp only [portCh, extWeight, sumWeight, hwCost, zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans (hP c σ hσ hI)
  · simp only [portCh, extWeight, sumWeight, zero_add, add_zero]
    exact tsum_potential_recStep_diag hφ0 hlab T hσ

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- Charges add portwise. -/
theorem portCh_add
    (cS₁ cS₂ : ∀ p : SpongePort, Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cR₁ cR₂ : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cP₁ cP₂ : HwProg X Z → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞) :
    portCh X Z S M' (fun p σ ↦ cS₁ p σ + cS₂ p σ) (fun c σ ↦ cR₁ c σ + cR₂ c σ)
        (fun c σ ↦ cP₁ c σ + cP₂ c σ) =
      fun i σ ↦ portCh X Z S M' cS₁ cR₁ cP₁ i σ + portCh X Z S M' cS₂ cR₂ cP₂ i σ := by
  funext i σ
  rcases i with ((_ | _) | _) | _
  · rfl
  · rfl
  · rfl
  · exact (add_zero 0).symm

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- The trace charges at the sponge and program ports are `spongeTr + progTr`. -/
theorem portCh_trace_eq :
    portCh X Z S M' (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (fun _ _ ↦ 0)
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) =
      fun i σ ↦ spongeTr X Z S M' i σ + progTr X Z S M' i σ := by
  funext i σ
  rcases i with ((_ | _) | _) | _
  · simp only [portCh, spongeTr, progTr, extCls, hwCls, progPort, Bool.false_eq_true,
      ↓reduceIte, add_zero]
    rfl
  · simp only [portCh, spongeTr, progTr, extCls, hwCls, progPort, Bool.false_eq_true,
      ↓reduceIte, add_zero]
  · simp only [portCh, spongeTr, progTr, extCls, hwCls, progPort, ↓reduceIte, zero_add]
    rfl
  · simp only [portCh, spongeTr, progTr, extCls, progPort, Bool.false_eq_true, ↓reduceIte,
      add_zero]

/-- **The trace charges at the sponge and program ports**: with at most `q` sponge calls and `P`
program calls, at most `(q + P) tr ρ` along the run. -/
theorem totalWeight_portCh_trace_le (m₀ : Finset S × M') (I : Λ.Interp)
    (x : QuantumComp Λ (recHwSpec X Z S M') Ω A) {q P : ℕ}
    (hq : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (hp : IFreeM.IsChargeBound x (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M')))
      P)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M'))) (A × QReg.of (HwReg X Z (Finset S × M')))
      ℂ} (hρ : ρ.PosSemidef) :
    (runtimeR m₀).totalWeight I (portCh X Z S M' (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
        (fun _ _ ↦ 0) (fun _ σ ↦ ENNReal.ofReal σ.trace.re)) x ρ ≤
      (q + P : ℕ) * ENNReal.ofReal ρ.trace.re := by
  refine (totalWeight_le_totalWeight (runtimeR m₀) I
    (w' := fun i σ ↦ spongeTr X Z S M' i σ + progTr X Z S M' i σ)
    (fun i σ _ ↦ le_of_eq (congrFun (congrFun portCh_trace_eq i) σ)) x hρ).trans ?_
  refine (le_of_eq (totalWeight_add_weight (runtimeR m₀) I (spongeTr X Z S M') (progTr X Z S M')
    x ρ)).trans ?_
  rw [Nat.cast_add, add_mul]
  have hs := totalWeight_trace_le_of_isChargeBound (runtimeR m₀) I _ x hq hρ
  rw [extProgCharge_eq_progPort] at hp
  have hpr := totalWeight_trace_le_of_isChargeBound' (runtimeR m₀) I
    (fun i ↦ progPort i = true) x hp hρ
  exact add_le_add hs hpr

/-- **The initial potential** of runtime 2 with record ports beside a basis state: `φ` at the
empty register. -/
theorem potential_basis_init {B : Type} [Fintype B] [DecidableEq B] (m₀ : Finset S × M')
    {φ : HwReg X Z (Finset S × M') → ℝ} (hφ0 : ∀ s, 0 ≤ φ s) (u : B) :
    potential (diagPot fun s ↦ √(φ s))
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) =
      ENNReal.ofReal (φ ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀)) := by
  rw [potential_diagPot_sqrt hφ0]
  congr 1
  have hinit : (runtimeR (X := X) (Z := Z) m₀).init.matrix =
      Matrix.single ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀)
        ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) 1 := rfl
  rw [hinit, SubState.matrix_basis, single_kronecker_single, one_mul,
    Finset.sum_eq_single (u, ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀))]
  · simp
  · intro b _ hb
    rw [Matrix.single_apply, ite_eq_right fun h ↦ hb h.1.symm]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The initial state of runtime 2 with record ports beside a basis state has trace one. -/
theorem ofReal_trace_basis_init {B : Type} [Fintype B] [DecidableEq B] (m₀ : Finset S × M')
    (u : B) :
    ENNReal.ofReal ((SubState.basis u).matrix ⊗ₖ
      (runtimeR (X := X) (Z := Z) m₀).init.matrix).trace.re = 1 := by
  rw [Matrix.trace_kronecker, SubState.trace_basis, one_mul]
  exact (congrArg (fun t : ℂ ↦ ENNReal.ofReal t.re) (SubState.trace_basis _)).trans
    (by rw [Complex.one_re, ENNReal.ofReal_one])

/-- **The joint count from a diagonal potential.** Let `φ ≥ 0` not read the memory label; let
every sponge call raise `diag φ` by at most its trace plus `cS`, every program call by at most its
trace, and every read `c` lower it by at least `2^-22 cnt c` up to `cR c`, on the inputs supported
on `Inv`, which all calls of `x` from `ρ` are; let `ρ` have potential `0` and trace at most `1`.
With at most `q` sponge calls and `P` program calls, the count `cnt` along the run is at most
`2^22 (q + P) + 2^22 Σ (cS + cR)`. -/
theorem totalWeight_le_jointPotential (m₀ : Finset S × M')
    {φ : HwReg X Z (Finset S × M') → ℝ} (hφ0 : ∀ s, 0 ≤ φ s) (hlab : PotLabelFree φ)
    (Inv : HwReg X Z (Finset S × M') → Prop)
    (cnt : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cS : ∀ p : SpongePort, Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (hS : ∀ p (σ : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
        (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → DiagOn Inv σ →
      ∑' _r : Unit, potential (diagPot fun s ↦ √(φ s))
          (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + (ENNReal.ofReal σ.trace.re + cS p σ))
    (hR : ∀ c σ, σ.PosSemidef → DiagOn Inv σ →
      (2 ^ 22 : ℝ≥0∞)⁻¹ * cnt c σ +
          ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + cR c σ)
    (hP : ∀ c σ, σ.PosSemidef → DiagOn Inv σ →
      ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwProgKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + ENNReal.ofReal σ.trace.re)
    (I : Λ.Interp) (x : QuantumComp Λ (recHwSpec X Z S M') Ω A) {q P : ℕ}
    (hq : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (hp : IFreeM.IsChargeBound x (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M')))
      P)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M'))) (A × QReg.of (HwReg X Z (Finset S × M')))
      ℂ} (hρ : ρ.PosSemidef) (hp0 : potential (diagPot fun s ↦ √(φ s)) ρ = 0)
    (htr : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hx : (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) (fun _ ↦ True) Inv) x ρ) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost cnt fun _ _ ↦ 0)) x ρ ≤
      2 ^ 22 * (q + P : ℕ) + 2 ^ 22 * (runtimeR m₀).totalWeight I
        (portCh X Z S M' cS cR fun _ _ ↦ 0) x ρ := by
  have h := totalWeight_le_diagPotential_runtimeR m₀ hφ0 hlab Inv
    (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * cnt c σ)
    (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ) (fun c σ ↦ 0 + cR c σ)
    (fun _ σ ↦ ENNReal.ofReal σ.trace.re + 0) (fun p σ hσ hI ↦ hS p σ hσ hI)
    (fun c σ hσ hI ↦ (hR c σ hσ hI).trans_eq (by rw [zero_add]))
    (fun c σ hσ hI ↦ (hP c σ hσ hI).trans_eq (by rw [add_zero])) I x hρ hx
  have hlow : (2 ^ 22 : ℝ≥0∞)⁻¹ *
      (runtimeR m₀).totalWeight I (extWeight (hwCost cnt fun _ _ ↦ 0)) x ρ ≤
      (runtimeR m₀).totalWeight I
        (extWeight (hwCost (fun c σ ↦ (2 ^ 22 : ℝ≥0∞)⁻¹ * cnt c σ) fun _ _ ↦ 0)) x ρ := by
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m₀) I _
      (extWeight (hwCost cnt fun _ _ ↦ 0)) x ρ).symm).trans
      (totalWeight_le_totalWeight (runtimeR m₀) I (fun i σ _ ↦ ?_) x hρ)
    rcases i with ((_ | _) | _) | _
    · exact le_of_eq (mul_zero _)
    · exact le_rfl
    · exact le_of_eq (mul_zero _)
    · exact le_of_eq (mul_zero _)
  have hsplit := (totalWeight_le_totalWeight (runtimeR m₀) I
    (w := portCh X Z S M' (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ) (fun c σ ↦ 0 + cR c σ)
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re + 0))
    (w' := fun i σ ↦ portCh X Z S M' (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (fun _ _ ↦ 0)
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ + portCh X Z S M' cS cR (fun _ _ ↦ 0) i σ)
    (fun i σ _ ↦ le_of_eq (congrFun (congrFun (portCh_add _ _ _ _ _ _) i) σ)) x hρ).trans
    (le_of_eq (totalWeight_add_weight (runtimeR m₀) I _ _ x ρ))
  have ht := (totalWeight_portCh_trace_le m₀ I x hq hp hρ).trans
    ((mul_le_mul_of_nonneg_left htr zero_le).trans_eq (mul_one _))
  have hmain := hlow.trans (h.trans ((add_le_add (le_of_eq hp0) le_rfl).trans_eq (zero_add _)
    |>.trans (hsplit.trans (add_le_add ht le_rfl))))
  have h2 : (2 ^ 22 : ℝ≥0∞) ≠ 0 := by positivity
  have h2' : (2 ^ 22 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : ∀ w : ℝ≥0∞, w = 2 ^ 22 * ((2 ^ 22 : ℝ≥0∞)⁻¹ * w) := fun w ↦ by
    rw [← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
  exact (e _).trans_le ((mul_le_mul_of_nonneg_left hmain zero_le).trans_eq (mul_add _ _ _))

/-- **The joint count from the initial state** (`totalWeight_le_jointPotential` with `φ = 0` at
the empty register): from a basis state beside the initial register. -/
theorem totalWeight_le_jointPotential_init (m₀ : Finset S × M')
    {φ : HwReg X Z (Finset S × M') → ℝ} (hφ0 : ∀ s, 0 ≤ φ s) (hlab : PotLabelFree φ)
    (hφi : φ ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) = 0)
    (Inv : HwReg X Z (Finset S × M') → Prop)
    (cnt : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cS : ∀ p : SpongePort, Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (hS : ∀ p (σ : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
        (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → DiagOn Inv σ →
      ∑' _r : Unit, potential (diagPot fun s ↦ √(φ s))
          (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + (ENNReal.ofReal σ.trace.re + cS p σ))
    (hR : ∀ c σ, σ.PosSemidef → DiagOn Inv σ →
      (2 ^ 22 : ℝ≥0∞)⁻¹ * cnt c σ +
          ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + cR c σ)
    (hP : ∀ c σ, σ.PosSemidef → DiagOn Inv σ →
      ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwProgKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(φ s)) σ + ENNReal.ofReal σ.trace.re)
    (I : Λ.Interp) {B : Type} [Fintype B] [DecidableEq B] (u : B)
    (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B)) {q P : ℕ}
    (hq : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (hp : IFreeM.IsChargeBound x (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M')))
      P)
    (hx : (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) (fun _ ↦ True) Inv) x
      ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost cnt fun _ _ ↦ 0)) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      2 ^ 22 * (q + P : ℕ) + 2 ^ 22 * (runtimeR m₀).totalWeight I
        (portCh X Z S M' cS cR fun _ _ ↦ 0) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) :=
  totalWeight_le_jointPotential m₀ hφ0 hlab Inv cnt cS cR hS hR hP I x hq hp
    ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
    ((potential_basis_init m₀ hφ0 u).trans
      ((congrArg ENNReal.ofReal hφi).trans ENNReal.ofReal_zero))
    (ofReal_trace_basis_init m₀ u).le hx

end runtimeR

/-! ## Survival of a trial read, weighted by a count that does not see the read cell -/

section weighted

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

/-- A weight on the register that sees neither the cell `z` of `h` nor the memory. -/
def OffCell (z : Z) (n : HwReg X Z M → ℝ) : Prop :=
  ∀ s s' : HwReg X Z M, (∀ b, b ≠ z → s'.1.1 b = s.1.1 b) → s'.1.2 = s.1.2 → s'.2.1 = s.2.1 →
    n s' = n s

omit [Fintype M] in
/-- A nonzero entry of a read of the cell `z` of `h` keeps the other cells, the `k`, `k'`
databases and the hardwired cells. -/
theorem readKrausH_ne_zero_rest (z : Z) (upd : M → Option X → M) (r : Option X × M)
    {s' s : HwReg X Z M} (h : readKrausH z upd r s' s ≠ 0) :
    (∀ b, b ≠ z → s'.1.1 b = s.1.1 b) ∧ s'.1.2 = s.1.2 ∧ s'.2.1 = s.2.1 := by
  rw [readKrausH, clsKraus_apply] at h
  split_ifs at h with hc
  · rw [kroneckerMap_apply] at h
    have h₁ := left_ne_zero_of_mul h
    have h₂ := right_ne_zero_of_mul h
    refine ⟨cellRead_apply_ne_zero h₁, ?_, by rw [hc.2]⟩
    by_contra hne
    exact h₂ (Matrix.one_apply_ne hne)
  · exact absurd rfl h

/-- The diagonal operator of the square roots of a weight on the register. -/
noncomputable def sqrtDiag (n : HwReg X Z M → ℝ) :
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ :=
  diagonal fun q ↦ ((√(n q.2) : ℝ) : ℂ)

omit [Fintype M] in
theorem sqrtDiag_conjTranspose (n : HwReg X Z M → ℝ) : (sqrtDiag n)ᴴ = sqrtDiag n := by
  rw [sqrtDiag, diagonal_conjTranspose]
  congr 1
  funext q
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

/-- The read of the cell `z` of `h` commutes with the square roots of a weight off that cell. -/
theorem sqrtDiag_mul_readH (z : Z) (upd : M → Option X → M) {n : HwReg X Z M → ℝ}
    (hn : OffCell z n) (r : Option X × M) :
    sqrtDiag n * hwReadKraus (.readH z upd) r = hwReadKraus (.readH z upd) r * sqrtDiag n := by
  refine diagonal_mul_comm_of _ _ fun a a' h ↦ ?_
  obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
  obtain ⟨h₁, h₂, h₃⟩ := readKrausH_ne_zero_rest z upd r h'
  rw [hn a.2 a'.2 h₁ h₂ h₃]

/-- The diagonal of `N σ N` for the square roots `N` of a nonnegative weight. -/
theorem re_sqrtDiag_conj_apply {n : HwReg X Z M → ℝ} (hn0 : ∀ s, 0 ≤ n s)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) (q : Unit × HwReg X Z M) :
    ((sqrtDiag n * σ * sqrtDiag n) q q).re = n q.2 * (σ q q).re := by
  rw [sqrtDiag, mul_diagonal, diagonal_mul, mul_comm, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hn0 q.2), Complex.re_ofReal_mul]

/-- The trace of `N A N` is the `n`-weighted diagonal of `A`. -/
theorem re_trace_sqrtDiag_conj {n : HwReg X Z M → ℝ} (hn0 : ∀ s, 0 ≤ n s)
    (A : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    (sqrtDiag n * A * sqrtDiag n).trace.re = ∑ q, n q.2 * (A q q).re := by
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_congr rfl fun q _ ↦ re_sqrtDiag_conj_apply hn0 A q

/-- **Survival of a read of an `h` cell, weighted** (`survive_readH_le` on `N σ N`, `N` the square
roots of a weight `n ≥ 0` that sees neither the read cell nor the memory, so commutes with the
read): the `n`-weighted outcomes that keep the memory in `T` weigh at most
`w_n - ρ e_n + p_n + 2 √(ρ e_n p_n)`, with `w_n`, `e_n` and `p_n` the `n`-weighted memories in `T`,
states of `SR` and other states. -/
theorem survive_readH_weighted_le [Nonempty X] (z : Z) (upd : M → Option X → M) (T : Set M)
    [DecidablePred (· ∈ T)] (good : X → Prop) [DecidablePred good] {ρ : ℝ}
    (hρ : ((Finset.univ.filter good).card : ℝ) / Fintype.card X = ρ)
    (hupd : ∀ m ∈ T, ∀ v, upd m (some v) ∈ T ↔ ¬ good v)
    (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → s.1.1 z = none ∧ s.2.1.1 z = none ∧ s.2.2 ∈ T)
    {n : HwReg X Z M → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    (∑ r : Option X × M, if upd r.2 r.1 ∈ T then
        ∑ q, n q.2 * ((MatrixMap.conj (hwReadKraus (.readH z upd) r) σ) q q).re else 0) ≤
      (∑ q, if q.2.2.2 ∈ T then n q.2 * (σ q q).re else 0) -
        ρ * (∑ q, if SR q.2 then n q.2 * (σ q q).re else 0) +
        (∑ q, if SR q.2 then 0 else n q.2 * (σ q q).re) +
        2 * √(ρ * (∑ q, if SR q.2 then n q.2 * (σ q q).re else 0) *
          (∑ q, if SR q.2 then 0 else n q.2 * (σ q q).re)) := by
  set N := sqrtDiag n
  have hσ' : (N * σ * N).PosSemidef := by
    have := hσ.mul_mul_conjTranspose_same (sqrtDiag n)
    rwa [sqrtDiag_conjTranspose] at this
  have h := survive_readH_le z upd T good hρ hupd SR hSR hσ'
  have hdiag : ∀ q, ((N * σ * N) q q).re = n q.2 * (σ q q).re := re_sqrtDiag_conj_apply hn0 σ
  have hT : (∑ q, if q.2.2.2 ∈ T then ((N * σ * N) q q).re else 0) =
      ∑ q, if q.2.2.2 ∈ T then n q.2 * (σ q q).re else 0 :=
    Finset.sum_congr rfl fun q _ ↦ by rw [hdiag]
  have hS : (∑ q, if SR q.2 then ((N * σ * N) q q).re else 0) =
      ∑ q, if SR q.2 then n q.2 * (σ q q).re else 0 :=
    Finset.sum_congr rfl fun q _ ↦ by rw [hdiag]
  have hp : (readPs SR * (N * σ * N)).trace.re = ∑ q, if SR q.2 then 0 else n q.2 * (σ q q).re := by
    rw [readPs, Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Matrix.diag_apply, diagonal_mul]
    by_cases hq : SR q.2
    · simp [hq]
    · simp only [hq, ↓reduceIte, one_mul]
      exact hdiag q
  have hL : ∀ r, (MatrixMap.conj (hwReadKraus (.readH z upd) r) (N * σ * N)).trace.re =
      ∑ q, n q.2 * ((MatrixMap.conj (hwReadKraus (.readH z upd) r) σ) q q).re := fun r ↦ by
    have hc := sqrtDiag_mul_readH z upd hn r
    have hc' : N * (hwReadKraus (.readH z upd) r)ᴴ = (hwReadKraus (.readH z upd) r)ᴴ * N := by
      have := congrArg conjTranspose hc
      simp only [conjTranspose_mul, sqrtDiag_conjTranspose] at this
      exact this.symm
    have heq : hwReadKraus (.readH z upd) r * (N * σ * N) * (hwReadKraus (.readH z upd) r)ᴴ =
        N * (hwReadKraus (.readH z upd) r * σ * (hwReadKraus (.readH z upd) r)ᴴ) * N := by
      calc hwReadKraus (.readH z upd) r * (N * σ * N) * (hwReadKraus (.readH z upd) r)ᴴ
          = (hwReadKraus (.readH z upd) r * N) * σ * (N * (hwReadKraus (.readH z upd) r)ᴴ) := by
            simp only [Matrix.mul_assoc]
        _ = (N * hwReadKraus (.readH z upd) r) * σ * ((hwReadKraus (.readH z upd) r)ᴴ * N) := by
            rw [hc, hc']
        _ = N * (hwReadKraus (.readH z upd) r * σ * (hwReadKraus (.readH z upd) r)ᴴ) * N := by
            simp only [Matrix.mul_assoc]
    rw [MatrixMap.conj_apply, MatrixMap.conj_apply, heq, re_trace_sqrtDiag_conj hn0]
  rw [hT, hS, hp] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun r _ ↦ ?_) h
  split_ifs
  · exact (hL r).symm
  · rfl

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M] in
/-- **A survival bound as a drop**: for a codeword rate `ρ ≥ 2^-21`, the survival bound
`A ≤ w - ρ e + p + 2 √(ρ e p)` gives `2^-22 e + A ≤ w + 3 p` (`2 √(ρ e p) ≤ ρ e / 2 + 2 p`). -/
theorem drop_of_survive {A w e p ρ : ℝ} (he : 0 ≤ e) (hp : 0 ≤ p) (hρ : (2 ^ 21 : ℝ)⁻¹ ≤ ρ)
    (h : A ≤ w - ρ * e + p + 2 * √(ρ * e * p)) : (2 ^ 22 : ℝ)⁻¹ * e + A ≤ w + 3 * p := by
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hρe : 0 ≤ ρ * e := mul_nonneg hρ0 he
  have hsq : 2 * √(ρ * e * p) ≤ ρ * e / 2 + 2 * p := by
    rw [Real.sqrt_mul hρe]
    have h1 := Real.sq_sqrt hρe
    have h2 := Real.sq_sqrt hp
    nlinarith [sq_nonneg (√(ρ * e) - 2 * √p)]
  have h22 : (2 ^ 22 : ℝ)⁻¹ * e ≤ ρ / 2 * e := by
    refine mul_le_mul_of_nonneg_right ?_ he
    have : (2 ^ 22 : ℝ)⁻¹ = (2 ^ 21 : ℝ)⁻¹ / 2 := by norm_num
    rw [this]
    linarith
  nlinarith

/-- **The weighted mass off `SR` against the mass off `SR`**: on states supported where
`n ≤ C`, `∑_{¬SR} n σ ≤ C tr (P σ)`. -/
theorem sum_not_weighted_le (SR : HwReg X Z M → Prop) [DecidablePred SR] {n : HwReg X Z M → ℝ}
    {C : ℝ} {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, n q.2 ≤ C ∨ σ q q = 0) :
    (∑ q, if SR q.2 then 0 else n q.2 * (σ q q).re) ≤ C * (readPs SR * σ).trace.re := by
  rw [readPs, Matrix.trace, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  have hre : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [Matrix.diag_apply, diagonal_mul]
  by_cases hq : SR q.2
  · simp [hq]
  · simp only [hq, ↓reduceIte, one_mul]
    rcases hC q with h | h
    · exact mul_le_mul_of_nonneg_right h hre
    · simp [h]

end weighted

/-! ## Averages of the classical costs with a mass-dependent Enc term -/

section average

/-- `(√f + √g)² = f + g + 2 √(f g)`. -/
theorem sq_rpow_add_eq (f g : ℝ≥0∞) :
    (f ^ (2⁻¹ : ℝ) + g ^ (2⁻¹ : ℝ)) ^ 2 = f + g + 2 * (f * g) ^ (2⁻¹ : ℝ) := by
  have hsq : ∀ y : ℝ≥0∞, (y ^ (2⁻¹ : ℝ)) ^ 2 = y := fun y ↦ by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [add_sq, hsq, hsq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  ring

/-- **The split of `(√f + √g)²`**: at most `(1 + s) f + (1 + 1/s) g` for every `s > 0`. -/
theorem sq_rpow_add_le_lin (f g : ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    (f ^ (2⁻¹ : ℝ) + g ^ (2⁻¹ : ℝ)) ^ 2 ≤
      ENNReal.ofReal (1 + s) * f + ENNReal.ofReal (1 + s⁻¹) * g := by
  have h1 : ENNReal.ofReal (1 + s) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have h2 : ENNReal.ofReal (1 + s⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by have := inv_pos.mpr hs; linarith)).ne'
  by_cases hf : f = ⊤
  · rw [hf, ENNReal.mul_top h1, top_add]
    exact le_top
  by_cases hg : g = ⊤
  · rw [hg, ENNReal.mul_top h2, add_top]
    exact le_top
  rw [← ENNReal.ofReal_toReal hf, ← ENNReal.ofReal_toReal hg, sq_rpow_add_eq]
  exact cost_le_lin hs ENNReal.toReal_nonneg ENNReal.toReal_nonneg

variable {Θ : Type*} [Fintype Θ]

/-- **Jensen for `(√f + √g)²`**: the average is at most `(√(E f) + √(E g))²`. -/
theorem uavg_sq_rpow_add_le (f g : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ (f θ ^ (2⁻¹ : ℝ) + g θ ^ (2⁻¹ : ℝ)) ^ 2) ≤
      (uavg f ^ (2⁻¹ : ℝ) + uavg g ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (le_sq_add_of_forall_lin fun s hs ↦ ?_).trans_eq (add_zero _)
  rw [add_zero, ← uavg_const_mul, ← uavg_const_mul, ← uavg_add]
  exact uavg_mono fun θ ↦ sq_rpow_add_le_lin (f θ) (g θ) hs

/-- The average of a constant is at most the constant. -/
theorem uavg_const_le (c : ℝ≥0∞) : uavg (fun _ : Θ ↦ c) ≤ c := by
  unfold uavg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
  by_cases h : Fintype.card Θ = 0
  · simp [h]
  · rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr h) (ENNReal.natCast_ne_top _), one_mul]

/-- **A mass-dependent bound, averaged over the good parameters**: if `F ≤ a + b m` on `good`
and the average of `m` over `good` is at most `c`, the average of `F` over `good` is at most
`a + b c` (linear: no Jensen). -/
theorem uavg_ite_le_add_mul {good : Θ → Prop} [DecidablePred good] {F m : Θ → ℝ≥0∞}
    {a b c : ℝ≥0∞} (hF : ∀ θ, good θ → F θ ≤ a + b * m θ)
    (hm : uavg (fun θ ↦ if good θ then m θ else 0) ≤ c) :
    uavg (fun θ ↦ if good θ then F θ else 0) ≤ a + b * c := by
  refine (uavg_mono (g := fun θ ↦ a + b * (if good θ then m θ else 0)) fun θ ↦ ?_).trans ?_
  · by_cases hθ : good θ
    · rw [ite_eq_left hθ, ite_eq_left hθ]
      exact hF θ hθ
    · rw [ite_eq_right hθ]
      exact zero_le
  · rw [uavg_add, uavg_const_mul]
    gcongr
    exact uavg_const_le a

/-- **The Enc term averaged over the good parameters**: if `cnt ≤ a + b m` on `good` and the
average of `m` over `good` is at most `c`, the average over `good` of `κ cnt` is at most
`κ (a + b c)`. -/
theorem uavg_ite_const_mul_le {good : Θ → Prop} [DecidablePred good] {cnt m : Θ → ℝ≥0∞}
    {κ a b c : ℝ≥0∞} (hcnt : ∀ θ, good θ → cnt θ ≤ a + b * m θ)
    (hm : uavg (fun θ ↦ if good θ then m θ else 0) ≤ c) :
    uavg (fun θ ↦ if good θ then κ * cnt θ else 0) ≤ κ * (a + b * c) := by
  have he : (fun θ ↦ if good θ then κ * cnt θ else 0) =
      fun θ ↦ κ * (if good θ then cnt θ else 0) := funext fun θ ↦ by
    by_cases hθ : good θ
    · rw [ite_eq_left hθ, ite_eq_left hθ]
    · rw [ite_eq_right hθ, ite_eq_right hθ, mul_zero]
  rw [he, uavg_const_mul]
  gcongr
  exact uavg_ite_le_add_mul hcnt hm

/-- **The classical costs averaged over the good parameters**, with an Enc term that grows with
the recorded mass. If on `good` the total `tw ≤ (√E + √m)² + p` and `E ≤ E₀ + β m`, and the
averages over `good` of `m` and `p` are at most `mc` and `pc`, then the average over `good` of
`tw` is at most `(√(E₀ + β mc) + √mc)² + pc`. -/
theorem uavg_ite_cost_le {good : Θ → Prop} [DecidablePred good] {tw E m p : Θ → ℝ≥0∞}
    {E₀ β mc pc : ℝ≥0∞} (htw : ∀ θ, good θ → tw θ ≤ (E θ ^ (2⁻¹ : ℝ) + m θ ^ (2⁻¹ : ℝ)) ^ 2 + p θ)
    (hE : ∀ θ, good θ → E θ ≤ E₀ + β * m θ)
    (hm : uavg (fun θ ↦ if good θ then m θ else 0) ≤ mc)
    (hp : uavg (fun θ ↦ if good θ then p θ else 0) ≤ pc) :
    uavg (fun θ ↦ if good θ then tw θ else 0) ≤
      ((E₀ + β * mc) ^ (2⁻¹ : ℝ) + mc ^ (2⁻¹ : ℝ)) ^ 2 + pc := by
  refine (uavg_mono (g := fun θ ↦ ((if good θ then E θ else 0) ^ (2⁻¹ : ℝ) +
    (if good θ then m θ else 0) ^ (2⁻¹ : ℝ)) ^ 2 + if good θ then p θ else 0) fun θ ↦ ?_).trans ?_
  · by_cases hθ : good θ
    · simp only [ite_eq_left hθ]
      exact htw θ hθ
    · simp only [ite_eq_right hθ]
      exact zero_le
  · rw [uavg_add]
    refine add_le_add ((uavg_sq_rpow_add_le _ _).trans ?_) hp
    gcongr
    exact uavg_ite_le_add_mul hE hm

end average

end Quantum.Xmss.Assembly

end
