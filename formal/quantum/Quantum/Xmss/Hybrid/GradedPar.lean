module

public import Quantum.Xmss.Hybrid.Graded
public import Quantum.Sponge.Oracle.Hardwired.EventPar

@[expose] public section

/-!
# The graded hybrid with rounds

The parallel runtimes of runtime 1 and `runtimeR` (`QuantumRuntime.par`, rounds of port `h`) differ
at a round by at most `4` times the hidden mass of the round, the sum of the hidden masses of its
slots, not `4` times its width squared: the two rounds agree on every query tuple without a hidden
slot, so their difference is supported on the union of the slot events.

* **Products agreeing outside the hidden slots** (`roundProd_apply_eq_of_agree`,
  `roundProd_slotLift_sub_eq`): for calls that agree outside `H` and keep the membership of the
  other slots in `H`, the rounds agree on the inputs with no slot in `H`.
* **The Kraus weight of a round** (`ofReal_trace_conj_roundProd_sub_le`): at most `4` times the
  summed masses of the slot events.
* **Parallel runtimes as Kraus runtimes** (`parKraus`, `par_branch_eq_conj`).
* **Runtime 1 against `runtimeR`, with rounds** (`sqrt_win_runtime1R_par_le_graded`): the graded
  hybrid of `Graded` on the parallel runtimes; rounds of width `0` are classical calls of mass `0`.
  Averaged, with the masses of the quantum calls summed (Cauchy-Schwarz over at most `d` quantum
  calls and rounds of positive width): `uavg_win_runtime1R_par_le_graded_total`,
  `E P₁ ≤ (√(E P₂) + √(4 d μ) + √ν)²`.
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v w

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime Quantum.Par

/-! ## Rounds agreeing outside the hidden slots -/

section rounds

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Products agreeing outside the marked inputs.** If the `j`-th factors agree on the inputs
outside `p j`, and every factor keeps the marks of the other factors, the products agree on the
inputs with no mark. -/
theorem roundProd_apply_eq_of_agree :
    ∀ {w : ℕ} (A B : Fin w → Matrix n n ℂ) (p : Fin w → n → Prop),
      (∀ j y x, ¬ p j x → A j y x = B j y x) →
      (∀ i j, i ≠ j → ∀ y x, A j y x ≠ 0 → (p i y ↔ p i x)) →
      (∀ i j, i ≠ j → ∀ y x, B j y x ≠ 0 → (p i y ↔ p i x)) →
      ∀ y x, (∀ j, ¬ p j x) → roundProd A y x = roundProd B y x
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | _ + 1, A, B, p, hAB, hA, hB, y, x, hx => by
    rw [roundProd_succ, roundProd_succ, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [hAB 0 z x (hx 0)]
    by_cases hz : B 0 z x = 0
    · rw [hz, mul_zero, mul_zero]
    · rw [roundProd_apply_eq_of_agree (fun j ↦ A j.succ) (fun j ↦ B j.succ) (fun j ↦ p j.succ)
        (fun j ↦ hAB j.succ)
        (fun i j hij ↦ hA i.succ j.succ fun e ↦ hij (Fin.succ_injective _ e))
        (fun i j hij ↦ hB i.succ j.succ fun e ↦ hij (Fin.succ_injective _ e)) y z
        (fun j hj ↦ hx j.succ ((hB j.succ 0 (Fin.succ_ne_zero j) z x hz).1 hj))]

/-- A product of factors keeping a label keeps the label. -/
theorem roundProd_apply_ne_zero_eq {Λ : Type*} (g : n → Λ) :
    ∀ {w : ℕ} (V : Fin w → Matrix n n ℂ), (∀ j y x, V j y x ≠ 0 → g y = g x) →
      ∀ y x, roundProd V y x ≠ 0 → g y = g x
  | 0, _, _, y, x, h => by
    by_cases hyx : y = x
    · rw [hyx]
    · rw [roundProd_zero, Matrix.one_apply_ne hyx] at h
      exact absurd rfl h
  | _ + 1, V, hV, y, x, h => by
    rw [roundProd_succ, Matrix.mul_apply] at h
    obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact (roundProd_apply_ne_zero_eq g (fun j ↦ V j.succ) (fun j ↦ hV j.succ) y z
      (left_ne_zero_of_mul hz)).trans (hV 0 z x (right_ne_zero_of_mul hz))

/-- The mass of the inputs in some set of a family is at most the summed masses. -/
theorem diagMass_exists_le {α ι : Type} [Fintype α] [Fintype ι] (T : ι → Set α)
    (σ : Matrix α α ℂ) : diagMass {a | ∃ j, a ∈ T j} σ ≤ ∑ j, diagMass (T j) σ := by
  simp only [diagMass]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  by_cases h : ∃ j, a ∈ T j
  · obtain ⟨j, hj⟩ := h
    calc {a | ∃ j, a ∈ T j}.indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a
        = (T j).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a := by
          rw [Set.indicator_of_mem (show a ∈ {a | ∃ j, a ∈ T j} from ⟨j, hj⟩),
            Set.indicator_of_mem hj]
      _ ≤ _ := Finset.single_le_sum (f := fun j ↦ (T j).indicator
          (fun a ↦ ENNReal.ofReal (σ a a).re) a) (fun _ _ ↦ zero_le) (Finset.mem_univ j)
  · have h0 : {a | ∃ j, a ∈ T j}.indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a = 0 :=
      Set.indicator_of_notMem (show a ∉ {a | ∃ j, a ∈ T j} from h) _
    rw [h0]
    exact zero_le

variable {S N : Type} [Fintype S] [DecidableEq S] [Fintype N] [DecidableEq N]

/-- **Rounds agreeing outside the hidden slots.** For calls `V₁`, `V₂` agreeing on the inputs
outside `H`, whose nonzero entries keep the membership in `H` of every slot input, the two rounds
differ only on the inputs with some slot in `H`. -/
theorem roundProd_slotLift_sub_eq {w : ℕ} (V₁ V₂ : Matrix (S × N) (S × N) ℂ) (H : Set (S × N))
    (hagree : ∀ y x, x ∉ H → V₁ y x = V₂ y x)
    (h₁ : ∀ y x, V₁ y x ≠ 0 → ∀ b, ((b, y.2) ∈ H ↔ (b, x.2) ∈ H))
    (h₂ : ∀ y x, V₂ y x ≠ 0 → ∀ b, ((b, y.2) ∈ H ↔ (b, x.2) ∈ H)) :
    roundProd (fun j : Fin w ↦ slotLift j V₁) - roundProd (fun j : Fin w ↦ slotLift j V₂) =
      (roundProd (fun j : Fin w ↦ slotLift j V₁) - roundProd (fun j : Fin w ↦ slotLift j V₂)) *
        setProj {x | ∃ j, (x.1 j, x.2) ∈ H} := by
  have hkeep : ∀ (V : Matrix (S × N) (S × N) ℂ),
      (∀ y x, V y x ≠ 0 → ∀ b, ((b, y.2) ∈ H ↔ (b, x.2) ∈ H)) →
      ∀ i j : Fin w, i ≠ j → ∀ y x, slotLift j V y x ≠ 0 →
        ((y.1 i, y.2) ∈ H ↔ (x.1 i, x.2) ∈ H) := by
    intro V hV i j hij y x hne
    rw [slotLift_apply] at hne
    split_ifs at hne with hr
    · have hyi : y.1 i = x.1 i := congrFun hr ⟨i, hij⟩
      rw [hyi]
      exact hV _ _ hne (x.1 i)
    · exact absurd rfl hne
  refine sub_eq_sub_mul_setProj _ _ _ fun y x hx ↦ roundProd_apply_eq_of_agree _ _
    (fun j x ↦ (x.1 j, x.2) ∈ H) (fun j y x hx ↦ ?_) (hkeep V₁ h₁) (hkeep V₂ h₂) y x
    fun j hj ↦ hx ⟨j, hj⟩
  rw [slotLift_apply, slotLift_apply]
  split_ifs
  · exact hagree _ _ hx
  · rfl

/-- **The Kraus weight of a round**: at most `4` times the summed masses of the slot events. -/
theorem ofReal_trace_conj_roundProd_sub_le {w : ℕ} (V₁ V₂ : Matrix (S × N) (S × N) ℂ)
    (hV₁ : V₁ ∈ unitaryGroup (S × N) ℂ) (hV₂ : V₂ ∈ unitaryGroup (S × N) ℂ) (H : Set (S × N))
    (hagree : ∀ y x, x ∉ H → V₁ y x = V₂ y x)
    (h₁ : ∀ y x, V₁ y x ≠ 0 → ∀ b, ((b, y.2) ∈ H ↔ (b, x.2) ∈ H))
    (h₂ : ∀ y x, V₂ y x ≠ 0 → ∀ b, ((b, y.2) ∈ H ↔ (b, x.2) ∈ H))
    {σ : Matrix ((Fin w → S) × N) ((Fin w → S) × N) ℂ} (hσ : σ.PosSemidef) :
    ENNReal.ofReal (MatrixMap.conj (roundProd (fun j : Fin w ↦ slotLift j V₁) -
        roundProd (fun j : Fin w ↦ slotLift j V₂)) σ).trace.re ≤
      4 * ∑ j : Fin w, diagMass {x | (x.1 j, x.2) ∈ H} σ := by
  have hu : ∀ V : Matrix (S × N) (S × N) ℂ, V ∈ unitaryGroup (S × N) ℂ →
      ∑ _ : Unit, (roundProd (fun j : Fin w ↦ slotLift j V))ᴴ *
        roundProd (fun j : Fin w ↦ slotLift j V) = 1 := fun V hV ↦ by
    have h := Matrix.mem_unitaryGroup_iff'.mp (roundProd_mem_unitaryGroup
      (V := fun j : Fin w ↦ slotLift j V) fun j ↦ onFactor_mem_unitaryGroup (slotEquiv j) hV)
    rw [star_eq_conjTranspose] at h
    rw [Fintype.sum_unique]
    exact h
  have h := tsum_ofReal_trace_conj_sub_le (fun _ : Unit ↦ roundProd (fun j : Fin w ↦ slotLift j V₁))
    (fun _ ↦ roundProd (fun j : Fin w ↦ slotLift j V₂)) (hu V₁ hV₁) (hu V₂ hV₂) _
    (fun _ ↦ roundProd_slotLift_sub_eq V₁ V₂ H hagree h₁ h₂) hσ
  rw [tsum_fintype, Fintype.sum_unique] at h
  exact h.trans (mul_le_mul_of_nonneg_left (diagMass_exists_le _ σ) zero_le)

end rounds

/-! ## Parallel runtimes of Kraus runtimes -/

section parKraus

variable {spec : QuantumOracleSpec.{0, 0}} {Q : Type} (port : Q → spec.Port)
  (R : QuantumRuntime spec)

/-- The Kraus operators of the rounds of `R.par port`. -/
noncomputable def parKraus
    (K : ∀ p, spec.Result p → Matrix (spec.Out p × R.D) (spec.In p × R.D) ℂ) :
    ∀ j : (roundSpec spec port).Port, (roundSpec spec port).Result j →
      Matrix ((roundSpec spec port).Out j × R.D) ((roundSpec spec port).In j × R.D) ℂ
  | .round _ f, rs => R.roundKraus K (fun i ↦ port (f i)) rs

/-- **The Kraus operators of a parallel runtime**: those of `R` on the single calls and the
round products on the rounds. -/
theorem par_branch_eq_conj
    (K : ∀ p, spec.Result p → Matrix (spec.Out p × R.D) (spec.In p × R.D) ℂ)
    (hK : ∀ i r, (R.step i).branch r = MatrixMap.conj (K i r)) :
    ∀ i r, ((R.par port).step i).branch r =
      MatrixMap.conj (Xmss.Assembly.sumKraus K (parKraus port R K) i r)
  | .inl i, r => hK i r
  | .inr (.round _ f), rs => R.branch_roundStep_of_conj K hK (fun i ↦ port (f i)) rs

end parKraus

/-! ## Runtime 1 against `runtimeR`, with rounds -/

section runtimeR

open Quantum.Sponge Quantum.Xmss.Assembly

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- A round of one sponge port of an extended hardwired-style runtime is the product of its
calls on the slots. -/
theorem roundKraus_mk_extend {M : Type} [Fintype M] [DecidableEq M] [AddCommGroup X]
    [AddCommGroup Z] (σ₀ : SubState (QReg.of (HwReg X Z M)))
    (s₀ : ∀ i, SubInstrument ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M)) ((hwSpec X Z M).Result i))
    {t : QuantumOracleSpec.{0, 0}}
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (K : ∀ i : ((hwSpec X Z M).sum t).Port, ((hwSpec X Z M).sum t).Result i →
      Matrix (((hwSpec X Z M).sum t).Out i × QReg.of (HwReg X Z M))
        (((hwSpec X Z M).sum t).In i × QReg.of (HwReg X Z M)) ℂ) (p : SpongePort) :
    ∀ {w : ℕ} (rs : RoundResult ((hwSpec X Z M).sum t)
      (fun _ : Fin w ↦ (.inl (.inl (.inl p)) : ((hwSpec X Z M).sum t).Port))),
      ((QuantumRuntime.mk _ σ₀ s₀).extend step').roundKraus K
          (fun _ : Fin w ↦ (.inl (.inl (.inl p)) : ((hwSpec X Z M).sum t).Port)) rs =
        roundProd (fun j : Fin w ↦ slotLift (S := spongeIn X Z p) (N := HwReg X Z M) j
          (K (.inl (.inl (.inl p))) ()))
  | 0, rs => by
      simp only [QuantumRuntime.roundKraus]
      rw [roundProd_zero]
      refine (congrArg basisMatrix (funext fun y ↦ ?_)).trans basisMatrix_id
      exact Prod.ext (funext fun i ↦ i.elim0) rfl
  | w + 1, rs => by
      simp only [QuantumRuntime.roundKraus]
      rw [roundKraus_mk_extend σ₀ s₀ step' K p (Fin.tail rs)]
      exact roundProd_succ_slotLift _

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']

variable (X Z S M') in
/-- The rounds of the parallel runtimes are rounds of port `h`. -/
abbrev recHPort : Unit → (recHwSpec X Z S M').Port := fun _ ↦ .inl (.inl (.inl .h))

variable (X Z S M') in
/-- The classical commands of the hybrid: the classical single calls and the rounds of width
`0`. -/
def hybCls : (parSpec (recHwSpec X Z S M') (recHPort X Z S M')).Port → Bool
  | .inl i => extCls X Z (Finset S × M') (recSpec S M') i
  | .inr (.round w _) => decide (w = 0)

/-- The label map: that of `runtimeR` on the single calls; rounds keep the hardwired cells. -/
def hybLabMap : ∀ i : (parSpec (recHwSpec X Z S M') (recHPort X Z S M')).Port,
    (parSpec (recHwSpec X Z S M') (recHPort X Z S M')).Result i → Hw X Z → Hw X Z
  | .inl i, r => hwLabMap i r
  | .inr _, _ => id

/-- The difference sets: those of the read ports; empty at the rounds. -/
def hybHidSet (Hh : Set Z) (Hk Hk' : Set X) :
    (parSpec (recHwSpec X Z S M') (recHPort X Z S M')).Port → Set (Hw X Z)
  | .inl i => readHidSet Hh Hk Hk' i
  | .inr _ => ∅

variable (M') in
/-- The hidden inputs of one call of port `h`. -/
def hSlotSet (Hh : Set Z) : Set ((Z × X) × HwReg X Z (Finset S × M')) :=
  {p | p.1.1 ∈ Hh ∧ p.2.2.1.1 p.1.1 = none}

variable (S M') in
/-- **The hidden mass of a round**: the summed hidden masses of its slots. -/
noncomputable def roundHidMass (Hh : Set Z) (w : ℕ)
    (σ : Matrix ((Fin w → Z × X) × HwReg X Z (Finset S × M'))
      ((Fin w → Z × X) × HwReg X Z (Finset S × M')) ℂ) : ℝ≥0∞ :=
  ∑ j : Fin w, diagMass {x | (x.1 j, x.2) ∈ hSlotSet M' Hh} σ

/-- **The hidden mass of a command**: that of `runtimeR`'s ports on the single calls, the
summed hidden masses of the slots on the rounds. -/
noncomputable def parHidMass (Hh : Set Z) (Hk Hk' : Set X) :
    ∀ i : (parSpec (recHwSpec X Z S M') (recHPort X Z S M')).Port,
      Matrix ((parSpec (recHwSpec X Z S M') (recHPort X Z S M')).In i ×
          QReg.of (HwReg X Z (Finset S × M')))
        ((parSpec (recHwSpec X Z S M') (recHPort X Z S M')).In i ×
          QReg.of (HwReg X Z (Finset S × M'))) ℂ → ℝ≥0∞
  | .inl i => extWeight (hiddenMass Hh Hk Hk') i
  | .inr (.round w _) => roundHidMass S M' Hh w

/-- **The hidden mass of the quantum commands**: `parHidMass`, `0` on the classical commands. -/
noncomputable def parSpongeMass (Hh : Set Z) (Hk Hk' : Set X) :
    ∀ i : (parSpec (recHwSpec X Z S M') (recHPort X Z S M')).Port,
      Matrix ((parSpec (recHwSpec X Z S M') (recHPort X Z S M')).In i ×
          QReg.of (HwReg X Z (Finset S × M')))
        ((parSpec (recHwSpec X Z S M') (recHPort X Z S M')).In i ×
          QReg.of (HwReg X Z (Finset S × M'))) ℂ → ℝ≥0∞ :=
  fun i σ ↦ if hybCls X Z S M' i then 0 else parHidMass Hh Hk Hk' i σ

theorem parSpongeMass_inl (Hh : Set Z) (Hk Hk' : Set X) (i : (recHwSpec X Z S M').Port) :
    parSpongeMass Hh Hk Hk' (.inl i) = spongeMass Hh Hk Hk' i := by
  rw [spongeMass_eq]
  rfl

theorem parSpongeMass_round (Hh : Set Z) (Hk Hk' : Set X) {w : ℕ} (hw : w ≠ 0)
    (f : Fin w → Unit) :
    parSpongeMass (S := S) (M' := M') Hh Hk Hk' (.inr (.round w f)) = roundHidMass S M' Hh w := by
  funext σ
  simp [parSpongeMass, hybCls, parHidMass, hw]

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
/-- Rounds of positive width and single quantum calls are the commands charged by
`spongeRounds`. -/
theorem spongeRounds_recHPort :
    spongeRounds (recHPort X Z S M') (extCls X Z (Finset S × M') (recSpec S M')) =
      fun i ↦ if hybCls X Z S M' i then 0 else 1 := by
  funext i
  rcases i with i | ⟨w, f⟩
  · simp only [spongeRounds, roundCharge, widthCharge, hybCls]
    by_cases h : extCls X Z (Finset S × M') (recSpec S M') i = true <;> simp [h]
  · simp [spongeRounds, roundCharge, widthCharge, hybCls, extCls, hwCls]

theorem clsMass_hybHidSet (Hh : Set Z) (Hk Hk' : Set X) :
    clsMass (D := QReg.of (HwReg X Z (Finset S × M'))) (hybCls X Z S M') hwLab
        (hybHidSet Hh Hk Hk') =
      parWeight (recHPort X Z S M') (readMass Hh Hk Hk') := by
  funext i σ
  rcases i with i | ⟨w, f⟩
  · exact congrFun (congrFun (clsMass_readHidSet (S := S) (M' := M') Hh Hk Hk') i) σ
  · simp [clsMass, hybHidSet, parWeight, diagMass]

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]

variable (X Z) in
/-- The Kraus operators of `runtimeR`. -/
noncomputable abbrev krausR (m₀ : Finset S × M') :=
  sumKraus (t := recSpec S M') (kraus2 X Z m₀) (fun T m ↦ recKraus (X := X) (Z := Z) T m)

variable (X Z) in
/-- The Kraus operators of `runtime1R`. -/
noncomputable abbrev kraus1R (L : Hw X Z) (m₀ : Finset S × M') :=
  sumKraus (t := recSpec S M') (kraus1 X Z L m₀) (fun T m ↦ recKraus (X := X) (Z := Z) T m)

theorem parKrausR_round (m₀ : Finset S × M') (w : ℕ) (f : Fin w → Unit)
    (rs : (parSpec (recHwSpec X Z S M') (recHPort X Z S M')).Result (.inr (.round w f))) :
    sumKraus (krausR X Z m₀) (parKraus (recHPort X Z S M') (runtimeR m₀) (krausR X Z m₀))
        (.inr (.round w f)) rs =
      roundProd (fun j : Fin w ↦ slotLift (S := Z × X)
        (N := HwReg X Z (Finset S × M')) j ((spongeHardwired X Z (hwEmpty X Z) m₀).U .h)) :=
  roundKraus_mk_extend (initHw X Z m₀) (spongeHardwiredRuntime X Z (hwEmpty X Z) m₀).step
    (t := recSpec S M') recStep (krausR X Z m₀) .h rs

theorem parKraus1R_round (L : Hw X Z) (m₀ : Finset S × M') (w : ℕ) (f : Fin w → Unit)
    (rs : (parSpec (recHwSpec X Z S M') (recHPort X Z S M')).Result (.inr (.round w f))) :
    sumKraus (kraus1R X Z L m₀)
        (parKraus (recHPort X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀))
        (.inr (.round w f)) rs =
      roundProd (fun j : Fin w ↦ slotLift (S := Z × X)
        (N := HwReg X Z (Finset S × M')) j ((spongeHardwired1 X Z L m₀).U .h)) :=
  roundKraus_mk_extend (initHw X Z m₀) (runtime1 X Z L m₀).step (t := recSpec S M') recStep
    (kraus1R X Z L m₀) .h rs

omit [Nonempty X] [Nonempty Z] in
/-- The calls of port `h` keep the hardwired register. -/
theorem snd_eq_of_U_h_ne_zero {m₀ : Finset S × M'}
    {V : Matrix ((Z × X) × HwReg X Z (Finset S × M')) ((Z × X) × HwReg X Z (Finset S × M')) ℂ}
    (hV : V = (spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U .h ∨
      ∃ L, V = (spongeHardwired1 X Z L (M := Finset S × M') m₀).U .h)
    (y x : (Z × X) × HwReg X Z (Finset S × M')) (h : V y x ≠ 0) : y.2.2 = x.2.2 := by
  obtain ⟨a', s'⟩ := y
  obtain ⟨a, s⟩ := x
  rcases hV with rfl | ⟨L, rfl⟩
  · exact hwPort_ne_zero_snd _ h
  · exact hwPort_ne_zero_snd _ h

omit [Nonempty X] [Nonempty Z] in
/-- The rounds of both runtimes keep the hardwired cells. -/
theorem hwLab_round_eq {m₀ : Finset S × M'} {V : Matrix ((Z × X) × HwReg X Z (Finset S × M'))
      ((Z × X) × HwReg X Z (Finset S × M')) ℂ}
    (hV : V = (spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U .h ∨
      ∃ L, V = (spongeHardwired1 X Z L (M := Finset S × M') m₀).U .h) {w : ℕ}
    (y x : (Fin w → Z × X) × HwReg X Z (Finset S × M'))
    (h : roundProd (fun j : Fin w ↦ slotLift j V) y x ≠ 0) : hwLab y.2 = hwLab x.2 :=
  roundProd_apply_ne_zero_eq (fun y : (Fin w → Z × X) × HwReg X Z (Finset S × M') ↦ hwLab y.2)
    _ (fun j y x hne ↦ by
      rw [slotLift_apply] at hne
      split_ifs at hne
      · exact congrArg Prod.fst (snd_eq_of_U_h_ne_zero hV _ _ hne)
      · exact absurd rfl hne) y x h

/-- The Kraus operators of `runtimeR.par` move the hardwired cells along `hybLabMap`. -/
theorem hwLab_parKrausR (m₀ : Finset S × M') :
    ∀ i r o d' j d, sumKraus (krausR X Z m₀)
      (parKraus (recHPort X Z S M') (runtimeR m₀) (krausR X Z m₀)) i r (o, d') (j, d) ≠ 0 →
        hwLab d' = hybLabMap i r (hwLab d)
  | .inl i, r, o, d', j, d, h => hwLab_sumKraus2 m₀ i r o d' j d h
  | .inr (.round w f), rs, o, d', j, d, h => by
    have e := congrFun (congrFun (parKrausR_round m₀ w f rs) (o, d')) (j, d)
    exact hwLab_round_eq (m₀ := m₀) (Or.inl rfl) (o, d') (j, d) fun h0 ↦ h (e.trans h0)

/-- The Kraus operators of `runtime1R.par` move the hardwired cells along `hybLabMap`. -/
theorem hwLab_parKraus1R (L : Hw X Z) (m₀ : Finset S × M') :
    ∀ i r o d' j d, sumKraus (kraus1R X Z L m₀)
      (parKraus (recHPort X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)) i r (o, d')
        (j, d) ≠ 0 → hwLab d' = hybLabMap i r (hwLab d)
  | .inl i, r, o, d', j, d, h => hwLab_sumKraus1 L m₀ i r o d' j d h
  | .inr (.round w f), rs, o, d', j, d, h => by
    have e := congrFun (congrFun (parKraus1R_round L m₀ w f rs) (o, d')) (j, d)
    exact hwLab_round_eq (m₀ := m₀) (Or.inr ⟨L, rfl⟩) (o, d') (j, d) fun h0 ↦ h (e.trans h0)

variable {Hh : Set Z} {Hk Hk' : Set X}

/-- At a classical command, the two parallel runtimes agree outside the difference sets. -/
theorem parKraus_eq_of_not_mem (L : Hw X Z) (m₀ : Finset S × M') (hL : Covers L Hh Hk Hk') :
    ∀ i, hybCls X Z S M' i = true → ∀ r o d' j d, hwLab d ∉ hybHidSet Hh Hk Hk' i →
      sumKraus (krausR X Z m₀) (parKraus (recHPort X Z S M') (runtimeR m₀) (krausR X Z m₀))
          i r (o, d') (j, d) =
        sumKraus (kraus1R X Z L m₀)
          (parKraus (recHPort X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)) i r (o, d')
          (j, d)
  | .inl i, hi, r, o, d', j, d, hd => sumKraus_eq_of_not_mem_readHidSet L m₀ hL i hi r o d' j d hd
  | .inr (.round w f), hi, rs, o, d', j, d, _ => by
    have hw : w = 0 := by simpa [hybCls] using hi
    subst hw
    exact (congrFun (congrFun (parKrausR_round m₀ 0 f rs) (o, d')) (j, d)).trans
      (congrFun (congrFun (parKraus1R_round L m₀ 0 f rs) (o, d')) (j, d)).symm

/-- **The per-command bound**: the Kraus weight of the difference of the two parallel runtimes
is at most `4` times the hidden mass of the command. -/
theorem krausWeight_par_le_hidden (L : Hw X Z) (m₀ : Finset S × M') (hL : Covers L Hh Hk Hk')
    (i : (parSpec (recHwSpec X Z S M') (recHPort X Z S M')).Port)
    {σ : Matrix ((parSpec (recHwSpec X Z S M') (recHPort X Z S M')).In i ×
        QReg.of (HwReg X Z (Finset S × M')))
      ((parSpec (recHwSpec X Z S M') (recHPort X Z S M')).In i ×
        QReg.of (HwReg X Z (Finset S × M'))) ℂ} (hσ : σ.PosSemidef) :
    krausWeight (fun i r ↦
      sumKraus (krausR X Z m₀) (parKraus (recHPort X Z S M') (runtimeR m₀) (krausR X Z m₀)) i r -
        sumKraus (kraus1R X Z L m₀)
          (parKraus (recHPort X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)) i r) i σ ≤
      4 * parHidMass Hh Hk Hk' i σ := by
  rcases i with i | ⟨w, f⟩
  · exact krausWeight_le_hidden_extend L m₀ hL _ i hσ
  · have hdiff : (spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U .h -
        (spongeHardwired1 X Z L (M := Finset S × M') m₀).U .h =
        ((spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U .h -
          (spongeHardwired1 X Z L (M := Finset S × M') m₀).U .h) * setProj (hSlotSet M' Hh) :=
      hwPort_sub_eq _ _ _ (fun q q' h1 h2 ↦ by simp [hSlotSet, h1, h2])
        (fun q hq ↦ by simp only [hwView, hwView_or_eq (w := q.2.2.1.1) (a := q.1.1) hL.1 hq])
    have hagree : ∀ y x, x ∉ hSlotSet M' Hh →
        (spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U .h y x =
          (spongeHardwired1 X Z L (M := Finset S × M') m₀).U .h y x := fun y x hx ↦ by
      have e := congrFun (congrFun hdiff y) x
      rw [Matrix.sub_apply, setProj, mul_diagonal, Set.indicator_of_notMem hx, mul_zero,
        sub_eq_zero] at e
      exact e
    have hkeep : ∀ V : Matrix ((Z × X) × HwReg X Z (Finset S × M'))
        ((Z × X) × HwReg X Z (Finset S × M')) ℂ,
        (V = (spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U .h ∨
          ∃ L, V = (spongeHardwired1 X Z L (M := Finset S × M') m₀).U .h) →
        ∀ y x, V y x ≠ 0 → ∀ b, ((b, y.2) ∈ hSlotSet M' Hh ↔ (b, x.2) ∈ hSlotSet M' Hh) :=
      fun V hV y x hne b ↦ by
        have e := snd_eq_of_U_h_ne_zero hV y x hne
        change (b.1 ∈ Hh ∧ y.2.2.1.1 b.1 = none) ↔ (b.1 ∈ Hh ∧ x.2.2.1.1 b.1 = none)
        rw [e]
    have e₂ := parKrausR_round (X := X) (Z := Z) m₀ w f
    have e₁ := parKraus1R_round L m₀ w f
    calc krausWeight (fun i r ↦
          sumKraus (krausR X Z m₀) (parKraus (recHPort X Z S M') (runtimeR m₀) (krausR X Z m₀))
            i r - sumKraus (kraus1R X Z L m₀)
              (parKraus (recHPort X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)) i r)
            (.inr (.round w f)) σ
        = ∑' _ : Fin w → Unit, ENNReal.ofReal (MatrixMap.conj
            (roundProd (fun j : Fin w ↦ slotLift (S := Z × X)
              (N := HwReg X Z (Finset S × M')) j
                ((spongeHardwired X Z (hwEmpty X Z) m₀).U .h)) -
              roundProd (fun j : Fin w ↦ slotLift (S := Z × X)
                (N := HwReg X Z (Finset S × M')) j ((spongeHardwired1 X Z L m₀).U .h)))
                  σ).trace.re :=
          tsum_congr fun rs ↦ by beta_reduce; rw [e₂ rs, e₁ rs]; rfl
      _ = ENNReal.ofReal (MatrixMap.conj
            (roundProd (fun j : Fin w ↦ slotLift (S := Z × X)
              (N := HwReg X Z (Finset S × M')) j
                ((spongeHardwired X Z (hwEmpty X Z) m₀).U .h)) -
              roundProd (fun j : Fin w ↦ slotLift (S := Z × X)
                (N := HwReg X Z (Finset S × M')) j ((spongeHardwired1 X Z L m₀).U .h)))
                  σ).trace.re :=
          by rw [tsum_fintype, Fintype.sum_unique]
      _ ≤ 4 * roundHidMass S M' Hh w σ :=
          ofReal_trace_conj_roundProd_sub_le _ _
            ((spongeHardwired X Z (hwEmpty X Z) m₀).unitary .h)
            ((spongeHardwired1 X Z L m₀).unitary .h) _ hagree
            (hkeep _ (Or.inl rfl)) (hkeep _ (Or.inr ⟨L, rfl⟩)) hσ

variable {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ]

/-- **Runtime 1 against `runtimeR`, with rounds, graded.** `√P₁ ≤ √P₂ + ∑ₙ √(4 μₙ) + √ν`, where
`μₙ` is the hidden mass of the `n`-th quantum command (a single sponge call or a round of
positive width, the round's mass being the summed masses of its slots) of the run against
`runtimeR.par`, and `ν` the hidden mass at the read ports summed over all calls. -/
theorem sqrt_win_runtime1R_par_le_graded (L : Hw X Z) (m₀ : Finset S × M')
    (hL : Covers L Hh Hk Hk')
    (x : QuantumComp Λ (parSpec (recHwSpec X Z S M') (recHPort X Z S M')) Xf A) (ρ : SubState A)
    (f : (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) :
    ((runtime1R X Z L m₀).par (recHPort X Z S M')).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      ((runtimeR m₀).par (recHPort X Z S M')).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) +
        ∑' n, (4 * kindWeight ((runtimeR m₀).par (recHPort X Z S M')) I (hybCls X Z S M')
          (parHidMass Hh Hk Hk') x
            (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) n) ^ (2⁻¹ : ℝ) +
        ((runtimeR m₀).par (recHPort X Z S M')).totalWeight I
          (parWeight (recHPort X Z S M') (readMass Hh Hk Hk')) x
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ^ (2⁻¹ : ℝ) := by
  have h := rpow_inv_two_outcomeLawWith_le_graded I (initHw X Z m₀)
    (par_branch_eq_conj (recHPort X Z S M') (runtimeR m₀) (krausR X Z m₀)
      (extend_branch_eq_conj (t := recSpec S M') (runtime2 X Z m₀) recStep (runtime2_branch m₀)
        fun T r ↦ recStep_branch T r))
    (par_branch_eq_conj (recHPort X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)
      (extend_branch_eq_conj (t := recSpec S M') (runtime1 X Z L m₀) recStep
        (runtime1_branch L m₀) fun T r ↦ recStep_branch T r))
    (cls := hybCls X Z S M') (κ := hwLab) (F := hybLabMap) (S := hybHidSet Hh Hk Hk')
    (hwLab_parKrausR m₀) (hwLab_parKraus1R L m₀) (parKraus_eq_of_not_mem L m₀ hL) (hwEmpty X Z)
    (querySupportedOn_initHw m₀) x ρ f hE
  refine h.trans (add_le_add (add_le_add le_rfl
    (ENNReal.tsum_le_tsum fun n ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)))
    (le_of_eq (congrArg (· ^ (2⁻¹ : ℝ)) (congrArg (fun W ↦
      ((runtimeR m₀).par (recHPort X Z S M')).totalWeight I W x
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix))
      (clsMass_hybHidSet Hh Hk Hk')))))
  calc _ ≤ kindWeight ((runtimeR m₀).par (recHPort X Z S M')) I (hybCls X Z S M')
        (fun i σ ↦ 4 * parHidMass Hh Hk Hk' i σ) x
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) n :=
        kindWeight_mono ((runtimeR m₀).par (recHPort X Z S M')) I (hybCls X Z S M')
          (fun i σ hσ ↦ krausWeight_par_le_hidden L m₀ hL i hσ) x
          (ρ.prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef n
    _ = _ := kindWeight_const_mul ((runtimeR m₀).par (recHPort X Z S M')) I (hybCls X Z S M') 4
        x _ n

/-- **Runtime 1 against `runtimeR`, with rounds, averaged, the masses summed** (Cauchy-Schwarz
over at most `d` single sponge calls and rounds of positive width on every path,
`tsum_rpow_kindWeight_le`): if the averaged hidden mass of the quantum commands
(`parSpongeMass`), summed over all commands, is at most `μ`, and that at the read ports at most
`ν`, then `E P₁ ≤ (√(E P₂) + √(4 d μ) + √ν)²`. -/
theorem uavg_win_runtime1R_par_le_graded_total {Θ : Type*} [Fintype Θ] (L : Θ → Hw X Z)
    (Hhθ : Θ → Set Z) (Hkθ Hk'θ : Θ → Set X) (hL : ∀ θ, Covers (L θ) (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (m₀ : Finset S × M')
    (x : Θ → QuantumComp Λ (parSpec (recHwSpec X Z S M') (recHPort X Z S M')) Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) (d : ℕ)
    (hd : ∀ θ, IFreeM.IsChargeBound (x θ)
      (portCharge (spongeRounds (recHPort X Z S M') (extCls X Z (Finset S × M') (recSpec S M'))))
      d)
    (μ ν : ℝ≥0∞)
    (hμ : uavg (fun θ ↦ ((runtimeR m₀).par (recHPort X Z S M')).totalWeight I
      (parSpongeMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) ≤ μ)
    (hν : uavg (fun θ ↦ ((runtimeR m₀).par (recHPort X Z S M')).totalWeight I
      (parWeight (recHPort X Z S M') (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ))) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) ≤ ν) :
    uavg (fun θ ↦ ((runtime1R X Z (L θ) m₀).par (recHPort X Z S M')).evalDistMap I (x θ) (ρ θ)
        (f θ) E) ≤
      (uavg (fun θ ↦ ((runtimeR m₀).par (recHPort X Z S M')).evalDistMap I (x θ) (ρ θ) (f θ) E) ^
          (2⁻¹ : ℝ) + (4 * (d * μ)) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)) ^ 2 := by
  set T : Θ → ℝ≥0∞ := fun θ ↦ ((runtimeR m₀).par (recHPort X Z S M')).totalWeight I
    (parSpongeMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
    ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) with hT
  have hz : ∀ (c : ℝ≥0∞), ∑' n : ℕ, (4 * if n = 0 then c else 0) ^ (2⁻¹ : ℝ) =
      (4 * c) ^ (2⁻¹ : ℝ) := fun c ↦ by
    rw [tsum_eq_single 0 fun n hn ↦ by
      simp [hn, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]]
    simp
  have hθ : ∀ θ, ((runtime1R X Z (L θ) m₀).par (recHPort X Z S M')).evalDistMap I (x θ) (ρ θ)
      (f θ) E ^ (2⁻¹ : ℝ) ≤
      ((runtimeR m₀).par (recHPort X Z S M')).evalDistMap I (x θ) (ρ θ) (f θ) E ^ (2⁻¹ : ℝ) +
        ∑' n : ℕ, (4 * if n = 0 then (d : ℝ≥0∞) * T θ else 0) ^ (2⁻¹ : ℝ) +
        ((runtimeR m₀).par (recHPort X Z S M')).totalWeight I
          (parWeight (recHPort X Z S M') (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ))) (x θ)
          ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ^ (2⁻¹ : ℝ) := by
    intro θ
    have hdθ := hd θ
    rw [spongeRounds_recHPort] at hdθ
    rw [hz]
    refine (sqrt_win_runtime1R_par_le_graded I (L θ) m₀ (hL θ) (x θ) (ρ θ) (f θ) hE).trans
      (add_le_add (add_le_add le_rfl ((tsum_rpow_kindWeight_le
        ((runtimeR m₀).par (recHPort X Z S M')) I _ (x θ) hdθ _ 4).trans_eq ?_)) le_rfl)
    rw [mul_left_comm]
    rfl
  refine (uavg_le_of_hybrid_graded _ _ _ _ hθ).trans ?_
  have hu : ∀ n : ℕ, uavg (fun θ ↦ if n = 0 then (d : ℝ≥0∞) * T θ else 0) =
      if n = 0 then (d : ℝ≥0∞) * uavg T else 0 := fun n ↦ by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte, uavg_const_mul]
    · simp [hn, uavg]
  simp only [hu, hz]
  exact pow_le_pow_left₀ zero_le (add_le_add (add_le_add le_rfl
    (ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμ zero_le)
      zero_le) (by norm_num)))
    (ENNReal.rpow_le_rpow hν (by norm_num))) 2

end runtimeR

end Quantum.Xmss.Hybrid

end
