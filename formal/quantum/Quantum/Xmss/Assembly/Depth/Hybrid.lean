module

public import Quantum.Xmss.Hybrid.GradedPar
public import Quantum.Xmss.Hybrid.GradedMasked
public import Quantum.Xmss.Assembly.Depth.Ports

@[expose] public section

/-!
# The masked hybrid with rounds of every sponge port (XPD)

GradedPar's graded hybrid for programs over `parSpec (recHwSpec X Z S M') (portR X Z S M')`:
rounds of any sponge port (`h`, `k`, `k'`) against the parallel runtimes of `runtimeR` and
runtime 1.

* **Rounds keep labels** (`roundKraus_apply_ne_zero_lab`): a round of Kraus steps that keep a
  label of the runtime register keeps it, whatever its ports.
* **The hidden mass of a round** (`roundHidMassR`): for a round of one port `p`, the summed
  hidden masses of its slots (`slotHid`, the call's hidden inputs, `hiddenMass_portR`); `⊤` for a
  round mixing ports (the depth programs have none).
* **The per-command bound** (`krausWeight_par_le_hidden_portR`): the Kraus weight of the difference
  of the two parallel runtimes is at most `4` times the hidden mass (`parHidMassR`).
* **The hybrid** (`sqrt_win_runtime1R_portR_le_graded`), averaged and masked by a good set
  (`uavg_win_runtime1R_portR_le_masked`, padded: `uavg_win_runtime1R_portR_le_masked_pad`):
  `E P₁ ≤ (√(E P₂) + √(4 d μ) + √ν)² + bad fraction`, `d` the number of single sponge calls and
  rounds of positive width (`spongeRounds`), `μ` the averaged hidden mass of those commands
  (`parSpongeMassR`), `ν` that of the read ports.
-/

open IPFunctor Matrix MeasureTheory
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime Quantum.Par

/-! ## Rounds keep labels -/

section roundLab

variable {m n o : Type*} {Λ' : Type*}

/-- A product of label-keeping matrices keeps labels. -/
theorem mul_apply_ne_zero_lab [Fintype n] {A : Matrix m n ℂ} {B : Matrix n o ℂ}
    {a : m → Λ'} {b : n → Λ'} {c : o → Λ'} (hA : ∀ x y, A x y ≠ 0 → a x = b y)
    (hB : ∀ y z, B y z ≠ 0 → b y = c z) : ∀ x z, (A * B) x z ≠ 0 → a x = c z := fun x z h ↦ by
  rw [Matrix.mul_apply] at h
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (hA x y (left_ne_zero_of_mul hy)).trans (hB y z (right_ne_zero_of_mul hy))

/-- A label-keeping matrix beside the identity keeps the label of the first component. -/
theorem kronecker_one_apply_ne_zero_lab {E : Type*} [DecidableEq E] {A : Matrix m n ℂ}
    {a : m → Λ'} {b : n → Λ'} (hA : ∀ x y, A x y ≠ 0 → a x = b y) :
    ∀ x y, (A ⊗ₖ (1 : Matrix E E ℂ)) x y ≠ 0 → a x.1 = b y.1 := fun x y h ↦
  hA x.1 y.1 (left_ne_zero_of_mul (by rwa [kroneckerMap_apply] at h))

/-- A basis matrix of a label-keeping map keeps labels. -/
theorem basisMatrix_apply_ne_zero_lab [DecidableEq n] (e : m → n) {a : m → Λ'} {b : n → Λ'}
    (he : ∀ x, b (e x) = a x) : ∀ y x, basisMatrix e y x ≠ 0 → b y = a x := fun y x h ↦ by
  rw [basisMatrix_apply] at h
  split_ifs at h with hy
  · rw [hy, he]
  · exact absurd rfl h

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)

/-- **Rounds keep labels.** If the Kraus operators of the ports of a round keep a label `g` of the
runtime register, so does the round's Kraus operator. -/
theorem roundKraus_apply_ne_zero_lab {Λ' : Type*} (g : R.D → Λ')
    (K : ∀ p, spec.Result p → Matrix (spec.Out p × R.D) (spec.In p × R.D) ℂ) :
    ∀ {w : ℕ} (f : Fin w → spec.Port), (∀ i r y x, K (f i) r y x ≠ 0 → g y.2 = g x.2) →
      ∀ (rs : RoundResult spec f) y x, R.roundKraus K f rs y x ≠ 0 → g y.2 = g x.2
  | 0, f, _, rs, y, x, h => by
    simp only [QuantumRuntime.roundKraus] at h
    exact basisMatrix_apply_ne_zero_lab _ (a := fun x ↦ g x.2) (b := fun y ↦ g y.2)
      (fun _ ↦ rfl) y x h
  | w + 1, f, hK, rs, y, x, h => by
    simp only [QuantumRuntime.roundKraus] at h
    have ih := roundKraus_apply_ne_zero_lab g K (fun i ↦ f i.succ) (fun i ↦ hK i.succ)
      (Fin.tail rs)
    have h1 : ∀ y q, basisMatrix (R.roundJoin f) y q ≠ 0 → g y.2 = g q.1.2 :=
      basisMatrix_apply_ne_zero_lab _ fun _ ↦ rfl
    have h2 := kronecker_one_apply_ne_zero_lab (E := spec.Out (f 0)) ih
    have h3 : ∀ q q', basisMatrix (R.roundShift f) q q' ≠ 0 → g q.1.2 = g q'.1.2 :=
      basisMatrix_apply_ne_zero_lab _ fun _ ↦ rfl
    have h4 := kronecker_one_apply_ne_zero_lab (E := roundIn spec fun i ↦ f i.succ)
      (hK 0 (rs 0))
    have h5 : ∀ q x, basisMatrix (R.roundSplit f) q x ≠ 0 → g q.1.2 = g x.2 :=
      basisMatrix_apply_ne_zero_lab _ fun _ ↦ rfl
    exact mul_apply_ne_zero_lab (mul_apply_ne_zero_lab (mul_apply_ne_zero_lab
      (mul_apply_ne_zero_lab h1 h2) h3) h4) h5 y x h

end roundLab

/-! ## Runtime 1 against `runtimeR`, with rounds of every sponge port -/

section portR

open Quantum.Sponge Quantum.Xmss.Assembly

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']

variable (X Z S M') in
/-- The classical commands of the hybrid: the classical single calls and the rounds of width
`0`. -/
def hybClsR : (parSpec (recHwSpec X Z S M') (portR X Z S M')).Port → Bool
  | .inl i => extCls X Z (Finset S × M') (recSpec S M') i
  | .inr (.round w _) => decide (w = 0)

/-- The label map: that of `runtimeR` on the single calls; rounds keep the hardwired cells. -/
def hybLabMapR : ∀ i : (parSpec (recHwSpec X Z S M') (portR X Z S M')).Port,
    (parSpec (recHwSpec X Z S M') (portR X Z S M')).Result i → Hw X Z → Hw X Z
  | .inl i, r => hwLabMap i r
  | .inr _, _ => id

/-- The difference sets: those of the read ports; empty at the rounds. -/
def hybHidSetR (Hh : Set Z) (Hk Hk' : Set X) :
    (parSpec (recHwSpec X Z S M') (portR X Z S M')).Port → Set (Hw X Z)
  | .inl i => readHidSet Hh Hk Hk' i
  | .inr _ => ∅

variable (M') in
/-- The hidden inputs of one call of a sponge port: its cell is hidden and not hardwired. -/
def slotHid (Hh : Set Z) (Hk Hk' : Set X) :
    ∀ p : SpongePort, Set (spongeIn X Z p × HwReg X Z (Finset S × M'))
  | .h => {q : (Z × X) × HwReg X Z (Finset S × M') | q.1.1 ∈ Hh ∧ q.2.2.1.1 q.1.1 = none}
  | .k => {q : (X × Z) × HwReg X Z (Finset S × M') | q.1.1 ∈ Hk ∧ q.2.2.1.2.1 q.1.1 = none}
  | .k' => {q : (X × Z) × HwReg X Z (Finset S × M') | q.1.1 ∈ Hk' ∧ q.2.2.1.2.2 q.1.1 = none}

/-- The hidden mass of a single call of a sponge port is the mass of `slotHid`. -/
theorem hiddenMass_portR (Hh : Set Z) (Hk Hk' : Set X) (p : SpongePort) :
    extWeight (hiddenMass (M := Finset S × M') Hh Hk Hk') (portR X Z S M' p) =
      diagMass (slotHid M' Hh Hk Hk' p) := by
  cases p <;> rfl

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
/-- Membership in `slotHid` depends on the query input and the hardwired part only. -/
theorem mem_slotHid_congr (Hh : Set Z) (Hk Hk' : Set X) (p : SpongePort)
    (q q' : spongeIn X Z p × HwReg X Z (Finset S × M')) (h1 : q.1 = q'.1)
    (h2 : q.2.2 = q'.2.2) : q ∈ slotHid M' Hh Hk Hk' p ↔ q' ∈ slotHid M' Hh Hk Hk' p := by
  cases p <;> simp [slotHid, h1, h2]

/-- **The hidden mass of a round**: for a round of one port, the summed hidden masses of its
slots; `⊤` for a round mixing ports. -/
noncomputable def roundHidMassR (Hh : Set Z) (Hk Hk' : Set X) {w : ℕ} (f : Fin w → SpongePort)
    (σ : Matrix ((roundIn (recHwSpec X Z S M') fun i ↦ portR X Z S M' (f i)) ×
        QReg.of (HwReg X Z (Finset S × M')))
      ((roundIn (recHwSpec X Z S M') fun i ↦ portR X Z S M' (f i)) ×
        QReg.of (HwReg X Z (Finset S × M'))) ℂ) : ℝ≥0∞ :=
  if ∀ j j', f j = f j' then ∑ j : Fin w, diagMass {x | (x.1 j, x.2) ∈ slotHid M' Hh Hk Hk' (f j)} σ
  else ⊤

/-- **The hidden mass of a command**: that of `runtimeR`'s ports on the single calls,
`roundHidMassR` on the rounds. -/
noncomputable def parHidMassR (Hh : Set Z) (Hk Hk' : Set X) :
    ∀ i : (parSpec (recHwSpec X Z S M') (portR X Z S M')).Port,
      Matrix ((parSpec (recHwSpec X Z S M') (portR X Z S M')).In i ×
          QReg.of (HwReg X Z (Finset S × M')))
        ((parSpec (recHwSpec X Z S M') (portR X Z S M')).In i ×
          QReg.of (HwReg X Z (Finset S × M'))) ℂ → ℝ≥0∞
  | .inl i => extWeight (hiddenMass Hh Hk Hk') i
  | .inr (.round _ f) => roundHidMassR Hh Hk Hk' f

/-- **The hidden mass of the quantum commands**: `parHidMassR`, `0` on the classical commands. -/
noncomputable def parSpongeMassR (Hh : Set Z) (Hk Hk' : Set X) :
    ∀ i : (parSpec (recHwSpec X Z S M') (portR X Z S M')).Port,
      Matrix ((parSpec (recHwSpec X Z S M') (portR X Z S M')).In i ×
          QReg.of (HwReg X Z (Finset S × M')))
        ((parSpec (recHwSpec X Z S M') (portR X Z S M')).In i ×
          QReg.of (HwReg X Z (Finset S × M'))) ℂ → ℝ≥0∞ :=
  fun i σ ↦ if hybClsR X Z S M' i then 0 else parHidMassR Hh Hk Hk' i σ

theorem parSpongeMassR_inl (Hh : Set Z) (Hk Hk' : Set X) (i : (recHwSpec X Z S M').Port) :
    parSpongeMassR Hh Hk Hk' (.inl i) = spongeMass Hh Hk Hk' i := by
  rw [spongeMass_eq]
  rfl

/-- A round of positive width of one port weighs the summed hidden masses of its slots. -/
theorem parSpongeMassR_round (Hh : Set Z) (Hk Hk' : Set X) {w : ℕ} (hw : w ≠ 0)
    (p : SpongePort) :
    parSpongeMassR (S := S) (M' := M') Hh Hk Hk' (.inr (.round w fun _ ↦ p)) =
      fun σ ↦ ∑ j : Fin w, diagMass {x | (x.1 j, x.2) ∈ slotHid M' Hh Hk Hk' p} σ := by
  funext σ
  have hc : ∀ j j' : Fin w, (fun _ : Fin w ↦ p) j = (fun _ ↦ p) j' := fun _ _ ↦ rfl
  show (if hybClsR X Z S M' (.inr (.round w fun _ ↦ p)) then 0 else
    roundHidMassR Hh Hk Hk' (fun _ ↦ p) σ) = _
  unfold roundHidMassR
  split_ifs with h1 <;> first | rfl | simp [hybClsR, hw] at h1

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
/-- Rounds of positive width and single quantum calls are the commands charged by
`spongeRounds`. -/
theorem spongeRounds_portR :
    spongeRounds (portR X Z S M') (extCls X Z (Finset S × M') (recSpec S M')) =
      fun i ↦ if hybClsR X Z S M' i then 0 else 1 := by
  funext i
  rcases i with i | ⟨w, f⟩
  · simp only [spongeRounds, roundCharge, widthCharge, hybClsR]
    by_cases h : extCls X Z (Finset S × M') (recSpec S M') i = true <;> simp [h]
  · simp [spongeRounds, roundCharge, widthCharge, hybClsR, extCls, hwCls]

theorem clsMass_hybHidSetR (Hh : Set Z) (Hk Hk' : Set X) :
    clsMass (D := QReg.of (HwReg X Z (Finset S × M'))) (hybClsR X Z S M') hwLab
        (hybHidSetR Hh Hk Hk') =
      parWeight (portR X Z S M') (readMass Hh Hk Hk') := by
  funext i σ
  rcases i with i | ⟨w, f⟩
  · exact congrFun (congrFun (clsMass_readHidSet (S := S) (M' := M') Hh Hk Hk') i) σ
  · simp [clsMass, hybHidSetR, parWeight, diagMass]

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]

theorem parKrausR_roundR (m₀ : Finset S × M') (p : SpongePort) (w : ℕ)
    (rs : (parSpec (recHwSpec X Z S M') (portR X Z S M')).Result (.inr (.round w fun _ ↦ p))) :
    sumKraus (krausR X Z m₀) (parKraus (portR X Z S M') (runtimeR m₀) (krausR X Z m₀))
        (.inr (.round w fun _ ↦ p)) rs =
      roundProd (fun j : Fin w ↦ slotLift (S := spongeIn X Z p)
        (N := HwReg X Z (Finset S × M')) j ((spongeHardwired X Z (hwEmpty X Z) m₀).U p)) :=
  roundKraus_mk_extend (initHw X Z m₀) (spongeHardwiredRuntime X Z (hwEmpty X Z) m₀).step
    (t := recSpec S M') recStep (krausR X Z m₀) p rs

theorem parKraus1R_roundR (L : Hw X Z) (m₀ : Finset S × M') (p : SpongePort) (w : ℕ)
    (rs : (parSpec (recHwSpec X Z S M') (portR X Z S M')).Result (.inr (.round w fun _ ↦ p))) :
    sumKraus (kraus1R X Z L m₀)
        (parKraus (portR X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀))
        (.inr (.round w fun _ ↦ p)) rs =
      roundProd (fun j : Fin w ↦ slotLift (S := spongeIn X Z p)
        (N := HwReg X Z (Finset S × M')) j ((spongeHardwired1 X Z L m₀).U p)) :=
  roundKraus_mk_extend (initHw X Z m₀) (runtime1 X Z L m₀).step (t := recSpec S M') recStep
    (kraus1R X Z L m₀) p rs

omit [Nonempty X] [Nonempty Z] in
/-- The calls of a sponge port keep the hardwired register. -/
theorem snd_eq_of_U_ne_zero {m₀ : Finset S × M'} (p : SpongePort)
    {V : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ}
    (hV : V = (spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U p ∨
      ∃ L, V = (spongeHardwired1 X Z L (M := Finset S × M') m₀).U p)
    (y x : spongeIn X Z p × HwReg X Z (Finset S × M')) (h : V y x ≠ 0) : y.2.2 = x.2.2 := by
  obtain ⟨a', s'⟩ := y
  obtain ⟨a, s⟩ := x
  rcases hV with rfl | ⟨L, rfl⟩ <;> cases p <;> exact hwPort_ne_zero_snd _ h

variable {Hh : Set Z} {Hk Hk' : Set X}

omit [Nonempty X] [Nonempty Z] in
/-- The two runtimes' calls of a sponge port differ only on its hidden inputs. -/
theorem U_sub_eq_mul_slotHid (L : Hw X Z) (m₀ : Finset S × M') (hL : Covers L Hh Hk Hk')
    (p : SpongePort) :
    (spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U p -
        (spongeHardwired1 X Z L (M := Finset S × M') m₀).U p =
      ((spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U p -
        (spongeHardwired1 X Z L (M := Finset S × M') m₀).U p) *
          setProj (slotHid M' Hh Hk Hk' p) := by
  obtain ⟨hLh, hLk, hLk'⟩ := hL
  cases p
  · exact hwPort_sub_eq _ _ _ (mem_slotHid_congr Hh Hk Hk' .h)
      (fun q hq ↦ by simp only [hwView, hwView_or_eq (w := q.2.2.1.1) (a := q.1.1) hLh hq])
  · exact hwPort_sub_eq _ _ _ (mem_slotHid_congr Hh Hk Hk' .k)
      (fun q hq ↦ by simp only [hwView, hwView_or_eq (w := q.2.2.1.2.1) (a := q.1.1) hLk hq])
  · exact hwPort_sub_eq _ _ _ (mem_slotHid_congr Hh Hk Hk' .k')
      (fun q hq ↦ by simp only [hwView, hwView_or_eq (w := q.2.2.1.2.2) (a := q.1.1) hLk' hq])

/-- The Kraus operators of `runtimeR.par` move the hardwired cells along `hybLabMapR`. -/
theorem hwLab_parKrausR_portR (m₀ : Finset S × M') :
    ∀ i r o d' j d, sumKraus (krausR X Z m₀)
      (parKraus (portR X Z S M') (runtimeR m₀) (krausR X Z m₀)) i r (o, d') (j, d) ≠ 0 →
        hwLab d' = hybLabMapR i r (hwLab d)
  | .inl i, r, o, d', j, d, h => hwLab_sumKraus2 m₀ i r o d' j d h
  | .inr (.round _ f), rs, o, d', j, d, h =>
    roundKraus_apply_ne_zero_lab (runtimeR m₀) hwLab (krausR X Z m₀)
      (fun i ↦ portR X Z S M' (f i))
      (fun _ r y x hne ↦ hwLab_sumKraus2 m₀ _ r y.1 y.2 x.1 x.2 hne) rs (o, d') (j, d) h

/-- The Kraus operators of `runtime1R.par` move the hardwired cells along `hybLabMapR`. -/
theorem hwLab_parKraus1R_portR (L : Hw X Z) (m₀ : Finset S × M') :
    ∀ i r o d' j d, sumKraus (kraus1R X Z L m₀)
      (parKraus (portR X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)) i r (o, d')
        (j, d) ≠ 0 → hwLab d' = hybLabMapR i r (hwLab d)
  | .inl i, r, o, d', j, d, h => hwLab_sumKraus1 L m₀ i r o d' j d h
  | .inr (.round _ f), rs, o, d', j, d, h =>
    roundKraus_apply_ne_zero_lab (runtime1R X Z L m₀) hwLab (kraus1R X Z L m₀)
      (fun i ↦ portR X Z S M' (f i))
      (fun _ r y x hne ↦ hwLab_sumKraus1 L m₀ _ r y.1 y.2 x.1 x.2 hne) rs (o, d') (j, d) h

/-- At a classical command, the two parallel runtimes agree outside the difference sets. -/
theorem parKraus_eq_of_not_mem_portR (L : Hw X Z) (m₀ : Finset S × M')
    (hL : Covers L Hh Hk Hk') :
    ∀ i, hybClsR X Z S M' i = true → ∀ r o d' j d, hwLab d ∉ hybHidSetR Hh Hk Hk' i →
      sumKraus (krausR X Z m₀) (parKraus (portR X Z S M') (runtimeR m₀) (krausR X Z m₀))
          i r (o, d') (j, d) =
        sumKraus (kraus1R X Z L m₀)
          (parKraus (portR X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)) i r (o, d')
          (j, d)
  | .inl i, hi, r, o, d', j, d, hd => sumKraus_eq_of_not_mem_readHidSet L m₀ hL i hi r o d' j d hd
  | .inr (.round w f), hi, rs, o, d', j, d, _ => by
    have hw : w = 0 := by simpa [hybClsR] using hi
    subst hw
    obtain rfl : f = fun _ ↦ .h := funext fun i ↦ i.elim0
    exact (congrFun (congrFun (parKrausR_roundR m₀ .h 0 rs) (o, d')) (j, d)).trans
      (congrFun (congrFun (parKraus1R_roundR L m₀ .h 0 rs) (o, d')) (j, d)).symm

/-- **The per-command bound**: the Kraus weight of the difference of the two parallel runtimes
is at most `4` times the hidden mass of the command. -/
theorem krausWeight_par_le_hidden_portR (L : Hw X Z) (m₀ : Finset S × M')
    (hL : Covers L Hh Hk Hk') (i : (parSpec (recHwSpec X Z S M') (portR X Z S M')).Port)
    {σ : Matrix ((parSpec (recHwSpec X Z S M') (portR X Z S M')).In i ×
        QReg.of (HwReg X Z (Finset S × M')))
      ((parSpec (recHwSpec X Z S M') (portR X Z S M')).In i ×
        QReg.of (HwReg X Z (Finset S × M'))) ℂ} (hσ : σ.PosSemidef) :
    krausWeight (fun i r ↦
      sumKraus (krausR X Z m₀) (parKraus (portR X Z S M') (runtimeR m₀) (krausR X Z m₀)) i r -
        sumKraus (kraus1R X Z L m₀)
          (parKraus (portR X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)) i r) i σ ≤
      4 * parHidMassR Hh Hk Hk' i σ := by
  rcases i with i | ⟨w, f⟩
  · exact krausWeight_le_hidden_extend L m₀ hL _ i hσ
  · by_cases hc : ∀ j j', f j = f j'
    · obtain ⟨p, rfl⟩ : ∃ p, f = fun _ ↦ p := by
        cases w with
        | zero => exact ⟨.h, funext fun i ↦ i.elim0⟩
        | succ w => exact ⟨f 0, funext fun j ↦ hc j 0⟩
      have hdiff := U_sub_eq_mul_slotHid L m₀ hL p
      have hagree : ∀ y x, x ∉ slotHid M' Hh Hk Hk' p →
          (spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U p y x =
            (spongeHardwired1 X Z L (M := Finset S × M') m₀).U p y x := fun y x hx ↦ by
        have e := congrFun (congrFun hdiff y) x
        rw [Matrix.sub_apply, setProj, mul_diagonal, Set.indicator_of_notMem hx, mul_zero,
          sub_eq_zero] at e
        exact e
      have hkeep : ∀ V : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
          (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ,
          (V = (spongeHardwired X Z (hwEmpty X Z) (M := Finset S × M') m₀).U p ∨
            ∃ L, V = (spongeHardwired1 X Z L (M := Finset S × M') m₀).U p) →
          ∀ y x, V y x ≠ 0 → ∀ b, ((b, y.2) ∈ slotHid M' Hh Hk Hk' p ↔
            (b, x.2) ∈ slotHid M' Hh Hk Hk' p) :=
        fun V hV y x hne b ↦
          mem_slotHid_congr Hh Hk Hk' p _ _ rfl (snd_eq_of_U_ne_zero p hV y x hne)
      have e₂ := parKrausR_roundR (X := X) (Z := Z) (S := S) (M' := M') m₀ p w
      have e₁ := parKraus1R_roundR (S := S) L m₀ p w
      have hm : parHidMassR Hh Hk Hk' (.inr (.round w fun _ ↦ p)) σ =
          ∑ j : Fin w, diagMass {x | (x.1 j, x.2) ∈ slotHid M' Hh Hk Hk' p} σ := by
        show roundHidMassR Hh Hk Hk' (fun _ ↦ p) σ = _
        unfold roundHidMassR
        split_ifs
        rfl
      rw [hm]
      calc krausWeight (fun i r ↦
            sumKraus (krausR X Z m₀) (parKraus (portR X Z S M') (runtimeR m₀) (krausR X Z m₀))
              i r - sumKraus (kraus1R X Z L m₀)
                (parKraus (portR X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)) i r)
              (.inr (.round w fun _ ↦ p)) σ
          = ∑' _ : Fin w → Unit, ENNReal.ofReal (MatrixMap.conj
              (roundProd (fun j : Fin w ↦ slotLift (S := spongeIn X Z p)
                (N := HwReg X Z (Finset S × M')) j
                  ((spongeHardwired X Z (hwEmpty X Z) m₀).U p)) -
                roundProd (fun j : Fin w ↦ slotLift (S := spongeIn X Z p)
                  (N := HwReg X Z (Finset S × M')) j ((spongeHardwired1 X Z L m₀).U p)))
                    σ).trace.re :=
            tsum_congr fun rs ↦ by beta_reduce; rw [e₂ rs, e₁ rs]; rfl
        _ = ENNReal.ofReal (MatrixMap.conj
              (roundProd (fun j : Fin w ↦ slotLift (S := spongeIn X Z p)
                (N := HwReg X Z (Finset S × M')) j
                  ((spongeHardwired X Z (hwEmpty X Z) m₀).U p)) -
                roundProd (fun j : Fin w ↦ slotLift (S := spongeIn X Z p)
                  (N := HwReg X Z (Finset S × M')) j ((spongeHardwired1 X Z L m₀).U p)))
                    σ).trace.re :=
            by rw [tsum_fintype, Fintype.sum_unique]
        _ ≤ 4 * ∑ j : Fin w, diagMass {x | (x.1 j, x.2) ∈ slotHid M' Hh Hk Hk' p} σ :=
            ofReal_trace_conj_roundProd_sub_le _ _
              ((spongeHardwired X Z (hwEmpty X Z) m₀).unitary p)
              ((spongeHardwired1 X Z L m₀).unitary p) _ hagree
              (hkeep _ (Or.inl rfl)) (hkeep _ (Or.inr ⟨L, rfl⟩)) hσ
    · have hm : parHidMassR Hh Hk Hk' (.inr (.round w f)) σ = ⊤ := by
        simp [parHidMassR, roundHidMassR, hc]
      rw [hm, ENNReal.mul_top (by norm_num)]
      exact le_top

variable {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ]

/-- **Runtime 1 against `runtimeR`, with rounds of every sponge port, graded.**
`√P₁ ≤ √P₂ + ∑ₙ √(4 μₙ) + √ν`, `μₙ` the hidden mass of the `n`-th quantum command (a single
sponge call or a round of positive width) of the run against `runtimeR.par`, `ν` the hidden mass
at the read ports summed over all calls. -/
theorem sqrt_win_runtime1R_portR_le_graded (L : Hw X Z) (m₀ : Finset S × M')
    (hL : Covers L Hh Hk Hk')
    (x : QuantumComp Λ (parSpec (recHwSpec X Z S M') (portR X Z S M')) Xf A) (ρ : SubState A)
    (f : (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) :
    ((runtime1R X Z L m₀).par (portR X Z S M')).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      ((runtimeR m₀).par (portR X Z S M')).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) +
        ∑' n, (4 * kindWeight ((runtimeR m₀).par (portR X Z S M')) I (hybClsR X Z S M')
          (parHidMassR Hh Hk Hk') x
            (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) n) ^ (2⁻¹ : ℝ) +
        ((runtimeR m₀).par (portR X Z S M')).totalWeight I
          (parWeight (portR X Z S M') (readMass Hh Hk Hk')) x
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ^ (2⁻¹ : ℝ) := by
  have h := rpow_inv_two_outcomeLawWith_le_graded I (initHw X Z m₀)
    (par_branch_eq_conj (portR X Z S M') (runtimeR m₀) (krausR X Z m₀)
      (extend_branch_eq_conj (t := recSpec S M') (runtime2 X Z m₀) recStep (runtime2_branch m₀)
        fun T r ↦ recStep_branch T r))
    (par_branch_eq_conj (portR X Z S M') (runtime1R X Z L m₀) (kraus1R X Z L m₀)
      (extend_branch_eq_conj (t := recSpec S M') (runtime1 X Z L m₀) recStep
        (runtime1_branch L m₀) fun T r ↦ recStep_branch T r))
    (cls := hybClsR X Z S M') (κ := hwLab) (F := hybLabMapR) (S := hybHidSetR Hh Hk Hk')
    (hwLab_parKrausR_portR m₀) (hwLab_parKraus1R_portR L m₀)
    (parKraus_eq_of_not_mem_portR L m₀ hL) (hwEmpty X Z) (querySupportedOn_initHw m₀) x ρ f hE
  refine h.trans (add_le_add (add_le_add le_rfl
    (ENNReal.tsum_le_tsum fun n ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)))
    (le_of_eq (congrArg (· ^ (2⁻¹ : ℝ)) (congrArg (fun W ↦
      ((runtimeR m₀).par (portR X Z S M')).totalWeight I W x
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix))
      (clsMass_hybHidSetR Hh Hk Hk')))))
  calc _ ≤ kindWeight ((runtimeR m₀).par (portR X Z S M')) I (hybClsR X Z S M')
        (fun i σ ↦ 4 * parHidMassR Hh Hk Hk' i σ) x
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) n :=
        kindWeight_mono ((runtimeR m₀).par (portR X Z S M')) I (hybClsR X Z S M')
          (fun i σ hσ ↦ krausWeight_par_le_hidden_portR L m₀ hL i hσ) x
          (ρ.prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef n
    _ = _ := kindWeight_const_mul ((runtimeR m₀).par (portR X Z S M')) I (hybClsR X Z S M') 4
        x _ n

variable {Θ : Type*} [Fintype Θ]

/-- **Runtime 1 against `runtimeR`, with rounds of every sponge port, averaged and masked by a
good set.** With at most `d` single sponge calls and rounds of positive width on every path
(`spongeRounds`), if the averaged hidden mass of the quantum commands (`parSpongeMassR`) over the
good set `G` (`0` off `G`) is at most `μ` and that at the read ports at most `ν`, then
`E P₁ ≤ (√(E P₂) + √(4 d μ) + √ν)² + |θ ∉ G| / |Θ|`. -/
theorem uavg_win_runtime1R_portR_le_masked (L : Θ → Hw X Z)
    (Hhθ : Θ → Set Z) (Hkθ Hk'θ : Θ → Set X) (hL : ∀ θ, Covers (L θ) (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (m₀ : Finset S × M')
    (x : Θ → QuantumComp Λ (parSpec (recHwSpec X Z S M') (portR X Z S M')) Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) (d : ℕ)
    (hd : ∀ θ, IFreeM.IsChargeBound (x θ)
      (portCharge (spongeRounds (portR X Z S M') (extCls X Z (Finset S × M') (recSpec S M'))))
      d)
    (G : Θ → Prop) [DecidablePred G] (μ ν : ℝ≥0∞)
    (hμ : uavg (fun θ ↦ if G θ then ((runtimeR m₀).par (portR X Z S M')).totalWeight I
      (parSpongeMassR (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ μ)
    (hν : uavg (fun θ ↦ if G θ then ((runtimeR m₀).par (portR X Z S M')).totalWeight I
      (parWeight (portR X Z S M') (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ))) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ ν) :
    uavg (fun θ ↦ ((runtime1R X Z (L θ) m₀).par (portR X Z S M')).evalDistMap I (x θ) (ρ θ)
        (f θ) E) ≤
      (uavg (fun θ ↦ ((runtimeR m₀).par (portR X Z S M')).evalDistMap I (x θ) (ρ θ) (f θ) E) ^
          (2⁻¹ : ℝ) + (4 * (d * μ)) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)) ^ 2 +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun θ ↦ ¬G θ).card := by
  set P₁ : Θ → ℝ≥0∞ := fun θ ↦ ((runtime1R X Z (L θ) m₀).par (portR X Z S M')).evalDistMap I
    (x θ) (ρ θ) (f θ) E with hP₁
  set P₂ : Θ → ℝ≥0∞ := fun θ ↦ ((runtimeR m₀).par (portR X Z S M')).evalDistMap I (x θ) (ρ θ)
    (f θ) E with hP₂
  set T : Θ → ℝ≥0∞ := fun θ ↦ ((runtimeR m₀).par (portR X Z S M')).totalWeight I
    (parSpongeMassR (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
    ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) with hT
  set V : Θ → ℝ≥0∞ := fun θ ↦ ((runtimeR m₀).par (portR X Z S M')).totalWeight I
    (parWeight (portR X Z S M') (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ))) (x θ)
    ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) with hV
  have h0 : (0 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  have hz : ∀ (c : ℝ≥0∞), ∑' n : ℕ, (4 * if n = 0 then c else 0) ^ (2⁻¹ : ℝ) =
      (4 * c) ^ (2⁻¹ : ℝ) := fun c ↦ by
    rw [tsum_eq_single 0 fun n hn ↦ by simp [hn, h0]]
    simp
  have hθ : ∀ θ, P₁ θ ^ (2⁻¹ : ℝ) ≤ P₂ θ ^ (2⁻¹ : ℝ) +
      ∑' n : ℕ, (4 * if n = 0 then (d : ℝ≥0∞) * T θ else 0) ^ (2⁻¹ : ℝ) + V θ ^ (2⁻¹ : ℝ) := by
    intro θ
    have hdθ := hd θ
    rw [spongeRounds_portR] at hdθ
    rw [hz]
    refine (sqrt_win_runtime1R_portR_le_graded I (L θ) m₀ (hL θ) (x θ) (ρ θ) (f θ) hE).trans
      (add_le_add (add_le_add le_rfl ((tsum_rpow_kindWeight_le
        ((runtimeR m₀).par (portR X Z S M')) I _ (x θ) hdθ _ 4).trans_eq ?_)) le_rfl)
    rw [mul_left_comm]
    rfl
  have hm : ∀ θ, (if G θ then P₁ θ else 0) ^ (2⁻¹ : ℝ) ≤ (if G θ then P₂ θ else 0) ^ (2⁻¹ : ℝ) +
      ∑' n : ℕ, (4 * (fun θ n ↦ if n = 0 then (d : ℝ≥0∞) * (if G θ then T θ else 0) else 0) θ n) ^
        (2⁻¹ : ℝ) + (if G θ then V θ else 0) ^ (2⁻¹ : ℝ) := by
    intro θ
    by_cases hG : G θ
    · simp only [hG, ↓reduceIte]
      exact hθ θ
    · simp only [hG, ↓reduceIte, h0]
      exact zero_le
  have h1 := uavg_le_of_hybrid_graded _ _ _ _ hm
  have hu : ∀ n : ℕ, uavg (fun θ ↦ if n = 0 then (d : ℝ≥0∞) * (if G θ then T θ else 0) else 0) =
      if n = 0 then (d : ℝ≥0∞) * uavg (fun θ ↦ if G θ then T θ else 0) else 0 := fun n ↦ by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte, uavg_const_mul]
    · simp [hn, uavg]
  simp only [hu, hz] at h1
  have hsplit : uavg P₁ ≤ uavg (fun θ ↦ if G θ then P₁ θ else 0) +
      uavg (fun θ ↦ if G θ then (0 : ℝ≥0∞) else 1) := by
    rw [← uavg_add]
    refine uavg_mono fun θ ↦ ?_
    by_cases hG : G θ
    · simp [hG]
    · simp only [hG, ↓reduceIte, zero_add]
      exact evalDistMap_apply_le_one _ I _ _ _ _
  refine hsplit.trans (add_le_add (h1.trans ?_) (uavg_ite_zero_one G).le)
  refine pow_le_pow_left₀ zero_le (add_le_add (add_le_add ?_ ?_) ?_) 2
  · refine ENNReal.rpow_le_rpow (uavg_mono fun θ ↦ ?_) (by norm_num)
    by_cases hG : G θ <;> simp [hG]
  · exact ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμ zero_le)
      zero_le) (by norm_num)
  · exact ENNReal.rpow_le_rpow hν (by norm_num)

/-- **The masked hybrid with rounds of every sponge port, padded good set**: the good set `G`
lives on the table padded by `E'`, the masses are averaged over the padded table, and the bad
fraction is that of the padded table. -/
theorem uavg_win_runtime1R_portR_le_masked_pad {E' : Type*} [Fintype E'] [Nonempty E']
    (L : Θ → Hw X Z) (Hhθ : Θ → Set Z) (Hkθ Hk'θ : Θ → Set X)
    (hL : ∀ θ, Covers (L θ) (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (m₀ : Finset S × M')
    (x : Θ → QuantumComp Λ (parSpec (recHwSpec X Z S M') (portR X Z S M')) Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) (d : ℕ)
    (hd : ∀ θ, IFreeM.IsChargeBound (x θ)
      (portCharge (spongeRounds (portR X Z S M') (extCls X Z (Finset S × M') (recSpec S M'))))
      d)
    (G : Θ × E' → Prop) [DecidablePred G] (μ ν : ℝ≥0∞)
    (hμ : uavg (fun t : Θ × E' ↦ if G t then ((runtimeR m₀).par (portR X Z S M')).totalWeight I
      (parSpongeMassR (Hhθ t.1) (Hkθ t.1) (Hk'θ t.1)) (x t.1)
      ((ρ t.1).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ μ)
    (hν : uavg (fun t : Θ × E' ↦ if G t then ((runtimeR m₀).par (portR X Z S M')).totalWeight I
      (parWeight (portR X Z S M') (readMass (Hhθ t.1) (Hkθ t.1) (Hk'θ t.1))) (x t.1)
      ((ρ t.1).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ ν) :
    uavg (fun θ ↦ ((runtime1R X Z (L θ) m₀).par (portR X Z S M')).evalDistMap I (x θ) (ρ θ)
        (f θ) E) ≤
      (uavg (fun θ ↦ ((runtimeR m₀).par (portR X Z S M')).evalDistMap I (x θ) (ρ θ) (f θ) E) ^
          (2⁻¹ : ℝ) + (4 * (d * μ)) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)) ^ 2 +
        (Fintype.card (Θ × E') : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬G t).card := by
  have h1 := uavg_pad (P := E') fun θ ↦
    ((runtime1R X Z (L θ) m₀).par (portR X Z S M')).evalDistMap I (x θ) (ρ θ) (f θ) E
  have h2 := uavg_pad (P := E') fun θ ↦
    ((runtimeR m₀).par (portR X Z S M')).evalDistMap I (x θ) (ρ θ) (f θ) E
  have h := uavg_win_runtime1R_portR_le_masked I (fun t : Θ × E' ↦ L t.1)
    (fun t ↦ Hhθ t.1) (fun t ↦ Hkθ t.1) (fun t ↦ Hk'θ t.1) (fun t ↦ hL t.1) m₀ (fun t ↦ x t.1)
    (fun t ↦ ρ t.1) (fun t ↦ f t.1) hE d (fun t ↦ hd t.1) G μ ν hμ hν
  rw [h1, h2] at h
  exact h

end portR

end Quantum.Xmss.Hybrid

end
