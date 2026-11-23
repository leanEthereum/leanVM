module

public import Quantum.StdModel.Qrom.CpreCalls
public import Quantum.Xmss.Assembly.Masses
public import Quantum.Xmss.Hybrid.Mismatch

@[expose] public section

/-!
# The hidden-cell hybrid of the CPRE game in the QROM (runtime 1 against runtime 2)

The QROM CPRE game of a straight-line reduction is runtime 1 on the realized template
(`probAvg_cpre_slRed_eq_runtime1R`), averaged over the parameter `P` and the hidden values `θ`
(`uavg_thetaOf`). The graded hybrid (`uavg_win_runtime1R_le_graded_total`, at the hidden values
`Par × ((s : CSrc ch) → CD ch s)`) compares it with runtime 2 (`p2C`, from the empty memory
`m0C`), at the cost of the hidden masses of runtime 1's cells (`hidCells P θ`, the honest cells).

* **Sources** (`cellSrc`, `srcVals`, `sourcesC`): under the cell decoding `CellDec ch P` (an
  honest cell determines its position and its chain value), a hidden cell not hardwired in a state
  of the source invariant has its position's source coordinate unrevealed, and the cell fixes that
  coordinate up to a fiber of the truncation: mass at most `kappaC Val F` per call
  (`card_srcVals_mul_le`), `F` the largest fiber of `ch.step.trunc`.
* **Sponge calls** (`uavg_spongeMass_le`): at most `n · κ` for an adversary of `n` hash calls.
* **Reads** (`uavg_readMass_le`): only reads at step cells carry mass (`readMass_le_readStepQ`);
  they are the reduction's step-cell reads, `c₀ + m k + c₁`, and the decision's walk, `lenMax ch`
  (`readCalls_cpreT`). Program and record ports cost nothing.
* **The hybrid** (`probAvg_cpre_slRed_le_hybrid`):
  `probAvg ≤ (√(E p2C) + √(4 n · n κ) + √(v κ))²`, `v = c₀ + m k + c₁ + lenMax ch`.
-/

open Matrix IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom.CpreQ

open Quantum Quantum.Qrom QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid Props HashSig
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR runtime1R realizeT extCls Sources
  sum_totalWeight_portMass_runtimeR_le_inv viewBy_runtimeR_of_disc)

variable {Par Tw J Val Fn Out : Type} {Msg : Fn → Type} {ch : Chains Par Tw J Val}

/-! ## The hidden cells and the cell decoding -/

section cells

/-- **The hidden cells at `P` and `θ`**: the honest cells. -/
def hidCells (P : Par) (θ : (s : CSrc ch) → CD ch s) : Set HashDomain :=
  {z | ∃ p, cellOf P θ p = z}

theorem thetaOf_split (θ : (s : CSrc ch) → CD ch s) :
    thetaOf (fun j ↦ θ (.inl j)) (fun p ↦ θ (.inr p)) = θ := by
  funext x
  cases x <;> rfl

variable (ch) in
/-- **The cell decoding at `P`**: an honest cell determines its position and the chain value
there, whatever the hidden values. -/
def CellDec (P : Par) : Prop :=
  ∀ (θ θ' : (s : CSrc ch) → CD ch s) (p p' : CPos ch), cellOf P θ p = cellOf P θ' p' →
    p = p' ∧ cval θ p.1 p.2 = cval θ' p'.1 p'.2

theorem CellDec.inj {P : Par} (h : CellDec ch P) (θ : (s : CSrc ch) → CD ch s) :
    Function.Injective (cellOf (ch := ch) P θ) :=
  fun _ _ he ↦ (h θ θ _ _ he).1

variable [Fintype J] [DecidableEq J]

/-- **Runtime 1's hardwired cells at `P` and `θ`**: the lazy table of the starts and outputs. -/
noncomputable def tableHw (P : Par) (hinj : ∀ θ, Function.Injective (cellOf (ch := ch) P θ))
    (θ : (s : CSrc ch) → CD ch s) : Hw HashOutput HashDomain :=
  (lazyT P (fun j ↦ θ (.inl j)) hinj).hwOf (fun p ↦ θ (.inr p))

omit [Fintype J] [DecidableEq J] in
theorem covers_tableHw (P : Par) (hinj : ∀ θ, Function.Injective (cellOf (ch := ch) P θ))
    (θ : (s : CSrc ch) → CD ch s) : Covers (tableHw P hinj θ) (hidCells P θ) ∅ ∅ := by
  refine ⟨fun z hz ↦ ?_, fun _ hx ↦ absurd rfl hx, fun _ hx ↦ absurd rfl hx⟩
  by_contra h
  apply hz
  show (lazyT P (fun j ↦ θ (.inl j)) hinj).tableDb (fun p ↦ θ (.inr p)) (fun p ↦ θ (.inr p)) z =
    none
  exact (lazyT P _ hinj).tableDb_of_forall_ne fun p hp ↦
    h ⟨p, (congrArg (cellOf P · p) (thetaOf_split θ)).symm.trans hp⟩

variable [Fintype Val]

/-- The hidden values as the starts and the honest outputs. -/
def thetaEquiv : ((s : CSrc ch) → CD ch s) ≃ (J → Val) × (CPos ch → HashOutput) where
  toFun θ := (fun j ↦ θ (.inl j), fun p ↦ θ (.inr p))
  invFun x := thetaOf x.1 x.2
  left_inv θ := thetaOf_split θ
  right_inv _ := rfl

/-- **The average over the starts and the honest outputs is the average over the hidden
values.** -/
theorem uavg_thetaOf (G : (J → Val) → (CPos ch → HashOutput) → ℝ≥0∞) :
    (uavg fun s ↦ uavg fun v ↦ G s v) =
      uavg fun θ : (s : CSrc ch) → CD ch s ↦ G (fun j ↦ θ (.inl j)) (fun p ↦ θ (.inr p)) := by
  rw [← uavg_prod (fun x : (J → Val) × (CPos ch → HashOutput) ↦ G x.1 x.2)]
  exact (uavg_equiv thetaEquiv _).symm

end cells

/-! ## The sources of the hidden cells -/

section sources

/-- The chain value a source coordinate carries: a start itself, a cell's output truncated. -/
def srcValC : (s : CSrc ch) → CD ch s → Val
  | .inl _, d => d
  | .inr _, d => ch.step.trunc d

theorem cval_eq_srcValC (θ : (s : CSrc ch) → CD ch s) (p : CPos ch) :
    cval θ p.1 p.2 = srcValC (srcP p) (θ (srcP p)) := by
  rcases p with ⟨j, ⟨_ | ν, h⟩⟩
  · rfl
  · show cval θ j (ν + 1) = _
    have hν : ν < ch.len j := by omega
    simp only [cval, hν, ↓reduceDIte]
    rfl

variable [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val]

open Classical in
/-- The source coordinates of a cell: that of the position it decodes to, if any. -/
noncomputable def cellSrc (P : Par) (z : HashDomain) : Finset (CSrc ch) :=
  if h : ∃ p : CPos ch, ∃ θ, cellOf P θ p = z then {srcP h.choose} else ∅

open Classical in
/-- The values of the coordinate `s`, the others as in `θ`, for which `z` is the honest cell of a
position whose source is `s`. -/
noncomputable def srcVals (P : Par) (z : HashDomain) (s : CSrc ch)
    (θ : (s : CSrc ch) → CD ch s) : Finset (CD ch s) :=
  Finset.univ.filter fun d ↦ ∃ p, srcP p = s ∧ cellOf P (Function.update θ s d) p = z

omit [DecidableEq Val] in
theorem srcVals_update (P : Par) (z : HashDomain) (s : CSrc ch) (θ : (s : CSrc ch) → CD ch s)
    (d : CD ch s) : srcVals P z s (Function.update θ s d) = srcVals P z s θ := by
  simp only [srcVals, Function.update_idem]

omit [DecidableEq Val] in
theorem srcValC_eq_of_mem {P : Par} (hdec : CellDec ch P) {z : HashDomain} {s : CSrc ch}
    {θ : (s : CSrc ch) → CD ch s} {d d' : CD ch s} (hd : d ∈ srcVals P z s θ)
    (hd' : d' ∈ srcVals P z s θ) : srcValC s d = srcValC s d' := by
  simp only [srcVals, Finset.mem_filter, Finset.mem_univ, true_and] at hd hd'
  obtain ⟨p, hp, hz⟩ := hd
  obtain ⟨p', hp', hz'⟩ := hd'
  have h := (hdec _ _ p p' (hz.trans hz'.symm)).2
  rw [cval_eq_srcValC, cval_eq_srcValC, hp, hp', Function.update_self,
    Function.update_self] at h
  exact h

variable (Val) in
/-- **The mass per call**: a start's `1/|Val|`, or a truncation fiber's `F/|HashOutput|`. -/
noncomputable def kappaC (F : ℕ) : ℝ≥0∞ :=
  max ((Fintype.card Val : ℝ≥0∞)⁻¹) ((F : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹)

/-- **A cell fixes its source up to a truncation fiber.** -/
theorem card_srcVals_mul_le {P : Par} (hdec : CellDec ch P) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y : HashOutput ↦ ch.step.trunc y = o).card ≤ F)
    (z : HashDomain) (s : CSrc ch) (θ : (s : CSrc ch) → CD ch s) :
    ((srcVals P z s θ).card : ℝ≥0∞) * (Fintype.card (CD ch s) : ℝ≥0∞)⁻¹ ≤ kappaC Val F := by
  rcases (srcVals P z s θ).eq_empty_or_nonempty with he | ⟨d₀, hd₀⟩
  · simp [he]
  · have hsub : srcVals P z s θ ⊆ Finset.univ.filter fun d ↦ srcValC s d = srcValC s d₀ :=
      fun d hd ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, srcValC_eq_of_mem hdec hd hd₀⟩
    have hc := Finset.card_le_card hsub
    cases s with
    | inl j =>
      have h1 : (Finset.univ.filter fun d : CD ch (.inl j) ↦
          srcValC (.inl j) d = srcValC (.inl j) d₀).card ≤ 1 :=
        Finset.card_le_one.mpr fun a ha b hb ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact ha.trans hb.symm
      rw [show Fintype.card (CD ch (.inl j)) = Fintype.card Val from rfl]
      refine le_trans ?_ (le_max_left _ _)
      calc ((srcVals P z (.inl j) θ).card : ℝ≥0∞) * (Fintype.card Val : ℝ≥0∞)⁻¹
          ≤ 1 * (Fintype.card Val : ℝ≥0∞)⁻¹ := by
            gcongr
            exact_mod_cast hc.trans h1
        _ = _ := one_mul _
    | inr q =>
      have h1 : (srcVals P z (.inr q) θ).card ≤ F := hc.trans (hF _)
      rw [show Fintype.card (CD ch (.inr q)) = Fintype.card HashOutput from rfl]
      refine le_trans ?_ (le_max_right _ _)
      gcongr

/-- **The sources of the hidden cells** on the states of the source invariant. -/
noncomputable def sourcesC (P : Par) (hdec : CellDec ch P) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y : HashOutput ↦ ch.step.trunc y = o).card ≤ F) :
    Sources HashOutput HashDomain (CSrc ch) JMem (CSrc ch) (CD ch) (fun r ↦ r.2.2.1)
      (fun θ ↦ SrcInv P θ) (hidCells P) (fun _ ↦ ∅) (fun _ ↦ ∅) (kappaC Val F) where
  sh z _ := cellSrc P z
  sk _ _ := ∅
  sk' _ _ := ∅
  Fh z _ s θ := srcVals P z s θ
  Fk _ _ _ _ := ∅
  Fk' _ _ _ _ := ∅
  hFh z _ s θ d := srcVals_update P z s θ d
  hFk _ _ _ _ _ := rfl
  hFk' _ _ _ _ _ := rfl
  hh θ z r hinv hz hnone := by
    obtain ⟨p, rfl⟩ := hz
    have hex : ∃ p' : CPos ch, ∃ θ', cellOf P θ' p' = cellOf P θ p := ⟨p, θ, rfl⟩
    have hc : cellSrc P (cellOf P θ p) = {srcP p} := by
      rw [cellSrc, dite_eq_left hex]
      obtain ⟨θ', h'⟩ := hex.choose_spec
      rw [(hdec _ _ _ _ h').1]
    refine ⟨srcP p, by rw [hc]; exact Finset.mem_singleton_self _,
      fun hp ↦ hinv p hp hnone, ?_⟩
    simp only [srcVals, Finset.mem_filter, Finset.mem_univ, true_and, Function.update_eq_self]
    exact ⟨p, rfl, rfl⟩
  hk _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hk' _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hκh z _ θ := by
    unfold cellSrc
    split
    · rw [Finset.sum_singleton]
      exact card_srcVals_mul_le hdec hF z _ θ
    · simp
  hκk _ _ _ := by simp
  hκk' _ _ _ := by simp

end sources

/-! ## The masses of the game -/

section masses

/-- A trace-weighted count summed over a finite type. -/
theorem sum_mul_trace_le {Θ : Type*} [Fintype Θ] (κ t : ℝ≥0∞) (ht : t ≤ 1) (N : ℕ) :
    κ * (N * ∑ _θ : Θ, t) ≤ N * κ * Fintype.card Θ := by
  calc κ * (N * ∑ _θ : Θ, t)
      ≤ κ * (N * ∑ _θ : Θ, (1 : ℝ≥0∞)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun _ _ ↦ ht) zero_le) zero_le
    _ = N * κ * Fintype.card Θ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← mul_assoc, mul_comm κ]

theorem uavg_const_le {α : Type*} [Fintype α] (c : ℝ≥0∞) : (uavg fun _ : α ↦ c) ≤ c := by
  cases isEmpty_or_nonempty α with
  | inl h => simp [uavg]
  | inr h => exact (uavg_const c).le

/-- The sponge calls: charge `1` per sponge call is `rCharge 1 0`. -/
theorem spongeCharge_eq (P : Par) :
    (fun i ↦ if extCls HashOutput HashDomain (Finset (CSrc ch) × JMem) (recSpec (CSrc ch) JMem) i
      then 0 else 1) = rCharge (ch := ch) 1 0 P := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 0).symm
  · rfl
  · rfl

/-- The reads at step cells: charge `1` per such read is `rCharge 0 1`. -/
theorem readStepCharge_eq (P : Par) :
    (fun i ↦ if readStepQ (ch := ch) P i = true then 1 else 0) = rCharge (ch := ch) 0 1 P := by
  funext i
  rcases i with ((i | r) | p) | T <;> rfl

variable [Fintype J] [DecidableEq J]

/-- **The initial memory of the hybrid**: nothing revealed, nothing recorded. -/
def m0C : Finset (CSrc ch) × JMem :=
  (∅, ∅)

/-- The initial state of the game and the register. -/
noncomputable def initC :
    Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem))) ℂ :=
  (SubState.basis ()).matrix ⊗ₖ
    (runtimeR (X := HashOutput) (Z := HashDomain) (m0C (ch := ch))).init.matrix

theorem initC_posSemidef : (initC (ch := ch)).PosSemidef :=
  ((SubState.basis ()).prod
    (runtimeR (X := HashOutput) (Z := HashDomain) (m0C (ch := ch))).init).posSemidef

theorem ofReal_trace_initC_le_one : ENNReal.ofReal (initC (ch := ch)).trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0C (ch := ch))).init).trace_re_le_one

variable [Fintype Val] [DecidableEq Val] [Inhabited Val]

variable {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q} (C : TwColl Par Tw Fn Msg Out) (P : Par)
  (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
  (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
  (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
  (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
    (J × ℕ × Val))

/-- The realized template is lazy in the hidden values. -/
theorem viewByOn_cpreT (m₀ : Finset (CSrc ch) × JMem)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem))) ℂ)
    (j : ℕ) :
    ViewByOn (runtimeR m₀) LocalSig.Interp.instruments (fun i ↦ i.isLeft = true)
      (fun r ↦ r.2.2.1) (fun θ ↦ realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
      (fun _ ↦ ρ) j :=
  (viewBy_runtimeR_of_disc _ m₀ (cpreT (ch := ch) C P pre adv st0 σ post) ∅
    (disc_cpreT C P pre adv st0 σ post ∅) (fun _ ↦ ρ) (lazy_const _ ρ)
    (fun _ ↦ suppAt_empty _ ρ) j).viewByOn _

variable (we : CpreQuery J Tw Fn Msg → ℕ)
  (hC : ∀ l t x, Common.QueryCostAtMost (C.eval romWorld l P t x) (stepW (ch := ch) P)
    (we (.eval l t x)))
  {c₀ m k c₁ n : ℕ}
  (hpre : Common.QueryCostAtMost pre (redW (ch := ch) P we) c₀)
  (hσ : ∀ st q, Common.QueryCostAtMost (σ st q) (redW (ch := ch) P we) m)
  (hpost : ∀ s0 f st, Common.QueryCostAtMost (post s0 f st) (redW (ch := ch) P we) c₁)
  (hn : ∀ s0, IFreeM.IsChargeBound (adv s0)
    (Quantum.StdModel.cmdCharge Quantum.StdModel.hashCharge) n)
  (hk : ∀ s0, IFreeM.IsChargeBound (adv s0)
    (Quantum.StdModel.cmdCharge Quantum.StdModel.callCharge) k)
include hC hpre hσ hpost hn hk

omit [Fintype Val] [DecidableEq Val] in
/-- **The realized game's sponge calls**: the adversary's `n` hash calls. -/
theorem advCalls_cpreT (θ : (s : CSrc ch) → CD ch s) :
    IFreeM.IsChargeBound (realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
      (portCharge fun i ↦ if extCls HashOutput HashDomain (Finset (CSrc ch) × JMem)
        (recSpec (CSrc ch) JMem) i then 0 else 1) n := by
  rw [spongeCharge_eq P]
  exact (chg_realizeT_cpreT 1 0 P we C hC pre adv st0 σ post hpre hσ hpost hn hk θ).mono
    (le_of_eq (by ring))

omit [Fintype Val] [DecidableEq Val] in
/-- **The realized game's reads at step cells**: the reduction's `c₀ + m k + c₁` and the
decision's `lenMax ch`. -/
theorem readCalls_cpreT (θ : (s : CSrc ch) → CD ch s) :
    IFreeM.IsChargeBound (realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
      (portCharge fun i ↦ if readStepQ (ch := ch) P i = true then 1 else 0)
      (c₀ + m * k + c₁ + lenMax ch) := by
  rw [readStepCharge_eq P]
  exact (chg_realizeT_cpreT 0 1 P we C hC pre adv st0 σ post hpre hσ hpost hn hk θ).mono
    (le_of_eq (by ring))

omit [Fintype Val] [DecidableEq Val] in
/-- **The realized game's charged calls**: sponge calls and reads at step cells, `n + v`. -/
theorem chg_cpre_total (θ : (s : CSrc ch) → CD ch s) :
    IFreeM.IsChargeBound (realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
      (portCharge (rCharge (ch := ch) 1 1 P)) (n + (c₀ + m * k + c₁ + lenMax ch)) :=
  (chg_realizeT_cpreT 1 1 P we C hC pre adv st0 σ post hpre hσ hpost hn hk θ).mono
    (le_of_eq (by ring))

variable (hdec : CellDec ch P) {Fb : ℕ}
  (hF : ∀ o, (Finset.univ.filter fun y : HashOutput ↦ ch.step.trunc y = o).card ≤ Fb)
include hdec hF

/-- **The sponge-port masses**: at most `n · κ`, averaged over the hidden values. -/
theorem uavg_spongeMass_le :
    uavg (fun θ : (s : CSrc ch) → CD ch s ↦ (runtimeR (m0C (ch := ch))).totalWeight .instruments
      (spongeMass (hidCells P θ) ∅ ∅) (realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
        initC) ≤ n * kappaC Val Fb := by
  have hc : (fun i ↦ if (extCls HashOutput HashDomain (Finset (CSrc ch) × JMem)
      (recSpec (CSrc ch) JMem) i = false) then 1 else 0) =
      fun i ↦ if extCls HashOutput HashDomain (Finset (CSrc ch) × JMem) (recSpec (CSrc ch) JMem) i
        then 0 else 1 := by
    funext i
    rcases Bool.eq_false_or_eq_true (extCls HashOutput HashDomain (Finset (CSrc ch) × JMem)
      (recSpec (CSrc ch) JMem) i) with h | h <;> simp [h]
  refine uavg_le_of_sum_le' _ _ ((sum_totalWeight_portMass_runtimeR_le_inv .instruments
    (fun i ↦ extCls HashOutput HashDomain (Finset (CSrc ch) × JMem) (recSpec (CSrc ch) JMem) i =
      false) m0C (fun r ↦ r.2.2.1) (fun θ ↦ realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
    (fun _ ↦ initC) (fun _ ↦ initC_posSemidef) (fun j ↦ viewByOn_cpreT C P pre adv st0 σ post m0C
      initC j) (fun θ ↦ SrcInv P θ)
    (fun θ ↦ forallQueries_cpreT (fun _ h ↦ Bool.noConfusion h) m0C C P pre adv st0 σ post θ
      initC (querySupportedOn_initQ m0C rfl _)) (hidCells P) (fun _ ↦ ∅) (fun _ ↦ ∅)
    (kappaC Val Fb) (sourcesC P hdec hF)
    (fun θ ↦ by
      rw [hc]
      exact advCalls_cpreT C P pre adv st0 σ post we hC hpre hσ hpost hn hk θ)).trans ?_)
  exact sum_mul_trace_le _ _ ofReal_trace_initC_le_one n

omit [Fintype Val] [DecidableEq Val] [Inhabited Val] hC hpre hσ hpost hn hk hdec hF in
/-- Only reads at step cells carry hidden mass. -/
theorem readMass_le_readStepQ (θ : (s : CSrc ch) → CD ch s)
    (i : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Port)
    (σ' : Matrix ((recHwSpec HashOutput HashDomain (CSrc ch) JMem).In i ×
      QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)))
      ((recHwSpec HashOutput HashDomain (CSrc ch) JMem).In i ×
      QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem))) ℂ) :
    readMass (hidCells P θ) ∅ ∅ i σ' ≤
      portMass (fun i ↦ readStepQ (ch := ch) P i = true) (hidCells P θ) ∅ ∅ i σ' := by
  rcases i with (((_ | _ | _) | (⟨z, u⟩ | ⟨y, u⟩ | ⟨y, u⟩)) | c) | T
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · by_cases hz : z ∈ stepCells ch P
    · simp only [readMass, portMass, readStepQ, stepRead, hz, decide_true]
      split <;> simp
    · have hz' : z ∉ hidCells P θ := fun ⟨p, hp⟩ ↦ hz (hp ▸ cellOf_mem_stepCells P θ p)
      simp [readMass, portMass, readStepQ, stepRead, hz, Quantum.Xmss.Assembly.extWeight,
        Quantum.Xmss.Assembly.sumWeight, hiddenMass, diagMass, hz']
  · simp [readMass, portMass, readStepQ, stepRead, Quantum.Xmss.Assembly.extWeight,
      Quantum.Xmss.Assembly.sumWeight, hiddenMass, diagMass]
  · simp [readMass, portMass, readStepQ, stepRead, Quantum.Xmss.Assembly.extWeight,
      Quantum.Xmss.Assembly.sumWeight, hiddenMass, diagMass]
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight,
      hiddenMass]
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight]

/-- **The read-port masses**: at most `(c₀ + m k + c₁ + lenMax ch) · κ`, averaged over the hidden
values. -/
theorem uavg_readMass_le :
    uavg (fun θ : (s : CSrc ch) → CD ch s ↦ (runtimeR (m0C (ch := ch))).totalWeight .instruments
      (readMass (hidCells P θ) ∅ ∅) (realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
        initC) ≤ ((c₀ + m * k + c₁ + lenMax ch : ℕ) : ℝ≥0∞) * kappaC Val Fb := by
  refine (uavg_mono fun θ ↦ totalWeight_le_totalWeight (runtimeR (m0C (ch := ch))) .instruments
    (fun i σ' _ ↦ readMass_le_readStepQ P θ i σ') _ initC_posSemidef).trans ?_
  refine uavg_le_of_sum_le' _ _ ((sum_totalWeight_portMass_runtimeR_le_inv .instruments
    (fun i ↦ readStepQ (ch := ch) P i = true) (m0C (ch := ch)) (fun r ↦ r.2.2.1)
    (fun θ ↦ realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
    (fun _ ↦ initC) (fun _ ↦ initC_posSemidef) (fun j ↦ viewByOn_cpreT C P pre adv st0 σ post m0C
      initC j) (fun θ ↦ SrcInv P θ)
    (fun θ ↦ forallQueries_cpreT (fun _ h ↦ Bool.noConfusion h) m0C C P pre adv st0 σ post θ
      initC (querySupportedOn_initQ m0C rfl _)) (hidCells P) (fun _ ↦ ∅) (fun _ ↦ ∅)
    (kappaC Val Fb) (sourcesC P hdec hF)
    (fun θ ↦ readCalls_cpreT C P pre adv st0 σ post we hC hpre hσ hpost hn hk θ)).trans ?_)
  exact sum_mul_trace_le _ _ (ofReal_trace_initC_le_one (ch := ch)) _

end masses

/-! ## The hybrid -/

section hybrid

variable [Fintype J] [DecidableEq J] [Inhabited Val] [DecidableEq Val] {Q St S0 F : Type}
  {R : OracleSpec.{0, 0} Q}

/-- **Runtime 2's win** at the parameter `P` and the hidden values `θ`, from the empty memory. -/
noncomputable def p2C (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) (θ : (s : CSrc ch) → CD ch s) : ℝ≥0∞ :=
  (runtimeR (X := HashOutput) (Z := HashDomain) (m0C (ch := ch))).evalDistMap .instruments
    (realizeT θ (cpreT C P pre adv st0 σ post)) (SubState.basis ()) (fun p ↦ p.2.2) {true}

/-- **The hidden-cell hybrid of the QROM CPRE game of a straight-line reduction**: for an
adversary of `n` hash calls and `k` classical calls, a reduction whose setup, handler and output
read at most `c₀`, `m` and `c₁` step cells (evaluations charged by `we`), and the cell decoding,
`probAvg ≤ (√(E_{P,θ} p2C) + √(4 n · n κ) + √(v κ))²`, `v = c₀ + m k + c₁ + lenMax ch`,
`κ = kappaC Val F`. -/
theorem probAvg_cpre_slRed_le_hybrid [Fintype Par] [SampleableType Par] [Fintype Val]
    [SampleableType Val] (C : TwColl Par Tw Fn Msg Out) (hlen : StepLen ch)
    (hdec : ∀ P, CellDec ch P) {Fb : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y : HashOutput ↦ ch.step.trunc y = o).card ≤ Fb)
    (pre : Unit → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Unit → S0 → St) (σ : Unit → HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : Unit → S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val))
    (we : Par → CpreQuery J Tw Fn Msg → ℕ) {c₀ m k c₁ n : ℕ}
    (hC : ∀ P l t x, Common.QueryCostAtMost (C.eval romWorld l P t x) (stepW (ch := ch) P)
      (we P (.eval l t x)))
    (hpre : ∀ P, Common.QueryCostAtMost (pre ()) (redW (ch := ch) P (we P)) c₀)
    (hσ : ∀ P st q, Common.QueryCostAtMost (σ () st q) (redW (ch := ch) P (we P)) m)
    (hpost : ∀ P s0 f st, Common.QueryCostAtMost (post () s0 f st) (redW (ch := ch) P (we P)) c₁)
    (hn : ∀ s0, IFreeM.IsChargeBound (adv () s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.hashCharge) n)
    (hk : ∀ s0, IFreeM.IsChargeBound (adv () s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.callCharge) k) :
    romWorld.probAvg ((cpre romWorld ch C).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      ((uavg fun P : Par ↦ uavg fun θ : (s : CSrc ch) → CD ch s ↦
          p2C C P (pre ()) (adv ()) (st0 ()) (σ ()) (post ()) θ) ^ (2⁻¹ : ℝ) +
        (4 * (n * (n * kappaC Val Fb))) ^ (2⁻¹ : ℝ) +
        (((c₀ + m * k + c₁ + lenMax ch : ℕ) : ℝ≥0∞) * kappaC Val Fb) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hinj : ∀ P θ, Function.Injective (cellOf (ch := ch) P θ) := fun P ↦ (hdec P).inj
  have h := uavg_win_runtime1R_le_graded_total .instruments
    (fun x : Par × ((s : CSrc ch) → CD ch s) ↦ tableHw x.1 (hinj x.1) x.2)
    (fun x ↦ hidCells x.1 x.2) (fun _ ↦ ∅) (fun _ ↦ ∅)
    (fun x ↦ covers_tableHw x.1 (hinj x.1) x.2) m0C
    (fun x ↦ realizeT x.2 (cpreT (ch := ch) C x.1 (pre ()) (adv ()) (st0 ()) (σ ()) (post ())))
    (fun _ ↦ SubState.basis ()) (fun _ p ↦ p.2.2) (measurableSet_singleton true) n
    (fun x ↦ advCalls_cpreT C x.1 (pre ()) (adv ()) (st0 ()) (σ ()) (post ()) (we x.1) (hC x.1)
      (hpre x.1) (hσ x.1) (hpost x.1) hn hk x.2)
    (n * kappaC Val Fb) (((c₀ + m * k + c₁ + lenMax ch : ℕ) : ℝ≥0∞) * kappaC Val Fb)
    (by
      rw [uavg_prod]
      exact (uavg_mono fun P ↦ uavg_spongeMass_le C P (pre ()) (adv ()) (st0 ()) (σ ())
        (post ()) (we P) (hC P) (hpre P) (hσ P) (hpost P) hn hk (hdec P) hF).trans
          (uavg_const_le _))
    (by
      rw [uavg_prod]
      exact (uavg_mono fun P ↦ uavg_readMass_le C P (pre ()) (adv ()) (st0 ()) (σ ())
        (post ()) (we P) (hC P) (hpre P) (hσ P) (hpost P) hn hk (hdec P) hF).trans
          (uavg_const_le _))
  rw [uavg_prod, uavg_prod] at h
  rw [probAvg_cpre_slRed_eq_runtime1R C hlen hinj m0C pre adv st0 σ post]
  refine le_of_eq_of_le ?_ h
  refine congrArg uavg (funext fun P ↦ ?_)
  rw [uavg_thetaOf]
  refine congrArg uavg (funext fun θ ↦ ?_)
  rw [thetaOf_split]
  rfl

end hybrid

end Quantum.StdModel.Qrom.CpreQ

end
