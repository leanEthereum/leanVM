module

public import Quantum.StdModel.Qrom.EncSaltAmort

@[expose] public section

/-!
# EncTCR$ in the QROM: the bound with the trial reads priced

The graded bound of EncTCR$ (`EncSalt.probAvg_encTcrSalt_le`) leaves the total weight `TW` of the
challenger's trial reads. Each answer costs at most `ansCost` (`totalWeight_answer_le`), linear
in the recorded cells of its tweak's class (`ansCost_le_cntY`), and these costs amortize over the
fresh tweaks (`totalWeight_saltProg_le`):
`TW ≤ λ (n₁ + q + kA nσ + n₂) + c₀ (m₁ + kA mσ + m₂)` with
`λ = limit ((2 + 2/N)/|Salt| + 2F/N)` and `c₀ = limit (2F limit + 2F + 2)/N`.

* `probAvg_encTcrSalt_le_explicit`: EncTCR$ against a straight-line reduction,
  `probAvg ≤ ((q + k₁ + k₂ + 2) √(gradeEta F) + √(λ (n₁ + q + kA nσ + n₂) + c₀ m))²`.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom.EncSalt

open Quantum QuantumRuntime Quantum.Sponge Quantum.Qrom HashSig Props OracleComp OracleSpec Common
open Quantum.Xmss.Hybrid (runtime2)
open Tcr (Mem GSep GCell rl)

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- The slope of an answer's cost in the recorded cells of its class. -/
noncomputable def lamS [Fintype Salt] (F : ℕ) : ℝ :=
  e.limit * ((2 + 2 / (Fintype.card HashOutput : ℝ)) / Fintype.card Salt +
    2 * F / Fintype.card HashOutput)

/-- The constant of an answer's cost. -/
noncomputable def c0S (F : ℕ) : ℝ :=
  e.limit * ((2 * F * e.limit + 2 * F + 2) / Fintype.card HashOutput)

theorem lamS_nonneg [Fintype Salt] (F : ℕ) : 0 ≤ lamS e F := by
  unfold lamS
  positivity

theorem c0S_nonneg (F : ℕ) : 0 ≤ c0S e F := by
  unfold c0S
  positivity

/-- An injection carrying a filter into another bounds its card. -/
theorem card_filter_le_of_inj {α β : Type} [Fintype α] [Fintype β] (p : α → Prop) (r : β → Prop)
    [DecidablePred p] [DecidablePred r] (f : α → β) (hf : Function.Injective f)
    (h : ∀ a, p a → r (f a)) : (Finset.univ.filter p).card ≤ (Finset.univ.filter r).card :=
  Finset.card_le_card_of_injOn f (fun a ha ↦ by
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at ha ⊢
    exact h a ha) fun _ _ _ _ hab ↦ hf hab

/-- The arithmetic of an answer's cost. -/
theorem ansCost_arith {L A a S N F c R : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hA : 0 ≤ A) (ha : a ≤ c) (hR : R ≤ 2 * F * c + 2 * F * L) :
    L * (A * a / S + (R + 2 * F + 2) / N) ≤
      L * (A / S + 2 * F / N) * c + L * ((2 * F * L + 2 * F + 2) / N) := by
  have h1 : A * a / S ≤ A / S * c := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left ha (div_nonneg hA hS)
  have h2 : (R + 2 * F + 2) / N ≤ (2 * F * c + 2 * F * L + 2 * F + 2) / N :=
    div_le_div_of_nonneg_right (by linarith) hN
  calc L * (A * a / S + (R + 2 * F + 2) / N) ≤
        L * (A / S * c + (2 * F * c + 2 * F * L + 2 * F + 2) / N) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hL
    _ = L * (A / S + 2 * F / N) * c + L * ((2 * F * L + 2 * F + 2) / N) := by ring

variable {e}

/-- The trial cells of a message at distinct salts are distinct. -/
theorem cell_injective (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen) (P : Par) (t : Tw) (M : Msg) :
    Function.Injective fun r : Salt ↦ cell e P t (M, r) := fun r r' h ↦ by
  have h' : cell e P t (M, r) = cell e P t (M, r') := h
  have := hinj P t (encodeInput_injective (encodeInput_cell hlen P t (M, r))
    ((encodeInput_cell hlen P t (M, r')).trans (congrArg some h'.symm)))
  exact congrArg Prod.snd this

open scoped Classical in
/-- **The cost of an answer is linear in the recorded cells of its class**: the trial cells of
the salts are distinct cells of the class. -/
theorem ansCost_le_cntY [Fintype Salt] (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen) (F : ℕ) (P : Par) (q : Tw × Msg)
    (s : HwReg HashOutput HashDomain Mem) :
    ansCost e F P q s ≤ lamS e F * cntY (Kset e P q.1) s + c0S e F := by
  have ha : ((Finset.univ.filter fun r : Salt ↦ s.1.1 (cell e P q.1 (q.2, r)) ≠ none).card : ℝ)
      ≤ cntY (Kset e P q.1) s :=
    Nat.cast_le.mpr (card_filter_le_of_inj _ _ (fun r ↦ cell e P q.1 (q.2, r))
      (cell_injective hinj hlen P q.1 q.2) fun r hr ↦ ⟨gCell_cell hlen P q.1 (q.2, r), hr⟩)
  have hg : ((Finset.univ.filter fun y ↦ GCell e.hash G y P q.1 ∧ s.1.1 y ≠ none).card : ℝ)
      ≤ cntY (Kset e P q.1) s :=
    Nat.cast_le.mpr (card_filter_le_of_inj _ _ id Function.injective_id fun _ hy ↦ hy)
  have hR : (if ∀ d, Tcr.Recordless e.hash G s.2.2 (cell e P q.1 d) then
      2 * (F : ℝ) * ((Finset.univ.filter fun y ↦ GCell e.hash G y P q.1 ∧ s.1.1 y ≠ none).card +
        e.limit) else 0) ≤ 2 * F * cntY (Kset e P q.1) s + 2 * F * e.limit := by
    have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
    have hc0 := cntY_nonneg (X := HashOutput) (M := Mem) (Kset e P q.1) s
    split_ifs
    · nlinarith
    · positivity
  exact ansCost_arith (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) ha hR

open scoped Classical in
/-- **Every answer costs at most `ansCost`.** -/
theorem ansBound_ansCost [SampleableType Par] [SampleableType Salt] [Fintype Salt]
    (hs : GSep e.hash G) (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (hbase : ∀ c, Function.Injective fun r0 ↦ e.shift r0 c)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c') :
    AnsBound e (ansCost e F) := fun P q B ρ hρ hW ↦
  totalWeight_answer_le hs hinj hlen hF hbase hdist mem0 P q B ρ hρ hW

variable (e)

open scoped Classical in
/-- **EncTCR$ in the QROM against a straight-line reduction, every cost explicit.** Let the
encoding inputs be cells of at most `maxLen` bytes, determine their parameter and tweak (`hs`),
be injective in the message and salt (`hinj`), the salts of distinct trials of a base be distinct
and each trial's salt determine the base, and let the truncation's fibers have at most `F` values.
Let the adversary make at most `q` calls of the oracle and `kA` calls of the handler. Let the
reduction's setup, handler and output read at most `n₁`, `nσ`, `n₂` encoding cells and ask the
challenger at most `m₁`, `mσ`, `m₂` times, each at a tweak not asked before (`FreshWP`, under an
invariant `J`); on the live runs, let its setup mark at most `k₁` encoding cells, its handler
none it did not mark before, and its output at most `k₂` more (under `Ju`). Then
`probAvg ≤ ((q + k₁ + k₂ + 2) √(gradeEta F) + √(λ (n₁ + q + kA nσ + n₂) + c₀ m))²`, where
`m = m₁ + kA mσ + m₂`, `λ = lamS e F` and `c₀ = c0S e F`. -/
theorem probAvg_encTcrSalt_le_explicit [SampleableType Par] [SampleableType Salt] [Fintype Salt]
    (hs : GSep e.hash G) (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (hbase : ∀ c, Function.Injective fun r0 ↦ e.shift r0 c)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 Fo : Type}
    (pre : Par → OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) S0)
    (adv : Par → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : Par → S0 → St) (σ : Par → HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (post : Par → S0 → Fo → St →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) (Tw × Msg × Salt))
    {q kA : ℕ} (hadv : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge hashCharge) q)
    (hadvC : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge callCharge) kA)
    {n₁ m₁ nσ mσ n₂ m₂ : ℕ}
    (hpreN : ∀ P, QueryCostAtMost (pre P) (costR e) n₁)
    (hpreM : ∀ P, QueryCostAtMost (pre P) (costA Tw Msg Salt Dig) m₁)
    (hσN : ∀ P st qq, QueryCostAtMost (σ P st qq) (costR e) nσ)
    (hσM : ∀ P st qq, QueryCostAtMost (σ P st qq) (costA Tw Msg Salt Dig) mσ)
    (hpostN : ∀ P a f st, QueryCostAtMost (post P a f st) (costR e) n₂)
    (hpostM : ∀ P a f st, QueryCostAtMost (post P a f st) (costA Tw Msg Salt Dig) m₂)
    (J : Par → St → SLog Tw Msg Salt Dig → Prop)
    (hpreF : ∀ P, FreshWP (pre P) [] fun a log ↦ J P (st0 P a) log)
    (hσF : ∀ P st qq log, J P st log → FreshWP (σ P st qq) log fun r log' ↦ J P r.2 log')
    (hpostF : ∀ P a f st log, J P st log → FreshWP (post P a f st) log fun _ _ ↦ True)
    (k₁ k₂ : ℕ) (Ju : Par → S0 → St × SLog Tw Msg Salt Dig → Option Mem → Prop)
    (hpreU : ∀ P a μ', LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (pre P) []
      (some mem0) a μ' → Ju P a.1 (st0 P a.1, a.2) μ' ∧ ∀ m', μ' = some m' → βS e m' ≤ k₁)
    (hσU : ∀ P a st log μ qq, LiveInv e P log μ → Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (σ P st qq) log μ r μ' →
        Ju P a (r.1.2, r.2) μ' ∧ ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m)
    (hpostU : ∀ P a f st log μ, LiveInv e P log μ → Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (post P a f st) log μ r μ' →
        ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m + k₂) :
    romWorld.probAvg ((encTcrSalt romWorld e).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (((q : ℝ≥0∞) + (k₁ + k₂ + 2 : ℕ)) * ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (lamS e F) * (n₁ + q + kA * nσ + n₂ : ℕ) +
          ENNReal.ofReal (c0S e F) * (m₁ + kA * mσ + m₂ : ℕ)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hTW := totalWeight_saltProg_le e hs (ansCost e F)
    (ansBound_ansCost hs hinj hlen hF hbase hdist) (lamS e F) (c0S e F) (lamS_nonneg e F)
    (c0S_nonneg e F) (fun P qq s ↦ ansCost_le_cntY hinj hlen F P qq s) pre adv st0 σ post hadv
    hadvC hpreN hpreM hσN hσM hpostN hpostM J hpreF hσF hpostF
  refine (probAvg_encTcrSalt_le e hs hinj hlen hF pre adv st0 σ post hadv k₁ k₂ Ju hpreU hσU
    hpostU).trans ?_
  gcongr

open scoped Classical in
/-- **EncTCR$ with B2's live budgets** (a setup marking no encoding cell, an output marking at
most two): `probAvg ≤ ((q + 4) √(gradeEta F) + √(λ (n₁ + q + kA nσ + n₂) + c₀ m))²`. -/
theorem probAvg_encTcrSalt_le_explicit_four [SampleableType Par] [SampleableType Salt]
    [Fintype Salt] (hs : GSep e.hash G) (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (hbase : ∀ c, Function.Injective fun r0 ↦ e.shift r0 c)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 Fo : Type}
    (pre : Par → OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) S0)
    (adv : Par → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : Par → S0 → St) (σ : Par → HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (post : Par → S0 → Fo → St →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) (Tw × Msg × Salt))
    {q kA : ℕ} (hadv : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge hashCharge) q)
    (hadvC : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge callCharge) kA)
    {n₁ m₁ nσ mσ n₂ m₂ : ℕ}
    (hpreN : ∀ P, QueryCostAtMost (pre P) (costR e) n₁)
    (hpreM : ∀ P, QueryCostAtMost (pre P) (costA Tw Msg Salt Dig) m₁)
    (hσN : ∀ P st qq, QueryCostAtMost (σ P st qq) (costR e) nσ)
    (hσM : ∀ P st qq, QueryCostAtMost (σ P st qq) (costA Tw Msg Salt Dig) mσ)
    (hpostN : ∀ P a f st, QueryCostAtMost (post P a f st) (costR e) n₂)
    (hpostM : ∀ P a f st, QueryCostAtMost (post P a f st) (costA Tw Msg Salt Dig) m₂)
    (J : Par → St → SLog Tw Msg Salt Dig → Prop)
    (hpreF : ∀ P, FreshWP (pre P) [] fun a log ↦ J P (st0 P a) log)
    (hσF : ∀ P st qq log, J P st log → FreshWP (σ P st qq) log fun r log' ↦ J P r.2 log')
    (hpostF : ∀ P a f st log, J P st log → FreshWP (post P a f st) log fun _ _ ↦ True)
    (Ju : Par → S0 → St × SLog Tw Msg Salt Dig → Option Mem → Prop)
    (hpreU : ∀ P a μ', LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (pre P) []
      (some mem0) a μ' → Ju P a.1 (st0 P a.1, a.2) μ' ∧ ∀ m', μ' = some m' → βS e m' = 0)
    (hσU : ∀ P a st log μ qq, LiveInv e P log μ → Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (σ P st qq) log μ r μ' →
        Ju P a (r.1.2, r.2) μ' ∧ ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m)
    (hpostU : ∀ P a f st log μ, LiveInv e P log μ → Ju P a (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (post P a f st) log μ r μ' →
        ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m + 2) :
    romWorld.probAvg ((encTcrSalt romWorld e).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (((q : ℝ≥0∞) + 4) * ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (lamS e F) * (n₁ + q + kA * nσ + n₂ : ℕ) +
          ENNReal.ofReal (c0S e F) * (m₁ + kA * mσ + m₂ : ℕ)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := probAvg_encTcrSalt_le_explicit e hs hinj hlen hF hbase hdist pre adv st0 σ post hadv
    hadvC hpreN hpreM hσN hσM hpostN hpostM J hpreF hσF hpostF 0 2 Ju
    (fun P a μ' hr ↦ ⟨(hpreU P a μ' hr).1, fun m' hm' ↦ ((hpreU P a μ' hr).2 m' hm').le⟩)
    hσU hpostU
  have h4 : ((0 + 2 + 2 : ℕ) : ℝ≥0∞) = 4 := by norm_num
  rw [h4] at h
  exact h

end Quantum.StdModel.Qrom.EncSalt

end
