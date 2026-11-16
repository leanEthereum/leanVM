module

public import Quantum.Xmss.Assembly.CwRec
public import Quantum.Xmss.Assembly.EncPorts
public import Quantum.Xmss.Assembly.HTrial

@[expose] public section

/-!
# The reveal charges of the randomizer searches

CwRec reduces the codeword-recorded mass to `CwRevView A R`: at each reveal of a label's
randomizer base, four times each trial whose block is recorded or hardwired while the key is
unselected (`cwTD`). Here that charge is split by the state's label at the reveal (`cwRevW_le`).

* **Support invariants of moded programs** (`forallQueries_of_modedP`).
* **The view lemma with a weight per state** (`sum_queryWeight_view_le_wt`, from Disclose's
  counting `sum_agree_and_le`): the bound `κ` of the sources may depend on the input state.
* **Trial blocks name their label** (`messageFields_inj`, `cwBlk_lab_inj`, `IsBlk`): a block is
  a trial block of at most one label, injectively in the base for a fixed trial.
* **The potential `Ψ`** (`revPot`): the recorded `k`-cells that are trial blocks of unrevealed
  labels. It is one-cell Lipschitz, the searches' reads (whose label is revealed, `labInv`),
  programs and records do not raise it, and a first reveal of `lab` lowers it by `lab`'s recorded
  trial blocks (`revDropO_add_le`, `revPot_step`). Along the prefix the drops add up to at most
  `6q` (`totalWeight_revDropW_le`).
* **First reveals, recorded blocks** (`firstW`, `sum_totalWeight_firstW_le`): the base is the
  undisclosed source, the bases whose trial-`j` block is recorded inject into the drop of `Ψ`:
  `4 · 2^32 · 6q / 2^128 = 24q · 2^-96` per hidden value (`revFirstC_eq`).
* **First reveals, hardwired blocks** (`hwRevW`, `totalWeight_hwRevW_eq_zero`): the hardwired
  `k`-cells are cells the signatures program (`ProgsK`, `progsK_prefixT`, `hwKIn_step`), cells
  of the in-table slots; off trial blocks (`HwTrialOff`, from `TrialHidGood` and `SrcGood`,
  `hwTrialOff_of_trialHidGood`) the charge vanishes.
* **Repeated reveals** (`reRevW`, `CwReView`): a reveal of an already revealed label with its key
  unselected (the earlier search failed), charged `4 · 2^32` times its mass, the hypothesis
  discharged by CwReFail.
* **Assembly** (`sum_cwRecT_good_le`, `uavg_cwRecPre_all_le_rev`): RestMass's average with the
  good set `r0G ∧ TrialHidGood`, at most `cwRevTau q ε + cwJunk + clsCap · 2^-400`.
-/

universe u v w w₁ u₁ v₁

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Support invariants of moded programs -/

section modedSupp

variable {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  {Mode : Type} {ok : Mode → spec.Port → Prop} {nx : Mode → (i : spec.Port) → spec.Result i → Mode}
  (R : QuantumRuntime spec) (I : L.Interp)

/-- **A support invariant per mode**: if every allowed call keeps the support in the invariant of
its mode, a moded program run from an operator supported on the invariant of its first mode
presents every call an operator supported on the invariant of a mode allowing it. -/
theorem forallQueries_of_modedP (Inv : Mode → Set R.D)
    (hstep : ∀ μ i r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ), ok μ i →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) (Inv μ) σ →
      QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) (Inv (nx μ i r)) ((R.step i).branch r σ))
    {fin : (Σ u, Ω u) → Mode → Prop} {A : QReg} (x : QuantumComp L spec Ω A) :
    ∀ μ, ModedP ok nx fin μ x → ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ},
      QuerySupportedOn (fun m : A × R.D ↦ m.2) (Inv μ) ρ →
      R.ForallQueries I (fun i E σ ↦ ∃ μ, ok μ i ∧
        QuerySupportedOn (fun m : (spec.In i × R.D) × E ↦ m.1.2) (Inv μ) σ) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _; trivial
  | primBind _ o k ih =>
    intro μ hx ρ hρ
    rw [QuantumRuntime.forallQueries_primBind_iff]
    exact fun b ↦ ih b μ (hx.2 (ULift.up b)) (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro μ hx ρ hρ
    rw [QuantumRuntime.forallQueries_queryBind_iff]
    refine ⟨⟨μ, hx.1, ?_⟩, fun r ↦ ih r _ (hx.2 (ULift.up r))
      (Hybrid.querySupportedOn_queryStep R (fun s ↦ s) i r (fun σ h ↦ hstep μ i r σ hx.1 h) E ℓ hρ)⟩
    exact (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
      (q' := fun m : (spec.In i × R.D) × E ↦ m.1.2) (S' := Inv μ) fun m hm ↦ by
        obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
        rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

end modedSupp

/-! ## Disclose's view lemma with a weight per state -/

section viewW

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)]

/-- The `κ`-weighted diagonal of an operator. -/
noncomputable def kWt {α : Type} [Fintype α] (κ : α → ℝ≥0∞) (σ : Matrix α α ℂ) : ℝ≥0∞ :=
  ∑ a, κ a * ENNReal.ofReal (σ a a).re

/-- **The pointwise count with a weight per state** (`sum_agree_diagMass_le` with `κ` depending on
the state). -/
theorem sum_agree_diagMass_le_wt [∀ s, Nonempty (D s)] {α : Type} [Fintype α]
    (lab : α → Finset S) (T : Finset S) (v : (s : S) → D s) (C : ((s : S) → D s) → Set α)
    (srcs : α → Finset S) (F : α → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ a s u d, F a s (Function.update u s d) = F a s u)
    (hsrc : ∀ u a, a ∈ C u → ∃ s ∈ srcs a, s ∉ lab a ∧ u s ∈ F a s u) (κ : α → ℝ≥0∞)
    (hκ : ∀ a u, ∑ s ∈ srcs a,
      ((F a s u).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ a) (σ : Matrix α α ℂ) :
    ∑ u, (if Agree T v u then diagMass (C u ∩ {a | lab a = T}) σ else 0) ≤
      (∑ u, if Agree T v u then (1 : ℝ≥0∞) else 0) *
        kWt (fun a ↦ if lab a = T then κ a else 0) σ := by
  classical
  simp only [diagMass, kWt]
  rw [Finset.mul_sum]
  calc ∑ u, (if Agree T v u then
          ∑ a, (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0)
      = ∑ a, ∑ u, (if Agree T v u then
          (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp
    _ ≤ _ := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        by_cases ha : lab a = T
        · calc ∑ u, (if Agree T v u then
                  (C u ∩ {a | lab a = T}).indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a else 0)
              = ENNReal.ofReal (σ a a).re *
                  ∑ u, (if Agree T v u ∧ a ∈ C u then (1 : ℝ≥0∞) else 0) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun u _ ↦ ?_
                by_cases h1 : Agree T v u <;> by_cases h2 : a ∈ C u <;>
                  simp [h1, h2, ha]
            _ ≤ ENNReal.ofReal (σ a a).re *
                  (κ a * ∑ u, if Agree T v u then (1 : ℝ≥0∞) else 0) := by
                gcongr
                exact sum_agree_and_le T v (fun u ↦ a ∈ C u) (srcs a) (F a) (hF a)
                  (fun u hu ↦ by
                    obtain ⟨s, hs, hsl, hsF⟩ := hsrc u a hu
                    exact ⟨s, hs, ha ▸ hsl, hsF⟩) (κ a) (hκ a)
            _ = _ := by rw [ite_eq_left ha]; ring
        · rw [ite_eq_right ha, zero_mul, mul_zero]
          refine le_of_eq (Finset.sum_eq_zero fun u _ ↦ ?_)
          split_ifs
          · exact Set.indicator_of_notMem (fun h ↦ ha h.2) _
          · rfl

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **The view lemma at one label with a weight per state.** -/
theorem sum_queryWeight_cut_le_wt [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (hCP : ∀ v i, ¬ P i → C v i = ∅)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ∀ i, spec.In i × R.D → ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ i p) (T : Finset S) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j ≤
      ∑ v, R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0))
        (x v) (ρ v) j := by
  classical
  obtain ⟨v₀⟩ : Nonempty ((s : S) → D s) := inferInstance
  set N : ℝ≥0∞ := ∑ u, if Agree T v₀ u then 1 else 0 with hN
  have hNv : ∀ v, ∑ u, (if Agree T v u then (1 : ℝ≥0∞) else 0) = N :=
    fun v ↦ sum_agree_eq T v v₀
  have hN1 : 1 ≤ N := by
    have h := Finset.single_le_sum (f := fun u ↦ if Agree T v₀ u then (1 : ℝ≥0∞) else 0)
      (fun _ _ ↦ by simp) (Finset.mem_univ v₀)
    simp only [show Agree T v₀ v₀ from fun _ _ ↦ rfl, ↓reduceIte] at h
    exact h
  have hN0 : N ≠ 0 := (zero_lt_one.trans_le hN1).ne'
  have hNtop : N ≠ ⊤ := by
    rw [hN]
    exact ENNReal.sum_ne_top.mpr fun u _ ↦ by split_ifs <;> simp
  have hv : ∀ v, ∑ u, (if Agree T v u then
      R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) ≤
        N * R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0))
          (x v) (ρ v) j := by
    intro v
    have hstep : ∀ u, (if Agree T v u then
        R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) =
          R.queryWeight I (fun i σ ↦ if Agree T v u then
            diagMass (C u i ∩ {p | lab p.2 = T}) σ else 0) (x v) (ρ v) j := by
      intro u
      by_cases h : Agree T v u
      · simp only [h, ↓reduceIte]
        exact (hview T v u h (fun i ↦ C u i ∩ {p | lab p.2 = T}) (fun i p hp ↦ hp.2)
          fun i hi ↦ by rw [hCP u i hi, Set.empty_inter]).symm
      · simp only [h, ↓reduceIte]
        exact (queryWeight_zero_weight R I (x v) (ρ v) j).symm
    simp only [hstep]
    rw [← queryWeight_fintype_sum, ← R.queryWeight_const_mul]
    refine R.queryWeight_mono I (fun i σ _ ↦ ?_) (x v) (hρ v) j
    have h := sum_agree_diagMass_le_wt (fun p : spec.In i × R.D ↦ lab p.2) T v (fun u ↦ C u i)
      (srcs i) (F i) (hF i) (fun u p hp ↦ hsrc u i p hp) (κ i) (fun p u ↦ hκ i p u) σ
    rwa [hNv v] at h
  have h1 : N * ∑ u, R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u)
      (ρ u) j = ∑ v, ∑ u, (if Agree T v u then
        R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j
          else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [← hNv u, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have hs : Agree T u v ↔ Agree T v u := ⟨Agree.symm, Agree.symm⟩
    by_cases h : Agree T v u <;> simp [h, hs]
  have h2 : N * ∑ u, R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u)
      (ρ u) j ≤ N * ∑ v, R.queryWeight I
        (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0)) (x v) (ρ v) j := by
    rw [h1, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ ↦ hv v
  exact (ENNReal.mul_le_mul_iff_right hN0 hNtop).mp h2

/-- **The adaptive view lemma with a weight per state**: under the lazy-sampling property, if every
input state `p ∈ C v i` names an undisclosed source with its value in `F`, the masses of `C v`
add up over the hidden values to at most the `κ`-weighted diagonals, where `κ i p` bounds
`∑ₛ |F i p s v| / |D s|` at the state `p`. -/
theorem sum_queryWeight_view_le_wt [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j)
    (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D)) (hCP : ∀ v i, ¬ P i → C v i = ∅)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ∀ i, spec.In i × R.D → ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ i p) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j ≤
      ∑ v, R.queryWeight I (fun i ↦ kWt (κ i)) (x v) (ρ v) j := by
  classical
  have hpart : ∀ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j =
      ∑ T, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j :=
    fun v ↦ by
      rw [← queryWeight_fintype_sum]
      refine congrArg (fun w ↦ R.queryWeight I w (x v) (ρ v) j) (funext fun i ↦ funext fun σ ↦ ?_)
      exact diagMass_eq_sum_label (fun p ↦ lab p.2) (C v i) σ
  have hκpart : ∀ v, R.queryWeight I (fun i ↦ kWt (κ i)) (x v) (ρ v) j =
      ∑ T, R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0))
        (x v) (ρ v) j :=
    fun v ↦ by
      rw [← queryWeight_fintype_sum]
      refine congrArg (fun w ↦ R.queryWeight I w (x v) (ρ v) j) (funext fun i ↦ funext fun σ ↦ ?_)
      simp only [kWt]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  calc ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j
      = ∑ T, ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v)
          (ρ v) j := by
        simp only [hpart]
        exact Finset.sum_comm
    _ ≤ ∑ T, ∑ v, R.queryWeight I (fun i ↦ kWt (fun p ↦ if lab p.2 = T then κ i p else 0))
          (x v) (ρ v) j :=
        Finset.sum_le_sum fun T _ ↦ sum_queryWeight_cut_le_wt R I lab x ρ hρ j P hview C hCP srcs
          F hF hsrc κ hκ T
    _ = _ := by
        rw [Finset.sum_comm]
        simp only [hκpart]

end viewW

/-! ## The trial blocks of a label -/

section blk

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- The message hash's address determines its layer and key. -/
theorem messageFields_inj {l l' : Layer} {e e' : KeyIndex}
    (h : hashDomainFields (.message l e) = hashDomainFields (.message l' e')) :
    l = l' ∧ e = e' := by
  have hhi := congrArg (fun f : TweakFields ↦ f.hi.toNat) h
  have hlo := congrArg (fun f : TweakFields ↦ f.lo.toNat) h
  simp only [hashDomainFields, tweakFields, layerHi, BitVec.toNat_ofNat] at hhi hlo
  have hl := l.isLt
  have hl' := l'.isLt
  have he := e.isLt
  have he' := e'.isLt
  simp only [layerCount, lifetime, layerHeight] at hl hl' he he'
  norm_num at hhi hlo he he'
  refine ⟨Fin.ext (by omega), Fin.ext ?_⟩
  rwa [Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt he'] at hlo

/-- **A trial block names its label and its trial value.** -/
theorem cwBlk_lab_inj (P : PublicParameter) {lab lab' : RLabel} {b b' : Randomizer} {j j' : ℕ}
    (h : cwBlk P lab b j = cwBlk P lab' b' j') :
    lab = lab' ∧ b + BitVec.ofNat digestBits j = b' + BitVec.ofNat digestBits j' := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (length_blocks_trial P
    (hashDomainFields (.message lab.layer lab.key)) (RLabel.length_msg_le lab) b j)
  obtain ⟨c', hc'⟩ := List.length_eq_one_iff.mp (length_blocks_trial P
    (hashDomainFields (.message lab'.layer lab'.key)) (RLabel.length_msg_le lab') b' j')
  have e1 : cwBlk P lab b j = c := by simp [cwBlk, hc]
  have e2 : cwBlk P lab' b' j' = c' := by simp [cwBlk, hc']
  have hcc : c = c' := e1.symm.trans (h.trans e2)
  obtain ⟨hf, hp⟩ := thInput_injective P (blocks_injective (hc.trans (hcc ▸ hc'.symm)))
  obtain ⟨hl, hk⟩ := messageFields_inj hf
  have hbt : bottomLayer ≠ topLayer := by decide
  rcases lab with ⟨e, m⟩ | ⟨e, d⟩ <;> rcases lab' with ⟨e', m'⟩ | ⟨e', d'⟩
  · obtain ⟨h1, h2⟩ := List.append_inj hp (by simp only [RLabel.msg, littleEndianBytes,
      List.length_ofFn])
    have hm : m = m' := littleEndianBytes_injective 32 h1
    have he : e = e' := hk
    subst hm he
    exact ⟨rfl, littleEndianBytes_injective 16 h2⟩
  · exact absurd hl hbt
  · exact absurd hl.symm hbt
  · obtain ⟨h1, h2⟩ := List.append_inj hp (by simp only [RLabel.msg, littleEndianBytes,
      List.length_ofFn])
    have hm : d = d' := littleEndianBytes_injective 16 h1
    have he : e = e' := hk
    subst hm he
    exact ⟨rfl, littleEndianBytes_injective 16 h2⟩

/-- For a fixed trial, the blocks of a label are injective in the base. -/
theorem cwBlk_base_inj (P : PublicParameter) (lab : RLabel) (j : ℕ) :
    Function.Injective fun b : Randomizer ↦ cwBlk P lab b j :=
  fun _ _ h ↦ add_right_cancel (cwBlk_lab_inj P h).2

/-- `y` is the block of a trial of the search of label `lab`. -/
def IsBlk (P : PublicParameter) (lab : RLabel) (y : X) : Prop :=
  ∃ b : Randomizer, ∃ j < randomizerAttemptLimit, y = cwBlk P lab b j

/-- `IsBlk`, decided classically. -/
noncomputable instance instDecidableIsBlk (P : PublicParameter) (lab : RLabel) (y : X) :
    Decidable (IsBlk P lab y) :=
  Classical.propDecidable _

theorem isBlk_unique {P : PublicParameter} {lab lab' : RLabel} {y : X} (h : IsBlk P lab y)
    (h' : IsBlk P lab' y) : lab = lab' := by
  obtain ⟨b, j, -, rfl⟩ := h
  obtain ⟨b', j', -, he⟩ := h'
  exact (cwBlk_lab_inj P he).1

end blk

/-! ## The potential: recorded trial blocks of unrevealed labels -/

section pot

variable {X₁ Z₁ M₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype M₁] [DecidableEq M₁] (B : RLabel → X₁ → Prop) [∀ l y, Decidable (B l y)]

/-- The unrevealed labels (under the memory label `T`) of which `y` is a trial block (`B`). -/
noncomputable def blkCnt (T : Finset HPos) (y : X₁) : ℝ :=
  ∑ l : RLabel, if Sum.inr l ∉ T ∧ B l y then 1 else 0

/-- **The potential `Ψ`**: the recorded `k`-cells that are trial blocks of unrevealed labels. -/
noncomputable def revPot (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : ℝ :=
  ∑ y : X₁, if s.1.2.1 y ≠ none then blkCnt B s.2.2.1 y else 0

/-- `Ψ` with the cell `x` counted as recorded: it does not see the cell `x`. -/
noncomputable def revPotAt (x : X₁) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : ℝ :=
  ∑ y : X₁, if y = x then blkCnt B s.2.2.1 x else
    if s.1.2.1 y ≠ none then blkCnt B s.2.2.1 y else 0

/-- **The drop of `Ψ` at a first reveal of `lab`**: its recorded trial blocks. -/
noncomputable def revDrop (lab : RLabel) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : ℝ :=
  if Sum.inr lab ∈ s.2.2.1 then 0 else
    ((Finset.univ.filter fun y : X₁ ↦ s.1.2.1 y ≠ none ∧ B lab y).card : ℝ)

/-- The drop at a reveal labelled `o`. -/
noncomputable def revDropO (o : Option RLabel) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : ℝ :=
  match o with
  | some lab => revDrop B lab s
  | none => 0

omit [Fintype X₁] [DecidableEq X₁] in
theorem blkCnt_nonneg (T : Finset HPos) (y : X₁) : 0 ≤ blkCnt B T y :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

omit [Fintype X₁] [DecidableEq X₁] in
theorem blkCnt_le_one (hB : ∀ {l l' y}, B l y → B l' y → l = l') (T : Finset HPos) (y : X₁) :
    blkCnt B T y ≤ 1 := by
  unfold blkCnt
  by_cases h : ∃ l, B l y
  · obtain ⟨l₀, hl₀⟩ := h
    rw [Finset.sum_eq_single l₀ (fun l _ hl ↦ ite_eq_right fun hc ↦
      hl (hB hc.2 hl₀)) (fun h ↦ absurd (Finset.mem_univ _) h)]
    split_ifs <;> norm_num
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun l _ ↦ ite_eq_right fun hc ↦ h ⟨l, hc.2⟩)
      zero_le_one

omit [Fintype X₁] [DecidableEq X₁] in
theorem blkCnt_eq_zero (hB : ∀ {l l' y}, B l y → B l' y → l = l') {T : Finset HPos}
    {lab : RLabel} {y : X₁} (hy : B lab y) (hT : Sum.inr lab ∈ T) : blkCnt B T y = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ ite_eq_right fun hc ↦ hc.1 (hB hy hc.2 ▸ hT)

omit [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPot_nonneg (s : HwReg X₁ Z₁ (Finset HPos × M₁)) : 0 ≤ revPot B s :=
  Finset.sum_nonneg fun y _ ↦ by
    split_ifs
    · exact blkCnt_nonneg B _ y
    · exact le_rfl

omit [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPot_congr {s s' : HwReg X₁ Z₁ (Finset HPos × M₁)} (hk : s'.1.2.1 = s.1.2.1)
    (hl : s'.2.2.1 = s.2.2.1) : revPot B s' = revPot B s := by
  unfold revPot
  rw [hk, hl]

omit [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPot_le_revPotAt (x : X₁) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) :
    revPot B s ≤ revPotAt B x s :=
  Finset.sum_le_sum fun y _ ↦ by
    by_cases hy : y = x
    · subst hy
      rw [ite_eq_left rfl]
      split_ifs
      · exact le_rfl
      · exact blkCnt_nonneg B _ y
    · rw [ite_eq_right hy]

omit [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPotAt_eq (hB : ∀ {l l' y}, B l y → B l' y → l = l') {x : X₁} {lab : RLabel}
    (hx : B lab x) {s : HwReg X₁ Z₁ (Finset HPos × M₁)} (hs : Sum.inr lab ∈ s.2.2.1) :
    revPotAt B x s = revPot B s :=
  Finset.sum_congr rfl fun y _ ↦ by
    by_cases hy : y = x
    · subst hy
      rw [ite_eq_left rfl, blkCnt_eq_zero B hB hx hs]
      split_ifs <;> rfl
    · rw [ite_eq_right hy]

omit [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem revPotAt_congr (x : X₁) {s s' : HwReg X₁ Z₁ (Finset HPos × M₁)}
    (hk : ∀ y, y ≠ x → s'.1.2.1 y = s.1.2.1 y) (hl : s'.2.2.1 = s.2.2.1) :
    revPotAt B x s' = revPotAt B x s :=
  Finset.sum_congr rfl fun y _ ↦ by
    rw [hl]
    by_cases hy : y = x
    · rw [ite_eq_left hy, ite_eq_left hy]
    · rw [ite_eq_right hy, ite_eq_right hy, hk y hy]

omit [Fintype Z₁] [Fintype M₁] [DecidableEq M₁] in
/-- **`Ψ` is one-cell Lipschitz** when a `k`-cell is a trial block of at most one label. -/
theorem oneCellLipschitz_revPot (hB : ∀ {l l' y}, B l y → B l' y → l = l') :
    OneCellLipschitz (revPot (Z₁ := Z₁) (M₁ := M₁) B) where
  h _ _ _ _ := le_of_eq_of_le (revPot_congr B rfl rfl) (le_add_of_nonneg_right zero_le_one)
  k' _ _ _ _ := le_of_eq_of_le (revPot_congr B rfl rfl) (le_add_of_nonneg_right zero_le_one)
  k D b x v := by
    set f : X₁ → ℝ := fun y ↦ if D.2.1 y ≠ none then blkCnt B b.2.1 y else 0
    set f' : X₁ → ℝ := fun y ↦
      if Function.update D.2.1 x v y ≠ none then blkCnt B b.2.1 y else 0
    have hd : ∑ y, (f' y - f y) = f' x - f x :=
      Finset.sum_eq_single x (fun y _ hy ↦ by simp [f, f', Function.update_of_ne hy])
        (fun h ↦ absurd (Finset.mem_univ x) h)
    have hf' : f' x ≤ 1 := by
      simp only [f']
      split_ifs
      · exact blkCnt_le_one B hB _ x
      · exact zero_le_one
    have hf : 0 ≤ f x := by
      simp only [f]
      split_ifs
      · exact blkCnt_nonneg B _ x
      · exact le_rfl
    show ∑ y, f' y ≤ ∑ y, f y + 1
    rw [Finset.sum_sub_distrib] at hd
    linarith

omit [Fintype Z₁] [Fintype M₁] [DecidableEq M₁] in
/-- **A program does not raise `Ψ`**: it discards its cell from the databases. -/
theorem revPot_progMap_le (c : HwProg X₁ Z₁) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) :
    revPot B (progMap c s) ≤ revPot B s := by
  obtain ⟨⟨dh, dk, dk'⟩, ⟨w1, w2, w3⟩, m⟩ := s
  rcases c with ⟨z, w⟩ | ⟨x, w⟩ | ⟨x, w⟩
  · exact le_of_eq (revPot_congr B rfl rfl)
  · refine Finset.sum_le_sum fun y _ ↦ ?_
    show (if Function.update dk x none y ≠ none then blkCnt B m.1 y else 0) ≤
      if dk y ≠ none then blkCnt B m.1 y else 0
    by_cases hy : y = x
    · subst hy
      rw [Function.update_self, ite_eq_right (fun h ↦ h rfl)]
      split_ifs
      · exact blkCnt_nonneg B _ y
      · exact le_rfl
    · rw [Function.update_of_ne hy]
  · exact le_of_eq (revPot_congr B rfl rfl)

/-- The register after a record of `T`. -/
def recMapR (T : Finset HPos) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) :
    HwReg X₁ Z₁ (Finset HPos × M₁) :=
  (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2))

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
theorem blkCnt_union_le (T T' : Finset HPos) (y : X₁) : blkCnt B (T ∪ T') y ≤ blkCnt B T y :=
  Finset.sum_le_sum fun l _ ↦ by
    by_cases h : Sum.inr l ∉ T ∪ T' ∧ B l y
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl ↦ h.1 (Finset.mem_union_left _ hl), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
/-- At one cell: the first-reveal drop of `lab` and the count after recording `{lab}`. -/
theorem ind_add_blkCnt_le {T : Finset HPos} {lab : RLabel} (hlab : Sum.inr lab ∉ T) (y : X₁) :
    (if B lab y then (1 : ℝ) else 0) + blkCnt B (T ∪ {Sum.inr lab}) y ≤ blkCnt B T y := by
  unfold blkCnt
  have h1 : (if B lab y then (1 : ℝ) else 0) =
      ∑ l : RLabel, if l = lab then (if Sum.inr l ∉ T ∧ B l y then 1 else 0) else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ lab, ite_eq_left (Finset.mem_univ _)]
    by_cases hb : B lab y
    · rw [ite_eq_left hb, ite_eq_left ⟨hlab, hb⟩]
    · rw [ite_eq_right hb, ite_eq_right fun h ↦ hb h.2]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ ↦ ?_
  by_cases hl : l = lab
  · subst hl
    have h0 : ¬(Sum.inr l ∉ T ∪ {Sum.inr l} ∧ B l y) :=
      fun h ↦ h.1 (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    rw [ite_eq_left rfl, ite_eq_right h0, add_zero]
  · rw [ite_eq_right hl, zero_add]
    by_cases h : Sum.inr l ∉ T ∪ {Sum.inr lab} ∧ B l y
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl' ↦ h.1 (Finset.mem_union_left _ hl'), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

omit [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M₁] [DecidableEq M₁] in
/-- **A record drops `Ψ` by at least the first-reveal drop.** -/
theorem revDropO_add_le (T : Finset HPos) (s : HwReg X₁ Z₁ (Finset HPos × M₁)) :
    revDropO B (cwRevLab T) s + revPot B (recMapR T s) ≤ revPot B s := by
  obtain ⟨⟨dh, dk, dk'⟩, W, ⟨L, m⟩⟩ := s
  have hle : revPot B (recMapR T ((dh, dk, dk'), W, (L, m))) ≤
      revPot B ((dh, dk, dk'), W, (L, m)) :=
    Finset.sum_le_sum fun y _ ↦ by
      show (if dk y ≠ none then blkCnt B (L ∪ T) y else 0) ≤
        if dk y ≠ none then blkCnt B L y else 0
      split_ifs
      · exact blkCnt_union_le B L T y
      · exact le_rfl
  cases ho : cwRevLab T with
  | none =>
    show 0 + _ ≤ _
    rw [zero_add]
    exact hle
  | some lab =>
    show revDrop B lab ((dh, dk, dk'), W, (L, m)) + _ ≤ _
    unfold revDrop
    split_ifs with hlab
    · rw [zero_add]
      exact hle
    · have hT : T = {Sum.inr lab} := cwRevLab_spec ho
      subst hT
      show ((Finset.univ.filter fun y : X₁ ↦ dk y ≠ none ∧ B lab y).card : ℝ) +
        ∑ y : X₁, (if dk y ≠ none then blkCnt B (L ∪ {Sum.inr lab}) y else 0) ≤
          ∑ y : X₁, if dk y ≠ none then blkCnt B L y else 0
      rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ ↦ ?_
      by_cases hD : dk y ≠ none
      · rw [ite_eq_left hD, ite_eq_left hD]
        have h := ind_add_blkCnt_le B hlab y
        by_cases hb : B lab y
        · rw [ite_eq_left hb] at h
          rw [ite_eq_left ⟨hD, hb⟩, Nat.cast_one]
          exact h
        · rw [ite_eq_right hb] at h
          rw [ite_eq_right fun h' ↦ hb h'.2, Nat.cast_zero]
          exact h
      · rw [ite_eq_right hD, ite_eq_right hD, ite_eq_right fun h ↦ hD h.1, Nat.cast_zero,
          zero_add]

end pot

/-! ## Diagonal potentials along the ports -/

section steps

variable {X₁ Z₁ M₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype M₁] [DecidableEq M₁]

/-- **A diagonal potential along a complete Kraus family** whose nonzero entries keep a weight
`φ' ≥ φ`, equal to `φ` on the support: the potential does not rise. -/
theorem tsum_potential_le_of_keep {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (K : ι → Matrix (Unit × β) (Unit × β) ℂ) (hsum : ∑ r, (K r)ᴴ * K r = 1)
    {φ φ' : β → ℝ} (hφ0 : ∀ s, 0 ≤ φ s) (hle : ∀ s, φ s ≤ φ' s)
    (hkeep : ∀ r a a', K r a' a ≠ 0 → φ' a'.2 = φ' a.2)
    {σ : Matrix (Unit × β) (Unit × β) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → φ q.2 = φ' q.2) :
    ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (K r) σ) ≤
      potential (diagPot fun s ↦ √(φ s)) σ := by
  have hd : ∀ r q, 0 ≤ ((MatrixMap.conj (K r) σ) q q).re := fun r q ↦
    (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  rw [tsum_fintype]
  simp only [potential_diagPot_sqrt hφ0]
  rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 q.2) (hd r q)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∑ r, ∑ q, φ q.2 * ((MatrixMap.conj (K r) σ) q q).re
      ≤ ∑ r, dW (fun q : Unit × β ↦ φ' q.2) (MatrixMap.conj (K r) σ) :=
        Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun q _ ↦
          mul_le_mul_of_nonneg_right (hle q.2) (hd r q)
    _ = dW (fun q : Unit × β ↦ φ' q.2) σ :=
        sum_dW_conj_of_keep K _ (fun r a a' h ↦ hkeep r a a' h) hsum σ
    _ = ∑ q, φ q.2 * (σ q q).re := Finset.sum_congr rfl fun q _ ↦ by
        by_cases h0 : σ q q = 0
        · rw [h0, Complex.zero_re, mul_zero, mul_zero]
        · rw [hsupp q h0]

omit [Fintype M₁] in
theorem recKraus_apply_eq (T : Finset HPos) (m : Finset HPos × M₁)
    (t s : Unit × HwReg X₁ Z₁ (Finset HPos × M₁)) :
    recKraus (X := X₁) (Z := Z₁) T m t s =
      if m = s.2.2.2 ∧ t = ((), recMapR T s.2) then 1 else 0 := by
  obtain ⟨⟨⟩, D', W', m'⟩ := t
  obtain ⟨⟨⟩, D, W, mm⟩ := s
  simp only [recKraus, kroneckerMap_apply, Matrix.one_apply_eq, one_mul, clsKraus_apply,
    Matrix.one_apply, recMapR, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- **A record port on a diagonal potential**: the weights after it are those of the recorded
states. -/
theorem tsum_potential_rec_eq {φ : HwReg X₁ Z₁ (Finset HPos × M₁) → ℝ} (hφ0 : ∀ s, 0 ≤ φ s)
    (T : Finset HPos)
    {σ : Matrix (Unit × HwReg X₁ Z₁ (Finset HPos × M₁)) (Unit × HwReg X₁ Z₁ (Finset HPos × M₁)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' m, potential (diagPot fun s ↦ √(φ s))
        (MatrixMap.conj (recKraus (X := X₁) (Z := Z₁) T m) σ) =
      ENNReal.ofReal (∑ q, φ (recMapR T q.2) * (σ q q).re) := by
  have hpost : ∀ m, 0 ≤ dW (fun q : Unit × HwReg X₁ Z₁ (Finset HPos × M₁) ↦ φ q.2)
      (MatrixMap.conj (recKraus (X := X₁) (Z := Z₁) T m) σ) := fun m ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  have hpot : ∀ τ : Matrix (Unit × HwReg X₁ Z₁ (Finset HPos × M₁))
      (Unit × HwReg X₁ Z₁ (Finset HPos × M₁)) ℂ,
      potential (diagPot fun s ↦ √(φ s)) τ = ENNReal.ofReal (dW (fun q ↦ φ q.2) τ) :=
    fun τ ↦ potential_diagPot_sqrt hφ0 τ
  have hinj : ∀ q q' : Unit × HwReg X₁ Z₁ (Finset HPos × M₁), q.2.2.2 = q'.2.2.2 →
      ((), recMapR T q.2) = ((), recMapR T q'.2) → q = q' := fun q q' hi hf ↦
    Prod.ext (Subsingleton.elim _ _) (Prod.ext (congrArg (fun t ↦ t.2.1) hf)
      (Prod.ext (congrArg (fun t ↦ t.2.2.1) hf) hi))
  simp only [hpot]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun m _ ↦ hpost m, sum_dW_conj,
    gram_classical_diag (recKraus (X := X₁) (Z := Z₁) T) (fun q ↦ q.2.2.2)
      (fun q ↦ ((), recMapR T q.2)) (recKraus_apply_eq T) hinj, re_trace_diagonal_mul]

end steps

/-! ## The label invariant of the searches and `Ψ` along the prefix -/

section labRun

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- **The label invariant of the search modes**: in the search of `lab`, its base is revealed. -/
def labInv : CwMode → Set (HwReg X Z Mem)
  | .free => Set.univ
  | .grd lab _ _ => {s | Sum.inr lab ∈ s.2.2.1}
  | .afK lab _ _ _ => {s | Sum.inr lab ∈ s.2.2.1}
  | .afK' lab _ _ _ _ => {s | Sum.inr lab ∈ s.2.2.1}

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- **The allowed calls keep the label invariant**: a reveal records the label whose search it
starts, the searches' reads keep the memory label. -/
theorem labInv_step (v : HPos → Digest) (μ : CwMode) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ)
    (hok : cwOkZ π P (cwLiftHu (cwHu1 cwUpd)) μ i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) (labInv μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) (labInv (cwNxZ π P v μ i r))
        (((runtimeR m0R).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · exact querySupportedOn_univ _ _
  · have hb : ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    rw [hb]
    rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
      rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z'⟩
    all_goals try exact hok.elim
    · obtain ⟨rfl, rfl⟩ := hok
      refine hσ.conj fun q' q hK hq ↦ ?_
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
      obtain ⟨-, -, h3, h4⟩ := cw_readKrausH_ne_zero _ _ r hK'
      have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [h4, h3]; rfl
      show Sum.inr lab ∈ q'.2.2.2.1
      rw [hl]
      exact hq
    · obtain ⟨-, rfl, rfl⟩ := hok
      refine hσ.conj fun q' q hK hq ↦ ?_
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
      obtain ⟨-, -, -, -, h5, h6⟩ := cw_readKrausK_ne_zero _ _ r hK'
      have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [h6, h5]
      show Sum.inr lab ∈ q'.2.2.2.1
      rw [hl]
      exact hq
    · obtain ⟨rfl, rfl⟩ := hok
      refine hσ.conj fun q' q hK hq ↦ ?_
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
      obtain ⟨-, -, -, h4, h5⟩ := cw_readKrausK'_ne_zero _ _ r hK'
      have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [h5, h4]
      show Sum.inr lab ∈ q'.2.2.2.1
      rw [hl]
      exact hq
  · exact querySupportedOn_univ _ _
  · cases ho : cwRevLab T with
    | none =>
      have hn : cwNxZ π P v μ (.inr T) r = .free := by
        show cwOptNx (cwRevLab T) _ = _
        rw [ho]
        rfl
      rw [hn]
      exact querySupportedOn_univ _ _
    | some lab =>
      have hn : cwNxZ π P v μ (.inr T) r = .grd lab (v (.inr lab)) 0 := by
        show cwOptNx (cwRevLab T) _ = _
        rw [ho]
        rfl
      have hT : T = {Sum.inr lab} := cwRevLab_spec ho
      rw [hn]
      refine QuerySupportedOn.conj (K := recKraus (X := X) (Z := Z) T r) hσ fun q' q hK _ ↦ ?_
      rw [eq_of_recKraus_ne_zero (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK]
      show Sum.inr lab ∈ q.2.2.2.1 ∪ T
      rw [hT]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- The drops of `Ψ` at the record ports. -/
noncomputable def revDropW :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ → ℝ≥0∞
  | .inr T, σ => ENNReal.ofReal (∑ q, revDropO (IsBlk P) (cwRevLab T) q.2 * (σ q q).re)
  | _, _ => 0

/-- The traces at the sponge ports. -/
noncomputable def spongeTrW (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ) : ℝ≥0∞ :=
  ((if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1 : ℕ) : ℝ≥0∞) *
    ENNReal.ofReal σ.trace.re

theorem revDropO_nonneg (o : Option RLabel) (s : HwReg X Z Mem) :
    0 ≤ revDropO (IsBlk P) o s := by
  cases o with
  | none => exact le_rfl
  | some lab =>
    show 0 ≤ revDrop (IsBlk P) lab s
    unfold revDrop
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _

/-- **The step of `Ψ`**: a sponge call raises it by at most its trace; a search's read, a program
and a record do not raise it, a record lowering it by the first-reveal drop. -/
theorem revPot_step (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ)
    (hσ : σ.PosSemidef)
    (hI : ∃ μ, cwOkZ π P (cwLiftHu (cwHu1 cwUpd)) μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
        (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) (labInv μ) σ) :
    revDropW P i σ + ∑' r, potential (diagPot fun s ↦ √(revPot (IsBlk P) s))
        (((runtimeR m0R).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(revPot (IsBlk P) s)) σ + spongeTrW i σ := by
  have hφ0 := revPot_nonneg (Z₁ := Z) (M₁ := Selections) (IsBlk P)
  rcases i with ((p | c) | c) | T
  · have hb : ∀ r : Unit, ((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R p r) σ
    have hc : spongeTrW (.inl (.inl (.inl p))) σ = ENNReal.ofReal σ.trace.re := by
      simp [spongeTrW, extCls, hwCls]
      rfl
    rw [hc]
    show 0 + _ ≤ _
    rw [zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans
      (tsum_potential_sponge_le hφ0 (oneCellLipschitz_revPot (IsBlk P) isBlk_unique)
        (hwEmpty X Z) m0R p hσ)
  · obtain ⟨μ, hok, hs⟩ := hI
    have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    have hc : spongeTrW (.inl (.inl (.inr c))) σ = 0 := by
      simp [spongeTrW, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    show ∑' r : c.Result, potential (diagPot fun s ↦ √(revPot (IsBlk P) s))
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ _
    rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
      rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z'⟩
    all_goals try exact hok.elim
    · obtain ⟨rfl, rfl⟩ := hok
      refine tsum_potential_le_of_keep _ (sum_hwReadKraus _) hφ0 (fun _ ↦ le_rfl)
        (fun r a a' h ↦ ?_) hσ (fun _ _ ↦ rfl)
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
      obtain ⟨h1, -, h3, h4⟩ := cw_readKrausH_ne_zero _ _ r hK'
      exact revPot_congr (IsBlk P) (congrArg Prod.fst h1) (by rw [h4, h3]; rfl)
    · obtain ⟨hj, rfl, rfl⟩ := hok
      have hx : IsBlk P lab (cwBlk P lab base j) := ⟨base, j, hj, rfl⟩
      refine tsum_potential_le_of_keep _ (sum_hwReadKraus _) hφ0
        (revPot_le_revPotAt (IsBlk P) (cwBlk P lab base j)) (fun r a a' h ↦ ?_) hσ
        (fun q hq ↦ (revPotAt_eq (IsBlk P) isBlk_unique hx (hs q q hq).1).symm)
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
      obtain ⟨-, -, h3, -, h5, h6⟩ := cw_readKrausK_ne_zero _ _ r hK'
      exact revPotAt_congr (IsBlk P) _ h3 (by rw [h6, h5])
    · obtain ⟨rfl, rfl⟩ := hok
      refine tsum_potential_le_of_keep _ (sum_hwReadKraus _) hφ0 (fun _ ↦ le_rfl)
        (fun r a a' h ↦ ?_) hσ (fun _ _ ↦ rfl)
      obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
      obtain ⟨-, h2, -, h4, h5⟩ := cw_readKrausK'_ne_zero _ _ r hK'
      exact revPot_congr (IsBlk P) h2 (by rw [h5, h4])
  · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r) σ
    have hc : spongeTrW (.inl (.inr c)) σ = 0 := by
      simp [spongeTrW, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    refine (le_of_eq (tsum_potential_prog_eq hφ0 c hσ)).trans ?_
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
    exact mul_le_mul_of_nonneg_right (revPot_progMap_le (IsBlk P) c q.2)
      (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  · have hc : spongeTrW (.inr T) σ = 0 := by
      simp [spongeTrW, extCls]
    rw [hc, add_zero]
    show ENNReal.ofReal (∑ q, revDropO (IsBlk P) (cwRevLab T) q.2 * (σ q q).re) +
      ∑' m, potential (diagPot fun s ↦ √(revPot (IsBlk P) s))
        (MatrixMap.conj (recKraus (X := X) (Z := Z) T m) σ) ≤ _
    rw [tsum_potential_rec_eq hφ0 T hσ]
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have h1 : 0 ≤ ∑ q, revDropO (IsBlk P) (cwRevLab T) q.2 * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (revDropO_nonneg P _ _) (hre q)
    have h2 : 0 ≤ ∑ q, revPot (IsBlk P) (recMapR T q.2) * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 _) (hre q)
    refine (ENNReal.ofReal_add h1 h2).symm.trans_le (ENNReal.ofReal_le_ofReal ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (revDropO_add_le (IsBlk P) T q.2) (hre q)

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The first-reveal drops of `Ψ` along the challenge prefix**: at most `6q`, the sponge calls
(the potential starts at `0`). -/
theorem totalWeight_revDropW_le (pub : Pub) (v : HPos → Digest) :
    (runtimeR m0R).totalWeight .instruments (revDropW pub.param)
      (realizeT v (prefixT Selections cwUpd pub A)) initR ≤ 6 * q := by
  set x := realizeT v (prefixT Selections cwUpd pub A)
  have hφ0 := revPot_nonneg (Z₁ := Z) (M₁ := Selections) (IsBlk pub.param)
  have hx := forallQueries_of_modedP (runtimeR m0R) .instruments labInv
    (fun μ i r σ hok h ↦ labInv_step pub.perm pub.param v μ i r σ hok h) x .free
    (modedP_prefixR cwUpd pub A v) (ρ := initR) (querySupportedOn_univ _ _)
  have h := totalWeight_le_potential_of_forallQueries (runtimeR m0R) .instruments
    (diagPot fun s ↦ √(revPot (IsBlk pub.param) s)) _
    (fun i σ ↦ ∃ μ, cwOkZ pub.perm pub.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
        (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) (labInv μ) σ)
    (fun i E σ hP ↦ by
      obtain ⟨μ, hok, hs⟩ := hP
      exact ⟨μ, hok, querySupportedOn_traceRight hs⟩)
    (revDropW pub.param) spongeTrW
    (fun i σ hσ hI ↦ revPot_step pub.perm pub.param i σ hσ hI) x initR_posSemidef hx
  have h0 : potential (diagPot fun s ↦ √(revPot (IsBlk pub.param) s)) initR = 0 := by
    unfold initR
    rw [potential_basis_init m0R hφ0 ()]
    refine (congrArg ENNReal.ofReal (Finset.sum_eq_zero fun y _ ↦ ite_eq_right fun h ↦
      h rfl)).trans ENNReal.ofReal_zero
  refine h.trans ((add_le_add (le_of_eq h0) le_rfl).trans ?_)
  rw [zero_add]
  refine (totalWeight_chargeTrace_le (runtimeR m0R) .instruments _ x
    (chg_prefixT_of_gameT (hN_sponge cwUpd A hperm hsign pub v)) initR_posSemidef).trans ?_
  calc ((6 * q : ℕ) : ℝ≥0∞) * ENNReal.ofReal initR.trace.re ≤ (6 * q : ℕ) * 1 := by
        gcongr
        exact ofReal_trace_initR_le_one
    _ = 6 * q := by rw [mul_one]; push_cast; ring

end labRun

/-- Membership in a filter of the whole type (over abstract types). -/
theorem mem_filter_univ_of {α : Type} [Fintype α] {p : α → Prop} [DecidablePred p] {a : α}
    (h : p a) : a ∈ Finset.univ.filter p :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

/-- A filter injected into another (over abstract types). -/
theorem card_filter_le_of_injective {α β : Type} [Fintype α] [Fintype β] {f : α → β}
    (hf : Function.Injective f) (p : α → Prop) [DecidablePred p] (r : β → Prop)
    [DecidablePred r] (h : ∀ a, p a → r (f a)) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter r).card := by
  classical
  refine Finset.card_le_card_of_injOn f (by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, h a ha.2⟩) (fun a _ a' _ e ↦ hf e)

/-! ## The first reveals: Disclose's view lemma against `Ψ` -/

section first

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable (P : PublicParameter)

/-- At a reveal of `lab` with base `b`: `lab` unrevealed, the block of trial `j` recorded. -/
def FirstRec (lab : RLabel) (b : Randomizer) (j : ℕ) (s : HwReg X Z Mem) : Prop :=
  Sum.inr lab ∉ s.2.2.1 ∧ s.1.2.1 (cwBlk P lab b j) ≠ none

/-- At a reveal of `lab` with base `b`: `lab` unrevealed, the block of trial `j` hardwired, the
key unselected. -/
def FirstHw (lab : RLabel) (b : Randomizer) (j : ℕ) (s : HwReg X Z Mem) : Prop :=
  Sum.inr lab ∉ s.2.2.1 ∧ s.2.1.2.1 (cwBlk P lab b j) ≠ none ∧ cwU lab s.2.2

/-- At a reveal of `lab`: `lab` already revealed (its search ran before) and its key
unselected. -/
def ReRev (lab : RLabel) (s : HwReg X Z Mem) : Prop :=
  Sum.inr lab ∈ s.2.2.1 ∧ cwU lab s.2.2

/-- The first-run states of trial `j` at a reveal labelled `o`. -/
def firstSetO (v : HPos → Digest) (j : ℕ) (o : Option RLabel) : Set (Unit × HwReg X Z Mem) :=
  match o with
  | some lab => {q | FirstRec P lab (v (.inr lab)) j q.2}
  | none => ∅

/-- The first-run states of trial `j` at the reveals. -/
def firstSet (v : HPos → Digest) (j : ℕ) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Set ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
  | .inr T => firstSetO P v j (cwRevLab T)
  | _ => ∅

/-- The bases whose trial-`j` block is recorded at `s`. -/
noncomputable def firstF (j : ℕ) (lab : RLabel) (s : HwReg X Z Mem) : Finset Digest :=
  Finset.univ.filter fun b : Digest ↦ s.1.2.1 (cwBlk P lab b j) ≠ none

/-- The source of a reveal labelled `o`: its base, if unrevealed. -/
def firstSrcO (o : Option RLabel) (q : Unit × HwReg X Z Mem) : Finset HPos :=
  match o with
  | some lab => if Sum.inr lab ∈ q.2.2.2.1 then ∅ else {Sum.inr lab}
  | none => ∅

/-- The sources at the reveals. -/
noncomputable def firstSrc : ∀ i : (recHwSpec X Z HPos Selections).Port,
    (recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem) → Finset HPos
  | .inr T, q => firstSrcO (cwRevLab T) q
  | _, _ => ∅

/-- The source values of a reveal labelled `o`. -/
noncomputable def firstFO (j : ℕ) (o : Option RLabel) (q : Unit × HwReg X Z Mem) :
    Finset Digest :=
  match o with
  | some lab => firstF P j lab q.2
  | none => ∅

/-- The source values at the reveals. -/
noncomputable def firstFv (j : ℕ) : ∀ i : (recHwSpec X Z HPos Selections).Port,
    (recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem) → (s : HPos) →
      ((s : HPos) → XD s) → Finset (XD s)
  | .inr T, q => fun _ _ ↦ firstFO P j (cwRevLab T) q
  | _, _ => fun _ _ ↦ ∅

/-- The weight per state of a reveal labelled `o`. -/
noncomputable def firstKO (j : ℕ) (o : Option RLabel) (q : Unit × HwReg X Z Mem) : ℝ≥0∞ :=
  ∑ _s ∈ firstSrcO o q, ((firstFO P j o q).card : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹

/-- The weights per state at the reveals. -/
noncomputable def firstK (j : ℕ) : ∀ i : (recHwSpec X Z HPos Selections).Port,
    (recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem) → ℝ≥0∞
  | .inr T, q => firstKO P j (cwRevLab T) q
  | _, _ => 0

/-- **The view lemma at the first reveals, trial by trial**: the first-run masses of trial `j`,
summed over the hidden values, are at most the weights `firstK` (the undisclosed base is the
source). -/
theorem sum_totalWeight_firstSet_le (pub : Pub) (A : Adversary (X × Z)) (j : ℕ) :
    ∑ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments
        (fun i ↦ diagMass (firstSet pub.param v j i))
        (realizeT v (prefixT Selections cwUpd pub A)) initR ≤
      ∑ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments
        (fun i ↦ kWt (firstK pub.param j i)) (realizeT v (prefixT Selections cwUpd pub A))
          initR := by
  have h := sum_totalWeight_le_of_forall (runtimeR m0R) LocalSig.Interp.instruments
    (fun v i ↦ diagMass (firstSet pub.param v j i)) (fun i ↦ kWt (firstK pub.param j i))
    (fun v ↦ realizeT v (prefixT Selections cwUpd pub A)) (fun _ ↦ initR) 1 fun n ↦ by
      rw [one_mul]
      refine sum_queryWeight_view_le_wt (runtimeR m0R) LocalSig.Interp.instruments
        (fun r ↦ r.2.2.1) (fun v ↦ realizeT v (prefixT Selections cwUpd pub A)) (fun _ ↦ initR)
        (fun _ ↦ initR_posSemidef) n (fun _ ↦ True)
        ((viewBy_runtimeR_of_disc LocalSig.Interp.instruments m0R (prefixT Selections cwUpd pub A)
          ∅ (disc_prefixT Selections cwUpd pub A ∅) (fun _ ↦ initR) (lazy_const _ initR)
          (fun _ ↦ suppAt_empty _ initR) n).viewByOn fun _ ↦ True)
        (fun v ↦ firstSet pub.param v j) (fun _ _ h ↦ absurd trivial h) firstSrc
        (firstFv pub.param j) (fun i p s v d ↦ ?_) (fun v i p hp ↦ ?_) (firstK pub.param j)
        (fun i p v ↦ ?_)
      · rcases i with ((i | c) | c) | T <;> rfl
      · rcases i with ((i | c) | c) | T
        · exact hp.elim
        · exact hp.elim
        · exact hp.elim
        · have hp' : p ∈ firstSetO pub.param v j (cwRevLab T) := hp
          show ∃ s ∈ firstSrcO (cwRevLab T) p, s ∉ p.2.2.2.1 ∧
            v s ∈ firstFO pub.param j (cwRevLab T) p
          revert hp'
          cases cwRevLab T with
          | none => exact fun hp' ↦ hp'.elim
          | some lab =>
            intro hp'
            refine ⟨Sum.inr lab, ?_, hp'.1, mem_filter_univ_of hp'.2⟩
            show Sum.inr lab ∈ (if Sum.inr lab ∈ p.2.2.2.1 then ∅ else {Sum.inr lab})
            rw [ite_eq_right hp'.1]
            exact Finset.mem_singleton_self _
      · rcases i with ((i | c) | c) | T
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_rfl
  rwa [one_mul] at h

/-- The constant of the first reveals: `4 · 2^32` trials per unit of `Ψ`, over `|Digest|`. -/
noncomputable def revFirstC : ℝ≥0∞ :=
  ((randomizerAttemptLimit * 4 : ℕ) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹

/-- The bases whose trial-`j` block is recorded inject into the recorded trial blocks. -/
theorem card_firstF_le {j : ℕ} (hj : j < randomizerAttemptLimit) (lab : RLabel)
    (s : HwReg X Z Mem) :
    (firstF P j lab s).card ≤
      (Finset.univ.filter fun y : X ↦ s.1.2.1 y ≠ none ∧ IsBlk P lab y).card :=
  card_filter_le_of_injective (cwBlk_base_inj P lab j) _ _ fun b hb ↦ ⟨hb, b, j, hj, rfl⟩

/-- **The first-reveal constant at Keccak's sizes**: `4 · 2^32 / 2^128 = 2^-94`, so the first
reveals cost `6q · 2^-94 = 24q · 2^-96`. -/
theorem revFirstC_eq : revFirstC = ((2 : ℝ≥0∞) ^ 94)⁻¹ := by
  have h4 : ((randomizerAttemptLimit * 4 : ℕ) : ℝ≥0∞) = 2 ^ 34 := by
    unfold randomizerAttemptLimit
    norm_num
  have h128 : (2 : ℝ≥0∞) ^ 128 = 2 ^ 34 * 2 ^ 94 := by rw [← pow_add]
  rw [revFirstC, card_digest_inv, h4, h128,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top
      ENNReal.ofNat_ne_top)), ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]

/-- **The weights of the trials at a reveal against the drop of `Ψ`.** -/
theorem sum_firstK_le (T : Finset HPos) (q : Unit × HwReg X Z Mem) :
    ∑ J : Fin randomizerAttemptLimit × Fin 4, firstKO P J.1 (cwRevLab T) q ≤
      revFirstC * ENNReal.ofReal (revDropO (IsBlk P) (cwRevLab T) q.2) := by
  cases cwRevLab T with
  | none => exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_empty) zero_le
  | some lab =>
    by_cases hl : Sum.inr lab ∈ q.2.2.2.1
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun J _ ↦ ?_) zero_le
      show ∑ _s ∈ (if Sum.inr lab ∈ q.2.2.2.1 then ∅ else {Sum.inr lab}), _ = 0
      rw [ite_eq_left hl, Finset.sum_empty]
    · have hd : revDropO (IsBlk P) (some lab) q.2 =
          ((Finset.univ.filter fun y : X ↦ q.2.1.2.1 y ≠ none ∧ IsBlk P lab y).card : ℝ) := by
        show revDrop (IsBlk P) lab q.2 = _
        unfold revDrop
        rw [ite_eq_right hl]
      have hK : ∀ J : Fin randomizerAttemptLimit × Fin 4, firstKO P J.1 (some lab) q =
          ((firstF P J.1 lab q.2).card : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := fun J ↦ by
        show ∑ _s ∈ (if Sum.inr lab ∈ q.2.2.2.1 then ∅ else {Sum.inr lab}), _ = _
        rw [ite_eq_right hl, Finset.sum_singleton]
        rfl
      rw [hd, ENNReal.ofReal_natCast]
      simp only [hK]
      calc ∑ J : Fin randomizerAttemptLimit × Fin 4,
            ((firstF P J.1 lab q.2).card : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹
          ≤ ∑ _J : Fin randomizerAttemptLimit × Fin 4,
              ((Finset.univ.filter fun y : X ↦ q.2.1.2.1 y ≠ none ∧ IsBlk P lab y).card :
                ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
            Finset.sum_le_sum fun J _ ↦ mul_le_mul'
              (Nat.cast_le.mpr (card_firstF_le P J.1.isLt lab q.2)) le_rfl
        _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul, revFirstC, mul_assoc,
              mul_comm (Fintype.card Digest : ℝ≥0∞)⁻¹]

/-- The first-run charges: four times each trial whose block is recorded at a first reveal. -/
noncomputable def firstW (v : HPos → Digest) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ) : ℝ≥0∞ :=
  ∑ J : Fin randomizerAttemptLimit × Fin 4, diagMass (firstSet P v J.1 i) σ

theorem sum_kWt_firstK_le (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ)
    (hσ : σ.PosSemidef) :
    ∑ J : Fin randomizerAttemptLimit × Fin 4, kWt (firstK P J.1 i) σ ≤
      revFirstC * revDropW P i σ := by
  rcases i with ((i | c) | c) | T
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      zero_mul _) zero_le
  · have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    show ∑ J : Fin randomizerAttemptLimit × Fin 4, ∑ q, firstKO P J.1 (cwRevLab T) q *
        ENNReal.ofReal (σ q q).re ≤
      revFirstC * ENNReal.ofReal (∑ q, revDropO (IsBlk P) (cwRevLab T) q.2 * (σ q q).re)
    rw [Finset.sum_comm, ENNReal.ofReal_sum_of_nonneg fun q _ ↦
      mul_nonneg (revDropO_nonneg P _ _) (hre q), Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← Finset.sum_mul, ENNReal.ofReal_mul (revDropO_nonneg P _ _), ← mul_assoc]
    exact mul_le_mul' (sum_firstK_le P T q) le_rfl

theorem totalWeight_firstW_eq {Ω : QReg → Type} (v : HPos → Digest)
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z Mem)) (QReg.of Unit × QReg.of (HwReg X Z Mem))
      ℂ) :
    (runtimeR m0R).totalWeight .instruments (firstW P v) x ρ =
      ∑ J : Fin randomizerAttemptLimit × Fin 4,
        (runtimeR m0R).totalWeight .instruments (fun i ↦ diagMass (firstSet P v J.1 i)) x ρ :=
  totalWeight_fintype_sum (runtimeR m0R) .instruments
    (fun (J : Fin randomizerAttemptLimit × Fin 4) i ↦ diagMass (firstSet P v J.1 i))
    x ρ

theorem sum_totalWeight_kWt_le {Ω : QReg → Type}
    (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    {ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z Mem)) (QReg.of Unit × QReg.of (HwReg X Z Mem))
      ℂ} (hρ : ρ.PosSemidef) :
    ∑ J : Fin randomizerAttemptLimit × Fin 4,
        (runtimeR m0R).totalWeight .instruments (fun i ↦ kWt (firstK P J.1 i)) x ρ ≤
      revFirstC * (runtimeR m0R).totalWeight .instruments (revDropW P) x ρ := by
  rw [← totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun (J : Fin randomizerAttemptLimit × Fin 4) i ↦ kWt (firstK P J.1 i)) x ρ,
    ← totalWeight_const_mul_weight (runtimeR m0R) .instruments revFirstC (revDropW P) x ρ]
  exact totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (fun i σ hσ ↦ sum_kWt_firstK_le P i σ hσ) x hρ

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The first-run charges**: summed over the hidden values, at most `revFirstC · 6q` per hidden
value (`4 · 2^32 · 6q / 2^128 = 24q · 2^-96`). -/
theorem sum_totalWeight_firstW_le (pub : Pub) :
    ∑ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments (firstW pub.param v)
        (realizeT v (prefixT Selections cwUpd pub A)) initR ≤
      revFirstC * (6 * q) * Fintype.card (HPos → Digest) := by
  calc ∑ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments (firstW pub.param v)
        (realizeT v (prefixT Selections cwUpd pub A)) initR
      = ∑ v : HPos → Digest, ∑ J : Fin randomizerAttemptLimit × Fin 4,
          (runtimeR m0R).totalWeight .instruments (fun i ↦ diagMass (firstSet pub.param v J.1 i))
            (realizeT v (prefixT Selections cwUpd pub A)) initR :=
        Finset.sum_congr rfl fun v _ ↦ totalWeight_firstW_eq pub.param v _ initR
    _ = ∑ J : Fin randomizerAttemptLimit × Fin 4, ∑ v : HPos → Digest,
          (runtimeR m0R).totalWeight .instruments (fun i ↦ diagMass (firstSet pub.param v J.1 i))
            (realizeT v (prefixT Selections cwUpd pub A)) initR := Finset.sum_comm
    _ ≤ ∑ J : Fin randomizerAttemptLimit × Fin 4, ∑ v : HPos → Digest,
          (runtimeR m0R).totalWeight .instruments (fun i ↦ kWt (firstK pub.param J.1 i))
            (realizeT v (prefixT Selections cwUpd pub A)) initR :=
        Finset.sum_le_sum fun J _ ↦ sum_totalWeight_firstSet_le pub A J.1
    _ = ∑ v : HPos → Digest, ∑ J : Fin randomizerAttemptLimit × Fin 4,
          (runtimeR m0R).totalWeight .instruments (fun i ↦ kWt (firstK pub.param J.1 i))
            (realizeT v (prefixT Selections cwUpd pub A)) initR := Finset.sum_comm
    _ ≤ ∑ v : HPos → Digest, revFirstC * (runtimeR m0R).totalWeight .instruments
          (revDropW pub.param) (realizeT v (prefixT Selections cwUpd pub A)) initR :=
        Finset.sum_le_sum fun v _ ↦ sum_totalWeight_kWt_le pub.param _ initR_posSemidef
    _ ≤ ∑ _v : HPos → Digest, revFirstC * (6 * q) :=
        Finset.sum_le_sum fun v _ ↦ mul_le_mul' le_rfl (totalWeight_revDropW_le hperm hsign pub v)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end first

/-! ## The reveal charges: first reveals, hardwired blocks, repeated reveals -/

section assemble

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable (P : PublicParameter)

/-- The hardwired first-run charge of a reveal labelled `o`. -/
noncomputable def hwRevO (o : Option RLabel) (bse : RLabel → Randomizer)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  match o with
  | some lab => ∑ J : Fin randomizerAttemptLimit × Fin 4,
      diagMass {q : Unit × HwReg X Z Mem | FirstHw P lab (bse lab) J.1 q.2} σ
  | none => 0

/-- **The hardwired first-run charges**: four times each trial whose block is hardwired at a
first reveal, the key unselected. -/
noncomputable def hwRevW (v : HPos → Digest) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ → ℝ≥0∞
  | .inr T, σ => hwRevO P (cwRevLab T) (fun lab ↦ v (.inr lab)) σ
  | _, _ => 0

/-- The repeated-reveal mass of a reveal labelled `o`. -/
noncomputable def reRevO (o : Option RLabel)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  match o with
  | some lab => diagMass {q : Unit × HwReg X Z Mem | ReRev lab q.2} σ
  | none => 0

/-- **The repeated-reveal masses**: at a reveal of an already revealed label, the mass with its
key unselected (the earlier search failed). -/
noncomputable def reRevW :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ → ℝ≥0∞
  | .inr T, σ => reRevO (cwRevLab T) σ
  | _, _ => 0

/-- A diagonal mass of a set covered by three sets. -/
theorem diagMass_le_three {α : Type} [Fintype α] {S A B C : Set α}
    (h : ∀ a ∈ S, a ∈ A ∨ a ∈ B ∨ a ∈ C) (σ : Matrix α α ℂ) :
    diagMass S σ ≤ diagMass A σ + diagMass B σ + diagMass C σ := by
  classical
  simp only [diagMass, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  by_cases hS : a ∈ S
  · rw [Set.indicator_of_mem hS]
    rcases h a hS with hA | hB | hC
    · rw [Set.indicator_of_mem hA]
      exact le_self_add.trans le_self_add
    · rw [Set.indicator_of_mem hB]
      exact le_add_self.trans le_self_add
    · rw [Set.indicator_of_mem hC]
      exact le_add_self
  · rw [Set.indicator_of_notMem hS]
    exact zero_le

/-- **The split of a reveal charge** by the label at the reveal: first runs (block recorded or
hardwired) and repeated reveals, the latter `4 · 2^32` times their mass. -/
theorem cwRevW_le (v : HPos → Digest) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ) :
    cwRevW P v i σ ≤ firstW P v i σ + hwRevW P v i σ +
      ((randomizerAttemptLimit * 4 : ℕ) : ℝ≥0∞) * reRevW i σ := by
  rcases i with ((i | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · show cwRevCharge P (cwRevLab T) (fun lab ↦ v (.inr lab)) σ ≤
      ∑ J : Fin randomizerAttemptLimit × Fin 4, diagMass (firstSetO P v J.1 (cwRevLab T)) σ +
        hwRevO P (cwRevLab T) (fun lab ↦ v (.inr lab)) σ +
          ((randomizerAttemptLimit * 4 : ℕ) : ℝ≥0∞) * reRevO (cwRevLab T) σ
    cases cwRevLab T with
    | none => exact zero_le
    | some lab =>
      show ∑ J : Fin randomizerAttemptLimit × Fin 4,
          diagMass {q : Unit × HwReg X Z Mem | q.2 ∈ cwTD P lab (v (.inr lab)) J.1} σ ≤
        ∑ J : Fin randomizerAttemptLimit × Fin 4,
            diagMass {q : Unit × HwReg X Z Mem | FirstRec P lab (v (.inr lab)) J.1 q.2} σ +
          ∑ J : Fin randomizerAttemptLimit × Fin 4,
            diagMass {q : Unit × HwReg X Z Mem | FirstHw P lab (v (.inr lab)) J.1 q.2} σ +
          ((randomizerAttemptLimit * 4 : ℕ) : ℝ≥0∞) *
            diagMass {q : Unit × HwReg X Z Mem | ReRev lab q.2} σ
      calc ∑ J : Fin randomizerAttemptLimit × Fin 4,
            diagMass {q : Unit × HwReg X Z Mem | q.2 ∈ cwTD P lab (v (.inr lab)) J.1} σ
          ≤ ∑ J : Fin randomizerAttemptLimit × Fin 4,
              (diagMass {q : Unit × HwReg X Z Mem | FirstRec P lab (v (.inr lab)) J.1 q.2} σ +
                diagMass {q : Unit × HwReg X Z Mem | FirstHw P lab (v (.inr lab)) J.1 q.2} σ +
                diagMass {q : Unit × HwReg X Z Mem | ReRev lab q.2} σ) :=
            Finset.sum_le_sum fun J _ ↦ diagMass_le_three (fun a ha ↦ by
              by_cases hl : Sum.inr lab ∈ a.2.2.2.1
              · exact Or.inr (Or.inr ⟨hl, ha.2⟩)
              · rcases ha.1 with hd | hw
                · exact Or.inl ⟨hl, hd⟩
                · exact Or.inr (Or.inl ⟨hl, hw, ha.2⟩)) σ
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]

end assemble

/-! ## The hardwired trial blocks vanish when no in-table `k`-cell is a trial block -/

section hwOff

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- A program keeps the hardwired `k`-cells in `K` when a `k` program is at a cell of `K`. -/
theorem hwK_progUpdate {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁] (K : Set X₁)
    (c : HwProg X₁ Z₁) (W : Hw X₁ Z₁) (hW : ∀ x, W.2.1 x ≠ none → x ∈ K)
    (hc : ∀ y a, c = .programK y a → y ∈ K) :
    ∀ x, (progUpdate c W).2.1 x ≠ none → x ∈ K := by
  intro x hx
  rcases c with ⟨z, a⟩ | ⟨y, a⟩ | ⟨y, a⟩
  · exact hW x hx
  · by_cases hxy : x = y
    · subst hxy
      exact hc x a rfl
    · simp only [progUpdate, Function.update_of_ne hxy] at hx
      exact hW x hx
  · exact hW x hx

/-- A program port allowed by the `k`-cells `K`: a `k` program at a cell of `K`. -/
def ProgK (K : Set X) : HwProg X Z → Prop
  | .programK x _ => x ∈ K
  | _ => True

section tree

variable {M : Type} {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (M) in
/-- The condition of `ProgsK` on a command: a program port is allowed by `K`. -/
def CmdK (K : Set X) (v : HPos → Digest) {A : QReg} : QuantumComp.Cmd Λ (XSpec M) A → Prop
  | .query (.inl (.inr p)) _ _ => ProgK K (p.1.realize v)
  | _ => True

/-- **A template programming `k`-cells of `K` only**, realized at `v`. -/
def ProgsK (K : Set X) (v : HPos → Digest) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Ω A → Prop
  | _, .pure _ => True
  | _, .liftBind c next => CmdK M K v c ∧ ∀ b, ProgsK K v (next b)

variable (K : Set X) (v : HPos → Digest)

theorem progsK_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Ω A) :
    ProgsK K v (e ▸ y) ↔ ProgsK K v y := by
  subst e
  rfl

theorem progsK_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Y u)
    (hx : ProgsK K v x) (hg : ∀ u a, ProgsK K v (g u a)) : ProgsK K v (x.bind g) := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact hg _ a
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem progsK₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ Λ (XSpec M) A B α) (g : α → QuantumComp₂ Λ (XSpec M) B B' β)
    (hx : ProgsK K v x) (hg : ∀ a, ProgsK K v (g a)) : ProgsK K v (x.bind g) := by
  refine progsK_bind K v x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

theorem progsK_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor Λ spec)
      (QuantumComp.toIPFunctor Λ (XSpec M)))
    (hσ : ∀ A c, ProgsK K v (σ A c)) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor Λ spec) Ω A) : ProgsK K v (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact progsK_bind K v _ _ (hσ s c) fun u ans ↦ (progsK_cast K v ans.2 _).mpr (ih ans.1)

/-- Runtime 1's programs call no program port. -/
theorem progsK_readLift {A : QReg} (y : QuantumComp Λ (hwReadSpec X Z M) Ω A) :
    ProgsK K v (readLift goodAll y) := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind _ c next ih =>
    show ProgsK K v (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _

theorem progsK_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    ProgsK K v (QComp.act (spec := XSpec M) p) :=
  ⟨trivial, fun _ ↦ trivial⟩

theorem progsK_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, ProgsK K v (k r)) : ProgsK K v (revealThen goodAll T k) :=
  ⟨trivial, fun r ↦ progsK₂_bind K v _ _ (progsK_act K v _) fun _ ↦ hk r.down⟩

theorem progsK_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) (hpK : ProgK K (p.realize v)) (hk : ProgsK K v k) :
    ProgsK K v (progThen p hp k) :=
  ⟨hpK, fun _ ↦ progsK₂_bind K v _ _ (progsK_act K v _) fun _ ↦ hk⟩

theorem progsK_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD))
    (h : ∀ p ∈ ps, ProgK K (p.realize v)) : ProgsK K v (progPorts M B ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact progsK_progThen K v p trivial _ (h p List.mem_cons_self)
      (ih fun p' hp' ↦ h p' (List.mem_cons_of_mem _ hp'))

theorem progsK_progSlots (pub : Pub) (B : QReg) (ss : List Slot)
    (h : ∀ s ∈ ss, ∀ p ∈ slotPorts pub s, ProgK K (p.realize v)) :
    ProgsK K v (progSlots M pub B ss) := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    exact progsK₂_bind K v _ _ (progsK_progPorts K v B _ (h s List.mem_cons_self)) fun _ ↦
      ih fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')

variable (upd : TrialUpd M) {pub : Pub}
  (hK : ∀ (l : Layer) (e : KeyIndex) (x : Encoding), e.val < keyCount l →
    ∀ s ∈ layerSlots l e x, ∀ p ∈ slotPorts pub s, ProgK K (p.realize v))
include hK

theorem progsK_signLayerT (B : QReg) (lab : RLabel) (he : lab.key.val < keyCount lab.layer) :
    ProgsK K v (signLayerT M upd pub B lab) := by
  refine progsK_revealThen K v _ _ fun _ ↦
    progsK₂_bind K v _ _ (progsK_readLift K v _) ?_
  rintro (_ | ⟨ρ, x⟩)
  · trivial
  · exact progsK_revealThen K v _ _ fun _ ↦ progsK₂_bind K v _ _
      (progsK_progSlots K v pub B _ (hK lab.layer lab.key x he)) fun _ ↦ trivial

theorem progsK_signT (B : QReg) (r : SigningRequest) : ProgsK K v (signT M upd pub B r) := by
  refine progsK₂_bind K v _ _ (progsK_signLayerT K v upd hK B (botLabel r)
    (keyIndexOnLayer_lt r.leafIndex bottomLayer)) ?_
  rintro (_ | ⟨bottom, f⟩)
  · trivial
  · refine progsK₂_bind K v _ _ (progsK_signLayerT K v upd hK B (topLabel r _)
      (keyIndexOnLayer_lt r.leafIndex topLayer)) ?_
    rintro (_ | ⟨top, _⟩) <;> trivial

theorem progsK_challengeT (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    ProgsK K v (challengeT M upd pub A c) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact progsK_readLift K v _
  · exact progsK_readLift K v _
  · exact progsK_bind K v _ _ (progsK₂_bind K v _ _ (progsK_act K v _) fun _ ↦
      progsK_signT K v upd hK _ r) fun _ _ ↦ trivial

/-- **The challenge prefix programs `k`-cells of `K` only.** -/
theorem progsK_prefixT (A : Adversary (X × Z)) : ProgsK K v (prefixT M upd pub A) :=
  progsK_revealThen K v _ _ fun _ ↦
    progsK₂_bind K v _ _ (progsK_substitute K v _ (progsK_challengeT K v upd hK) _) fun _ ↦
      trivial

end tree

/-- The `k`-cells of the in-table slots at the values `w`. -/
def slotCellsK (pub : Pub) (w : ValPos → Digest) : Set X :=
  {x | ∃ s, InTable s ∧ ∃ j < nBlocks pub s, srcCellK pub s w j = x}

/-- **The signatures' program ports program `k`-cells of the in-table slots.** -/
theorem progK_slotPorts (pub : Pub) (v : HPos → Digest) {l : Layer} {e : KeyIndex}
    {x : Encoding} (he : e.val < keyCount l) {s : Slot} (hs : s ∈ layerSlots l e x)
    {p : LazyProg X Z HPos XD} (hp : p ∈ slotPorts pub s) :
    ProgK (slotCellsK pub fun q ↦ v (.inl q)) (p.realize v) := by
  simp only [slotPorts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  obtain ⟨j, hj, rfl | rfl | rfl⟩ := hp
  · have hv : ∀ q ∈ slotNeed s, extendVals (restrictTo (inlSet (slotNeed s)) v) q = v (.inl q) :=
      fun q hq ↦ extendVals_restrictTo (inl_mem_inlSet.mpr hq) v
    have e1 : roundK pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j =
        roundK pub s (fun p ↦ v (.inl p)) j := by
      simp only [roundK, slotInput_eq_of_need pub hv]
    show (roundK pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j).1 ∈ _
    rw [e1]
    exact ⟨s, inTable_of_mem_layerSlots he hs, j, hj, rfl⟩
  · trivial
  · trivial

/-- The hardwired `k`-cells lie in `K`. -/
def HwKIn (K : Set X) (s : HwReg X Z Mem) : Prop :=
  ∀ x, s.2.1.2.1 x ≠ none → x ∈ K

/-- The calls allowed by `K` on runtime 2 with record ports. -/
def PortK (K : Set X) : (recHwSpec X Z HPos Selections).Port → Prop
  | .inl (.inr c) => ProgK K c
  | _ => True

/-- **Realizing keeps the allowed program ports**, as a moded program with one mode. -/
theorem modedP_realizeT_progsK {K : Set X} (v : HPos → Digest) {L : LocalSig.{u, v}}
    {Ω : QReg → Type w} {A : QReg} (y : QuantumComp L (XSpec Selections) Ω A)
    (hy : ProgsK K v y) :
    ModedP (fun _ : Unit ↦ PortK K) (fun _ _ _ ↦ ()) (fun _ _ ↦ True) () (realizeT v y) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => trivial
  | liftBind _ c next ih =>
    show ModedP _ _ _ () (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 (ULift.up (restrictTo T v, b.down)))⟩

/-- **The allowed calls keep the hardwired `k`-cells in `K`.** -/
theorem hwKIn_step (K : Set X) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ)
    (hok : PortK K i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) {s | HwKIn K s} σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) {s | HwKIn K s}
        (((runtimeR m0R).step i).branch r σ) := by
  rcases i with ((p | c) | c) | T
  · have hb : ((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U p) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R p r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m0R p q.1 q'.1 q.2 q'.2 hK
      show HwKIn K q'.2
      intro x hx
      rw [congrArg Prod.fst he] at hx
      exact hq x hx
  · have hb : ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      show HwKIn K q'.2
      intro x hx
      rw [hwReadKraus_ne_zero_hw c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK] at hx
      exact hq x hx
  · have hb : ((runtimeR m0R).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      have he := hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
      show HwKIn K q'.2
      intro x hx
      rw [congrArg Prod.fst he] at hx
      exact hwK_progUpdate K c q.2.2.1 hq (fun y a hc ↦ by subst hc; exact hok) x hx
  · refine QuerySupportedOn.conj (K := recKraus (X := X) (Z := Z) T r) hσ fun q' q hK hq ↦ ?_
    show HwKIn K q'.2
    intro x hx
    rw [recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK] at hx
    exact hq x hx

/-- No in-table `k`-cell at `w` is a trial block. -/
def HwTrialOff (pub : Pub) (w : ValPos → Digest) : Prop :=
  ∀ s, InTable s → ∀ j < nBlocks pub s, ¬TrialBlock pub.param (srcCellK pub s w j)

/-- `HwTrialOff`, decided classically. -/
noncomputable instance instDecidableHwTrialOff (pub : Pub) : DecidablePred (HwTrialOff pub) :=
  Classical.decPred _

/-- **`TrialHidGood` with good sources keeps the trial blocks off the in-table `k`-cells.** -/
theorem hwTrialOff_of_trialHidGood {pub : Pub} {v : HPos → Digest} (h : TrialHidGood pub v)
    (hs : SrcGood pub fun q ↦ v (.inl q)) : HwTrialOff pub fun q ↦ v (.inl q) :=
  fun s hsI j hj hT ↦ h.2 _ hT
    (show SrcGood pub (fun q ↦ v (.inl q)) ∧ ∃ s', InTable s' ∧ ∃ j' < nBlocks pub s',
      srcCellK pub s' (fun q ↦ v (.inl q)) j' = srcCellK pub s (fun q ↦ v (.inl q)) j from
      ⟨hs, s, hsI, j, hj, rfl⟩)

/-- A trial's block is a trial block. -/
theorem trialBlock_cwBlk (P : PublicParameter) (lab : RLabel) (b : Randomizer) (j : ℕ) :
    TrialBlock P (cwBlk P lab b j) := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (length_blocks_trial P
    (hashDomainFields (.message lab.layer lab.key)) (RLabel.length_msg_le lab) b j)
  have e1 : cwBlk P lab b j = c := by simp [cwBlk, hc]
  exact ⟨lab.layer, lab.key, lab.msg, b + BitVec.ofNat digestBits j, RLabel.length_msg_le lab,
    by rw [hc, e1]⟩

/-- A diagonal mass vanishes on an operator with no diagonal weight on its set. -/
theorem diagMass_eq_zero_of {α : Type} [Fintype α] {S : Set α} {σ : Matrix α α ℂ}
    (h : ∀ a ∈ S, σ a a = 0) : diagMass S σ = 0 :=
  Finset.sum_eq_zero fun a _ ↦ by
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, h a ha, Complex.zero_re, ENNReal.ofReal_zero]
    · exact Set.indicator_of_notMem ha _

/-- **The hardwired first-run charges vanish** when no in-table `k`-cell is a trial block: the
hardwired `k`-cells are the cells the signatures program, cells of the in-table slots. -/
theorem totalWeight_hwRevW_eq_zero (pub : Pub) (v : HPos → Digest) (A : Adversary (X × Z))
    (hoff : HwTrialOff pub fun q ↦ v (.inl q)) :
    (runtimeR m0R).totalWeight .instruments (hwRevW pub.param v)
      (realizeT v (prefixT Selections cwUpd pub A)) initR = 0 := by
  set K := slotCellsK pub fun q ↦ v (.inl q)
  have hmod := modedP_realizeT_progsK v _ (progsK_prefixT K v cwUpd
    (fun l e x he s hs p hp ↦ progK_slotPorts pub v he hs hp) A)
  have hinit : QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2)
      {s | HwKIn K s} initR :=
    (querySupportedOn_initR_hw (hwEmpty X Z)).mono fun s hs x hx ↦ by
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hx
      exact absurd (hs.2.1 x u hu) (by simp [hwEmpty])
  have hx := forallQueries_of_modedP (runtimeR m0R) .instruments (fun _ ↦ {s | HwKIn K s})
    (fun _ i r σ hok h ↦ hwKIn_step K i r σ hok h) _ () hmod hinit
  have hoffK : ∀ lab b j, cwBlk pub.param lab b j ∉ K := fun lab b j ⟨s, hs, j', hj', he⟩ ↦
    hoff s hs j' hj' (he ▸ trialBlock_cwBlk pub.param lab b j)
  refine le_antisymm ?_ zero_le
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2) {s | HwKIn K s} σ)
    (fun i E σ hP ↦ by
      obtain ⟨_, _, hs⟩ := hP
      exact querySupportedOn_traceRight hs)
    (w' := fun i σ ↦ 0 * hwRevW pub.param v i σ) (fun i σ _ hok ↦ ?_) _ initR_posSemidef
    hx).trans (le_of_eq ((totalWeight_const_mul_weight (runtimeR m0R) .instruments 0
      (hwRevW pub.param v) _ initR).trans (zero_mul _)))
  rw [zero_mul]
  rcases i with ((i | c) | c) | T
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · show hwRevO pub.param (cwRevLab T) (fun lab ↦ v (.inr lab)) σ ≤ 0
    cases cwRevLab T with
    | none => exact le_rfl
    | some lab =>
      refine le_of_eq (Finset.sum_eq_zero fun J _ ↦ diagMass_eq_zero_of fun q hq ↦ ?_)
      by_contra h0
      exact hoffK lab _ _ ((hok q q h0).1 _ hq.2.1)

end hwOff

/-! ## The codeword-recorded mass on the hidden values off trial blocks, and its average -/

section avgGood

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- **The constant of the codeword-recorded mass**: the first reveals `revFirstC · 6q`, the
repeated reveals `4 · 2^32 ε`, the fresh parts `cwFreshEps (6q + clsCap) · clsCap`. -/
noncomputable def cwRevTau (q : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  revFirstC * (6 * q) + ((randomizerAttemptLimit * 4 : ℕ) : ℝ≥0∞) * ε +
    ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap

/-- **The failed searches**: on a `PermGood` permutation, the mass at the repeated reveals with
the key unselected, summed over the hidden values off trial blocks, at most `ε` per hidden
value. -/
def CwReView (A : Adversary (X × Z)) (ε : ℝ≥0∞) : Prop :=
  ∀ p : RP, PermGood (pubR p).perm 18 → ∑ v : HPos → Digest,
    (if HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then (runtimeR m0R).totalWeight .instruments
      reRevW (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR else 0) ≤
      ε * Fintype.card (HPos → Digest)

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- The codeword-recorded mass at one hidden value: the fresh parts and the reveal charges. -/
theorem cwRecT_le_rev (pub : Pub) (v : HPos → Digest) :
    cwRecT A pub v ≤ ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap +
      (runtimeR m0R).totalWeight .instruments (cwRevW pub.param v)
        (realizeT v (prefixT Selections cwUpd pub A)) initR := by
  refine (cwRecT_le_charge A pub v).trans ?_
  refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := fun i σ ↦ cwFreshW pub.perm i σ + cwRevW pub.param v i σ)
    (fun i σ _ ↦ cwCharge_le _ _ v i σ) _ initR_posSemidef).trans ?_
  refine (le_of_eq (totalWeight_add_weight (runtimeR m0R) .instruments
    (cwFreshW pub.perm) (cwRevW pub.param v) _ initR)).trans ?_
  exact add_le_add (totalWeight_cwFreshW_le hperm hsign pub v) le_rfl

omit hperm hsign in
/-- The reveal charges at a hidden value off trial blocks: first runs and repeated reveals. -/
theorem totalWeight_cwRevW_le_good (pub : Pub) (v : HPos → Digest)
    (hoff : HwTrialOff pub fun q ↦ v (.inl q)) :
    (runtimeR m0R).totalWeight .instruments (cwRevW pub.param v)
        (realizeT v (prefixT Selections cwUpd pub A)) initR ≤
      (runtimeR m0R).totalWeight .instruments (firstW pub.param v)
          (realizeT v (prefixT Selections cwUpd pub A)) initR +
        ((randomizerAttemptLimit * 4 : ℕ) : ℝ≥0∞) * (runtimeR m0R).totalWeight .instruments
          reRevW (realizeT v (prefixT Selections cwUpd pub A)) initR := by
  set c : ℝ≥0∞ := ((randomizerAttemptLimit * 4 : ℕ) : ℝ≥0∞)
  refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := fun i σ ↦ (firstW pub.param v i σ + hwRevW pub.param v i σ) + c * reRevW i σ)
    (fun i σ _ ↦ cwRevW_le pub.param v i σ) _ initR_posSemidef).trans (le_of_eq
      ((totalWeight_add_weight (runtimeR m0R) .instruments
        (fun i σ ↦ firstW pub.param v i σ + hwRevW pub.param v i σ) (fun i σ ↦ c * reRevW i σ) _
          initR).trans ?_))
  rw [totalWeight_add_weight (runtimeR m0R) .instruments (firstW pub.param v)
      (hwRevW pub.param v) _ initR, totalWeight_hwRevW_eq_zero pub v A hoff, add_zero]
  exact congrArg (_ + ·) (totalWeight_const_mul_weight (runtimeR m0R) .instruments c reRevW _
    initR)

/-- **The codeword-recorded mass on the hidden values off trial blocks**, summed over the hidden
values: at most `cwRevTau q ε` per hidden value, given the failed searches `CwReView A ε`. -/
theorem sum_cwRecT_good_le {ε : ℝ≥0∞} (hre : CwReView A ε) (p : RP)
    (hπ : PermGood (pubR p).perm 18) :
    ∑ v : HPos → Digest, (if HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then
      cwRecT A (pubR p) v else 0) ≤ cwRevTau q ε * Fintype.card (HPos → Digest) := by
  set c : ℝ≥0∞ := ((randomizerAttemptLimit * 4 : ℕ) : ℝ≥0∞)
  set F : ℝ≥0∞ := ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap
  have hv : ∀ v : HPos → Digest, (if HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then
      cwRecT A (pubR p) v else 0) ≤
      F + ((runtimeR m0R).totalWeight .instruments (firstW (pubR p).param v)
          (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR +
        c * (if HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then (runtimeR m0R).totalWeight
          .instruments reRevW (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR
            else 0)) := fun v ↦ by
    split_ifs with hoff
    · exact (cwRecT_le_rev hperm hsign (pubR p) v).trans
        (add_le_add le_rfl (totalWeight_cwRevW_le_good (pubR p) v hoff))
    · exact zero_le
  calc ∑ v : HPos → Digest, (if HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then
        cwRecT A (pubR p) v else 0)
      ≤ ∑ v : HPos → Digest, (F + ((runtimeR m0R).totalWeight .instruments
          (firstW (pubR p).param v) (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR +
        c * (if HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then (runtimeR m0R).totalWeight
          .instruments reRevW (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR
            else 0))) :=
        Finset.sum_le_sum fun v _ ↦ hv v
    _ = F * Fintype.card (HPos → Digest) +
        (∑ v : HPos → Digest, (runtimeR m0R).totalWeight .instruments (firstW (pubR p).param v)
          (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR +
        c * ∑ v : HPos → Digest, (if HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then
          (runtimeR m0R).totalWeight .instruments reRevW
            (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
    _ ≤ F * Fintype.card (HPos → Digest) +
        (revFirstC * (6 * q) * Fintype.card (HPos → Digest) +
          c * (ε * Fintype.card (HPos → Digest))) :=
        add_le_add le_rfl (add_le_add (sum_totalWeight_firstW_le hperm hsign (pubR p))
          (mul_le_mul' le_rfl (hre p hπ)))
    _ = _ := by
        unfold cwRevTau
        ring

omit hperm hsign in
/-- A constant plus a scaled family, summed (over an abstract finite type). -/
theorem sum_const_add_mul_eq {K : Type} [Fintype K] (a : ℝ≥0∞) (N : ℕ) (f : K → ℝ≥0∞) :
    ∑ k, (a + N * f k) = Fintype.card K * a + N * ∑ k, f k := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

open scoped Classical in
/-- **The averaged codeword-recorded mass** over all tables: at most
`cwRevTau q ε + cwJunk + clsCap · 2^-400`, given the failed searches `CwReView A ε`. The tables
of ReparamR0's good set with `TrialHidGood` (whose in-table `k`-cells are no trial blocks, so no
trial block is ever hardwired) carry the per-datum bound `sum_cwRecT_good_le`; the others are at
most `2^-174 + 2^-400` of the tables (`r0G_frac_le_keccak`, HTrial's
`trialHidGood_r0G_frac_le_keccak`), at most `clsCap` each. -/
theorem uavg_cwRecPre_all_le_rev {ε : ℝ≥0∞} (hre : CwReView A ε) :
    uavg (cwRecPre A) ≤ cwRevTau q ε + cwJunk + clsCap * ENNReal.ofReal (1 / 2 ^ 400) := by
  set N : ℕ := clsCap
  set εR : ℝ≥0∞ := (Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z
  set τ := cwRevTau q ε
  set G : HonestTable × RE → Prop := fun t ↦
    r0G treeQ 18 t ∧ TrialHidGood (pubR (r0E t).1) (r0E t).2.1
  set g : RP → (HPos → Digest) × (RK × RW) → ℝ≥0∞ := fun p w ↦
    (if PermGood (permR p) 18 ∧ HwTrialOff (pubR p) (fun q ↦ w.1 (.inl q)) then
      cwDiagT A (pubR p) w.1 else 0) +
      N * revW m0R .instruments (r0Bk (permR p) (parR p) w.2.1)
        (realizeT w.1 (prefixT Selections cwUpd (pubR p) A)) initR
  have hQ : ∀ i : (recHwSpec X Z HPos Selections).Port, ¬ readRecPort Selections i = true →
      cwSet i = ∅ := fun i hi ↦ by
    rcases i with ((p | c) | c) | T
    · rfl
    · exact absurd rfl hi
    · rfl
    · rfl
  have hfg : ∀ t, G t → cwRecPre A t.1 ≤ g (r0E t).1 (r0E t).2 := fun t ht ↦ by
    obtain ⟨v, hv, hgeq⟩ := hpre_r0E cwUpd A hashesSlots_treeQ ht.1
    have hsg : SrcGood (pubR (r0E t).1) (fun q ↦ (r0E t).2.1 (.inl q)) := ht.1.2.2.2
    have hoff : HwTrialOff (pubR (r0E t).1) (fun q ↦ (r0E t).2.1 (.inl q)) :=
      hwTrialOff_of_trialHidGood ht.2 hsg
    have hπ : PermGood (permR (r0E t).1) 18 := by
      rw [permR_r0E]
      exact ht.1.2.1
    show cwRecPre A t.1 ≤ (if PermGood (permR (r0E t).1) 18 ∧
      HwTrialOff (pubR (r0E t).1) (fun q ↦ (r0E t).2.1 (.inl q)) then
      cwDiagT A (pubR (r0E t).1) (r0E t).2.1 else 0) + _
    rw [ite_eq_left ⟨hπ, hoff⟩]
    calc cwRecPre A t.1 = cwDiagT A (pubOf t.1) (valueAt t.1) :=
          (cwDiagT_eq _ _ _).symm
      _ = (runtimeR m0R).totalWeight .instruments (fun i ↦ diagMass (cwSet i))
          (realizeT v (prefixT Selections cwUpd (pubR (r0E t).1) A)) initR := by
          rw [cwDiagT, hgeq]
      _ ≤ _ := totalWeight_le_mismatch m0R .instruments
          (prefixT Selections cwUpd (pubR (r0E t).1) A)
          (disc_prefixT Selections cwUpd _ A ∅) (keepsLab_prefixT cwUpd _ A) initR
          initR_posSemidef (Hybrid.querySupportedOn_initR m0R _) _
          (Finset.disjoint_empty_left _) (fun i ↦ readRecPort Selections i = true) cwSet hQ hv
          (hN_readRec_prefixT hperm hsign _ v)
  have hrev : ∀ p (v : HPos → Digest), ∑ k : RK × RW, revW m0R .instruments
      (r0Bk (permR p) (parR p) k.1) (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR ≤
      Fintype.card (RK × RW) * (((2 * lifetime : ℕ) : ℝ≥0∞) * εR) := fun p v ↦
    (sum_revW_le m0R .instruments _ initR_posSemidef (fun k : RK × RW ↦ r0Bk (permR p) (parR p) k.1)
      rJ (fun k ↦ r0Bk_subset _ _ _) εR
      (fun s _ ↦ le_of_eq_of_le (card_filter_pad (W := RW)
        (fun k : RK ↦ s ∈ r0Bk (permR p) (parR p) k))
        ((mul_le_mul_of_nonneg_right (card_filter_r0Bk_le _ _ s) zero_le).trans_eq
          (by rw [mul_assoc, ← Nat.cast_mul, ← Fintype.card_prod])))
      (hR_prefixT hperm hsign _ v)).trans
      (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left ofReal_trace_initR_le_one
        zero_le).trans_eq (mul_one _)) zero_le)
  have hg : ∀ p, ∑ w, g p w ≤ (τ + N * (((2 * lifetime : ℕ) : ℝ≥0∞) * εR)) *
      Fintype.card ((HPos → Digest) × (RK × RW)) := fun p ↦ by
    have hv : ∑ v : HPos → Digest, (if PermGood (permR p) 18 ∧
        HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then cwDiagT A (pubR p) v else 0) ≤
        τ * Fintype.card (HPos → Digest) := by
      by_cases hπ : PermGood (permR p) 18
      · refine le_of_eq_of_le (Finset.sum_congr rfl fun v _ ↦ ?_)
          (sum_cwRecT_good_le hperm hsign hre p hπ)
        rw [cwDiagT_eq]
        exact if_congr (and_iff_right hπ) rfl rfl
      · exact (Finset.sum_eq_zero fun v _ ↦ ite_eq_right fun h ↦ hπ h.1).trans_le zero_le
    rw [Fintype.sum_prod_type]
    calc ∑ v : HPos → Digest, ∑ k : RK × RW, g p (v, k)
        = ∑ v : HPos → Digest, (Fintype.card (RK × RW) *
            (if PermGood (permR p) 18 ∧ HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then
              cwDiagT A (pubR p) v else 0) +
            N * ∑ k : RK × RW, revW m0R .instruments (r0Bk (permR p) (parR p) k.1)
              (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR) := by
          refine Finset.sum_congr rfl fun v _ ↦ ?_
          dsimp only [g]
          exact sum_const_add_mul_eq
            (if PermGood (permR p) 18 ∧ HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then
              cwDiagT A (pubR p) v else 0) N
            (fun k : RK × RW ↦ revW m0R .instruments (r0Bk (permR p) (parR p) k.1)
              (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR)
      _ ≤ ∑ v : HPos → Digest, (Fintype.card (RK × RW) *
            (if PermGood (permR p) 18 ∧ HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then
              cwDiagT A (pubR p) v else 0) +
            N * (Fintype.card (RK × RW) * (((2 * lifetime : ℕ) : ℝ≥0∞) * εR))) :=
          Finset.sum_le_sum fun v _ ↦ add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (hrev p v) zero_le)
      _ = Fintype.card (RK × RW) * ∑ v : HPos → Digest,
            (if PermGood (permR p) 18 ∧ HwTrialOff (pubR p) (fun q ↦ v (.inl q)) then
              cwDiagT A (pubR p) v else 0) +
            Fintype.card (HPos → Digest) *
              (N * (Fintype.card (RK × RW) * (((2 * lifetime : ℕ) : ℝ≥0∞) * εR))) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
      _ ≤ Fintype.card (RK × RW) * (τ * Fintype.card (HPos → Digest)) +
            Fintype.card (HPos → Digest) *
              (N * (Fintype.card (RK × RW) * (((2 * lifetime : ℕ) : ℝ≥0∞) * εR))) :=
          add_le_add (mul_le_mul_of_nonneg_left hv zero_le) le_rfl
      _ = (τ + N * (((2 * lifetime : ℕ) : ℝ≥0∞) * εR)) *
            Fintype.card ((HPos → Digest) × (RK × RW)) := by
          rw [Fintype.card_prod (HPos → Digest) (RK × RW),
            Nat.cast_mul (Fintype.card (HPos → Digest))]
          exact cards_add_mul_eq _ _ _ _ _
  have h := uavg_le_of_injOn r0E G ((r0E_injOn treeQ 18).mono fun _ h ↦ h.1) card_r0E_le
    (cwRecPre A) g hfg (clsCap : ℝ≥0∞) (fun t _ ↦ cwRecPre_le_clsCap hperm hsign t.1) _ hg
  have hfrac : (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
      (Finset.univ.filter fun t ↦ ¬G t).card ≤
      ENNReal.ofReal (1 / 2 ^ 174) + ENNReal.ofReal (1 / 2 ^ 400) := by
    have hc := card_filter_le_add_of_imp (fun t ↦ ¬G t) (fun t ↦ ¬r0G treeQ 18 t)
      (fun t ↦ r0G treeQ 18 t ∧ ¬TrialHidGood (pubR (r0E t).1) (r0E t).2.1) fun t ht ↦ by
        by_cases h1 : r0G treeQ 18 t
        · exact Or.inr ⟨h1, fun h2 ↦ ht ⟨h1, h2⟩⟩
        · exact Or.inl h1
    calc (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬G t).card
        ≤ (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
            (((Finset.univ.filter fun t ↦ ¬r0G treeQ 18 t).card : ℝ≥0∞) +
              (Finset.univ.filter fun t ↦
                r0G treeQ 18 t ∧ ¬TrialHidGood (pubR (r0E t).1) (r0E t).2.1).card) := by
          gcongr
          exact_mod_cast hc
      _ = _ := mul_add _ _ _
      _ ≤ _ := add_le_add r0G_frac_le_keccak trialHidGood_r0G_frac_le_keccak
  refine h.trans ?_
  calc τ + N * (((2 * lifetime : ℕ) : ℝ≥0∞) * εR) + (clsCap : ℝ≥0∞) *
        ((Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬G t).card)
      ≤ τ + N * ENNReal.ofReal (1 / 2 ^ 190) +
          (clsCap : ℝ≥0∞) * (ENNReal.ofReal (1 / 2 ^ 174) + ENNReal.ofReal (1 / 2 ^ 400)) :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left revTerm_le_keccak zero_le))
          (mul_le_mul_of_nonneg_left hfrac zero_le)
    _ = _ := by
        unfold cwJunk
        ring

end avgGood

end Quantum.Xmss.Assembly

end
