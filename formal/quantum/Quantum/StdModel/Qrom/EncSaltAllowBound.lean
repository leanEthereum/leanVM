module

public import Quantum.StdModel.Qrom.EncSalt
public import Quantum.StdModel.Qrom.EncSaltAllow

@[expose] public section

/-!
# EncTCR$ in the QROM with allowed classical calls

EncSalt's `probAvg_game_slRed_le_moded_budget` and `probAvg_encTcrSalt_le` ask the reduction's
handler to keep its invariant on every classical call. Here, as in `modedP_mixGame_allow`, the
invariant is also indexed by `g`, the handler's step is required only on the calls allowed by
`g` (the index moving to `nxt g q`), and the adversary makes only allowed calls
(`CallsIn ok nxt g₀`).

* `probAvg_game_slRed_le_moded_budget_allow`: the graded bound with a live budget and additive
  costs, `((n + nB) √η + √(∑ d))²`.
* `probAvg_encTcrSalt_le_allow`: EncTCR$, `((q + k₁ + k₂ + 2) √(gradeEta F) + √TW)²`.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom.EncSalt

open Quantum QuantumRuntime Quantum.Sponge Quantum.Qrom HashSig Props
open Quantum.Xmss.Assembly (ModedP)
open Quantum.Xmss.Hybrid (runtime2)
open Tcr (Mem BadR)

section assembly

open OracleComp OracleSpec

variable {Sx M' : Type} [Fintype Sx] [DecidableEq Sx] [Fintype M'] [DecidableEq M']

open scoped Classical in
/-- **The property game of a straight-line reduction, graded with a live budget and additive
costs, with allowed calls**: as `probAvg_game_slRed_le_moded_budget`, with the handler's
invariant `J` also indexed by `g`, its step `hσ` required only on calls allowed by `g`, for an
adversary making only allowed calls from `g₀`. -/
theorem probAvg_game_slRed_le_moded_budget_allow {Q : Type} {R : OracleSpec.{0, 0} Q}
    {Q' : Type} {R' : OracleSpec.{0, 0} Q'} {St Pub Out : Type}
    (E : Experiment romWorld R' Pub Out)
    {S0 F : Type} (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out)
    (upd : Caller → HashDomain → Finset Sx × M' → Option HashOutput → Finset Sx × M')
    (rl : Finset Sx × M' → HashDomain → Option HashOutput)
    (hrec : ∀ c z, RecordsAt rl z (upd c z)) (m₀ : Finset Sx × M') (hrl : ∀ z, rl m₀ z = none)
    {Gx : Type} (ok : Gx → Q → Prop) (nxt : Gx → Q → Gx) (g₀ : Gx)
    (hcalls : ∀ s a, CallsIn ok nxt g₀ (adv (E.pub s) a))
    (I0 : E.State → Option (Finset Sx × M') → Prop)
    (h0 : ∀ s μ, LiveRun rl (upd .setup) E.setup (some m₀) s μ → I0 s μ)
    (J : E.State → S0 → Gx → St × QueryLog R' → Option (Finset Sx × M') → Prop)
    (hpre : ∀ s μ, I0 s μ → ∀ a μ', LiveRedRun rl upd (E.answer s) (pre (E.pub s)) [] μ a μ' →
      J s a.1 g₀ (st0 (E.pub s) a.1, a.2) μ')
    (hσ : ∀ s a g st log μ q, ok g q → J s a g (st, log) μ → ∀ r μ',
      LiveRedRun rl upd (E.answer s) (σ (E.pub s) st q) log μ r μ' →
        J s a (nxt g q) (r.1.2, r.2) μ')
    (Ipost : E.State → Out × QueryLog R' → Option (Finset Sx × M') → Prop)
    (hpost : ∀ s a f g st log μ, J s a g (st, log) μ → ∀ r μ',
      LiveRedRun rl upd (E.answer s) (post (E.pub s) a f st) log μ r μ' → Ipost s r μ')
    (Won : Set (Finset Sx × M')) (β : Finset Sx × M' → ℕ) (nB : ℕ)
    (hjudge : ∀ s r μ, Ipost s r μ → ∀ b μ', LiveRun rl (upd .judge) (E.judge s r.2 r.1) μ b μ' →
      ∀ m, μ' = some m → β m ≤ nB ∧ (b = true → m ∈ Won))
    (S : Set (RomReg HashDomain HashOutput (Finset Sx × M'))) [DecidablePred (· ∈ S)]
    (hE : ∀ s : RomReg HashDomain HashOutput (Finset Sx × M'), s.2.2 ∈ Won → s ∈ S)
    (hS0 : potential (hwProjector S) (rhoMem0 m₀) = 0)
    (Inv : Finset Sx × M' → Prop) (hInv0 : Inv m₀)
    (hInv : ∀ m i r m', OkD rl (some m) i → PolicyPort upd i → Inv m →
      nxD rl (some m) i r = some m' → Inv m')
    (κ : (hwSpec HashOutput HashDomain (Finset Sx × M')).Port → ℕ)
    (κB : Finset Sx × M' → (hwSpec HashOutput HashDomain (Finset Sx × M')).Port → ℕ)
    (hβ : ∀ m i r m', OkD rl (some m) i → PolicyPort upd i →
      nxD rl (some m) i r = some m' → κB m i + β m ≤ β m')
    (η : ℝ≥0∞)
    (d : ∀ i, Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
      RomReg HashDomain HashOutput (Finset Sx × M'))
      ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
        RomReg HashDomain HashOutput (Finset Sx × M')) ℂ → ℝ≥0∞)
    (hη : ∀ m i (τ : Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
        RomReg HashDomain HashOutput (Finset Sx × M'))
        ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
          RomReg HashDomain HashOutput (Finset Sx × M')) ℂ),
      OkD rl (some m) i → PolicyPort upd i → Inv m → τ.PosSemidef → DSupp rl id (some m) τ →
      ∑' r, (if nxD rl (some m) i r = none ∨ ∃ m', nxD rl (some m) i r = some m' ∧ nB < β m'
          then 0 else
          potential (hwProjector S) (((runtime2 HashOutput HashDomain m₀).step i).branch r τ)) ≤
        (potential (hwProjector S) τ ^ (2⁻¹ : ℝ) +
          (κ i * (η * ENNReal.ofReal τ.trace.re) ^ (2⁻¹ : ℝ) +
            κB m i * (η * ENNReal.ofReal τ.trace.re) ^ (2⁻¹ : ℝ))) ^ 2 + d i τ)
    {n : ℕ} (hn : IFreeM.IsChargeBound (readProgOf upd (mixGame E pre adv st0 σ post))
      (portCharge κ) n) :
    romWorld.probAvg (E.game fun p ↦ slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (((n : ℝ≥0∞) + nB) * η ^ (2⁻¹ : ℝ) + ((runtime2 HashOutput HashDomain m₀).totalWeight
        .instruments d (readProgOf upd (mixGame E pre adv st0 σ post)) (rhoMem0 m₀)) ^
          (2⁻¹ : ℝ)) ^ 2 := by
  set x := readProgOf upd (mixGame E pre adv st0 σ post)
  set fin : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → Option (Finset Sx × M') → Prop :=
    fun p μ ↦ μ = none ∨ ∀ m, μ = some m → β m ≤ nB ∧ (p.2.2 = true → m ∈ Won)
  have hmix := modedP_mixGame_allow upd rl E pre adv st0 σ post m₀ ok nxt g₀ hcalls I0 h0 J hpre
    hσ Ipost hpost
    (fun b μ ↦ μ = none ∨ ∀ m, μ = some m → β m ≤ nB ∧ (b = true → m ∈ Won))
    (fun s r μ hI b μ' hr ↦ Or.inr (hjudge s r μ hI b μ' hr))
  have hx : ModedP (fun μ i ↦ OkD rl μ i ∧ (μ ≠ none → PolicyPort upd i)) (nxD rl) fin
      (some m₀) x :=
    modedP_toReads_policy upd rl hrec (fun _ ↦ Or.inl rfl) _ _ hmix
  have hρ : (rhoMem0 m₀).PosSemidef :=
    ((SubState.basis ()).prod (runtime2 HashOutput HashDomain m₀).init).posSemidef
  have htr : ENNReal.ofReal (rhoMem0 m₀).trace.re ≤ 1 := by
    change ENNReal.ofReal ((SubState.basis ()).matrix ⊗ₖ
      (runtime2 HashOutput HashDomain m₀).init.matrix).trace.re ≤ 1
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr
      ((SubState.basis ()).prod (runtime2 HashOutput HashDomain m₀).init).trace_re_le_one
  have hwin := evalDistMap_le_eventWeight_moded (X := HashOutput) (Z := HashDomain) rl id m₀ hrl
    (fun _ _ h ↦ h.1) (fun _ _ _ _ ↦ rfl) S Won hE x (some m₀) rfl hx
    (fun p μ h hp m hm ↦ by
      rcases h with h | h
      · rw [h] at hm
        cases hm
      · exact (h m hm).2 hp)
  set doom : Option (Finset Sx × M') → Prop :=
    fun μ ↦ μ = none ∨ ∃ m', μ = some m' ∧ nB < β m' with hdoom
  set bud : Option (Finset Sx × M') → ℕ := fun μ ↦ μ.elim 0 fun m ↦ nB - β m
  set κB' : Option (Finset Sx × M') → (hwSpec HashOutput HashDomain (Finset Sx × M')).Port →
    ℕ := fun μ i ↦ μ.elim 0 fun m ↦ κB m i
  set CInv : Option (Finset Sx × M') → Set (RomReg HashDomain HashOutput (Finset Sx × M')) :=
    fun μ ↦ {_s | ∀ m, μ = some m → Inv m}
  have hsq := rpow_inv_two_tsum_potential_runtime2_moded_add (rl := rl) (proj := id) m₀
    (ok := fun μ i ↦ OkD rl μ i ∧ (μ ≠ none → PolicyPort upd i)) (nx := nxD rl)
    (fun _ _ h ↦ h.1) (fun _ _ _ _ ↦ rfl) S doom
    (fun μ i r hi h ↦ by
      rcases h with h | ⟨m', rfl, hm'⟩
      · rw [h]
        exact Or.inl rfl
      · rcases hnx : nxD rl (some m') i r with _ | m''
        · exact Or.inl rfl
        · exact Or.inr ⟨m'', rfl, lt_of_lt_of_le hm'
            ((Nat.le_add_left _ _).trans (hβ m' i r m'' hi.1 (hi.2 (by simp)) hnx))⟩)
    κ κB' bud
    (fun μ i r hi hnd ↦ by
      rcases μ with _ | m
      · exact absurd (Or.inl rfl) hnd
      rcases hnx : nxD rl (some m) i r with _ | m'
      · exact absurd (Or.inl hnx) hnd
      have hb := hβ m i r m' hi.1 (hi.2 (by simp)) hnx
      have hm' : β m' ≤ nB := not_lt.mp fun h ↦ hnd (Or.inr ⟨m', hnx, h⟩)
      change κB m i + (nB - β m') ≤ nB - β m
      omega)
    η η CInv
    (fun μ i r τ hi hτ ↦ by
      by_cases hI : ∀ m, μ = some m → Inv m
      · have hI' : ∀ m', nxD rl μ i r = some m' → Inv m' := by
          intro m' hm'
          rcases μ with _ | m
          · cases hm'
          · exact hInv m i r m' hi.1 (hi.2 (by simp)) (hI m rfl) hm'
        exact fun _ _ _ ↦ ⟨hI', hI'⟩
      · have h0 : τ = 0 := by
          ext a b
          by_contra hab
          exact hI (hτ a b hab).1
        subst h0
        rw [map_zero]
        exact fun a b hab ↦ absurd (Matrix.zero_apply a b) hab)
    d
    (fun μ i τ hi hd hτ hs hc ↦ by
      rcases μ with _ | m
      · exact absurd (Or.inl rfl) hd
      · by_cases hIm : Inv m
        · refine le_trans (le_of_eq (tsum_congr fun r ↦ ?_))
            (hη m i τ hi.1 (hi.2 (by simp)) hIm hτ hs)
          split_ifs <;> rfl
        · have h0 : τ = 0 := by
            ext a b
            by_contra hab
            exact hIm ((hc a b hab).1 m rfl)
          subst h0
          refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun r ↦ ?_)) zero_le
          split_ifs
          · rfl
          · rw [map_zero]
            simp [potential])
    (fun p μ h hd ↦ by
      rcases hd with hd | ⟨m', rfl, hm'⟩
      · exact hd
      · rcases h with h | h
        · exact absurd h (by simp)
        · exact absurd (h m' rfl).1 (not_le.mpr hm'))
    .instruments x n hn (some m₀) hx hρ (dInv_init rl m₀ hrl _) (fun _ _ _ ↦ ⟨fun m hm ↦ by
      cases hm
      exact hInv0, fun m hm ↦ by cases hm; exact hInv0⟩)
  simp only [hS0, zero_add] at hsq
  refine (probAvg_game_slRed_le_hw E pre adv st0 σ post upd m₀).trans (hwin.trans ?_)
  refine (le_of_eq (eventWeight_eq_tsum_potential (runtime2 HashOutput HashDomain m₀)
    .instruments (hwProjector S) x (rhoMem0 m₀))).trans ?_
  refine (le_of_eq (sq_rpow_inv_two _).symm).trans ?_
  refine pow_le_pow_left₀ zero_le (hsq.trans ?_) 2
  have hη1 : (η * ENNReal.ofReal (rhoMem0 m₀).trace.re) ^ (2⁻¹ : ℝ) ≤ η ^ (2⁻¹ : ℝ) := by
    gcongr
    calc η * ENNReal.ofReal (rhoMem0 m₀).trace.re ≤ η * 1 := by gcongr
      _ = η := mul_one η
  have hb : (bud (some m₀) : ℝ≥0∞) ≤ nB := by
    exact_mod_cast Nat.sub_le nB (β m₀)
  rw [add_mul]
  gcongr

end assembly

section main

open OracleComp OracleSpec
open Tcr (GSep rl liveRun_bind liveRun_pure liveRun_hashQ liveRun_noHash hashW)

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

open scoped Classical in
/-- **EncTCR$ against a straight-line reduction, with a live budget and allowed calls**: as
`probAvg_encTcrSalt_le`, with the reduction's invariant `Ju` also indexed by `g`, the handler's
step `hσU` required only on calls allowed by `g` (the index moving to `nxt g qq`), for an
adversary making only allowed calls from `g₀`:
`probAvg ≤ ((q + k₁ + k₂ + 2) √(gradeEta F) + √TW)²`. -/
theorem probAvg_encTcrSalt_le_allow [SampleableType Par] [SampleableType Salt]
    (hs : GSep e.hash G)
    (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 Fo : Type}
    (pre : Par → OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) S0)
    (adv : Par → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : Par → S0 → St) (σ : Par → HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (post : Par → S0 → Fo → St →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) (Tw × Msg × Salt))
    {q : ℕ} (hadv : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge hashCharge) q)
    {Gx : Type} (ok : Gx → Q → Prop) (nxt : Gx → Q → Gx) (g₀ : Gx)
    (hcalls : ∀ P a, CallsIn ok nxt g₀ (adv P a))
    (k₁ k₂ : ℕ) (Ju : Par → S0 → Gx → St × SLog Tw Msg Salt Dig → Option Mem → Prop)
    (hpreU : ∀ P a μ', LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (pre P) []
      (some mem0) a μ' → Ju P a.1 g₀ (st0 P a.1, a.2) μ' ∧ ∀ m', μ' = some m' → βS e m' ≤ k₁)
    (hσU : ∀ P a g st log μ qq, ok g qq → LiveInv e P log μ → Ju P a g (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (σ P st qq) log μ r μ' →
        Ju P a (nxt g qq) (r.1.2, r.2) μ' ∧
          ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m)
    (hpostU : ∀ P a f g st log μ, LiveInv e P log μ → Ju P a g (st, log) μ → ∀ r μ',
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) (post P a f st) log μ r μ' →
        ∀ m m', μ = some m → μ' = some m' → βS e m' ≤ βS e m + k₂) :
    romWorld.probAvg ((encTcrSalt romWorld e).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (((q : ℝ≥0∞) + (k₁ + k₂ + 2 : ℕ)) * ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ) +
        (runtime2 HashOutput HashDomain mem0).totalWeight .instruments (dS e)
          (saltProg e pre adv st0 σ post) (rhoMem0 mem0) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hinv : ∀ (P : Par) {α : Type} (oa : OracleComp (romWorld.Oracles +
      (Tw × Msg →ₒ Option (Salt × Dig))) α) log μ r μ', LiveInv e P log μ →
      LiveRedRun rl (upd e) ((encTcrSalt romWorld e).answer P) oa log μ r μ' →
        LiveInv e P r.2 μ' := fun P _ oa ↦
    liveRedRun_inv _ (LiveInv e P) (fun _ _ _ _ _ hI h ↦ liveInv_red hI h)
      (fun _ _ q' _ _ hI h ↦ liveInv_answer hs hlen q' hI h) oa
  refine probAvg_game_slRed_le_moded_budget_allow (encTcrSalt romWorld e) pre adv st0 σ post
    (upd e) rl (recordsAt_upd e) mem0 (fun _ ↦ rfl) ok nxt g₀ (fun _ a ↦ hcalls _ a)
    (fun _ μ ↦ μ = some mem0) (fun _ μ h ↦ ?_)
    (fun P a g s μ ↦ LiveInv e P s.2 μ ∧ Ju P a g s μ ∧ ∀ m, μ = some m → βS e m ≤ k₁)
    (fun P μ hμ a μ' h ↦ ?_) (fun P a g st log μ qq hq hJ r μ' h ↦ ?_)
    (fun P r μ ↦ LiveInv e P r.2 μ ∧ ∀ m, μ = some m → βS e m ≤ k₁ + k₂)
    (fun P a f g st log μ hJ r μ' h ↦ ?_) (Tcr.Won e.hash G) (βS e) (k₁ + k₂ + 2)
    (fun P r μ hI b μ' h m hm ↦ ?_) (BadR e.hash G)
    (fun s hs' ↦ by
      obtain ⟨z, y, h1, h2⟩ := hs'
      exact Or.inr ⟨z, y, h1, h2⟩)
    (Tcr.potential_init_badR (C := e.hash) (G := G) mem0 fun _ ↦ rfl) InvS
    (fun _ h ↦ absurd h Bool.false_ne_true) (fun _ _ _ _ _ hp hI h ↦ invS_step hp hI h) κA (κB e)
    (fun _ _ _ _ _ hp h ↦ κB_add_βS_le hp h) (ENNReal.ofReal (gradeEta HashOutput F)) (dS e)
    (fun m i τ hi _ hI hτ hsupp ↦ (ENNReal.tsum_le_tsum fun r ↦ by
      split_ifs
      · exact zero_le
      · exact le_rfl).trans (tsum_potential_step_salt hF mem0 m i τ hi hI hτ hsupp))
    (isChargeBound_toReads (upd e)
      (isChargeBound_mixGame (encTcrSalt romWorld e) pre adv st0 σ post hadv))
  · exact liveRun_noHash _ (Common.isWeightBound_liftM_probComp hashW (fun _ ↦ rfl) _) h
  · subst hμ
    obtain ⟨hJu, hβ⟩ := hpreU P a μ' h
    exact ⟨hinv P _ [] _ a μ' (liveInv_mem0 P) h, hJu, hβ⟩
  · obtain ⟨hI, hJu, hβ⟩ := hJ
    obtain ⟨hJu', hβ'⟩ := hσU P a g st log μ qq hq hI hJu r μ' h
    refine ⟨hinv P _ log μ r μ' hI h, hJu', fun m' hm' ↦ ?_⟩
    rcases μ with _ | m
    · rw [liveRedRun_none _ _ h] at hm'
      cases hm'
    · exact (hβ' m m' rfl hm').trans (hβ m rfl)
  · obtain ⟨hI, hJu, hβ⟩ := hJ
    refine ⟨hinv P _ log μ r μ' hI h, fun m' hm' ↦ ?_⟩
    rcases μ with _ | m
    · rw [liveRedRun_none _ _ h] at hm'
      cases hm'
    · have := hpostU P a f g st log _ hI hJu r μ' h m m' rfl hm'
      have := hβ m rfl
      omega
  · obtain ⟨hI, hβ⟩ := hI
    rcases μ with _ | m₁
    · rw [liveRun_none _ h] at hm
      cases hm
    refine ⟨?_, fun hb ↦ ?_⟩
    · have := βS_judge_le hlen r.1 h rfl hm
      have := hβ m₁ rfl
      omega
    · subst hb
      exact won_of_judge hs hinj hlen r.1 hI h m hm

end main

end Quantum.StdModel.Qrom.EncSalt

end
