module

public import Quantum.Qrom.Xmss.Multi.GameTFacts
public import Quantum.Qrom.Xmss.Multi.GameTCalls
public import Quantum.Qrom.Xmss.Hybrid
public import Quantum.Xmss.Hybrid.GradedMasked

@[expose] public section

/-!
# The hidden-value hybrid of multi-user leanXMSS in the QROM (runtime 1 against runtime 2)

The `n`-user analog of `Quantum.Qrom.Xmss.Hybrid`. The multi-user QROM game is at most the bad
fraction of tables plus runtime 1 on the realized template over good tables, averaged over the
hidden values `θ : HPosN n → Digest` (`muWinProb_le_uavg_goodN`). The graded hybrid, masked by the
good set `GoodN` on both runtimes (`uavg_mask_win_runtime1R_le_graded`), compares it with runtime 2.

* **Sources** (`cellSrcN`, `srcValsN`, `sourcesQN`): a hidden cell of user `i` at a position `p`
  names the coordinates `(j, srcOf p)` of all users `j`; user `j`'s values are the single-user
  ones (`srcVals`) when no other user can make the cell a cell of its own by changing that
  coordinate, else none. So at most one user contributes (`srcValsN_eq_empty`), and the mass per
  call is `2^-128` (`kappaQ`), as for one user. On `GoodN` the owner contributes
  (`srcVals_eq_empty_of_goodN`): prefixed cells carry their user's distinct public parameter, the
  master seed's and the parameter derivation's cells the high half of the user's master seed and
  scheme seed, distinct by `HiDistinct`. The masses are asked only on `GoodN` (`maskHidN`).
* **Masses** (`uavg_mask_spongeMass_leN`, `uavg_mask_readMass_leN`): `q · 2^-128` at the sponge
  calls, `verifyCalls · 2^-128` at the reads (the trials read message digests, no table cells).
* **The collision term** (`uavg_not_goodN_le`): `GoodN` fails with probability at most
  `3 C(n,2) 2^-128` (`collTermN`); the table's bad fraction is inside it.
* **The hybrid** (`sqrt_win_runtime1_le_qromN`, `muWinProb_le_hybridN`):
  `muWinProb ≤ collTermN n + (√(E[1_GoodN p2QN]) + hybTermQ q)²`.
-/

open Matrix IPFunctor MeasureTheory
open scoped ENNReal Kronecker ComplexOrder

universe u v w

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT runtime1R extCls Sources
  sum_totalWeight_portMass_runtimeR_le_inv)
open Quantum.Qrom.SufCma.Multi (muGame muWinProb muWinProb_eq_uniform cmdCharge hashCharge
  signCharge)
open Quantum.Qrom.MultiUser (uavg_restrict_injective uavg_not_injective_le)

/-! ## The masked graded hybrid with a masked runtime 2 -/

section masked

variable {Θ : Type*} [Fintype Θ]
  {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ]

/-- **Runtime 1 against `runtimeR` on a good set**: if the averaged hidden masses over the good set
`G` are at most `μ` (sponge ports) and `ν` (read ports), then `E[1_G P₁] ≤ (√(E[1_G P₂]) +
√(4 q μ) + √ν)²`. -/
theorem uavg_mask_win_runtime1R_le_graded (L : Θ → Hw X Z)
    (Hhθ : Θ → Set Z) (Hkθ Hk'θ : Θ → Set X) (hL : ∀ θ, Covers (L θ) (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (m₀ : Finset S × M') (x : Θ → QuantumComp Λ (recHwSpec X Z S M') Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) (q : ℕ)
    (hq : ∀ θ, IFreeM.IsChargeBound (x θ) (portCharge fun i ↦
      if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (G : Θ → Prop) [DecidablePred G] (μ ν : ℝ≥0∞)
    (hμ : uavg (fun θ ↦ if G θ then (runtimeR m₀).totalWeight I
      (spongeMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
        ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ μ)
    (hν : uavg (fun θ ↦ if G θ then (runtimeR m₀).totalWeight I
      (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
        ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ ν) :
    uavg (fun θ ↦ if G θ then
        (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E else 0) ≤
      (uavg (fun θ ↦ if G θ then (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E else 0) ^
        (2⁻¹ : ℝ) + (4 * (q * μ)) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)) ^ 2 := by
  set P₁ : Θ → ℝ≥0∞ := fun θ ↦ (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E
    with hP₁
  set P₂ : Θ → ℝ≥0∞ := fun θ ↦ (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E with hP₂
  set T : Θ → ℝ≥0∞ := fun θ ↦ (runtimeR m₀).totalWeight I (spongeMass (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (x θ) ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) with hT
  set V : Θ → ℝ≥0∞ := fun θ ↦ (runtimeR m₀).totalWeight I (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (x θ) ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) with hV
  have h0 : (0 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  have hz : ∀ (c : ℝ≥0∞), ∑' n : ℕ, (4 * if n = 0 then c else 0) ^ (2⁻¹ : ℝ) =
      (4 * c) ^ (2⁻¹ : ℝ) := fun c ↦ by
    rw [tsum_eq_single 0 fun n hn ↦ by simp [hn, h0]]
    simp
  have hθ : ∀ θ, P₁ θ ^ (2⁻¹ : ℝ) ≤ P₂ θ ^ (2⁻¹ : ℝ) +
      ∑' n : ℕ, (4 * if n = 0 then (q : ℝ≥0∞) * T θ else 0) ^ (2⁻¹ : ℝ) + V θ ^ (2⁻¹ : ℝ) := by
    intro θ
    rw [hz]
    refine (sqrt_win_runtime1R_le_graded I (L θ) m₀ (hL θ) (x θ) (ρ θ) (f θ) hE).trans
      (add_le_add (add_le_add le_rfl ((tsum_rpow_kindWeight_le (runtimeR m₀) I _ (x θ) (hq θ)
        _ 4).trans_eq ?_)) le_rfl)
    simp only [hT, spongeMass_eq]
    rw [mul_left_comm]
    rfl
  have hm : ∀ θ, (if G θ then P₁ θ else 0) ^ (2⁻¹ : ℝ) ≤ (if G θ then P₂ θ else 0) ^ (2⁻¹ : ℝ) +
      ∑' n : ℕ, (4 * (fun θ n ↦ if n = 0 then (q : ℝ≥0∞) * (if G θ then T θ else 0) else 0) θ n) ^
        (2⁻¹ : ℝ) + (if G θ then V θ else 0) ^ (2⁻¹ : ℝ) := by
    intro θ
    by_cases hG : G θ
    · simp only [hG, ↓reduceIte]
      exact hθ θ
    · simp only [hG, ↓reduceIte, h0]
      exact zero_le
  have h1 := uavg_le_of_hybrid_graded _ _ _ _ hm
  have hu : ∀ n : ℕ, uavg (fun θ ↦ if n = 0 then (q : ℝ≥0∞) * (if G θ then T θ else 0) else 0) =
      if n = 0 then (q : ℝ≥0∞) * uavg (fun θ ↦ if G θ then T θ else 0) else 0 := fun n ↦ by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte, uavg_const_mul]
    · simp [hn, uavg]
  simp only [hu, hz] at h1
  refine h1.trans (pow_le_pow_left₀ zero_le (add_le_add (add_le_add le_rfl ?_) ?_) 2)
  · exact ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμ zero_le)
      zero_le) (by norm_num)
  · exact ENNReal.rpow_le_rpow hν (by norm_num)

end masked

variable {n : ℕ}

/-! ## The hidden cells -/

section cells

/-- **The hidden cells at `θ`**: the cells of all users' tables. -/
def hidCellsN (θ : HPosN n → Digest) : Set HashDomain :=
  {z | ∃ i p, cellOf (seedsOf θ i) p (tabOf (userOf θ i)) = z}

/-- Runtime 1's hardwired cells at `θ`: the table of the users' master seeds and values. -/
noncomputable def tableHwN (θ : HPosN n → Digest) : Hw HashOutput HashDomain :=
  (tableN (seedsOf θ)).hwOf (tabOfN θ)

theorem covers_tableHwN (θ : HPosN n → Digest) : Covers (tableHwN θ) (hidCellsN θ) ∅ ∅ := by
  refine ⟨fun z hz ↦ ?_, fun _ hx ↦ absurd rfl hx, fun _ hx ↦ absurd rfl hx⟩
  by_contra h
  exact hz ((tableN (seedsOf θ)).tableDb_of_forall_ne fun a ha ↦ h ⟨a.1, a.2, ha⟩)

/-- No hidden cell is a message digest. -/
theorem isMsgCell_of_mem_hidCellsN {θ : HPosN n → Digest} {z : HashDomain}
    (hz : z ∈ hidCellsN θ) : isMsgCell z = false := by
  obtain ⟨i, p, rfl⟩ := hz
  rw [isMsgCell, slotOf_cellOf]
  cases p <;> rfl

end cells

/-! ## The good set -/

section good

/-- **The high halves** of the users' master seeds and scheme seeds are pairwise distinct. -/
def HiDistinct (θ : HPosN n → Digest) : Prop :=
  Function.Injective (fun i ↦ θ (i, (none, true))) ∧ Function.Injective (fun i ↦ θ (i, hiC .seed))

/-- **The mask of the hybrid**: a good table and distinct high seed halves. -/
def GoodN (θ : HPosN n → Digest) : Prop :=
  (tableN (seedsOf θ)).good (tabOfN θ) ∧ HiDistinct θ

noncomputable instance instDecidablePredGoodN : DecidablePred (GoodN (n := n)) :=
  Classical.decPred _

/-- **The collision term**: `3 C(n,2) 2^-128`. -/
noncomputable def collTermN (n : ℕ) : ℝ≥0∞ :=
  3 * n.choose 2 * (2 ^ 128 : ℝ≥0∞)⁻¹

theorem userOf_update_self (θ : HPosN n → Digest) (i : Fin n) (t : HPos) (d : Digest) :
    userOf (Function.update θ (i, t) d) i = Function.update (userOf θ i) t d := by
  funext s
  simp only [userOf, Function.update_apply, Prod.mk.injEq, true_and]

theorem userOf_update_of_ne (θ : HPosN n → Digest) {i j : Fin n} (h : j ≠ i) (t : HPos)
    (d : Digest) : userOf (Function.update θ (i, t) d) j = userOf θ j :=
  funext fun _ ↦ Function.update_of_ne (fun he ↦ h (Prod.mk.inj he).1) _ _

/-- The high half of a master seed of hidden values. -/
theorem upperHalfOfHash_seedOf (θ : HPos → Digest) :
    upperHalfOfHash (seedOf θ) = θ (none, true) :=
  upperHalfOfHash_joinHalves _ _

/-- The high half of a scheme seed of hidden values. -/
theorem upperHalfOfHash_seed_tabOf (θ : HPos → Digest) :
    upperHalfOfHash (tabOf θ).seed = θ (hiC .seed) :=
  upperHalfOfHash_joinHalves _ _

/-- **On `GoodN` no other user makes a cell its own** by changing its value at the cell's source
coordinate. -/
theorem srcVals_eq_empty_of_goodN {θ : HPosN n → Digest} (hG : GoodN θ) (i j : Fin n)
    (hji : j ≠ i) (p : Pos) :
    srcVals (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) (srcOf p) (userOf θ j) = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun d hd ↦ ?_
  simp only [srcVals, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  obtain ⟨p', hs', hc⟩ := hd
  set θj := Function.update (userOf θ j) (srcOf p) d with hθj
  have hsl : some p'.slot = some p.slot :=
    (slotOf_cellOf _ _ p').symm.trans ((congrArg slotOf hc).trans (slotOf_cellOf _ _ p))
  have hsl' : p'.slot = p.slot := Option.some.inj hsl
  have hgood : goodN (seedsOf θ) (tabOfN θ) := hG.1
  by_cases h1 : p = .seed
  · subst h1
    have hp' : p' = .seed := Pos.eq_seed_of_slot hsl'
    subst hp'
    have hc' : cell (tabOf (userOf θ i)).param Quantum.Xmss.Slot.seed (seedOf θj) =
        cell (tabOf (userOf θ i)).param Quantum.Xmss.Slot.seed (seedsOf θ i) :=
      (cell_seed_eq _ _ _).trans hc
    have hsig := cell_injective _ (addressable_slot .seed) (addressable_slot .seed) hc'
    have hpay : seedOf θj = seedsOf θ i := eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
    have hu := congrArg upperHalfOfHash hpay
    rw [upperHalfOfHash_seedOf, seedsOf, upperHalfOfHash_seedOf, hθj,
      Function.update_of_ne (show ((none, true) : HPos) ≠ srcOf Pos.seed by
        rw [show srcOf Pos.seed = (none, false) from rfl]; simp)] at hu
    exact hji (hG.2.1 hu)
  by_cases h2 : p = .param
  · subst h2
    have hp' : p' = .param := Pos.eq_param_of_slot hsl'
    subst hp'
    have hc' : cell (tabOf (userOf θ i)).param Quantum.Xmss.Slot.param (tabOf θj).seed =
        cell (tabOf (userOf θ i)).param Quantum.Xmss.Slot.param (tabOf (userOf θ i)).seed :=
      (cell_param_eq _ _ _).trans hc
    have hsig := cell_injective _ (addressable_slot .param) (addressable_slot .param) hc'
    have hpay : (tabOf θj).seed = (tabOf (userOf θ i)).seed :=
      eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
    have hu := congrArg upperHalfOfHash hpay
    rw [upperHalfOfHash_seed_tabOf, upperHalfOfHash_seed_tabOf, hθj,
      Function.update_of_ne (show hiC Pos.seed ≠ srcOf Pos.param by
        rw [show srcOf Pos.param = (some Pos.seed, false) from rfl]; simp [hiC])] at hu
    exact hji (hG.2.2 hu)
  · have hpre : prefixedSlot p.slot = true := prefixedSlot_slot h1 h2
    have hpre' : prefixedSlot p'.slot = true := hsl' ▸ hpre
    have hP := (prefixOf_cell (tabOf θj).param (addressable_slot p') hpre'
      (payload (seedOf θj) (tabOf θj) p')).symm.trans ((congrArg prefixOf hc).trans
        (prefixOf_cell (tabOf (userOf θ i)).param (addressable_slot p) hpre
          (payload (seedsOf θ i) (tabOf (userOf θ i)) p)))
    have hPe : (tabOf (userOf θ j)).param = (tabOf (userOf θ i)).param := by
      have h := Option.some.inj hP
      rw [param_tabOf, hθj, Function.update_of_ne (srcOf_ne_paramC p).symm] at h
      rw [param_tabOf, h, param_tabOf]
    exact hji (hgood.2 hPe)

/-- Distinct values at injective coordinates `e` of uniform digests, up to `C(n,2) 2^-128`. -/
theorem uavg_not_injective_digest_le {P : Type} [Fintype P] [DecidableEq P] (e : Fin n → P)
    (he : Function.Injective e) :
    uavg (fun θ : P → Digest ↦
        if Function.Injective fun i ↦ θ (e i) then (0 : ℝ≥0∞) else 1) ≤
      n.choose 2 * (2 ^ 128)⁻¹ := by
  have hr := uavg_restrict_injective e he
    fun u : Fin n → Digest ↦ if Function.Injective fun i ↦ u i then (0 : ℝ≥0∞) else 1
  have h := uavg_not_injective_le (n := n) (fun b : Digest ↦ b) (c := 1)
    (card_filter_eq_le_one (β := Digest))
  rw [card_digest, Nat.cast_one, one_div, Nat.cast_pow, Nat.cast_ofNat] at h
  exact hr.trans_le h

/-- `GoodN` from three injectivities: public parameters, high halves of master seeds and of
scheme seeds. -/
theorem goodN_of_hi {θ : HPosN n → Digest} (hP : Function.Injective fun i ↦ θ (i, paramC))
    (hS0 : Function.Injective fun i ↦ θ (i, (none, true)))
    (hS : Function.Injective fun i ↦ θ (i, hiC .seed)) : GoodN θ := by
  refine ⟨goodN_of (fun a b h ↦ hS0 ?_) (fun a b h ↦ hS ?_) (fun a b h ↦ hP ?_), hS0, hS⟩
  · have hu := congrArg upperHalfOfHash h
    simp only [seedsOf, upperHalfOfHash_seedOf] at hu
    exact hu
  · have hu : upperHalfOfHash (tabOf (userOf θ a)).seed =
        upperHalfOfHash (tabOf (userOf θ b)).seed := congrArg upperHalfOfHash h
    rwa [upperHalfOfHash_seed_tabOf, upperHalfOfHash_seed_tabOf] at hu
  · have hu : (tabOf (userOf θ a)).param = (tabOf (userOf θ b)).param := h
    rw [param_tabOf, param_tabOf] at hu
    exact hu

/-- **The collision bound**: `GoodN` fails with probability at most `3 C(n,2) 2^-128`. -/
theorem uavg_not_goodN_le :
    uavg (fun θ : HPosN n → Digest ↦ if GoodN θ then (0 : ℝ≥0∞) else 1) ≤ collTermN n := by
  have he : ∀ c : HPos, Function.Injective fun i : Fin n ↦ ((i, c) : HPosN n) :=
    fun _ _ _ h ↦ (Prod.mk.inj h).1
  have h1 := uavg_not_injective_digest_le (P := HPosN n) _ (he paramC)
  have h2 := uavg_not_injective_digest_le (P := HPosN n) _ (he (none, true))
  have h3 := uavg_not_injective_digest_le (P := HPosN n) _ (he (hiC .seed))
  have hpt : ∀ θ : HPosN n → Digest, (if GoodN θ then (0 : ℝ≥0∞) else 1) ≤
      (if Function.Injective fun i : Fin n ↦ θ (i, paramC) then (0 : ℝ≥0∞) else 1) +
        (if Function.Injective fun i : Fin n ↦ θ (i, (none, true)) then (0 : ℝ≥0∞) else 1) +
        (if Function.Injective fun i : Fin n ↦ θ (i, hiC .seed) then (0 : ℝ≥0∞) else 1) :=
    fun θ ↦ by
      by_cases a : Function.Injective fun i : Fin n ↦ θ (i, paramC)
      · by_cases b : Function.Injective fun i : Fin n ↦ θ (i, (none, true))
        · by_cases c : Function.Injective fun i : Fin n ↦ θ (i, hiC .seed)
          · rw [ite_eq_left (goodN_of_hi a b c)]
            exact zero_le
          · rw [ite_eq_right c]
            split_ifs <;> simp
        · rw [ite_eq_right b]
          split_ifs <;> simp
      · rw [ite_eq_right a]
        split_ifs <;> simp
  refine (uavg_mono hpt).trans ?_
  rw [uavg_add, uavg_add]
  refine (add_le_add (add_le_add h1 h2) h3).trans_eq ?_
  rw [collTermN]
  ring

end good

/-! ## The sources of the hidden cells -/

section sources

/-- The source coordinates of a cell: those of its slot, for every user. -/
def cellSrcN (z : HashDomain) : Finset (HPosN n) :=
  Finset.univ ×ˢ cellSrc z

open Classical in
/-- **User `i`'s values of the coordinate `t`** making `z` its cell: the single-user ones, when no
other user can make `z` its cell by changing its own coordinate `t`. -/
noncomputable def srcValsN (z : HashDomain) (i : Fin n) (t : HPos) (θ : HPosN n → Digest) :
    Finset Digest :=
  if ∀ j, j ≠ i → srcVals z t (userOf θ j) = ∅ then srcVals z t (userOf θ i) else ∅

theorem srcValsN_update (z : HashDomain) (i : Fin n) (t : HPos) (θ : HPosN n → Digest)
    (d : Digest) : srcValsN z i t (Function.update θ (i, t) d) = srcValsN z i t θ := by
  have hc : (∀ j, j ≠ i → srcVals z t (userOf (Function.update θ (i, t) d) j) = ∅) ↔
      ∀ j, j ≠ i → srcVals z t (userOf θ j) = ∅ :=
    forall_congr' fun j ↦ imp_congr_right fun hj ↦ by rw [userOf_update_of_ne θ hj]
  simp only [srcValsN, hc, userOf_update_self, srcVals_update]

theorem card_srcValsN_le_one (z : HashDomain) (i : Fin n) (t : HPos) (θ : HPosN n → Digest) :
    (srcValsN z i t θ).card ≤ 1 := by
  unfold srcValsN
  split
  · exact card_srcVals_le_one z t _
  · simp

/-- **At most one user has source values.** -/
theorem srcValsN_eq_empty {z : HashDomain} {t : HPos} {θ : HPosN n → Digest} {i j : Fin n}
    (h : (srcValsN z i t θ).Nonempty) (hji : j ≠ i) : srcValsN z j t θ = ∅ := by
  unfold srcValsN at h ⊢
  by_cases hi : ∀ k, k ≠ i → srcVals z t (userOf θ k) = ∅
  · have hj := hi j hji
    split
    · exact hj
    · rfl
  · rw [ite_eq_right hi] at h
    exact absurd h Finset.not_nonempty_empty

theorem sum_cellSrcN_le (z : HashDomain) (θ : HPosN n → Digest) :
    ∑ a ∈ cellSrcN (n := n) z, ((srcValsN z a.1 a.2 θ).card : ℝ≥0∞) *
      (Fintype.card (HDN n a) : ℝ≥0∞)⁻¹ ≤ kappaQ := by
  have hc : (Fintype.card Digest : ℝ≥0∞)⁻¹ = kappaQ := by
    rw [card_digest, kappaQ, Nat.cast_pow, Nat.cast_ofNat]
  have hterm : ∀ (i : Fin n) (t : HPos),
      ((srcValsN z i t θ).card : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ ≤ kappaQ :=
    fun i t ↦ by
      rw [hc]
      refine (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_srcValsN_le_one z i t θ))
        zero_le).trans_eq ?_
      rw [Nat.cast_one, one_mul]
  unfold cellSrcN cellSrc
  split
  · rename_i s _
    rw [Finset.sum_product, Finset.sum_comm, Finset.sum_singleton]
    by_cases hex : ∃ i : Fin n, (srcValsN z i (srcSlot s) θ).Nonempty
    · obtain ⟨i, hi⟩ := hex
      rw [Finset.sum_eq_single i (fun j _ hji ↦ by
        rw [srcValsN_eq_empty hi hji, Finset.card_empty, Nat.cast_zero, zero_mul])
        (fun h ↦ absurd (Finset.mem_univ i) h)]
      exact hterm i _
    · simp only [not_exists, Finset.not_nonempty_iff_eq_empty] at hex
      rw [Finset.sum_eq_zero fun i _ ↦ by
        rw [hex i, Finset.card_empty, Nat.cast_zero, zero_mul]]
      exact zero_le
  · rw [Finset.product_empty, Finset.sum_empty]
    exact zero_le

/-- **The hidden cells on the good set**: all cells on `GoodN`, none elsewhere. -/
def maskHidN (θ : HPosN n → Digest) : Set HashDomain :=
  {z | GoodN θ ∧ z ∈ hidCellsN θ}

theorem maskHidN_of_goodN {θ : HPosN n → Digest} (hG : GoodN θ) : maskHidN θ = hidCellsN θ :=
  Set.ext fun _ ↦ and_iff_right hG

/-- **The sources of the hidden cells on the good set**, on the states of the source invariant. -/
noncomputable def sourcesQN :
    Sources HashOutput HashDomain (HPosN n) (SelMemN n) (HPosN n) (HDN n) (fun r ↦ r.2.2.1)
      (fun θ ↦ SrcInvN θ) maskHidN (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ where
  sh z _ := cellSrcN z
  sk _ _ := ∅
  sk' _ _ := ∅
  Fh z _ a θ := srcValsN z a.1 a.2 θ
  Fk _ _ _ _ := ∅
  Fk' _ _ _ _ := ∅
  hFh z _ a θ d := srcValsN_update z a.1 a.2 θ d
  hFk _ _ _ _ _ := rfl
  hFk' _ _ _ _ _ := rfl
  hh θ z r hinv hz hnone := by
    obtain ⟨hG, i, p, rfl⟩ := hz
    refine ⟨(i, srcOf p), ?_, fun hp ↦ hinv i p hp hnone, ?_⟩
    · simp only [cellSrcN, cellSrc, slotOf_cellOf, Finset.mem_product, Finset.mem_univ,
        Finset.mem_singleton, true_and]
      rfl
    · change θ (i, srcOf p) ∈ srcValsN _ i (srcOf p) θ
      unfold srcValsN
      rw [ite_eq_left fun j hji ↦ srcVals_eq_empty_of_goodN hG i j hji p]
      exact mem_srcVals (userOf θ i) p
  hk _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hk' _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hκh z _ θ := sum_cellSrcN_le z θ
  hκk _ _ _ := by simp
  hκk' _ _ _ := by simp

end sources

/-! ## The masses of the game -/

section masses

/-- The initial state of the game and the register. -/
noncomputable def initN :
    Matrix (QReg.of Unit × QReg.of (RRegN n (SelMemN n)))
      (QReg.of Unit × QReg.of (RRegN n (SelMemN n))) ℂ :=
  (SubState.basis ()).matrix ⊗ₖ
    (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).init.matrix

theorem initN_posSemidef : (initN (n := n)).PosSemidef :=
  ((SubState.basis ()).prod
    (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).init).posSemidef

theorem ofReal_trace_initN_le_one : ENNReal.ofReal (initN (n := n)).trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).init).trace_re_le_one

/-- The masked masses are those of the masked hidden sets. -/
theorem ite_totalWeight_le_maskHidN {θ : HPosN n → Digest}
    (w : Set HashDomain → (i : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Port) →
      Matrix ((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In i ×
        QReg.of (RRegN n (SelMemN n)))
        ((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In i ×
        QReg.of (RRegN n (SelMemN n))) ℂ → ℝ≥0∞) (valid : SignLog → Bool)
    (A : MuAdversary n) :
    (if GoodN θ then (runtimeR m0N).totalWeight .instruments (w (hidCellsN θ))
      (muGameQN valid A θ) initN else 0) ≤
      (runtimeR m0N).totalWeight .instruments (w (maskHidN θ)) (muGameQN valid A θ) initN := by
  split_ifs with hG
  · rw [maskHidN_of_goodN hG]
  · exact zero_le

/-- The trials' reads carry no hidden mass: on hidden sets without message digests, the read mass
is that of the reads at cells other than message digests. -/
theorem readMass_le_readQN {H : Set HashDomain} (hH : ∀ z ∈ H, isMsgCell z = false)
    (i : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Port)
    (σ : Matrix ((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In i ×
      QReg.of (RRegN n (SelMemN n)))
      ((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In i ×
      QReg.of (RRegN n (SelMemN n))) ℂ) :
    readMass H ∅ ∅ i σ ≤
      portMass (fun i ↦ readQN (SelMemN n) (n := n) i = true) H ∅ ∅ i σ := by
  rcases i with (((_ | _ | _) | (⟨z, u⟩ | ⟨y, u⟩ | ⟨y, u⟩)) | c) | T
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · by_cases hz : isMsgCell z = true
    · have hz' : z ∉ H := fun h ↦ by
        rw [hH z h] at hz
        exact Bool.false_ne_true hz
      simp [readMass, portMass, readQN, readMsg, hz, Quantum.Xmss.Assembly.extWeight,
        Quantum.Xmss.Assembly.sumWeight, hiddenMass, diagMass, hz']
    · simp only [Bool.not_eq_true] at hz
      simp only [readMass, portMass, readQN, readMsg, hz, Bool.not_false]
      split <;> simp
  · simp only [readMass, portMass, readQN, readMsg, Bool.not_false]
    split <;> simp
  · simp only [readMass, portMass, readQN, readMsg, Bool.not_false]
    split <;> simp
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight,
      hiddenMass]
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight]

variable (valid : SignLog → Bool) (A : MuAdversary n) {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
include hhash hsign

/-- **The sponge-port masses on the good set**: at most `q · 2^-128`, averaged over the hidden
values. -/
theorem uavg_mask_spongeMass_leN :
    uavg (fun θ : HPosN n → Digest ↦ if GoodN θ then (runtimeR m0N).totalWeight .instruments
      (spongeMass (hidCellsN θ) ∅ ∅) (muGameQN valid A θ) initN else 0) ≤ q * kappaQ := by
  have hc : (fun i ↦ if (extCls HashOutput HashDomain (Finset (HPosN n) × SelMemN n)
      (recSpec (HPosN n) (SelMemN n)) i = false) then 1 else 0) =
      fun i ↦ if extCls HashOutput HashDomain (Finset (HPosN n) × SelMemN n)
        (recSpec (HPosN n) (SelMemN n)) i then 0 else 1 := by
    funext i
    rcases Bool.eq_false_or_eq_true (extCls HashOutput HashDomain (Finset (HPosN n) × SelMemN n)
      (recSpec (HPosN n) (SelMemN n)) i) with h | h <;> simp [h]
  refine (uavg_mono fun θ ↦ ite_totalWeight_le_maskHidN (fun H ↦ spongeMass H ∅ ∅) valid
    A).trans ?_
  refine uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv .instruments
    (fun i ↦ extCls HashOutput HashDomain (Finset (HPosN n) × SelMemN n)
      (recSpec (HPosN n) (SelMemN n)) i = false)
    m0N (fun r ↦ r.2.2.1) (fun θ ↦ muGameQN valid A θ) (fun _ ↦ initN)
    (fun _ ↦ initN_posSemidef) (fun j ↦ viewByOn_muGameT (SelMemN n) cwUpdN valid A m0N initN j)
    (fun θ ↦ SrcInvN θ)
    (fun θ ↦ forallQueries_muGameQN cwUpdN (fun _ h ↦ Bool.noConfusion h) m0N valid A θ initN
      (querySupportedOn_initQN m0N rfl _)) maskHidN (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQN
    (fun θ ↦ by rw [hc]; exact advCalls_muGameQ cwUpdN valid A hhash hsign θ)).trans ?_)
  exact sum_mul_trace_le kappaQ _ ofReal_trace_initN_le_one q

/-- **The read-port masses on the good set**: the verification's reads, at most
`verifyCalls · 2^-128`, averaged over the hidden values. -/
theorem uavg_mask_readMass_leN :
    uavg (fun θ : HPosN n → Digest ↦ if GoodN θ then (runtimeR m0N).totalWeight .instruments
      (readMass (hidCellsN θ) ∅ ∅) (muGameQN valid A θ) initN else 0) ≤
      verifyCalls * kappaQ := by
  refine (uavg_mono fun θ ↦ (ite_totalWeight_le_maskHidN (fun H ↦ readMass H ∅ ∅) valid
    A).trans (totalWeight_le_totalWeight (runtimeR m0N) .instruments
      (fun i σ _ ↦ readMass_le_readQN (fun z hz ↦ isMsgCell_of_mem_hidCellsN hz.2) i σ)
      (muGameQN valid A θ) initN_posSemidef)).trans ?_
  refine uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv .instruments
    (fun i ↦ readQN (SelMemN n) (n := n) i = true) m0N (fun r ↦ r.2.2.1)
    (fun θ ↦ muGameQN valid A θ) (fun _ ↦ initN)
    (fun _ ↦ initN_posSemidef) (fun j ↦ viewByOn_muGameT (SelMemN n) cwUpdN valid A m0N initN j)
    (fun θ ↦ SrcInvN θ)
    (fun θ ↦ forallQueries_muGameQN cwUpdN (fun _ h ↦ Bool.noConfusion h) m0N valid A θ initN
      (querySupportedOn_initQN m0N rfl _)) maskHidN (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQN
    (fun θ ↦ readQCalls_muGameQ cwUpdN valid A hhash hsign θ)).trans ?_)
  exact sum_mul_trace_le kappaQ _ ofReal_trace_initN_le_one verifyCalls

end masses

/-! ## The hybrid -/

section hybrid

/-- **Runtime 1's win at the hidden values `θ`**: all users' table cells hardwired at the start. -/
noncomputable def p1QN (valid : SignLog → Bool) (A : MuAdversary n) (θ : HPosN n → Digest) :
    ℝ≥0∞ :=
  (runtime1R HashOutput HashDomain (tableHwN θ) m0N).evalDistMap .instruments
    (muGameQN valid A θ) (SubState.basis ()) winObsQ {true}

/-- **Runtime 2's win at the hidden values `θ`** (the quantity the end slice bounds, masked by
`GoodN` and averaged over `θ`). -/
noncomputable def p2QN (valid : SignLog → Bool) (A : MuAdversary n) (θ : HPosN n → Digest) :
    ℝ≥0∞ :=
  (runtimeR m0N).evalDistMap .instruments (muGameQN valid A θ) (SubState.basis ()) winObsQ {true}

/-- **The multi-user QROM game is at most the bad fraction of tables plus runtime 1 on good
tables, averaged over the hidden values.** -/
theorem muWinProb_le_uavg_goodN (valid : SignLog → Bool) (A : MuAdversary n) :
    muWinProb xmssRom valid n A ≤
      uavg (fun θ : HPosN n → Digest ↦
        (if (tableN (seedsOf θ)).good (tabOfN θ) then (0 : ℝ≥0∞) else 1) +
          if (tableN (seedsOf θ)).good (tabOfN θ) then p1QN valid A θ else 0) := by
  rw [muWinProb_eq_uniform xmssRom valid prEvent_sampleSeed_xmssRom A,
    uavg_equiv_prod thetaEquivN, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    ENNReal.inv_pow]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S0 _ ↦ ?_) zero_le
  refine (qromEvalDistMap_muGame_le_runtime1R (SelMemN n) cwUpdN S0 valid A m0N
    (SubState.basis ()) winObsQ {true}).trans (le_of_eq ?_)
  rw [inv_card_mul_card_filter_not_eq_uavg, uavg, ← Finset.mul_sum, ← mul_add,
    ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun w _ ↦ ?_)
  simp only [thetaEquivN, Equiv.coe_fn_symm_mk, p1QN, tableHwN, muGameQN, seedsOf_thetaOfN,
    tabOfN_thetaOfN]

/-- **The mask moves to `GoodN`**: the bad fraction of tables and the gap to `GoodN` are the bad
fraction of `GoodN`. -/
theorem muWinProb_le_uavg_maskN (valid : SignLog → Bool) (A : MuAdversary n) :
    muWinProb xmssRom valid n A ≤
      uavg (fun θ : HPosN n → Digest ↦ if GoodN θ then (0 : ℝ≥0∞) else 1) +
        uavg (fun θ ↦ if GoodN θ then p1QN valid A θ else 0) := by
  refine (muWinProb_le_uavg_goodN valid A).trans ?_
  rw [← uavg_add]
  refine uavg_mono fun θ ↦ ?_
  by_cases hG : GoodN θ
  · rw [ite_eq_left hG.1, ite_eq_left hG.1, ite_eq_left hG, ite_eq_left hG]
  · rw [ite_eq_right hG, ite_eq_right hG, add_zero]
    by_cases hg : (tableN (seedsOf θ)).good (tabOfN θ)
    · rw [ite_eq_left hg, ite_eq_left hg, zero_add]
      exact evalDistMap_apply_le_one _ _ _ _ _ _
    · rw [ite_eq_right hg, ite_eq_right hg, add_zero]

variable (valid : SignLog → Bool) (A : MuAdversary n) {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
include hhash hsign

/-- **The graded hybrid on the good set, averaged**: runtime 1 against runtime 2. -/
theorem uavg_mask_p1QN_le :
    uavg (fun θ ↦ if GoodN θ then p1QN valid A θ else 0) ≤
      (uavg (fun θ ↦ if GoodN θ then p2QN valid A θ else 0) ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2 := by
  have h := uavg_mask_win_runtime1R_le_graded .instruments tableHwN hidCellsN (fun _ ↦ ∅)
    (fun _ ↦ ∅) covers_tableHwN m0N (fun θ ↦ muGameQN valid A θ) (fun _ ↦ SubState.basis ())
    (fun _ ↦ winObsQ) (measurableSet_singleton true) q
    (fun θ ↦ advCalls_muGameQ cwUpdN valid A hhash hsign θ) GoodN (q * kappaQ)
    (verifyCalls * kappaQ) (uavg_mask_spongeMass_leN valid A hhash hsign)
    (uavg_mask_readMass_leN valid A hhash hsign)
  rw [add_assoc] at h
  exact h

/-- **The hidden-value hybrid of multi-user leanXMSS in the QROM**, on the good set:
`√(E[1_GoodN p1QN]) ≤ √(E[1_GoodN p2QN]) + 2q·2^-64 + √(verifyCalls · 2^-128)`. -/
theorem sqrt_win_runtime1_le_qromN :
    uavg (fun θ ↦ if GoodN θ then p1QN valid A θ else 0) ^ (2⁻¹ : ℝ) ≤
      uavg (fun θ ↦ if GoodN θ then p2QN valid A θ else 0) ^ (2⁻¹ : ℝ) + hybTermQ q :=
  (ENNReal.rpow_le_rpow (uavg_mask_p1QN_le valid A hhash hsign) (by norm_num)).trans_eq
    (sq_rpow_inv_two_eq _)

/-- **The multi-user QROM game through the hybrid**: `muWinProb ≤ 3 C(n,2) 2^-128 +
(√(E[1_GoodN p2QN]) + hybTermQ q)²`. -/
theorem muWinProb_le_hybridN :
    muWinProb xmssRom valid n A ≤
      collTermN n +
        (uavg (fun θ ↦ if GoodN θ then p2QN valid A θ else 0) ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2 :=
  (muWinProb_le_uavg_maskN valid A).trans
    (add_le_add uavg_not_goodN_le (uavg_mask_p1QN_le valid A hhash hsign))

end hybrid

end Quantum.Qrom.Xmss.Multi

end
