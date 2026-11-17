module

public import Quantum.Qrom.Xmss.GameTCalls
public import Quantum.Qrom.Xmss.GameT

@[expose] public section

/-!
# The hidden-value hybrid of leanXMSS in the QROM (runtime 1 against runtime 2)

The QROM game is runtime 1 on the realized template (`qrom_game_eq_runtime1R`), averaged over the
master seed and the table, that is over the hidden values `θ` (`thetaEquiv`):
`winProb_eq_uavg_p1Q`. The graded hybrid (`uavg_win_runtime1R_le_graded_total`) compares it with
runtime 2 (`runtimeR`), at the cost of the hidden masses of runtime 1's cells (`hidCells θ`, the
cells of the table) at the sponge calls and at the reads.

* **Sources** (`cellSrc`, `srcVals`, `sourcesQ`): a hidden cell not hardwired in a state of the
  source invariant (`SrcInv`, GameTCalls) has its source coordinate unrevealed, and the cell fixes
  that coordinate's value (`card_srcVals_le_one`), so its mass is at most `2^-128` per call
  (`kappaQ`), whatever the number of positions.
* **Sponge calls** (`uavg_spongeMass_le`): at most `q · 2^-128` summed over the `q` calls.
* **Reads** (`uavg_readMass_le`): the trials read message-digest cells, which are no table cells
  (`isMsgCell_of_mem_hidCells`): mass `0`; the verification's reads `verifyCalls · 2^-128`.
  Program and record ports cost nothing.
* **The hybrid** (`sqrt_win_runtime1_le_qrom`): `√winProb ≤ √(E p2Q) + 2q·2^-64 + √(v·2^-128)`,
  `p2Q A θ` runtime 2's win at `θ`.
-/

open Matrix IPFunctor MeasureTheory
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT runtime1R extCls Sources
  sum_totalWeight_portMass_runtimeR_le_inv)

/-! ## The hidden cells -/

section cells

/-- **The hidden cells at `θ`**: the cells of runtime 1's table. -/
def hidCells (θ : HPos → Digest) : Set HashDomain :=
  {z | ∃ p, cellOf (seedOf θ) p (tabOf θ) = z}

/-- Runtime 1's hardwired cells at `θ`: the table of the master seed and values of `θ`. -/
noncomputable def tableHwQ (θ : HPos → Digest) : Hw HashOutput HashDomain :=
  (table (seedOf θ)).hwOf (tabOf θ)

theorem covers_tableHwQ (θ : HPos → Digest) : Covers (tableHwQ θ) (hidCells θ) ∅ ∅ := by
  refine ⟨fun z hz ↦ ?_, fun _ hx ↦ absurd rfl hx, fun _ hx ↦ absurd rfl hx⟩
  by_contra h
  exact hz ((table (seedOf θ)).tableDb_of_forall_ne fun p hp ↦ h ⟨p, hp⟩)

/-- No hidden cell is a message digest. -/
theorem isMsgCell_of_mem_hidCells {θ : HPos → Digest} {z : HashDomain} (hz : z ∈ hidCells θ) :
    isMsgCell z = false := by
  obtain ⟨p, rfl⟩ := hz
  rw [isMsgCell, slotOf_cellOf]
  cases p <;> rfl

end cells

/-! ## The sources of the hidden cells -/

section sources

/-- The source coordinates of a cell: that of its slot. -/
def cellSrc (z : HashDomain) : Finset HPos :=
  match slotOf z with
  | some s => {srcSlot s}
  | none => ∅

open Classical in
/-- The values of the coordinate `s`, the others as in `θ`, for which `z` is the cell of a
position whose source is `s`. -/
noncomputable def srcVals (z : HashDomain) (s : HPos) (θ : HPos → Digest) : Finset Digest :=
  Finset.univ.filter fun d ↦ ∃ p, srcOf p = s ∧
    cellOf (seedOf (Function.update θ s d)) p (tabOf (Function.update θ s d)) = z

theorem srcVals_update (z : HashDomain) (s : HPos) (θ : HPos → Digest) (d : Digest) :
    srcVals z s (Function.update θ s d) = srcVals z s θ := by
  simp only [srcVals, Function.update_idem]

theorem mem_srcVals (θ : HPos → Digest) (p : Pos) :
    θ (srcOf p) ∈ srcVals (cellOf (seedOf θ) p (tabOf θ)) (srcOf p) θ := by
  classical
  simp only [srcVals, Finset.mem_filter, Finset.mem_univ, true_and, Function.update_eq_self]
  exact ⟨p, rfl, rfl⟩

/-- The value of a structural position's source at the values `θ`. -/
theorem value_tabOf_vcoord {q : Quantum.Xmss.Pos} (hq : VRange q) (θ : HPos → Digest) :
    (tabOf θ).value q = θ (vcoord q) := by
  rcases q with ⟨l, e, i, _ | j⟩ | ⟨l, _ | k, a⟩ <;> simp only [VRange, chainLength_eq] at hq
  · change hashHalfForChain i.val (tabOf θ _) = _
    unfold hashHalfForChain tabOf
    rw [vcoord_chain_zero]
    by_cases hi : i.val % 2 = 0
    · simp only [hi, ↓reduceIte, ne_eq, not_true_eq_false, decide_false]
      exact truncateHash_joinHalves _ _
    · simp only [hi, ↓reduceIte, ne_eq, not_false_eq_true, decide_true]
      exact upperHalfOfHash_joinHalves _ _
  · have hj : j < chainLength - 1 := by rw [chainLength_eq]; omega
    change QTable.chainValue _ l e i (j + 1) = _
    rw [vcoord_chain_succ l e i hj]
    simp only [QTable.chainValue, dite_eq_left hj]
    exact truncateHash_joinHalves _ _
  · change truncateHash (tabOf θ _) = _
    rw [vcoord_tree_zero]
    exact truncateHash_joinHalves _ _
  · have hk := tree_succ_cond hq.1 hq.2
    change QTable.treeValue _ l (k + 1) a = _
    rw [vcoord_tree_succ l k a hk]
    simp only [QTable.treeValue, dite_eq_left hk]
    exact truncateHash_joinHalves _ _

/-- The source's value read from a payload. -/
def srcVal : (p : Pos) → Payload p.slot → Digest
  | .seed, d => truncateHash d
  | .param, d => truncateHash d
  | .prf .., d => truncateHash d
  | .chain .., d => d
  | .leaf .., d => d chain0
  | .node .., d => d.1
  | .rndBottom .., d => truncateHash d.1
  | .rndTop .., d => truncateHash d.1

/-- **A cell's payload carries its source's value.** -/
theorem srcVal_payload (θ : HPos → Digest) :
    ∀ p : Pos, srcVal p (payload (seedOf θ) (tabOf θ) p) = θ (srcOf p)
  | .seed => truncateHash_joinHalves _ _
  | .param => truncateHash_joinHalves _ _
  | .prf .. => truncateHash_joinHalves _ _
  | .rndBottom .. => truncateHash_joinHalves _ _
  | .rndTop .. => truncateHash_joinHalves _ _
  | .chain l e i step => by
    rw [srcOf_struct (isStruct_chain l e i step)]
    exact value_tabOf_vcoord (vRange_srcQ (isStruct_chain l e i step)) θ
  | .leaf l e => by
    rw [srcOf_struct (p := .leaf l e) trivial]
    exact value_tabOf_vcoord (vRange_srcQ (p := .leaf l e) trivial) θ
  | .node l k x => by
    rw [srcOf_struct (p := .node l k x) trivial]
    exact value_tabOf_vcoord (vRange_srcQ (p := .node l k x) trivial) θ

/-- **A cell fixes its source's value**: at most one value of the source makes `z` a cell of a
position with that source. -/
theorem card_srcVals_le_one (z : HashDomain) (s : HPos) (θ : HPos → Digest) :
    (srcVals z s θ).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun d₁ h₁ d₂ h₂ ↦ ?_
  simp only [srcVals, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  obtain ⟨p₁, rfl, hz₁⟩ := h₁
  obtain ⟨p₂, hs, hz₂⟩ := h₂
  have hne : paramC ≠ srcOf p₁ := (srcOf_ne_paramC p₁).symm
  have hP : (tabOf (Function.update θ (srcOf p₁) d₂)).param =
      (tabOf (Function.update θ (srcOf p₁) d₁)).param := by
    rw [param_tabOf, param_tabOf, Function.update_of_ne hne, Function.update_of_ne hne]
  unfold cellOf at hz₁ hz₂
  rw [hP, ← hz₁] at hz₂
  have hsig := cell_injective _ (addressable_slot p₁) (addressable_slot p₂) hz₂.symm
  have hp : p₁ = p₂ := Option.some.inj ((posOf_payload _ _ p₁).symm.trans
    ((congrArg (fun x : Σ s, Payload s ↦ posOf x.1 x.2) hsig).trans (posOf_payload _ _ p₂)))
  subst hp
  have hpay := eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
  calc d₁ = Function.update θ (srcOf p₁) d₁ (srcOf p₁) :=
        (Function.update_self (srcOf p₁) d₁ θ).symm
    _ = srcVal p₁ (payload (seedOf (Function.update θ (srcOf p₁) d₁))
          (tabOf (Function.update θ (srcOf p₁) d₁)) p₁) := (srcVal_payload _ p₁).symm
    _ = srcVal p₁ (payload (seedOf (Function.update θ (srcOf p₁) d₂))
          (tabOf (Function.update θ (srcOf p₁) d₂)) p₁) := by rw [hpay]
    _ = Function.update θ (srcOf p₁) d₂ (srcOf p₁) := srcVal_payload _ p₁
    _ = d₂ := Function.update_self (srcOf p₁) d₂ θ

theorem card_digest : Fintype.card Digest = 2 ^ 128 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  rfl

/-- **The mass per call**: one 128-bit source per hidden cell. -/
noncomputable def kappaQ : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹

theorem sum_cellSrc_le (z : HashDomain) (θ : HPos → Digest) :
    ∑ s ∈ cellSrc z, ((srcVals z s θ).card : ℝ≥0∞) * (Fintype.card (HD s) : ℝ≥0∞)⁻¹ ≤
      kappaQ := by
  unfold cellSrc
  split
  · rw [Finset.sum_singleton]
    have hc : (Fintype.card Digest : ℝ≥0∞)⁻¹ = kappaQ := by
      rw [card_digest, kappaQ, Nat.cast_pow, Nat.cast_ofNat]
    refine (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_srcVals_le_one _ _ θ))
      zero_le).trans_eq ?_
    rw [Nat.cast_one, one_mul]
    exact hc
  · rw [Finset.sum_empty]
    exact zero_le

/-- **The sources of the hidden cells** on the states of the source invariant. -/
noncomputable def sourcesQ :
    Sources HashOutput HashDomain HPos SelMem HPos HD (fun r ↦ r.2.2.1) (fun θ ↦ SrcInv θ)
      hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ where
  sh z _ := cellSrc z
  sk _ _ := ∅
  sk' _ _ := ∅
  Fh z _ s θ := srcVals z s θ
  Fk _ _ _ _ := ∅
  Fk' _ _ _ _ := ∅
  hFh z _ s θ d := srcVals_update z s θ d
  hFk _ _ _ _ _ := rfl
  hFk' _ _ _ _ _ := rfl
  hh θ z r hinv hz hnone := by
    obtain ⟨p, rfl⟩ := hz
    refine ⟨srcOf p, ?_, fun hp ↦ hinv p hp hnone, mem_srcVals θ p⟩
    simp only [cellSrc, slotOf_cellOf, Finset.mem_singleton]
    rfl
  hk _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hk' _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hκh z _ θ := sum_cellSrc_le z θ
  hκk _ _ _ := by simp
  hκk' _ _ _ := by simp

end sources

/-! ## The masses of the game -/

section masses

/-- The canonical initial memory: nothing revealed, no selection recorded. -/
def m0H : Finset HPos × SelMem :=
  (∅, fun _ _ ↦ none)

/-- The initial state of the game and the register. -/
noncomputable def initH :
    Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × SelMem)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × SelMem))) ℂ :=
  (SubState.basis ()).matrix ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m0H).init.matrix

theorem initH_posSemidef : initH.PosSemidef :=
  ((SubState.basis ()).prod (runtimeR (X := HashOutput) (Z := HashDomain) m0H).init).posSemidef

theorem ofReal_trace_initH_le_one : ENNReal.ofReal initH.trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := HashOutput) (Z := HashDomain) m0H).init).trace_re_le_one

/-- An average bounded through its sum. -/
theorem uavg_le_of_sum_le {Θ : Type*} [Fintype Θ] [Nonempty Θ] (f : Θ → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∑ θ, f θ ≤ c * Fintype.card Θ) : uavg f ≤ c := by
  have h0 : (Fintype.card Θ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold uavg
  calc (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, f θ
      ≤ (Fintype.card Θ : ℝ≥0∞)⁻¹ * (c * Fintype.card Θ) := by gcongr
    _ = c := by rw [mul_comm c, ← mul_assoc, ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _),
      one_mul]

/-- A trace-weighted count summed over a finite type. -/
theorem sum_mul_trace_le {Θ : Type*} [Fintype Θ] (κ t : ℝ≥0∞) (ht : t ≤ 1) (N : ℕ) :
    κ * (N * ∑ _θ : Θ, t) ≤ N * κ * Fintype.card Θ := by
  calc κ * (N * ∑ _θ : Θ, t)
      ≤ κ * (N * ∑ _θ : Θ, (1 : ℝ≥0∞)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun _ _ ↦ ht) zero_le) zero_le
    _ = N * κ * Fintype.card Θ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← mul_assoc, mul_comm κ]

variable (A : Adversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) lifetime)
include hhash hsign

/-- **The sponge-port masses**: at most `q · 2^-128`, averaged over the hidden values. -/
theorem uavg_spongeMass_le :
    uavg (fun θ : HPos → Digest ↦ (runtimeR m0H).totalWeight .instruments
      (spongeMass (hidCells θ) ∅ ∅) (gameQ A θ) initH) ≤ q * kappaQ := by
  have hc : (fun i ↦ if (extCls HashOutput HashDomain (Finset HPos × SelMem)
      (recSpec HPos SelMem) i = false) then 1 else 0) =
      fun i ↦ if extCls HashOutput HashDomain (Finset HPos × SelMem) (recSpec HPos SelMem) i
        then 0 else 1 := by
    funext i
    rcases Bool.eq_false_or_eq_true (extCls HashOutput HashDomain (Finset HPos × SelMem)
      (recSpec HPos SelMem) i) with h | h <;> simp [h]
  refine uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv .instruments
    (fun i ↦ extCls HashOutput HashDomain (Finset HPos × SelMem) (recSpec HPos SelMem) i = false)
    m0H (fun r ↦ r.2.2.1) (fun θ ↦ gameQ A θ) (fun _ ↦ initH) (fun _ ↦ initH_posSemidef)
    (fun j ↦ viewByOn_gameT SelMem cwUpd A m0H initH j) (fun θ ↦ SrcInv θ)
    (fun θ ↦ forallQueries_gameQ cwUpd (fun _ h ↦ Bool.noConfusion h) m0H A θ initH
      (querySupportedOn_initQ m0H rfl _)) hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQ
    (fun θ ↦ by rw [hc]; exact advCalls_gameQ cwUpd A hhash hsign θ)).trans ?_)
  exact sum_mul_trace_le kappaQ _ ofReal_trace_initH_le_one q

omit hhash hsign in
/-- The trials' reads carry no hidden mass: the read mass is that of the reads at cells other than
message digests. -/
theorem readMass_le_readQ (θ : HPos → Digest)
    (i : (recHwSpec HashOutput HashDomain HPos SelMem).Port)
    (σ : Matrix ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
      QReg.of (HwReg HashOutput HashDomain (Finset HPos × SelMem)))
      ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
      QReg.of (HwReg HashOutput HashDomain (Finset HPos × SelMem))) ℂ) :
    readMass (hidCells θ) ∅ ∅ i σ ≤
      portMass (fun i ↦ readQ SelMem i = true) (hidCells θ) ∅ ∅ i σ := by
  rcases i with (((_ | _ | _) | (⟨z, u⟩ | ⟨y, u⟩ | ⟨y, u⟩)) | c) | T
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · by_cases hz : isMsgCell z = true
    · have hz' : z ∉ hidCells θ := fun h ↦ by
        rw [isMsgCell_of_mem_hidCells h] at hz
        exact Bool.false_ne_true hz
      simp [readMass, portMass, readQ, readMsg, hz, Quantum.Xmss.Assembly.extWeight,
        Quantum.Xmss.Assembly.sumWeight, hiddenMass, diagMass, hz']
    · simp only [Bool.not_eq_true] at hz
      simp only [readMass, portMass, readQ, readMsg, hz, Bool.not_false]
      split <;> simp
  · simp only [readMass, portMass, readQ, readMsg, Bool.not_false]
    split <;> simp
  · simp only [readMass, portMass, readQ, readMsg, Bool.not_false]
    split <;> simp
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight,
      hiddenMass]
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight]

/-- **The read-port masses**: the verification's reads, at most `verifyCalls · 2^-128`, averaged
over the hidden values. -/
theorem uavg_readMass_le :
    uavg (fun θ : HPos → Digest ↦ (runtimeR m0H).totalWeight .instruments
      (readMass (hidCells θ) ∅ ∅) (gameQ A θ) initH) ≤ verifyCalls * kappaQ := by
  refine (uavg_mono fun θ ↦ totalWeight_le_totalWeight (runtimeR m0H) .instruments
    (fun i σ _ ↦ readMass_le_readQ θ i σ) (gameQ A θ) initH_posSemidef).trans ?_
  refine uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv .instruments
    (fun i ↦ readQ SelMem i = true) m0H (fun r ↦ r.2.2.1) (fun θ ↦ gameQ A θ) (fun _ ↦ initH)
    (fun _ ↦ initH_posSemidef) (fun j ↦ viewByOn_gameT SelMem cwUpd A m0H initH j)
    (fun θ ↦ SrcInv θ)
    (fun θ ↦ forallQueries_gameQ cwUpd (fun _ h ↦ Bool.noConfusion h) m0H A θ initH
      (querySupportedOn_initQ m0H rfl _)) hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQ
    (fun θ ↦ readQCalls_gameQ cwUpd A hhash hsign θ)).trans ?_)
  exact sum_mul_trace_le kappaQ _ ofReal_trace_initH_le_one verifyCalls

end masses

/-! ## The hybrid -/

section hybrid

/-- The win observable of the game's leaves. -/
def winObsQ : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → Bool :=
  fun p ↦ p.2.2

/-- **Runtime 1's win at the hidden values `θ`**: the table's cells hardwired from the start. -/
noncomputable def p1Q (A : Adversary) (θ : HPos → Digest) : ℝ≥0∞ :=
  (runtime1R HashOutput HashDomain (tableHwQ θ) m0H).evalDistMap .instruments (gameQ A θ)
    (SubState.basis ()) winObsQ {true}

/-- **Runtime 2's win at the hidden values `θ`** (the quantity the end slice bounds, averaged
over `θ`). -/
noncomputable def p2Q (A : Adversary) (θ : HPos → Digest) : ℝ≥0∞ :=
  (runtimeR m0H).evalDistMap .instruments (gameQ A θ) (SubState.basis ()) winObsQ {true}

/-- The uniform average over a product, through an equivalence. -/
theorem uavg_equiv_prod {Θ α β : Type*} [Fintype Θ] [Fintype α] [Fintype β] (e : Θ ≃ α × β)
    (F : Θ → ℝ≥0∞) :
    uavg F = (Fintype.card α : ℝ≥0∞)⁻¹ *
      ∑ a, ((Fintype.card β : ℝ≥0∞)⁻¹ * ∑ b, F (e.symm (a, b))) := by
  unfold uavg
  rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
    ← Equiv.sum_comp e.symm, Fintype.sum_prod_type, mul_assoc, Finset.mul_sum]

theorem prEvent_sampleSeed_xmssRom (S0 : MasterSeed) :
    Pr{let s ← xmssRom.sampleSeed}[s = S0] = (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ := by
  rw [show xmssRom.sampleSeed = sampleMasterSeed from rfl, sampleMasterSeed,
    @SampleableType.prEvent_uniformSample MasterSeed (SampleableType.ofFintype MasterSeed) _
      (· = S0) _, Finset.filter_eq', ite_eq_left (Finset.mem_univ _), Finset.card_singleton,
    Nat.cast_one, one_div]

/-- **The QROM game is runtime 1 on the realized template, averaged over the hidden values.** -/
theorem winProb_eq_uavg_p1Q (A : Adversary) : SufCma.winProb xmssRom A = uavg (p1Q A) := by
  rw [SufCma.winProb_eq_uniform xmssRom prEvent_sampleSeed_xmssRom A,
    uavg_equiv_prod thetaEquiv]
  refine congrArg _ (Finset.sum_congr rfl fun S0 _ ↦ ?_)
  have h := congrArg (fun μ : Measure Bool ↦ μ {true})
    (qrom_game_eq_runtime1R SelMem cwUpd S0 A m0H (SubState.basis ()) winObsQ)
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at h
  refine h.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp only [thetaEquiv, Equiv.coe_fn_symm_mk, p1Q, tableHwQ, seedOf_thetaOf, tabOf_thetaOf]
  rfl

theorem sq_rpow_inv_two_eq (x : ℝ≥0∞) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **The hybrid term**: `√(4 q · q κ) + √(verifyCalls · κ)` (`= 2q·2^-64 + √(v·2^-128)`). -/
noncomputable def hybTermQ (q : ℕ) : ℝ≥0∞ :=
  (4 * (q * (q * kappaQ))) ^ (2⁻¹ : ℝ) + (verifyCalls * kappaQ) ^ (2⁻¹ : ℝ)

variable (A : Adversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) lifetime)
include hhash hsign

/-- **The graded hybrid, averaged**: runtime 1 against runtime 2. -/
theorem uavg_p1Q_le :
    uavg (p1Q A) ≤ (uavg (p2Q A) ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2 := by
  have h := uavg_win_runtime1R_le_graded_total .instruments tableHwQ hidCells (fun _ ↦ ∅)
    (fun _ ↦ ∅) covers_tableHwQ m0H (fun θ ↦ gameQ A θ) (fun _ ↦ SubState.basis ())
    (fun _ ↦ winObsQ) (measurableSet_singleton true) q
    (fun θ ↦ advCalls_gameQ cwUpd A hhash hsign θ) (q * kappaQ) (verifyCalls * kappaQ)
    (uavg_spongeMass_le A hhash hsign) (uavg_readMass_le A hhash hsign)
  rw [add_assoc] at h
  exact h

/-- **The hybrid, squared**: `winProb ≤ (√(E p2Q) + hybTermQ q)²`. -/
theorem winProb_le_hybrid_qrom :
    SufCma.winProb xmssRom A ≤ (uavg (p2Q A) ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2 :=
  (winProb_eq_uavg_p1Q A).trans_le (uavg_p1Q_le A hhash hsign)

/-- **The hidden-value hybrid of leanXMSS in the QROM**: `√winProb ≤ √(E_θ p2Q) + 2q·2^-64 +
√(verifyCalls · 2^-128)`. -/
theorem sqrt_win_runtime1_le_qrom :
    SufCma.winProb xmssRom A ^ (2⁻¹ : ℝ) ≤ uavg (p2Q A) ^ (2⁻¹ : ℝ) + hybTermQ q :=
  (ENNReal.rpow_le_rpow (winProb_le_hybrid_qrom A hhash hsign) (by norm_num)).trans_eq
    (sq_rpow_inv_two_eq _)

end hybrid

end Quantum.Qrom.Xmss

end
