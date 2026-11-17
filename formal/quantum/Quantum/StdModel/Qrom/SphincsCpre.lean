module

public import Quantum.StdModel.Qrom.Cpre
public import Quantum.StdModel.Qrom.SphincsInst

@[expose] public section

/-!
# The leanSPHINCS CPRE instance of the QROM bound (B5)

The obligations of `Quantum.StdModel.Qrom.CpreQ.probAvg_cpre_slRed_le` at leanSPHINCS's CPRE game
`cpre romWorld cpreChains slotColl` played by B5 (`cpreRed`):

* `sph_cellInj`: distinct steps or values have distinct cells (`cpreStep_layout_inj`);
* `stepW_le_twCellCost`: a step cell is a cell of a chain step or a FORS leaf (`CpreCell`), so
  B5's step-cell reads are among its calls at the CPRE tweaks (`twCalls_cpre_*`: `0`, `0`,
  `1200`);
* `cost_slotColl_eval`: an evaluation of `slotColl` reads a step cell only at a step slot
  (`stepSlot`), charged by `cpreEvW`; B5 evaluates only at the hypertree's and FORS trees'
  nodes, leaves and roots and at the encodings (`cprePre_ev`, `cpreHandler_ev`, `cprePost_ev`);
* `lenMax_cpreChains`: the chains have at most `chainLength - 1 = 3` steps;
* the truncation's fibers have `2^128` digests (`card_fiber_truncateHash`).

`probAvg_cpreRed_le`: for an adversary of `n` hash calls,
`probAvg ≤ ((n + 1203) √(gradeEta 2^128) + √(4 n · n κ) + √(1203 κ))²`,
`κ = kappaC Digest 2^128`.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

set_option synthInstance.maxSize 2000

namespace Quantum.StdModel.Qrom.SphInst

open Quantum.StdModel Props Quantum.StdModel.Sphincs
open Quantum.Sphincs (Slot Key msgPos)
open Quantum.Qrom.Sphincs (RawPos slotInput SlotPayload SlotInRange)
open Common (QueryCostAtMost isWeightBound_pure isWeightBound_query isWeightBound_map)
open Quantum.StdModel.Qrom.CpreQ (CellInj stepW stepCells redW lenMax kappaC
  probAvg_cpre_slRed_le)

/-! ## Weights -/

theorem queryCostAtMost_zero {ι α : Type} {spec : OracleSpec.{0, 0} ι}
    (oa : OracleComp spec α) : QueryCostAtMost oa (fun _ ↦ 0) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isWeightBound_pure _ _ _
  | query_bind t k ih => exact (Common.isWeightBound_query_bind_iff _ _ _ _).mpr ⟨le_rfl, ih⟩

/-- **Bounds add along the weights.** -/
theorem queryCostAtMost_add_weight {ι α : Type} {spec : OracleSpec.{0, 0} ι}
    {oa : OracleComp spec α} {w₁ w₂ : ι → ℕ} {a b : ℕ} (h₁ : QueryCostAtMost oa w₁ a)
    (h₂ : QueryCostAtMost oa w₂ b) : QueryCostAtMost oa (fun t ↦ w₁ t + w₂ t) (a + b) := by
  induction oa using OracleComp.inductionOn generalizing a b with
  | pure x => exact isWeightBound_pure _ _ _
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h₁ h₂ ⊢
    obtain ⟨h₁a, h₁b⟩ := h₁
    obtain ⟨h₂a, h₂b⟩ := h₂
    exact ⟨by omega, fun u ↦ (ih u (h₁b u) (h₂b u)).mono (by omega)⟩

/-! ## The step cells -/

/-- **Distinct steps or values have distinct cells.** -/
theorem sph_cellInj (P : PublicParameter) : CellInj cpreChains P := by
  intro j ν x j' ν' x' hν hν' h
  have e1 := Quantum.StdModel.Qrom.encodeInput_eq_cellOf
    (cpreStep_lengthLe () P (cpreChains.tweak j ν) x)
  have e2 := Quantum.StdModel.Qrom.encodeInput_eq_cellOf
    (cpreStep_lengthLe () P (cpreChains.tweak j' ν') x')
  exact cpreStep_layout_inj P hν hν' (Quantum.Qrom.encodeInput_injective e1
    (e2.trans (congrArg some h.symm)))

/-- The step slots: the chain steps and the FORS leaves. -/
def stepSlot : Slot → Bool
  | .chain .. | .forsLeaf .. => true
  | _ => false

/-- A step's input is the slot input of a step slot. -/
theorem cpreLayout_eq (P : PublicParameter) (j : CpreJ) (ν : ℕ) (y : Digest) :
    ∃ s d, cpreChains.step.layout () P (cpreChains.tweak j ν) y = slotInput (pubKey P) 0 s d ∧
      stepSlot s = true ∧ SlotInRange s := by
  rcases j with ⟨K, i⟩ | ⟨idx, κ, s⟩
  · exact ⟨.chain K.1 K.2.1 K.2.2 i ⟨ν % (chainLength - 1), Nat.mod_lt _ (by decide)⟩, y, rfl,
      rfl, trivial⟩
  · exact ⟨.forsLeaf idx κ s, y, rfl, rfl, trivial⟩

theorem encodeInput_stepSlot {P : PublicParameter} {j : CpreJ} {ν : ℕ} {y : Digest} {s : Slot}
    {d : SlotPayload s}
    (he : cpreChains.step.layout () P (cpreChains.tweak j ν) y = slotInput (pubKey P) 0 s d) :
    Quantum.Qrom.encodeInput (slotInput (pubKey P) 0 s d) =
      some (Quantum.StdModel.Qrom.CpreQ.cellAt cpreChains P j ν y) := by
  rw [← he]
  exact Quantum.StdModel.Qrom.encodeInput_eq_cellOf (cpreStep_lengthLe () P _ y)

/-- A step cell is a cell of a chain step or a FORS leaf. -/
theorem cpreCell_of_mem_stepCells {P : PublicParameter} {z : Quantum.Qrom.HashDomain}
    (hz : z ∈ stepCells cpreChains P) : CpreCell z := by
  obtain ⟨j, ν, y, -, rfl⟩ := hz
  obtain ⟨s, d, he, hs, -⟩ := cpreLayout_eq P j ν y
  refine ⟨P, s, d, ?_, encodeInput_stepSlot he⟩
  cases s <;> simp_all [stepSlot, CpreSlot]

/-- **B5's step-cell reads are among its calls at the CPRE tweaks.** -/
theorem stepW_le_twCellCost (P : PublicParameter) (t : Quantum.Qrom.RomOracles.Domain) :
    stepW (ch := cpreChains) P t ≤ twCellCost CpreCell t := by
  rcases t with _ | z
  · exact le_rfl
  · by_cases hz : z ∈ stepCells cpreChains P
    · simp [stepW, twCellCost, hz, cpreCell_of_mem_stepCells hz]
    · simp [stepW, hz]

theorem stepW_eq_twCellCost (P : PublicParameter) :
    stepW (ch := cpreChains) P = twCellCost (· ∈ stepCells cpreChains P) := by
  funext t
  rcases t with _ | _ <;> rfl

/-! ## Evaluations -/

/-- **The evaluation weight**: one per evaluation at a step slot. -/
def cpreEvW : CpreQ → ℕ
  | .eval l _ _ => if stepSlot l then 1 else 0
  | _ => 0

/-- An evaluation off the step slots reads no step cell. -/
theorem not_mem_stepCells_of_eval {P : PublicParameter} {l t : Slot} {m : SlotPayload l}
    (hl : stepSlot l = false) {c : Quantum.Qrom.HashDomain}
    (hc : Quantum.Qrom.encodeInput (slotColl.layout l P t m) = some c) :
    c ∉ stepCells cpreChains P := by
  rintro ⟨j, ν, y, -, rfl⟩
  obtain ⟨s, d, he, hs, hr⟩ := cpreLayout_eq P j ν y
  have e := Quantum.Qrom.encodeInput_injective hc (encodeInput_stepSlot he)
  change slotLayout l P t m = _ at e
  unfold slotLayout at e
  split_ifs at e with h
  · have hls := congrArg Sigma.fst (sphincs_slotInput_inj (pubKey P) 0 h.2 hr e)
    simp only at hls
    rw [hls, hs] at hl
    exact Bool.noConfusion hl
  · have hlen := congrArg List.length e
    rw [List.length_nil, length_slotInput] at hlen
    cases s <;> simp [slotLen] at hlen

/-- **An evaluation of `slotColl`** reads a step cell only at a step slot. -/
theorem cost_slotColl_eval (P : PublicParameter) (l t : Slot) (m : SlotPayload l) :
    QueryCostAtMost (slotColl.eval romWorld l P t m) (stepW (ch := cpreChains) P)
      (cpreEvW (.eval l t m)) := by
  rw [stepW_eq_twCellCost]
  unfold Props.TwColl.eval
  refine isWeightBound_map _ ((hashQ_twCellCost _ _).mono ?_)
  unfold twInputCost
  split
  · rename_i c hc
    cases hl : stepSlot l
    · simp [cpreEvW, hl, not_mem_stepCells_of_eval hl hc]
    · simp only [cpreEvW, hl]
      split_ifs <;> omega
  · exact Nat.zero_le _

/-- The challenger part of B5's weight: its evaluations at step slots. -/
def evOnly : (romWorld.Oracles + CpreS).Domain → ℕ
  | .inl _ => 0
  | .inr q => cpreEvW q

theorem redW_le_add (P : PublicParameter) :
    ∀ t : Quantum.Qrom.RomOracles.Domain ⊕ CpreQ, redW (ch := cpreChains) P cpreEvW t ≤
      hcallCostOn CpreCell (R' := CpreS) t + evOnly t
  | .inl t => (stepW_le_twCellCost P t).trans (Nat.le_add_right _ _)
  | .inr _ => Nat.le_add_left _ _

/-! ## B5 evaluates off the step slots -/

theorem liftW_evOnly {α : Type} (oa : OracleComp romWorld.Oracles α) :
    QueryCostAtMost (liftW CpreS oa) evOnly 0 :=
  queryCostAtMost_liftW_of romWorld (c := fun _ ↦ 0) (fun _ ↦ le_rfl) (queryCostAtMost_zero oa)

theorem portQ_evOnly (q : CpreQ) (h : cpreEvW q = 0) :
    QueryCostAtMost (portQ romWorld CpreS q) evOnly 0 :=
  (isWeightBound_query evOnly (.inr q)).mono h.le

theorem cpreValQ_ev (j : CpreJ) (μ : ℕ) : QueryCostAtMost (cpreValQ romWorld j μ) evOnly 0 :=
  portQ_evOnly _ rfl

theorem cpreEvQ_ev (l t : Slot) (m : SlotPayload l) (hl : stepSlot l = false) :
    QueryCostAtMost (cpreEvQ romWorld l t m) evOnly 0 :=
  portQ_evOnly _ (by simp [cpreEvW, hl])

theorem cpreAsk_ev (p : RawPos) (t : RawPos → Digest) :
    QueryCostAtMost (cpreAsk romWorld p t) evOnly 0 := by
  cases p with
  | chain l τ e i step =>
    show QueryCostAtMost (cpreChainAsk romWorld l τ e i step) _ 0
    unfold cpreChainAsk
    split
    · exact cpreValQ_ev _ _
    · exact isWeightBound_pure _ _ _
  | leaf => exact cpreEvQ_ev _ _ _ rfl
  | node => exact cpreEvQ_ev _ _ _ rfl
  | forsLeaf => exact cpreValQ_ev _ _
  | forsNode => exact cpreEvQ_ev _ _ _ rfl
  | forsRoots => exact cpreEvQ_ev _ _ _ rfl
  | _ => exact isWeightBound_pure _ _ _

theorem cpreSelFrom_ev (K : Key) (m : Digest) :
    ∀ n c, QueryCostAtMost (cpreSelFrom romWorld K m n c) evOnly 0
  | 0, _ => by
    simp only [cpreSelFrom]
    exact isWeightBound_pure _ _ _
  | n + 1, c => by
    simp only [cpreSelFrom]
    refine ((cpreEvQ_ev _ _ _ rfl).bind (b := 0) fun d ↦ ?_).mono le_rfl
    split
    · exact isWeightBound_pure _ _ _
    · exact cpreSelFrom_ev K m n (c + 1)

theorem cpreOpenQ_ev (sel : Key → Option (EncodingCounter × Encoding))
    (x : Key × ChainIndex × Fin chainLength) :
    QueryCostAtMost (cpreOpenQ romWorld sel x) evOnly 0 := by
  unfold cpreOpenQ
  split
  · split
    · exact cpreValQ_ev _ _
    · exact isWeightBound_pure _ _ _
  · exact isWeightBound_pure _ _ _

theorem cpreStage_ev : QueryCostAtMost (cpreStage romWorld) evOnly 0 := by
  unfold cpreStage cpreSelAll cpreOpenAll
  exact ((buildDig_zero cpreAsk_ev).bind fun tf ↦
    (cpreTab_zero cpreKeys none fun K ↦ cpreSelFrom_ev K
      ((ofDig tf).valuePos (msgPos K)) encodingAttemptLimit 0).bind fun sel ↦
    (cpreTab_zero cprePositions 0 (cpreOpenQ_ev sel)).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono le_rfl

/-- **B5's setup evaluates off the step slots.** -/
theorem cprePre_ev : QueryCostAtMost (cprePre romWorld) evOnly 0 := by
  unfold cprePre cpreRevQ
  exact ((liftW_evOnly _).bind fun _ ↦ cpreStage_ev.bind fun _ ↦ (portQ_evOnly _ rfl).bind
    fun _ ↦ isWeightBound_pure _ _ 0).mono le_rfl

theorem cpreSignIdx_ev (a : CpreData) (sl : SignLog) (fl : List (CpreFJ × Digest))
    (M : Message) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    QueryCostAtMost (cpreSignIdx romWorld a sl fl M idx lv) evOnly 0 := by
  unfold cpreSignIdx
  split
  · exact isWeightBound_pure _ _ _
  · unfold cpreForsQ
    exact ((cpreTab_zero (List.finRange forsTreeCount) 0 fun κ ↦
      cpreValQ_ev (.inr (idx, κ, lv κ)) 0).bind fun _ ↦ isWeightBound_pure _ _ 0).mono le_rfl

/-- **B5's signer makes no evaluation.** -/
theorem cpreHandler_ev (st : CpreSt) (M : Message) :
    QueryCostAtMost (cpreHandler romWorld st M) evOnly 0 := by
  unfold cpreHandler
  exact ((liftW_evOnly _).bind fun _ ↦ (liftW_evOnly _).bind fun _ ↦
    cpreSignIdx_ev _ _ _ _ _ _).mono le_rfl

/-- **B5's output makes no evaluation.** -/
theorem cprePost_ev (a : CpreData) (f : Forgery) (st : CpreSt) :
    QueryCostAtMost (cprePost romWorld a f st) evOnly 0 := by
  unfold cprePost
  exact (recVerify_mapM_tw (w := fun _ ↦ 0) (c := Kinds.const 0)
    (fun l ↦ liftW_evOnly (romWorld.hash l))
    (fun _ _ _ _ ↦ (queryCostAtMost_zero _).mono (Nat.zero_le _))
    (fun rv os ↦ cpreOut a st.2.2 (cpreLookup rv.2 os)) a.pk f.message f.signature).mono
      (by simp [verifyW_const])

/-! ## The bound -/

theorem card_trunc_fiber_le (o : Digest) :
    (Finset.univ.filter fun y : HashOutput ↦ cpreChains.step.trunc y = o).card ≤ 2 ^ 128 := by
  have h2 : Fintype.card (BitVec 128) = 2 ^ 128 := by
    rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  rw [← Fintype.card_subtype]
  exact ((card_fiber_truncateHash o).trans h2).le

theorem lenMax_cpreChains : lenMax cpreChains = 3 := by
  refine le_antisymm (Finset.sup_le fun j _ ↦ ?_)
    (Finset.le_sup (f := cpreChains.len) (Finset.mem_univ
      (Sum.inl ((⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩), ⟨0, by decide⟩))))
  rcases j with _ | _
  · exact le_rfl
  · exact (by decide : 1 ≤ 3)

-- A bound on a reduction is otherwise unfolded by `whnf`.
attribute [local irreducible] QueryCostAtMost

/-- **The leanSPHINCS CPRE game in the QROM (B5)**: for an adversary of `n` hash calls (and any
number `k` of signing requests), B5 wins with probability at most
`((n + 1203) √(gradeEta 2^128) + √(4 n · n κ) + √(1203 κ))²`, `κ = kappaC Digest 2^128`: B5
reads `1200` step cells in its output and the decision walks at most `3` steps. -/
theorem probAvg_cpreRed_le (A : SAdv romWorld) {n k : ℕ}
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hk : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) k) :
    romWorld.probAvg ((cpre romWorld cpreChains slotColl).game (cpreRed romWorld A)) ≤
      (((n + 1203 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ) +
        (4 * (n * (n * kappaC Digest (2 ^ 128)))) ^ (2⁻¹ : ℝ) +
        (((1203 : ℕ) : ℝ≥0∞) * kappaC Digest (2 ^ 128)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := probAvg_cpre_slRed_le (ch := cpreChains) slotColl
    (fun P _ _ x _ ↦ cpreStep_lengthLe () P _ x) sph_cellInj card_trunc_fiber_le
    (fun _ ↦ cprePre romWorld) (fun _ a ↦ A a.pk) (fun _ a ↦ (a, [], []))
    (fun _ ↦ cpreHandler romWorld) (fun _ ↦ cprePost romWorld) (fun _ ↦ cpreEvW)
    (c₀ := 0) (m := 0) (c₁ := 1200) (fun P l t m ↦ cost_slotColl_eval P l t m)
    (fun P ↦ (queryCostAtMost_add_weight twCalls_cpre_pre cprePre_ev).mono_weight
      (redW_le_add P))
    (fun P st M ↦ (queryCostAtMost_add_weight (twCalls_cpre_sign st M)
      (cpreHandler_ev st M)).mono_weight (redW_le_add P))
    (fun P a f st ↦ (queryCostAtMost_add_weight (twCalls_cpre_post a f st)
      (cprePost_ev a f st)).mono_weight (redW_le_add P))
    (fun a ↦ hn a.pk) (fun a ↦ hk a.pk)
  simp only [lenMax_cpreChains, zero_mul, zero_add] at h
  exact h

end Quantum.StdModel.Qrom.SphInst

end
