module

public import Quantum.StdModel.Qrom.EncSaltBound
public import Quantum.StdModel.Qrom.EncSaltLive
public import Quantum.StdModel.Qrom.XmssTcr2

@[expose] public section

/-!
# EncTCR$ in the QROM at leanXMSS B2

The obligations of the EncTCR$ bound (`Quantum.StdModel.Qrom.EncSalt`) at leanXMSS's instance
`xmssEnc` played by B2 (`encRed`).

* **The instance** (`xmssEnc_gSep`, `xmssEnc_layout_injective`, `card_truncateHash_fiber_le_enc`,
  `xmssEnc_shift_injective`, `xmssEnc_shift_distinct`): an encoding input determines its
  parameter, tweak, message and salt; `2^128` digests per truncation; the salts of a base are
  distinct within the trial limit, and each determines the base.
* **Encoding cells** (`isG_xmssEnc_msgSlot`): an encoding cell names a message-digest slot.
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props Common
open Quantum.StdModel.Qrom.Tcr (GSep GCell IsG Mem rl)
open Quantum.Qrom.Xmss (MsgBytes)

/-! ## The instance -/

theorem xmssEnc_layout_prefix (P : PublicParameter) (t : Layer × KeyIndex)
    (d : MsgBytes × Randomizer) :
    ∃ rest, xmssEnc.hash.layout () P t d = littleEndianBytes 16 P ++ rest :=
  ⟨_, rfl⟩

/-- **An encoding input determines its parameter and tweak.** -/
theorem xmssEnc_gSep : GSep xmssEnc.hash Qrom.EncSalt.G := by
  intro _ P t m _ P' t' m' _ h
  obtain ⟨r, hr⟩ := xmssEnc_layout_prefix P t m
  obtain ⟨r', hr'⟩ := xmssEnc_layout_prefix P' t' m'
  have hP : P' = P := xmss_param_eq_of_prefix (hr'.symm.trans (h.trans hr))
  subst hP
  have hs := congrArg Sigma.fst (xmss_slotInput_inj (s := .msg t'.1 t'.2) (s' := .msg t.1 t.2)
    P' trivial trivial h)
  injection hs with h1 h2
  exact ⟨rfl, Prod.ext h1 h2⟩

/-- **An encoding input determines its message and salt.** -/
theorem xmssEnc_layout_injective (P : PublicParameter) (t : Layer × KeyIndex) :
    (xmssEnc.hash.layout () P t).Injective :=
  fun d d' h ↦ Qrom.Xmss.slotInput_injective P (.msg t.1 t.2) d d' h

open scoped Classical in
/-- **`2^128` digests per truncation**, decided classically. -/
theorem card_truncateHash_fiber_le_enc (o : Digest) :
    (Finset.univ.filter fun y : HashOutput ↦ xmssEnc.hash.trunc y = o).card ≤ 2 ^ 128 := by
  convert card_truncateHash_fiber_le o using 4
  exact rfl

/-- **Each salt determines its base.** -/
theorem xmssEnc_shift_injective (c : ℕ) : Function.Injective fun r0 ↦ xmssEnc.shift r0 c :=
  fun _ _ h ↦ add_right_cancel (h : _ + BitVec.ofNat digestBits c = _ + BitVec.ofNat digestBits c)

/-- **The salts of a base are distinct within the trial limit.** -/
theorem xmssEnc_shift_distinct (r0 : Randomizer) (c c' : ℕ) (hc : c < xmssEnc.limit)
    (hc' : c' < xmssEnc.limit) (h : xmssEnc.shift r0 c = xmssEnc.shift r0 c') : c = c' := by
  have h' : BitVec.ofNat digestBits c = BitVec.ofNat digestBits c' :=
    add_left_cancel (h : r0 + BitVec.ofNat digestBits c = r0 + BitVec.ofNat digestBits c')
  have hl : xmssEnc.limit = 2 ^ 32 := rfl
  have h2 := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
  have hd : digestBits = 128 := rfl
  rw [hd] at h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  exact h2

/-! ## Encoding cells -/

/-- **An encoding cell names a message-digest slot.** -/
theorem isG_xmssEnc_msgSlot {z : Qrom.HashDomain} (h : IsG xmssEnc.hash Qrom.EncSalt.G z) :
    (Qrom.Xmss.slotOf z).any msgSlots = true := by
  obtain ⟨P, t, _l, d, _hG, hz⟩ := h
  have h2 := Qrom.Xmss.encodeInput_slotInput P (.msg t.1 t.2) d
  have hzc : z = Qrom.Xmss.cell P (.msg t.1 t.2) d := Option.some.inj (hz.symm.trans h2)
  subst hzc
  rw [Qrom.Xmss.slotOf_cell (s := .msg t.1 t.2) P trivial d]
  rfl

open Quantum.StdModel.Qrom.EncSalt (costR costA)

open scoped Classical in
/-- The reduction's reads of encoding cells are among its message-digest queries. -/
theorem costR_le_msgSlots (t : (romWorld.Oracles + EncSpec).Domain) :
    costR xmssEnc t ≤ sumCost (slotCost msgSlots) t := by
  rcases t with (n | z) | q
  · exact le_rfl
  · simp only [costR, sumCost, slotCost]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (isG_xmssEnc_msgSlot h1) h2
    · exact Nat.zero_le _
    · exact le_rfl
  · exact le_rfl

/-- One message digest per digest, nothing else. -/
theorem kindBound_msgSlots : KindBound romWorld.hash (slotCost msgSlots) ⟨0, 0, 0, 1⟩ :=
  slotCost_kinds msgSlots _ (fun _ _ _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ le_rfl)
    fun _ _ ↦ le_rfl

/-- A computation lifted to the left of a sum weighs nothing under a weight free on the left. -/
theorem cost_liftComp_inl_zero {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} ι'} {α : Type} (oa : OracleComp spec α) (w : ι ⊕ ι' → ℕ)
    (hw : ∀ t, w (.inl t) = 0) : QueryCostAtMost (liftComp oa (spec + spec')) w 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isWeightBound_pure _ _ _
  | query_bind t k ih =>
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    change QueryCostAtMost (liftM ((spec + spec').query (.inl t)) >>= fun u ↦
      liftComp (k u) (spec + spec')) w 0
    exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨(hw t).le, fun u ↦ by
      rw [hw t, Nat.zero_sub]
      exact ih u⟩

/-- A world computation, lifted, makes no challenger query. -/
theorem cost_liftL_zero {α : Type} (oa : OracleComp romWorld.Oracles α)
    (w : (romWorld.Oracles + EncSpec).Domain → ℕ) (hw : ∀ t, w (.inl t) = 0) :
    QueryCostAtMost (liftL (s₂ := EncSpec) oa) w 0 :=
  cost_liftComp_inl_zero oa w hw

/-- **B2's setup reads no encoding cell.** -/
theorem cost_encPre_costR (P : PublicParameter) :
    QueryCostAtMost (encPre romWorld P) (costR xmssEnc) 0 := by
  have h := cost_encPre kindBound_msgSlots (slotCost_coinsFree msgSlots) P
  have h0 : encPreCost (⟨0, 0, 0, 1⟩ : Kinds) = 0 := by
    simp only [encPreCost, treeNodeCost, keyLeafCost, hKinds, mul_zero, add_zero]
  rw [h0] at h
  exact h.mono_weight costR_le_msgSlots

/-- **B2's output reads at most two encoding cells.** -/
theorem cost_encPost_costR (P : PublicParameter) (s0 : Starts × Digest) (F : Forgery)
    (s : EncSt) : QueryCostAtMost (encPost romWorld P s0 F s) (costR xmssEnc) 2 := by
  have h := cost_encPost kindBound_msgSlots P s0 F s
  have h2 : encPostCost (⟨0, 0, 0, 1⟩ : Kinds) = 2 := by
    simp only [encPostCost, layerRootCost, mul_zero, add_zero]
  rw [h2] at h
  exact h.mono_weight costR_le_msgSlots

/-- B2's setup makes no challenger query. -/
theorem cost_encPre_ans (P : PublicParameter) :
    QueryCostAtMost (encPre romWorld P) (Qrom.ansCost (R' := EncSpec)) 0 :=
  cost_liftL_zero _ _ fun _ ↦ rfl

/-- B2's output makes no challenger query. -/
theorem cost_encPost_ans (P : PublicParameter) (s0 : Starts × Digest) (F : Forgery)
    (s : EncSt) : QueryCostAtMost (encPost romWorld P s0 F s) (Qrom.ansCost (R' := EncSpec)) 0 :=
  cost_liftL_zero _ _ fun _ ↦ rfl

/-! ## The live budgets of B2's setup and output -/

open Quantum.StdModel.Qrom.EncSalt (βS mem0 upd)
open Quantum.StdModel.Qrom (LiveRedRun stepRd)
open Quantum.StdModel.Qrom.EncSalt.Live (liveRedRun_βS_le βS_mem0)

/-- **B2's setup marks no encoding cell** on its live runs. -/
theorem βS_encPre_live (P : PublicParameter) {a : (Starts × Digest) × QueryLog EncSpec}
    {μ' : Option Mem}
    (h : LiveRedRun rl (upd xmssEnc) ((encTcrSalt romWorld xmssEnc).answer P)
      (encPre romWorld P) [] (some mem0) a μ') :
    ∀ m', μ' = some m' → βS xmssEnc m' ≤ 0 := by
  intro m' hm'
  have h1 := liveRedRun_βS_le xmssEnc _ (encPre romWorld P) (cost_encPre_costR P)
    (cost_encPre_ans P) h mem0 m' rfl hm'
  have h2 := βS_mem0 xmssEnc
  omega

/-- **B2's output marks at most two encoding cells** on its live runs. -/
theorem βS_encPost_live (P : PublicParameter) (s0 : Starts × Digest) (F : Forgery) (s : EncSt)
    {log : QueryLog EncSpec} {μ : Option Mem} {r : EncOut × QueryLog EncSpec}
    {μ' : Option Mem}
    (h : LiveRedRun rl (upd xmssEnc) ((encTcrSalt romWorld xmssEnc).answer P)
      (encPost romWorld P s0 F s) log μ r μ') :
    ∀ m m', μ = some m → μ' = some m' → βS xmssEnc m' ≤ βS xmssEnc m + 2 :=
  liveRedRun_βS_le xmssEnc _ _ (cost_encPost_costR P s0 F s) (cost_encPost_ans P s0 F s) h

end Quantum.StdModel.Xmss

end
