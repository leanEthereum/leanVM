module

public import Quantum.StdModel.Sphincs.PropsInRed
public import Quantum.StdModel.Qrom.Prf
public import Quantum.StdModel.Sphincs.CostsRedA
public import Quantum.StdModel.Sphincs.CostsRedB

@[expose] public section

/-!
# leanSPHINCS property instances in the QROM

The QROM bounds of the generic property games (`Quantum.StdModel.Qrom.{Prf,Tcr,Cpre,EncTcr}`)
at the leanSPHINCS instances of `Quantum.StdModel.Sphincs.Instances`, for every adversary.

Theorem 2 (`Quantum.StdModel.Sphincs.sphincs_suf_le_props`) holds at every table of `romWorld`.
The QROM winning probability of an adversary is the average over the tables `H` of its winning
probabilities at `H` (`winProb_qrom_eq_avg`), and the QROM scheme `sphincsRom` is the scheme of
Theorem 2 over `romWorld` (`sphincsRom = sphincsOver romWorld.hash`). Averaging Theorem 2 bounds
the QROM winning probability by the averages of the six property terms
(`winProb_sphincsRom_le_avg`).
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Qrom.SphInst

open Quantum.StdModel Props Quantum.StdModel.Sphincs

/-- **The average over the tables of `romWorld`** of a real function. -/
noncomputable def romAvg (f : romWorld.Tab → ℝ) : ℝ :=
  ∑ H, (Fintype.card romWorld.Tab : ℝ)⁻¹ * f H

/-! ## Layout obligations of the instances -/

open Quantum.Sphincs (Slot) in
open Quantum.Qrom.Sphincs (SlotPayload SlotInRange slotInput) in
/-- A slot input in range determines its payload. -/
theorem slotInput_payload_inj (P : PublicParameter) {s : Slot} (hs : SlotInRange s)
    {m m' : SlotPayload s} (h : slotInput (pubKey P) 0 s m = slotInput (pubKey P) 0 s m') :
    m = m' :=
  eq_of_heq (Sigma.mk.inj (sphincs_slotInput_inj (pubKey P) 0 hs hs h)).2

/-- The bytes of a target message determine it. -/
theorem tcrBytes_injective (l : TcrFn) : Function.Injective (tcrBytes l) := by
  cases l with
  | leaf => exact Quantum.Qrom.Sphincs.digestsPayload_injective
  | forsRoots => exact Quantum.Qrom.Sphincs.digestsPayload_injective
  | node =>
    intro m m' h
    obtain ⟨h1, h2⟩ := Quantum.Qrom.Sphincs.nodePayload_injective h
    exact Prod.ext h1 h2
  | forsNode =>
    intro m m' h
    obtain ⟨h1, h2⟩ := Quantum.Qrom.Sphincs.nodePayload_injective h
    exact Prod.ext h1 h2

/-- **The SM-TCR targets' inputs determine their messages** at every function and tweak. -/
theorem tcrColl_layout_injective (l : TcrFn) (P : PublicParameter) (t : Quantum.Sphincs.Slot) :
    Function.Injective (tcrColl.layout l P t) := by
  intro m m' h
  have junk : littleEndianBytes 16 P ++ tcrBytes l m = littleEndianBytes 16 P ++ tcrBytes l m' →
      m = m' := fun e ↦ tcrBytes_injective l (List.append_cancel_left e)
  change tcrLayout P l t m = tcrLayout P l t m' at h
  cases l <;> cases t <;> simp only [tcrLayout] at h junk ⊢ <;>
    first
    | exact junk h
    | exact slotInput_payload_inj P (by exact trivial) h
    | (split_ifs at h with hr
       · exact slotInput_payload_inj P hr h
       · exact junk h)

/-- A counter below `encodingAttemptLimit` is determined by its 32-bit encoding. -/
theorem ofNat_counter_inj {c c' : ℕ} (hc : c < encodingAttemptLimit)
    (hc' : c' < encodingAttemptLimit)
    (h : BitVec.ofNat counterBits c = BitVec.ofNat counterBits c') : c = c' := by
  have e := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at e
  rwa [Nat.mod_eq_of_lt (by simpa [counterBits, encodingAttemptLimit] using hc),
    Nat.mod_eq_of_lt (by simpa [counterBits, encodingAttemptLimit] using hc')] at e

/-- **The EncTCR+C inputs determine the message and the counter** at every tweak, for counters
below `encodingAttemptLimit`. -/
theorem encHash_layout_injOn (P : PublicParameter) (t : Quantum.Sphincs.Slot) :
    Set.InjOn (encCtr.hash.layout () P t) {x | x.2 < encodingAttemptLimit} := by
  rintro ⟨m, c⟩ hc ⟨m', c'⟩ hc' h
  change encLayout P t (m, c) = encLayout P t (m', c') at h
  cases t
  case enc a b d =>
    have e := slotInput_payload_inj P (s := .enc a b d) trivial h
    obtain ⟨h1, h2⟩ := Prod.mk.inj e
    exact Prod.ext h1 (ofNat_counter_inj hc hc' h2)
  all_goals
    obtain ⟨h1, h2⟩ := List.append_inj (List.append_cancel_left (by
      simpa only [encLayout, List.append_assoc] using h)) (by simp [littleEndianBytes])
    exact Prod.ext (Quantum.Sphincs.littleEndianBytes_injective 16 h1)
      (ofNat_counter_inj hc hc' (Quantum.Sphincs.bigEndianBytes_injective 4 h2))

/-- **The CPRE step inputs on the chains determine the step and the value**: two step inputs of
the chains' tweaks with the same bytes are the same step of the same chain on the same value. -/
theorem cpreStep_layout_inj (P : PublicParameter) {j j' : CpreJ} {μ μ' : ℕ}
    (hμ : μ < cpreChains.len j) (hμ' : μ' < cpreChains.len j') {m m' : Digest}
    (h : cpreChains.step.layout () P (cpreChains.tweak j μ) m =
      cpreChains.step.layout () P (cpreChains.tweak j' μ') m') :
    j = j' ∧ μ = μ' ∧ m = m' := by
  have hs : ∀ (j : CpreJ) (μ : ℕ) (m : Digest), ∃ d,
      cpreChains.step.layout () P (cpreChains.tweak j μ) m =
        Quantum.Qrom.Sphincs.slotInput (pubKey P) 0 (cpreChains.tweak j μ) d ∧
        HEq d m := by
    rintro (⟨K, i⟩ | ⟨idx, κ, s⟩) μ m <;> exact ⟨m, rfl, HEq.rfl⟩
  obtain ⟨d, hd, hdm⟩ := hs j μ m
  obtain ⟨d', hd', hdm'⟩ := hs j' μ' m'
  have e := sphincs_slotInput_inj (pubKey P) 0 (s := cpreChains.tweak j μ)
    (s' := cpreChains.tweak j' μ') (by rcases j with _ | _ <;> trivial)
    (by rcases j' with _ | _ <;> trivial) (hd.symm.trans (h.trans hd'))
  obtain ⟨rfl, rfl⟩ := cpreChains_distinctTweaks j μ j' μ' hμ hμ' (Sigma.mk.inj e).1
  exact ⟨rfl, rfl, eq_of_heq (hdm.symm.trans ((Sigma.mk.inj e).2.trans hdm'))⟩

/-- **A slot input of an in-range tweak determines the tweak** among the inputs of a collection
of shaped inputs. -/
theorem tweak_eq_of_shaped {Fn : Type} {Msg : Fn → Type}
    (C : TwColl PublicParameter Quantum.Sphincs.Slot Fn Msg Digest)
    (hC : ∀ l P t m, SlotShaped P t (C.layout l P t m)) {P : PublicParameter}
    {t : Quantum.Sphincs.Slot} (ht : Quantum.Qrom.Sphincs.SlotInRange t)
    {d : Quantum.Qrom.Sphincs.SlotPayload t} {l' : Fn} {t' : Quantum.Sphincs.Slot} {m' : Msg l'}
    (h : C.layout l' P t' m' = Quantum.Qrom.Sphincs.slotInput (pubKey P) 0 t d) : t' = t := by
  rcases hC l' P t' m' with ⟨d', ht', hd'⟩ | ⟨hn, -⟩
  · exact congrArg Sigma.fst (sphincs_slotInput_inj (pubKey P) 0 ht' ht (hd'.symm.trans h))
  · exact absurd h.symm (slotInput_ne_of_length fun hm ↦ hn (List.mem_cons_of_mem _ hm))

/-- At a target tweak, the target input is the tweak's slot input. -/
theorem tcrColl_layout_slot {l : TcrFn} {t : Quantum.Sphincs.Slot} (ht : TcrTwIn l t)
    (P : PublicParameter) (m : TcrMsg l) :
    Quantum.Qrom.Sphincs.SlotInRange t ∧
      ∃ d, tcrColl.layout l P t m = Quantum.Qrom.Sphincs.slotInput (pubKey P) 0 t d := by
  cases l <;> cases t <;> simp only [TcrTwIn] at ht
  · exact ⟨trivial, m, rfl⟩
  · exact ⟨ht, m, ite_eq_left ht⟩
  · exact ⟨ht, m, ite_eq_left ht⟩
  · exact ⟨trivial, m, rfl⟩

/-- **SM-TCR tweak separation at the target tweaks**: an input of `tcrColl` equal to a target
input at a target tweak has the same tweak. -/
theorem tcrColl_tweak_eq {l : TcrFn} {t : Quantum.Sphincs.Slot} (ht : TcrTwIn l t)
    (P : PublicParameter) (m : TcrMsg l) {l' : TcrFn} {t' : Quantum.Sphincs.Slot} {m' : TcrMsg l'}
    (h : tcrColl.layout l' P t' m' = tcrColl.layout l P t m) : t' = t := by
  obtain ⟨hr, d, hd⟩ := tcrColl_layout_slot ht P m
  exact tweak_eq_of_shaped tcrColl (fun l P t m ↦ tcrLayout_shaped P l t m) hr (h.trans hd)

/-- Every input of `tcrColl` starts with the bytes of its public parameter. -/
theorem tcrColl_layout_prefix (l : TcrFn) (P : PublicParameter) (t : Quantum.Sphincs.Slot)
    (m : TcrMsg l) : ∃ rest, tcrColl.layout l P t m = littleEndianBytes 16 P ++ rest := by
  change ∃ rest, tcrLayout P l t m = _
  cases l <;> cases t <;> simp only [tcrLayout] <;> (try split) <;> exact ⟨_, rfl⟩

/-- Inputs starting with the bytes of two public parameters agree on the parameter. -/
theorem param_eq_of_prefix {P P' : PublicParameter} {r r' : HashInput}
    (h : littleEndianBytes 16 P' ++ r' = littleEndianBytes 16 P ++ r) : P' = P :=
  Quantum.Sphincs.littleEndianBytes_injective 16
    (List.append_inj h (by simp [littleEndianBytes])).1

/-- **SM-TCR separation at the target tweaks, with the parameter**: an input of `tcrColl` under
any parameter equal to a target input at a target tweak has the same parameter and tweak. -/
theorem tcrColl_param_tweak_eq {l : TcrFn} {t : Quantum.Sphincs.Slot} (ht : TcrTwIn l t)
    (P : PublicParameter) (m : TcrMsg l) {l' : TcrFn} {P' : PublicParameter}
    {t' : Quantum.Sphincs.Slot} {m' : TcrMsg l'}
    (h : tcrColl.layout l' P' t' m' = tcrColl.layout l P t m) : P' = P ∧ t' = t := by
  obtain ⟨r, hr⟩ := tcrColl_layout_prefix l P t m
  obtain ⟨r', hr'⟩ := tcrColl_layout_prefix l' P' t' m'
  obtain rfl := param_eq_of_prefix (hr'.symm.trans (h.trans hr))
  exact ⟨rfl, tcrColl_tweak_eq ht _ m h⟩

/-- Every input of the encoding starts with the bytes of its public parameter. -/
theorem encHash_layout_prefix (P : PublicParameter) (t : Quantum.Sphincs.Slot)
    (x : Digest × ℕ) : ∃ rest, encCtr.hash.layout () P t x = littleEndianBytes 16 P ++ rest := by
  change ∃ rest, encLayout P t x = _
  cases t <;> simp only [encLayout] <;> exact ⟨_, List.append_assoc _ _ _⟩

/-- **EncTCR+C separation at the target tweaks, with the parameter**: an input of the encoding
under any parameter equal to an input at an encoding slot has the same parameter and tweak. -/
theorem encHash_param_tweak_eq {t : Quantum.Sphincs.Slot} (ht : EncTwIn t) (P : PublicParameter)
    (x : Digest × ℕ) {P' : PublicParameter} {t' : Quantum.Sphincs.Slot} {x' : Digest × ℕ}
    (h : encCtr.hash.layout () P' t' x' = encCtr.hash.layout () P t x) : P' = P ∧ t' = t := by
  obtain ⟨r, hr⟩ := encHash_layout_prefix P t x
  obtain ⟨r', hr'⟩ := encHash_layout_prefix P' t' x'
  obtain rfl := param_eq_of_prefix (hr'.symm.trans (h.trans hr))
  refine ⟨rfl, ?_⟩
  cases t <;> simp only [EncTwIn] at ht
  exact tweak_eq_of_shaped encCtr.hash (fun _ P t x ↦ encLayout_shaped P t x) (by exact trivial)
    h

/-- The prefix and suffix lengths of the KIM formats: `11` and `1` for `S1`, `S2`, `48` and `0`
for `S3`. -/
theorem kimFmt_lengths (x : KimDom) :
    ((kimFmt x).1.length = 11 ∧ (kimFmt x).2.length = 1) ∨
      ((kimFmt x).1.length = 48 ∧ (kimFmt x).2.length = 0) := by
  cases x with
  | publicSeed => exact Or.inl ⟨rfl, rfl⟩
  | prfKey => exact Or.inl ⟨rfl, rfl⟩
  | prf P d =>
    refine Or.inr ⟨?_, rfl⟩
    simp [kimFmt, littleEndianBytes, Quantum.Sphincs.length_toBytes]

/-- **Per-key cell injectivity of KIM-PRF**: under a fixed key, distinct formats give distinct
inputs. -/
theorem kim_cellInjective (K : MasterSeed) :
    Function.Injective fun x : KimDom ↦ (kimFmt x).1 ++ littleEndianBytes 32 K ++ (kimFmt x).2 := by
  intro x y h
  have hl := congrArg List.length h
  simp only [List.length_append] at hl
  have ha : (kimFmt x).1.length = (kimFmt y).1.length := by
    rcases kimFmt_lengths x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases kimFmt_lengths y with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [ha])
  exact kimFmt_injective (Prod.ext (List.append_inj h1 ha).1 h2)

/-- **Per-key cell injectivity of PRF_msg**: under a fixed key, distinct inputs of the message
domain give distinct inputs. -/
theorem prfMsg_cellInjective (K : HashOutput) : Function.Injective
    fun x : MsgDom ↦ ([] : HashInput) ++ littleEndianBytes 32 K ++ msgBytes x := by
  intro x y h
  have h' := List.append_cancel_left h
  unfold msgBytes framedMessage at h'
  obtain ⟨h1, h2⟩ := List.append_inj h' (by simp [littleEndianBytes])
  obtain ⟨-, h3⟩ := List.append_inj h2 (by simp)
  exact Prod.ext (Quantum.Sphincs.littleEndianBytes_injective 16 h1)
    (Quantum.Sphincs.littleEndianBytes_injective 32 h3)

/-! ## KIM-PRF and PRF_msg in the QROM -/

theorem card_masterSeed : Fintype.card MasterSeed = 2 ^ 256 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem card_hashOutput' : Fintype.card HashOutput = 2 ^ 256 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-- The KIM inputs of one byte string under the keys number at most two: one per prefix
length. -/
theorem card_filter_kimInput_kimFmt (l : HashInput) :
    (Finset.univ.filter fun K : MasterSeed ↦
      ∃ x, kimInput kimFmt (littleEndianBytes 32) K x = l).card ≤ 2 := by
  have hsub : ∀ x, (kimFmt x).1.length ∈ ({11, 48} : Finset ℕ) := fun x ↦ by
    rcases kimFmt_lengths x with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h2 : ({11, 48} : Finset ℕ).card = 2 := rfl
  refine (card_filter_kimInput_le kimFmt (littleEndianBytes 32)
    (Quantum.Sphincs.littleEndianBytes_injective 32) (n := 32) (fun _ ↦ by simp [littleEndianBytes])
    l).trans (h2 ▸ Finset.card_le_card (Finset.image_subset_iff.mpr fun x _ ↦ hsub x))

/-- **KIM-PRF under `SK.seed` in the QROM** (formats S1, S2, S3), for every adversary with `q`
hash calls: the averaged advantage is at most `4 q √(2 / 2^256)`. -/
theorem leanSphincs_kimPrf_qrom (B : Adversary romWorld (KimDom →ₒ HashOutput) Unit Bool) {q : ℕ}
    (hB : ∀ p, IFreeM.IsChargeBound (B p) (cmdCharge hashCharge) q) :
    |romAvg fun H ↦ kimPrfAdv romWorld (Key := MasterSeed) kimFmt (littleEndianBytes 32) kimTrunc
      H B| ≤ 4 * q * Real.sqrt (2 / 2 ^ 256) := by
  have h := abs_avg_kimPrfAdv_le kimFmt (littleEndianBytes 32) kimTrunc kim_lengthLe
    kim_cellInjective card_filter_kimInput_kimFmt B hB
  rw [card_masterSeed] at h
  exact_mod_cast h

/-- **PRF_msg under `SK.prf` in the QROM**, for every adversary with `q` hash calls: the averaged
advantage is at most `4 q √(1 / 2^256)`. -/
theorem leanSphincs_prfMsg_qrom (B : Adversary romWorld (MsgDom →ₒ Digest) Unit Bool) {q : ℕ}
    (hB : ∀ p, IFreeM.IsChargeBound (B p) (cmdCharge hashCharge) q) :
    |romAvg fun H ↦ prfMsgAdv romWorld (Key := HashOutput) msgBytes (littleEndianBytes 32)
      truncateHash H B| ≤ 4 * q * Real.sqrt (1 / 2 ^ 256) := by
  have hbytes : Function.Injective msgBytes := fun x y h ↦
    prfMsg_cellInjective 0 (by simp only [List.nil_append, h])
  have h := abs_avg_prfMsgAdv_le msgBytes (littleEndianBytes 32) truncateHash prfMsg_lengthLe
    hbytes (Quantum.Sphincs.littleEndianBytes_injective 32) (n := 32)
    (fun _ ↦ by simp [littleEndianBytes]) B hB
  rw [card_hashOutput'] at h
  exact_mod_cast h

/-- **The KIM-PRF term of Theorem 2 in the QROM**: B1 makes `A`'s `q` hash calls plus its honest
work, `273410 + 12886291206` per signing request `+ 879`. -/
theorem leanSphincs_kimPrf_B1_qrom (A : SAdv romWorld) {q signs : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
    (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) signs) :
    |romAvg fun H ↦ kimPrfAdv romWorld (Key := MasterSeed) kimFmt (littleEndianBytes 32) kimTrunc
      H (B1 romWorld A)| ≤
      4 * ((273410 + ((q + 12886291206 * signs) + 879) : ℕ) : ℝ) * Real.sqrt (2 / 2 ^ 256) := by
  have h := isChargeBound_B1_hash hashCostLe_romWorld A hq hs
  simp only [Nat.mul_one] at h
  exact leanSphincs_kimPrf_qrom (B1 romWorld A) fun _ ↦ h

/-- **The PRF_msg term of Theorem 2 in the QROM**: B2 makes `A`'s `q` hash calls plus its
honest work, `273410 + 12886291206` per signing request `+ 879`. -/
theorem leanSphincs_prfMsg_B2_qrom (A : SAdv romWorld) {q signs : ℕ}
    (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
    (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) signs) :
    |romAvg fun H ↦ prfMsgAdv romWorld (Key := HashOutput) msgBytes (littleEndianBytes 32)
      truncateHash H (B2 romWorld A)| ≤
      4 * ((273410 + ((q + 12886291206 * signs) + 879) : ℕ) : ℝ) * Real.sqrt (1 / 2 ^ 256) := by
  have h := isChargeBound_B2_hash hashCostLe_romWorld A hq hs
  simp only [Nat.mul_one] at h
  exact leanSphincs_prfMsg_qrom (B2 romWorld A) fun _ ↦ h

/-- The winning probability at a fixed table is at most `1`. -/
theorem winProbAt_le_one {PK Req Resp F Seed SK : Type} [Fintype Seed] (W : OracleWorld)
    (sch : Quantum.Qrom.SchemeOver W.Oracles Seed PK SK Req Resp F) (tab : W.Tab)
    (A : SufAdversary W PK Req Resp F) : winProbAt W sch tab A ≤ 1 := by
  unfold winProbAt
  calc _ ≤ ∑ S0 : Seed, Pr{let s ← sch.sampleSeed}[s = S0] * 1 :=
        Finset.sum_le_sum fun S0 _ ↦ mul_le_mul_of_nonneg_left
          (QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _) zero_le
    _ ≤ 1 := by simpa using sum_prEvent_eq_some_le_one sch.sampleSeed some

/-- **Theorem 2 averaged over `romWorld`**: the QROM winning probability of a leanSPHINCS
adversary is at most the averages over the tables of the six property terms of its
reductions. -/
theorem winProb_sphincsRom_le_avg
    (A : Quantum.Qrom.SufCma.Adversary PublicKey Message (Option Signature) Forgery) :
    (Quantum.Qrom.SufCma.winProb Quantum.Qrom.Sphincs.sphincsRom A).toReal ≤
      romAvg (fun H ↦ kimPrfAdv romWorld (Key := MasterSeed) kimFmt (littleEndianBytes 32)
          kimTrunc H (B1 romWorld (ofQrom A))) +
        romAvg (fun H ↦ prfMsgAdv romWorld (Key := HashOutput) msgBytes (littleEndianBytes 32)
          truncateHash H (B2 romWorld (ofQrom A))) +
        romAvg (fun H ↦ (itsrSucc romWorld itsrMap H (itsrRed romWorld (ofQrom A))).toReal) +
        romAvg (fun H ↦
          (encTcrCtrSucc romWorld encCtr slotColl H (encRed romWorld (ofQrom A))).toReal) +
        romAvg (fun H ↦
          (cpreSucc romWorld cpreChains slotColl H (cpreRed romWorld (ofQrom A))).toReal) +
        romAvg (fun H ↦
          (smTcrSucc romWorld tcrColl slotColl H (tcrRed romWorld (ofQrom A))).toReal) := by
  have hc : (Fintype.card romWorld.Tab : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have e : Quantum.Qrom.SufCma.winProb Quantum.Qrom.Sphincs.sphincsRom A =
      ∑ H, (Fintype.card romWorld.Tab : ℝ≥0∞)⁻¹ *
        winProbAt romWorld (Quantum.Qrom.Sphincs.sphincsOver romWorld.hash) H (ofQrom A) :=
    winProb_qrom_eq_avg _ A
  rw [e, ENNReal.toReal_sum fun H _ ↦ ENNReal.mul_ne_top hc
    (ne_top_of_le_ne_top ENNReal.one_ne_top (winProbAt_le_one _ _ H _))]
  simp only [romAvg, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_le_sum fun H _ ↦ ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  exact mul_le_mul_of_nonneg_left (sphincs_suf_le_props romWorld romWorld_coinsFair H (ofQrom A))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

end Quantum.StdModel.Qrom.SphInst

end
