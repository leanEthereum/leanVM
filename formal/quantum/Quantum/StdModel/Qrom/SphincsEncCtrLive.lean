module

public import Quantum.StdModel.Qrom.SphincsEncCtrChk
public import Quantum.StdModel.Qrom.SphincsEncCtrSign
public import Quantum.StdModel.Qrom.XmssEncSaltBudget

@[expose] public section

/-!
# EncTCR+C at leanSPHINCS B4: the signer keeps the live invariant

On a live run of B4's signer from a memory of the live invariant `EncJu` and the challenger
invariant `EncTcr.Inv`, the signer makes no charged read: every encoding trial it reads is a trial
the challenger read while grinding the targets, and every other cell it reads is no cell of a
class. The run is checked (`liveRedRun_of_chk`) against the run answering the reads by the final
log, refusing the charged cells; that run succeeds (`chk_encRedSign`) since the signer is the
honest signer of the table of the built digests (`sign_eq_pure_of_path`), whose trials on its
path are the challenger's (`GrindFacts`).

* `encJu_sign`: the handler hypothesis `hσU` of `probAvg_encTcrCtrIn_encRed_le_ju`.
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Key keyOf)

namespace Quantum.StdModel.Qrom.SphEnc

open Quantum.StdModel Props Quantum.StdModel.Sphincs
open Quantum.Qrom.Sphincs
open Quantum.StdModel.Qrom.EncTcr (Mem Gc upd rl mem₀ Inv Charged cntAfter GrindFacts tgtAt
  EvAt bnd)

attribute [local instance] secretsSampleable encRndSampleable

attribute [local irreducible] LiveRedRun LiveRun encRedPost encRedSign encRedPre

/-! ## Cells of no class -/

/-- **An honest input of a slot of no encoding is the input of no cell of a class.** -/
theorem encTw_slotInput_none (key : _root_.Sphincs.KeyGenerationAndSigning.ExpandedKey)
    (root : Digest) (s : Quantum.Sphincs.Slot) (p : SlotPayload s) (hs : encTwKinds.of s = 0)
    {x : Quantum.Qrom.HashDomain}
    (hx : Quantum.Qrom.encodeInput (slotInput key root s p) = some x) :
    EncTcr.encTw encCtr EncTwIn x = none := by
  by_contra h
  obtain ⟨key', root', s', p', h1, hx'⟩ := gc_kindCell (x := x) h
  have e := kindsOf_eq_of_slotInput_eq (Quantum.Qrom.encodeInput_injective hx hx') encTwKinds
  omega

theorem encTwKinds_posSlot (v : QTable) (p : RawPos) : encTwKinds.of (posSlot v p) = 0 := by
  cases p <;> rfl

/-! ## The targets of B4's transcript -/

theorem filterMap_tg_nil (tg : List EncTgt) (Ks : List Key) (msg : Key → Digest)
    (h : tg.map (fun x ↦ (x.1, x.2.1)) = Ks.map fun K ↦ (K, msg K)) {K : Key} (hK : K ∉ Ks)
    (f : EncTgt → Option (Digest × Option (ℕ × Digest)))
    (hf : ∀ y : EncTgt, y.1 ≠ K → f y = none) : tg.filterMap f = [] := by
  have h1 := congrArg (List.map Prod.fst) h
  simp only [List.map_map, Function.comp_def] at h1
  have h1' : tg.map Prod.fst = Ks := by simpa using h1
  refine List.filterMap_eq_nil_iff.mpr fun y hy ↦ hf y fun e ↦ hK ?_
  rw [← e, ← h1']
  exact List.mem_map_of_mem hy

theorem filterMap_tg_single (msg : Key → Digest) (K : Key)
    (f : EncTgt → Option (Digest × Option (ℕ × Digest)))
    (hf1 : ∀ y : EncTgt, y.1 = K → f y = some (y.2.1, y.2.2))
    (hf2 : ∀ y : EncTgt, y.1 ≠ K → f y = none) :
    ∀ (Ks : List Key) (tg : List EncTgt), Ks.Nodup →
      tg.map (fun x ↦ (x.1, x.2.1)) = Ks.map (fun K ↦ (K, msg K)) → K ∈ Ks →
        ∃ ans, tg.filterMap f = [(msg K, ans)]
  | [], _, _, _, hK => absurd hK List.not_mem_nil
  | K₀ :: Ks, [], _, h, _ => by simp at h
  | K₀ :: Ks, y :: tg, hnd, h, hK => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hy1, hy2⟩, h⟩ := h
    rw [List.nodup_cons] at hnd
    by_cases hyK : y.1 = K
    · rw [List.filterMap_cons_some (hf1 y hyK)]
      refine ⟨y.2.2, ?_⟩
      have hK0 : K ∉ Ks := by rw [← hyK, hy1]; exact hnd.1
      rw [filterMap_tg_nil tg Ks msg h hK0 f hf2]
      rw [← hyK, hy2, hy1]
    · rw [List.filterMap_cons_none (hf2 y hyK)]
      refine filterMap_tg_single msg K f hf1 hf2 Ks tg hnd.2 h ?_
      rcases List.mem_cons.mp hK with rfl | hK
      · exact absurd hy1 hyK
      · exact hK

/-- **The targets at the encoding slot of a key in use**: one, on its message. -/
theorem tgtAt_encTw (a : EncData) (htg : TgOk a) (log : QueryLog EncCtrPorts)
    (hlog : LogOk a log) {K : Key} (hK : K ∈ encKeys) :
    ∃ ans, tgtAt log (encTw K) = [(keyMessage (ofDig a.tf) K, ans)] := by
  obtain ⟨Tb, hTb, rfl⟩ := hlog
  unfold tgtAt
  rw [ctrTargets_enc Tb hTb a.tg a.P, List.filterMap_map]
  refine filterMap_tg_single (fun K ↦ keyMessage (ofDig a.tf) K) K _ (fun y h ↦ ?_)
    (fun y h ↦ ?_) encKeys a.tg nodup_encKeys htg hK
  · simp [h]
  · have h' : encTw y.1 ≠ encTw K := fun e ↦ h (encTw_injective e)
    simp [h']

/-- **No evaluation at an encoding slot.** -/
theorem not_evAt_enc (a : EncData) (log : QueryLog EncCtrPorts) (hlog : LogOk a log) (K : Key) :
    ¬ EvAt log (encTw K) := by
  obtain ⟨Tb, hTb, rfl⟩ := hlog
  intro h
  obtain ⟨e, he, het⟩ := List.mem_filterMap.mp h
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · exact (hTb e he).2.2 _ het trivial
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp he
      simp [encEntry, Props.CtrQuery.evalTweak] at het
  · rw [List.mem_singleton.mp he] at het
    simp [encRev, Props.CtrQuery.evalTweak] at het

/-! ## The checked run of the signer -/

section chk

variable (m₀ : Mem nB) (T : Quantum.Qrom.HashDomain → HashOutput)

/-- The charged cells at `m₀`. -/
def badAt (z : Quantum.Qrom.HashDomain) : Prop :=
  EncTcr.encTw encCtr EncTwIn z ≠ none ∧ m₀.ax z = false

open scoped Classical in
/-- The checked hash: `T` off the charged cells. -/
noncomputable def hashChk (l : HashInput) : Option HashOutput :=
  (Quantum.Qrom.encodeInput l).elim (some 0) fun x ↦ if badAt m₀ x then none else some (T x)

/-- The hash answering every input by `T`. -/
noncomputable def hashT (l : HashInput) : HashOutput :=
  (Quantum.Qrom.encodeInput l).elim 0 T

variable {m₀ T}

theorem hashChk_of_not_bad {l : HashInput} {x : Quantum.Qrom.HashDomain}
    (hx : Quantum.Qrom.encodeInput l = some x) (hb : ¬ badAt m₀ x) :
    hashChk m₀ T l = pure (hashT T l) := by
  simp only [hashChk, hashT, hx, Option.elim, hb, ↓reduceIte]
  rfl

theorem hashChk_slotInput (key : _root_.Sphincs.KeyGenerationAndSigning.ExpandedKey)
    (root : Digest) (s : Quantum.Sphincs.Slot) (p : SlotPayload s) (hs : encTwKinds.of s = 0) :
    hashChk m₀ T (slotInput key root s p) = pure (hashT T (slotInput key root s p)) :=
  hashChk_of_not_bad (Quantum.Qrom.Sphincs.encodeInput_slotInput key root s p)
    fun hb ↦ hb.1 (encTw_slotInput_none key root s p hs
      (Quantum.Qrom.Sphincs.encodeInput_slotInput key root s p))

/-- **The counter search of a target ground by the challenger** is answered on its trials. -/
theorem encOkFrom_of_grind {P : PublicParameter} {v : QTable} (hvP : v.publicSeed = P)
    (hT : ∀ z w, m₀.log z = some w → T z = w)
    {sec : KeygenDomain → Option Digest} {rnd : Message → Option Digest}
    (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (mm : Digest) (ans : Option (ℕ × Digest))
    (hGF : GrindFacts encCtr EncTwIn nB P (.enc l τ e) mm ans m₀) :
    ∀ att c, c + att = encodingAttemptLimit → c ≤ bnd encCtr ans →
      EncOkFrom (routeHash P sec rnd (hashChk m₀ T)) v (cellHash (hashT T)) l τ e mm att c
  | 0, _, _, _ => trivial
  | att + 1, c, hc, hb => by
    have hcl : c < encodingAttemptLimit := by omega
    set x := encCell v.publicSeed l τ e mm (BitVec.ofNat counterBits c) with hxdef
    have hx := Quantum.Qrom.Sphincs.encodeInput_encCell v.publicSeed l τ e mm
      (BitVec.ofNat counterBits c)
    have hcell : EncTcr.cellOf encCtr P (.enc l τ e) mm c = some x := by
      rw [← hx, ← hvP]
      rfl
    have hax : m₀.ax x = true ∧ ∃ w, m₀.log x = some w ∧
        (c = bnd encCtr ans → encIsCode (truncateHash w) = true) := by
      rcases Nat.lt_or_ge c (bnd encCtr ans) with hlt | hge
      · obtain ⟨h1, w, hw, -⟩ := hGF.1 c x hlt hcell
        exact ⟨h1, w, hw, fun h ↦ absurd h hlt.ne⟩
      · have hceq : c = bnd encCtr ans := le_antisymm hb hge
        rcases ans with _ | ⟨c', d⟩
        · exact absurd hceq (by simp only [bnd]; change c ≠ encodingAttemptLimit; omega)
        · change c = c' at hceq
          subst hceq
          obtain ⟨-, hd, hx'⟩ := hGF.2.1 c d rfl
          obtain ⟨h1, w, hw, -, hwd⟩ := hx' x hcell
          refine ⟨h1, w, hw, fun _ ↦ ?_⟩
          rw [show truncateHash w = d from hwd]
          exact hd
    obtain ⟨hax1, w, hw, hcode⟩ := hax
    have hTx : T x = w := hT x w hw
    have hnb : ¬ badAt m₀ x := fun h ↦ by rw [h.2] at hax1; cases hax1
    have hH : cellHash (hashT T) x = T x := by
      simp only [cellHash, hashT]
      rw [hxdef, Quantum.Qrom.decodeInput_of_encodeInput_eq_some hx, hx]
      rfl
    refine ⟨?_, fun hnone ↦ encOkFrom_of_grind hvP hT l τ e mm ans hGF att (c + 1) (by omega) ?_⟩
    · rw [routeHash_encInput, hashChk_of_not_bad hx hnb, ← hxdef]
      simp only [hashT, hx, Option.elim]
      exact congrArg pure hH.symm
    · rcases Nat.lt_or_ge c (bnd encCtr ans) with hlt | hge
      · exact hlt
      · exfalso
        have hc' := hcode (le_antisymm hb hge)
        have hdig : v.encDigest (cellHash (hashT T)) l τ e mm (BitVec.ofNat counterBits c) =
            truncateHash w := by
          change truncateHash (cellHash (hashT T) x) = _
          rw [hH, hTx]
        rw [hdig] at hnone
        unfold encIsCode at hc'
        rw [hnone] at hc'
        cases hc'

end chk

/-! ## The signer's checked run succeeds -/

open scoped Classical in
/-- **B4's signer, its reads answered by the final log off the charged cells, returns.** -/
theorem chk_encRedSign (P : PublicParameter) (a : EncData) (st : EncData × SignLog)
    (log : QueryLog EncCtrPorts) (M : Message) (hst : st.1 = a) (hP : a.P = P) (hsec : SecOk a)
    (htg : TgOk a) (hlog : LogOk a log) (m₀ : Mem nB) (hK : KeyLogged P a.tf m₀)
    (hI : Inv encCtr EncTwIn nB P log m₀) (T : Quantum.Qrom.HashDomain → HashOutput)
    (hT : ∀ z w, m₀.log z = some w → T z = w) :
    ∃ b, simulateQ (chkImpl (R' := EncCtrPorts) T (badAt m₀)) (encRedSign romWorld st M) =
      some b := by
  obtain ⟨a', sl⟩ := st
  obtain rfl : a = a' := hst.symm
  subst hP
  set v := digTable (hashT T) a.P a.s a.r with hv
  have hvP : v.publicSeed = a.P := publicSeed_digTable _ _ _ _
  -- the built digests are the table's
  have hpub : ∀ p : Pos, KeyPart p.1 → ¬IsSecret p.1 →
      a.tf p.1 = thSlot (hashT T) a.P (keySlot p.1) (keyPayload p.1 a.tf) := by
    intro p hk hs
    obtain ⟨x, o, hx, -, ho, hot⟩ := hK p hk hs
    change a.tf p.1 = truncateHash (hashT T (keyInput a.P a.tf p.1))
    rw [hashT, hx]
    simp only [Option.elim]
    rw [hT x o ho, hot]
  have hd := tf_eq_dig_of_fix (r := a.r) hsec hpub
  -- the signer over the checked hash
  have hsign : LeanSphincsOver.sign (routeHash a.P (fun d ↦ (pure (a.s d) : Option Digest))
      (fun M ↦ pure (a.r M)) (hashChk m₀ T)) 0 M =
      pure (v.signature (cellHash (hashT T)) M) := by
    refine sign_eq_pure_of_path (answersTable_routeHash_of (fun _ ↦ rfl) (fun _ ↦ rfl)
      fun p _ _ ↦ hashChk_slotInput _ _ _ _ (encTwKinds_posSlot _ p))
      (answersDigest_routeHash_of fun M' ↦ hashChk_slotInput (pubKey v.publicSeed) v.root
        (.hmsg (v.randomizer M') M' 1) () rfl) M fun l ↦ ?_
    have hk := keyIn_keyOf l (v.index M)
    obtain ⟨ans, hans⟩ := tgtAt_encTw a htg log hlog hk
    have hGF := (hI.2 (encTw (keyOf l (v.index M))) trivial
      (not_evAt_enc a log hlog _)).2 _ ans hans
    rw [keyMessage_keyOf_eq a.tf v hd l (v.index M)] at hGF
    exact encOkFrom_of_grind hvP hT l _ _ _ ans hGF encodingAttemptLimit 0 (by omega)
      (Nat.zero_le _)
  refine ⟨(v.signature (cellHash (hashT T)) M,
    (a, sl ++ [⟨M, v.signature (cellHash (hashT T)) M⟩])), ?_⟩
  unfold encRedSign
  rw [simulateQ_bind, Over.simulateQ_sign]
  simp only [simulateQ_routeHash, simulateQ_pure, encH, simulateQ_chkImpl_liftW,
    simulateQ_chkImplW_hash]
  change (LeanSphincsOver.sign (routeHash a.P (fun d ↦ (pure (a.s d) : Option Digest))
      (fun M ↦ pure (a.r M)) (hashChk m₀ T)) 0 M >>= _) = _
  rw [hsign]
  rfl

/-! ## The handler keeps the live invariant -/

/-- **B4's handler keeps the live invariant** on its live runs: the hypothesis `hσU` of
`probAvg_encTcrCtrIn_encRed_le_ju`. -/
theorem encJu_sign (P : PublicParameter) (a : EncData) (st : EncData × SignLog)
    (log : QueryLog EncCtrPorts) (μ : Option (Mem nB)) (M : Message)
    (hI : ∀ m, μ = some m → Inv encCtr EncTwIn nB P log m) (hJ : EncJu P a (st, log) μ)
    (r : (Option Signature × (EncData × SignLog)) × QueryLog EncCtrPorts) (μ' : Option (Mem nB))
    (hrun : LiveRedRun (rl nB) (upd encCtr EncTwIn nB)
      ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P) (encRedSign romWorld st M) log
      μ r μ') :
    EncJu P a (r.1.2, r.2) μ' := by
  obtain ⟨hst, hP, hsec, htg, hlog, hmem⟩ := hJ
  have hlog' : r.2 = log := (liveRedRun_count (upd encCtr EncTwIn nB) (rl nB) _ (fun _ ↦ 0)
    (fun _ ↦ 0) (fun _ _ _ ↦ le_rfl) _ (queryCostAtMost_zero_sphChk _)
    (SphInst.encRedSign_ansCost st M) hrun).2
  have hst' : r.1.2.1 = a := by
    unfold encRedSign at hrun
    obtain ⟨sig, log₁, μ₁, -, h2⟩ := Quantum.StdModel.Xmss.liveRedRun_bind_inv hrun
    obtain ⟨h3, -⟩ := Quantum.StdModel.Xmss.liveRedRun_pure_inv h2
    rw [h3]
    exact hst
  refine ⟨hst', hP, hsec, htg, hlog' ▸ hlog, fun m' hm' ↦ ?_⟩
  rcases μ with _ | m₀
  · rw [liveRedRun_none_sph _ _ _ _ hrun] at hm'
    cases hm'
  subst hm'
  obtain ⟨hK, hc⟩ := hmem m₀ rfl
  have hle := liveRedRun_logLe_sph (rl nB) (upd encCtr EncTwIn nB) EncTcr.recordsAt_upd _ _ hrun
  set T : Quantum.Qrom.HashDomain → HashOutput := fun z ↦ (m'.log z).getD 0 with hTdef
  have hT' : ∀ z w, rl nB m' z = some w → T z = w := fun z w h ↦ by
    change (m'.log z).getD 0 = w
    change m'.log z = some w at h
    rw [h]
    rfl
  obtain ⟨b, hb⟩ := chk_encRedSign P a st log M hst hP hsec htg hlog m₀ hK (hI m₀ rfl) T
    fun z w h ↦ hT' z w (hle z w h)
  obtain ⟨-, hax, hcnt⟩ := liveRedRun_of_chk (rl nB) (upd encCtr EncTwIn nB)
    EncTcr.recordsAt_upd _ T (badAt m₀) (fun m ↦ m.ax = m₀.ax ∧ m.cnt.val = 0)
    (fun z m v hz hm ↦ by
      refine ⟨hm.1, ?_⟩
      change (cntAfter encCtr EncTwIn nB m z).val = 0
      unfold cntAfter
      have hnc : ¬ Charged encCtr EncTwIn nB m z := fun h ↦ hz ⟨h.1, hm.1 ▸ h.2⟩
      simp only [hnc, ↓reduceIte]
      exact hm.2) _ hb hrun hT' ⟨rfl, hc⟩
  refine ⟨fun p hk hs ↦ ?_, hcnt⟩
  obtain ⟨x, o, hx, hxa, ho, hot⟩ := hK p hk hs
  exact ⟨x, o, hx, hax ▸ hxa, hle x o ho, hot⟩

end Quantum.StdModel.Qrom.SphEnc

end
