module

public import Quantum.StdModel.Sphincs.Prf
public import Quantum.StdModel.Sphincs.ItsrHop
public import Quantum.StdModel.Sphincs.Build
public import Quantum.StdModel.Sphincs.Trace

@[expose] public section

/-!
# leanSPHINCS at a fixed table: the EncTCR+C hop

The ideal hybrid read through the EncTCR+C decision (`ideal W tab A (encDec h)`) is at most the
success of a straight-line reduction `encRed W A` (B4) against the EncTCR+C challenger of the
WOTS+C encoding (`Props.encTcrCtr W encCtr slotColl`), at every table of a world with fair coins.

* `encRed W A`: samples the secret digests `s` and the randomizers `r`; while `P` is hidden,
  computes the digests of the key's positions (`buildDig`), the secrets from `s`, every other
  position by an evaluation of `slotColl` at its slot; submits for every key in use (`encKeys`)
  the target `(T_e, m)` of its message `m` (`keyMessage` of the built table) and keeps the
  answers; reveals `P`; answers signing requests with the routed signer (`routeHash`); finally
  records the forgery's verification (`recVerify`), hashes the recorded inputs and outputs a
  witness of `EncHit` (a recorded trial input of a target's key whose digest is the target's
  answer, at a different message or counter).
* `ideal_enc_le`: `ideal W tab A (encDec h) ≤ encTcrCtrSucc W encCtr slotColl tab (encRed W A)`.
  The reduction's transcript is valid (`encValid`: distinct `.enc` tweaks, all targets before the
  reveal, evaluations only at slots of the key's positions), and a forgery in `EvEncT` gives a
  witness that wins (`encJ_of_hit`, `encDec_imp`).
* `isChargeBound_encRed_hash`: `A`'s hash calls plus the honest work; `isChargeBound_encRed_call`:
  one classical call per evaluation, target and reveal of the setup, none afterwards.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Common.SufCma (SchemeHashSpec)
open Quantum.Sphincs (Key ValPos msgPos treeBits)
open Quantum.Qrom.Sphincs (QTable RawPos Pos SlotPayload slotInput)

namespace Quantum.StdModel.Sphincs

/-! ## The ports and the reduction -/

/-- The EncTCR+C ports of the leanSPHINCS instance. -/
abbrev EncCtrPorts :=
  Props.CtrSpec PublicParameter Quantum.Sphincs.Slot Digest Digest Quantum.Sphincs.Slot
    SlotPayload Digest

/-- A classical query of the EncTCR+C ports. -/
abbrev EncCQ := Props.CtrQuery Quantum.Sphincs.Slot Digest Quantum.Sphincs.Slot SlotPayload

/-- A transcript entry of the EncTCR+C ports. -/
abbrev EncEnt := (q : EncCQ) × EncCtrPorts.Range q

/-- A submitted target: the key, its message, the challenger's answer. -/
abbrev EncTgt := Key × Digest × Option (ℕ × Digest)

/-- The encoding tweak of a key. -/
def encTw (K : Key) : Quantum.Sphincs.Slot :=
  .enc K.1 K.2.1 K.2.2

/-- The transcript entry of a submitted target. -/
def encEntry (e : EncTgt) : EncEnt :=
  ⟨.target (encTw e.1) e.2.1, e.2.2⟩

/-- The keys in use. -/
noncomputable def encKeys : List Key :=
  (Finset.univ.filter fun K : Key ↦
    K.2.1.val < 2 ^ treeBits K.1 ∧ K.2.2.val < 2 ^ layerHeight K.1).toList

/-- The secret domain of a secret position. -/
def encSecDom : RawPos → Option KeygenDomain
  | .chainStart l τ e i => some (.oneTimeChain l τ e i)
  | .forsSecret idx κ j => some (.forsSecret idx κ j)
  | _ => none

/-- The digests of a world program in the reduction. -/
noncomputable def encH (W : OracleWorld) (l : HashInput) :
    OracleComp (W.Oracles + EncCtrPorts) HashOutput :=
  liftW EncCtrPorts (W.hash l)

/-- Uniform randomizers. -/
@[instance_reducible]
noncomputable def encRndSampleable : SampleableType (Message → Digest) :=
  SampleableType.ofFintype _

attribute [local instance] secretsSampleable encRndSampleable

/-- **The reduction's setup data**: `P`, the secrets, the randomizers, the built digests, the
submitted targets with their answers. -/
structure EncData where
  /-- `PK.seed`. -/
  P : PublicParameter
  /-- The secret digests. -/
  s : KeygenDomain → Digest
  /-- The randomizers. -/
  r : Message → Digest
  /-- The digests of the key's positions. -/
  tf : RawPos → Digest
  /-- The targets with the challenger's answers. -/
  tg : List EncTgt

/-- The public key of the setup: `P` and the built root. -/
def EncData.pk (a : EncData) : PublicKey :=
  ⟨a.P, (ofDig a.tf).root⟩

/-- A trial input recorded by the verification that hits a target: a different message or
counter whose digest is the target's answer. -/
def EncHit (P : PublicParameter) (tg : List EncTgt) (pr : List (HashInput × HashOutput))
    (w : Key × Digest × EncodingCounter) : Prop :=
  ∃ m c D, (w.1, m, some (c, D)) ∈ tg ∧ (m, c) ≠ (w.2.1, w.2.2.toNat) ∧
    ∃ o, (slotInput (pubKey P) 0 (.enc w.1.1 w.1.2.1 w.1.2.2) (w.2.1, w.2.2), o) ∈ pr ∧
      truncateHash o = D

/-- The EncTCR+C output of a witness. -/
def encOutOf (w : Key × Digest × EncodingCounter) : Quantum.Sphincs.Slot × Digest × ℕ :=
  (encTw w.1, w.2.1, w.2.2.toNat)

/-- The output: a hit, chosen classically, if there is one. -/
noncomputable def encPick (P : PublicParameter) (tg : List EncTgt)
    (pr : List (HashInput × HashOutput)) : Quantum.Sphincs.Slot × Digest × ℕ :=
  @dite _ (∃ w, EncHit P tg pr w) (Classical.propDecidable _) (fun hw ↦ encOutOf hw.choose)
    fun _ ↦ (.expand 0, 0, 0)

variable (W : OracleWorld)

/-- The digest of a key position: the secret, or an evaluation of `slotColl` at its slot. -/
noncomputable def encAsk (s : KeygenDomain → Digest) (p : RawPos) (t : RawPos → Digest) :
    OracleComp (W.Oracles + EncCtrPorts) Digest :=
  match encSecDom p with
  | some d => pure (s d)
  | none => portQ W EncCtrPorts (.eval (keySlot p) (keySlot p) (keyPayload p t))

/-- The targets of the keys `Ks` at the messages `msg`, with the answers. -/
noncomputable def encTargets (msg : Key → Digest) :
    List Key → OracleComp (W.Oracles + EncCtrPorts) (List EncTgt)
  | [] => pure []
  | K :: Ks => do
    let a ← portQ W EncCtrPorts (.target (encTw K) (msg K))
    let rest ← encTargets msg Ks
    pure ((K, msg K, a) :: rest)

/-- The setup after the sampling: the key's digests, the targets, the reveal. -/
noncomputable def encCore (s : KeygenDomain → Digest) (r : Message → Digest) :
    OracleComp (W.Oracles + EncCtrPorts) EncData := do
  let tf ← buildDig (encAsk W s)
  let tg ← encTargets W (fun K ↦ keyMessage (ofDig tf) K) encKeys
  let P ← portQ W EncCtrPorts .reveal
  pure ⟨P, s, r, tf, tg⟩

/-- **The reduction's setup**: uniform secrets and randomizers, then `encCore`. -/
noncomputable def encRedPre : OracleComp (W.Oracles + EncCtrPorts) EncData := do
  let s ← liftW EncCtrPorts (Props.sample W (KeygenDomain → Digest))
  let r ← liftW EncCtrPorts (Props.sample W (Message → Digest))
  encCore W s r

/-- **The reduction's signer**: the routed signer of its setup, logging each answer. -/
noncomputable def encRedSign : HHandler W SignSpec EncCtrPorts (EncData × SignLog) :=
  fun st M ↦ do
    let sig ← Qrom.Sphincs.LeanSphincsOver.sign
      (routeHash st.1.P (fun d ↦ pure (st.1.s d)) (fun M ↦ pure (st.1.r M)) (encH W)) 0 M
    pure (sig, (st.1, st.2 ++ [⟨M, sig⟩]))

/-- **The reduction's output**: the recorded verification, the digests of the recorded inputs,
then a hit. -/
noncomputable def encRedPost (a : EncData) (forg : Forgery) (_ : EncData × SignLog) :
    OracleComp (W.Oracles + EncCtrPorts) (Quantum.Sphincs.Slot × Digest × ℕ) := do
  let rv ← recVerify (encH W) a.pk forg.message forg.signature
  let os ← rv.2.mapM (encH W)
  pure (encPick a.P a.tg (rv.2.zip os))

/-- **The EncTCR+C reduction (B4)**: the adversary run once against the reduction's signer. -/
noncomputable def encRed (A : SAdv W) :
    Props.Adversary W EncCtrPorts Unit (Quantum.Sphincs.Slot × Digest × ℕ) := fun _ ↦
  slRed W (encRedPre W) (fun a ↦ A a.pk) (fun a ↦ (a, [])) (encRedSign W) (encRedPost W)

/-! ## Combinatorics of the keys, the built table and the transcript -/

theorem mem_encKeys {K : Key} : K ∈ encKeys ↔ KeyIn K := by
  simp [encKeys, KeyIn]

theorem nodup_encKeys : encKeys.Nodup :=
  Finset.nodup_toList _

theorem encTw_injective : Function.Injective encTw := by
  rintro ⟨l, τ, e⟩ ⟨l', τ', e'⟩ h
  simp only [encTw, Quantum.Sphincs.Slot.enc.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- The encoding slots. -/
def IsEncSlot : Quantum.Sphincs.Slot → Prop
  | .enc .. => True
  | _ => False

theorem not_isEncSlot_keySlot (p : RawPos) : ¬IsEncSlot (keySlot p) := by
  cases p <;> exact id

theorem encSecDom_none {p : RawPos} (hs : ¬IsSecret p) : encSecDom p = none := by
  cases p <;> first | rfl | exact (hs trivial).elim

theorem encKeyPart_ne_hmsg {p : Pos} (hk : KeyPart p.1) : ∀ M, p.1 ≠ .hmsg M :=
  fun M hM ↦ by rw [hM] at hk; exact hk

/-- The honest value at a symbolic position reads only the key's positions. -/
theorem encValuePos_congr {v v' : QTable} (hd : ∀ q : RawPos, KeyPart q → v.dig q = v'.dig q)
    (x : ValPos) : v.valuePos x = v'.valuePos x := by
  cases x with
  | chain l τ e i j =>
    show v.chainValue l τ e i j.val = v'.chainValue l τ e i j.val
    exact chainValue_congr_key fun q hq _ ↦ hd q hq
  | tree l τ level index =>
    show v.treeValue l τ level.val index.val = v'.treeValue l τ level.val index.val
    exact treeValue_congr_key fun q hq _ ↦ hd q hq
  | forsSecret idx κ s => exact hd (.forsSecret idx κ s) trivial
  | forsTree idx κ height node =>
    show v.forsValue idx κ height.val node.val = v'.forsValue idx κ height.val node.val
    exact forsValue_congr_key fun q hq _ ↦ hd q hq
  | forsKey idx => exact hd (.forsRoots idx) trivial

/-- Digests agreeing with a table on the key's positions give its digests there. -/
theorem encDig_ofDig {tf : RawPos → Digest} {v : QTable}
    (htf : ∀ p : Pos, KeyPart p.1 → tf p.1 = v.dig p.1) :
    ∀ q : RawPos, KeyPart q → (ofDig tf).dig q = v.dig q :=
  fun q hq ↦ (dig_ofDig_congr (t' := v.dig) fun hp hk ↦ htf ⟨q, hp⟩ hk).trans
    (dig_ofDig_dig v hq)

theorem encMem_zip_map (h : HashInput → HashOutput) {x : HashInput} {o : HashOutput} :
    ∀ xs : List HashInput, (x, o) ∈ xs.zip (xs.map h) ↔ x ∈ xs ∧ o = h x
  | [] => by simp
  | y :: ys => by
    rw [List.map_cons, List.zip_cons_cons, List.mem_cons, encMem_zip_map h ys, List.mem_cons,
      Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨hx, rfl⟩)
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr hx, rfl⟩
    · rintro ⟨rfl | hx, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨hx, rfl⟩

/-! ## The transcript -/

/-- The reveal entry. -/
def encRev (P : PublicParameter) : EncEnt :=
  ⟨.reveal, P⟩

/-- An entry of the build: an evaluation at a slot of no encoding. -/
def EncEvalOk (e : EncEnt) : Prop :=
  e.1.isTarget = false ∧ e.1.isReveal = false ∧
    ∀ t, Props.CtrQuery.evalTweak e = some t → ¬IsEncSlot t

theorem asTarget_of_evalOk {e : EncEnt} (he : EncEvalOk e) :
    Props.CtrQuery.asTarget e = none := by
  obtain ⟨q, a⟩ := e
  cases q with
  | target t m => exact absurd he.1 (by simp [Props.CtrQuery.isTarget])
  | eval => rfl
  | reveal => rfl

/-- The targets of the reduction's transcript. -/
theorem ctrTargets_enc (Tb : List EncEnt) (hTb : ∀ e ∈ Tb, EncEvalOk e) (tg : List EncTgt)
    (P : PublicParameter) :
    Props.ctrTargets (Tb ++ tg.map encEntry ++ [encRev P] : QueryLog EncCtrPorts) =
      tg.map fun e ↦ ((encTw e.1, e.2.1), e.2.2) := by
  have h1 : Tb.filterMap Props.CtrQuery.asTarget = [] :=
    List.filterMap_eq_nil_iff.mpr fun e he ↦ asTarget_of_evalOk (hTb e he)
  unfold Props.ctrTargets
  rw [List.filterMap_append, List.filterMap_append, h1, List.filterMap_map, List.nil_append,
    show (Props.CtrQuery.asTarget ∘ encEntry : EncTgt → _) =
      some ∘ (fun e ↦ ((encTw e.1, e.2.1), e.2.2)) from rfl, List.filterMap_eq_map]
  exact List.append_nil _

/-- **The reduction's transcript is valid.** -/
theorem encValid (Tb : List EncEnt) (hTb : ∀ e ∈ Tb, EncEvalOk e) (tg : List EncTgt)
    (htg : (tg.map Prod.fst).Nodup) (P : PublicParameter) :
    Props.EncCtrValid (Tb ++ tg.map encEntry ++ [encRev P] : QueryLog EncCtrPorts) := by
  rw [Props.EncCtrValid, ctrTargets_enc Tb hTb tg P]
  refine ⟨?_, ?_, ?_⟩
  · have h := htg.map encTw_injective
    rw [List.map_map] at h ⊢
    exact h
  · intro e he
    have hpre : ∀ a ∈ Tb ++ tg.map encEntry, (!a.1.isReveal) = true := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · simp [(hTb a ha).2.1]
      · obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
        rfl
    have hrev : ¬(!(encRev P).1.isReveal) = true := by
      simp [encRev, Props.CtrQuery.isReveal]
    rw [Props.phaseTwo, List.dropWhile_append_of_pos hpre,
      List.dropWhile_cons_of_neg (p := fun a : EncEnt ↦ !a.1.isReveal) hrev,
      List.mem_singleton] at he
    rw [he]
    rfl
  · intro t ht htg'
    obtain ⟨e, he, het⟩ := List.mem_filterMap.mp ht
    rw [List.map_map] at htg'
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp htg'
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · exact (hTb e he).2.2 _ het trivial
      · obtain ⟨y, -, rfl⟩ := List.mem_map.mp he
        simp [encEntry, Props.CtrQuery.evalTweak] at het
    · rw [List.mem_singleton.mp he] at het
      simp [encRev, Props.CtrQuery.evalTweak] at het

/-! ## The setup at a fixed hash -/

/-- The digest of a key position under `h`: the secret, or `Th` at its slot. -/
def encVal (h : HashInput → HashOutput) (P : PublicParameter) (s : KeygenDomain → Digest)
    (p : RawPos) (t : RawPos → Digest) : Digest :=
  match encSecDom p with
  | some d => s d
  | none => thSlot h P (keySlot p) (keyPayload p t)

/-- The built digests under `h`. -/
noncomputable def encTfAt (h : HashInput → HashOutput) (P : PublicParameter)
    (s : KeygenDomain → Digest) : RawPos → Digest :=
  buildDig (m := Id) fun p t ↦ encVal h P s p t

/-- The challenger's answer to the target of `K` at `m`: the table's selection. -/
def encGr (h : HashInput → HashOutput) (v : QTable) (P : PublicParameter) (K : Key)
    (m : Digest) : Option (ℕ × Digest) :=
  (v.select (cellHash h) K.1 K.2.1 K.2.2 m).map fun sel ↦
    (sel.1.toNat, thSlot h P (.enc K.1 K.2.1 K.2.2) (m, sel.1))

/-- The submitted targets under `h`. -/
noncomputable def encTgAt (h : HashInput → HashOutput) (P : PublicParameter)
    (s : KeygenDomain → Digest) (r : Message → Digest) : List EncTgt :=
  encKeys.map fun K ↦ (K, keyMessage (ofDig (encTfAt h P s)) K,
    encGr h (digTable h P s r) P K (keyMessage (ofDig (encTfAt h P s)) K))

/-- The setup data under `h`. -/
noncomputable def encDataAt (h : HashInput → HashOutput) (P : PublicParameter)
    (s : KeygenDomain → Digest) (r : Message → Digest) : EncData :=
  ⟨P, s, r, encTfAt h P s, encTgAt h P s r⟩

section Semantics

variable (h : HashInput → HashOutput) (P : PublicParameter) (s : KeygenDomain → Digest)
  (r : Message → Digest)

/-- **The built digests are those of `digTable`** at the key's positions. -/
theorem encTfAt_spec : ∀ p : Pos, KeyPart p.1 → encTfAt h P s p.1 = (digTable h P s r).dig p.1 := by
  have hsec : ∀ p : Pos, KeyPart p.1 → IsSecret p.1 → ∀ t,
      ((fun p t ↦ encVal h P s p t) p.1 t : Id Digest) =
        (pure ((digTable h P s r).dig p.1) : Id Digest) := by
    intro p hk hs t
    obtain ⟨p, hp⟩ := p
    cases p with
    | chainStart l τ e i => exact (dig_chainStart_digTable h P s r hp).symm
    | forsSecret idx κ j => exact (dig_forsSecret_digTable h P s r idx κ j).symm
    | _ => first | exact (hk : False).elim | exact (hs : False).elim
  have hth : ∀ p : Pos, KeyPart p.1 → ¬IsSecret p.1 → ∀ t,
      ((fun p t ↦ encVal h P s p t) p.1 t : Id Digest) =
        (pure (thSlot h P (keySlot p.1) (keyPayload p.1 t)) : Id Digest) := by
    intro p _ hs t
    show encVal h P s p.1 t = _
    unfold encVal
    rw [encSecDom_none hs]
    rfl
  obtain ⟨tf, htf, hag⟩ := buildDig_digTable (m := Id) h P s r _ hsec hth
  intro p hk
  rw [show encTfAt h P s = tf from htf]
  exact hag p hk

theorem encMsg_eq (K : Key) :
    keyMessage (ofDig (encTfAt h P s)) K = keyMessage (digTable h P s r) K :=
  encValuePos_congr (encDig_ofDig (encTfAt_spec h P s r)) (msgPos K)

theorem encDataAt_pk : (encDataAt h P s r).pk = (digTable h P s r).publicKey := by
  have hd := encDig_ofDig (encTfAt_spec h P s r)
  show (⟨P, (ofDig (encTfAt h P s)).root⟩ : PublicKey) =
    ⟨(digTable h P s r).publicSeed, (digTable h P s r).root⟩
  rw [publicSeed_digTable]
  congr 1
  show (ofDig (encTfAt h P s)).treeValue topLayer 0 (layerHeight topLayer) 0 =
    (digTable h P s r).treeValue topLayer 0 (layerHeight topLayer) 0
  exact treeValue_congr_key fun q hq _ ↦ hd q hq

end Semantics

/-! ## The decision -/

/-- The recorded inputs of the verification with their digests under `h`. -/
def encPairs (h : HashInput → HashOutput) (pk : PublicKey) (forg : Forgery) :
    List (HashInput × HashOutput) :=
  (Extract.verifyQueries h pk forg.message forg.signature).zip
    ((Extract.verifyQueries h pk forg.message forg.signature).map h)

/-- The EncTCR+C challenger's decision under `h`. -/
noncomputable def encJ (h : HashInput → HashOutput) (P : PublicParameter)
    (log : QueryLog EncCtrPorts) (out : Quantum.Sphincs.Slot × Digest × ℕ) : Bool :=
  Props.holds (Props.EncCtrValid log ∧ out.2.2 < encCtr.limit ∧
    ∃ x ∈ Props.ctrTargets log, ∃ c,
      x.2 = some (c, truncateHash (h (encLayout P out.1 (out.2.1, out.2.2)))) ∧
        x.1.1 = out.1 ∧ (x.1.2, c) ≠ out.2)

theorem encPick_spec {P : PublicParameter} {tg : List EncTgt}
    {pr : List (HashInput × HashOutput)} (hex : ∃ w, EncHit P tg pr w) :
    ∃ w, EncHit P tg pr w ∧ encPick P tg pr = encOutOf w :=
  ⟨hex.choose, hex.choose_spec, dite_eq_left hex⟩

/-- **A hit wins** against a valid transcript recording the targets. -/
theorem encJ_of_hit (h : HashInput → HashOutput) (P : PublicParameter) (Tb : List EncEnt)
    (hTb : ∀ e ∈ Tb, EncEvalOk e) (tg : List EncTgt) (htg : (tg.map Prod.fst).Nodup)
    (pr : List (HashInput × HashOutput)) (hpr : ∀ x o, (x, o) ∈ pr → o = h x)
    (w : Key × Digest × EncodingCounter) (hw : EncHit P tg pr w) :
    encJ h P (Tb ++ tg.map encEntry ++ [encRev P]) (encOutOf w) = true := by
  obtain ⟨m, c, D, hmem, hne, o, ho, hoD⟩ := hw
  have hin : encLayout P (encOutOf w).1 ((encOutOf w).2.1, (encOutOf w).2.2) =
      slotInput (pubKey P) 0 (.enc w.1.1 w.1.2.1 w.1.2.2) (w.2.1, w.2.2) := by
    show slotInput (pubKey P) 0 (.enc w.1.1 w.1.2.1 w.1.2.2)
      (w.2.1, BitVec.ofNat counterBits w.2.2.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine Props.holds_eq_true.mpr ⟨encValid Tb hTb tg htg P, w.2.2.isLt,
    ((encTw w.1, m), some (c, D)), ?_, c, ?_, rfl, hne⟩
  · rw [ctrTargets_enc Tb hTb tg P]
    exact List.mem_map_of_mem (f := fun e : EncTgt ↦ ((encTw e.1, e.2.1), e.2.2)) hmem
  · rw [hin, ← hpr _ _ ho, hoD]

/-- **The EncTCR+C event gives a winning output** at the setup of `P`, `s`, `r`. -/
theorem encDec_imp (h : HashInput → HashOutput) (P : PublicParameter)
    (s : KeygenDomain → Digest) (r : Message → Digest) (Tb : List EncEnt)
    (hTb : ∀ e ∈ Tb, EncEvalOk e) (g : Forgery × SignLog)
    (hE : encDec h (digTable h P s r) g = true) :
    encJ h P (Tb ++ (encTgAt h P s r).map encEntry ++ [encRev P])
      (encPick P (encTgAt h P s r) (encPairs h (digTable h P s r).publicKey g.1)) = true := by
  obtain ⟨K, hK, sel, hS, m', c', hne, o, ho, hd⟩ := Props.holds_eq_true.mp hE
  have hvP : (digTable h P s r).publicSeed = P := publicSeed_digTable h P s r
  rw [hvP] at ho hd
  have hho : slotInput (pubKey P) 0 (.enc K.1 K.2.1 K.2.2) (m', c') ∈
      Extract.verifyQueries h (digTable h P s r).publicKey g.1.message g.1.signature ∧
        o = h (slotInput (pubKey P) 0 (.enc K.1 K.2.1 K.2.2) (m', c')) := by
    unfold forgTrace Extract.traceH at ho
    split_ifs at ho with hx
    exact ⟨hx, (Option.some.inj ho).symm⟩
  have hpr : ∀ x o, (x, o) ∈ encPairs h (digTable h P s r).publicKey g.1 → o = h x :=
    fun x o hx ↦ ((encMem_zip_map h _).mp hx).2
  have htg : ((encTgAt h P s r).map Prod.fst).Nodup := by
    have e : (encTgAt h P s r).map Prod.fst = encKeys := by
      simp [encTgAt, List.map_map, Function.comp_def]
    rw [e]
    exact nodup_encKeys
  have hmem : (K, keyMessage (digTable h P s r) K,
      some (sel.1.toNat, thSlot h P (.enc K.1 K.2.1 K.2.2) (keyMessage (digTable h P s r) K,
        sel.1))) ∈ encTgAt h P s r := by
    refine List.mem_map.mpr ⟨K, mem_encKeys.mpr hK, ?_⟩
    rw [encMsg_eq h P s r K]
    have hS' : (digTable h P s r).select (cellHash h) K.1 K.2.1 K.2.2
        (keyMessage (digTable h P s r) K) = some sel := hS
    simp only [encGr, hS', Option.map_some]
  have hne' : (keyMessage (digTable h P s r) K, sel.1.toNat) ≠ (m', c'.toNat) := fun heq ↦
    hne (Prod.ext (Prod.mk.inj heq).1.symm (BitVec.eq_of_toNat_eq (Prod.mk.inj heq).2.symm))
  obtain ⟨w, hw, hpick⟩ := encPick_spec (P := P) (tg := encTgAt h P s r)
    (pr := encPairs h (digTable h P s r).publicKey g.1) ⟨(K, m', c'), _, _, _, hmem, hne', o,
    (encMem_zip_map h _).mpr hho, hd⟩
  rw [hpick]
  exact encJ_of_hit h P Tb hTb _ htg _ hpr w hw

/-! ## The reduction at a fixed table -/

section Table

variable (tab : W.Tab)

theorem simulateQ_logImpl_encH (ans : (q : EncCQ) → OracleComp W.Oracles (EncCtrPorts.Range q))
    (l : HashInput) :
    simulateQ (logImpl tab ans) (encH W l) =
      (pure (W.hashOf tab l) : StateT (QueryLog EncCtrPorts) ProbComp HashOutput) := by
  refine StateT.ext fun log ↦ ?_
  rw [encH, run_simulateQ_logImpl_liftW, W.simulateQ_hash, map_pure, StateT.run_pure]

theorem run_encRedSign (ans : (q : EncCQ) → OracleComp W.Oracles (EncCtrPorts.Range q))
    (a : EncData) (sl : SignLog) (M : Message) (log : QueryLog EncCtrPorts) :
    (simulateQ (logImpl tab ans) (encRedSign W (a, sl) M)).run log =
      pure (((digTable (W.hashOf tab) a.P a.s a.r).signature (cellHash (W.hashOf tab)) M,
        (a, sl ++ [⟨M, (digTable (W.hashOf tab) a.P a.s a.r).signature
          (cellHash (W.hashOf tab)) M⟩])), log) := by
  have hsign : simulateQ (logImpl tab ans) (Qrom.Sphincs.LeanSphincsOver.sign
      (routeHash a.P (fun d ↦ pure (a.s d)) (fun M ↦ pure (a.r M)) (encH W)) 0 M) =
      (pure ((digTable (W.hashOf tab) a.P a.s a.r).signature (cellHash (W.hashOf tab)) M) :
        StateT (QueryLog EncCtrPorts) ProbComp (Option Signature)) := by
    rw [Over.simulateQ_sign]
    simp only [simulateQ_routeHash, simulateQ_pure, simulateQ_logImpl_encH]
    exact sign_routeHash (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) M
  simp only [encRedSign, simulateQ_bind, hsign, pure_bind, simulateQ_pure, StateT.run_pure]

theorem encSimulateQ_mapM {ι : Type} {O : OracleSpec.{0, 0} ι} {n : Type → Type} [Monad n]
    [LawfulMonad n] (impl : QueryImpl O n) (g : HashInput → OracleComp O HashOutput)
    (h : HashInput → HashOutput) (hg : ∀ x, simulateQ impl (g x) = pure (h x)) :
    ∀ xs : List HashInput, simulateQ impl (xs.mapM g) = pure (xs.map h)
  | [] => by simp only [List.mapM_nil, simulateQ_pure, List.map_nil]
  | x :: xs => by
    simp only [List.mapM_cons, simulateQ_bind, hg, pure_bind, encSimulateQ_mapM impl g h hg xs,
      simulateQ_pure, List.map_cons]

theorem run_encRedPost (ans : (q : EncCQ) → OracleComp W.Oracles (EncCtrPorts.Range q))
    (a : EncData) (forg : Forgery) (st : EncData × SignLog) (log : QueryLog EncCtrPorts) :
    (simulateQ (logImpl tab ans) (encRedPost W a forg st)).run log =
      pure (encPick a.P a.tg (encPairs (W.hashOf tab) a.pk forg), log) := by
  have hh := simulateQ_logImpl_encH W tab ans
  simp only [encRedPost, simulateQ_bind, simulateQ_recVerify (logImpl tab ans) (encH W) _ hh,
    pure_bind, encSimulateQ_mapM (logImpl tab ans) (encH W) _ hh, simulateQ_pure,
    StateT.run_pure]
  rfl

theorem simulateQ_encJudge (P : PublicParameter) (log : QueryLog EncCtrPorts)
    (out : Quantum.Sphincs.Slot × Digest × ℕ) :
    simulateQ (W.eager tab) ((Props.encTcrCtr W encCtr slotColl).judge P log out) =
      pure (encJ (W.hashOf tab) P log out) := by
  simp only [Props.encTcrCtr, simulateQ_bind, simulateQ_eval, pure_bind, simulateQ_pure]
  rfl

variable (P : PublicParameter) (s : KeygenDomain → Digest) (r : Message → Digest)

theorem run_logImpl_portQ {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q : Q') → OracleComp W.Oracles (R'.Range q)) (x : Q') (log : QueryLog R') :
    (simulateQ (logImpl tab ans) (portQ W R' x)).run log =
      (fun a ↦ (a, log ++ [⟨x, a⟩])) <$> simulateQ (W.eager tab) (ans x) := by
  rw [portQ, simulateQ_spec_query]
  rfl

theorem run_encAsk (p : Pos) (hk : KeyPart p.1) (t : RawPos → Digest)
    (log : QueryLog EncCtrPorts) :
    ∃ T, (simulateQ (logImpl tab ((Props.encTcrCtr W encCtr slotColl).answer P))
        (encAsk W s p.1 t)).run log = pure (encVal (W.hashOf tab) P s p.1 t, log ++ T) ∧
      ∀ e ∈ T, EncEvalOk e := by
  unfold encAsk encVal
  cases encSecDom p.1 with
  | some d =>
    exact ⟨[], by rw [simulateQ_pure, StateT.run_pure, List.append_nil], fun e he ↦ by simp at he⟩
  | none =>
    refine ⟨[⟨.eval (keySlot p.1) (keySlot p.1) (keyPayload p.1 t),
      thSlot (W.hashOf tab) P (keySlot p.1) (keyPayload p.1 t)⟩], ?_, ?_⟩
    · have hans : simulateQ (W.eager tab) ((Props.encTcrCtr W encCtr slotColl).answer P
          (.eval (keySlot p.1) (keySlot p.1) (keyPayload p.1 t))) =
          pure (thSlot (W.hashOf tab) P (keySlot p.1) (keyPayload p.1 t)) :=
        simulateQ_slotColl_eval W tab P (slotInRange_keySlot p (encKeyPart_ne_hmsg hk)) _
      dsimp only
      refine (run_logImpl_portQ W tab _ (.eval (keySlot p.1) (keySlot p.1) (keyPayload p.1 t))
        log).trans ?_
      rw [hans]
      generalize thSlot (W.hashOf tab) P (keySlot p.1) (keyPayload p.1 t) = x
      exact map_pure _ _
    · intro e he
      rw [List.mem_singleton.mp he]
      refine ⟨rfl, rfl, fun t' ht' ↦ ?_⟩
      obtain rfl : keySlot p.1 = t' := Option.some.inj ht'
      exact not_isEncSlot_keySlot p.1

theorem run_encFold : ∀ (L : List Pos), (∀ p ∈ L, KeyPart p.1) →
    ∀ (t : RawPos → Digest) (log : QueryLog EncCtrPorts), ∃ T,
      (simulateQ (logImpl tab ((Props.encTcrCtr W encCtr slotColl).answer P))
        (L.foldlM (buildStep (encAsk W s)) t)).run log =
        pure (L.foldlM (m := Id) (buildStep fun p t ↦ encVal (W.hashOf tab) P s p t) t,
          log ++ T) ∧ ∀ e ∈ T, EncEvalOk e
  | [], _, t, log => ⟨[], by
      simp only [List.foldlM_nil, simulateQ_pure, StateT.run_pure, List.append_nil]
      rfl, fun e he ↦ by simp at he⟩
  | p :: L, hL, t, log => by
    obtain ⟨T₁, h1, hT1⟩ := run_encAsk W tab P s p (hL p List.mem_cons_self) t log
    obtain ⟨T₂, h2, hT2⟩ := run_encFold L (fun q hq ↦ hL q (List.mem_cons_of_mem _ hq))
      (Function.update t p.1 (encVal (W.hashOf tab) P s p.1 t)) (log ++ T₁)
    refine ⟨T₁ ++ T₂, ?_, fun e he ↦ (List.mem_append.mp he).elim (hT1 e) (hT2 e)⟩
    rw [List.foldlM_cons, buildStep, simulateQ_bind, simulateQ_bind, StateT.run_bind,
      StateT.run_bind, h1, pure_bind, simulateQ_pure, StateT.run_pure, pure_bind, h2,
      List.append_assoc]
    rfl

theorem run_encTargets (gr : Key → Digest → Option (ℕ × Digest))
    (hgr : ∀ K m, simulateQ (W.eager tab) ((Props.encTcrCtr W encCtr slotColl).answer P
      (.target (encTw K) m)) = (pure (gr K m) : ProbComp (EncCtrPorts.Range (.target (encTw K) m))))
    (msg : Key → Digest) :
    ∀ (Ks : List Key) (log : QueryLog EncCtrPorts),
      (simulateQ (logImpl tab ((Props.encTcrCtr W encCtr slotColl).answer P))
        (encTargets W msg Ks)).run log =
        pure (Ks.map (fun K ↦ (K, msg K, gr K (msg K))),
          log ++ (Ks.map (fun K ↦ (K, msg K, gr K (msg K)))).map encEntry)
  | [], log => by simp [encTargets]
  | K :: Ks, log => by
    have hq : (simulateQ (logImpl tab ((Props.encTcrCtr W encCtr slotColl).answer P))
        (portQ W EncCtrPorts (.target (encTw K) (msg K)))).run log =
        (pure (gr K (msg K), log ++ [encEntry (K, msg K, gr K (msg K))]) :
            ProbComp (EncCtrPorts.Range (.target (encTw K) (msg K)) × QueryLog EncCtrPorts)) := by
      rw [portQ, simulateQ_spec_query, run_logImpl_inr, hgr]
      generalize gr K (msg K) = x
      exact map_pure _ _
    simp only [encTargets, simulateQ_bind, StateT.run_bind, hq, pure_bind,
      run_encTargets gr hgr msg Ks, simulateQ_pure, StateT.run_pure, List.map_cons,
      List.append_assoc, List.singleton_append]

/-- **The setup after the sampling at a fixed table**: the data under the table's hash, the
transcript of the build (evaluations), the targets and the reveal. -/
theorem run_encCore : ∃ Tb, (∀ e ∈ Tb, EncEvalOk e) ∧
    (simulateQ (logImpl tab ((Props.encTcrCtr W encCtr slotColl).answer P))
      (encCore W s r)).run [] =
      pure (encDataAt (W.hashOf tab) P s r,
        Tb ++ (encTgAt (W.hashOf tab) P s r).map encEntry ++ [encRev P]) := by
  obtain ⟨Tb, hb, hTb⟩ := run_encFold W tab P s keyOrder (fun p hp ↦ (mem_keyOrder p).1 hp)
    (fun _ ↦ 0) []
  refine ⟨Tb, hTb, ?_⟩
  have hrev : ∀ log, (simulateQ (logImpl tab ((Props.encTcrCtr W encCtr slotColl).answer P))
      (portQ W EncCtrPorts .reveal)).run log = pure (P, log ++ [encRev P]) := fun log ↦ by
    rw [portQ, simulateQ_spec_query, run_logImpl_inr]
    exact (congrArg _ (simulateQ_pure (W.eager tab) P)).trans (map_pure _ _)
  simp only [encCore, buildDig, simulateQ_bind, StateT.run_bind, hb, pure_bind,
    run_encTargets W tab P (encGr (W.hashOf tab) (digTable (W.hashOf tab) P s r) P)
      (fun K m ↦ simulateQ_encCtr_grind W tab _ (publicSeed_digTable _ _ _ _) K.1 K.2.1 K.2.2 m),
    hrev,
    simulateQ_pure, StateT.run_pure, List.nil_append]
  rfl

theorem run_encRedPre (hW : W.CoinsFair) :
    (simulateQ (logImpl tab ((Props.encTcrCtr W encCtr slotColl).answer P)) (encRedPre W)).run
        [] =
      (do
        let s ← $ᵗ (KeygenDomain → Digest)
        let r ← $ᵗ (Message → Digest)
        (simulateQ (logImpl tab ((Props.encTcrCtr W encCtr slotColl).answer P))
          (encCore W s r)).run []) := by
  simp only [encRedPre, simulateQ_bind, StateT.run_bind, run_simulateQ_logImpl_liftW,
    W.simulateQ_sample hW tab, bind_map_left]

end Table

/-! ## The EncTCR+C hop -/

section Run

variable (tab : W.Tab) (A : SAdv W)

theorem encUnifAvg_mono {X : Type} [Fintype X] {Φ Ψ : X → ℝ≥0∞} (h : ∀ x, Φ x ≤ Ψ x) :
    unifAvg X Φ ≤ unifAvg X Ψ :=
  mul_le_mul' le_rfl (Finset.sum_le_sum fun x _ ↦ h x)

theorem tsum_encSetup (hW : W.CoinsFair) (f : PublicParameter → ℝ≥0∞) :
    ∑' P : PublicParameter,
        Pr{let z ← simulateQ (W.eager tab) (Props.encTcrCtr W encCtr slotColl).setup}[z = P] *
          f P = unifAvg PublicParameter f :=
  tsum_sample_mul W tab hW f

/-- The challenger's decision on the reduction's output for the forgery `f`. -/
noncomputable def encD (h : HashInput → HashOutput) (P : PublicParameter)
    (T : QueryLog EncCtrPorts) (a : EncData) (pk : PublicKey) (f : Forgery) : Bool :=
  encJ h P T (encPick a.P a.tg (encPairs h pk f))

/-- The reduction's kernel answers as the signer of its setup's table. -/
theorem encKernel_sim (P : PublicParameter) (a : EncData)
    (st : (EncData × SignLog) × QueryLog EncCtrPorts) (ha : st.1.1 = a) (M : Message) :
    Prod.map id (fun st : (EncData × SignLog) × QueryLog EncCtrPorts ↦ st.1.2) <$>
        hKernel tab ((Props.encTcrCtr W encCtr slotColl).answer P) (encRedSign W) st M =
      detKernel (W.hashOf tab) (digTable (W.hashOf tab) a.P a.s a.r) st.1.2 M := by
  obtain ⟨⟨a', sl⟩, log⟩ := st
  obtain rfl : a' = a := ha
  unfold hKernel
  dsimp only
  rw [run_encRedSign, map_pure, map_pure]
  simp only [detKernel, Prod.map_apply, id_eq]

/-- The reduction's kernel keeps its setup and its transcript. -/
theorem encKernel_inv (P : PublicParameter) (a : EncData) (T : QueryLog EncCtrPorts)
    (st : (EncData × SignLog) × QueryLog EncCtrPorts) (hst : st.1.1 = a ∧ st.2 = T)
    (M : Message) :
    ∀ p ∈ support (hKernel tab ((Props.encTcrCtr W encCtr slotColl).answer P) (encRedSign W)
      st M), p.2.1.1 = a ∧ p.2.2 = T := by
  obtain ⟨⟨a', sl⟩, log⟩ := st
  obtain ⟨ha, hl⟩ := hst
  obtain rfl : a' = a := ha
  obtain rfl : log = T := hl
  intro p hp
  unfold hKernel at hp
  dsimp only at hp
  rw [run_encRedSign, map_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact ⟨rfl, rfl⟩

/-- **The reduction's run at a setup** is at least the game at its table read through the
EncTCR+C decision, when the event implies the challenger's decision. -/
theorem encTail_le (P : PublicParameter) (a : EncData) (T : QueryLog EncCtrPorts)
    (hpk : a.pk = (digTable (W.hashOf tab) a.P a.s a.r).publicKey)
    (himp : ∀ g, encDec (W.hashOf tab) (digTable (W.hashOf tab) a.P a.s a.r) g = true →
      encD (W.hashOf tab) P T a (digTable (W.hashOf tab) a.P a.s a.r).publicKey g.1 = true) :
    gameAt W tab A (digTable (W.hashOf tab) a.P a.s a.r)
        (encDec (W.hashOf tab) (digTable (W.hashOf tab) a.P a.s a.r)) ≤
      W.probAt tab ((kRunQ W (hKernel tab ((Props.encTcrCtr W encCtr slotColl).answer P)
        (encRedSign W)) (A a.pk) ((a, []), T)).map fun r' ↦
          encD (W.hashOf tab) P r'.2.2 a a.pk r'.1) := by
  rw [hpk]
  refine le_of_le_of_eq ?_ (probAt_eq_of_run₂ W tab (run₂_map_kRunQ_sim (W.runtime tab)
    (detKernel (W.hashOf tab) (digTable (W.hashOf tab) a.P a.s a.r))
    (hKernel tab ((Props.encTcrCtr W encCtr slotColl).answer P) (encRedSign W))
    (fun st ↦ st.1.1 = a ∧ st.2 = T) (fun st ↦ st.1.2)
    (fun st hst M ↦ encKernel_sim W tab P a st hst.1 M)
    (fun st hst M ↦ encKernel_inv W tab P a T st hst M)
    (A (digTable (W.hashOf tab) a.P a.s a.r).publicKey) ((a, []), T) ⟨rfl, rfl⟩
    (fun g ↦ encD (W.hashOf tab) P T a (digTable (W.hashOf tab) a.P a.s a.r).publicKey g.1)
    (fun r' ↦ encD (W.hashOf tab) P r'.2.2 a (digTable (W.hashOf tab) a.P a.s a.r).publicKey
      r'.1)
    fun g st hst ↦ congrArg (fun L ↦ encD (W.hashOf tab) P L a
      (digTable (W.hashOf tab) a.P a.s a.r).publicKey g) hst.2)).symm
  exact le_of_le_of_eq (probAt_map_le_sum W tab
    (kRunQ W (detKernel (W.hashOf tab) (digTable (W.hashOf tab) a.P a.s a.r))
      (A (digTable (W.hashOf tab) a.P a.s a.r).publicKey) [])
    (encDec (W.hashOf tab) (digTable (W.hashOf tab) a.P a.s a.r)) {()}
    (fun _ g ↦ encD (W.hashOf tab) P T a (digTable (W.hashOf tab) a.P a.s a.r).publicKey g.1)
    fun g hg ↦ ⟨(), Finset.mem_singleton_self _, himp g hg⟩) (Finset.sum_singleton _ _)

/-- **The EncTCR+C hop of Theorem 2**: at every table of a world with fair coins, the ideal game
read through the EncTCR+C decision is at most the EncTCR+C success of `encRed W A`. -/
theorem ideal_enc_le (hW : W.CoinsFair) :
    ideal W tab A (encDec (W.hashOf tab)) ≤
      Props.encTcrCtrSucc W encCtr slotColl tab (encRed W A) := by
  refine le_of_le_of_eq ?_ (probAt_eq_of_run₂ W tab (run₂_game_slRed tab
    (Props.encTcrCtr W encCtr slotColl) (fun _ ↦ encRedPre W) (fun _ a ↦ A a.pk)
    (fun _ a ↦ (a, [])) (fun _ ↦ encRedSign W) (fun _ ↦ encRedPost W))).symm
  rw [probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt (W.runtime tab) _)]
  refine le_of_le_of_eq ?_ (tsum_encSetup W tab hW _).symm
  unfold ideal
  refine encUnifAvg_mono fun P ↦ ?_
  rw [slNormal, QuantumComp₂.bind_assoc,
    probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt (W.runtime tab) _),
    run_encRedPre W tab P hW]
  simp only [tsum_prEvent_bind_mul, tsum_prEvent_uniformSample]
  refine encUnifAvg_mono fun s ↦ encUnifAvg_mono fun r ↦ ?_
  obtain ⟨Tb, hTb, hrun⟩ := run_encCore W tab P s r
  rw [hrun, tsum_prEvent_pure_mul]
  dsimp only
  rw [QuantumComp₂.bind_assoc]
  have htail : ∀ r' : (Forgery × (EncData × SignLog)) × QueryLog EncCtrPorts,
      (W.runtime tab).run₂ .instruments (QuantumComp₂.bind
        (((simulateQ (logImpl tab ((Props.encTcrCtr W encCtr slotColl).answer P))
          (encRedPost W (encDataAt (W.hashOf tab) P s r) r'.1.1 r'.1.2)).run r'.2).toQuantumAt
            (QComp.coinImpl W.spec (QReg.of Unit))) fun r'' ↦
          (simulateQ (W.eager tab) ((Props.encTcrCtr W encCtr slotColl).judge P r''.2
            r''.1)).toQuantumAt (QComp.coinImpl W.spec (QReg.of Unit))) =
        (W.runtime tab).run₂ .instruments (QuantumComp₂.pure (encJ (W.hashOf tab) P r'.2
          (encPick P (encTgAt (W.hashOf tab) P s r)
            (encPairs (W.hashOf tab) (encDataAt (W.hashOf tab) P s r).pk r'.1.1)))) := by
    intro r'
    refine run₂_eq_of_classicalOn (((classicalOn_coinImpl_toQuantumAt _ _).bind_id fun r'' ↦
      classicalOn_coinImpl_toQuantumAt _ _).congr ?_ rfl) (classicalOn_pure _)
    rw [run_encRedPost, pure_bind]
    exact simulateQ_encJudge W tab P _ _
  refine le_of_le_of_eq ?_ (probAt_eq_of_run₂ W tab (run₂_bind_congr rfl htail)).symm
  rw [← QuantumComp₂.map_eq_bind_pure, kRunL_eq_map, map_map_qcomp]
  exact encTail_le W tab A P (encDataAt (W.hashOf tab) P s r) _
    (encDataAt_pk (W.hashOf tab) P s r) fun g hg ↦ encDec_imp (W.hashOf tab) P s r Tb hTb g hg

end Run

/-! ## Charges -/

section Charges

theorem encH_eq : encH W = fun l ↦ liftW EncCtrPorts (W.hash l) :=
  rfl

/-- A world program makes no EncTCR+C query. -/
theorem queryCostAtMost_liftW_enc {α : Type} (oa : OracleComp W.Oracles α) (b : ℕ) :
    Common.QueryCostAtMost (liftW EncCtrPorts oa) (portCost W (R' := EncCtrPorts)) b := by
  unfold liftW
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [simulateQ_pure]
    trivial
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (OracleComp.isQueryBound_query_bind_iff _ _ _ _ _).mpr ⟨Nat.zero_le _, ih⟩

theorem queryCostAtMost_portQ_enc (q : EncCQ) :
    Common.QueryCostAtMost (portQ W EncCtrPorts q) (portCost W (R' := EncCtrPorts)) 1 :=
  (OracleComp.isQueryBound_query_iff _ _ _ _).mpr le_rfl

theorem queryCostAtMost_encAsk (s : KeygenDomain → Digest) (p : RawPos) (t : RawPos → Digest) :
    Common.QueryCostAtMost (encAsk W s p t) (portCost W (R' := EncCtrPorts)) 1 := by
  unfold encAsk
  cases encSecDom p with
  | some d => trivial
  | none => exact queryCostAtMost_portQ_enc W _

theorem queryCostAtMost_encFold (s : KeygenDomain → Digest) :
    ∀ (L : List Pos) (t : RawPos → Digest), Common.QueryCostAtMost
      (L.foldlM (buildStep (encAsk W s)) t) (portCost W (R' := EncCtrPorts)) L.length
  | [], _ => trivial
  | p :: L, t => by
    rw [List.foldlM_cons, List.length_cons, show L.length + 1 = (1 + 0) + L.length by omega]
    exact queryCostAtMost_bind _ (queryCostAtMost_bind _ (queryCostAtMost_encAsk W s p.1 t)
      fun _ ↦ trivial) fun t' ↦ queryCostAtMost_encFold s L t'

theorem queryCostAtMost_encTargets (msg : Key → Digest) :
    ∀ Ks : List Key, Common.QueryCostAtMost (encTargets W msg Ks)
      (portCost W (R' := EncCtrPorts)) Ks.length
  | [] => trivial
  | K :: Ks => by
    rw [encTargets, List.length_cons, show Ks.length + 1 = 1 + (Ks.length + 0) by omega]
    exact queryCostAtMost_bind _ (queryCostAtMost_portQ_enc W _) fun _ ↦
      queryCostAtMost_bind _ (queryCostAtMost_encTargets msg Ks) fun _ ↦ trivial

/-- The setup makes one EncTCR+C query per key position at most, one per key in use, and the
reveal. -/
theorem queryCostAtMost_encRedPre :
    Common.QueryCostAtMost (encRedPre W) (portCost W (R' := EncCtrPorts))
      (keyOrder.length + encKeys.length + 1) := by
  rw [show keyOrder.length + encKeys.length + 1 =
    0 + (0 + (keyOrder.length + (encKeys.length + (1 + 0)))) by omega]
  exact queryCostAtMost_bind _ (queryCostAtMost_liftW_enc W _ _) fun s ↦
    queryCostAtMost_bind _ (queryCostAtMost_liftW_enc W _ _) fun _ ↦
      queryCostAtMost_bind _ (queryCostAtMost_encFold W s keyOrder _) fun _ ↦
        queryCostAtMost_bind _ (queryCostAtMost_encTargets W _ encKeys) fun _ ↦
          queryCostAtMost_bind _ (queryCostAtMost_portQ_enc W _) fun _ ↦ trivial

/-- The signer makes no EncTCR+C query. -/
theorem queryCostAtMost_encRedSign (st : EncData × SignLog) (M : Message) :
    Common.QueryCostAtMost (encRedSign W st M) (portCost W (R' := EncCtrPorts)) 0 := by
  have hsign : Qrom.Sphincs.LeanSphincsOver.sign
      (routeHash st.1.P (fun d ↦ pure (st.1.s d)) (fun M ↦ pure (st.1.r M)) (encH W)) 0 M =
      liftW EncCtrPorts (Qrom.Sphincs.LeanSphincsOver.sign
        (routeHash st.1.P (fun d ↦ pure (st.1.s d)) (fun M ↦ pure (st.1.r M)) W.hash) 0 M) := by
    simp only [encH_eq, liftW, Over.simulateQ_sign, simulateQ_routeHash, simulateQ_pure]
  simp only [encRedSign, hsign]
  exact queryCostAtMost_bind _ (n₁ := 0) (n₂ := 0) (queryCostAtMost_liftW_enc W _ 0)
    fun _ ↦ trivial

theorem queryCostAtMost_recRun_enc
    (hash : HashInput → OracleComp (W.Oracles + EncCtrPorts) HashOutput)
    (hh : ∀ x, Common.QueryCostAtMost (hash x) (portCost W (R' := EncCtrPorts)) 0) {α : Type}
    (x : OracleComp SchemeHashSpec α) :
    ∀ l : List HashInput, Common.QueryCostAtMost ((simulateQ (recImpl hash) x).run l)
      (portCost W (R' := EncCtrPorts)) 0 := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro l
    rw [simulateQ_pure, StateT.run_pure]
    trivial
  | query_bind t k ih =>
    intro l
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hq : (recImpl hash t).run l = (fun o ↦ (o, l ++ [t])) <$> hash t := by
      simp [recImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_modify]
    rw [hq, bind_map_left]
    exact queryCostAtMost_bind _ (n₁ := 0) (n₂ := 0) (hh t) fun o ↦ ih o _

theorem queryCostAtMost_mapM_encH :
    ∀ xs : List HashInput, Common.QueryCostAtMost (xs.mapM (encH W))
      (portCost W (R' := EncCtrPorts)) 0
  | [] => by
    rw [List.mapM_nil]
    trivial
  | x :: xs => by
    rw [List.mapM_cons]
    exact queryCostAtMost_bind _ (n₁ := 0) (n₂ := 0) (queryCostAtMost_liftW_enc W _ 0) fun _ ↦
      queryCostAtMost_bind _ (n₁ := 0) (n₂ := 0) (queryCostAtMost_mapM_encH xs) fun _ ↦ trivial

/-- The output makes no EncTCR+C query. -/
theorem queryCostAtMost_encRedPost (a : EncData) (f : Forgery) (st : EncData × SignLog) :
    Common.QueryCostAtMost (encRedPost W a f st) (portCost W (R' := EncCtrPorts)) 0 :=
  queryCostAtMost_bind _ (n₁ := 0) (n₂ := 0) (queryCostAtMost_recRun_enc W (encH W)
    (fun _ ↦ queryCostAtMost_liftW_enc W _ 0) _ []) fun rv ↦
    queryCostAtMost_bind _ (n₁ := 0) (n₂ := 0) (queryCostAtMost_mapM_encH W rv.2) fun _ ↦ trivial

/-- **The reduction's hash calls**: `A`'s hash calls plus the honest work of the setup (`c₀`), of
each signing request (`k`) and of the output (`c₁`). -/
theorem isChargeBound_encRed_hash (A : SAdv W) {c₀ c₁ k n m : ℕ}
    (hpre : Common.QueryCostAtMost (encRedPre W) (hcallCost W (R' := EncCtrPorts)) c₀)
    (hσ : ∀ st M,
      Common.QueryCostAtMost (encRedSign W st M) (hcallCost W (R' := EncCtrPorts)) k)
    (hpost : ∀ a f st,
      Common.QueryCostAtMost (encRedPost W a f st) (hcallCost W (R' := EncCtrPorts)) c₁)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (encRed W A ()) (cmdCharge hashCharge) (c₀ + ((n + k * m) + c₁)) :=
  isChargeBound_slRed_hash W (encRedPre W) (fun a ↦ A a.pk) (fun a ↦ (a, [])) (encRedSign W)
    (encRedPost W) hpre hσ hpost (fun a ↦ hn a.pk) fun a ↦ hm a.pk

/-- **The reduction's EncTCR+C queries**: at most one evaluation per key position, one target per
key in use and the reveal, all in the setup; none per signing request and none in the output. -/
theorem isChargeBound_encRed_call (A : SAdv W) {m : ℕ}
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (encRed W A ()) (cmdCharge callCharge)
      ((keyOrder.length + encKeys.length + 1) + (0 * m + 0)) :=
  isChargeBound_slRed_call W (encRedPre W) (fun a ↦ A a.pk) (fun a ↦ (a, [])) (encRedSign W)
    (encRedPost W) (queryCostAtMost_encRedPre W) (fun st M ↦ queryCostAtMost_encRedSign W st M)
    (fun a f st ↦ queryCostAtMost_encRedPost W a f st) fun a ↦ hm a.pk

end Charges

end Quantum.StdModel.Sphincs

end
