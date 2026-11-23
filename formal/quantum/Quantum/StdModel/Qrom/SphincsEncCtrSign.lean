module

public import Quantum.StdModel.Qrom.SphincsEncCtrDefs

@[expose] public section

/-!
# EncTCR+C at leanSPHINCS B4: the signer on the trials it reads

* **The signer reads only its path's trials** (`EncOkFrom`, `EncPathOk`): a hash answering the
  table's positions, call 1 of each digest and, for the three keys of the index of `M`, the
  encoding trials of the counter search up to the first codeword returns the table's signature of
  `M` (`sign_eq_pure_of_path`), the weakening of `Quantum.Qrom.Sphincs.sign_eq_pure`, which asks
  for every encoding trial.
* **The routed hash** (`routeHash`) answers the table of the routed digests on the table's
  positions and call 1 of each digest when the hash does (`answersTable_routeHash_of`,
  `answersDigest_routeHash_of`), and passes every encoding input to the hash
  (`routeHash_encInput`).
* **The built digests** (`tf_eq_dig_of_fix`): digests satisfying the build's equations at every key
  position are those of `digTable`; their key messages are the table's layer messages
  (`keyMessage_keyOf_eq`), and the keys of an index are in use (`keyIn_keyOf`).
-/

open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Key keyOf msgPos leafOfIndex_lt messageDigestInput treeOfIndex_topLayer)

namespace Quantum.StdModel.Qrom.SphEnc

open Quantum.Qrom.Sphincs Quantum.StdModel.Sphincs

/-! ## The signer on the trials it reads -/

section Sign

variable {m : Type → Type} [Monad m]

/-- **The hash answers the counter search** of the key `(l, τ, e)` on `message` by `H`, from
`counter`, for `attempts` counters, up to the first codeword. -/
def EncOkFrom (hash : HashInput → m HashOutput) (v : QTable)
    (H : Quantum.Qrom.HashDomain → HashOutput) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (message : Digest) : ℕ → ℕ → Prop
  | 0, _ => True
  | a + 1, c =>
    hash (addressedHashInput v.publicSeed (hashDomainFields (.encoding l τ e))
        (littleEndianBytes 16 message ++ bigEndianBytes 4 (BitVec.ofNat counterBits c))) =
        pure (H (encCell v.publicSeed l τ e message (BitVec.ofNat counterBits c))) ∧
      (TargetSum.decodeDigest (v.encDigest H l τ e message (BitVec.ofNat counterBits c)) = none →
        EncOkFrom hash v H l τ e message a (c + 1))

/-- **The hash answers the counter searches of the index `idx`**: those of its three keys on
their messages. -/
def EncPathOk (hash : HashInput → m HashOutput) (v : QTable)
    (H : Quantum.Qrom.HashDomain → HashOutput) (idx : Index) : Prop :=
  ∀ l : Layer, EncOkFrom hash v H l (treeOfIndex l idx) (leafOfIndex l idx) (v.layerMessage idx l)
    encodingAttemptLimit 0

variable [LawfulMonad m] {S0 : MasterSeed} {v : QTable}
  {H : Quantum.Qrom.HashDomain → HashOutput} {hash : HashInput → m HashOutput}

theorem otsSignFrom_eq_pure_of_ok (hT : AnswersTable S0 v hash) {l : Layer} {τ : TreeIndex}
    {e : TreeLeafIndex} (hτ : τ.val < 2 ^ Quantum.Sphincs.treeBits l)
    (he : e.val < 2 ^ layerHeight l) (message : Digest) : ∀ attempts counter,
      EncOkFrom hash v H l τ e message attempts counter →
      LeanSphincsOver.otsSignFrom hash (v.expandedKey S0) l τ e message attempts counter =
        pure ((v.selectFrom H l τ e message attempts counter).map fun sel ↦
          (sel.1, fun i ↦ v.chainValue l τ e i (sel.2 i).val))
  | 0, _, _ => rfl
  | attempts + 1, counter, ⟨h1, h2⟩ => by
    have henc : LeanSphincsOver.encode hash (v.expandedKey S0).publicSeed l τ e message
        (BitVec.ofNat counterBits counter) =
        pure (TargetSum.decodeDigest
          (v.encDigest H l τ e message (BitVec.ofNat counterBits counter))) := by
      simp only [LeanSphincsOver.encode, LeanSphincsOver.tweakableHash,
        LeanSphincsOver.addressedHash, QTable.expandedKey_publicSeed, h1, pure_bind]
      rfl
    rw [LeanSphincsOver.otsSignFrom, henc, pure_bind, QTable.selectFrom]
    cases hd : TargetSum.decodeDigest
        (v.encDigest H l τ e message (BitVec.ofNat counterBits counter)) with
    | none => exact otsSignFrom_eq_pure_of_ok hT hτ he message attempts (counter + 1) (h2 hd)
    | some x =>
      simp only [otsSecrets_eq_pure hT hτ he, pure_bind, chainWalk_eq_pure hT hτ he,
        sequenceFin_pure, Option.map_some]

theorem signLayer_eq_pure_of_ok (hT : AnswersTable S0 v hash) {top : List (List Digest)}
    (htop : LevelsOf v topLayer 0 top) (idx : Index) (layer : Layer) (message : Digest)
    (hE : EncOkFrom hash v H layer (treeOfIndex layer idx) (leafOfIndex layer idx) message
      encodingAttemptLimit 0) :
    LeanSphincsOver.signLayer hash (v.expandedKey S0) top idx layer message =
      pure ((v.layerSignature H layer (treeOfIndex layer idx) (leafOfIndex layer idx)
        message).map fun sig ↦ (sig, v.treeRoot layer (treeOfIndex layer idx))) := by
  have hτ := treeOfIndex_lt layer idx
  have he := leafOfIndex_lt layer idx
  rw [LeanSphincsOver.signLayer, LeanSphincsOver.otsSign,
    otsSignFrom_eq_pure_of_ok hT hτ he message _ _ hE, pure_bind, QTable.layerSignature,
    QTable.select]
  cases v.selectFrom H layer (treeOfIndex layer idx) (leafOfIndex layer idx) message
      encodingAttemptLimit 0 with
  | none => rfl
  | some sel =>
    simp only [Option.map_some]
    by_cases h : layer = topLayer
    · subst h
      obtain ⟨hpath, hroot⟩ := levelsOf_fields htop (leafOfIndex topLayer idx) he
      rw [ite_eq_left rfl, pure_bind, treeOfIndex_topLayer, hpath, hroot]
    · obtain ⟨levels, hl, hlev⟩ := treeLevels_eq_pure (S0 := S0) (hash := hash) hT hτ
      obtain ⟨hpath, hroot⟩ := levelsOf_fields hlev (leafOfIndex layer idx) he
      rw [ite_eq_right h, hl, pure_bind, hpath, hroot]

/-- **Signing returns the table's signature** over a hash answering the table, call 1 of each
digest and the counter searches of the index of the message. -/
theorem sign_eq_pure_of_path (hT : AnswersTable S0 v hash) (hD : AnswersDigest v hash)
    (M : Message) (hE : EncPathOk hash v H (v.index M)) :
    LeanSphincsOver.sign hash S0 M = pure (v.signature H M) := by
  obtain ⟨top, htop, hlev⟩ := keygenInternal_eq_pure hT
  have hI : digestIndex (v.messageDigest M) = v.index M := rfl
  have hV : digestForsLeaves (v.messageDigest M) = v.leaves M := rfl
  have h0 := signLayer_eq_pure_of_ok hT hlev (v.index M) 0 (v.forsKey (v.index M)) (hE 0)
  have h1 := signLayer_eq_pure_of_ok hT hlev (v.index M) 1
    (v.treeRoot 0 (treeOfIndex 0 (v.index M))) (hE 1)
  have h2 := signLayer_eq_pure_of_ok hT hlev (v.index M) 2
    (v.treeRoot 1 (treeOfIndex 1 (v.index M))) (hE 2)
  rw [LeanSphincsOver.sign, expandKey_eq_pure hT, pure_bind, LeanSphincsOver.signWithExpandedKey,
    htop, pure_bind]
  simp only [prfMessage_eq_randomizer hT, messageDigest_eq_pure hT hD, pure_bind, hI, hV,
    forsOpen_eq_pure hT, h0]
  simp only [QTable.signature, QTable.layerSig, QTable.layerMessage_zero,
    QTable.layerMessage_one, QTable.layerMessage_two]
  cases v.layerSignature H 0 (treeOfIndex 0 (v.index M)) (leafOfIndex 0 (v.index M))
      (v.forsKey (v.index M)) with
  | none => rfl
  | some bottom =>
    simp only [Option.map_some, h1, pure_bind]
    cases v.layerSignature H 1 (treeOfIndex 1 (v.index M))
        (leafOfIndex 1 (v.index M)) (v.treeRoot 0 (treeOfIndex 0 (v.index M))) with
    | none => rfl
    | some middle =>
      simp only [Option.map_some, h2, pure_bind]
      cases v.layerSignature H 2 (treeOfIndex 2 (v.index M))
          (leafOfIndex 2 (v.index M)) (v.treeRoot 1 (treeOfIndex 1 (v.index M))) with
      | none => rfl
      | some top => rfl

end Sign

/-! ## The routed hash -/

section Route

variable {m : Type → Type} [Monad m] {P : PublicParameter} {sec : KeygenDomain → m Digest}
  {rnd : Message → m Digest} {hash : HashInput → m HashOutput}

/-- The routed hash passes an input that is no secret's routed input to the hash. -/
theorem routeHash_eq_of_ne {x : HashInput} (hx : ∀ q : Pos, IsSecret q.1 → secInput P q.1 ≠ x) :
    routeHash P sec rnd hash x = hash x := by
  unfold routeHash
  exact dite_eq_right fun ⟨q, hq, e⟩ ↦ hx q hq e

/-- **The routed hash passes every encoding input to the hash**: an encoding input is no
secret's input (the kinds of their slots differ). -/
theorem routeHash_encInput (P : PublicParameter) (sec : KeygenDomain → m Digest)
    (rnd : Message → m Digest) (hash : HashInput → m HashOutput) (seed : PublicParameter)
    (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (msg : Digest) (c : EncodingCounter) :
    routeHash P sec rnd hash (addressedHashInput seed (hashDomainFields (.encoding l τ e))
      (littleEndianBytes 16 msg ++ bigEndianBytes 4 c)) =
      hash (addressedHashInput seed (hashDomainFields (.encoding l τ e))
        (littleEndianBytes 16 msg ++ bigEndianBytes 4 c)) := by
  refine routeHash_eq_of_ne fun ⟨q, hq⟩ hs ex ↦ ?_
  obtain ⟨v, hP, hK⟩ : ∃ v : QTable, v.publicSeed = P ∧ v.prfKey = 0 :=
    ⟨digTable (fun _ ↦ 0) P (fun _ ↦ 0) (fun _ ↦ 0), publicSeed_digTable _ _ _ _,
      prfKey_digTable _ _ _ _⟩
  have hin : slotInput (v.expandedKey 0) v.root (posSlot v q) (posPayload v q) =
      slotInput (pubKey seed) 0 (.enc l τ e) (msg, c) :=
    (posInput_eq_secInput v hP hK hs).trans ex
  have hk := kindsOf_eq_of_slotInput_eq hin encTwKinds
  cases q <;> first | exact (hs : False).elim | exact Nat.zero_ne_one hk

variable [LawfulMonad m] {h : HashInput → HashOutput} {s : KeygenDomain → Digest}
  {r : Message → Digest}

/-- **The routed hash answers the table of the routed digests** when the hash answers its public
positions by `h`. -/
theorem answersTable_routeHash_of (hs : ∀ d, sec d = pure (s d)) (hr : ∀ M, rnd M = pure (r M))
    (hK : ∀ p : RawPos, p.InRange → ¬IsSecret p →
      hash (posInput 0 (digTable h P s r) p) = pure (h (posInput 0 (digTable h P s r) p))) :
    AnswersTable 0 (digTable h P s r) (routeHash P sec rnd hash) := fun p hp ↦ by
  by_cases hsec : IsSecret p
  · exact answersSecrets_routeHash hs hr ⟨p, hp⟩ hsec
  · have hne : ∀ q : Pos, IsSecret q.1 → secInput P q.1 ≠ posInput 0 (digTable h P s r) p :=
      fun q hq e ↦ hsec (by
        obtain rfl := posInput_inj (q := ⟨p, hp⟩) ((posInput_eq_secInput (digTable h P s r)
          (publicSeed_digTable h P s r) (prfKey_digTable h P s r) hq).trans e)
        exact hq)
    rw [routeHash_eq_of_ne hne, hK p hp hsec]
    exact congrArg pure ((honest_digTable h P s r).out ⟨p, hp⟩ hsec).symm

omit [LawfulMonad m] in
/-- **The routed hash answers call 1 of each digest** when the hash answers it by `h`. -/
theorem answersDigest_routeHash_of
    (hD : ∀ M, hash (messageDigestInput ((digTable h P s r).randomizer M)
      (digTable h P s r).publicSeed (digTable h P s r).root M 1) =
      pure (h (messageDigestInput ((digTable h P s r).randomizer M)
        (digTable h P s r).publicSeed (digTable h P s r).root M 1))) :
    AnswersDigest (digTable h P s r) (routeHash P sec rnd hash) := fun M ↦ by
  set v := digTable h P s r with hv
  have hne : ∀ q : Pos, IsSecret q.1 →
      secInput P q.1 ≠ messageDigestInput (v.randomizer M) v.publicSeed v.root M 1 := by
    intro q hq e
    rw [← posInput_eq_secInput v (publicSeed_digTable h P s r) (prfKey_digTable h P s r) hq]
      at e
    exact sphincs_slotInput_ne (v.expandedKey 0) v.root (slotInRange_posSlot v q)
      (s' := .hmsg (v.randomizer M) M 1) trivial
      (posSlot_ne_of_secret v hq (fun _ e' ↦ by cases e') (fun _ e' ↦ by cases e')
        fun _ e' ↦ by cases e') _ () e
  rw [routeHash_eq_of_ne hne, hD M]
  exact congrArg pure ((honest_digTable h P s r).call1 M).symm

end Route

/-! ## The built digests -/

section Built

variable {h : HashInput → HashOutput} {P : PublicParameter} {s : KeygenDomain → Digest}
  {r : Message → Digest}

/-- **Digests satisfying the build's equations at every key position are `digTable`'s.** -/
theorem tf_eq_dig_of_fix {tf : RawPos → Digest}
    (hsec : ∀ p : Pos, KeyPart p.1 → IsSecret p.1 → ∃ d, encSecDom p.1 = some d ∧ tf p.1 = s d)
    (hpub : ∀ p : Pos, KeyPart p.1 → ¬IsSecret p.1 →
      tf p.1 = thSlot h P (keySlot p.1) (keyPayload p.1 tf)) :
    ∀ p : Pos, KeyPart p.1 → tf p.1 = (digTable h P s r).dig p.1 := by
  intro p
  refine (measure fun q : Pos ↦ q.1.rank).wf.induction
    (C := fun p : Pos ↦ KeyPart p.1 → tf p.1 = (digTable h P s r).dig p.1) p
    (fun p ih hk ↦ ?_)
  by_cases hs : IsSecret p.1
  · obtain ⟨d, hd, htf⟩ := hsec p hk hs
    rw [htf]
    obtain ⟨p, hp⟩ := p
    cases p with
    | chainStart l τ e i =>
      obtain rfl := Option.some.inj hd
      exact (dig_chainStart_digTable h P s r hp).symm
    | forsSecret idx κ j =>
      obtain rfl := Option.some.inj hd
      exact (dig_forsSecret_digTable h P s r idx κ j).symm
    | _ => first | exact (hk : False).elim | exact (hs : False).elim
  · have ht : ∀ q : Pos, KeyPart q.1 → q.1.rank < p.1.rank →
        tf q.1 = (digTable h P s r).dig q.1 := fun q hq hr ↦ ih q hr hq
    rw [hpub p hk hs, keyPayload_congr p.1 ht, ← dig_digTable_eq_thSlot h P s r p hk hs]

/-- **The key message of `K_l(idx)`** under digests agreeing with a table on the key's positions
is the table's layer message. -/
theorem keyMessage_keyOf_eq (tf : RawPos → Digest) (v : QTable)
    (hd : ∀ p : Pos, KeyPart p.1 → tf p.1 = v.dig p.1) (l : Layer) (idx : Index) :
    keyMessage (ofDig tf) (keyOf l idx) = v.layerMessage idx l :=
  (encValuePos_congr (encDig_ofDig hd) (msgPos _)).trans (QTable.msgPos_eq v l idx)

/-- The keys of an index are in use. -/
theorem keyIn_keyOf (l : Layer) (idx : Index) : keyOf l idx ∈ encKeys :=
  mem_encKeys.2 ⟨treeOfIndex_lt l idx, leafOfIndex_lt l idx⟩
end Built

end Quantum.StdModel.Qrom.SphEnc

end
