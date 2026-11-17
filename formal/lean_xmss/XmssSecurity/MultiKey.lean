module

public import XmssSecurity.Rpm
public import Common.MultiKey.Main
public import LeanXmss.Bytes
public import XmssSecurity.Proof.RandomOracle

@[expose] public section

/-!
# leanXMSS with many keys

`XmssSecurity.leanXmss_multiKey`: leanXMSS is multi-key strongly unforgeable in the
random-permutation model, for up to `2^32` keys, each signing at most `lifetime` requests:
`k · (q + 2^10 + k) · 2^-127`. It is
`Common.SufCma.MultiKey.multiKeyStronglyUnforgeable_of_romBoundAdv` for the hash-query scheme with
the crate's key (`schemeWithHashFromSeed`), its single-key bound at the adversary's own count
(`XmssSecurity.romBoundAdvFromSeed`), and two facts of the scheme.

The public ownership of an input (`ownedPub`): the input is `P || A || payload` with `P` the key's
public parameter, an address of any type but the parameter derivation's (`TWEAK_PARAMETER = 5`)
and a payload of more than 8 bytes (`OwnedBy`). Key generation queries the seed derivation
`"leanXMSS" || S_0` (40 bytes, owned by no key), the parameter derivation `0 || A_param || S`
(owned by no key), and inputs owned by its own parameter (`Shape`); the signer derives `S` again
from `S_0` (key generation's first query) and otherwise queries inputs its parameter owns; the
verifier only inputs its public key's parameter owns (`separation`).

A fresh key clashes with a fixed one (`Common.SufCma.MultiKey.Clash`) only if their seeds `S_0`,
their scheme seeds `S` or their parameters `P` agree (`Shape.clash`). In the random-oracle model
`S_0` is uniform, `S` the answer of a first query to an empty cache, and `P` the truncation of the
answer of a second, fresh query, so the clash has probability at most
`2^-256 + 2^-256 + 2^-128` (`clash_le`).
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma Common.SufCma.MultiKey
open HashSig HashSig.OverPermutation LeanXmss

namespace LeanXmss.MultiKey

/-! ## Inputs and their ownership -/

/-- The parameter derivation's input `0 || A_param || S` (`keygenDomainFields .parameter`). -/
def paramInput (seed : MasterSeed) : HashInput :=
  thInput 0 (keygenDomainFields .parameter) (littleEndianBytes 32 seed)

/-- **An input owned by the public parameter `P`**: `P || A || payload` at an address of any type
but the parameter derivation's, with a payload of more than 8 bytes. -/
def OwnedBy (P : PublicParameter) (x : HashInput) : Prop :=
  ∃ fields payload, x = thInput P fields payload ∧ fields.tag ≠ 5 ∧ 9 ≤ payload.length

/-- **The public ownership**: the inputs a public key's parameter owns. -/
def ownedPub (pk : HashSig.PublicKey) (x : HashInput) : Prop := OwnedBy pk.parameter x

noncomputable instance (pk : HashSig.PublicKey) : DecidablePred (ownedPub pk) :=
  Classical.decPred _

theorem OwnedBy.length_gt {P : PublicParameter} {x : HashInput} (h : OwnedBy P x) :
    40 < x.length := by
  obtain ⟨fields, payload, rfl, -, hp⟩ := h
  rw [Common.XmssCost.thInput_length]
  omega

theorem not_ownedBy_seed (P : PublicParameter) (s : MasterSeed) :
    ¬OwnedBy P (seedHashInput s) := by
  intro h
  have := h.length_gt
  rw [seedHashInput_length] at this
  omega

theorem not_ownedBy_param (P : PublicParameter) (S : MasterSeed) :
    ¬OwnedBy P (paramInput S) := by
  rintro ⟨fields, payload, h, htag, -⟩
  have h' : littleEndianBytes 16 0 ++ addressBytes (keygenDomainFields .parameter) ++
      littleEndianBytes 32 S = littleEndianBytes 16 P ++ addressBytes fields ++ payload := h
  obtain ⟨hf, -, -⟩ := fieldInput_injective h'
  rw [← hf] at htag
  exact htag rfl

theorem OwnedBy.unique {P P' : PublicParameter} {x : HashInput} (h : OwnedBy P x)
    (h' : OwnedBy P' x) : P = P' := by
  obtain ⟨fields, payload, rfl, -, -⟩ := h
  obtain ⟨fields', payload', h', -, -⟩ := h'
  exact (fieldInput_injective h').2.1

theorem paramInput_length (S : MasterSeed) : (paramInput S).length = 64 := by
  rw [paramInput, Common.XmssCost.thInput_length, bytesLE_length]

theorem paramInput_ne_seed (S s : MasterSeed) : paramInput S ≠ seedHashInput s := by
  intro h
  have := congrArg List.length h
  rw [paramInput_length, seedHashInput_length] at this
  omega

theorem paramInput_injective {S S' : MasterSeed} (h : paramInput S = paramInput S') : S = S' :=
  bytesLE_injective (fieldInput_injective h).2.2

/-! ## The shape of a key's record -/

/-- An input of key generation from the seed `S_0 = s`, the scheme seed `S` and the parameter `P`:
the seed derivation, the parameter derivation, or an input `P` owns. -/
def KeygenQuery (s S : MasterSeed) (P : PublicParameter) (x : HashInput) : Prop :=
  x = seedHashInput s ∨ x = paramInput S ∨ OwnedBy P x

/-- **A key record of seed `s`, scheme seed `S` and parameter `P`**: its public parameter and kept
key, the seed derivation among its queries, and every query of key generation's. -/
structure Shape (z : KeyRec HashSig.PublicKey LeanXmss.SecretKey) (s S : MasterSeed)
    (P : PublicParameter) : Prop where
  param : z.1.1.parameter = P
  key : z.1.2 = ⟨s, P⟩
  seed_mem : seedHashInput s ∈ z.2
  log : ∀ x ∈ z.2, KeygenQuery s S P x

/-- **Two keys clash only if their seeds, scheme seeds or parameters agree.** -/
theorem Shape.clash {za zb : KeyRec HashSig.PublicKey LeanXmss.SecretKey}
    {sa Sa sb Sb : MasterSeed} {Pa Pb : PublicParameter} (ha : Shape za sa Sa Pa)
    (hb : Shape zb sb Sb Pb) (h : Clash ownedPub za zb) : sa = sb ∨ Sa = Sb ∨ Pa = Pb := by
  obtain ⟨x, ⟨hxb, hxa⟩ | ⟨hxa, hxb⟩⟩ := h
  · have ha' : KeygenQuery sa Sa Pa x := hxa.elim (ha.log x) fun h ↦
      Or.inr (Or.inr (by rw [← ha.param]; exact h))
    rcases hb.log x hxb with rfl | rfl | hb' <;> rcases ha' with ha' | ha' | ha'
    · exact Or.inl (seedHashInput_injective ha').symm
    · exact absurd ha'.symm (paramInput_ne_seed _ _)
    · exact absurd ha' (not_ownedBy_seed _ _)
    · exact absurd ha' (paramInput_ne_seed _ _)
    · exact Or.inr (Or.inl (paramInput_injective ha').symm)
    · exact absurd ha' (not_ownedBy_param _ _)
    · subst ha'; exact absurd hb' (not_ownedBy_seed _ _)
    · subst ha'; exact absurd hb' (not_ownedBy_param _ _)
    · exact Or.inr (Or.inr (ha'.unique hb'))
  · have hxa' : OwnedBy Pa x := by rw [← ha.param]; exact hxa
    have hxb' : OwnedBy Pb x := by rw [← hb.param]; exact hxb
    exact Or.inr (Or.inr (hxa'.unique hxb'))

/-! ## Queries in a part of the domain: the combinators -/

section Combinators

variable {Q : HashInput → Prop}

theorem queriesIn_mono {Q' : HashInput → Prop} (hQ : ∀ x, Q x → Q' x) {α : Type}
    {X : OracleComp SchemeHashSpec α} (hX : QueriesIn Q X) : QueriesIn Q' X := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [queriesIn_query_bind] at hX ⊢
    exact ⟨hQ t hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem queriesIn_sequenceFin {γ : Type} :
    ∀ {n : ℕ} (cs : Fin n → OracleComp SchemeHashSpec γ), (∀ j, QueriesIn Q (cs j)) →
      QueriesIn Q (sequenceFin cs)
  | 0, _, _ => trivial
  | n + 1, cs, h => by
    simp only [sequenceFin]
    exact queriesIn_bind (h 0) fun _ ↦
      queriesIn_bind (queriesIn_sequenceFin _ fun j ↦ h j.succ) fun _ ↦ trivial

theorem queriesIn_walkChain {k : ℕ}
    (step : Fin k → HashSig.Digest → OracleComp SchemeHashSpec HashSig.Digest)
    (h : ∀ t v, QueriesIn Q (step t v)) :
    ∀ start steps v, QueriesIn Q (walkChain step start steps v)
  | _, 0, _ => trivial
  | start, steps + 1, v => by
    simp only [walkChain]
    refine queriesIn_bind (queriesIn_walkChain step h start steps v) fun _ ↦ ?_
    split
    · exact h _ _
    · trivial

theorem queriesIn_foldPath
    (node : ℕ → ℕ → HashInput → OracleComp SchemeHashSpec HashSig.Digest)
    (h : ∀ l i a b, QueriesIn Q (node l i (nodePayload a b))) (leafIndex : ℕ)
    (sibling : ℕ → HashSig.Digest) :
    ∀ levels v, QueriesIn Q (foldPath node leafIndex sibling levels v)
  | 0, _ => trivial
  | l + 1, v => by
    simp only [foldPath]
    refine queriesIn_bind (queriesIn_foldPath node h leafIndex sibling l v) fun _ ↦ ?_
    split
    · exact h _ _ _ _
    · exact h _ _ _ _

theorem queriesIn_buildTree (leaf : ℕ → OracleComp SchemeHashSpec HashSig.Digest)
    (node : ℕ → ℕ → HashInput → OracleComp SchemeHashSpec HashSig.Digest)
    (hleaf : ∀ i, QueriesIn Q (leaf i))
    (hnode : ∀ l i a b, QueriesIn Q (node l i (nodePayload a b))) :
    ∀ l i, QueriesIn Q (buildTree leaf node l i)
  | 0, i => hleaf i
  | l + 1, i => by
    simp only [buildTree]
    exact queriesIn_bind (queriesIn_buildTree leaf node hleaf hnode l _) fun _ ↦
      queriesIn_bind (queriesIn_buildTree leaf node hleaf hnode l _) fun _ ↦ hnode _ _ _ _

theorem queriesIn_oracleHash {x : HashInput} (hx : Q x) :
    QueriesIn Q (Verification.oracleHashWithHash (m := OracleComp HashSpec) x) :=
  queriesIn_query hx

end Combinators

/-! ## The scheme's queries -/

-- A combinator at a literal size must not be unfolded when a bound is elaborated.
attribute [local irreducible] sequenceFin walkChain foldPath buildTree

section SchemeQueries

theorem queriesIn_th {P : PublicParameter} {fields : TweakFields} {payload : HashInput}
    (htag : fields.tag ≠ 5) (hp : 9 ≤ payload.length) :
    QueriesIn (OwnedBy P) (Verification.thWithHash (m := OracleComp HashSpec) P fields payload) :=
  queriesIn_bind (queriesIn_oracleHash ⟨fields, payload, rfl, htag, hp⟩) fun _ ↦ trivial

theorem queriesIn_thPair {P : PublicParameter} {fields : TweakFields} {payload : HashInput}
    (htag : fields.tag ≠ 5) (hp : 9 ≤ payload.length) :
    QueriesIn (OwnedBy P)
      (Verification.thPairWithHash (m := OracleComp HashSpec) P fields payload) :=
  queriesIn_oracleHash ⟨fields, payload, rfl, htag, hp⟩

theorem hashDomainFields_tag (d : HashDomain) : (hashDomainFields d).tag ≠ 5 := by
  cases d <;> simp only [hashDomainFields, tweakFields] <;> decide

theorem queriesIn_tweakable (P : PublicParameter) (d : HashDomain) {payload : HashInput}
    (hp : 9 ≤ payload.length) :
    QueriesIn (OwnedBy P)
      (Verification.tweakableHashWithHash (m := OracleComp HashSpec) P d payload) :=
  queriesIn_th (hashDomainFields_tag d) hp

theorem queriesIn_chainWalk (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (start steps : ℕ) (v : HashSig.Digest) :
    QueriesIn (OwnedBy P)
      (Verification.chainWalkWithHash (m := OracleComp HashSpec) P lay key chainIdx start steps
        v) :=
  queriesIn_walkChain _ (fun _ _ ↦ queriesIn_tweakable _ _ (by
    simp only [Verification.chainPayload, List.length_append, littleEndianBytes, List.length_ofFn]
    omega)) start steps v

theorem queriesIn_leafHash (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → HashSig.Digest) :
    QueriesIn (OwnedBy P)
      (Verification.leafHashWithHash (m := OracleComp HashSpec) P lay key endpoints) :=
  queriesIn_tweakable _ _ (by rw [Common.XmssCost.digestsPayload_length]; decide)

theorem queriesIn_messageDigest (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (randomness : Randomizer) :
    QueriesIn (OwnedBy P)
      (Verification.messageDigestWithHash (m := OracleComp HashSpec) P lay key message
        randomness) :=
  queriesIn_tweakable _ _ (by
    simp only [List.length_append, littleEndianBytes, List.length_ofFn]; omega)

theorem queriesIn_otsLeaf (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (randomness : Randomizer) (values : ChainIndex → HashSig.Digest) :
    QueriesIn (OwnedBy P)
      (Verification.otsLeafWithHash (m := OracleComp HashSpec) P lay key message randomness
        values) := by
  unfold Verification.otsLeafWithHash
  refine queriesIn_bind (queriesIn_messageDigest _ _ _ _ _) fun _ ↦ ?_
  split
  · exact queriesIn_bind (queriesIn_sequenceFin _ fun _ ↦ queriesIn_chainWalk _ _ _ _ _ _ _)
      fun _ ↦ queriesIn_bind (queriesIn_leafHash _ _ _ _) fun _ ↦ trivial
  · trivial

theorem queriesIn_treeFold (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → HashSig.Digest) (levels : ℕ) (v : HashSig.Digest) :
    QueriesIn (OwnedBy P)
      (Verification.treeFoldWithHash (m := OracleComp HashSpec) P lay key path levels v) :=
  queriesIn_foldPath _ (fun _ _ _ _ ↦ queriesIn_tweakable _ _ (by
    simp only [nodePayload, List.length_append, littleEndianBytes, List.length_ofFn]
    omega)) _ _ levels v

theorem queriesIn_layerRoot (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (part : LayerSignature) :
    QueriesIn (OwnedBy P)
      (Verification.layerRootWithHash (m := OracleComp HashSpec) P lay key message part) := by
  unfold Verification.layerRootWithHash
  refine queriesIn_bind (queriesIn_otsLeaf _ _ _ _ _ _) fun leaf ↦ ?_
  rcases leaf with _ | _
  · trivial
  · exact queriesIn_bind (queriesIn_treeFold _ _ _ _ _ _) fun _ ↦ trivial

/-- **The verifier asks only inputs its public key owns.** -/
theorem queriesIn_verify (pk : HashSig.PublicKey) (message : Message) (signature : Signature) :
    QueriesIn (ownedPub pk)
      (Verification.verifyWithHash (m := OracleComp HashSpec) pk message signature) := by
  unfold Verification.verifyWithHash
  refine queriesIn_bind (queriesIn_layerRoot _ _ _ _ _) fun root ↦ ?_
  rcases root with _ | _
  · trivial
  · refine queriesIn_bind (queriesIn_layerRoot _ _ _ _ _) fun root' ↦ ?_
    rcases root' with _ | _ <;> trivial

theorem queriesIn_otsSecrets (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    QueriesIn (OwnedBy P)
      (KeyGenerationAndSigning.otsSecretsWithHash (m := OracleComp HashSpec) P lay key seed) := by
  unfold KeyGenerationAndSigning.otsSecretsWithHash
  exact queriesIn_bind (queriesIn_sequenceFin _ fun _ ↦ queriesIn_thPair
    (by simp only [keygenDomainFields, tweakFields]; decide)
    (by simp only [bytesLE_length]; omega)) fun _ ↦ trivial

theorem queriesIn_oneTimePublicKey (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    QueriesIn (OwnedBy P)
      (KeyGenerationAndSigning.oneTimePublicKeyWithHash (m := OracleComp HashSpec) P lay key
        seed) := by
  unfold KeyGenerationAndSigning.oneTimePublicKeyWithHash
  exact queriesIn_bind (queriesIn_otsSecrets _ _ _ _) fun _ ↦
    queriesIn_sequenceFin _ fun _ ↦ queriesIn_chainWalk _ _ _ _ _ _ _

theorem queriesIn_otsSignFrom (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) (base : Randomizer) :
    ∀ attempts trial, QueriesIn (OwnedBy P)
      (KeyGenerationAndSigning.otsSignFromWithHash (m := OracleComp HashSpec) P lay key seed
        message base attempts trial)
  | 0, _ => by
    simp only [KeyGenerationAndSigning.otsSignFromWithHash]
    trivial
  | attempts + 1, trial => by
    simp only [KeyGenerationAndSigning.otsSignFromWithHash]
    refine queriesIn_bind (queriesIn_messageDigest _ _ _ _ _) fun _ ↦ ?_
    split
    · exact queriesIn_bind (queriesIn_otsSecrets _ _ _ _) fun _ ↦
        queriesIn_bind (queriesIn_sequenceFin _ fun _ ↦ queriesIn_chainWalk _ _ _ _ _ _ _)
          fun _ ↦ trivial
    · exact queriesIn_otsSignFrom P lay key seed message base attempts (trial + 1)

theorem queriesIn_otsSign (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) :
    QueriesIn (OwnedBy P)
      (KeyGenerationAndSigning.otsSignWithHash (m := OracleComp HashSpec) P lay key seed
        message) := by
  unfold KeyGenerationAndSigning.otsSignWithHash
  exact queriesIn_bind (queriesIn_th (by simp only [tweakFields]; decide)
    (by simp only [List.length_append, littleEndianBytes, List.length_ofFn]; omega)) fun _ ↦
      queriesIn_otsSignFrom _ _ _ _ _ _ _ _

theorem queriesIn_treeNode (P : PublicParameter) (lay : Layer) (seed : MasterSeed)
    (level index : ℕ) :
    QueriesIn (OwnedBy P)
      (KeyGenerationAndSigning.treeNodeWithHash (m := OracleComp HashSpec) P lay seed level
        index) :=
  queriesIn_buildTree _ _
    (fun _ ↦ queriesIn_bind (queriesIn_oneTimePublicKey _ _ _ _) fun _ ↦
      queriesIn_leafHash _ _ _ _)
    (fun _ _ _ _ ↦ queriesIn_tweakable _ _ (by
      simp only [nodePayload, List.length_append, littleEndianBytes, List.length_ofFn]
      omega)) level index

theorem queriesIn_treePath (P : PublicParameter) (lay : Layer) (seed : MasterSeed)
    (key : KeyIndex) :
    QueriesIn (OwnedBy P)
      (KeyGenerationAndSigning.treePathWithHash (m := OracleComp HashSpec) P lay seed key) :=
  queriesIn_sequenceFin _ fun _ ↦ queriesIn_treeNode _ _ _ _ _

theorem queriesIn_signLayer (sk : SchemeSeedKey) (lay : Layer) (key : KeyIndex)
    (message : HashInput) :
    QueriesIn (OwnedBy sk.parameter)
      (KeyGenerationAndSigning.signLayerWithHash (m := OracleComp HashSpec) sk lay key
        message) := by
  unfold KeyGenerationAndSigning.signLayerWithHash
  refine queriesIn_bind (queriesIn_otsSign _ _ _ _ _) fun o ↦ ?_
  rcases o with _ | ⟨_, _⟩
  · trivial
  · exact queriesIn_bind (queriesIn_treePath _ _ _ _) fun _ ↦ trivial

/-- **The signer, from `S` and `P`, asks only inputs `P` owns.** -/
theorem queriesIn_sign (sk : SchemeSeedKey) (index : LeafIndex) (message : Message) :
    QueriesIn (OwnedBy sk.parameter)
      (KeyGenerationAndSigning.signWithHash (m := OracleComp HashSpec) sk index message) := by
  unfold KeyGenerationAndSigning.signWithHash
  refine queriesIn_bind (queriesIn_signLayer _ _ _ _) fun o ↦ ?_
  rcases o with _ | _
  · trivial
  · refine queriesIn_bind (queriesIn_treeNode _ _ _ _ _) fun _ ↦
      queriesIn_bind (queriesIn_signLayer _ _ _ _) fun o' ↦ ?_
    rcases o' with _ | _ <;> trivial

theorem queriesIn_keygenRest (key : SchemeSeedKey) :
    QueriesIn (OwnedBy key.parameter) (RandomPermutationModel.keygenRest key) := by
  unfold RandomPermutationModel.keygenRest
  exact queriesIn_bind (queriesIn_treeNode _ _ _ _ _) fun _ ↦ trivial

end SchemeQueries

/-! ## Key generation, logged -/

open RandomPermutationModel

/-- Key generation: the seed derivation, the parameter derivation, then the top tree. -/
theorem keygen_eq (s : MasterSeed) :
    schemeWithHashFromSeed.keygen s =
      (liftM (SchemeHashSpec.query (seedHashInput s)) : OracleComp SchemeHashSpec _) >>=
        fun u₁ ↦ (liftM (SchemeHashSpec.query (paramInput u₁)) : OracleComp SchemeHashSpec _) >>=
          fun u₂ ↦ (fun keys ↦ (keys.1, (⟨s, truncateHash u₂⟩ : LeanXmss.SecretKey))) <$>
            keygenRest ⟨u₁, truncateHash u₂⟩ := by
  simp only [schemeWithHashFromSeed, KeptKey.scheme, keptKey,
    KeyGenerationAndSigning.deriveSchemeSeedKey, Verification.taggedSeedWithHash,
    Verification.thWithHash, bind_assoc, pure_bind]
  rfl

/-- A logged query logs its input first. -/
theorem loggedRun_query_bind {α : Type} (x : HashInput)
    (k : BitVec 256 → OracleComp SchemeHashSpec α) :
    (simulateQ logImpl ((liftM (SchemeHashSpec.query x) : OracleComp SchemeHashSpec _) >>=
      k)).run =
      (liftM (SchemeHashSpec.query x) : OracleComp SchemeHashSpec _) >>= fun u ↦
        (fun p ↦ (p.1, x :: p.2)) <$> (simulateQ logImpl (k u)).run := by
  have h0 : (logImpl x).run = (fun u ↦ (u, [x])) <$>
      (liftM (SchemeHashSpec.query x) : OracleComp SchemeHashSpec _) := by
    simp [logImpl, run_liftM_query_writer]
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, WriterT.run_bind', h0, bind_map_left]
  rfl

/-- A logged run's output is the computation's, and its log holds only queries of the
computation's. -/
theorem logged_support {α : Type} (X : OracleComp SchemeHashSpec α)
    {z : α × List HashInput} (hz : z ∈ support (simulateQ logImpl X).run) :
    z.1 ∈ support X ∧ ∀ Q, QueriesIn Q X → ∀ x ∈ z.2, Q x := by
  induction X using OracleComp.inductionOn generalizing z with
  | pure a =>
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨by simp, fun _ _ x hx ↦ by simp at hx⟩
  | query_bind t k ih =>
    rw [loggedRun_query_bind, mem_support_bind_iff] at hz
    obtain ⟨u, -, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨h1, h2⟩ := ih u hw
    refine ⟨?_, fun Q hQ x hx ↦ ?_⟩
    · rw [mem_support_bind_iff]
      exact ⟨u, by simp, h1⟩
    rw [queriesIn_query_bind] at hQ
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hQ.1
    · exact h2 Q (hQ.2 u) x hx

/-- Key generation after its two derivations, logged. -/
def restLog (s u₁ u₂ : BitVec 256) :
    OracleComp SchemeHashSpec (KeyRec HashSig.PublicKey LeanXmss.SecretKey) :=
  (simulateQ logImpl ((fun keys ↦ (keys.1, (⟨s, truncateHash u₂⟩ : LeanXmss.SecretKey))) <$>
    keygenRest ⟨u₁, truncateHash u₂⟩)).run

theorem loggedKeygen_eq (s : MasterSeed) :
    loggedKeygen schemeWithHashFromSeed s =
      (liftM (SchemeHashSpec.query (seedHashInput s)) : OracleComp SchemeHashSpec _) >>=
        fun u₁ ↦ (fun p ↦ (p.1, seedHashInput s :: p.2)) <$>
          ((liftM (SchemeHashSpec.query (paramInput u₁)) : OracleComp SchemeHashSpec _) >>=
            fun u₂ ↦ (fun p ↦ (p.1, paramInput u₁ :: p.2)) <$> restLog s u₁ u₂) := by
  rw [loggedKeygen, keygen_eq]
  simp only [loggedRun_query_bind]
  rfl

theorem keygenRest_parameter {key : SchemeSeedKey}
    {keys : HashSig.PublicKey × SchemeSeedKey} (h : keys ∈ support (keygenRest key)) :
    keys.1.parameter = key.parameter := by
  simp only [keygenRest, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

theorem shape_of_rest {s u₁ u₂ : BitVec 256} {y : KeyRec HashSig.PublicKey LeanXmss.SecretKey}
    (hy : y ∈ support (restLog s u₁ u₂)) :
    Shape (y.1, seedHashInput s :: paramInput u₁ :: y.2) s u₁ (truncateHash u₂) := by
  obtain ⟨h1, h2⟩ := logged_support _ hy
  have hown := h2 _ (queriesIn_map _ (queriesIn_keygenRest ⟨u₁, truncateHash u₂⟩))
  rw [support_map] at h1
  obtain ⟨keys, hkeys, hy1⟩ := h1
  refine ⟨?_, ?_, by simp, fun x hx ↦ ?_⟩
  · show y.1.1.parameter = _
    rw [← hy1]
    exact keygenRest_parameter hkeys
  · show y.1.2 = _
    rw [← hy1]
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl rfl
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (hown x hx))

theorem shape_of_isKey {s : MasterSeed} {z : KeyRec HashSig.PublicKey LeanXmss.SecretKey}
    (hz : z ∈ support (loggedKeygen schemeWithHashFromSeed s)) : ∃ S P, Shape z s S P := by
  rw [loggedKeygen_eq, mem_support_bind_iff] at hz
  obtain ⟨u₁, -, hz⟩ := hz
  rw [support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [mem_support_bind_iff] at hw
  obtain ⟨u₂, -, hw⟩ := hw
  rw [support_map] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  exact ⟨u₁, truncateHash u₂, shape_of_rest hy⟩

/-! ## The separation facts -/

/-- **The separation facts of leanXMSS** for the public ownership `ownedPub`. -/
theorem separation : Separation schemeWithHashFromSeed ownedPub where
  sign_queries := by
    rintro ⟨⟨pk, sk⟩, log⟩ ⟨s, hs⟩ r
    obtain ⟨S, P, hpar, hkey, hseed, -⟩ := shape_of_isKey hs
    dsimp only at hpar hkey hseed ⊢
    subst hkey
    simp only [schemeWithHashFromSeed, KeptKey.scheme, keptKey,
      KeyGenerationAndSigning.rederiveSchemeSeedKey, bind_assoc, pure_bind]
    exact queriesIn_bind (queriesIn_oracleHash (Or.inr hseed)) fun u ↦
      queriesIn_mono (fun x hx ↦ Or.inl (by rw [ownedPub, hpar]; exact hx))
        (queriesIn_sign ⟨u, P⟩ r.leafIndex r.message)
  verify_queries pk f := queriesIn_verify pk f.message f.signature
  keygen_owned := by
    rintro z ⟨s, hs⟩ x hx pk' hpk
    obtain ⟨S, P, h⟩ := shape_of_isKey hs
    rcases h.log x hx with rfl | rfl | hx'
    · exact absurd hpk (not_ownedBy_seed _ _)
    · exact absurd hpk (not_ownedBy_param _ _)
    · show OwnedBy z.1.1.parameter x
      rw [h.param]
      exact hx'

/-! ## The clash of a fresh key -/

/-- The fresh key's draws: its seed `S_0`, the first query's answer `S`, the second's. -/
noncomputable def draws : ProbComp (MasterSeed × BitVec 256 × BitVec 256) := do
  let s ← sampleMasterSeed
  let u₁ ← $ᵗ BitVec 256
  let u₂ ← $ᵗ BitVec 256
  return (s, u₁, u₂)

/-- The cache after the fresh key's two derivations. -/
def cacheAfter (t : MasterSeed × BitVec 256 × BitVec 256) : SchemeHashSpec.QueryCache :=
  ((∅ : SchemeHashSpec.QueryCache).cacheQuery (seedHashInput t.1) t.2.1).cacheQuery
    (paramInput t.2.1) t.2.2

theorem romRun_liftM_prob {α : Type} (oa : ProbComp α) (c : SchemeHashSpec.QueryCache) :
    Common.SufCma.romRun (liftM oa : OracleComp World α) c = (·, c) <$> oa :=
  simulateQ_romImpl_liftM_run oa c

/-- A query to a cache without it is a uniform answer, cached. -/
theorem romRun_query_bind_of_none {α : Type} (x : HashInput)
    (k : BitVec 256 → OracleComp SchemeHashSpec α) {c : SchemeHashSpec.QueryCache}
    (hc : c x = none) :
    romRun (liftM ((liftM (SchemeHashSpec.query x) : OracleComp SchemeHashSpec _) >>= k) :
      OracleComp World α) c =
      ($ᵗ BitVec 256 : ProbComp _) >>= fun u ↦ romRun (liftM (k u)) (c.cacheQuery x u) := by
  rw [liftM_query_bind, romRun_bind]
  simp only [Common.SufCma.romRun, simulateQ_spec_query, romImpl_inr_run, roStep_of_none hc,
    bind_assoc, pure_bind]

/-- **A fresh key in the random-oracle model**: its draws, then the rest of key generation from
the cache of its two derivations. -/
theorem romRun_freshRec :
    romRun (freshRec schemeWithHashFromSeed) ∅ = draws >>= fun t ↦
      (fun p ↦ ((p.1.1, seedHashInput t.1 :: paramInput t.2.1 :: p.1.2), p.2)) <$>
        romRun (liftM (restLog t.1 t.2.1 t.2.2)) (cacheAfter t) := by
  rw [freshRec, romRun_bind, romRun_liftM_prob, bind_map_left]
  simp only [draws, bind_assoc, pure_bind]
  refine bind_congr fun s ↦ ?_
  rw [loggedKeygen_eq, romRun_query_bind_of_none _ _ rfl]
  refine bind_congr fun u₁ ↦ ?_
  rw [liftM_map, romRun_map, romRun_query_bind_of_none _ _ (by
    rw [QueryCache.cacheQuery_of_ne _ _ (paramInput_ne_seed _ _)]; rfl), map_bind]
  refine bind_congr fun u₂ ↦ ?_
  rw [liftM_map, romRun_map, Functor.map_map]
  rfl

theorem card_bitVec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  simp

theorem draws_fst (sb : MasterSeed) :
    Pr{let t ← draws}[t.1 = sb] ≤ ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold draws
  refine (prEvent_bind_le_of_imp _ _ (· = sb)
    (fun t : MasterSeed × BitVec 256 × BitVec 256 ↦ t.1 = sb) fun s _ t ht h ↦ ?_).trans ?_
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ht
    obtain ⟨_, -, _, -, rfl⟩ := ht
    exact h
  · simp only [sampleMasterSeed]
    rw [@SampleableType.prEvent_uniformSample_eq_singleton MasterSeed
      (SampleableType.ofFintype MasterSeed) _ sb, card_bitVec]

theorem draws_snd (Sb : BitVec 256) :
    Pr{let t ← draws}[t.2.1 = Sb] ≤ ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold draws
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun s _ ↦ ?_
  refine (prEvent_bind_le_of_imp _ _ (· = Sb)
    (fun t : MasterSeed × BitVec 256 × BitVec 256 ↦ t.2.1 = Sb) fun u₁ _ t ht h ↦
    ?_).trans ?_
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ht
    obtain ⟨_, -, rfl⟩ := ht
    exact h
  · rw [SampleableType.prEvent_uniformSample_eq_singleton, card_bitVec]

theorem draws_trd (Pb : PublicParameter) :
    Pr{let t ← draws}[truncateHash t.2.2 = Pb] ≤ ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold draws
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun s _ ↦ ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun u₁ _ ↦ ?_
  refine (prEvent_bind_le_of_imp _ _ (fun u ↦ truncateHash u = Pb)
    (fun t : MasterSeed × BitVec 256 × BitVec 256 ↦ truncateHash t.2.2 = Pb)
    fun u₂ _ t ht h ↦ ?_).trans ?_
  · simp only [support_pure, Set.mem_singleton_iff] at ht
    subst ht
    exact h
  · change Pr{let u ← ($ᵗ XmssSecurity.HashOutput : ProbComp _)}[
      XmssSecurity.truncateHash u = (Pb : XmssSecurity.Digest)] ≤ _
    rw [← prEvent_map ($ᵗ XmssSecurity.HashOutput) XmssSecurity.truncateHash
        (· = (Pb : XmssSecurity.Digest)),
      XmssSecurity.Rom.evalDist_truncate_uniformHashOutput.prEvent_eq]
    exact (SampleableType.prEvent_uniformSample_eq_singleton (α := XmssSecurity.Digest)
      Pb).trans_le (le_of_eq (by rw [card_bitVec, XmssSecurity.digestBits]))

theorem inv_two_pow_add_self {m n : ℕ} (h : m = n + 1) :
    ((2 ^ m : ℕ) : ℝ≥0∞)⁻¹ + ((2 ^ m : ℕ) : ℝ≥0∞)⁻¹ = ((2 ^ n : ℕ) : ℝ≥0∞)⁻¹ := by
  subst h
  simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

/-- **A fresh key clashes with a fixed one with probability at most `2^-128 + 2^-255`.** -/
theorem clash_le (zb : KeyRec HashSig.PublicKey LeanXmss.SecretKey)
    (hzb : IsKey schemeWithHashFromSeed zb) :
    Pr{let z ← romRun (freshRec schemeWithHashFromSeed) ∅}[Clash ownedPub z.1 zb] ≤
      ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ + ((2 ^ 255 : ℕ) : ℝ≥0∞)⁻¹ := by
  obtain ⟨sb, hsb⟩ := hzb
  obtain ⟨Sb, Pb, hb⟩ := shape_of_isKey hsb
  rw [romRun_freshRec]
  refine (prEvent_bind_le_of_imp draws _
    (fun t ↦ t.1 = sb ∨ t.2.1 = Sb ∨ truncateHash t.2.2 = Pb)
    (fun z : KeyRec HashSig.PublicKey LeanXmss.SecretKey × SchemeHashSpec.QueryCache ↦
      Clash ownedPub z.1 zb)
    fun t _ z hz hc ↦ ?_).trans ?_
  · rw [support_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact (shape_of_rest ((mem_support_liftM_world _ _).mp
      (KeptKey.fst_mem_support_romRun' hp))).clash hb hc
  · calc _ ≤ Pr{let t ← draws}[t.1 = sb] +
          (Pr{let t ← draws}[t.2.1 = Sb] + Pr{let t ← draws}[truncateHash t.2.2 = Pb]) :=
          (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_or_le _ _ _))
      _ ≤ ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ + (((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ + ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹) :=
          add_le_add (draws_fst sb) (add_le_add (draws_snd Sb) (draws_trd Pb))
      _ = _ := by
          rw [← add_assoc, inv_two_pow_add_self (m := 256) (n := 255) rfl, add_comm]

theorem clash_bound_le :
    ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ + ((2 ^ 255 : ℕ) : ℝ≥0∞)⁻¹ ≤ ((2 ^ 127 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [← inv_two_pow_add_self (m := 128) (n := 127) rfl]
  exact add_le_add le_rfl (ENNReal.inv_le_inv.2
    (Nat.cast_le.2 (Nat.pow_le_pow_right (by norm_num) (by norm_num))))

end LeanXmss.MultiKey

namespace XmssSecurity

/-- **leanXMSS with many keys, in the random-permutation model**: for up to `2^32` keys, an
adversary that itself makes at most `q` calls of `π` and `π⁻¹` and at most `lifetime` signing
requests to each key forges under some key with probability at most
`k · (q + 2^10 + k) · 2^-127`. -/
theorem leanXmss_multiKey :
    Common.SufCma.MultiKeyStronglyUnforgeable LeanXmss.RandomPermutationModel.sufCmaScheme
      (2 ^ 32) LeanXmss.lifetime LeanXmss.RandomPermutationModel.securitySlack 127 := by
  rw [LeanXmss.RandomPermutationModel.scheme_eq]
  exact Common.SufCma.MultiKey.multiKeyStronglyUnforgeable_of_romBoundAdv
    LeanXmss.RandomPermutationModel.schemeWithHashFromSeed LeanXmss.MultiKey.ownedPub
    (by norm_num) romBoundAdvFromSeed LeanXmss.MultiKey.separation LeanXmss.MultiKey.clash_le
    LeanXmss.MultiKey.clash_bound_le
    (fun seed ↦ LeanXmss.RandomPermutationModel.scheme_eq ▸
      Common.XmssCost.sufCmaScheme_generateKeys_cost seed)
    (fun sk r ↦ LeanXmss.RandomPermutationModel.scheme_eq ▸
      Common.XmssCost.sufCmaScheme_sign_cost sk r)
    (fun pk f ↦ LeanXmss.RandomPermutationModel.scheme_eq ▸
      Common.XmssCost.sufCmaScheme_verify_cost pk f)
    Common.XmssCost.total_le

end XmssSecurity
