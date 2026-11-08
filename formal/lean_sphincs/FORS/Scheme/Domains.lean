import FORS.Scheme.Bytes
import FORS.Scheme.Encoding
import FORS.Scheme.RandomOracle

/-! Injectivity and separation of the candidate's exact byte inputs. These facts keep the
derivation and verification addresses distinct in later random-oracle reductions. -/

namespace FORS.Security

variable [Params]

/-- The fixed-width prefix `PK.seed || ADRS` determines its fields and parameter, with no restriction
on payload. -/
theorem fieldInput_injective {fields fields' : TweakFields}
    {parameter parameter' : PublicParameter} {payload payload' : HashInput}
    (h : bytesLE 16 parameter ++ fieldBytes fields ++ payload =
      bytesLE 16 parameter' ++ fieldBytes fields' ++ payload') :
    fields = fields' ∧ parameter = parameter' ∧ payload = payload' := by
  obtain ⟨hprefix, hpayload⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length, bytesBE_length])
  obtain ⟨hparameter, hfields⟩ := List.append_inj hprefix (by simp [bytesLE_length])
  exact ⟨fieldBytes_injective hfields, bytesLE_injective hparameter, hpayload⟩

end FORS.Security

namespace FORS.Completeness

variable [Params]

/-- Domain separation is independent of the public parameter and payload: the type word is at
bytes 32 to 35 of every addressed input. -/
theorem fieldInput_ne_of_tag_ne_across (parameter parameter' : PublicParameter)
    {fields1 fields2 : TweakFields} (htag : fields1.tag ≠ fields2.tag)
    (payload1 payload2 : HashInput) :
    bytesLE 16 parameter ++ fieldBytes fields1 ++ payload1 ≠
      bytesLE 16 parameter' ++ fieldBytes fields2 ++ payload2 := fun h =>
  htag (congrArg TweakFields.tag (Security.fieldInput_injective h).1)

end FORS.Completeness

namespace FORS.Security

variable [Params]

theorem tweakableInput_injective {parameter parameter' : PublicParameter}
    {domain domain' : HashDomain} {payload payload' : HashInput}
    (h : tweakableHashInput parameter domain payload =
      tweakableHashInput parameter' domain' payload') :
    hashDomainFields domain = hashDomainFields domain' ∧
      parameter = parameter' ∧ payload = payload' :=
  fieldInput_injective h

/-! ### FORS addresses -/

theorem two_pow_forsHeight_le : 2 ^ forsHeight ≤ 2 ^ 12 :=
  Nat.pow_le_pow_right (by decide) Params.forsHeight_le

theorem level_lt_16 (level : FLevel) : level.val + 1 < 16 := by
  have := level.isLt; have := Params.forsHeight_le
  omega

/-- An in-range FORS tree index lies below `2 ^ 18`, under the out-of-range ones. -/
private theorem forsTreeIndex_inRange_lt (κ : FTree) (height : Nat) {node : Nat}
    (h : node < 2 ^ (forsHeight - height)) : κ.val * 2 ^ (forsHeight - height) + node < 2 ^ 18 := by
  have hP : 2 ^ (forsHeight - height) ≤ 2 ^ 12 :=
    Nat.pow_le_pow_right (by decide) ((Nat.sub_le _ _).trans Params.forsHeight_le)
  have := κ.isLt; have := Params.forsTrees_le
  calc κ.val * 2 ^ (forsHeight - height) + node < κ.val * 2 ^ (forsHeight - height) + 2 ^ (forsHeight - height) :=
        by omega
    _ = (κ.val + 1) * 2 ^ (forsHeight - height) := by ring
    _ ≤ 64 * 2 ^ 12 := Nat.mul_le_mul (by omega) hP
    _ = 2 ^ 18 := by norm_num

/-- A FORS tree index fits its 32-bit word. -/
theorem forsTreeIndex_lt (κ : FTree) (height : Nat) {node : Nat} (h : node < 2 ^ forsHeight) :
    forsTreeIndex κ height node < 2 ^ 32 := by
  have := κ.isLt; have := Params.forsTrees_le
  have h12 : 2 ^ forsHeight ≤ 4096 := two_pow_forsHeight_le
  unfold forsTreeIndex
  split
  · exact (forsTreeIndex_inRange_lt κ height (by assumption)).trans (by decide)
  · omega

/-- At one height, a FORS tree index determines the tree and the node. -/
theorem forsTreeIndex_injective {κ κ' : FTree} {height node node' : Nat} (hn : node < 2 ^ forsHeight)
    (hn' : node' < 2 ^ forsHeight) (h : forsTreeIndex κ height node = forsTreeIndex κ' height node') :
    κ = κ' ∧ node = node' := by
  have := κ.isLt; have := κ'.isLt; have := Params.forsTrees_le
  have h12 : 2 ^ forsHeight ≤ 4096 := two_pow_forsHeight_le
  have hpos : 0 < 2 ^ (forsHeight - height) := Nat.two_pow_pos _
  unfold forsTreeIndex at h
  split at h <;> split at h
  · rename_i hl hr
    have hdiv : ∀ (a : FTree) (b : Nat), b < 2 ^ (forsHeight - height) →
        (a.val * 2 ^ (forsHeight - height) + b) / 2 ^ (forsHeight - height) = a.val := by
      intro a b hb
      rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hb, Nat.add_zero]
    have hκ : κ = κ' := Fin.ext (by rw [← hdiv κ node hl, ← hdiv κ' node' hr, h])
    subst hκ
    exact ⟨rfl, by omega⟩
  · rename_i hl _
    have := forsTreeIndex_inRange_lt κ height hl
    omega
  · rename_i _ hr
    have := forsTreeIndex_inRange_lt κ' height hr
    omega
  · exact ⟨Fin.ext (by omega), by omega⟩

/-- The tree and key-pair words of a FORS address determine the instance. -/
theorem forsAddress_index_injective {index index' : Index}
    (htree : BitVec.ofNat 96 (index.val / 2 ^ bottomHeight) = BitVec.ofNat 96 (index'.val / 2 ^ bottomHeight))
    (hkey : BitVec.ofNat 32 (index.val % 2 ^ bottomHeight) = BitVec.ofNat 32 (index'.val % 2 ^ bottomHeight)) :
    index = index' := by
  have hi := index_lt_two_pow_32 index; have hi' := index_lt_two_pow_32 index'
  have h96 : (2 : Nat) ^ 32 ≤ 2 ^ 96 := Nat.pow_le_pow_right (by decide) (by decide)
  have hq := ofNat_inj_of_lt ((Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi).trans_le h96)
    ((Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi').trans_le h96) htree
  have hr := ofNat_inj_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hi)
    (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hi') hkey
  apply Fin.ext
  rw [← Nat.div_add_mod index.val (2 ^ bottomHeight), ← Nat.div_add_mod index'.val (2 ^ bottomHeight), hq, hr]

theorem tree_lt_two_pow_96 (tree : TreeIndex) : tree.val < 2 ^ 96 :=
  (tree_lt_two_pow_32 tree).trans_le (Nat.pow_le_pow_right (by decide) (by decide))

theorem deriveFields_injective : Function.Injective keygenDomainFields := by
  intro left right h
  have htag := congrArg TweakFields.tag h
  cases left <;> cases right
  all_goals try { simp [keygenDomainFields, treeFields, forsFields, tweakFields] at htag; done }
  · rename_i lay tree leaf chain lay' tree' leaf' chain'
    have hl : lay = lay' := layerByte_ofNat_injective (lay := lay) (lay' := lay') (congrArg TweakFields.layer h)
    have ht : tree = tree' := Fin.ext (ofNat_inj_of_lt (w := 96) (tree_lt_two_pow_96 tree) (tree_lt_two_pow_96 tree')
      (congrArg TweakFields.tree h))
    have he : leaf = leaf' := Fin.ext (ofNat_inj_of_lt (w := 32) (leaf_lt_two_pow_32 leaf) (leaf_lt_two_pow_32 leaf')
      (congrArg TweakFields.keyPair h))
    have hc : chain = chain' := Fin.ext (ofNat_inj_of_lt (w := 32) (chain.isLt.trans_le (by decide))
      (chain'.isLt.trans_le (by decide)) (congrArg TweakFields.height h))
    cases hl; cases ht; cases he; cases hc; rfl
  · rename_i index κ leaf index' κ' leaf'
    have hidx : index = index' :=
      forsAddress_index_injective (congrArg TweakFields.tree h) (congrArg TweakFields.keyPair h)
    have hp := ofNat_inj_of_lt (w := 32) (forsTreeIndex_lt κ 0 leaf.isLt) (forsTreeIndex_lt κ' 0 leaf'.isLt)
      (congrArg TweakFields.index h)
    obtain ⟨hκ, hleaf⟩ := forsTreeIndex_injective leaf.isLt leaf'.isLt hp
    subst hidx hκ
    cases Fin.ext hleaf; rfl
  · rename_i level level'
    have hl : level = level' := by
      apply Fin.ext
      have := totalHeight_le_28; have := maxLayerHeight_le
      exact ofNat_inj_of_lt (w := 32) (level.isLt.trans_le (by omega))
        (level'.isLt.trans_le (by omega)) (congrArg TweakFields.height h)
    cases hl; rfl

/-- No two seed-derivation queries have the same input unless their full arguments agree. -/
theorem keygenInput_injective {parameter parameter' : PublicParameter}
    {domain domain' : KeygenDomain} {seed seed' : MasterSeed}
    (h : keygenHashInput parameter domain seed = keygenHashInput parameter' domain' seed') :
    parameter = parameter' ∧ domain = domain' ∧ seed = seed' := by
  obtain ⟨hfields, hp, hs⟩ := fieldInput_injective h
  exact ⟨hp, deriveFields_injective hfields, bytesLE_injective hs⟩

/-- Every verification-domain tag is distinct from every seed-derivation tag. -/
theorem derive_tag_ne_hash_tag (derive : KeygenDomain) (hash : HashDomain) :
    (keygenDomainFields derive).tag ≠ (hashDomainFields hash).tag := by
  cases derive <;> cases hash <;>
    simp [keygenDomainFields, hashDomainFields, tweakFields, treeFields, forsFields]

/-- Seed derivation cannot be confused with any verifier hash input, even across parameters. -/
theorem keygenInput_ne_hashInput (parameter parameter' : PublicParameter)
    (derive : KeygenDomain) (hash : HashDomain) (seed : MasterSeed) (payload : HashInput) :
    keygenHashInput parameter derive seed ≠ tweakableHashInput parameter' hash payload :=
  Completeness.fieldInput_ne_of_tag_ne_across parameter parameter'
    (derive_tag_ne_hash_tag derive hash) _ _

/-! ### Separation by length

The unaddressed inputs (`keySeedInput`, `randomizerHashInput`, `messageDigestInput`) have no address,
so they are told apart from each other and from the addressed ones by their lengths: 44, 93 and 84
bytes, against `48 + payload` for a tweakable hash and 80 for a seed derivation. -/

theorem keySeedInput_length (seed : MasterSeed) (domain : Nat) : (keySeedInput seed domain).length = 44 := by
  simp [keySeedInput, seedTag, bytesLE_length]

theorem framedMessage_length (message : Message) : (framedMessage message).length = 45 := by
  simp [framedMessage, seedTag, bytesLE_length]

theorem randomizerHashInput_length (prf : HashOutput) (parameter : PublicParameter) (message : Message) :
    (randomizerHashInput prf parameter message).length = 93 := by
  simp only [randomizerHashInput, List.length_append, bytesLE_length, framedMessage_length]

theorem messageDigestInput_length (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) :
    (messageDigestInput parameter root message randomness call).length = 84 := by
  simp only [messageDigestInput, List.length_append, bytesLE_length, bytesBE_length]

theorem keySeedInput_ne_tweakableHashInput (seed : MasterSeed) (index : Nat) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) :
    keySeedInput seed index ≠ tweakableHashInput parameter domain payload := fun h => by
  have := congrArg List.length h
  rw [keySeedInput_length, tweakableHashInput_length] at this
  omega

theorem randomizerHashInput_ne_tweakableHashInput (prf : HashOutput) (parameter parameter' : PublicParameter)
    (message : Message) (domain : HashDomain) {payload : HashInput} (hpayload : payload.length ≠ 45) :
    randomizerHashInput prf parameter message ≠ tweakableHashInput parameter' domain payload := fun h => by
  have := congrArg List.length h
  rw [randomizerHashInput_length, tweakableHashInput_length] at this
  omega

theorem messageDigestInput_ne_tweakableHashInput (parameter parameter' : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) (call : DigestCall) (domain : HashDomain)
    {payload : HashInput} (hpayload : payload.length ≠ 36) :
    messageDigestInput parameter root message randomness call ≠ tweakableHashInput parameter' domain payload :=
  fun h => by
    have := congrArg List.length h
    rw [messageDigestInput_length, tweakableHashInput_length] at this
    omega

theorem keySeedInput_ne_keygenHashInput (seed seed' : MasterSeed) (index : Nat) (parameter : PublicParameter)
    (domain : KeygenDomain) : keySeedInput seed index ≠ keygenHashInput parameter domain seed' := fun h => by
  have := congrArg List.length h
  rw [keySeedInput_length, keygenHashInput_length] at this
  omega

theorem randomizerHashInput_ne_keygenHashInput (prf : HashOutput) (parameter parameter' : PublicParameter)
    (message : Message) (domain : KeygenDomain) (seed : MasterSeed) :
    randomizerHashInput prf parameter message ≠ keygenHashInput parameter' domain seed := fun h => by
  have := congrArg List.length h
  rw [randomizerHashInput_length, keygenHashInput_length] at this
  omega

theorem keySeedInput_ne_randomizerHashInput (seed : MasterSeed) (index : Nat) (prf : HashOutput)
    (parameter : PublicParameter) (message : Message) :
    keySeedInput seed index ≠ randomizerHashInput prf parameter message := fun h => by
  have := congrArg List.length h
  rw [keySeedInput_length, randomizerHashInput_length] at this
  omega

/-! ### Injectivity of the unaddressed inputs -/

/-- The key-seed input determines the seed and, below 256, the domain byte. -/
theorem keySeedInput_injective {seed seed' : MasterSeed} {domain domain' : Nat} (hd : domain < 256)
    (hd' : domain' < 256) (h : keySeedInput seed domain = keySeedInput seed' domain') :
    seed = seed' ∧ domain = domain' := by
  unfold keySeedInput at h
  obtain ⟨hprefix, hbyte⟩ := List.append_inj' h rfl
  have hseed := List.append_cancel_left hprefix
  refine ⟨bytesLE_injective hseed, ?_⟩
  have := congrArg UInt8.toNat (List.singleton_inj.mp hbyte)
  simp only [UInt8.toNat_ofNat'] at this
  omega

theorem framedMessage_injective {message message' : Message}
    (h : framedMessage message = framedMessage message') : message = message' :=
  bytesLE_injective (List.append_cancel_left h)

/-- The randomizer input determines `SK.prf`, `PK.seed` and the message. -/
theorem randomizerHashInput_injective {prf prf' : HashOutput} {parameter parameter' : PublicParameter}
    {message message' : Message}
    (h : randomizerHashInput prf parameter message = randomizerHashInput prf' parameter' message') :
    prf = prf' ∧ parameter = parameter' ∧ message = message' := by
  unfold randomizerHashInput at h
  obtain ⟨hprefix, hmessage⟩ := List.append_inj' h (by rw [framedMessage_length, framedMessage_length])
  obtain ⟨hprf, hparameter⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hprf, bytesLE_injective hparameter, framedMessage_injective hmessage⟩

theorem digestCall_lt (call : DigestCall) : call.val < 2 ^ 32 := by
  have := call.isLt
  have hk : forsTrees * forsHeight ≤ 64 * 12 := Nat.mul_le_mul Params.forsTrees_le Params.forsHeight_le
  have := bottomHeight_le; have := totalHeight_le_28
  unfold digestCalls digestBytes mdBytes treeIndexBytes leafIndexBytes at *
  omega

/-- A message-digest input determines every argument, the call included. -/
theorem messageDigestInput_injective {parameter parameter' : PublicParameter} {root root' : Digest}
    {message message' : Message} {randomness randomness' : Randomness} {call call' : DigestCall}
    (h : messageDigestInput parameter root message randomness call =
      messageDigestInput parameter' root' message' randomness' call') :
    parameter = parameter' ∧ root = root' ∧ message = message' ∧ randomness = randomness' ∧
      call = call' := by
  unfold messageDigestInput at h
  obtain ⟨h, hcall⟩ := List.append_inj' h (by simp [bytesBE_length])
  obtain ⟨h, hmessage⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hroot⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hrandomness, hparameter⟩ := List.append_inj' h (by simp [bytesLE_length])
  refine ⟨bytesLE_injective hparameter, bytesLE_injective hroot, bytesLE_injective hmessage,
    bytesLE_injective hrandomness, Fin.ext (ofNat_inj_of_lt (digestCall_lt call) (digestCall_lt call') ?_)⟩
  exact bytesBE_injective hcall

end FORS.Security
