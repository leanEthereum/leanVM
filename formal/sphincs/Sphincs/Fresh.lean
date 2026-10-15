import Sphincs.Encoding
import Sphincs.World
import Sphincs.Bytes

/-!
Compositional preservation of fresh random-oracle inputs. These lemmas quantify over the actual
support of oracle runs, so their conclusions apply after random key generation and adaptive binds.
-/

open OracleComp OracleSpec

namespace Sphincs.Completeness

open Concrete

/-- A computation preserves absence of one cache entry, from every initial cache. -/
def PreservesFresh {α : Type} (target : HashInput) (oa : OracleComp HashSpec α) : Prop :=
  ∀ (cache : QueryCache HashSpec) (r : α × QueryCache HashSpec),
    r ∈ support ((simulateQ randomOracle oa).run cache) →
    cache target = none → r.2 target = none

namespace PreservesFresh

theorem pure' {α : Type} (target : HashInput) (x : α) : PreservesFresh target (pure x) := by
  intro cache r hr hfresh
  simpa using (show r = (x, cache) by simpa using hr) ▸ hfresh

theorem bind {α β : Type} {target : HashInput} {oa : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β} (hleft : PreservesFresh target oa)
    (hright : ∀ a, PreservesFresh target (next a)) : PreservesFresh target (oa >>= next) := by
  intro cache r hr hfresh
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mid, hmid, hr⟩ := hr
  exact hright mid.1 mid.2 r hr (hleft cache mid hmid hfresh)

theorem query {target input : HashInput} (hne : input ≠ target) :
    PreservesFresh target (oracleHash input : OracleComp HashSpec HashOutput) := by
  intro cache r hr hfresh
  simp only [oracleHash, HasQuery.query, simulateQ_spec_query] at hr
  change r ∈ support ((randomOracle (spec := HashSpec) input).run cache) at hr
  cases hc : cache input with
  | some answer =>
      rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hr
      subst r
      exact hfresh
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      exact (QueryCache.cacheQuery_of_ne cache answer (Ne.symm hne)).trans hfresh

theorem tweakableHash (target : HashInput) (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (hne : tweakableHashInput parameter domain payload ≠ target) :
    PreservesFresh target (Concrete.tweakableHash parameter domain payload) := by
  exact bind (query hne) (fun _ => pure' _ _)

theorem deriveKey (target : HashInput) (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) (hne : keygenHashInput parameter domain seed ≠ target) :
    PreservesFresh target (Sphincs.deriveKey parameter domain seed) :=
  bind (query hne) (fun _ => pure' _ _)

theorem deriveOutput (target : HashInput) (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) (hne : keygenHashInput parameter domain seed ≠ target) :
    PreservesFresh target (Sphincs.deriveOutput parameter domain seed) :=
  query hne

theorem sequenceFin {α : Type} {n : Nat} (target : HashInput)
    (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ i, PreservesFresh target (computation i)) :
    PreservesFresh target (Concrete.sequenceFin computation) := by
  induction n with
  | zero => exact pure' _ _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      exact bind (h 0) (fun _ => bind (ih _ (fun i => h i.succ)) (fun _ => pure' _ _))

theorem messageDigest {target : HashInput} (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness)
    (hs : tweakableHashInput parameter .message
        (messageDigestPayload root message randomness) ≠ target) :
    PreservesFresh target (Concrete.messageDigest parameter root message randomness) := by
  rw [Concrete.messageDigest]
  exact bind (query hs) (fun _ => pure' _ _)

end PreservesFresh

/-- Domain separation is independent of the public parameter and payload: the type byte is at
offset 23 of every input. -/
theorem fieldInput_ne_of_tag_ne_across (parameter parameter' : PublicParameter)
    {fields1 fields2 : TweakFields} (htag : fields1.tag ≠ fields2.tag)
    (payload1 payload2 : HashInput) :
    bytesLE 16 parameter ++ fieldBytes fields1 ++ payload1 ≠
      bytesLE 16 parameter' ++ fieldBytes fields2 ++ payload2 := by
  intro h
  apply htag
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length])
  obtain ⟨_, hfields⟩ := List.append_inj hprefix (by simp [bytesLE_length])
  rw [Sphincs.fieldBytes_injective hfields]

/-- Every derivation domain is separate from both encoding (4) and message (12). -/
theorem keygenDomain_tag_ne (domain : KeygenDomain) (tag : Nat) (htag : tag = 4 ∨ tag = 12) :
    (keygenDomainFields domain).tag ≠ BitVec.ofNat 5 tag := by
  rcases htag with rfl | rfl <;> cases domain <;> simp [keygenDomainFields, tweakFields]

/-- Exclusion facts needed by structural tree computations. Surrogate derivations are included. -/
structure StructuralFresh (target : HashInput) : Prop where
  derive : ∀ parameter domain seed, keygenHashInput parameter domain seed ≠ target
  chain : ∀ parameter lay tree leaf chain step payload,
    tweakableHashInput parameter (.chain lay tree leaf chain step) payload ≠ target
  leaf : ∀ parameter lay tree leaf payload,
    tweakableHashInput parameter (.leaf lay tree leaf) payload ≠ target
  node : ∀ parameter lay tree level index payload,
    tweakableHashInput parameter (.node lay tree level index) payload ≠ target
  fchain : ∀ parameter index c s j a i t payload,
    tweakableHashInput parameter (.fchain index c s j a i t) payload ≠ target
  childLeaf : ∀ parameter index c s j a payload,
    tweakableHashInput parameter (.childLeaf index c s j a) payload ≠ target
  subNode : ∀ parameter index c s j level node payload,
    tweakableHashInput parameter (.subNode index c s j level node) payload ≠ target
  superChild : ∀ parameter index c s payload,
    tweakableHashInput parameter (.superChild index c s) payload ≠ target
  topNode : ∀ parameter index c level node payload,
    tweakableHashInput parameter (.topNode index c level node) payload ≠ target
  roots : ∀ parameter index payload,
    tweakableHashInput parameter (.roots index) payload ≠ target

/-- Structural computations cannot query either a message input or an encoding input. -/
theorem structuralFresh_of_tag (parameter : PublicParameter) (fields : TweakFields)
    (payload : HashInput) (tag : Nat) (htag : tag = 4 ∨ tag = 12)
    (hfields : fields.tag = BitVec.ofNat 5 tag) :
    StructuralFresh (bytesLE 16 parameter ++ fieldBytes fields ++ payload) := by
  constructor
  · intro p domain seed
    exact fieldInput_ne_of_tag_ne_across p parameter
      (by rw [hfields]; exact keygenDomain_tag_ne domain tag htag) _ _
  all_goals
    intros
    apply fieldInput_ne_of_tag_ne_across
    rw [hfields]
    rcases htag with rfl | rfl <;> simp [hashDomainFields, tweakFields]

/-- Every counter-search input is separate from all structural tree inputs. -/
theorem structuralFresh_encoding (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (c : Nat) :
    StructuralFresh (encodeInput parameter lay tree leaf message c) :=
  structuralFresh_of_tag parameter (hashDomainFields (.encoding lay tree leaf))
    _ 4 (Or.inl rfl) rfl

/-- Message hashing cannot populate any encoding-search cache entry, even for another key. -/
theorem messageInput_ne_encoding (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness)
    (encodingParameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (encodingMessage : Digest) (c : Nat) :
    tweakableHashInput parameter .message
      (messageDigestPayload root message randomness) ≠
        encodeInput encodingParameter lay tree leaf encodingMessage c := by
  apply fieldInput_ne_of_tag_ne_across
  simp [hashDomainFields, tweakFields]

/-- Message inputs are separate from structural key generation for all public parameters. -/
theorem structuralFresh_message (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) :
    StructuralFresh (tweakableHashInput parameter .message
      (messageDigestPayload root message randomness)) :=
  structuralFresh_of_tag parameter (hashDomainFields .message) _ 12 (Or.inr rfl) rfl

namespace PreservesFresh

variable {target : HashInput} (hs : StructuralFresh target)
include hs

theorem chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chain : ChainIndex) (start steps : Nat) (value : Digest) :
    PreservesFresh target (Concrete.chainWalk parameter lay tree leaf chain start steps value) := by
  induction steps with
  | zero => exact pure' _ _
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine bind ih (fun _ => ?_)
      split
      · exact tweakableHash _ _ _ _ (hs.chain _ _ _ _ _ _ _)
      · exact pure' _ _

theorem otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    PreservesFresh target (Seeded.otsSecrets parameter lay tree leaf seed) := by
  rw [Seeded.otsSecrets]
  exact bind (sequenceFin _ _ (fun _ => deriveOutput _ _ _ _ (hs.derive _ _ _))) (fun _ => pure' _ _)

theorem oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    PreservesFresh target (Seeded.oneTimePublicKey parameter lay tree leaf seed) := by
  rw [Seeded.oneTimePublicKey]
  exact bind (otsSecrets hs _ _ _ _ _) (fun _ => sequenceFin _ _ (fun _ => chainWalk hs _ _ _ _ _ _ _ _))

theorem treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (level index : Nat) :
    PreservesFresh target (Seeded.treeNode parameter lay tree seed level index) := by
  induction level generalizing index with
  | zero =>
      rw [Seeded.treeNode]
      exact bind (oneTimePublicKey hs _ _ _ _ _) (fun _ => tweakableHash _ _ _ _ (hs.leaf _ _ _ _ _))
  | succ level ih =>
      rw [Seeded.treeNode]
      exact bind (ih _) (fun _ => bind (ih _) (fun _ => tweakableHash _ _ _ _ (hs.node _ _ _ _ _ _)))

theorem surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) :
    PreservesFresh target (Seeded.surrogate parameter seed level) := by
  rw [Seeded.surrogate]
  split
  · exact deriveKey _ _ _ _ (hs.derive _ _ _)
  · exact pure' _ _

variable [Params]

theorem spineNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (steps : Nat) :
    PreservesFresh target (Seeded.spineNode parameter lay tree seed steps) := by
  induction steps with
  | zero => exact treeNode hs _ _ _ _ _ _
  | succ steps ih =>
      rw [Seeded.spineNode]
      refine bind ih (fun _ => bind (surrogate hs _ _ _) (fun _ => ?_))
      dsimp only
      split <;> exact tweakableHash _ _ _ _ (hs.node _ _ _ _ _ _)

theorem keygenFromSeed (seed : MasterSeed) :
    PreservesFresh target (Seeded.keygenFromSeed seed) := by
  rw [Seeded.keygenFromSeed]
  exact bind (deriveKey _ _ _ _ (hs.derive _ _ _)) (fun _ =>
    bind (spineNode hs _ _ _ _ _) (fun _ => pure' _ _))

omit [Params] in
theorem forestWalk (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (start steps : Nat) (value : Digest) :
    PreservesFresh target (Concrete.forestWalk parameter index c s j a i start steps value) := by
  induction steps with
  | zero => exact pure' _ _
  | succ steps ih =>
      rw [Concrete.forestWalk]
      refine bind ih (fun _ => ?_)
      split
      · exact tweakableHash _ _ _ _ (hs.fchain _ _ _ _ _ _ _ _ _)
      · exact pure' _ _

omit [Params] in
theorem chainValue (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (seed : MasterSeed) (pos : Nat) :
    PreservesFresh target (Seeded.chainValue parameter index c s j a i seed pos) := by
  rw [Seeded.chainValue, Seeded.forestStart]
  exact bind (bind (deriveOutput _ _ _ _ (hs.derive _ _ _)) (fun _ => pure' _ _))
    (fun _ => forestWalk hs _ _ _ _ _ _ _ _ _ _)

omit [Params] in
theorem forestSecrets (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (seed : MasterSeed) :
    PreservesFresh target (Seeded.forestSecrets parameter index c s j a seed) := by
  rw [Seeded.forestSecrets]
  exact bind (sequenceFin _ _ (fun _ => deriveOutput _ _ _ _ (hs.derive _ _ _))) (fun _ => pure' _ _)

omit [Params] in
theorem childLeaf (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (seed : MasterSeed) :
    PreservesFresh target (Seeded.childLeaf parameter index c s j a seed) := by
  rw [Seeded.childLeaf]
  exact bind (forestSecrets hs _ _ _ _ _ _ _) (fun _ =>
    bind (sequenceFin _ _ (fun _ => forestWalk hs _ _ _ _ _ _ _ _ _ _))
      (fun _ => tweakableHash _ _ _ _ (hs.childLeaf _ _ _ _ _ _ _)))

omit [Params] in
theorem subNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (seed : MasterSeed) (level node : Nat) :
    PreservesFresh target (Seeded.subNode parameter index c s j seed level node) := by
  induction level generalizing node with
  | zero =>
      rw [Seeded.subNode]
      exact childLeaf hs _ _ _ _ _ _ _
  | succ level ih =>
      rw [Seeded.subNode]
      refine bind (ih _) (fun _ => bind (ih _) (fun _ => ?_))
      split
      · exact tweakableHash _ _ _ _ (hs.subNode _ _ _ _ _ _ _ _)
      · exact pure' _ _

omit [Params] in
theorem superNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (seed : MasterSeed) :
    PreservesFresh target (Seeded.superNode parameter index c s seed) := by
  rw [Seeded.superNode]
  exact bind (sequenceFin _ _ (fun _ => bind (subNode hs _ _ _ _ _ _ _ _) (fun _ =>
      bind (subNode hs _ _ _ _ _ _ _ _) (fun _ => pure' _ _))))
    (fun _ => tweakableHash _ _ _ _ (hs.superChild _ _ _ _ _))

omit [Params] in
theorem topNode (parameter : PublicParameter) (index : Index) (c : Coord)
    (seed : MasterSeed) (level node : Nat) :
    PreservesFresh target (Seeded.topNode parameter index c seed level node) := by
  induction level generalizing node with
  | zero =>
      rw [Seeded.topNode]
      exact superNode hs _ _ _ _ _
  | succ level ih =>
      rw [Seeded.topNode]
      refine bind (ih _) (fun _ => bind (ih _) (fun _ => ?_))
      split
      · exact tweakableHash _ _ _ _ (hs.topNode _ _ _ _ _ _)
      · exact pure' _ _

omit [Params] in
theorem forestKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) :
    PreservesFresh target (Seeded.forestKey parameter index seed) := by
  rw [Seeded.forestKey]
  exact bind (sequenceFin _ _ (fun _ => bind (topNode hs _ _ _ _ _ _) (fun _ =>
      bind (topNode hs _ _ _ _ _ _) (fun _ => pure' _ _))))
    (fun _ => tweakableHash _ _ _ _ (hs.roots _ _ _))

omit [Params] in
theorem coordOpen (parameter : PublicParameter) (index : Index) (c : Coord) (mark : CoordMark)
    (seed : MasterSeed) :
    PreservesFresh target (Seeded.coordOpen parameter index c mark seed) := by
  rw [Seeded.coordOpen]
  refine bind (sequenceFin _ _ (fun _ => ?_)) (fun _ =>
    bind (sequenceFin _ _ (fun _ => topNode hs _ _ _ _ _ _)) (fun _ => pure' _ _))
  exact bind (forestSecrets hs _ _ _ _ _ _ _) (fun _ =>
    bind (sequenceFin _ _ (fun _ => forestWalk hs _ _ _ _ _ _ _ _ _ _)) (fun _ =>
      bind (sequenceFin _ _ (fun _ => subNode hs _ _ _ _ _ _ _ _)) (fun _ => pure' _ _)))

omit [Params] in
theorem forestOpen (parameter : PublicParameter) (index : Index)
    (marks : Coord → CoordMark) (seed : MasterSeed) :
    PreservesFresh target (Seeded.forestOpen parameter index marks seed) := by
  rw [Seeded.forestOpen]
  exact sequenceFin _ _ (fun _ => coordOpen hs _ _ _ _ _)

end PreservesFresh

end Sphincs.Completeness
