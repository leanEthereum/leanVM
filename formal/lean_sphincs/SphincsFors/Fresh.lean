import SphincsFors.Encoding
import SphincsFors.World
import SphincsFors.Bytes

/-!
Compositional preservation of fresh random-oracle inputs. These lemmas quantify over the actual
support of oracle runs, so their conclusions apply after random key generation and adaptive binds.
-/

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

namespace SphincsFors.Completeness

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
    PreservesFresh target (SphincsFors.deriveKey parameter domain seed) :=
  bind (query hne) (fun _ => pure' _ _)

theorem derivePair (target : HashInput) (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) (hne : keygenHashInput parameter domain seed ≠ target) :
    PreservesFresh target (SphincsFors.derivePair parameter domain seed) :=
  bind (query hne) (fun _ => pure' _ _)

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
    (hs : ∀ block : Fin 2,
      tweakableHashInput parameter (.message block)
        (messageDigestPayload root message randomness) ≠ target) :
    PreservesFresh target (Concrete.messageDigest parameter root message randomness) := by
  rw [Concrete.messageDigest]
  exact bind (query (hs 0)) (fun _ => bind (query (hs 1)) (fun _ => pure' _ _))

end PreservesFresh

/-- Domain separation is independent of the public parameter and payload. -/
theorem fieldInput_ne_of_tag_ne_across (parameter parameter' : PublicParameter)
    {fields1 fields2 : TweakFields} (htag : fields1.tag ≠ fields2.tag)
    (payload1 payload2 : HashInput) :
    bytesLE 16 parameter ++ fieldBytes fields1 ++ payload1 ≠
      bytesLE 16 parameter' ++ fieldBytes fields2 ++ payload2 := by
  intro h
  apply htag
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length])
  obtain ⟨_, hfields⟩ := List.append_inj hprefix (by simp [bytesLE_length])
  rw [SphincsFors.fieldBytes_injective hfields]

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
  ftsLeaf : ∀ parameter index tree leaf payload,
    tweakableHashInput parameter (.ftsLeaf index tree leaf) payload ≠ target
  ftsNode : ∀ parameter index tree level node payload,
    tweakableHashInput parameter (.ftsNode index tree level node) payload ≠ target
  ftsRoots : ∀ parameter index payload,
    tweakableHashInput parameter (.ftsRoots index) payload ≠ target

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
    (message : Message) (randomness : Randomness) (block : Fin 2)
    (encodingParameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (encodingMessage : Digest) (c : Nat) :
    tweakableHashInput parameter (.message block)
      (messageDigestPayload root message randomness) ≠
        encodeInput encodingParameter lay tree leaf encodingMessage c := by
  apply fieldInput_ne_of_tag_ne_across
  simp [hashDomainFields, tweakFields]

/-- Message inputs are separate from structural key generation for all public parameters. -/
theorem structuralFresh_message (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) (block : Fin 2) :
    StructuralFresh (tweakableHashInput parameter (.message block)
      (messageDigestPayload root message randomness)) :=
  structuralFresh_of_tag parameter (hashDomainFields (.message block)) _ 12 (Or.inr rfl) rfl

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

theorem otsValues (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (steps : ChainIndex → Nat) :
    PreservesFresh target (Seeded.otsValues parameter lay tree leaf seed steps) := by
  rw [Seeded.otsValues]
  refine bind (sequenceFin _ _ fun pair => ?_) (fun _ => pure' _ _)
  exact bind (derivePair _ _ _ _ (hs.derive _ _ _)) (fun _ =>
    bind (chainWalk hs _ _ _ _ _ _ _ _) (fun _ =>
      bind (chainWalk hs _ _ _ _ _ _ _ _) (fun _ => pure' _ _)))

theorem oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    PreservesFresh target (Seeded.oneTimePublicKey parameter lay tree leaf seed) :=
  otsValues hs _ _ _ _ _ _

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
theorem ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (seed : MasterSeed) (level node : Nat) :
    PreservesFresh target (Seeded.ftsNode parameter index tree seed level node) := by
  induction level generalizing node with
  | zero =>
      rw [Seeded.ftsNode]
      exact bind (deriveKey _ _ _ _ (hs.derive _ _ _))
        (fun _ => tweakableHash _ _ _ _ (hs.ftsLeaf _ _ _ _ _))
  | succ level ih =>
      cases level with
      | zero =>
          rw [Seeded.ftsNode]
          exact bind (derivePair _ _ _ _ (hs.derive _ _ _)) (fun _ =>
            bind (tweakableHash _ _ _ _ (hs.ftsLeaf _ _ _ _ _)) (fun _ =>
              bind (tweakableHash _ _ _ _ (hs.ftsLeaf _ _ _ _ _)) (fun _ =>
                tweakableHash _ _ _ _ (hs.ftsNode _ _ _ _ _ _))))
      | succ level =>
          rw [Seeded.ftsNode]
          exact bind (ih _) (fun _ => bind (ih _) (fun _ => tweakableHash _ _ _ _ (hs.ftsNode _ _ _ _ _ _)))

omit [Params] in
theorem ftsKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) :
    PreservesFresh target (Seeded.ftsKey parameter index seed) := by
  rw [Seeded.ftsKey]
  exact bind (sequenceFin _ _ (fun _ => bind (ftsNode hs _ _ _ _ _ _)
      (fun _ => bind (ftsNode hs _ _ _ _ _ _) (fun _ => pure' _ _))))
    (fun _ => tweakableHash _ _ _ _ (hs.ftsRoots _ _ _))

omit [Params] in
theorem ftsOpen (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (seed : MasterSeed) :
    PreservesFresh target (Seeded.ftsOpen parameter index leaves seed) := by
  rw [Seeded.ftsOpen]
  exact sequenceFin _ _ (fun _ => sequenceFin _ _ (fun _ => ftsNode hs _ _ _ _ _ _))

end PreservesFresh

end SphincsFors.Completeness
