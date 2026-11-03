import FORS.GraphView.Secrets
import FORS.Seed.Coupling

section

/-! Exact hash-call counts (`hashCalls`) of the honest seeded computations on a fixed answer
function: wrappers, chains, one-time keys, tree and FORS nodes, encodings, message digests and
signing attempts. One seed derivation gives the starts of two chains: a one-time key costs
`32 + 64 · 3 = 224` calls, and a FORS pair of leaves `1 + 2 = 3` (its derivation and two hashes). -/

open OracleComp OracleSpec

namespace FORS.Security.Prefix

variable [Params]
open Concrete

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.treeNode
  Seeded.forsNode Seeded.forsKey Seeded.forsOpen Seeded.treePath Seeded.signLayer chainWalk
  deriveKey
set_option backward.isDefEq.respectTransparency false

def hashCalls {α : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) : Nat :=
  (queriedInputs f computation).length

@[simp] theorem hashCalls_pure {α : Type} (f : QueryImpl HashSpec Id) (value : α) :
    hashCalls f (pure value) = 0 := rfl

theorem hashCalls_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    hashCalls f (computation >>= next) = hashCalls f computation +
      hashCalls f (next (evalWithAnswerFn f computation)) := by
  simp only [hashCalls, queriedInputs_bind, List.length_append]

@[simp] theorem hashCalls_oracleHash (f : QueryImpl HashSpec Id) (input : HashInput) :
    hashCalls f (oracleHash input : OracleComp HashSpec HashOutput) = 1 := rfl

@[simp] theorem hashCalls_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    hashCalls f (tweakableHash parameter domain payload : OracleComp HashSpec Digest) = 1 := by
  simp only [hashCalls, queriedInputs_tweakableHash, List.length_singleton]

@[simp] theorem hashCalls_deriveKey (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    hashCalls f (deriveKey parameter domain seed : OracleComp HashSpec Digest) = 1 := by
  simp only [deriveKey, hashCalls_bind, hashCalls_oracleHash, hashCalls_pure, Nat.add_zero]

@[simp] theorem hashCalls_deriveOutput (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    hashCalls f (deriveOutput parameter domain seed : OracleComp HashSpec HashOutput) = 1 := by
  simp only [deriveOutput, hashCalls_oracleHash]

theorem hashCalls_sequenceFin {α : Type} {n : Nat} (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α) :
    hashCalls f (sequenceFin computation) = ∑ i, hashCalls f (computation i) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      simp only [sequenceFin, hashCalls_bind, hashCalls_pure, Nat.add_zero, ih,
        Fin.sum_univ_succ]

theorem hashCalls_chainWalk (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    hashCalls f (chainWalk parameter lay tree leaf chain start steps value : OracleComp HashSpec Digest) = steps := by
  induction steps generalizing start value with
  | zero => simp only [chainWalk, hashCalls_pure]
  | succ steps ih =>
      rw [chainWalk, hashCalls_bind, dif_pos (by omega), hashCalls_tweakableHash, ih _ _ (by omega)]

/-- The 64 chain starts of a one-time key cost 32 seed derivations. -/
theorem hashCalls_otsSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.otsSecrets parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) = 32 := by
  simp only [Seeded.otsSecrets, hashCalls_bind, hashCalls_sequenceFin, hashCalls_deriveOutput,
    hashCalls_pure]
  decide

/-- A one-time key costs `32 + 64 · 3 = 224` calls. -/
theorem hashCalls_oneTimePublicKey (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.oneTimePublicKey parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) = 224 := by
  simp only [Seeded.oneTimePublicKey, hashCalls_sequenceFin, hashCalls_bind, hashCalls_otsSecrets]
  have walk (chain : ChainIndex) (value : Digest) :
      hashCalls f (chainWalk parameter lay tree leaf chain 0 (chainLength - 1) value :
        OracleComp HashSpec Digest) = chainLength - 1 :=
    hashCalls_chainWalk f parameter lay tree leaf chain 0 (chainLength - 1) value (by omega)
  simp only [walk]
  decide

theorem hashCalls_treeNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (level nodeIdx : Nat) :
    hashCalls f (Seeded.treeNode parameter lay tree seed level nodeIdx : OracleComp HashSpec Digest) =
      226 * 2 ^ level - 1 := by
  induction level generalizing nodeIdx with
  | zero => simp [Seeded.treeNode, hashCalls_bind, hashCalls_oneTimePublicKey, leafHash]
  | succ level ih =>
      simp only [Seeded.treeNode, hashCalls_bind, ih, hashCalls_tweakableHash]
      have hpos : 0 < 2 ^ level := Nat.two_pow_pos level
      rw [pow_succ]
      omega

/-- A FORS node at level `level + 1` costs `5 · 2^level - 1` calls: per pair of leaves a derivation
and two hashes. -/
theorem hashCalls_forsNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (κ : FTree) (seed : MasterSeed) (level node : Nat) (hlevel : level < forsHeight) :
    hashCalls f (Seeded.forsNode parameter index κ seed (level + 1) node : OracleComp HashSpec Digest) =
      5 * 2 ^ level - 1 := by
  induction level generalizing node with
  | zero =>
      rw [Seeded.forsNode, hashCalls_bind, hashCalls_deriveOutput, hashCalls_bind, forsLeafHash,
        hashCalls_tweakableHash, hashCalls_bind, forsLeafHash, hashCalls_tweakableHash, hashCalls_tweakableHash]
      rfl
  | succ level ih =>
      rw [Seeded.forsNode, hashCalls_bind, hashCalls_bind, dif_pos hlevel, hashCalls_tweakableHash,
        ih _ (by omega), ih _ (by omega)]
      have hp : 0 < 2 ^ level := Nat.two_pow_pos level
      rw [pow_succ]
      omega

/-- Building the FORS key costs `k · 2 · (5 · 2^(a - 2) - 1)` hash calls: the two level-`(a - 1)` nodes
of each of the `k` trees. A tree has no root hash and the key has no hash. -/
theorem hashCalls_forsKey (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) :
    hashCalls f (Seeded.forsKey parameter index seed : OracleComp HashSpec ForsKey) =
      forsTrees * (2 * (5 * 2 ^ (forsHeight - 2) - 1)) := by
  have ha := Params.forsHeight_ge
  have htop (κ : FTree) (node : Nat) :
      hashCalls f (Seeded.forsNode parameter index κ seed (forsHeight - 1) node : OracleComp HashSpec Digest) =
        5 * 2 ^ (forsHeight - 2) - 1 := by
    have h := hashCalls_forsNode f parameter index κ seed (forsHeight - 2) node (by omega)
    rwa [show forsHeight - 2 + 1 = forsHeight - 1 by omega] at h
  rw [Seeded.forsKey, hashCalls_sequenceFin]
  simp only [hashCalls_bind, hashCalls_pure, htop, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

theorem hashCalls_encode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput) (counter : Counter) :
    hashCalls f (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) = 1 := by
  simp only [encode, hashCalls_bind, hashCalls_tweakableHash, hashCalls_pure, Nat.add_zero]

/-- The cost of running the computations from index `0` up, stopping after the first failure. -/
def seqCost : {n : Nat} → (Fin n → Bool) → (Fin n → Nat) → Nat
  | 0, _, _ => 0
  | _ + 1, ok, cost => cost 0 + if ok 0 then seqCost (fun i => ok i.succ) (fun i => cost i.succ) else 0

theorem hashCalls_sequenceDep (f : QueryImpl HashSpec Id) : ∀ {n : Nat} {α : Fin n → Type}
    (computation : (i : Fin n) → OracleComp HashSpec (Option (α i))),
    hashCalls f (sequenceDep computation) =
      seqCost (fun i => (evalWithAnswerFn f (computation i)).isSome) (fun i => hashCalls f (computation i))
  | 0, _, _ => rfl
  | n + 1, α, computation => by
      simp only [sequenceDep, hashCalls_bind, seqCost]
      cases hhead : evalWithAnswerFn f (computation 0) with
      | none => simp only [hashCalls_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      | some head =>
          simp only [hashCalls_bind, Option.isSome_some, ↓reduceIte,
            hashCalls_sequenceDep f (α := fun i => α i.succ) fun i => computation i.succ]
          cases evalWithAnswerFn f (sequenceDep (α := fun i => α i.succ) fun i => computation i.succ) <;>
            simp only [hashCalls_pure, Nat.add_zero]

theorem hashCalls_sequenceLayers {α : Layer → Type} (f : QueryImpl HashSpec Id)
    (computation : (lay : Layer) → OracleComp HashSpec (Option (α lay))) :
    hashCalls f (sequenceLayers computation) =
      seqCost (fun lay => (evalWithAnswerFn f (computation lay)).isSome)
        (fun lay => hashCalls f (computation lay)) :=
  hashCalls_sequenceDep f computation

theorem hashCalls_messageDigestCall (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (message : Message) (randomness : Randomness) (call : DigestCall) :
    hashCalls f (messageDigestCall parameter root message randomness call : OracleComp HashSpec HashOutput) = 1 := rfl

theorem hashCalls_messageDigest (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (message : Message) (randomness : Randomness) :
    hashCalls f (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest) =
      digestCalls := by
  simp only [messageDigest, hashCalls_bind, hashCalls_sequenceFin, hashCalls_messageDigestCall, hashCalls_pure,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, Nat.add_zero]

theorem hashCalls_signAttempt (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) :
    hashCalls f (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) = 1 := by
  rw [Seeded.signAttempt, hashCalls_bind, hashCalls_messageDigestCall]
  split <;> rfl

end FORS.Security.Prefix

end

section

/-! Counting the hash queries of lifted hash computations: on a fixed answer function, counting
returns the value together with its `hashCalls`. Private randomizer draws contribute zero hash
calls. -/

open OracleComp OracleSpec

namespace FORS.Security.Prefix

variable [Params]
open Concrete QueryCap

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.finishSign
  Seeded.signAttempt
set_option backward.isDefEq.respectTransparency false

theorem counted_lift_hash {α : Type} (computation : OracleComp HashSpec α) :
    counted SourceHash (liftM computation : OracleComp OracleWorld α) =
    (liftM (counted (fun _ => True) computation) : OracleComp OracleWorld (α × Nat)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, counted_pure]
  | query_bind input next ih =>
      simp only [liftM_bind]
      change counted SourceHash (liftM (OracleWorld.query (.inr input)) >>= fun output => liftM (next output)) = _
      simp only [counted_query_bind, SourceHash, if_true, ih, liftM_bind, liftM_pure]
      rfl

theorem eval_counted_hash {α : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) :
    evalWithAnswerFn f (counted (fun _ => True) computation) =
      (evalWithAnswerFn f computation, hashCalls f computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [counted_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from simulateQ_spec_query f input,
        ih, if_true]
      change (_, 1 + hashCalls f (next (f input))) = (_, (input :: queriedInputs f (next (f input))).length)
      simp only [List.length_cons, hashCalls, Nat.add_comm]

theorem fixedHashWorld_counted_lift_hash {α : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedHashWorld f) (counted SourceHash (liftM computation : OracleComp OracleWorld α)) =
      PMF.pure (evalWithAnswerFn f computation, hashCalls f computation) := by
  rw [counted_lift_hash, fixedHashWorld_lift_hash, eval_counted_hash]

end FORS.Security.Prefix

end

section

/-! The exact hash cost of key generation: the top layer's kept subtree and its surrogate spine,
`226 · 2^k + 2 (h_top - k)` calls with `k = keptHeight topLayer` (`226 · 2^b + 2 (h - b)` for one
layer, `226 · 2^h_top` for a layered key). -/

open OracleComp OracleSpec

namespace FORS.Security.Prefix

variable [Params]
open Concrete Completeness SeedModel

attribute [local irreducible] Seeded.treeNode Seeded.spineNode Seeded.treeRoot
  programCache
set_option backward.isDefEq.respectTransparency false


theorem hashCalls_spineNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (steps : Nat)
    (hsteps : steps ≤ layerHeight lay - keptHeight lay) :
    hashCalls f (Seeded.spineNode parameter lay tree seed steps : OracleComp HashSpec Digest) =
      (226 * 2 ^ keptHeight lay - 1) + 2 * steps := by
  induction steps with
  | zero => simp only [Seeded.spineNode, hashCalls_treeNode, Nat.mul_zero, Nat.add_zero]
  | succ steps ih =>
      have hkl := Completeness.keptHeight_le lay
      have hll := layerHeight_le lay
      have hlevel : keptHeight lay + steps < maxLayerHeight := by omega
      rw [Seeded.spineNode, hashCalls_bind, ih (by omega), hashCalls_bind]
      simp only [Seeded.surrogate, dif_pos hlevel, hashCalls_deriveKey]
      split <;> rw [hashCalls_tweakableHash] <;> omega

/-- The cost of a layer's tree root: its kept part and its spine. -/
theorem hashCalls_treeRoot (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) =
      (226 * 2 ^ keptHeight lay - 1) + 2 * (layerHeight lay - keptHeight lay) := by
  rw [Seeded.treeRoot, hashCalls_spineNode f _ _ _ seed _ (le_refl _)]

/-- The hash calls of key generation: the parameter, the top layer's kept subtree and its surrogate
spine. -/
def keygenHashCost : Nat := 226 * 2 ^ keptHeight topLayer + 2 * (layerHeight topLayer - keptHeight topLayer)

theorem hashCalls_keygenFromSeed (f : QueryImpl HashSpec Id) (seed : MasterSeed) :
    hashCalls f (Seeded.keygenFromSeed seed) = keygenHashCost := by
  unfold keygenHashCost
  simp only [Seeded.keygenFromSeed, hashCalls_bind, hashCalls_deriveKey, hashCalls_treeRoot,
    hashCalls_pure, Nat.add_zero]
  have := Nat.two_pow_pos (keptHeight topLayer)
  omega

end FORS.Security.Prefix

end

section

/-! The fixed-function cost world (`fixedWorldCost`: private draws are free, hash queries cost one
each), and how mapping the base monad commutes with query logging and with lifting. -/

open OracleComp OracleSpec

namespace FORS.Security.Prefix

variable [Params]
open Concrete Completeness SeedModel
open SeedCoupling
open QueryCap

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000
attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

noncomputable def fixedWorldCost (f : QueryImpl HashSpec Id) :
    QueryImpl OracleWorld (AddWriterT Nat PMF) :=
  (fixedHashWorld f).withAddCost (fun | .inl _ => 0 | .inr _ => 1)

theorem map_logging_query {I J : Type} {spec : OracleSpec I} {target : OracleSpec J}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (outer : QueryImpl target m) (inner : QueryImpl spec (OracleComp target)) (input : I) :
    (outer.writerTMapBase inner.withLogging) input =
      (QueryImpl.withLogging (spec := spec) (fun t => simulateQ outer (inner t))) input := by
  apply WriterT.ext
  simp only [QueryImpl.writerTMapBase, QueryImpl.run_withLogging_apply]
  change simulateQ outer (inner input >>= fun output =>
    pure (output, (show QueryLog spec from [⟨input, output⟩]))) = _
  simp only [simulateQ_bind, simulateQ_pure]

theorem map_lift_query {I J : Type} {spec : OracleSpec I} {target : OracleSpec J}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {log : Type} [EmptyCollection log] [Append log]
    (outer : QueryImpl target m) (inner : QueryImpl spec (OracleComp target)) (input : I) :
    (outer.writerTMapBase (inner.liftTarget (WriterT log (OracleComp target)))) input =
      (liftM (simulateQ outer (inner input)) : WriterT log m (spec.Range input)) := by
  apply WriterT.ext
  change simulateQ outer ((fun output => (output, (∅ : log))) <$> inner input) = _
  rw [simulateQ_map]
  rfl

end FORS.Security.Prefix

end
