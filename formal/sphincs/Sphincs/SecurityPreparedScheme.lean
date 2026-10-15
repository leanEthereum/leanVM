import Sphincs.SecuritySeedCoupling

/-!
Privileged compilation of honest seeded computations into material reads and ordinary hash calls.
Every replaced derivation emits one explicit virtual query, so its hash cost is retained. Only
honest code is compiled; adversarial hash requests must continue to use the ordinary hash oracle.
-/

open OracleComp OracleSpec

namespace Sphincs.Security.PreparedScheme
open SeedModel SeedCoupling Completeness Concrete

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] programCache digestAttemptLimit encodingAttemptLimit
  sequenceFin Seeded.treeNode Seeded.spineNode Seeded.subNode Seeded.topNode chainWalk forestWalk

/-- A replaced honest derivation still consumes one counted call. -/
abbrev VirtualSpec := Unit →ₒ Unit
abbrev PreparedHashSpec := HashSpec + VirtualSpec
abbrev PreparedWorld := unifSpec + PreparedHashSpec

noncomputable def tick : OracleComp PreparedHashSpec Unit :=
  liftM (VirtualSpec.query ())

/-- Privileged compiler for honest code. Its emitted raw hash calls do not pass through this
compiler a second time, and its material reads leave a visible unit-cost virtual query. -/
noncomputable def compileHash (seed : MasterSeed) (material : Material) :
    QueryImpl HashSpec (OracleComp PreparedHashSpec) := fun input =>
  match programCache ∅ seed material input with
  | none => liftM (HashSpec.query input)
  | some output => do
      let _ ← tick
      pure output

noncomputable def compileWorld (seed : MasterSeed) (material : Material) :
    QueryImpl OracleWorld (OracleComp PreparedWorld) :=
  QueryImpl.addLift (QueryImpl.ofLift unifSpec (OracleComp PreparedWorld)) (compileHash seed material)

theorem simulate_sequenceFin {I : Type} {spec : OracleSpec I} {m : Type → Type}
    [Monad m] [LawfulMonad m] {α : Type} {n : Nat} (impl : QueryImpl spec m)
    (computations : Fin n → OracleComp spec α) :
    simulateQ impl (sequenceFin computations) = sequenceFin (fun i => simulateQ impl (computations i)) := by
  induction n with
  | zero => simp only [sequenceFin, simulateQ_pure]
  | succ n ih => simp only [sequenceFin, simulateQ_bind, simulateQ_pure, ih]

theorem compile_oracleHash (seed : MasterSeed) (material : Material) (input : HashInput) :
    simulateQ (compileHash seed material) (oracleHash input : OracleComp HashSpec HashOutput) =
      compileHash seed material input := by
  simp only [oracleHash, HasQuery.query]
  exact simulateQ_spec_query _ _

theorem compile_parameter (seed : MasterSeed) (material : Material) :
    simulateQ (compileHash seed material) (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) =
      (do let _ ← tick; pure (parameter material)) := by
  simp only [deriveKey, simulateQ_bind, simulateQ_pure, compile_oracleHash]
  rw [show keygenHashInput 0 .parameter seed = parameterInput seed from rfl,
    compileHash, programCache_parameter]
  simp only [bind_assoc, pure_bind]
  rfl

/-- One derivation is one tick and the answer the material gives it. -/
theorem compile_derivation (seed : MasterSeed) (material : Material) (derivation : Derivation) :
    simulateQ (compileHash seed material)
      (deriveOutput (parameter material) (derivationDomain derivation) seed : OracleComp HashSpec HashOutput) =
      (do let _ ← tick; pure (derivedOutput material.2 derivation)) := by
  simp only [deriveOutput, compile_oracleHash]
  rw [show keygenHashInput (parameter material) (derivationDomain derivation) seed =
      derivationInput seed material derivation from rfl, compileHash, programCache_derivation]

/-- The derivation of a pair of WOTS+C chain starts: one tick. -/
theorem compile_ots (seed : MasterSeed) (material : Material) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair) :
    simulateQ (compileHash seed material)
      (deriveOutput (parameter material) (.ots lay tree leaf pair) seed : OracleComp HashSpec HashOutput) =
      (do let _ ← tick; pure (derivedOutput material.2 (.inl (lay, tree, leaf, pair)))) := by
  simpa only [derivationDomain] using compile_derivation seed material (.inl (lay, tree, leaf, pair))

/-- The derivation of a pair of forest chain starts: one tick. -/
theorem compile_forest (seed : MasterSeed) (material : Material) (index : Index)
    (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (pair : FPair) :
    simulateQ (compileHash seed material)
      (deriveOutput (parameter material) (.forest index c s j a pair) seed : OracleComp HashSpec HashOutput) =
      (do let _ ← tick; pure (derivedOutput material.2 (.inr (.inl (index, c, s, j, a, pair))))) := by
  simpa only [derivationDomain] using compile_derivation seed material (.inr (.inl (index, c, s, j, a, pair)))

theorem compile_surrogate (seed : MasterSeed) (material : Material) (level : Fin totalHeight) :
    simulateQ (compileHash seed material)
      (deriveKey (parameter material) (.surrogate level) seed : OracleComp HashSpec Digest) =
      (do let _ ← tick; pure (truncateHash (material.2 (.inr (.inr level))))) := by
  simp only [deriveKey, simulateQ_bind, simulateQ_pure, compile_oracleHash]
  rw [show keygenHashInput (parameter material) (.surrogate level) seed =
      derivationInput seed material (.inr (.inr level)) from rfl, compileHash, programCache_derivation]
  simp only [bind_assoc, pure_bind]
  rfl

theorem compile_tweakableHash (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    simulateQ (compileHash seed material)
      (tweakableHash p domain payload : OracleComp HashSpec Digest) =
        liftM (tweakableHash p domain payload : OracleComp HashSpec Digest) := by
  simp only [tweakableHash, simulateQ_bind, simulateQ_pure, compile_oracleHash]
  rw [compileHash, programCache_verifier]
  rfl

theorem compile_messageDigestCall (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    simulateQ (compileHash seed material)
      (messageDigestCall p root message randomness : OracleComp HashSpec HashOutput) =
        liftM (messageDigestCall p root message randomness : OracleComp HashSpec HashOutput) := by
  rw [messageDigestCall, compile_oracleHash, compileHash, programCache_verifier]
  rfl

theorem compileWorld_lift_hash {α : Type} (seed : MasterSeed) (material : Material)
    (computation : OracleComp HashSpec α) :
    simulateQ (compileWorld seed material) (liftM computation : OracleComp OracleWorld α) =
      liftM (simulateQ (compileHash seed material) computation) := by
  rw [compileWorld, QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftM_right,
    simulateQ_liftTarget]

theorem compileWorld_lift_prob {α : Type} (seed : MasterSeed) (material : Material)
    (computation : ProbComp α) :
    simulateQ (compileWorld seed material) (liftM computation : OracleComp OracleWorld α) =
      (liftM computation : OracleComp PreparedWorld α) := by
  rw [compileWorld, QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftM_left,
    simulateQ_liftTarget]
  rfl

theorem compile_chainWalk (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (start steps : Nat) (value : Digest) :
    simulateQ (compileHash seed material)
      (chainWalk p lay tree leaf chain start steps value : OracleComp HashSpec Digest) =
        liftM (chainWalk p lay tree leaf chain start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => simp only [chainWalk, simulateQ_pure, liftM_pure]
  | succ steps ih =>
      simp only [chainWalk, simulateQ_bind, liftM_bind, ih]
      apply bind_congr
      intro previous
      split <;> simp only [compile_tweakableHash, simulateQ_pure, liftM_pure]

theorem compile_forestWalk (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
    (i : FChain) (start steps : Nat) (value : Digest) :
    simulateQ (compileHash seed material)
      (forestWalk p index c s j a i start steps value : OracleComp HashSpec Digest) =
        liftM (forestWalk p index c s j a i start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => simp only [forestWalk, simulateQ_pure, liftM_pure]
  | succ steps ih =>
      simp only [forestWalk, simulateQ_bind, liftM_bind, ih]
      apply bind_congr
      intro previous
      split <;> simp only [compile_tweakableHash, simulateQ_pure, liftM_pure]

theorem compile_encode (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    simulateQ (compileHash seed material)
      (encode p lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) =
        liftM (encode p lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) := by
  simp only [encode, simulateQ_bind, compile_tweakableHash, simulateQ_pure, liftM_bind, liftM_pure]

/-- Changing the seed in the source code does not change the compiled chain starts of a one-time
key: 32 ticks and the material. -/
theorem compiled_otsSecrets_eq (left right : MasterSeed) (material : Material)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    simulateQ (compileHash left material)
      (Seeded.otsSecrets (parameter material) lay tree leaf left : OracleComp HashSpec _) =
    simulateQ (compileHash right material)
      (Seeded.otsSecrets (parameter material) lay tree leaf right : OracleComp HashSpec _) := by
  simp only [Seeded.otsSecrets, simulate_sequenceFin, simulateQ_bind, compile_ots, simulateQ_pure]

/-- Changing the seed in the source code does not change the compiled OTS public key. -/
theorem compiled_oneTimePublicKey_eq (left right : MasterSeed) (material : Material)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    simulateQ (compileHash left material)
      (Seeded.oneTimePublicKey (parameter material) lay tree leaf left : OracleComp HashSpec _) =
    simulateQ (compileHash right material)
      (Seeded.oneTimePublicKey (parameter material) lay tree leaf right : OracleComp HashSpec _) := by
  simp only [Seeded.oneTimePublicKey, simulate_sequenceFin, simulateQ_bind,
    compiled_otsSecrets_eq left right, compile_chainWalk]

theorem compiled_treeNode_eq (left right : MasterSeed) (material : Material)
    (lay : Layer) (tree : TreeIndex) (level node : Nat) :
    simulateQ (compileHash left material)
      (Seeded.treeNode (parameter material) lay tree left level node : OracleComp HashSpec Digest) =
    simulateQ (compileHash right material)
      (Seeded.treeNode (parameter material) lay tree right level node : OracleComp HashSpec Digest) := by
  induction level generalizing node with
  | zero =>
      simp only [Seeded.treeNode, simulateQ_bind, compiled_oneTimePublicKey_eq left right,
        leafHash, compile_tweakableHash]
  | succ level ih =>
      simp only [Seeded.treeNode, simulateQ_bind, ih, compile_tweakableHash]

variable [Params]

omit [Params] in
theorem compiled_surrogate_eq (left right : MasterSeed) (material : Material) (level : Nat) :
    simulateQ (compileHash left material)
      (Seeded.surrogate (parameter material) left level : OracleComp HashSpec Digest) =
    simulateQ (compileHash right material)
      (Seeded.surrogate (parameter material) right level : OracleComp HashSpec Digest) := by
  simp only [Seeded.surrogate, simulateQ_dite, compile_surrogate, simulateQ_pure]

theorem compiled_spineNode_eq (left right : MasterSeed) (material : Material)
    (lay : Layer) (tree : TreeIndex) (steps : Nat) :
    simulateQ (compileHash left material)
      (Seeded.spineNode (parameter material) lay tree left steps : OracleComp HashSpec Digest) =
    simulateQ (compileHash right material)
      (Seeded.spineNode (parameter material) lay tree right steps : OracleComp HashSpec Digest) := by
  induction steps with
  | zero =>
      rw [Seeded.spineNode, Seeded.spineNode]
      exact compiled_treeNode_eq left right material lay tree _ _
  | succ steps ih =>
      simp only [Seeded.spineNode, simulateQ_bind, ih, compiled_surrogate_eq left right]
      apply bind_congr
      intro below
      apply bind_congr
      intro sibling
      split <;> rw [compile_tweakableHash, compile_tweakableHash]

theorem compiled_treePath_eq (left right : MasterSeed) (material : Material)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    simulateQ (compileHash left material)
      (Seeded.treePath (parameter material) lay tree left leaf : OracleComp HashSpec _) =
    simulateQ (compileHash right material)
      (Seeded.treePath (parameter material) lay tree right leaf : OracleComp HashSpec _) := by
  simp only [Seeded.treePath, simulate_sequenceFin]
  congr 1
  funext level
  split
  · exact compiled_treeNode_eq left right material lay tree _ _
  · exact compiled_surrogate_eq left right material _

omit [Params] in
/-- The compiled chain starts of a child: 3 ticks and the material. -/
theorem compiled_forestSecrets_eq (left right : MasterSeed) (material : Material)
    (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) :
    simulateQ (compileHash left material)
      (Seeded.forestSecrets (parameter material) index c s j a left : OracleComp HashSpec _) =
    simulateQ (compileHash right material)
      (Seeded.forestSecrets (parameter material) index c s j a right : OracleComp HashSpec _) := by
  simp only [Seeded.forestSecrets, simulate_sequenceFin, simulateQ_bind, compile_forest, simulateQ_pure]

omit [Params] in
theorem compiled_chainValue_eq (left right : MasterSeed) (material : Material)
    (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (pos : Nat) :
    simulateQ (compileHash left material)
      (Seeded.chainValue (parameter material) index c s j a i left pos : OracleComp HashSpec Digest) =
    simulateQ (compileHash right material)
      (Seeded.chainValue (parameter material) index c s j a i right pos : OracleComp HashSpec Digest) := by
  simp only [Seeded.chainValue, Seeded.forestStart, simulateQ_bind, compile_forest, compile_forestWalk,
    simulateQ_pure]

omit [Params] in
theorem compiled_childLeaf_eq (left right : MasterSeed) (material : Material)
    (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) :
    simulateQ (compileHash left material)
      (Seeded.childLeaf (parameter material) index c s j a left : OracleComp HashSpec Digest) =
    simulateQ (compileHash right material)
      (Seeded.childLeaf (parameter material) index c s j a right : OracleComp HashSpec Digest) := by
  simp only [Seeded.childLeaf, simulateQ_bind, simulate_sequenceFin, compiled_forestSecrets_eq left right,
    compile_forestWalk, childLeafHash, compile_tweakableHash]

omit [Params] in
theorem compiled_subNode_eq (left right : MasterSeed) (material : Material)
    (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (level node : Nat) :
    simulateQ (compileHash left material)
      (Seeded.subNode (parameter material) index c s j left level node : OracleComp HashSpec Digest) =
    simulateQ (compileHash right material)
      (Seeded.subNode (parameter material) index c s j right level node : OracleComp HashSpec Digest) := by
  induction level generalizing node with
  | zero =>
      rw [Seeded.subNode, Seeded.subNode]
      exact compiled_childLeaf_eq left right material _ _ _ _ _
  | succ level ih =>
      simp only [Seeded.subNode, simulateQ_bind, ih]
      apply bind_congr
      intro l
      apply bind_congr
      intro r
      split <;> simp only [compile_tweakableHash, simulateQ_pure]

omit [Params] in
theorem compiled_superNode_eq (left right : MasterSeed) (material : Material)
    (index : Index) (c : Coord) (s : SuperIdx) :
    simulateQ (compileHash left material)
      (Seeded.superNode (parameter material) index c s left : OracleComp HashSpec Digest) =
    simulateQ (compileHash right material)
      (Seeded.superNode (parameter material) index c s right : OracleComp HashSpec Digest) := by
  simp only [Seeded.superNode, simulateQ_bind, simulate_sequenceFin, compiled_subNode_eq left right,
    superHash, compile_tweakableHash, simulateQ_pure]

omit [Params] in
theorem compiled_topNode_eq (left right : MasterSeed) (material : Material)
    (index : Index) (c : Coord) (level node : Nat) :
    simulateQ (compileHash left material)
      (Seeded.topNode (parameter material) index c left level node : OracleComp HashSpec Digest) =
    simulateQ (compileHash right material)
      (Seeded.topNode (parameter material) index c right level node : OracleComp HashSpec Digest) := by
  induction level generalizing node with
  | zero =>
      rw [Seeded.topNode, Seeded.topNode]
      exact compiled_superNode_eq left right material _ _ _
  | succ level ih =>
      simp only [Seeded.topNode, simulateQ_bind, ih]
      apply bind_congr
      intro l
      apply bind_congr
      intro r
      split <;> simp only [compile_tweakableHash, simulateQ_pure]

omit [Params] in
theorem compiled_forestKey_eq (left right : MasterSeed) (material : Material) (index : Index) :
    simulateQ (compileHash left material)
      (Seeded.forestKey (parameter material) index left : OracleComp HashSpec Digest) =
    simulateQ (compileHash right material)
      (Seeded.forestKey (parameter material) index right : OracleComp HashSpec Digest) := by
  simp only [Seeded.forestKey, simulateQ_bind, simulate_sequenceFin,
    compiled_topNode_eq left right, compile_tweakableHash, simulateQ_pure]

omit [Params] in
theorem compiled_coordOpen_eq (left right : MasterSeed) (material : Material) (index : Index)
    (c : Coord) (mark : CoordMark) :
    simulateQ (compileHash left material)
      (Seeded.coordOpen (parameter material) index c mark left : OracleComp HashSpec _) =
    simulateQ (compileHash right material)
      (Seeded.coordOpen (parameter material) index c mark right : OracleComp HashSpec _) := by
  simp only [Seeded.coordOpen, simulateQ_bind, simulate_sequenceFin, compiled_forestSecrets_eq left right,
    compile_forestWalk, compiled_subNode_eq left right, compiled_topNode_eq left right, simulateQ_pure]

omit [Params] in
theorem compiled_forestOpen_eq (left right : MasterSeed) (material : Material) (index : Index)
    (marks : Coord → CoordMark) :
    simulateQ (compileHash left material)
      (Seeded.forestOpen (parameter material) index marks left : OracleComp HashSpec _) =
    simulateQ (compileHash right material)
      (Seeded.forestOpen (parameter material) index marks right : OracleComp HashSpec _) := by
  simp only [Seeded.forestOpen, simulate_sequenceFin, compiled_coordOpen_eq left right]

omit [Params] in
theorem compiled_otsSignFrom_eq (left right : MasterSeed) (material : Material)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (attempts counter : Nat) :
    simulateQ (compileHash left material)
      (Seeded.otsSignFrom (parameter material) lay tree leaf left message attempts counter : OracleComp HashSpec _) =
    simulateQ (compileHash right material)
      (Seeded.otsSignFrom (parameter material) lay tree leaf right message attempts counter : OracleComp HashSpec _) := by
  induction attempts generalizing counter with
  | zero => simp only [Seeded.otsSignFrom, simulateQ_pure]
  | succ attempts ih =>
      simp only [Seeded.otsSignFrom, simulateQ_bind, compile_encode]
      apply bind_congr
      intro encoded
      cases encoded with
      | none => exact ih _
      | some encoded =>
          simp only [simulateQ_bind, simulate_sequenceFin, compiled_otsSecrets_eq left right,
            compile_chainWalk, simulateQ_pure]

/-- Replace only the private seed field, retaining the public fields used by signing. -/
def reseedKey (seed : MasterSeed) (key : Seeded.SecretKey) : Seeded.SecretKey :=
  ⟨seed, key.parameter, key.root⟩

/-- Key generation compiles identically except for its explicit private seed field. -/
theorem compiled_keygen_eq (left right : MasterSeed) (material : Material) :
    simulateQ (compileHash left material) (Seeded.keygenFromSeed left) =
      (fun result => (result.1, reseedKey left result.2)) <$>
        simulateQ (compileHash right material) (Seeded.keygenFromSeed right) := by
  simp only [Seeded.keygenFromSeed, simulateQ_bind, compile_parameter, bind_assoc, pure_bind,
    map_bind, Seeded.treeRoot, compiled_spineNode_eq left right, simulateQ_pure, map_pure, reseedKey]

/-- Candidate key generation using only material, ordinary hash calls, and virtual ticks. -/
noncomputable def keygen (material : Material) : OracleComp PreparedHashSpec (PublicKey × Seeded.SecretKey) :=
  simulateQ (compileHash 0 material) (Seeded.keygenFromSeed 0)

theorem compile_keygen (seed : MasterSeed) (material : Material) :
    simulateQ (compileHash seed material) (Seeded.keygenFromSeed seed) =
      (fun result => (result.1, reseedKey seed result.2)) <$> keygen material :=
  compiled_keygen_eq seed 0 material

theorem compiled_signLayer_eq (left right : MasterSeed) (material : Material) (root : Digest)
    (index : Index) (lay : Layer) :
    simulateQ (compileHash left material)
      (Seeded.signLayer ⟨left, parameter material, root⟩ index lay : OracleComp HashSpec _) =
    simulateQ (compileHash right material)
      (Seeded.signLayer ⟨right, parameter material, root⟩ index lay : OracleComp HashSpec _) := by
  simp only [Seeded.signLayer, Seeded.layerMessage, simulateQ_bind, compiled_forestKey_eq left right,
    Seeded.otsSign, compiled_otsSignFrom_eq left right]
  apply bind_congr
  intro message
  apply bind_congr
  intro result
  cases result with
  | none => rw [simulateQ_pure, simulateQ_pure]
  | some result =>
      simp only [simulateQ_bind, compiled_treePath_eq left right, simulateQ_pure]

omit [Params] in
theorem compile_messageDigest (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    simulateQ (compileHash seed material)
      (messageDigest p root message randomness : OracleComp HashSpec MessageDigest) =
      liftM (messageDigest p root message randomness : OracleComp HashSpec MessageDigest) := by
  simp only [messageDigest, simulateQ_bind, compile_messageDigestCall,
    simulateQ_pure, liftM_bind, liftM_pure]

theorem compiled_finishSign_eq (left right : MasterSeed) (material : Material) (root : Digest)
    (message : Message) (randomness : Randomness) :
    simulateQ (compileHash left material)
      (Randomized.finishSign ⟨left, parameter material, root⟩ message randomness) =
    simulateQ (compileHash right material)
      (Randomized.finishSign ⟨right, parameter material, root⟩ message randomness) := by
  simp only [Randomized.finishSign, simulateQ_bind, compile_messageDigest]
  apply bind_congr
  intro digest
  simp only [compiled_forestOpen_eq left right]
  apply bind_congr
  intro opening
  simp only [sequenceLayers, simulateQ_bind, compiled_signLayer_eq left right, bind_assoc]
  apply bind_congr
  intro layer
  cases layer <;> simp only [simulateQ_pure, pure_bind]

theorem compile_signAttempt (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    simulateQ (compileHash seed material)
      (Seeded.signAttempt ⟨seed, p, root⟩ message randomness : OracleComp HashSpec (Option Index)) =
      liftM (Seeded.signAttempt ⟨0, p, root⟩ message randomness : OracleComp HashSpec (Option Index)) := by
  simp only [Seeded.signAttempt, simulateQ_bind, compile_messageDigestCall, liftM_bind]
  apply bind_congr
  intro first
  split <;> simp only [simulateQ_pure, liftM_pure]

/-- The scan from a start makes only digest calls, which do not depend on the seed. -/
theorem compiled_scanLoop_eq (left right : MasterSeed) (material : Material) (root : Digest)
    (message : Message) :
    ∀ (attempts : Nat) (randomness : Randomness),
      simulateQ (compileHash left material)
        (Randomized.scanLoop ⟨left, parameter material, root⟩ message attempts randomness) =
      simulateQ (compileHash right material)
        (Randomized.scanLoop ⟨right, parameter material, root⟩ message attempts randomness) := by
  intro attempts
  induction attempts with
  | zero => intro randomness; simp only [Randomized.scanLoop, simulateQ_pure]
  | succ attempts ih =>
      intro randomness
      simp only [Randomized.scanLoop, simulateQ_bind, compile_signAttempt]
      apply bind_congr
      intro result
      cases result with
      | none => exact ih (randomness + 1)
      | some index => rw [simulateQ_pure, simulateQ_pure]

/-- The genuinely private start draw is retained while compiling the grinding loop. -/
theorem compiled_signDigestLoop_eq (left right : MasterSeed) (material : Material) (root : Digest)
    (message : Message) (attempts : Nat) :
    simulateQ (compileWorld left material)
      (Randomized.signDigestLoop ⟨left, parameter material, root⟩ message attempts) =
    simulateQ (compileWorld right material)
      (Randomized.signDigestLoop ⟨right, parameter material, root⟩ message attempts) := by
  simp only [Randomized.signDigestLoop, simulateQ_bind, compileWorld_lift_prob,
    compileWorld_lift_hash, compiled_scanLoop_eq left right]

theorem compiled_sign_eq (left right : MasterSeed) (material : Material) (root : Digest)
    (message : Message) :
    simulateQ (compileWorld left material)
      (Randomized.sign ⟨left, parameter material, root⟩ message) =
    simulateQ (compileWorld right material)
      (Randomized.sign ⟨right, parameter material, root⟩ message) := by
  simp only [Randomized.sign, simulateQ_bind, compiled_signDigestLoop_eq left right]
  apply bind_congr
  intro result
  cases result with
  | none => rw [simulateQ_pure, simulateQ_pure]
  | some randomness =>
      rw [compileWorld_lift_hash, compileWorld_lift_hash, compiled_finishSign_eq left right]

/-- Signing is a computation of material and public root; it has no hidden-seed argument. -/
noncomputable def sign (material : Material) (root : Digest) (message : Message) :
    OracleComp PreparedWorld (Option Signature) :=
  simulateQ (compileWorld 0 material) (Randomized.sign ⟨0, parameter material, root⟩ message)

theorem compile_sign (seed : MasterSeed) (material : Material) (root : Digest) (message : Message) :
    simulateQ (compileWorld seed material) (Randomized.sign ⟨seed, parameter material, root⟩ message) =
      sign material root message := compiled_sign_eq seed 0 material root message

end Sphincs.Security.PreparedScheme

namespace Sphincs.Security.PreparedScheme
open SeedModel SeedCoupling Completeness Concrete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] programCache

/-- The ordinary hash cache has no privileged material entries. Virtual queries only charge
cost; their answer is the unique unit value and they never query or modify this cache. -/
noncomputable def preparedHashOracle : QueryImpl PreparedHashSpec (StateT (QueryCache HashSpec) ProbComp) :=
  (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) +
    ((fun (_ : Unit) => pure ()) : QueryImpl VirtualSpec (StateT (QueryCache HashSpec) ProbComp))

noncomputable def preparedRom : QueryImpl PreparedWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + preparedHashOracle

theorem programCache_lookup (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (input : HashInput) :
    programCache base seed material input =
      match programCache ∅ seed material input with
      | some answer => some answer
      | none => base input := by
  unfold programCache
  split
  · rfl
  · split <;> rfl

theorem programCache_cacheQuery_none (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (input : HashInput) (answer : HashOutput) (hnone : programCache ∅ seed material input = none) :
    programCache (base.cacheQuery input answer) seed material =
      (programCache base seed material).cacheQuery input answer := by
  funext query
  by_cases hquery : query = input
  · subst query
    rw [programCache_lookup, hnone, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hquery]
    unfold programCache
    split
    · rfl
    · split
      · rfl
      · exact QueryCache.cacheQuery_of_ne _ _ hquery

theorem simulate_tick : simulateQ preparedHashOracle tick = pure () := by
  change simulateQ preparedHashOracle (liftM (PreparedHashSpec.query (.inr ()))) = pure ()
  rw [simulateQ_spec_query]
  rfl

theorem simulate_ordinary_query (input : HashInput) :
    simulateQ preparedHashOracle (liftM (HashSpec.query input) : OracleComp PreparedHashSpec HashOutput) =
      randomOracle (spec := HashSpec) input := by
  change simulateQ preparedHashOracle (liftM (PreparedHashSpec.query (.inl input))) = _
  rw [simulateQ_spec_query]
  rfl

/-- One original hash call corresponds either to a cached material read plus a virtual tick,
or to the same ordinary random-oracle call. -/
theorem run_compileHash_query (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (input : HashInput) :
    (randomOracle (spec := HashSpec) input).run (programCache base seed material) =
      (fun result => (result.1, programCache result.2 seed material)) <$>
        (simulateQ preparedHashOracle (compileHash seed material input)).run base := by
  cases htable : programCache ∅ seed material input with
  | some answer =>
      have hcached : programCache base seed material input = some answer := by
        rw [programCache_lookup, htable]
      rw [QueryImpl.withCaching_run_some _ hcached, compileHash, htable]
      simp only [simulateQ_bind, simulate_tick, simulateQ_pure, pure_bind, StateT.run_pure, map_pure]
  | none =>
      have hagree : programCache base seed material input = base input := by
        rw [programCache_lookup, htable]
      rw [compileHash, htable, simulate_ordinary_query]
      cases hcached : base input with
      | some answer =>
          rw [QueryImpl.withCaching_run_some _ hcached,
            QueryImpl.withCaching_run_some _ (hagree.trans hcached), map_pure]
      | none =>
          rw [QueryImpl.withCaching_run_none _ hcached,
            QueryImpl.withCaching_run_none _ (hagree.trans hcached), Functor.map_map]
          congr 1
          funext answer
          exact congrArg (fun cache => (answer, cache))
            (programCache_cacheQuery_none base seed material input answer htable).symm

theorem preparedRom_lift_hash {α : Type} (computation : OracleComp PreparedHashSpec α) :
    simulateQ preparedRom (liftM computation : OracleComp PreparedWorld α) =
      simulateQ preparedHashOracle computation :=
  QueryImpl.simulateQ_add_liftM_right _ _ _

theorem run_compileWorld_query (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (input : OracleWorld.Domain) :
    (romImpl input).run (programCache base seed material) =
      (fun result => (result.1, programCache result.2 seed material)) <$>
        (simulateQ preparedRom (compileWorld seed material input)).run base := by
  cases input with
  | inl input =>
      have hquery : compileWorld seed material (.inl input) =
          (liftM (PreparedWorld.query (.inl input)) : OracleComp PreparedWorld _) := rfl
      rw [hquery, simulateQ_spec_query]
      change ((fun answer => (answer, programCache base seed material)) <$>
          (liftM (unifSpec.query input) : ProbComp _)) = _
      rw [show (preparedRom (.inl input)).run base =
        (fun answer => (answer, base)) <$> (liftM (unifSpec.query input) : ProbComp _) from rfl,
        Functor.map_map]
  | inr input =>
      change (randomOracle (spec := HashSpec) input).run (programCache base seed material) =
        (fun result => (result.1, programCache result.2 seed material)) <$>
          (simulateQ preparedRom (liftM (compileHash seed material input))).run base
      rw [preparedRom_lift_hash]
      exact run_compileHash_query base seed material input

/-- Private draws are preserved as actual draws; only honest material queries become ticks. -/
theorem run_compileWorld {α : Type} (seed : MasterSeed) (material : Material)
    (computation : OracleComp OracleWorld α) (base : QueryCache HashSpec) :
    (simulateQ romImpl computation).run (programCache base seed material) =
      (fun result => (result.1, programCache result.2 seed material)) <$>
        (simulateQ preparedRom (simulateQ (compileWorld seed material) computation)).run base := by
  induction computation using OracleComp.inductionOn generalizing base with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [run_compileWorld_query, bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 result.2

/-- Both ordinary hash queries and virtual derivation queries count; private draws do not. -/
noncomputable def countPreparedQueries {α : Type} (computation : OracleComp PreparedWorld α) :
    OracleComp PreparedWorld (α × Nat) :=
  SphincsBase.QueryCap.counted
    (fun input : PreparedWorld.Domain => input matches .inr _) computation

noncomputable def preparedCountedOracle := preparedRom.withAddCost
  (fun | .inl _ => (0 : Nat) | .inr _ => 1)

theorem counted_query {I : Type} {spec : OracleSpec I} (selected : I → Prop)
    [DecidablePred selected] (input : spec.Domain) :
    SphincsBase.QueryCap.counted selected (liftM (spec.query input)) =
      (fun answer => (answer, if selected input then 1 else 0)) <$>
        (liftM (spec.query input) : OracleComp spec _) := by
  change (do
    let answer ← liftM (spec.query input)
    pure (answer, (if selected input then 1 else 0) + 0)) = _
  simp only [Nat.add_zero, bind_pure_comp]

theorem countPrepared_compileWorld_query (seed : MasterSeed) (material : Material)
    (input : OracleWorld.Domain) :
    countPreparedQueries (compileWorld seed material input) =
      (fun answer => (answer,
        if (fun query : OracleWorld.Domain => query matches .inr _) input then 1 else 0)) <$>
        compileWorld seed material input := by
  cases input with
  | inl input =>
      change SphincsBase.QueryCap.counted _
        (liftM (PreparedWorld.query (.inl input))) = _
      exact counted_query (spec := PreparedWorld) _ (.inl input)
  | inr input =>
      change countPreparedQueries (liftM (compileHash seed material input) : OracleComp PreparedWorld _) =
        (fun answer => (answer, 1)) <$> (liftM (compileHash seed material input) : OracleComp PreparedWorld _)
      unfold compileHash
      cases htable : programCache ∅ seed material input with
      | none =>
          change SphincsBase.QueryCap.counted _
            (liftM (PreparedWorld.query (.inr (.inl input)))) = _
          exact counted_query (spec := PreparedWorld) _ (.inr (.inl input))
      | some output =>
          simp only [liftM_bind, liftM_pure]
          change SphincsBase.QueryCap.counted _
            (liftM (PreparedWorld.query (.inr (.inr ()))) >>= fun _ => pure output) = _
          rw [SphincsBase.QueryCap.counted_query_bind]
          simp only [SphincsBase.QueryCap.counted_pure, pure_bind, Nat.add_zero, map_bind, map_pure]
          rfl

/-- Compiling an instrumented computation equals instrumenting the compiled computation.
This equality is the reason no replaced derivation disappears from the hash budget. -/
theorem countPrepared_compileWorld {α : Type} (seed : MasterSeed) (material : Material)
    (computation : OracleComp OracleWorld α) :
    countPreparedQueries (simulateQ (compileWorld seed material) computation) =
      simulateQ (compileWorld seed material) (countHashQueries computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, countHashQueries_query_bind,
        simulateQ_pure]
      rw [countPreparedQueries, SphincsBase.QueryCap.counted_bind]
      change (countPreparedQueries (compileWorld seed material input) >>= _) = _
      rw [countPrepared_compileWorld_query, bind_map_left]
      apply bind_congr
      intro answer
      change (countPreparedQueries (simulateQ (compileWorld seed material) (next answer)) >>= _) = _
      rw [ih answer]
      rfl

theorem simulateQ_countPreparedQueries {α : Type} (computation : OracleComp PreparedWorld α) :
    simulateQ preparedRom (countPreparedQueries computation) =
      (simulateQ preparedCountedOracle computation).run := by
  rw [countPreparedQueries, SphincsBase.QueryCap.simulate_withCost]
  congr 2
  funext input
  cases input <;> rfl

/-- Exact preservation of the result, total original hash count, and related final caches.
Virtual queries retain every substituted derivation's cost. -/
theorem run_compileWorld_counted {α : Type} (seed : MasterSeed) (material : Material)
    (computation : OracleComp OracleWorld α) (base : QueryCache HashSpec) :
    (simulateQ countedOracle computation).run.run (programCache base seed material) =
      (fun result => (result.1, programCache result.2 seed material)) <$>
        (simulateQ preparedCountedOracle (simulateQ (compileWorld seed material) computation)).run.run base := by
  rw [← simulateQ_countHashQueries, run_compileWorld, ← countPrepared_compileWorld,
    simulateQ_countPreparedQueries]

variable [Params]

/-- Prepared key generation returns its material parameter and a dummy-seed private key. -/
theorem keygen_eq (material : Material) :
    keygen material = (do
      let _ ← tick
      let root ← simulateQ (compileHash 0 material)
        (Seeded.treeRoot (parameter material) topLayer rootTree 0 : OracleComp HashSpec Digest)
      return (⟨root, parameter material⟩, ⟨0, parameter material, root⟩)) := by
  simp only [keygen, Seeded.keygenFromSeed, simulateQ_bind, compile_parameter,
    bind_assoc, pure_bind, simulateQ_pure]

/-- Ordinary adversarial queries bypass the privileged honest-code compiler completely. -/
noncomputable def ordinaryWorld : QueryImpl OracleWorld (OracleComp PreparedWorld)
  | .inl input => liftM (PreparedWorld.query (.inl input))
  | .inr input => liftM (PreparedWorld.query (.inr (.inl input)))

/-- The material sign oracle retains the same message/signature transcript as the actual game. -/
noncomputable def materialSigningOracle (material : Material) (root : Digest) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp PreparedWorld)) :=
  QueryImpl.withLogging fun message => liftM (sign material root message)

/-- A literally seed-independent frontend: honest derivations use the material compiler,
adversarial queries remain ordinary calls, and all calls retain their original unit cost. -/
noncomputable def materialGame (material : Material) (adversary : Adversary) :
    OracleComp PreparedWorld Bool := do
  let (pk, _) ← liftM (keygen material)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (ordinaryWorld.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp PreparedWorld)) +
      materialSigningOracle material pk.root) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

end Sphincs.Security.PreparedScheme
