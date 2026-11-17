module

public import Quantum.StdModel.Xmss.Gen
public import Quantum.StdModel.World

@[expose] public section

/-!
# Evaluating leanXMSS: naturality, fixed tables and the real operations

* **Naturality**: a monad morphism `F : m →ᵐ n` commutes with leanXMSS over any hash
  (`Over.mmap_keygenFromSeed`, `Over.mmap_sign`, `Over.mmap_verify`: `F` of the scheme over `hash`
  is the scheme over `F ∘ hash`), with the abstract signer (`Gen.mmap_sign`, ...: `F` of `Gen` over
  `o` is `Gen` over `o.map F`) and with grinding (`mmap_grind`).
* **Fixed tables**: a morphism sending each hash to a pure value sends the scheme to the pure
  scheme over those values (`Over.mmap_sign_of_pure`, ...); at a fixed table of a world, the
  scheme's computations are pure (`simulateQ_xmssOver_generateKeys`, `simulateQ_xmssOver_sign`,
  `simulateQ_xmssOver_verify`), and so is the abstract signer over operations answered purely
  (`Gen.simulateQ_sign`, `Gen.simulateQ_root`, `Gen.simulateQ_treeNode`).
* **Real operations**: `realOps h S P` are the signer's operations of the scheme seed `S` and
  the parameter `P`; the scheme over a pure hash is `Gen` over them (`keygenFromSeed_id`,
  `sign_id`).
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss Quantum.Qrom.Xmss

namespace Quantum.StdModel.Xmss

/-- **Operations through a monad morphism**: each operation followed by `F`. -/
def Ops.map {m n : Type → Type} [Monad m] [Monad n] (F : m →ᵐ n) (o : Ops m) : Ops n where
  chain l e i μ := F (o.chain l e i μ)
  leaf l e ends := F (o.leaf l e ends)
  node l k j a b := F (o.node l k j a b)
  encode e msg := F (o.encode e msg)

section Natural

variable {m n : Type → Type} [Monad m] [Monad n] (F : m →ᵐ n)

@[simp] theorem Ops.map_chain (o : Ops m) (l : Layer) (e : KeyIndex) (i : ChainIndex) (μ : ℕ) :
    (o.map F).chain l e i μ = F (o.chain l e i μ) :=
  rfl

@[simp] theorem Ops.map_leaf (o : Ops m) (l : Layer) (e : KeyIndex) (ends : ChainIndex → Digest) :
    (o.map F).leaf l e ends = F (o.leaf l e ends) :=
  rfl

@[simp] theorem Ops.map_node (o : Ops m) (l : Layer) (k j : ℕ) (a b : Digest) :
    (o.map F).node l k j a b = F (o.node l k j a b) :=
  rfl

@[simp] theorem Ops.map_encode (o : Ops m) (e : KeyIndex) (msg : LayerMsg) :
    (o.map F).encode e msg = F (o.encode e msg) :=
  rfl

/-! ## Naturality of the shared combinators -/

theorem mmap_sequenceFin {α : Type} {k : ℕ} (c : Fin k → m α) :
    F (sequenceFin c) = sequenceFin fun i ↦ F (c i) := by
  induction k with
  | zero => simp only [sequenceFin, F.mmap_pure]
  | succ k ih => simp only [sequenceFin, F.mmap_bind, F.mmap_pure, ih]

theorem mmap_walkChain {s : ℕ} (step : Fin s → Digest → m Digest) (start : ℕ) :
    ∀ (steps : ℕ) (v : Digest),
      F (walkChain step start steps v) = walkChain (fun t x ↦ F (step t x)) start steps v
  | 0, _ => by simp only [walkChain, F.mmap_pure]
  | steps + 1, v => by
    simp only [walkChain, F.mmap_bind, F.mmap_dite, F.mmap_pure, mmap_walkChain step start steps]

theorem mmap_foldPath (node : ℕ → ℕ → HashInput → m Digest) (idx : ℕ) (sib : ℕ → Digest) :
    ∀ (k : ℕ) (v : Digest),
      F (foldPath node idx sib k v) = foldPath (fun a b x ↦ F (node a b x)) idx sib k v
  | 0, _ => by simp only [foldPath, F.mmap_pure]
  | k + 1, v => by simp only [foldPath, F.mmap_bind, mmap_foldPath node idx sib k]

theorem mmap_buildTree (leaf : ℕ → m Digest) (node : ℕ → ℕ → HashInput → m Digest) :
    ∀ (k j : ℕ), F (buildTree leaf node k j) =
      buildTree (fun j ↦ F (leaf j)) (fun a b x ↦ F (node a b x)) k j
  | 0, _ => by simp only [buildTree]
  | k + 1, j => by simp only [buildTree, F.mmap_bind, mmap_buildTree leaf node k]

/-! ## Naturality of the scheme over a hash -/

namespace Over

variable (hash : HashInput → m HashOutput)

theorem mmap_th (P : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    F (Over.th hash P fields payload) = Over.th (fun x ↦ F (hash x)) P fields payload := by
  simp only [Over.th, F.mmap_bind, F.mmap_pure]

theorem mmap_tweakableHash (P : PublicParameter) (d : HashDomain) (payload : HashInput) :
    F (Over.tweakableHash hash P d payload) =
      Over.tweakableHash (fun x ↦ F (hash x)) P d payload :=
  mmap_th F hash P _ payload

theorem mmap_chainWalk (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (start steps : ℕ) (v : Digest) :
    F (Over.chainWalk hash P l e i start steps v) =
      Over.chainWalk (fun x ↦ F (hash x)) P l e i start steps v := by
  simp only [Over.chainWalk, mmap_walkChain, mmap_tweakableHash]

theorem mmap_recoverChain (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (digit : WinternitzDigit) (v : Digest) :
    F (Over.recoverChain hash P l e i digit v) =
      Over.recoverChain (fun x ↦ F (hash x)) P l e i digit v :=
  mmap_chainWalk F hash P l e i _ _ v

theorem mmap_leafHash (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (ends : ChainIndex → Digest) :
    F (Over.leafHash hash P l e ends) = Over.leafHash (fun x ↦ F (hash x)) P l e ends :=
  mmap_th F hash P _ _

theorem mmap_messageDigest (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : HashInput)
    (ρ : Randomizer) :
    F (Over.messageDigest hash P l e M ρ) = Over.messageDigest (fun x ↦ F (hash x)) P l e M ρ :=
  mmap_th F hash P _ _

theorem mmap_otsLeaf (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : HashInput)
    (ρ : Randomizer) (values : ChainIndex → Digest) :
    F (Over.otsLeaf hash P l e M ρ values) =
      Over.otsLeaf (fun x ↦ F (hash x)) P l e M ρ values := by
  simp only [Over.otsLeaf, F.mmap_bind, mmap_messageDigest]
  congr 1
  funext d
  cases Codeword.decode d with
  | none => simp only [F.mmap_pure]
  | some x =>
    simp only [F.mmap_bind, F.mmap_pure, mmap_sequenceFin, mmap_recoverChain, mmap_leafHash]

theorem mmap_treeFold (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (path : Fin layerHeight → Digest) (k : ℕ) (v : Digest) :
    F (Over.treeFold hash P l e path k v) = Over.treeFold (fun x ↦ F (hash x)) P l e path k v := by
  simp only [Over.treeFold, mmap_foldPath, mmap_tweakableHash]

theorem mmap_layerRoot (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : HashInput)
    (σ : LayerSignature) :
    F (Over.layerRoot hash P l e M σ) = Over.layerRoot (fun x ↦ F (hash x)) P l e M σ := by
  simp only [Over.layerRoot, F.mmap_bind, mmap_otsLeaf]
  congr 1
  funext r
  cases r with
  | none => simp only [F.mmap_pure]
  | some v => simp only [F.mmap_bind, F.mmap_pure, mmap_treeFold]

theorem mmap_verify (pk : PublicKey) (msg : Message) (σ : Signature) :
    F (Over.verify hash pk msg σ) = Over.verify (fun x ↦ F (hash x)) pk msg σ := by
  simp only [Over.verify, F.mmap_bind, mmap_layerRoot]
  congr 1
  funext r
  cases r with
  | none => simp only [F.mmap_pure]
  | some b =>
    simp only [F.mmap_bind, mmap_layerRoot]
    congr 1
    funext r'
    cases r' <;> simp only [F.mmap_pure]

theorem mmap_otsSecrets (P : PublicParameter) (l : Layer) (e : KeyIndex) (S : MasterSeed) :
    F (Over.otsSecrets hash P l e S) = Over.otsSecrets (fun x ↦ F (hash x)) P l e S := by
  simp only [Over.otsSecrets, Over.thPair, F.mmap_bind, F.mmap_pure, mmap_sequenceFin]

theorem mmap_oneTimePublicKey (P : PublicParameter) (l : Layer) (e : KeyIndex) (S : MasterSeed) :
    F (Over.oneTimePublicKey hash P l e S) =
      Over.oneTimePublicKey (fun x ↦ F (hash x)) P l e S := by
  simp only [Over.oneTimePublicKey, F.mmap_bind, mmap_otsSecrets, mmap_sequenceFin,
    mmap_chainWalk]

theorem mmap_otsSignFrom (P : PublicParameter) (l : Layer) (e : KeyIndex) (S : MasterSeed)
    (M : HashInput) (r0 : Randomizer) : ∀ (k t : ℕ),
    F (Over.otsSignFrom hash P l e S M r0 k t) =
      Over.otsSignFrom (fun x ↦ F (hash x)) P l e S M r0 k t
  | 0, _ => by simp only [Over.otsSignFrom, F.mmap_pure]
  | k + 1, t => by
    simp only [Over.otsSignFrom, F.mmap_bind, mmap_messageDigest]
    congr 1
    funext d
    cases Codeword.decode d with
    | none => exact mmap_otsSignFrom P l e S M r0 k (t + 1)
    | some x =>
      simp only [F.mmap_bind, F.mmap_pure, mmap_otsSecrets, mmap_sequenceFin, mmap_chainWalk]

theorem mmap_otsSign (P : PublicParameter) (l : Layer) (e : KeyIndex) (S : MasterSeed)
    (M : HashInput) :
    F (Over.otsSign hash P l e S M) = Over.otsSign (fun x ↦ F (hash x)) P l e S M := by
  simp only [Over.otsSign, F.mmap_bind, mmap_th, mmap_otsSignFrom]

theorem mmap_treeNode (P : PublicParameter) (l : Layer) (S : MasterSeed) (k j : ℕ) :
    F (Over.treeNode hash P l S k j) = Over.treeNode (fun x ↦ F (hash x)) P l S k j := by
  simp only [Over.treeNode, mmap_buildTree, F.mmap_bind, mmap_leafHash, mmap_oneTimePublicKey,
    mmap_tweakableHash]

theorem mmap_treePath (P : PublicParameter) (l : Layer) (S : MasterSeed) (e : KeyIndex) :
    F (Over.treePath hash P l S e) = Over.treePath (fun x ↦ F (hash x)) P l S e := by
  simp only [Over.treePath, mmap_sequenceFin, mmap_treeNode]

theorem mmap_schemeSeedOf (S0 : MasterSeed) :
    F (Over.schemeSeedOf hash S0) = Over.schemeSeedOf (fun x ↦ F (hash x)) S0 :=
  rfl

theorem mmap_publicParameterOf (S : MasterSeed) :
    F (Over.publicParameterOf hash S) = Over.publicParameterOf (fun x ↦ F (hash x)) S :=
  mmap_th F hash 0 _ _

theorem mmap_keygenFromSeed (S0 : MasterSeed) :
    F (Over.keygenFromSeed hash S0) = Over.keygenFromSeed (fun x ↦ F (hash x)) S0 := by
  simp only [Over.keygenFromSeed, F.mmap_bind, F.mmap_pure, mmap_schemeSeedOf,
    mmap_publicParameterOf, mmap_treeNode]

theorem mmap_signLayer (S : MasterSeed) (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (M : HashInput) :
    F (Over.signLayer hash S P l e M) = Over.signLayer (fun x ↦ F (hash x)) S P l e M := by
  simp only [Over.signLayer, F.mmap_bind, mmap_otsSign]
  congr 1
  funext r
  rcases r with _ | ⟨ρ, values⟩
  · simp only [F.mmap_pure]
  · simp only [F.mmap_bind, F.mmap_pure, mmap_treePath]

theorem mmap_signWithSchemeSeed (S : MasterSeed) (P : PublicParameter) (idx : LeafIndex)
    (msg : Message) :
    F (Over.signWithSchemeSeed hash S P idx msg) =
      Over.signWithSchemeSeed (fun x ↦ F (hash x)) S P idx msg := by
  simp only [Over.signWithSchemeSeed, F.mmap_bind, mmap_signLayer]
  congr 1
  funext r
  cases r with
  | none => simp only [F.mmap_pure]
  | some b =>
    simp only [F.mmap_bind, mmap_treeNode, mmap_signLayer]
    congr 1
    funext root
    congr 1
    funext r'
    cases r' <;> simp only [F.mmap_pure]

theorem mmap_sign (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    F (Over.sign hash sk idx msg) = Over.sign (fun x ↦ F (hash x)) sk idx msg := by
  simp only [Over.sign, Over.schemeSeedOf, F.mmap_bind, mmap_signWithSchemeSeed]

end Over

/-! ## Naturality of grinding and of the abstract signer -/

theorem mmap_grind (hash : HashInput → m HashOutput) (P : PublicParameter) (l : Layer)
    (e : KeyIndex) (M : HashInput) (r0 : Randomizer) : ∀ (k t : ℕ),
    F (grind hash P l e M r0 k t) = grind (fun x ↦ F (hash x)) P l e M r0 k t
  | 0, _ => by simp only [grind, F.mmap_pure]
  | k + 1, t => by
    simp only [grind, F.mmap_bind, Over.mmap_messageDigest, F.mmap_ite, F.mmap_pure,
      mmap_grind hash P l e M r0 k (t + 1)]

namespace Gen

variable (o : Ops m)

theorem mmap_otsPublicKey (l : Layer) (e : KeyIndex) :
    F (otsPublicKey o l e) = otsPublicKey (o.map F) l e := by
  simp only [otsPublicKey, mmap_sequenceFin, Ops.map_chain]

theorem mmap_keyLeaf (l : Layer) (e : KeyIndex) :
    F (keyLeaf o l e) = keyLeaf (o.map F) l e := by
  simp only [keyLeaf, F.mmap_bind, mmap_otsPublicKey, Ops.map_leaf]

theorem mmap_treeNode (l : Layer) : ∀ (k j : ℕ),
    F (treeNode o l k j) = treeNode (o.map F) l k j
  | 0, j => by simp only [treeNode, mmap_keyLeaf]
  | k + 1, j => by simp only [treeNode, F.mmap_bind, mmap_treeNode l k, Ops.map_node]

theorem mmap_treePath (l : Layer) (e : KeyIndex) :
    F (treePath o l e) = treePath (o.map F) l e := by
  simp only [treePath, mmap_sequenceFin, mmap_treeNode]

theorem mmap_root : F (root o) = root (o.map F) :=
  mmap_treeNode F o topLayer layerHeight 0

theorem mmap_signLayer (e : KeyIndex) (msg : LayerMsg) :
    F (signLayer o e msg) = signLayer (o.map F) e msg := by
  simp only [signLayer, F.mmap_bind, Ops.map_encode]
  congr 1
  funext r
  rcases r with _ | ⟨ρ, d⟩
  · simp only [F.mmap_pure]
  · dsimp only
    cases Codeword.decode d with
    | none => simp only [F.mmap_pure]
    | some x =>
      simp only [F.mmap_bind, F.mmap_pure, mmap_sequenceFin, Ops.map_chain, mmap_treePath]

theorem mmap_sign (idx : LeafIndex) (msg : Message) :
    F (sign o idx msg) = sign (o.map F) idx msg := by
  simp only [sign, F.mmap_bind, mmap_signLayer]
  congr 1
  funext r
  cases r with
  | none => simp only [F.mmap_pure]
  | some b =>
    simp only [F.mmap_bind, mmap_treeNode, mmap_signLayer]
    congr 1
    funext root
    congr 1
    funext r'
    cases r' <;> simp only [F.mmap_pure]

end Gen

end Natural

/-! ## Pure evaluation -/

section Pure

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad n] (F : m →ᵐ n)

namespace Over

variable (hash : HashInput → m HashOutput) (h : HashInput → HashOutput)

/-- A morphism answering each hash purely sends the hash to the pure hash. -/
theorem comp_eq_pure (hF : ∀ x, F (hash x) = pure (h x)) :
    (fun x ↦ F (hash x)) = fun x ↦ MonadHom.pure n (h x) :=
  funext hF

theorem mmap_keygenFromSeed_of_pure (hF : ∀ x, F (hash x) = pure (h x)) (S0 : MasterSeed) :
    F (Over.keygenFromSeed hash S0) = pure (Over.keygenFromSeed (m := Id) h S0) := by
  rw [mmap_keygenFromSeed, comp_eq_pure F hash h hF, ← mmap_keygenFromSeed]
  rfl

theorem mmap_sign_of_pure (hF : ∀ x, F (hash x) = pure (h x)) (sk : SecretKey) (idx : LeafIndex)
    (msg : Message) :
    F (Over.sign hash sk idx msg) = pure (Over.sign (m := Id) h sk idx msg) := by
  rw [mmap_sign, comp_eq_pure F hash h hF, ← mmap_sign]
  rfl

theorem mmap_verify_of_pure (hF : ∀ x, F (hash x) = pure (h x)) (pk : PublicKey) (msg : Message)
    (σ : Signature) :
    F (Over.verify hash pk msg σ) = pure (Over.verify (m := Id) h pk msg σ) := by
  rw [mmap_verify, comp_eq_pure F hash h hF, ← mmap_verify]
  rfl

end Over

namespace Gen

variable (o : Ops m) (o' : Ops Id)

/-- Operations answered purely by `o'` through `F`. -/
theorem map_eq_pure (hc : ∀ l e i μ, F (o.chain l e i μ) = pure (o'.chain l e i μ))
    (hl : ∀ l e ends, F (o.leaf l e ends) = pure (o'.leaf l e ends))
    (hn : ∀ l k j a b, F (o.node l k j a b) = pure (o'.node l k j a b))
    (he : ∀ e msg, F (o.encode e msg) = pure (o'.encode e msg)) :
    o.map F = o'.map (MonadHom.pure n) := by
  unfold Ops.map
  congr 1
  · funext l e i μ
    exact hc l e i μ
  · funext l e ends
    exact hl l e ends
  · funext l k j a b
    exact hn l k j a b
  · funext e msg
    exact he e msg

theorem mmap_treeNode_of_map (ho : o.map F = o'.map (MonadHom.pure n)) (l : Layer) (k j : ℕ) :
    F (treeNode o l k j) = pure (treeNode o' l k j) := by
  rw [mmap_treeNode, ho, ← mmap_treeNode]
  rfl

theorem mmap_root_of_map (ho : o.map F = o'.map (MonadHom.pure n)) :
    F (root o) = pure (root o') :=
  mmap_treeNode_of_map F o o' ho topLayer layerHeight 0

theorem mmap_sign_of_map (ho : o.map F = o'.map (MonadHom.pure n)) (idx : LeafIndex)
    (msg : Message) :
    F (sign o idx msg) = pure (sign o' idx msg) := by
  rw [mmap_sign, ho, ← mmap_sign]
  rfl

end Gen

end Pure

/-! ## Fixed tables -/

section Simulate

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {r : Type → Type} [Monad r] [LawfulMonad r]
  (impl : QueryImpl spec r) (o : Ops (OracleComp spec)) (o' : Ops Id)
  (hc : ∀ l e i μ, simulateQ impl (o.chain l e i μ) = pure (o'.chain l e i μ))
  (hl : ∀ l e ends, simulateQ impl (o.leaf l e ends) = pure (o'.leaf l e ends))
  (hn : ∀ l k j a b, simulateQ impl (o.node l k j a b) = pure (o'.node l k j a b))
  (he : ∀ e msg, simulateQ impl (o.encode e msg) = pure (o'.encode e msg))
include hc hl hn he

theorem Gen.simulateQ_map :
    o.map (simulateQ' impl) = o'.map (MonadHom.pure r) :=
  Gen.map_eq_pure (simulateQ' impl) o o' hc hl hn he

theorem Gen.simulateQ_treeNode (l : Layer) (k j : ℕ) :
    simulateQ impl (Gen.treeNode o l k j) = pure (Gen.treeNode o' l k j) := by
  have := Gen.mmap_treeNode_of_map (simulateQ' impl) o o' (Gen.simulateQ_map impl o o' hc hl hn he)
    l k j
  rwa [simulateQ'_apply] at this

theorem Gen.simulateQ_root :
    simulateQ impl (Gen.root o) = pure (Gen.root o') := by
  have := Gen.mmap_root_of_map (simulateQ' impl) o o' (Gen.simulateQ_map impl o o' hc hl hn he)
  rwa [simulateQ'_apply] at this

theorem Gen.simulateQ_sign (idx : LeafIndex) (msg : Message) :
    simulateQ impl (Gen.sign o idx msg) = pure (Gen.sign o' idx msg) := by
  have := Gen.mmap_sign_of_map (simulateQ' impl) o o' (Gen.simulateQ_map impl o o' hc hl hn he)
    idx msg
  rwa [simulateQ'_apply] at this

end Simulate

section World

variable (W : OracleWorld) (tab : W.Tab)

theorem simulateQ_xmssOver_generateKeys (S0 : MasterSeed) :
    simulateQ (W.eager tab) ((xmssOver W.hash).generateKeys S0) =
      pure (Over.keygenFromSeed (m := Id) (W.hashOf tab) S0) :=
  Over.mmap_keygenFromSeed_of_pure (simulateQ' (W.eager tab)) W.hash (W.hashOf tab)
    (W.simulateQ_hash tab) S0

theorem simulateQ_xmssOver_sign (sk : SecretKey) (req : SigningRequest) :
    simulateQ (W.eager tab) ((xmssOver W.hash).sign sk req) =
      pure (Over.sign (m := Id) (W.hashOf tab) sk req.leafIndex req.message) :=
  Over.mmap_sign_of_pure (simulateQ' (W.eager tab)) W.hash (W.hashOf tab) (W.simulateQ_hash tab)
    sk req.leafIndex req.message

theorem simulateQ_xmssOver_verify (pk : PublicKey) (F : Forgery) :
    simulateQ (W.eager tab) ((xmssOver W.hash).verify pk F) =
      pure (Over.verify (m := Id) (W.hashOf tab) pk F.message F.signature) :=
  Over.mmap_verify_of_pure (simulateQ' (W.eager tab)) W.hash (W.hashOf tab)
    (W.simulateQ_hash tab) pk F.message F.signature

end World

/-! ## The real operations -/

/-- **The real operations** of the scheme seed `S` and the parameter `P` at the hash `h`: chains
from the seed-derived starts, the leaf and node hashes, grinding from the seed-derived randomizer
base. -/
def realOps (h : HashInput → HashOutput) (S : MasterSeed) (P : PublicParameter) : Ops Id where
  chain l e i μ := Over.chainWalk (m := Id) h P l e i 0 μ
    (hashHalfForChain i.val
      (h (thInput P (keygenDomainFields (.oneTimeChainPair l e (chainPair i)))
        (littleEndianBytes 32 S))))
  leaf l e ends := Over.leafHash (m := Id) h P l e ends
  node l k j a b := Over.tweakableHash (m := Id) h P (.node l (k + 1) j) (nodePayload a b)
  encode e msg := grind (m := Id) h P msg.layer e msg.bytes
    (truncateHash (h (thInput P (tweakFields 7 0 (layerHi msg.layer 0) e)
      (littleEndianBytes 32 S ++ msg.bytes))))
    randomizerAttemptLimit 0

section Real

variable (h : HashInput → HashOutput)

theorem bind_run {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x.run :=
  rfl

theorem sequenceFin_pure {α : Type} {k : ℕ} (c : Fin k → Id α) :
    sequenceFin c = pure fun i ↦ (c i).run := by
  induction k with
  | zero =>
    rw [sequenceFin]
    exact congrArg pure (funext fun i ↦ i.elim0)
  | succ k ih =>
    rw [sequenceFin, ih]
    simp only [bind_run, Id.run_pure]
    refine congrArg pure (funext fun i ↦ ?_)
    cases i using Fin.cases <;> simp only [Fin.cases_zero, Fin.cases_succ]

theorem th_id (P : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    Over.th (m := Id) h P fields payload = truncateHash (h (thInput P fields payload)) :=
  rfl

theorem oneTimePublicKey_id (S : MasterSeed) (P : PublicParameter) (l : Layer) (e : KeyIndex) :
    Over.oneTimePublicKey (m := Id) h P l e S = Gen.otsPublicKey (realOps h S P) l e := by
  simp only [Over.oneTimePublicKey, Over.otsSecrets, Gen.otsPublicKey, sequenceFin_pure, bind_run]
  rfl

theorem treeNode_id (S : MasterSeed) (P : PublicParameter) (l : Layer) : ∀ (k j : ℕ),
    Over.treeNode (m := Id) h P l S k j = Gen.treeNode (realOps h S P) l k j
  | 0, j => by
    rw [Gen.treeNode, Gen.keyLeaf, ← oneTimePublicKey_id]
    rfl
  | k + 1, j => by
    rw [Gen.treeNode, ← treeNode_id S P l k, ← treeNode_id S P l k]
    rfl

theorem treePath_id (S : MasterSeed) (P : PublicParameter) (l : Layer) (e : KeyIndex) :
    Over.treePath (m := Id) h P l S e = Gen.treePath (realOps h S P) l e := by
  simp only [Over.treePath, Gen.treePath, treeNode_id]

/-- Trying randomizers until a codeword, then opening the chains, is grinding, then decoding,
then opening the chains of the real operations. -/
theorem otsSignFrom_id (S : MasterSeed) (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (M : HashInput) (r0 : Randomizer) : ∀ (k t : ℕ),
    (Over.otsSignFrom (m := Id) h P l e S M r0 k t).run =
      (grind (m := Id) h P l e M r0 k t).run.bind fun p ↦ (Codeword.decode p.2).map fun x ↦
        (p.1, fun i ↦ ((realOps h S P).chain l e i (x i).val).run)
  | 0, _ => rfl
  | k + 1, t => by
    simp only [Over.otsSignFrom, grind, bind_run]
    split
    next x hd =>
      simp only [hd, Option.isSome_some, ite_true, Id.run_pure, Option.bind_some,
        Option.map_some, Over.otsSecrets, sequenceFin_pure, bind_run]
      rfl
    next hd =>
      simp only [hd, Option.isSome_none, Bool.false_eq_true, ite_false]
      exact otsSignFrom_id S P l e M r0 k (t + 1)

theorem otsSign_id (S : MasterSeed) (P : PublicParameter) (e : KeyIndex) (msg : LayerMsg) :
    (Over.otsSign (m := Id) h P msg.layer e S msg.bytes).run =
      ((realOps h S P).encode e msg).run.bind fun p ↦ (Codeword.decode p.2).map fun x ↦
        (p.1, fun i ↦ ((realOps h S P).chain msg.layer e i (x i).val).run) := by
  simp only [Over.otsSign, th_id, bind_run]
  exact otsSignFrom_id h S P msg.layer e msg.bytes _ randomizerAttemptLimit 0

theorem signLayer_id (S : MasterSeed) (P : PublicParameter) (e : KeyIndex) (msg : LayerMsg) :
    Over.signLayer (m := Id) h S P msg.layer e msg.bytes = Gen.signLayer (realOps h S P) e msg := by
  apply Id.ext
  have hl : (Over.signLayer (m := Id) h S P msg.layer e msg.bytes).run =
      (Over.otsSign (m := Id) h P msg.layer e S msg.bytes).run.map fun p ↦
        (⟨p.1, p.2, (Over.treePath (m := Id) h P msg.layer S e).run⟩ : LayerSignature) := by
    simp only [Over.signLayer, bind_run]
    rcases (Over.otsSign (m := Id) h P msg.layer e S msg.bytes).run with _ | ⟨ρ, values⟩ <;> rfl
  have hr : (Gen.signLayer (realOps h S P) e msg).run =
      ((realOps h S P).encode e msg).run.bind fun p ↦ (Codeword.decode p.2).map fun x ↦
        (⟨p.1, fun i ↦ ((realOps h S P).chain msg.layer e i (x i).val).run,
          (Gen.treePath (realOps h S P) msg.layer e).run⟩ : LayerSignature) := by
    simp only [Gen.signLayer, bind_run, sequenceFin_pure]
    rcases ((realOps h S P).encode e msg).run with _ | ⟨ρ, d⟩
    · rfl
    · simp only [Option.bind_some]
      cases Codeword.decode d <;> rfl
  rw [hl, hr, otsSign_id, treePath_id]
  rcases ((realOps h S P).encode e msg).run with _ | ⟨ρ, d⟩
  · rfl
  · simp only [Option.bind_some]
    cases Codeword.decode d <;> rfl

/-- Key generation from the scheme seed `S` and the parameter `P` it derives: the root of the top
tree. -/
theorem keygenFromSeed_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (hash : HashInput → m HashOutput) (S0 S : MasterSeed) (P : PublicParameter)
    (hS : Over.schemeSeedOf hash S0 = pure S) (hP : Over.publicParameterOf hash S = pure P) :
    Over.keygenFromSeed hash S0 =
      (fun R ↦ ((⟨R, P⟩ : PublicKey), (⟨S0, P⟩ : SecretKey))) <$>
        Over.treeNode hash P topLayer S layerHeight 0 := by
  simp only [Over.keygenFromSeed, hS, hP, pure_bind, bind_pure_comp]

/-- **Key generation** over a pure hash: the root of the top tree of the real operations. -/
theorem keygenFromSeed_id (S0 : MasterSeed) :
    let S : MasterSeed := h (seedTag ++ littleEndianBytes 32 S0)
    let P : PublicParameter :=
      truncateHash (h (thInput 0 (keygenDomainFields .parameter) (littleEndianBytes 32 S)))
    (Over.keygenFromSeed (m := Id) h S0).run =
      (⟨(Gen.root (realOps h S P)).run, P⟩, ⟨S0, P⟩) := by
  intro S P
  rw [keygenFromSeed_eq (m := Id) h S0 S P rfl rfl, Id.run_map, treeNode_id]
  rfl

/-- The signer at a scheme seed is the abstract signer over operations with the same layer
signatures and tree nodes. -/
theorem signWithSchemeSeed_eq_sign {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput)
    (S : MasterSeed) (P : PublicParameter) (o : Ops m)
    (hs : ∀ e msg, Over.signLayer hash S P msg.layer e msg.bytes = Gen.signLayer o e msg)
    (ht : ∀ l k j, Over.treeNode hash P l S k j = Gen.treeNode o l k j) (idx : LeafIndex)
    (msg : Message) :
    Over.signWithSchemeSeed hash S P idx msg = Gen.sign o idx msg := by
  simp only [Gen.sign, ← hs, ← ht, LayerMsg.layer, LayerMsg.bytes]
  rfl

/-- **Signing** over a pure hash: the abstract signer over the real operations. -/
theorem sign_id (S0 : MasterSeed) (P : PublicParameter) (idx : LeafIndex) (msg : Message) :
    Over.sign (m := Id) h ⟨S0, P⟩ idx msg =
      Gen.sign (realOps h (h (seedTag ++ littleEndianBytes 32 S0)) P) idx msg := by
  have key := signWithSchemeSeed_eq_sign (m := Id) h (h (seedTag ++ littleEndianBytes 32 S0)) P _
    (signLayer_id h _ P) (fun l ↦ treeNode_id h _ P l) idx msg
  rw [Over.sign, bind_run]
  exact key

end Real

end Quantum.StdModel.Xmss

end
