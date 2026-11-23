module

public import Quantum.StdModel.Xmss.Ideal
public import Quantum.StdModel.Xmss.Inst
public import Quantum.StdModel.Xmss.Eval
public import Quantum.StdModel.Xmss.PrfInst

@[expose] public section

/-!
# B4: the SM-TCR-C reduction of leanXMSS

`tcrRed W A` plays SM-TCR-C (`smTcr W xmssTcrC xmssTcrD`: targets of the leaf compression and the
node hash, evaluations of the chain step) with the SUF-CMA adversary `A`:

* setup (`tcrPre`): sample the chain starts `c` and the randomizer bases `g`; before the reveal,
  compute every leaf of every key of both layers and every node of the bottom trees and the top
  tree, chain steps by `eval` queries, leaves and nodes by `target` queries (`preAll`, each tweak
  once since the tree recursion visits each position once), keeping the transcript; then `reveal`
  the parameter `P`; the public key is the top root and `P`;
* handler (`tcrSigner`): the abstract signer over `signOps`, which read leaves and nodes from the
  recorded targets and compute chains and grinding honestly;
* output (`tcrPost`): the first candidate of the forgery (the leaf input and the node inputs along
  the path, on both layers) that collides with a recorded target.

`idealProb_tcr_le`: at every table of a world with fair coins, the SM-TCR-C event of the ideal
game is at most the success of `tcrRed W A`. At a fixed table the precomputation is deterministic
and its transcript is honest, complete and valid (`tcrDet_preAll`, `tcrValid_of_allQ`), so the
handler signs as the ideal signer (`hKernel_tcrSigner`) and the event yields a colliding
candidate (`tcrDecB_of_tcrDec`). `isChargeBound_tcrRed`: its hash calls.
-/

open IPFunctor OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal
open Quantum.Xmss (Slot)

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props Common

/-! ## The ports and the reduction -/

/-- The SM-TCR-C ports of the leanXMSS instance. -/
abbrev TcrPorts :=
  TcrSpec PublicParameter XTw TcrFn TcrMsg Digest Unit (fun _ ↦ Digest) Digest

/-- A classical query of the SM-TCR-C ports. -/
abbrev TcrQ := TcrQuery XTw TcrFn TcrMsg Unit (fun _ ↦ Digest)

/-- An output of the SM-TCR-C game: a target function, a tweak and a message. -/
abbrev TcrOut := Σ f : TcrFn, XTw × TcrMsg f

/-- The tweak of the leaf of key `(l, e)`. -/
abbrev leafTw (l : Layer) (e : KeyIndex) : XTw :=
  ⟨.leaf l e, trivial⟩

/-- The tweak of step `s` of chain `i` of key `(l, e)`. -/
abbrev chainTw (l : Layer) (e : KeyIndex) (s : ChainStep) (i : ChainIndex) : XTw :=
  ⟨.chain l e s i, trivial⟩

/-- The tweak of the node at level `k + 1`, index `j`, of layer `l`. -/
abbrev nodeTw (l : Layer) (k j : ℕ) (h : k < layerHeight ∧ j < 2 ^ 32) : XTw :=
  ⟨.node l (k + 1) j, addressable_node l h.1 h.2⟩

theorem keyIndex_lt (e : KeyIndex) : e.val < 2 ^ 32 :=
  e.isLt

/-- The tweak of the node at level `k + 1` above key `e`. -/
def nodeTwOf (l : Layer) (e : KeyIndex) (k : Fin layerHeight) : XTw :=
  nodeTw l k.val (e.val / 2 ^ (k.val + 1))
    ⟨k.isLt, lt_of_le_of_lt (Nat.div_le_self _ _) (keyIndex_lt e)⟩

variable (W : OracleWorld)

/-- A call of the SM-TCR-C port `q`. -/
def tcrCall (q : TcrQ) : OracleComp (W.Oracles + TcrPorts) (TcrPorts.Range q) :=
  liftM ((W.Oracles + TcrPorts).query (.inr q))

/-- A program over the world's oracles as a program of the reduction. -/
def tcrLift {α : Type} (oa : OracleComp W.Oracles α) : OracleComp (W.Oracles + TcrPorts) α :=
  simulateQ (fun t ↦ liftM ((W.Oracles + TcrPorts).query (.inl t))) oa

/-- Keccak-256 of the world, as a call of the reduction. -/
def tcrHash (x : HashInput) : OracleComp (W.Oracles + TcrPorts) HashOutput :=
  tcrLift W (W.hash x)

/-- The coins of the reduction: the chain starts and the randomizer bases. -/
abbrev TcrCoins :=
  (Layer → KeyIndex → ChainIndex → Digest) × (KeyIndex × LayerMsg → Randomizer)

/-- **The precomputation's operations**: chain steps by evaluation queries, leaves and nodes by
target queries at their slots. -/
def preOps (c : Layer → KeyIndex → ChainIndex → Digest) :
    Ops (OracleComp (W.Oracles + TcrPorts)) where
  chain l e i μ := walkChain (fun s x ↦ tcrCall W (.eval () (chainTw l e s i) x)) 0 μ (c l e i)
  leaf l e ends := tcrCall W (.target .leaf (leafTw l e) ends)
  node l k j a b :=
    if h : k < layerHeight ∧ j < 2 ^ 32 then tcrCall W (.target .node (nodeTw l k j h) (a, b))
    else pure 0
  encode _ _ := pure none

/-- The first `n` bottom trees. -/
def preTrees {m : Type → Type} [Monad m] (o : Ops m) : ℕ → m Unit
  | 0 => pure ()
  | n + 1 => do
    preTrees o n
    let _ ← Gen.treeNode o bottomLayer layerHeight n
    pure ()

/-- **The precomputation**: the top tree, then every bottom tree; the top root. -/
def preAll {m : Type → Type} [Monad m] (o : Ops m) : m Digest := do
  let root ← Gen.root o
  preTrees o (2 ^ layerHeight)
  pure root

/-- The reduction's oracles with its own transcript of the SM-TCR-C ports. -/
def recImpl :
    QueryImpl (W.Oracles + TcrPorts)
      (StateT (QueryLog TcrPorts) (OracleComp (W.Oracles + TcrPorts)))
  | .inl t => liftM (liftM ((W.Oracles + TcrPorts).query (.inl t)) :
      OracleComp (W.Oracles + TcrPorts) _)
  | .inr q => fun log ↦ (fun a ↦ (a, log ++ [⟨q, a⟩])) <$> tcrCall W q

/-- The reduction's data after its setup. -/
structure TcrData where
  /-- The chain starts. -/
  c : Layer → KeyIndex → ChainIndex → Digest
  /-- The randomizer bases. -/
  g : KeyIndex × LayerMsg → Randomizer
  /-- The revealed parameter. -/
  P : PublicParameter
  /-- The top root. -/
  root : Digest
  /-- The transcript of the precomputation. -/
  log : QueryLog TcrPorts

/-- **The setup of B4**: coins, the precomputation with its transcript, then the reveal. -/
noncomputable def tcrPre : OracleComp (W.Oracles + TcrPorts) TcrData := do
  let cg ← tcrLift W (sample W TcrCoins)
  let r ← (simulateQ (recImpl W) (preAll (preOps W cg.1))).run []
  let P ← tcrCall W .reveal
  pure ⟨cg.1, cg.2, P, r.1, r.2⟩

/-- The position of a leaf or node slot: its layer, level and index. -/
def slotPos : Slot → Option (Layer × ℕ × ℕ)
  | .leaf l e => some (l, 0, e.val)
  | .node l k j => some (l, k, j)
  | _ => none

/-- The position of a target. -/
def tgtPos (e : TcrOut × Digest) : Option (Layer × ℕ × ℕ) :=
  slotPos e.1.2.1.1

/-- The answer to the first recorded target at the position `(l, k, j)`. -/
def tcrLookup (L : QueryLog TcrPorts) (l : Layer) (k j : ℕ) : Digest :=
  (((tcrTargets L).find? fun e ↦ tgtPos e = some (l, k, j)).map Prod.snd).getD 0

/-- **The signing operations of B4**: chains and grinding honestly, leaves and nodes read from the
recorded targets. -/
def signOps (d : TcrData) : Ops (OracleComp (W.Oracles + TcrPorts)) where
  chain l e i μ := Qrom.Xmss.Over.chainWalk (tcrHash W) d.P l e i 0 μ (d.c l e i)
  leaf l e _ := pure (tcrLookup d.log l 0 e.val)
  node l k j _ _ := pure (tcrLookup d.log l (k + 1) j)
  encode e M := grind (tcrHash W) d.P M.layer e M.bytes (d.g (e, M)) randomizerAttemptLimit 0

/-- The handler state of B4: its data and the signing transcript. -/
abbrev TcrSt := TcrData × QueryLog SigningOracleSpec

/-- **The handler of B4**: the abstract signer over `signOps`, logged. -/
def tcrSigner : HHandler W SigningOracleSpec TcrPorts TcrSt := fun s r ↦ do
  let sig ← Gen.sign (signOps W s.1) r.leafIndex r.message
  pure (sig, (s.1, s.2 ++ [⟨r, sig⟩]))

/-- The candidates of layer `l` with the forged message `M`: the forged leaf input, and the forged
inputs of the nodes along the path. -/
def layerCands {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput) (P : PublicParameter)
    (F : Forgery) (l : Layer) (M : LayerMsg) : m (List TcrOut) := do
  let d ← Qrom.Xmss.Over.messageDigest hash P l (forgedKey F l) M.bytes
    (F.signature.layers l).randomizer
  (Codeword.decode d).elim (pure []) fun x ↦ do
    let ends ← sequenceFin fun i ↦ Qrom.Xmss.Over.recoverChain hash P l (forgedKey F l) i (x i)
      ((F.signature.layers l).chainValues i)
    let leaf ← Qrom.Xmss.Over.leafHash hash P l (forgedKey F l) ends
    let folds ← sequenceFin fun k : Fin layerHeight ↦ Qrom.Xmss.Over.treeFold hash P l
      (forgedKey F l) (F.signature.layers l).authenticationPath k.val leaf
    pure (⟨.leaf, leafTw l (forgedKey F l), ends⟩ :: List.ofFn fun k ↦
      ⟨.node, nodeTwOf l (forgedKey F l) k, forgedKids F l k.val (folds k)⟩)

/-- The candidates of both layers. -/
def allCands {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput) (P : PublicParameter)
    (F : Forgery) : m (List TcrOut) := do
  let cb ← layerCands hash P F bottomLayer (.inl F.message)
  let r ← Qrom.Xmss.Over.layerRoot hash P bottomLayer (forgedKey F bottomLayer)
    (littleEndianBytes 32 F.message) (F.signature.layers bottomLayer)
  let ct ← r.elim (pure []) fun r ↦ layerCands hash P F topLayer (.inr r)
  pure (cb ++ ct)

/-- Each candidate with its digest. -/
def withDigests {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput)
    (P : PublicParameter) : List TcrOut → m (List (TcrOut × Digest))
  | [] => pure []
  | c :: cs => do
    let y ← hash (xmssTcrC.layout c.1 P c.2.1 c.2.2)
    let ys ← withDigests hash P cs
    pure ((c, truncateHash y) :: ys)

/-- The candidates with their digests. -/
def postCands {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput) (P : PublicParameter)
    (F : Forgery) : m (List (TcrOut × Digest)) := do
  let cands ← allCands hash P F
  withDigests hash P cands

/-- The output `out` with digest `y` collides with a target of the transcript `L`. -/
def TcrHit (L : QueryLog TcrPorts) (out : TcrOut) (y : Digest) : Prop :=
  ∃ e ∈ tcrTargets L, e.1.1 = out.1 ∧ e.1.2.1 = out.2.1 ∧ e.1 ≠ out ∧ e.2 = y

/-- The output when no candidate collides. -/
def tcrDefault : TcrOut :=
  ⟨.leaf, leafTw bottomLayer ⟨0, by decide⟩, fun _ ↦ 0⟩

/-- The first candidate that collides with a target of `L`. -/
noncomputable def tcrPick (L : QueryLog TcrPorts) (cs : List (TcrOut × Digest)) : TcrOut :=
  ((cs.find? fun cy ↦ holds (TcrHit L cy.1 cy.2)).map Prod.fst).getD tcrDefault

/-- **The output of B4**: the first colliding candidate. -/
noncomputable def tcrPost (d : TcrData) (F : Forgery) (_ : TcrSt) :
    OracleComp (W.Oracles + TcrPorts) TcrOut :=
  tcrPick d.log <$> postCands (tcrHash W) d.P F

/-- **B4, the SM-TCR-C reduction**: the setup `tcrPre`, `A` on the top root and the revealed
parameter with its requests answered by `tcrSigner`, the output `tcrPost`. -/
noncomputable def tcrRed (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    Props.Adversary W TcrPorts Unit TcrOut :=
  fun _ ↦ slRed W (tcrPre W) (fun d ↦ A ⟨d.root, d.P⟩) (fun d ↦ (d, [])) (tcrSigner W)
    (tcrPost W)

/-- **The hash calls of B4**: `A`'s hash calls plus the honest work of its setup, of each signing
request and of its output. -/
theorem isChargeBound_tcrRed
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) {c₀ c₁ k n m : ℕ}
    (hpre : QueryCostAtMost (tcrPre W) (hcallCost W (R' := TcrPorts)) c₀)
    (hσ : ∀ s q, QueryCostAtMost (tcrSigner W s q) (hcallCost W (R' := TcrPorts)) k)
    (hpost : ∀ a f s, QueryCostAtMost (tcrPost W a f s) (hcallCost W (R' := TcrPorts)) c₁)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (tcrRed W A ()) (cmdCharge hashCharge) (c₀ + ((n + k * m) + c₁)) :=
  isChargeBound_slRed_hash W _ _ _ _ _ hpre hσ hpost (fun _ ↦ hn _) (fun _ ↦ hm _)

/-! ## Determinate runs against the challenger -/

section Det

/-- A transcript entry of the SM-TCR-C ports. -/
abbrev TcrEnt := (q : TcrQ) × TcrPorts.Range q

/-- `x`, run from any transcript, returns `v` and appends a transcript satisfying `Q`. -/
def TcrDet {α : Type} (x : StateT (QueryLog TcrPorts) ProbComp α) (v : α)
    (Q : QueryLog TcrPorts → Prop) : Prop :=
  ∀ s, ∃ T, x.run s = pure (v, s ++ T) ∧ Q T

variable {α β : Type}

theorem TcrDet.mono {x : StateT (QueryLog TcrPorts) ProbComp α} {v : α}
    {Q Q' : QueryLog TcrPorts → Prop} (h : TcrDet x v Q) (hQ : ∀ T, Q T → Q' T) :
    TcrDet x v Q' :=
  fun s ↦ (h s).imp fun _ hT ↦ ⟨hT.1, hQ _ hT.2⟩

theorem tcrDet_pure (v : α) :
    TcrDet (pure v : StateT (QueryLog TcrPorts) ProbComp α) v (· = []) :=
  fun s ↦ ⟨[], by rw [StateT.run_pure, List.append_nil], rfl⟩

theorem TcrDet.bind {x : StateT (QueryLog TcrPorts) ProbComp α}
    {f : α → StateT (QueryLog TcrPorts) ProbComp β} {v : α} {w : β}
    {Q₁ Q₂ : QueryLog TcrPorts → Prop} (hx : TcrDet x v Q₁) (hf : TcrDet (f v) w Q₂) :
    TcrDet (x >>= f) w fun T ↦ ∃ T₁ T₂, T = T₁ ++ T₂ ∧ Q₁ T₁ ∧ Q₂ T₂ := by
  intro s
  obtain ⟨T₁, h₁, q₁⟩ := hx s
  obtain ⟨T₂, h₂, q₂⟩ := hf (s ++ T₁)
  refine ⟨T₁ ++ T₂, ?_, T₁, T₂, rfl, q₁, q₂⟩
  rw [StateT.run_bind, h₁, pure_bind, h₂, List.append_assoc]

/-- Sequencing keeps a property of every entry. -/
theorem TcrDet.bind_all {R : TcrEnt → Prop} {x : StateT (QueryLog TcrPorts) ProbComp α}
    {f : α → StateT (QueryLog TcrPorts) ProbComp β} {v : α} {w : β}
    (hx : TcrDet x v fun T ↦ ∀ a ∈ T, R a) (hf : TcrDet (f v) w fun T ↦ ∀ a ∈ T, R a) :
    TcrDet (x >>= f) w fun T ↦ ∀ a ∈ T, R a :=
  (hx.bind hf).mono fun _ ⟨_, _, hT, h₁, h₂⟩ ↦ hT ▸ fun a ha ↦
    (List.mem_append.mp ha).elim (h₁ a) (h₂ a)

theorem tcrDet_pure_all {R : TcrEnt → Prop} (v : α) :
    TcrDet (pure v : StateT (QueryLog TcrPorts) ProbComp α) v fun T ↦ ∀ a ∈ T, R a :=
  (tcrDet_pure v).mono fun _ hT a ha ↦ by simp [hT] at ha

theorem tcrDet_sequenceFin {R : TcrEnt → Prop} :
    ∀ {n : ℕ} (c : Fin n → StateT (QueryLog TcrPorts) ProbComp α) (v : Fin n → α),
      (∀ i, TcrDet (c i) (v i) fun T ↦ ∀ a ∈ T, R a) →
        TcrDet (sequenceFin c) v fun T ↦ ∀ a ∈ T, R a
  | 0, c, v, _ => by
    rw [show v = Fin.elim0 from funext fun i ↦ i.elim0]
    exact tcrDet_pure_all _
  | n + 1, c, v, h => by
    refine (h 0).bind_all ((tcrDet_sequenceFin (fun i ↦ c i.succ) (fun i ↦ v i.succ)
      fun i ↦ h i.succ).bind_all ?_)
    have hv : (Fin.cases (v 0) fun i ↦ v i.succ : Fin (n + 1) → α) = v :=
      funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
    rw [hv]
    exact tcrDet_pure_all _

end Det

/-! ## The precomputation at a fixed table -/

section Table

variable (tab : W.Tab) (P : PublicParameter)

/-- The SM-TCR-C challenger of the parameter `P` at the table `tab`, with the transcript. -/
noncomputable abbrev tcrImpl :
    QueryImpl (W.Oracles + TcrPorts) (StateT (QueryLog TcrPorts) ProbComp) :=
  logImpl tab ((smTcr W xmssTcrC xmssTcrD).answer P)

theorem run_tcrCall (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q)) (q : TcrQ)
    (s : QueryLog TcrPorts) :
    (simulateQ (logImpl tab ans) (tcrCall W q)).run s =
      (fun a ↦ (a, s ++ [⟨q, a⟩])) <$> simulateQ (W.eager tab) (ans q) := by
  rw [tcrCall, simulateQ_spec_query]
  rfl

theorem simulateQ_tcrLift (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q))
    {α : Type} (oa : OracleComp W.Oracles α) :
    simulateQ (logImpl tab ans) (tcrLift W oa) = liftM (simulateQ (W.eager tab) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [tcrLift]
  | query_bind t k ih =>
    simp only [tcrLift, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    simp only [ih, liftM_bind]
    rfl

theorem simulateQ_tcrHash (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q))
    (x : HashInput) :
    simulateQ (logImpl tab ans) (tcrHash W x) = pure (W.hashOf tab x) := by
  rw [tcrHash, simulateQ_tcrLift, W.simulateQ_hash]
  simp

theorem simulateQ_tcrAnswer_target (f : TcrFn) (t : XTw) (m : TcrMsg f) :
    simulateQ (W.eager tab) ((smTcr W xmssTcrC xmssTcrD).answer P (.target f t m)) =
      pure (truncateHash (W.hashOf tab (xmssTcrC.layout f P t m))) :=
  simulateQ_eval W tab xmssTcrC f P t m

theorem simulateQ_tcrAnswer_eval (t : XTw) (x : Digest) :
    simulateQ (W.eager tab) ((smTcr W xmssTcrC xmssTcrD).answer P (.eval () t x)) =
      pure (truncateHash (W.hashOf tab (xmssTcrD.layout () P t x))) :=
  simulateQ_eval W tab xmssTcrD () P t x

/-- An evaluation at a chain slot. -/
def IsEval (a : TcrEnt) : Prop :=
  ∃ l e s i, TcrQuery.evalTweak a = some (chainTw l e s i)

theorem tcrDet_eval (l : Layer) (e : KeyIndex) (s : ChainStep) (i : ChainIndex) (x : Digest) :
    TcrDet (simulateQ (tcrImpl W tab P) (tcrCall W (.eval () (chainTw l e s i) x)))
      (Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P (.chain l e s)
        (Verification.chainPayload i x)) fun T ↦ ∀ a ∈ T, IsEval a := by
  intro s'
  refine ⟨[⟨.eval () (chainTw l e s i) x, Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P
    (.chain l e s) (Verification.chainPayload i x)⟩], ?_, ?_⟩
  · rw [run_tcrCall, simulateQ_tcrAnswer_eval]
    rfl
  · intro a ha
    rw [List.mem_singleton] at ha
    exact ha ▸ ⟨l, e, s, i, rfl⟩

theorem tcrDet_walk (l : Layer) (e : KeyIndex) (i : ChainIndex) :
    ∀ (n : ℕ) (v : Digest),
      TcrDet (walkChain (fun s x ↦ simulateQ (tcrImpl W tab P)
        (tcrCall W (.eval () (chainTw l e s i) x))) 0 n v)
        (Qrom.Xmss.Over.chainWalk (m := Id) (W.hashOf tab) P l e i 0 n v)
        fun T ↦ ∀ a ∈ T, IsEval a
  | 0, v => tcrDet_pure_all v
  | n + 1, v => by
    refine (tcrDet_walk l e i n v).bind_all ?_
    by_cases hn : 0 + n < chainLength - 1
    · rw [dite_eq_left hn]
      have hv' : Qrom.Xmss.Over.chainWalk (m := Id) (W.hashOf tab) P l e i 0 (n + 1) v =
          Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P (.chain l e ⟨0 + n, hn⟩)
            (Verification.chainPayload i
              (Qrom.Xmss.Over.chainWalk (m := Id) (W.hashOf tab) P l e i 0 n v)) := by
        rw [Qrom.Xmss.Over.chainWalk, walkChain_succ_id, dite_eq_left hn]
      rw [hv']
      exact tcrDet_eval W tab P l e _ i _
    · rw [dite_eq_right hn]
      have hv' : Qrom.Xmss.Over.chainWalk (m := Id) (W.hashOf tab) P l e i 0 (n + 1) v = 0 := by
        rw [Qrom.Xmss.Over.chainWalk, walkChain_succ_id, dite_eq_right hn]
        rfl
      rw [hv']
      exact tcrDet_pure_all _

/-- The honest targets at the operations `o`: a leaf with its chain ends, a node with its
children. -/
def TgtOK (o : Ops Id) (y : TcrOut × Digest) : Prop :=
  (∃ l e, y = (⟨.leaf, leafTw l e, Gen.otsPublicKey o l e⟩, Gen.keyLeaf o l e)) ∨
    ∃ l k j h, y = (⟨.node, nodeTw l k j h,
      (Gen.treeNode o l k (2 * j), Gen.treeNode o l k (2 * j + 1))⟩, Gen.treeNode o l (k + 1) j)

/-- An entry of the precomputation: an evaluation at a chain slot or an honest target. -/
def EntOK (o : Ops Id) (a : TcrEnt) : Prop :=
  IsEval a ∨ ∃ y, TcrQuery.asTarget a = some y ∧ TgtOK o y

/-- The position `p` lies in the subtree of the node at level `k`, index `j`, of layer `l`. -/
def InSub (l : Layer) (k j : ℕ) (p : Option (Layer × ℕ × ℕ)) : Prop :=
  ∃ k' j', p = some (l, k', j') ∧ k' ≤ k ∧ j' / 2 ^ (k - k') = j

/-- The transcript of the subtree at level `k`, index `j`, of layer `l`: honest entries, distinct
target positions inside the subtree, and a target at every position of the subtree. -/
def TreeQ (o : Ops Id) (l : Layer) (k j : ℕ) (T : QueryLog TcrPorts) : Prop :=
  (∀ a ∈ T, EntOK o a) ∧ ((tcrTargets T).map tgtPos).Nodup ∧
    (∀ y ∈ tcrTargets T, InSub l k j (tgtPos y)) ∧
    ∀ k' ≤ k, ∀ j', j' / 2 ^ (k - k') = j → ∃ y ∈ tcrTargets T, tgtPos y = some (l, k', j')

theorem tcrTargets_append (a b : QueryLog TcrPorts) :
    tcrTargets (a ++ b) = tcrTargets a ++ tcrTargets b :=
  List.filterMap_append

theorem tcrTargets_evals {T : QueryLog TcrPorts} (h : ∀ a ∈ T, IsEval a) : tcrTargets T = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun a ha ↦ ?_
  obtain ⟨l, e, s, i, he⟩ := h a ha
  obtain ⟨q, y⟩ := a
  cases q <;> simp_all [TcrQuery.evalTweak, TcrQuery.asTarget]

theorem inSub_unique {l : Layer} {k j j' : ℕ} {p : Option (Layer × ℕ × ℕ)} (h : InSub l k j p)
    (h' : InSub l k j' p) : j = j' := by
  obtain ⟨k₁, j₁, rfl, -, rfl⟩ := h
  obtain ⟨k₂, j₂, he, -, rfl⟩ := h'
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨-, rfl, rfl⟩ := he
  rfl

theorem div_two_pow_succ (j' k k' : ℕ) (hk : k' ≤ k) :
    j' / 2 ^ (k + 1 - k') = j' / 2 ^ (k - k') / 2 := by
  rw [show k + 1 - k' = k - k' + 1 by omega, pow_succ, Nat.div_div_eq_div_mul]

theorem inSub_succ {l : Layer} {k j : ℕ} {p : Option (Layer × ℕ × ℕ)}
    (h : InSub l k (2 * j) p ∨ InSub l k (2 * j + 1) p) : InSub l (k + 1) j p := by
  rcases h with ⟨k', j', rfl, hk, hj⟩ | ⟨k', j', rfl, hk, hj⟩ <;>
    refine ⟨k', j', rfl, by omega, ?_⟩ <;> rw [div_two_pow_succ _ _ _ hk, hj] <;> omega

theorem not_inSub_succ {l : Layer} {k j j' : ℕ} : ¬ InSub l k j (some (l, k + 1, j')) := by
  rintro ⟨k', j'', he, hk, -⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  omega

variable (c : Layer → KeyIndex → ChainIndex → Digest) (g : KeyIndex × LayerMsg → Randomizer)

theorem tcrDet_leafCall (l : Layer) (e : KeyIndex) (ends : ChainIndex → Digest) :
    TcrDet (simulateQ (tcrImpl W tab P) (tcrCall W (.target .leaf (leafTw l e) ends)))
      (Qrom.Xmss.Over.leafHash (m := Id) (W.hashOf tab) P l e ends)
      (· = [⟨.target .leaf (leafTw l e) ends,
        Qrom.Xmss.Over.leafHash (m := Id) (W.hashOf tab) P l e ends⟩]) := by
  intro s
  refine ⟨_, ?_, rfl⟩
  rw [run_tcrCall, simulateQ_tcrAnswer_target]
  rfl

theorem tcrDet_nodeCall (l : Layer) (k j : ℕ) (hkj : k < layerHeight ∧ j < 2 ^ 32) (a b : Digest) :
    TcrDet (simulateQ (tcrImpl W tab P) ((preOps W c).node l k j a b))
      (Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P (.node l (k + 1) j)
        (nodePayload a b))
      (· = [⟨.target .node (nodeTw l k j hkj) (a, b), Qrom.Xmss.Over.tweakableHash (m := Id)
        (W.hashOf tab) P (.node l (k + 1) j) (nodePayload a b)⟩]) := by
  have h : TcrDet
      (simulateQ (tcrImpl W tab P) (tcrCall W (.target .node (nodeTw l k j hkj) (a, b))))
      (Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P (.node l (k + 1) j)
        (nodePayload a b))
      (· = [⟨.target .node (nodeTw l k j hkj) (a, b), Qrom.Xmss.Over.tweakableHash (m := Id)
        (W.hashOf tab) P (.node l (k + 1) j) (nodePayload a b)⟩]) := by
    intro s
    refine ⟨_, ?_, rfl⟩
    rw [run_tcrCall, simulateQ_tcrAnswer_target]
    rfl
  have he : (preOps W c).node l k j a b = tcrCall W (.target .node (nodeTw l k j hkj) (a, b)) :=
    dite_eq_left hkj
  rw [he]
  exact h

theorem tcrDet_otsPublicKey (l : Layer) (e : KeyIndex) :
    TcrDet (simulateQ (tcrImpl W tab P) (Gen.otsPublicKey (preOps W c) l e))
      (Gen.otsPublicKey (idealOps (W.hashOf tab) P c g) l e) fun T ↦ ∀ a ∈ T, IsEval a := by
  have h1 := mmap_sequenceFin (simulateQ' (tcrImpl W tab P))
    fun i ↦ (preOps W c).chain l e i (chainLength - 1)
  simp only at h1
  have hv : Gen.otsPublicKey (idealOps (W.hashOf tab) P c g) l e =
      fun i ↦ ((idealOps (W.hashOf tab) P c g).chain l e i (chainLength - 1)).run :=
    sequenceFin_pure _
  rw [Gen.otsPublicKey, h1, hv]
  refine tcrDet_sequenceFin _ _ fun i ↦ ?_
  have h2 := mmap_walkChain (simulateQ' (tcrImpl W tab P))
    (fun s x ↦ tcrCall W (.eval () (chainTw l e s i) x)) 0 (chainLength - 1) (c l e i)
  simp only at h2
  show TcrDet (simulateQ (tcrImpl W tab P) (walkChain _ 0 (chainLength - 1) (c l e i))) _ _
  rw [h2]
  exact tcrDet_walk W tab P l e i _ _

theorem tcrDet_keyLeaf (l : Layer) (e : KeyIndex) :
    TcrDet (simulateQ (tcrImpl W tab P) (Gen.keyLeaf (preOps W c) l e))
      (Gen.keyLeaf (idealOps (W.hashOf tab) P c g) l e)
      fun T ↦ ∃ T₁ T₂, T = T₁ ++ T₂ ∧ (∀ a ∈ T₁, IsEval a) ∧
        T₂ = [⟨.target .leaf (leafTw l e) (Gen.otsPublicKey (idealOps (W.hashOf tab) P c g) l e),
          Gen.keyLeaf (idealOps (W.hashOf tab) P c g) l e⟩] := by
  rw [Gen.keyLeaf, simulateQ_bind]
  exact (tcrDet_otsPublicKey W tab P c g l e).bind (tcrDet_leafCall W tab P l e _)

theorem treeNode_succ {m : Type → Type} [Monad m] (o : Ops m) (l : Layer) (k j : ℕ) :
    Gen.treeNode o l (k + 1) j = Gen.treeNode o l k (2 * j) >>= fun a ↦
      Gen.treeNode o l k (2 * j + 1) >>= fun b ↦ o.node l k j a b :=
  rfl

theorem keyAt_val_of_lt {j : ℕ} (hj : j < 2 ^ 32) : (keyAt j).val = j :=
  Nat.mod_eq_of_lt hj

/-- **The precomputation of a subtree**: its value is the honest node and its transcript is the
honest transcript of the subtree. -/
theorem tcrDet_treeNode (l : Layer) : ∀ (k j : ℕ), k ≤ layerHeight → (j + 1) * 2 ^ k ≤ 2 ^ 32 →
    TcrDet (simulateQ (tcrImpl W tab P) (Gen.treeNode (preOps W c) l k j))
      (Gen.treeNode (idealOps (W.hashOf tab) P c g) l k j)
      (TreeQ (idealOps (W.hashOf tab) P c g) l k j)
  | 0, j, _, hj => by
    have hj' : j < 2 ^ 32 := by omega
    refine (tcrDet_keyLeaf W tab P c g l (keyAt j)).mono ?_
    rintro T ⟨T₁, T₂, rfl, h₁, rfl⟩
    set o := idealOps (W.hashOf tab) P c g
    have ht : tcrTargets (T₁ ++
        [⟨.target .leaf (leafTw l (keyAt j)) (Gen.otsPublicKey o l (keyAt j)),
          Gen.keyLeaf o l (keyAt j)⟩]) =
        [(⟨.leaf, leafTw l (keyAt j), Gen.otsPublicKey o l (keyAt j)⟩,
          Gen.keyLeaf o l (keyAt j))] := by
      rw [tcrTargets_append, tcrTargets_evals h₁]
      rfl
    have hpos : tgtPos (⟨.leaf, leafTw l (keyAt j), Gen.otsPublicKey o l (keyAt j)⟩,
        Gen.keyLeaf o l (keyAt j)) = some (l, 0, j) := by
      simp only [tgtPos, slotPos, keyAt_val_of_lt hj']
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl (h₁ a ha)
      · rw [List.mem_singleton] at ha
        subst ha
        exact Or.inr ⟨_, rfl, Or.inl ⟨l, keyAt j, rfl⟩⟩
    · rw [ht]
      exact List.nodup_singleton _
    · rw [ht]
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨0, j, hpos, le_rfl, by simp⟩
    · intro k' hk' j' hj''
      obtain rfl : k' = 0 := by omega
      obtain rfl : j' = j := by simpa using hj''
      exact ⟨_, by rw [ht]; exact List.mem_singleton_self _, hpos⟩
  | k + 1, j, hk, hj => by
    have hkj : k < layerHeight ∧ j < 2 ^ 32 := by
      refine ⟨by omega, ?_⟩
      have : j * 2 ^ (k + 1) < 2 ^ 32 := by nlinarith [Nat.one_le_two_pow (n := k + 1)]
      nlinarith [Nat.one_le_two_pow (n := k + 1)]
    have hl : (2 * j + 1) * 2 ^ k ≤ 2 ^ 32 := by rw [pow_succ] at hj; nlinarith
    have hr : (2 * j + 1 + 1) * 2 ^ k ≤ 2 ^ 32 := by rw [pow_succ] at hj; nlinarith
    rw [treeNode_succ]
    simp only [simulateQ_bind]
    refine ((tcrDet_treeNode l k (2 * j) (by omega) hl).bind
      ((tcrDet_treeNode l k (2 * j + 1) (by omega) hr).bind
        (tcrDet_nodeCall W tab P c l k j hkj _ _))).mono ?_
    · rintro T ⟨T₁, T₂, rfl, ⟨e₁, n₁, s₁, c₁⟩, T₃, T₄, rfl, ⟨e₃, n₃, s₃, c₃⟩, rfl⟩
      set o := idealOps (W.hashOf tab) P c g
      set yN : TcrOut × Digest := (⟨.node, nodeTw l k j hkj,
        (Gen.treeNode o l k (2 * j), Gen.treeNode o l k (2 * j + 1))⟩,
          Gen.treeNode o l (k + 1) j) with hyN
      have ht : tcrTargets (T₁ ++ (T₃ ++ [⟨.target .node (nodeTw l k j hkj)
          (Gen.treeNode o l k (2 * j), Gen.treeNode o l k (2 * j + 1)),
          Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P (.node l (k + 1) j)
            (nodePayload (Gen.treeNode o l k (2 * j)) (Gen.treeNode o l k (2 * j + 1)))⟩])) =
          tcrTargets T₁ ++ (tcrTargets T₃ ++ [yN]) := by
        rw [tcrTargets_append, tcrTargets_append]
        rfl
      have hpN : tgtPos yN = some (l, k + 1, j) := rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact e₁ a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact e₃ a ha
        rw [List.mem_singleton] at ha
        subst ha
        exact Or.inr ⟨yN, rfl, Or.inr ⟨l, k, j, hkj, rfl⟩⟩
      · rw [ht, List.map_append, List.map_append, List.nodup_append, List.nodup_append]
        refine ⟨n₁, ⟨n₃, List.nodup_singleton _, ?_⟩, ?_⟩
        · intro p hp q hq
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hq
          subst hq
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
          intro he
          have h3 := s₃ y hy
          rw [he, hpN] at h3
          exact not_inSub_succ h3
        · intro p hp q hq
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
          intro he
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hq
            have h1 := s₁ y hy
            have h2 := s₃ y' hy'
            rw [he] at h1
            have := inSub_unique h1 h2
            omega
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hq
            have h1 := s₁ y hy
            rw [he, hq, hpN] at h1
            exact not_inSub_succ h1
      · rw [ht]
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact inSub_succ (Or.inl (s₁ y hy))
        rcases List.mem_append.mp hy with hy | hy
        · exact inSub_succ (Or.inr (s₃ y hy))
        rw [List.mem_singleton] at hy
        subst hy
        exact ⟨k + 1, j, hpN, le_rfl, by simp⟩
      · intro k' hk' j' hj'
        rw [ht]
        by_cases hkk : k' = k + 1
        · subst hkk
          obtain rfl : j' = j := by simpa using hj'
          exact ⟨yN, by simp, hpN⟩
        · have hk'' : k' ≤ k := by omega
          rw [div_two_pow_succ _ _ _ hk''] at hj'
          rcases (show j' / 2 ^ (k - k') = 2 * j ∨ j' / 2 ^ (k - k') = 2 * j + 1 by omega) with
            h | h
          · obtain ⟨y, hy, hp⟩ := c₁ k' hk'' j' h
            exact ⟨y, List.mem_append_left _ hy, hp⟩
          · obtain ⟨y, hy, hp⟩ := c₃ k' hk'' j' h
            exact ⟨y, List.mem_append_right _ (List.mem_append_left _ hy), hp⟩

theorem inSub_layer {l l' : Layer} {k k' j j' : ℕ} {p : Option (Layer × ℕ × ℕ)}
    (h : InSub l k j p) (h' : InSub l' k' j' p) : l = l' := by
  obtain ⟨_, _, rfl, -, -⟩ := h
  obtain ⟨_, _, he, -, -⟩ := h'
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  exact he.1

/-- The transcript of the first `n` bottom trees. -/
def IterQ (o : Ops Id) (n : ℕ) (T : QueryLog TcrPorts) : Prop :=
  (∀ a ∈ T, EntOK o a) ∧ ((tcrTargets T).map tgtPos).Nodup ∧
    (∀ y ∈ tcrTargets T, ∃ t < n, InSub bottomLayer layerHeight t (tgtPos y)) ∧
    ∀ t < n, ∀ k' ≤ layerHeight, ∀ j', j' / 2 ^ (layerHeight - k') = t →
      ∃ y ∈ tcrTargets T, tgtPos y = some (bottomLayer, k', j')

theorem tcrDet_preTrees : ∀ n : ℕ, n ≤ 2 ^ layerHeight →
    TcrDet (simulateQ (tcrImpl W tab P) (preTrees (preOps W c) n)) ()
      (IterQ (idealOps (W.hashOf tab) P c g) n)
  | 0, _ => (tcrDet_pure ()).mono fun T hT ↦ by
      subst hT
      exact ⟨by simp, by simp [tcrTargets], fun y hy ↦ by simp [tcrTargets] at hy,
        fun t ht ↦ by omega⟩
  | n + 1, hn => by
    have hb : (n + 1) * 2 ^ layerHeight ≤ 2 ^ 32 := by
      have h2 : (2 : ℕ) ^ 32 = 2 ^ layerHeight * 2 ^ layerHeight := by
        rw [show layerHeight = 16 from rfl]
        norm_num
      rw [h2]
      exact Nat.mul_le_mul_right _ hn
    have h1 := tcrDet_treeNode W tab P c g bottomLayer layerHeight n le_rfl hb
    generalize Gen.treeNode (idealOps (W.hashOf tab) P c g) bottomLayer layerHeight n = v at h1
    simp only [preTrees, simulateQ_bind, simulateQ_pure]
    refine TcrDet.mono (TcrDet.bind (tcrDet_preTrees n (by omega))
      (TcrDet.bind h1 (tcrDet_pure ()))) ?_
    rintro T ⟨T₁, T₂, rfl, ⟨e₁, n₁, s₁, c₁⟩, T₃, T₄, rfl, ⟨e₃, n₃, s₃, c₃⟩, rfl⟩
    rw [List.append_nil]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      exacts [e₁ a ha, e₃ a ha]
    · rw [tcrTargets_append, List.map_append, List.nodup_append]
      refine ⟨n₁, n₃, ?_⟩
      intro p hp q hq he
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hq
      obtain ⟨t, ht, h1⟩ := s₁ y hy
      have h2 := s₃ y' hy'
      rw [← he] at h2
      have := inSub_unique h1 h2
      omega
    · rw [tcrTargets_append]
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨t, ht, h⟩ := s₁ y hy
        exact ⟨t, by omega, h⟩
      · exact ⟨n, by omega, s₃ y hy⟩
    · rw [tcrTargets_append]
      intro t ht k' hk' j' hj'
      by_cases htn : t = n
      · subst htn
        obtain ⟨y, hy, hp⟩ := c₃ k' hk' j' hj'
        exact ⟨y, List.mem_append_right _ hy, hp⟩
      · obtain ⟨y, hy, hp⟩ := c₁ t (by omega) k' hk' j' hj'
        exact ⟨y, List.mem_append_left _ hy, hp⟩

/-- The number of trees of a layer: `2^16` bottom trees, one top tree. -/
def nTrees (l : Layer) : ℕ :=
  if l = bottomLayer then 2 ^ layerHeight else 1

/-- The position `(l, k, j)` is a node (or for `k = 0`, a leaf) of the trees of layer `l`. -/
def Covered (l : Layer) (k j : ℕ) : Prop :=
  k ≤ layerHeight ∧ j / 2 ^ (layerHeight - k) < nTrees l

/-- **The transcript of the precomputation**: honest entries, distinct target positions, and a
target at every position of both layers. -/
def AllQ (o : Ops Id) (T : QueryLog TcrPorts) : Prop :=
  (∀ a ∈ T, EntOK o a) ∧ ((tcrTargets T).map tgtPos).Nodup ∧
    ∀ l k j, Covered l k j → ∃ y ∈ tcrTargets T, tgtPos y = some (l, k, j)

theorem layer_cases (l : Layer) : l = bottomLayer ∨ l = topLayer := by
  rcases l with ⟨_ | _ | n, hn⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hn (by simp [layerCount])

theorem topLayer_ne_bottomLayer : topLayer ≠ bottomLayer := by
  decide

/-- **The precomputation at a fixed table**: its value is the top root and its transcript is
honest and complete. -/
theorem tcrDet_preAll :
    TcrDet (simulateQ (tcrImpl W tab P) (preAll (preOps W c)))
      (Gen.root (idealOps (W.hashOf tab) P c g)) (AllQ (idealOps (W.hashOf tab) P c g)) := by
  have h32 : (0 + 1) * 2 ^ layerHeight ≤ 2 ^ 32 := by
    rw [show layerHeight = 16 from rfl]
    norm_num
  have h1 := tcrDet_treeNode W tab P c g topLayer layerHeight 0 le_rfl h32
  simp only [preAll, Gen.root, simulateQ_bind, simulateQ_pure]
  generalize Gen.treeNode (idealOps (W.hashOf tab) P c g) topLayer layerHeight 0 = v at h1 ⊢
  refine TcrDet.mono (TcrDet.bind h1 (TcrDet.bind
    (tcrDet_preTrees W tab P c g (2 ^ layerHeight) le_rfl) (tcrDet_pure v))) ?_
  rintro T ⟨T₁, T₂, rfl, ⟨e₁, n₁, s₁, c₁⟩, T₃, T₄, rfl, ⟨e₃, n₃, s₃, c₃⟩, rfl⟩
  rw [List.append_nil]
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    exacts [e₁ a ha, e₃ a ha]
  · rw [tcrTargets_append, List.map_append, List.nodup_append]
    refine ⟨n₁, n₃, ?_⟩
    intro p hp q hq he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hq
    obtain ⟨t, -, h2⟩ := s₃ y' hy'
    rw [← he] at h2
    exact topLayer_ne_bottomLayer (inSub_layer (s₁ y hy) h2)
  · rintro l k j ⟨hk, hj⟩
    rw [tcrTargets_append]
    rcases layer_cases l with rfl | rfl
    · rw [nTrees, ite_eq_left (rfl : bottomLayer = bottomLayer)] at hj
      obtain ⟨y, hy, hp⟩ := c₃ _ hj k hk j rfl
      exact ⟨y, List.mem_append_right _ hy, hp⟩
    · rw [nTrees, ite_eq_right topLayer_ne_bottomLayer] at hj
      obtain ⟨y, hy, hp⟩ := c₁ k hk j (Nat.lt_one_iff.mp hj)
      exact ⟨y, List.mem_append_left _ hy, hp⟩

/-! ### The reduction's own transcript -/

variable (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q))

theorem run_logImpl_inl {α : Type} (q : W.Oracles.Domain)
    (k : W.Oracles.Range q → OracleComp (W.Oracles + TcrPorts) α) (u : QueryLog TcrPorts) :
    (simulateQ (logImpl tab ans) (liftM ((W.Oracles + TcrPorts).query (.inl q)) >>= k)).run u =
      W.eager tab q >>= fun a ↦ (simulateQ (logImpl tab ans) (k a)).run u := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change (StateT.lift (W.eager tab q)).run u >>= _ = _
  rw [StateT.run_lift, bind_assoc]
  simp only [pure_bind]

theorem run_logImpl_inr {α : Type} (q : TcrQ)
    (k : TcrPorts.Range q → OracleComp (W.Oracles + TcrPorts) α) (u : QueryLog TcrPorts) :
    (simulateQ (logImpl tab ans) (liftM ((W.Oracles + TcrPorts).query (.inr q)) >>= k)).run u =
      simulateQ (W.eager tab) (ans q) >>= fun a ↦
        (simulateQ (logImpl tab ans) (k a)).run (u ++ [⟨q, a⟩]) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((fun a ↦ (a, u ++ [⟨q, a⟩])) <$> simulateQ (W.eager tab) (ans q)) >>= _ = _
  exact bind_map_left _ _ _

theorem run_recImpl_inl {α : Type} (q : W.Oracles.Domain)
    (k : W.Oracles.Range q → OracleComp (W.Oracles + TcrPorts) α) (s : QueryLog TcrPorts) :
    (simulateQ (recImpl W) (liftM ((W.Oracles + TcrPorts).query (.inl q)) >>= k)).run s =
      liftM ((W.Oracles + TcrPorts).query (.inl q)) >>= fun a ↦
        (simulateQ (recImpl W) (k a)).run s := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change (StateT.lift (liftM ((W.Oracles + TcrPorts).query (.inl q)) :
    OracleComp (W.Oracles + TcrPorts) _)).run s >>= _ = _
  rw [StateT.run_lift, bind_assoc]
  simp only [pure_bind]

theorem run_recImpl_inr {α : Type} (q : TcrQ)
    (k : TcrPorts.Range q → OracleComp (W.Oracles + TcrPorts) α) (s : QueryLog TcrPorts) :
    (simulateQ (recImpl W) (liftM ((W.Oracles + TcrPorts).query (.inr q)) >>= k)).run s =
      tcrCall W q >>= fun a ↦ (simulateQ (recImpl W) (k a)).run (s ++ [⟨q, a⟩]) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((fun a ↦ (a, s ++ [⟨q, a⟩])) <$> tcrCall W q) >>= _ = _
  exact bind_map_left _ _ _

theorem run_logImpl_append {α : Type} (x : OracleComp (W.Oracles + TcrPorts) α)
    (t : QueryLog TcrPorts) :
    (simulateQ (logImpl tab ans) x).run t =
      (fun p ↦ (p.1, t ++ p.2)) <$> (simulateQ (logImpl tab ans) x).run [] := by
  induction x using OracleComp.inductionOn generalizing t with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with q | q
    · rw [run_logImpl_inl, run_logImpl_inl, map_bind]
      exact bind_congr fun a ↦ ih a t
    · rw [run_logImpl_inr, run_logImpl_inr, map_bind]
      refine bind_congr fun a ↦ ?_
      conv_lhs => rw [ih a]
      conv_rhs => rw [ih a, Functor.map_map]
      simp only [List.nil_append, List.append_assoc]

/-- **The reduction's own transcript** is the challenger's transcript. -/
theorem run_logImpl_recImpl {α : Type} (x : OracleComp (W.Oracles + TcrPorts) α)
    (s t : QueryLog TcrPorts) :
    (simulateQ (logImpl tab ans) ((simulateQ (recImpl W) x).run s)).run t =
      (fun p ↦ ((p.1, s ++ p.2), t ++ p.2)) <$> (simulateQ (logImpl tab ans) x).run [] := by
  induction x using OracleComp.inductionOn generalizing s t with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with q | q
    · rw [run_recImpl_inl, run_logImpl_inl, run_logImpl_inl, map_bind]
      exact bind_congr fun a ↦ ih a s t
    · rw [run_recImpl_inr, tcrCall, run_logImpl_inr, run_logImpl_inr, map_bind]
      refine bind_congr fun a ↦ ?_
      conv_lhs => rw [ih a]
      conv_rhs => rw [run_logImpl_append W tab ans (k a), Functor.map_map]
      simp only [List.nil_append, List.append_assoc]

/-- **The setup of B4 at a fixed table**: uniform coins, then the precomputation's data and
transcript, deterministically. -/
theorem run_tcrPre (hW : W.CoinsFair) :
    ∃ T₀ : TcrCoins → QueryLog TcrPorts,
      (∀ cg, AllQ (idealOps (W.hashOf tab) P cg.1 cg.2) (T₀ cg)) ∧
      (simulateQ (tcrImpl W tab P) (tcrPre W)).run [] = $ᵗ TcrCoins >>= fun cg ↦
        pure (⟨cg.1, cg.2, P, Gen.root (idealOps (W.hashOf tab) P cg.1 cg.2), T₀ cg⟩,
          T₀ cg ++ [⟨.reveal, P⟩]) := by
  choose T₀ hT₀ hQ using fun cg : TcrCoins ↦ tcrDet_preAll W tab P cg.1 cg.2 []
  refine ⟨T₀, hQ, ?_⟩
  rw [tcrPre, simulateQ_bind, StateT.run_bind, simulateQ_tcrLift, W.simulateQ_sample hW,
    StateT.run_monadLift]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun cg ↦ ?_
  rw [simulateQ_bind, StateT.run_bind, run_logImpl_recImpl, hT₀ cg, map_pure, pure_bind]
  simp only [List.nil_append]
  rw [simulateQ_bind, StateT.run_bind, tcrCall, simulateQ_spec_query]
  change ((fun a ↦ (a, T₀ cg ++ [⟨.reveal, a⟩])) <$>
    simulateQ (W.eager tab) (pure P : OracleComp W.Oracles PublicParameter)) >>= _ = _
  simp only [simulateQ_pure, map_pure, StateT.run_pure]
  rfl

end Table

/-! ## Signing from the recorded targets -/

section Sign

variable (h : HashInput → HashOutput)

/-- The signing operations of B4 at a fixed hash: the ideal chains and encodings, leaves and
nodes read from the recorded targets. -/
def lookOps (d : TcrData) : Ops Id :=
  { idealOps h d.P d.c d.g with
    leaf := fun l e _ ↦ tcrLookup d.log l 0 e.val
    node := fun l k j _ _ ↦ tcrLookup d.log l (k + 1) j }

theorem mem_tcrTargets {T : QueryLog TcrPorts} {y : TcrOut × Digest} (hy : y ∈ tcrTargets T) :
    ∃ a ∈ T, TcrQuery.asTarget a = some y :=
  List.mem_filterMap.mp hy

theorem keyAt_eq {e : KeyIndex} : keyAt e.val = e :=
  Fin.ext (Nat.mod_eq_of_lt e.isLt)

/-- An honest target at the position `(l, k, j)` carries the honest node there. -/
theorem tgtOK_digest {o : Ops Id} {y : TcrOut × Digest} (hy : TgtOK o y) {l : Layer} {k j : ℕ}
    (hp : tgtPos y = some (l, k, j)) : y.2 = Gen.treeNode o l k j := by
  rcases hy with ⟨l', e, rfl⟩ | ⟨l', k', j', hkj, rfl⟩
  · simp only [tgtPos, slotPos, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    show Gen.keyLeaf o l' e = Gen.keyLeaf o l' (keyAt e.val)
    rw [keyAt_eq]
  · simp only [tgtPos, slotPos, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    rfl

theorem entOK_target {o : Ops Id} {a : TcrEnt} (ha : EntOK o a) {y : TcrOut × Digest}
    (hy : TcrQuery.asTarget a = some y) : TgtOK o y := by
  rcases ha with ⟨l, e, s, i, he⟩ | ⟨y', hy', hok⟩
  · obtain ⟨q, r⟩ := a
    cases q <;> simp_all [TcrQuery.evalTweak, TcrQuery.asTarget]
  · rw [hy] at hy'
    cases hy'
    exact hok

/-- **A recorded node is the honest node.** -/
theorem tcrLookup_eq {o : Ops Id} {T : QueryLog TcrPorts} (hT : AllQ o T) {l : Layer} {k j : ℕ}
    (hc : Covered l k j) : tcrLookup T l k j = Gen.treeNode o l k j := by
  obtain ⟨y, hy, hp⟩ := hT.2.2 l k j hc
  obtain ⟨y', hfind⟩ : ∃ y', (tcrTargets T).find? (fun e ↦ tgtPos e = some (l, k, j)) =
      some y' :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨y, hy, by simpa using hp⟩)
  have hp' : tgtPos y' = some (l, k, j) := by simpa using List.find?_some hfind
  obtain ⟨a, ha, hay⟩ := mem_tcrTargets (List.mem_of_find?_eq_some hfind)
  rw [tcrLookup, hfind]
  exact tgtOK_digest (entOK_target (hT.1 a ha) hay) hp'

theorem lt_of_covered {l : Layer} {j : ℕ} (hc : Covered l 0 j) : j < 2 ^ 32 := by
  have h1 : nTrees l ≤ 2 ^ layerHeight := by
    unfold nTrees
    split_ifs
    exacts [le_rfl, Nat.one_le_two_pow]
  have h2 := hc.2
  rw [Nat.sub_zero] at h2
  have h3 : j < nTrees l * 2 ^ layerHeight := (Nat.div_lt_iff_lt_mul (by positivity)).mp h2
  have h4 : nTrees l * 2 ^ layerHeight ≤ 2 ^ 32 := by
    calc nTrees l * 2 ^ layerHeight ≤ 2 ^ layerHeight * 2 ^ layerHeight :=
          Nat.mul_le_mul_right _ h1
      _ = 2 ^ 32 := by rw [show layerHeight = 16 from rfl]; norm_num
  omega

/-- The nodes of the operations read from an honest complete transcript are the honest
nodes. -/
theorem treeNode_lookOps {c : Layer → KeyIndex → ChainIndex → Digest}
    {g : KeyIndex × LayerMsg → Randomizer} {P : PublicParameter} {root : Digest}
    {T : QueryLog TcrPorts} (hT : AllQ (idealOps h P c g) T) (l : Layer) :
    ∀ k j, Covered l k j →
      Gen.treeNode (lookOps h ⟨c, g, P, root, T⟩) l k j = Gen.treeNode (idealOps h P c g) l k j
  | 0, j, hc => by
    have hj := lt_of_covered hc
    have e1 : Gen.treeNode (lookOps h ⟨c, g, P, root, T⟩) l 0 j = tcrLookup T l 0 (keyAt j).val :=
      rfl
    rw [e1, keyAt_val_of_lt hj]
    exact tcrLookup_eq hT hc
  | k + 1, j, hc => by
    have e1 : Gen.treeNode (lookOps h ⟨c, g, P, root, T⟩) l (k + 1) j = tcrLookup T l (k + 1) j :=
      rfl
    rw [e1]
    exact tcrLookup_eq hT hc

theorem treePath_congr {o o' : Ops Id} {l : Layer} {e : KeyIndex}
    (h : ∀ lv : Fin layerHeight, Gen.treeNode o' l lv.val (Nat.xor (e.val / 2 ^ lv.val) 1) =
      Gen.treeNode o l lv.val (Nat.xor (e.val / 2 ^ lv.val) 1)) :
    Gen.treePath o' l e = Gen.treePath o l e := by
  simp only [Gen.treePath, h]

theorem signLayer_congr {o o' : Ops Id} (hc : o'.chain = o.chain) (he : o'.encode = o.encode)
    {e : KeyIndex} {msg : LayerMsg}
    (hp : Gen.treePath o' msg.layer e = Gen.treePath o msg.layer e) :
    Gen.signLayer o' e msg = Gen.signLayer o e msg := by
  unfold Gen.signLayer
  rw [hc, he, hp]

theorem xor_one_div_two (n : ℕ) : Nat.xor n 1 / 2 = n / 2 := by
  rcases Nat.even_or_odd n with h | h
  · change (n ^^^ 1) / 2 = _
    rw [Nat.xor_one_of_even h]
    have := Nat.even_iff.1 h
    omega
  · change (n ^^^ 1) / 2 = _
    rw [Nat.xor_one_of_odd h]
    have := Nat.odd_iff.1 h
    omega

/-- The path nodes of a key are covered. -/
theorem covered_path {l : Layer} {e : KeyIndex}
    (he : e.val < nTrees l * 2 ^ layerHeight) (lv : Fin layerHeight) :
    Covered l lv.val (Nat.xor (e.val / 2 ^ lv.val) 1) := by
  refine ⟨lv.isLt.le, ?_⟩
  have hlv := lv.isLt
  set b := layerHeight - lv.val - 1 with hb
  have hsplit : layerHeight = lv.val + (b + 1) := by omega
  have h1 : e.val / 2 ^ lv.val < nTrees l * 2 ^ (b + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_assoc, ← pow_add, add_comm (b + 1)]
    rw [← hsplit]
    exact he
  have h2 : Nat.xor (e.val / 2 ^ lv.val) 1 / 2 ^ (b + 1) = e.val / 2 ^ lv.val / 2 ^ (b + 1) := by
    rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, xor_one_div_two]
  rw [show layerHeight - lv.val = b + 1 by omega, h2]
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr h1

theorem keyBound_bottom (e : KeyIndex) : e.val < nTrees bottomLayer * 2 ^ layerHeight := by
  rw [nTrees, ite_eq_left (rfl : bottomLayer = bottomLayer), ← pow_add]
  exact e.isLt

theorem keyBound_top (idx : LeafIndex) :
    (keyIndexOnLayer idx topLayer).val < nTrees topLayer * 2 ^ layerHeight := by
  rw [nTrees, ite_eq_right topLayer_ne_bottomLayer, one_mul]
  show idx.val / 2 ^ (layerHeight * 1) < 2 ^ layerHeight
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, mul_one]
  exact idx.isLt

/-- **B4 signs as the ideal signer.** -/
theorem sign_lookOps {c : Layer → KeyIndex → ChainIndex → Digest}
    {g : KeyIndex × LayerMsg → Randomizer} {P : PublicParameter} {root : Digest}
    {T : QueryLog TcrPorts} (hT : AllQ (idealOps h P c g) T) (idx : LeafIndex) (msg : Message) :
    Gen.sign (lookOps h ⟨c, g, P, root, T⟩) idx msg = Gen.sign (idealOps h P c g) idx msg := by
  have hpath : ∀ l e, e.val < nTrees l * 2 ^ layerHeight →
      Gen.treePath (lookOps h ⟨c, g, P, root, T⟩) l e = Gen.treePath (idealOps h P c g) l e :=
    fun l e he ↦ treePath_congr fun lv ↦ treeNode_lookOps h hT l _ _ (covered_path he lv)
  have hroot : Gen.treeNode (lookOps h ⟨c, g, P, root, T⟩) bottomLayer layerHeight
      (keyIndexOnLayer idx topLayer).val =
        Gen.treeNode (idealOps h P c g) bottomLayer layerHeight
          (keyIndexOnLayer idx topLayer).val :=
    treeNode_lookOps h hT _ _ _ ⟨le_rfl, by
      rw [Nat.sub_self, pow_zero, Nat.div_one]
      exact lt_of_lt_of_le (keyBound_top idx) (by
        rw [nTrees, ite_eq_right topLayer_ne_bottomLayer, one_mul, nTrees,
          ite_eq_left (rfl : bottomLayer = bottomLayer)])⟩
  have hc : (lookOps h ⟨c, g, P, root, T⟩).chain = (idealOps h P c g).chain := rfl
  have he : (lookOps h ⟨c, g, P, root, T⟩).encode = (idealOps h P c g).encode := rfl
  have hbot (M : LayerMsg) (hM : M.layer = bottomLayer) (e : KeyIndex) :
      Gen.signLayer (lookOps h ⟨c, g, P, root, T⟩) e M = Gen.signLayer (idealOps h P c g) e M :=
    signLayer_congr hc he (hpath _ _ (hM ▸ keyBound_bottom e))
  have htop (r : Digest) : Gen.signLayer (lookOps h ⟨c, g, P, root, T⟩)
      (keyIndexOnLayer idx topLayer) (.inr r) =
        Gen.signLayer (idealOps h P c g) (keyIndexOnLayer idx topLayer) (.inr r) :=
    signLayer_congr hc he (hpath _ _ (keyBound_top idx))
  simp only [Gen.sign, hbot (.inl msg) rfl, hroot, htop]

end Sign

/-! ## The handler, the output and the judge at a fixed table -/

section Naturality

variable {m n : Type → Type} [Monad m] [Monad n] (F : m →ᵐ n)
  (hash : HashInput → m HashOutput) (P : PublicParameter) (Fg : Forgery)

theorem mmap_layerCands (l : Layer) (M : LayerMsg) :
    F (layerCands hash P Fg l M) = layerCands (fun x ↦ F (hash x)) P Fg l M := by
  simp only [layerCands, F.mmap_bind, Over.mmap_messageDigest, MonadHom.mmap_option_elim,
    F.mmap_pure, mmap_sequenceFin, Over.mmap_recoverChain, Over.mmap_leafHash,
    Over.mmap_treeFold]

theorem mmap_allCands : F (allCands hash P Fg) = allCands (fun x ↦ F (hash x)) P Fg := by
  simp only [allCands, F.mmap_bind, mmap_layerCands, Over.mmap_layerRoot,
    MonadHom.mmap_option_elim, F.mmap_pure]

theorem mmap_withDigests :
    ∀ cs : List TcrOut, F (withDigests hash P cs) = withDigests (fun x ↦ F (hash x)) P cs
  | [] => F.mmap_pure _
  | c :: cs => by
    simp only [withDigests, F.mmap_bind, F.mmap_pure, mmap_withDigests cs]

theorem mmap_postCands : F (postCands hash P Fg) = postCands (fun x ↦ F (hash x)) P Fg := by
  simp only [postCands, F.mmap_bind, mmap_allCands, mmap_withDigests]

end Naturality

section Fixed

variable (tab : W.Tab) (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q))

theorem simulateQ_chainWalk_tcrHash (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (i : ChainIndex) (s n : ℕ) (v : Digest) :
    simulateQ (logImpl tab ans) (Qrom.Xmss.Over.chainWalk (tcrHash W) P l e i s n v) =
      pure (Qrom.Xmss.Over.chainWalk (m := Id) (W.hashOf tab) P l e i s n v) := by
  have h1 := Over.mmap_chainWalk (simulateQ' (logImpl tab ans)) (tcrHash W) P l e i s n v
  rw [simulateQ'_apply] at h1
  rw [h1, Over.comp_eq_pure (simulateQ' (logImpl tab ans)) (tcrHash W) (W.hashOf tab)
    (simulateQ_tcrHash W tab ans), ← Over.mmap_chainWalk]
  rfl

theorem simulateQ_grind_tcrHash (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : HashInput)
    (r0 : Randomizer) (k t : ℕ) :
    simulateQ (logImpl tab ans) (grind (tcrHash W) P l e M r0 k t) =
      pure (grind (m := Id) (W.hashOf tab) P l e M r0 k t) := by
  have h1 := mmap_grind (simulateQ' (logImpl tab ans)) (tcrHash W) P l e M r0 k t
  rw [simulateQ'_apply] at h1
  rw [h1, Over.comp_eq_pure (simulateQ' (logImpl tab ans)) (tcrHash W) (W.hashOf tab)
    (simulateQ_tcrHash W tab ans), ← mmap_grind]
  rfl

theorem simulateQ_sign_signOps (d : TcrData) (idx : LeafIndex) (msg : Message) :
    simulateQ (logImpl tab ans) (Gen.sign (signOps W d) idx msg) =
      pure (Gen.sign (lookOps (W.hashOf tab) d) idx msg) :=
  Gen.simulateQ_sign (logImpl tab ans) (signOps W d) (lookOps (W.hashOf tab) d)
    (fun l e i μ ↦ simulateQ_chainWalk_tcrHash W tab ans d.P l e i 0 μ (d.c l e i))
    (fun _ _ _ ↦ simulateQ_pure _ _) (fun _ _ _ _ _ ↦ simulateQ_pure _ _)
    (fun e M ↦ simulateQ_grind_tcrHash W tab ans d.P M.layer e M.bytes (d.g (e, M))
      randomizerAttemptLimit 0) idx msg

/-- **The handler of B4 at a fixed table** answers as the ideal signer, without SM-TCR-C
queries. -/
theorem hKernel_tcrSigner {c : Layer → KeyIndex → ChainIndex → Digest}
    {g : KeyIndex × LayerMsg → Randomizer} {P : PublicParameter} {root : Digest}
    {T : QueryLog TcrPorts} (hT : AllQ (idealOps (W.hashOf tab) P c g) T)
    (sl : QueryLog SigningOracleSpec) (L : QueryLog TcrPorts) (r : SigningRequest) :
    hKernel tab ans (tcrSigner W) ((⟨c, g, P, root, T⟩, sl), L) r =
      pure (idealSign (W.hashOf tab) (P, c, g) r, ((⟨c, g, P, root, T⟩,
        sl ++ [⟨r, idealSign (W.hashOf tab) (P, c, g) r⟩]), L)) := by
  have hs := simulateQ_sign_signOps W tab ans ⟨c, g, P, root, T⟩ r.leafIndex r.message
  rw [sign_lookOps _ hT] at hs
  simp only [hKernel, tcrSigner, simulateQ_bind, hs, pure_bind, simulateQ_pure, StateT.run_pure,
    map_pure]
  rfl

/-- The output of B4 at a fixed table: the first colliding candidate, without SM-TCR-C
queries. -/
theorem run_tcrPost (d : TcrData) (Fg : Forgery) (s : TcrSt) (L : QueryLog TcrPorts) :
    (simulateQ (logImpl tab ans) (tcrPost W d Fg s)).run L =
      pure (tcrPick d.log (postCands (m := Id) (W.hashOf tab) d.P Fg), L) := by
  have h1 := mmap_postCands (simulateQ' (logImpl tab ans)) (tcrHash W) d.P Fg
  rw [simulateQ'_apply, Over.comp_eq_pure (simulateQ' (logImpl tab ans)) (tcrHash W)
    (W.hashOf tab) (simulateQ_tcrHash W tab ans), ← mmap_postCands] at h1
  rw [tcrPost, simulateQ_map, h1]
  rfl

/-- The SM-TCR-C decision on a transcript and an output at a fixed table. -/
noncomputable def tcrJudge (h : HashInput → HashOutput) (P : PublicParameter)
    (L : QueryLog TcrPorts) (out : TcrOut) : Bool :=
  holds (TcrValid L ∧ ∃ e ∈ tcrTargets L, e.1.1 = out.1 ∧ e.1.2.1 = out.2.1 ∧ e.1 ≠ out ∧
    e.2 = truncateHash (h (xmssTcrC.layout out.1 P out.2.1 out.2.2)))

theorem simulateQ_tcrJudge (P : PublicParameter) (L : QueryLog TcrPorts) (out : TcrOut) :
    simulateQ (W.eager tab) ((smTcr W xmssTcrC xmssTcrD).judge P L out) =
      pure (tcrJudge (W.hashOf tab) P L out) := by
  change simulateQ (W.eager tab) (xmssTcrC.eval W out.1 P out.2.1 out.2.2 >>= fun y ↦
    pure (holds (TcrValid L ∧ ∃ e ∈ tcrTargets L, e.1.1 = out.1 ∧ e.1.2.1 = out.2.1 ∧ e.1 ≠ out ∧
      e.2 = y))) = _
  rw [simulateQ_bind, simulateQ_eval, pure_bind, simulateQ_pure]
  rfl

end Fixed

/-! ## The SM-TCR-C event gives a win of B4 -/

section Decision

variable (h : HashInput → HashOutput) (P : PublicParameter)

/-- The digest of a candidate. -/
def candDigest (c : TcrOut) : Digest :=
  truncateHash (h (xmssTcrC.layout c.1 P c.2.1 c.2.2))

/-- **The decision of B4's game** after the precomputation's transcript `T`: the judge on the
first colliding candidate of the forgery. -/
noncomputable def tcrDecB (T : QueryLog TcrPorts) (F : Forgery) : Bool :=
  tcrJudge h P (T ++ [⟨.reveal, P⟩]) (tcrPick T (postCands (m := Id) h P F))

theorem withDigests_cons (c : TcrOut) (cs : List TcrOut) :
    (withDigests (m := Id) h P (c :: cs)).run =
      (c, candDigest h P c) :: (withDigests (m := Id) h P cs).run :=
  rfl

theorem digest_of_mem_withDigests :
    ∀ (cs : List TcrOut), ∀ cy ∈ (withDigests (m := Id) h P cs).run, cy.2 = candDigest h P cy.1
  | [], cy, hcy => by simp [withDigests] at hcy
  | c :: cs, cy, hcy => by
    rw [withDigests_cons, List.mem_cons] at hcy
    rcases hcy with rfl | hcy
    · rfl
    · exact digest_of_mem_withDigests cs cy hcy

theorem mem_withDigests :
    ∀ {cs : List TcrOut} {c : TcrOut}, c ∈ cs →
      (c, candDigest h P c) ∈ (withDigests (m := Id) h P cs).run
  | c' :: cs, c, hc => by
    rw [withDigests_cons, List.mem_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl rfl
    · exact Or.inr (mem_withDigests hc)

variable (F : Forgery)

/-- The candidates of a layer whose forged digest decodes to `x`. -/
theorem layerCands_id {l : Layer} {M : LayerMsg} {x : Encoding}
    (hx : Codeword.decode (forgedDigest h P F l M) = some x) :
    (layerCands (m := Id) h P F l M).run =
      ⟨.leaf, leafTw l (forgedKey F l), forgedEnds h P F l x⟩ ::
      List.ofFn fun k : Fin layerHeight ↦ ⟨.node, nodeTwOf l (forgedKey F l) k,
        forgedKids F l k.val (forgedFold h P F l
          (Qrom.Xmss.Over.leafHash (m := Id) h P l (forgedKey F l) (forgedEnds h P F l x))
          k.val)⟩ := by
  have hx' : Codeword.decode (Qrom.Xmss.Over.messageDigest (m := Id) h P l (forgedKey F l) M.bytes
      (F.signature.layers l).randomizer).run = some x := hx
  simp only [layerCands, bind_run, hx', Option.elim, sequenceFin_pure, Id.run_pure]
  rfl

theorem allCands_id : (allCands (m := Id) h P F).run =
    (layerCands (m := Id) h P F bottomLayer (.inl F.message)).run ++
      (Qrom.Xmss.Over.layerRoot (m := Id) h P bottomLayer (forgedKey F bottomLayer)
        (littleEndianBytes 32 F.message) (F.signature.layers bottomLayer)).run.elim []
        fun r ↦ (layerCands (m := Id) h P F topLayer (.inr r)).run :=
  rfl

theorem mem_allCands {l : Layer} {M : LayerMsg} (hM : forgedMsg h P F l = some M) {c : TcrOut}
    (hc : c ∈ (layerCands (m := Id) h P F l M).run) : c ∈ (allCands (m := Id) h P F).run := by
  rw [allCands_id]
  rcases layer_cases l with rfl | rfl
  · rw [forgedMsg, ite_eq_left (rfl : bottomLayer = bottomLayer)] at hM
    cases hM
    exact List.mem_append_left _ hc
  · rw [forgedMsg, ite_eq_right topLayer_ne_bottomLayer] at hM
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hM
    refine List.mem_append_right _ ?_
    rw [show forgedKey F bottomLayer = keyIndexOnLayer F.signature.leafIndex bottomLayer from rfl,
      hr]
    exact hc

theorem keyBound_forged (l : Layer) : (forgedKey F l).val < nTrees l * 2 ^ layerHeight := by
  rcases layer_cases l with rfl | rfl
  · exact keyBound_bottom _
  · exact keyBound_top _

/-- **The SM-TCR-C event yields a colliding candidate.** -/
theorem exists_hit {c : Layer → KeyIndex → ChainIndex → Digest}
    {g : KeyIndex × LayerMsg → Randomizer} {T : QueryLog TcrPorts}
    (hT : AllQ (idealOps h P c g) T) (hev : TcrEv h P (idealOps h P c g) F) :
    ∃ cy ∈ (postCands (m := Id) h P F).run, TcrHit T cy.1 cy.2 := by
  set o := idealOps h P c g
  obtain ⟨l, M, hM, x, hx, hev⟩ := hev
  have hb := keyBound_forged F l
  have hL := layerCands_id h P F hx
  have hpos : ∀ k j, Covered l k j → ∃ y ∈ tcrTargets T, tgtPos y = some (l, k, j) ∧ TgtOK o y :=
    fun k j hc ↦ by
      obtain ⟨y, hy, hp⟩ := hT.2.2 l k j hc
      obtain ⟨a, ha, hay⟩ := mem_tcrTargets hy
      exact ⟨y, hy, hp, entOK_target (hT.1 a ha) hay⟩
  rcases hev with ⟨hne, hleaf⟩ | ⟨k, hk, hne, hnode⟩
  · set cand : TcrOut := ⟨.leaf, leafTw l (forgedKey F l), forgedEnds h P F l x⟩
    have hmem : cand ∈ (allCands (m := Id) h P F).run :=
      mem_allCands h P F hM (by rw [hL]; exact List.mem_cons_self)
    refine ⟨(cand, candDigest h P cand), mem_withDigests h P hmem, ?_⟩
    have hc : Covered l 0 (forgedKey F l).val := ⟨Nat.zero_le _, by
      rw [Nat.sub_zero]
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr hb⟩
    obtain ⟨y, hy, hp, hok⟩ := hpos _ _ hc
    rcases hok with ⟨l', e, rfl⟩ | ⟨l', k', j', hkj, rfl⟩
    · have hp' : (some (l', 0, e.val) : Option (Layer × ℕ × ℕ)) =
          some (l, 0, (forgedKey F l).val) := hp
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hp'
      obtain ⟨rfl, he⟩ := hp'
      obtain rfl : e = forgedKey F l' := Fin.ext he
      refine ⟨_, hy, rfl, rfl, fun heq ↦ hne ?_, hleaf.symm⟩
      injection heq with _ h3
      exact (congrArg Prod.snd h3).symm
    · have hp' : (some (l', k' + 1, j') : Option (Layer × ℕ × ℕ)) =
          some (l, 0, (forgedKey F l).val) := hp
      simp at hp'
  · set e := forgedKey F l
    set kids := forgedKids F l k (forgedFold h P F l
      (Qrom.Xmss.Over.leafHash (m := Id) h P l e (forgedEnds h P F l x)) k)
    set j := e.val / 2 ^ (k + 1)
    set cand : TcrOut := ⟨.node, nodeTwOf l e ⟨k, hk⟩, kids⟩
    have hmem : cand ∈ (allCands (m := Id) h P F).run :=
      mem_allCands h P F hM (by
        rw [hL]
        exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨⟨k, hk⟩, rfl⟩))
    refine ⟨(cand, candDigest h P cand), mem_withDigests h P hmem, ?_⟩
    have hc : Covered l (k + 1) j := ⟨hk, by
      rw [Nat.div_div_eq_div_mul, ← pow_add, show k + 1 + (layerHeight - (k + 1)) = layerHeight by
        omega]
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr hb⟩
    obtain ⟨y, hy, hp, hok⟩ := hpos _ _ hc
    rcases hok with ⟨l', e', rfl⟩ | ⟨l', k', j', hkj, rfl⟩
    · have hp' : (some (l', 0, e'.val) : Option (Layer × ℕ × ℕ)) = some (l, k + 1, j) := hp
      simp at hp'
    · have hp' : (some (l', k' + 1, j') : Option (Layer × ℕ × ℕ)) = some (l, k + 1, j) := hp
      simp only [Option.some.injEq, Prod.mk.injEq, Nat.add_right_cancel_iff] at hp'
      obtain ⟨rfl, rfl, rfl⟩ := hp'
      refine ⟨_, hy, rfl, rfl, fun heq ↦ hne ?_, hnode.symm⟩
      injection heq with _ h3
      exact (congrArg Prod.snd h3).symm

theorem tcrTargets_reveal (T : QueryLog TcrPorts) :
    tcrTargets (T ++ [⟨.reveal, P⟩]) = tcrTargets T := by
  rw [tcrTargets_append]
  exact List.append_nil _

theorem entOK_not_reveal {o : Ops Id} {a : TcrEnt} (ha : EntOK o a) : a.1.isReveal = false := by
  obtain ⟨q, r⟩ := a
  rcases ha with ⟨l, e, s, i, he⟩ | ⟨y, hy, -⟩ <;> cases q <;>
    simp_all [TcrQuery.evalTweak, TcrQuery.asTarget, TcrQuery.isReveal]

theorem chainTw_ne_of_tgtOK {o : Ops Id} {y : TcrOut × Digest} (hy : TgtOK o y) (l : Layer)
    (e : KeyIndex) (s : ChainStep) (i : ChainIndex) : y.1.2.1 ≠ chainTw l e s i := by
  rcases hy with ⟨l', e', rfl⟩ | ⟨l', k', j', hkj, rfl⟩ <;> intro heq <;>
    have := congrArg Subtype.val heq <;> simp at this

/-- **The precomputation's transcript is valid**: distinct target tweaks, all before the reveal,
no evaluation at a target tweak. -/
theorem tcrValid_of_allQ {o : Ops Id} {T : QueryLog TcrPorts} (hT : AllQ o T) :
    TcrValid (T ++ [⟨.reveal, P⟩]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tcrTargets_reveal]
    have h1 := hT.2.1
    have h2 : (tcrTargets T).map tgtPos =
        ((tcrTargets T).map fun e ↦ e.1.2.1).map fun t : XTw ↦ slotPos t.1 := by
      rw [List.map_map]
      rfl
    rw [h2] at h1
    exact h1.of_map _
  · intro e he
    have hd : phaseTwo (fun q ↦ q.isReveal) (T ++ [⟨.reveal, P⟩]) = [⟨.reveal, P⟩] := by
      unfold phaseTwo
      rw [List.dropWhile_append_of_pos fun a ha ↦ by simp [entOK_not_reveal (hT.1 a ha)]]
      rfl
    rw [hd, List.mem_singleton] at he
    rw [he]
    rfl
  · intro t ht hmem
    rw [List.filterMap_append] at ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨a, ha, hat⟩ := List.mem_filterMap.mp ht
      rw [tcrTargets_reveal] at hmem
      obtain ⟨y, hy, hyt⟩ := List.mem_map.mp hmem
      obtain ⟨a', ha', hay⟩ := mem_tcrTargets hy
      have hok := entOK_target (hT.1 a' ha') hay
      rcases hT.1 a ha with ⟨l, e, s, i, he⟩ | ⟨y', hy', -⟩
      · rw [he, Option.some.injEq] at hat
        exact chainTw_ne_of_tgtOK hok l e s i (hyt.trans hat.symm)
      · obtain ⟨q, r⟩ := a
        cases q <;> simp_all [TcrQuery.evalTweak, TcrQuery.asTarget]
    · simp [TcrQuery.evalTweak] at ht

theorem tcrPick_spec {T : QueryLog TcrPorts} {cs : List (TcrOut × Digest)}
    (h : ∃ cy ∈ cs, TcrHit T cy.1 cy.2) :
    ∃ cy ∈ cs, tcrPick T cs = cy.1 ∧ TcrHit T cy.1 cy.2 := by
  obtain ⟨cy, hfind⟩ : ∃ cy, cs.find? (fun cy ↦ holds (TcrHit T cy.1 cy.2)) = some cy :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr
      (h.imp fun cy hcy ↦ ⟨hcy.1, holds_eq_true.mpr hcy.2⟩))
  have hsome := List.find?_some hfind
  refine ⟨cy, List.mem_of_find?_eq_some hfind, ?_, holds_eq_true.mp hsome⟩
  rw [tcrPick, hfind]
  rfl

/-- **The SM-TCR-C event of the ideal game is a win of B4.** -/
theorem tcrDecB_of_tcrDec {c : Layer → KeyIndex → ChainIndex → Digest}
    {g : KeyIndex × LayerMsg → Randomizer} {T : QueryLog TcrPorts}
    (hT : AllQ (idealOps h P c g) T) (run : Forgery × QueryLog SigningOracleSpec)
    (hd : tcrDec h (P, c, g) run = true) : tcrDecB h P T run.1 = true := by
  obtain ⟨-, -, hev⟩ := holds_eq_true.mp hd
  obtain ⟨cy, hcy, hpick, hhit⟩ := tcrPick_spec (exists_hit h P run.1 hT hev)
  refine holds_eq_true.mpr ⟨tcrValid_of_allQ P hT, ?_⟩
  rw [tcrTargets_reveal]
  have hdig := digest_of_mem_withDigests h P _ cy hcy
  obtain ⟨e, he, h1, h2, h3, h4⟩ := hhit
  have hpick' : tcrPick T (postCands (m := Id) h P run.1) = cy.1 := hpick
  show ∃ e ∈ tcrTargets T, _
  rw [hpick']
  exact ⟨e, he, h1, h2, h3, h4.trans hdig⟩

end Decision

/-! ## The bound -/

section Bound

variable (tab : W.Tab) (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery)

/-- **The run of B4 after its setup collapses onto the ideal run**: for each outcome of the setup,
the SM-TCR-C event of the ideal game at the same ideal secret is at most B4's winning
probability. -/
theorem probAt_tcrDec_le (P : PublicParameter) (cg : TcrCoins) {T : QueryLog TcrPorts}
    (hT : AllQ (idealOps (W.hashOf tab) P cg.1 cg.2) T) :
    W.probAt tab ((idealRun W tab (P, cg) A).map (tcrDec (W.hashOf tab) (P, cg))) ≤
      W.probAt tab (QuantumComp₂.bind (QuantumComp₂.bind
        (kRunL W (hKernel tab ((smTcr W xmssTcrC xmssTcrD).answer P) (tcrSigner W))
          (A ⟨Gen.root (idealOps (W.hashOf tab) P cg.1 cg.2), P⟩)
          (⟨cg.1, cg.2, P, Gen.root (idealOps (W.hashOf tab) P cg.1 cg.2), T⟩, [])
          (T ++ [⟨.reveal, P⟩])) fun r ↦
        ((simulateQ (logImpl tab ((smTcr W xmssTcrC xmssTcrD).answer P))
          (tcrPost W ⟨cg.1, cg.2, P, Gen.root (idealOps (W.hashOf tab) P cg.1 cg.2), T⟩ r.1.1
            r.1.2)).run r.2).toQuantumAt (QComp.coinImpl W.spec _)) fun r ↦
        (simulateQ (W.eager tab) ((smTcr W xmssTcrC xmssTcrD).judge P r.2 r.1)).toQuantumAt
          (QComp.coinImpl W.spec _)) := by
  conv_rhs =>
    rw [kRunL_eq_map, QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc,
      QuantumComp₂.bind_assoc]
    simp only [QuantumComp₂.pure_bind, run_tcrPost, toQuantumAt_pure, simulateQ_tcrJudge]
    rw [← QuantumComp₂.map_eq_bind_pure]
  have hsim := run₂_map_kRunQ_sim (W.runtime tab) (idealKernel (W.hashOf tab) (P, cg))
    (hKernel tab ((smTcr W xmssTcrC xmssTcrD).answer P) (tcrSigner W))
    (fun s ↦ s.1.1 = ⟨cg.1, cg.2, P, Gen.root (idealOps (W.hashOf tab) P cg.1 cg.2), T⟩ ∧
      s.2 = T ++ [⟨.reveal, P⟩])
    (fun s ↦ s.1.2) ?hK ?hInv (A ⟨Gen.root (idealOps (W.hashOf tab) P cg.1 cg.2), P⟩)
    ((⟨cg.1, cg.2, P, Gen.root (idealOps (W.hashOf tab) P cg.1 cg.2), T⟩, []),
      T ++ [⟨.reveal, P⟩]) ⟨rfl, rfl⟩
    (fun r ↦ tcrDecB (W.hashOf tab) P T r.1)
    (fun r ↦ tcrJudge (W.hashOf tab) P r.2.2 (tcrPick T (postCands (m := Id) (W.hashOf tab) P r.1)))
    ?hd
  case hK =>
    rintro ⟨⟨d', sl⟩, L⟩ ⟨hd', -⟩ q
    dsimp only at hd'
    subst hd'
    rw [hKernel_tcrSigner W tab _ hT sl L q, map_pure]
    rfl
  case hInv =>
    rintro ⟨⟨d', sl⟩, L⟩ ⟨hd', hL⟩ q p hp
    dsimp only at hd' hL
    subst hd' hL
    rw [hKernel_tcrSigner W tab _ hT sl _ q, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨rfl, rfl⟩
  case hd =>
    rintro a ⟨⟨d', sl⟩, L⟩ ⟨-, hL⟩
    dsimp only at hL
    subst hL
    rfl
  rw [probAt_eq_of_run₂ W tab hsim]
  have hu := probAt_map_le_sum W tab (idealRun W tab (P, cg) A) (tcrDec (W.hashOf tab) (P, cg))
    ({()} : Finset Unit) (fun _ r ↦ tcrDecB (W.hashOf tab) P T r.1)
    fun r hr ↦ ⟨(), Finset.mem_singleton_self _, tcrDecB_of_tcrDec (W.hashOf tab) P hT r hr⟩
  rw [Finset.sum_singleton] at hu
  exact hu

theorem unifAvg_le_tsum {α : Type} [Fintype α] [SampleableType α] {F G : α → ℝ≥0∞}
    (h : ∀ a, F a ≤ G a) : unifAvg F ≤ ∑' a, Pr{let z ← $ᵗ α}[z = a] * G a := by
  rw [tsum_fintype]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton]
  exact Finset.sum_le_sum fun a _ ↦ mul_le_mul' le_rfl (h a)

/-- **B4 after the reveal of `P`**: the SM-TCR-C event averaged over the coins is at most B4's
winning probability. -/
theorem unifAvg_le_rest (hW : W.CoinsFair) (P : PublicParameter) :
    unifAvg (fun cg : TcrCoins ↦
      W.probAt tab ((idealRun W tab (P, cg) A).map (tcrDec (W.hashOf tab) (P, cg)))) ≤
      W.probAt tab (QuantumComp₂.bind (slNormal tab ((smTcr W xmssTcrC xmssTcrD).answer P)
        (tcrPre W) (fun d ↦ A ⟨d.root, d.P⟩) (fun d ↦ (d, [])) (tcrSigner W) (tcrPost W))
        fun r ↦ (simulateQ (W.eager tab) ((smTcr W xmssTcrC xmssTcrD).judge P r.2 r.1)).toQuantumAt
          (QComp.coinImpl W.spec _)) := by
  obtain ⟨T₀, hQ, hpre⟩ := run_tcrPre W tab P hW
  rw [slNormal, QuantumComp₂.bind_assoc,
    probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _), hpre,
    tsum_prEvent_bind_mul]
  simp only [tsum_prEvent_pure_mul]
  exact unifAvg_le_tsum fun cg ↦ probAt_tcrDec_le W tab A P cg (hQ cg)

end Bound

/-- **B4 bounds the SM-TCR-C event of the ideal game**: at every table of a world with fair coins,
the probability of the SM-TCR-C event of the ideal game, averaged over a uniform ideal secret, is
at most the SM-TCR-C success of `tcrRed W A`. -/
theorem idealProb_tcr_le (hW : W.CoinsFair) (tab : W.Tab)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    idealProb W tab A (fun k ↦ tcrDec (W.hashOf tab) k) ≤
      Props.smTcrSucc W xmssTcrC xmssTcrD tab (tcrRed W A) := by
  have hN := run₂_game_slRed tab (smTcr W xmssTcrC xmssTcrD) (fun _ ↦ tcrPre W)
    (fun _ d ↦ A ⟨d.root, d.P⟩) (fun _ d ↦ (d, [])) (fun _ ↦ tcrSigner W) (fun _ ↦ tcrPost W)
  have hS := probAt_eq_of_run₂ W tab hN
  have hset : simulateQ (W.eager tab) (smTcr W xmssTcrC xmssTcrD).setup = $ᵗ PublicParameter :=
    W.simulateQ_sample hW tab PublicParameter
  rw [probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _), hset] at hS
  refine le_of_le_of_eq ?_ hS.symm
  have hp : idealProb W tab A (fun k ↦ tcrDec (W.hashOf tab) k) =
      unifAvg fun P : PublicParameter ↦ unifAvg fun cg : TcrCoins ↦
        W.probAt tab ((idealRun W tab (P, cg) A).map (tcrDec (W.hashOf tab) (P, cg))) :=
    unifAvg_prod _
  rw [hp]
  exact unifAvg_le_tsum fun P ↦ unifAvg_le_rest W tab A hW P

end Quantum.StdModel.Xmss

end
