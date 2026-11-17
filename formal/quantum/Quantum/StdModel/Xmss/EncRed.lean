module

public import Quantum.StdModel.Xmss.Ideal
public import Quantum.StdModel.Xmss.Inst
public import Quantum.StdModel.Xmss.Eval

@[expose] public section

/-!
# leanXMSS's reduction to EncTCR$ (B2)

`encRed W A` is the straight-line reduction from a SUF-CMA adversary `A` of leanXMSS to the
EncTCR$ game of the message digest (`xmssEnc`). On the public `P` it samples the chain starts,
computes the top root honestly and runs `A` on `⟨root, P⟩`. A signing request is answered by the
abstract signer (`Gen.sign`) with the honest chains and tree, and with encodings computed once per
key and message (`EncSt.cache`): the challenger's target answer if the tweak `(l, e)` of the key
is new, else B2's own grinding from a fresh uniform base. At the end, B2 outputs the forged
message and randomizer of the bottom layer if they collide with the challenger's answer at that
key (`winsAt`), else those of the top layer.

* `idealProb_enc_le`: at every table of a world with fair coins, the averaged probability of the
  EncTCR$ event of the ideal game (`encDec`) is at most B2's success. The randomizer bases `g`
  of the ideal secret are sampled lazily (`card_smul_branch_kRun_lazy`), the first use of a key
  and message drawing a fresh base: B2's kernel is the lazy kernel through a state map, and the
  eager kernel at `g` is the ideal signer through another.
* `isChargeBound_encRed`: B2's hash calls are `A`'s plus its honest work.
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open Quantum.Qrom.Xmss (MsgBytes)
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props Common Qrom

/-! ## The reduction -/

/-- The challenger ports of the EncTCR$ game of leanXMSS. -/
abbrev EncSpec := (Layer × KeyIndex) × MsgBytes →ₒ Option (Randomizer × Digest)

/-- An encoding: the randomizer and the codeword digest, or nothing. -/
abbrev EncAns := Option (Randomizer × Digest)

/-- The output of an EncTCR$ adversary: the tweak, the message and the randomizer. -/
abbrev EncOut := (Layer × KeyIndex) × MsgBytes × Randomizer

/-- The chain starts. -/
abbrev Starts := Layer → KeyIndex → ChainIndex → Digest

theorem LayerMsg.length_bytes_le (M : LayerMsg) : M.bytes.length ≤ maxLen - 64 := by
  cases M with
  | inl m => exact Qrom.Xmss.length_messageBytes_le m
  | inr r => exact Qrom.Xmss.length_digestBytes_le r

/-- A layer's message as a short message of the EncTCR$ game. -/
def LayerMsg.mb (M : LayerMsg) : MsgBytes :=
  ⟨M.bytes, M.length_bytes_le⟩

/-- **B2's handler state**: the chain starts, the signing transcript, the encodings computed so
far by key and message, and the message and answer of each tweak sent to the challenger. -/
structure EncSt where
  /-- The chain starts. -/
  starts : Starts
  /-- The signing transcript. -/
  log : QueryLog SigningOracleSpec
  /-- The encodings computed so far. -/
  cache : KeyIndex × LayerMsg → Option EncAns
  /-- The message sent at each tweak, with its answer. -/
  sent : Layer × KeyIndex → Option (MsgBytes × EncAns)

/-- The state after encoding `msg` with key `e` to `v`: cached, and the tweak recorded if new. -/
def EncSt.record (s : EncSt) (e : KeyIndex) (msg : LayerMsg) (v : EncAns) : EncSt where
  starts := s.starts
  log := s.log
  cache := Function.update s.cache (e, msg) (some v)
  sent := if (s.sent (msg.layer, e)).isNone then
      Function.update s.sent (msg.layer, e) (some (msg.mb, v))
    else s.sent

/-- The state after the signature `sig` of `r`, logged. -/
def EncSt.signed (s : EncSt) (r : SigningRequest) (sig : Option Signature) : EncSt where
  starts := s.starts
  log := s.log ++ [⟨r, sig⟩]
  cache := s.cache
  sent := s.sent

/-- The challenger transcript after encoding `msg` with key `e` to `v`: the target, if new. -/
def logUpd (s : EncSt) (lg : QueryLog EncSpec) (e : KeyIndex) (msg : LayerMsg) (v : EncAns) :
    QueryLog EncSpec :=
  if (s.sent (msg.layer, e)).isNone then lg ++ [⟨((msg.layer, e), msg.mb), v⟩] else lg

/-- No encodings. -/
def noEnc : KeyIndex → LayerMsg → EncAns := fun _ _ ↦ none

/-- The encodings of the bottom message (`v1`) and of the top message (`v2`). -/
def pairEnc (v1 v2 : EncAns) : KeyIndex → LayerMsg → EncAns := fun _ msg ↦
  match msg with
  | .inl _ => v1
  | .inr _ => v2

/-- A computation over `s₁` as one over `s₁ + s₂`, by the left inclusion. -/
def liftL {ι₁ ι₂ : Type} {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} {α : Type}
    (oa : OracleComp s₁ α) : OracleComp (s₁ + s₂) α :=
  liftComp oa (s₁ + s₂)

variable (W : OracleWorld)

/-- **The honest operations** over the world's oracles: chains, leaves and nodes by the world's
hash, at the parameter `P` and the chain starts `c`; the encodings given. -/
noncomputable def hOps (P : PublicParameter) (c : Starts) (enc : KeyIndex → LayerMsg → EncAns) :
    Ops (OracleComp W.Oracles) where
  chain l e i μ := Qrom.Xmss.Over.chainWalk W.hash P l e i 0 μ (c l e i)
  leaf l e ends := Qrom.Xmss.Over.leafHash W.hash P l e ends
  node l k j a b := Qrom.Xmss.Over.tweakableHash W.hash P (.node l (k + 1) j) (nodePayload a b)
  encode e msg := pure (enc e msg)

/-- B2's encoding of `msg` with key `e`: cached, else the challenger's target if the tweak is new,
else B2's own grinding from a fresh uniform base. -/
noncomputable def encStep (P : PublicParameter) (s : EncSt) (e : KeyIndex) (msg : LayerMsg) :
    OracleComp (W.Oracles + EncSpec) (EncAns × EncSt) :=
  match s.cache (e, msg) with
  | some v => pure (v, s)
  | none => do
    let v ← if (s.sent (msg.layer, e)).isNone then
        (liftM ((W.Oracles + EncSpec).query (.inr ((msg.layer, e), msg.mb))) :
          OracleComp (W.Oracles + EncSpec) EncAns)
      else liftL (do
        let r0 ← sample W Randomizer
        xmssEnc.grind W P (msg.layer, e) msg.mb r0 0 xmssEnc.limit)
    pure (v, s.record e msg v)

/-- **B2's signing handler**: the bottom root of the request's top key, the two encodings, the
signature by the abstract signer with those encodings, logged. -/
noncomputable def encSign (P : PublicParameter) : HHandler W SigningOracleSpec EncSpec EncSt :=
  fun s r ↦ do
  let root ← liftL (Gen.treeNode (hOps W P s.starts noEnc) bottomLayer layerHeight
    (keyIndexOnLayer r.leafIndex topLayer).val)
  let p1 ← encStep W P s (keyIndexOnLayer r.leafIndex bottomLayer) (.inl r.message)
  let p2 ← encStep W P p1.2 (keyIndexOnLayer r.leafIndex topLayer) (.inr root)
  let sig ← liftL (Gen.sign (hOps W P s.starts (pairEnc p1.1 p2.1)) r.leafIndex r.message)
  pure (sig, p2.2.signed r sig)

/-- B2's setup: uniform chain starts and the honest top root. -/
noncomputable def encPre (P : PublicParameter) :
    OracleComp (W.Oracles + EncSpec) (Starts × Digest) :=
  liftL (do
    let c ← sample W Starts
    let root ← Gen.root (hOps W P c noEnc)
    pure (c, root))

/-- B2's initial handler state. -/
def encSt0 (s0 : Starts × Digest) : EncSt where
  starts := s0.1
  log := []
  cache := fun _ ↦ none
  sent := fun _ ↦ none

/-- Whether the forged message `M` and randomizer `ρ'` with digest `d` at the tweak `(l, e)`
collide with the challenger's answer there. -/
def winsAt (s : EncSt) (l : Layer) (e : KeyIndex) (M : LayerMsg) (ρ' : Randomizer) (d : Digest) :
    Bool :=
  match s.sent (l, e) with
  | some (M0, some (ρ, D)) => decide (D = d ∧ (M0, ρ) ≠ (M.mb, ρ'))
  | _ => false

/-- **B2's output** over a hash `hash`: the forged bottom message and randomizer if they collide
with the challenger's answer, else the forged top message (the recovered bottom root) and
randomizer. -/
def encOut {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput) (P : PublicParameter)
    (F : Forgery) (s : EncSt) : m EncOut := do
  let bk := forgedKey F bottomLayer
  let ρb := (F.signature.layers bottomLayer).randomizer
  let db ← Qrom.Xmss.Over.messageDigest hash P bottomLayer bk
    (LayerMsg.bytes (.inl F.message)) ρb
  if winsAt s bottomLayer bk (.inl F.message) ρb db then
    pure ((bottomLayer, bk), LayerMsg.mb (.inl F.message), ρb)
  else do
    let root ← Qrom.Xmss.Over.layerRoot hash P bottomLayer bk (littleEndianBytes 32 F.message)
      (F.signature.layers bottomLayer)
    match root with
    | none => pure ((bottomLayer, bk), LayerMsg.mb (.inl F.message), ρb)
    | some x => pure ((topLayer, forgedKey F topLayer), LayerMsg.mb (.inr x),
        (F.signature.layers topLayer).randomizer)

/-- B2's output step: `encOut` over the world's hash. -/
noncomputable def encPost (P : PublicParameter) (_s0 : Starts × Digest) (F : Forgery)
    (s : EncSt) : OracleComp (W.Oracles + EncSpec) EncOut :=
  liftL (encOut W.hash P F s)

/-- **B2, the EncTCR$ reduction**, straight-line: setup `encPre`, the adversary on `⟨root, P⟩`,
the handler `encSign`, the output `encPost`. -/
noncomputable def encRed (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    Props.Adversary W EncSpec PublicParameter EncOut :=
  fun P ↦ slRed W (encPre W P) (fun s0 ↦ A ⟨s0.2, P⟩) encSt0 (encSign W P) (encPost W P)

/-- The EncTCR$ challenger's answer at the parameter `P`. -/
noncomputable def encAnswer (P : PublicParameter) (q : (Layer × KeyIndex) × MsgBytes) :
    OracleComp W.Oracles EncAns :=
  (encTcrSalt W xmssEnc).answer P q

/-- The EncTCR$ judge at the parameter `P`. -/
noncomputable def encJudge (P : PublicParameter) (lg : QueryLog EncSpec) (out : EncOut) :
    OracleComp W.Oracles Bool :=
  (encTcrSalt W xmssEnc).judge P lg out

/-! ## The honest operations at a fixed hash -/

section Honest

variable (h : HashInput → HashOutput) (P : PublicParameter) (c : Starts)

/-- **The honest operations at the hash `h`**, with the encodings given. -/
def iOps (enc : KeyIndex → LayerMsg → EncAns) : Ops Id where
  chain l e i μ := Qrom.Xmss.Over.chainWalk (m := Id) h P l e i 0 μ (c l e i)
  leaf l e ends := Qrom.Xmss.Over.leafHash (m := Id) h P l e ends
  node l k j a b :=
    Qrom.Xmss.Over.tweakableHash (m := Id) h P (.node l (k + 1) j) (nodePayload a b)
  encode e msg := enc e msg

/-- The ideal encodings of the randomizer bases `g`. -/
def idealEnc (g : KeyIndex × LayerMsg → Randomizer) : KeyIndex → LayerMsg → EncAns :=
  fun e msg ↦ grind (m := Id) h P msg.layer e msg.bytes (g (e, msg)) randomizerAttemptLimit 0

theorem idealOps_eq_iOps (g : KeyIndex × LayerMsg → Randomizer) :
    idealOps h P c g = iOps h P c (idealEnc h P g) :=
  rfl

end Honest

section Congr

variable (ch : Layer → KeyIndex → ChainIndex → ℕ → Id Digest)
  (lf : Layer → KeyIndex → (ChainIndex → Digest) → Id Digest)
  (nd : Layer → ℕ → ℕ → Digest → Digest → Id Digest)
  (en en' : KeyIndex → LayerMsg → Id EncAns)

/-- The tree does not read the encodings. -/
theorem treeNode_encode_congr (l : Layer) :
    ∀ k j, Gen.treeNode (⟨ch, lf, nd, en⟩ : Ops Id) l k j = Gen.treeNode ⟨ch, lf, nd, en'⟩ l k j
  | 0, _ => rfl
  | k + 1, j => by
    simp only [Gen.treeNode, treeNode_encode_congr l k]

theorem treePath_encode_congr (l : Layer) (e : KeyIndex) :
    Gen.treePath (⟨ch, lf, nd, en⟩ : Ops Id) l e = Gen.treePath ⟨ch, lf, nd, en'⟩ l e := by
  simp only [Gen.treePath, treeNode_encode_congr ch lf nd en en']

/-- A layer's signature reads the encodings only at its key and message. -/
theorem signLayer_encode_congr (e : KeyIndex) (msg : LayerMsg) (h : en e msg = en' e msg) :
    Gen.signLayer (⟨ch, lf, nd, en⟩ : Ops Id) e msg = Gen.signLayer ⟨ch, lf, nd, en'⟩ e msg := by
  simp only [Gen.signLayer, h, treePath_encode_congr ch lf nd en en']

/-- **The signer reads the encodings only at the request's two layer messages.** -/
theorem sign_encode_congr (idx : LeafIndex) (m : Message)
    (h1 : en (keyIndexOnLayer idx bottomLayer) (.inl m) =
      en' (keyIndexOnLayer idx bottomLayer) (.inl m))
    (h2 : en (keyIndexOnLayer idx topLayer) (.inr (Gen.treeNode (⟨ch, lf, nd, en'⟩ : Ops Id)
        bottomLayer layerHeight (keyIndexOnLayer idx topLayer).val)) =
      en' (keyIndexOnLayer idx topLayer) (.inr (Gen.treeNode (⟨ch, lf, nd, en'⟩ : Ops Id)
        bottomLayer layerHeight (keyIndexOnLayer idx topLayer).val))) :
    Gen.sign (⟨ch, lf, nd, en⟩ : Ops Id) idx m = Gen.sign ⟨ch, lf, nd, en'⟩ idx m := by
  simp only [Gen.sign, Extract.id_bind, signLayer_encode_congr ch lf nd en en' _ _ h1,
    treeNode_encode_congr ch lf nd en en', signLayer_encode_congr ch lf nd en en' _ _ h2]

end Congr

section HonestCongr

variable (h : HashInput → HashOutput) (P : PublicParameter) (c : Starts)

theorem treeNode_iOps (enc enc' : KeyIndex → LayerMsg → EncAns) (l : Layer) (k j : ℕ) :
    Gen.treeNode (iOps h P c enc) l k j = Gen.treeNode (iOps h P c enc') l k j :=
  treeNode_encode_congr _ _ _ enc enc' l k j

/-- **B2's signature is the ideal signer's** when its two encodings are the ideal ones. -/
theorem sign_iOps_pairEnc (g : KeyIndex × LayerMsg → Randomizer) (r : SigningRequest)
    (v1 v2 : EncAns)
    (h1 : v1 = idealEnc h P g (keyIndexOnLayer r.leafIndex bottomLayer) (.inl r.message))
    (h2 : v2 = idealEnc h P g (keyIndexOnLayer r.leafIndex topLayer)
      (.inr (Gen.treeNode (iOps h P c noEnc) bottomLayer layerHeight
        (keyIndexOnLayer r.leafIndex topLayer).val))) :
    Gen.sign (iOps h P c (pairEnc v1 v2)) r.leafIndex r.message =
      idealSign h (P, c, g) r := by
  refine (sign_encode_congr _ _ _ (pairEnc v1 v2) (idealEnc h P g) r.leafIndex r.message h1
    ?_).trans rfl
  exact h2.trans (congrArg (fun x ↦ idealEnc h P g (keyIndexOnLayer r.leafIndex topLayer) (.inr x))
    (treeNode_iOps h P c noEnc (idealEnc h P g) _ _ _))

end HonestCongr

section Sim

variable {W} (tab : W.Tab) (P : PublicParameter) (c : Starts) (enc : KeyIndex → LayerMsg → EncAns)

theorem simulateQ_hOps_chain (l : Layer) (e : KeyIndex) (i : ChainIndex) (μ : ℕ) :
    simulateQ (W.eager tab) ((hOps W P c enc).chain l e i μ) =
      pure ((iOps (W.hashOf tab) P c enc).chain l e i μ) := by
  change simulateQ' (W.eager tab) _ = _
  rw [hOps, Over.mmap_chainWalk, Over.comp_eq_pure _ W.hash (W.hashOf tab) (W.simulateQ_hash tab),
    ← Over.mmap_chainWalk]
  rfl

theorem simulateQ_hOps_leaf (l : Layer) (e : KeyIndex) (ends : ChainIndex → Digest) :
    simulateQ (W.eager tab) ((hOps W P c enc).leaf l e ends) =
      pure ((iOps (W.hashOf tab) P c enc).leaf l e ends) := by
  change simulateQ' (W.eager tab) _ = _
  rw [hOps, Over.mmap_leafHash, Over.comp_eq_pure _ W.hash (W.hashOf tab) (W.simulateQ_hash tab),
    ← Over.mmap_leafHash]
  rfl

theorem simulateQ_hOps_node (l : Layer) (k j : ℕ) (a b : Digest) :
    simulateQ (W.eager tab) ((hOps W P c enc).node l k j a b) =
      pure ((iOps (W.hashOf tab) P c enc).node l k j a b) := by
  change simulateQ' (W.eager tab) _ = _
  rw [hOps, Over.mmap_tweakableHash,
    Over.comp_eq_pure _ W.hash (W.hashOf tab) (W.simulateQ_hash tab), ← Over.mmap_tweakableHash]
  rfl

theorem simulateQ_hOps_encode (e : KeyIndex) (msg : LayerMsg) :
    simulateQ (W.eager tab) ((hOps W P c enc).encode e msg) =
      pure ((iOps (W.hashOf tab) P c enc).encode e msg) :=
  simulateQ_pure _ _

theorem simulateQ_hOps_treeNode (l : Layer) (k j : ℕ) :
    simulateQ (W.eager tab) (Gen.treeNode (hOps W P c enc) l k j) =
      pure (Gen.treeNode (iOps (W.hashOf tab) P c enc) l k j) :=
  Gen.simulateQ_treeNode (W.eager tab) _ _ (simulateQ_hOps_chain tab P c enc)
    (simulateQ_hOps_leaf tab P c enc) (simulateQ_hOps_node tab P c enc)
    (simulateQ_hOps_encode tab P c enc) l k j

theorem simulateQ_hOps_root :
    simulateQ (W.eager tab) (Gen.root (hOps W P c enc)) =
      pure (Gen.root (iOps (W.hashOf tab) P c enc)) :=
  Gen.simulateQ_root (W.eager tab) _ _ (simulateQ_hOps_chain tab P c enc)
    (simulateQ_hOps_leaf tab P c enc) (simulateQ_hOps_node tab P c enc)
    (simulateQ_hOps_encode tab P c enc)

theorem simulateQ_hOps_sign (idx : LeafIndex) (m : Message) :
    simulateQ (W.eager tab) (Gen.sign (hOps W P c enc) idx m) =
      pure (Gen.sign (iOps (W.hashOf tab) P c enc) idx m) :=
  Gen.simulateQ_sign (W.eager tab) _ _ (simulateQ_hOps_chain tab P c enc)
    (simulateQ_hOps_leaf tab P c enc) (simulateQ_hOps_node tab P c enc)
    (simulateQ_hOps_encode tab P c enc) idx m

end Sim

/-! ## B2's handler at a fixed table -/

/-- Grinding the message `msg` of key `e` from the base `r0`. -/
def grindAt (h : HashInput → HashOutput) (P : PublicParameter) (e : KeyIndex) (msg : LayerMsg)
    (r0 : Randomizer) : EncAns :=
  grind (m := Id) h P msg.layer e msg.bytes r0 randomizerAttemptLimit 0

/-- **One encoding step at a fixed table**: cached, else grinding from a uniform base, with the
state and the challenger transcript updated. -/
noncomputable def stepNF (h : HashInput → HashOutput) (P : PublicParameter) (s : EncSt)
    (lg : QueryLog EncSpec) (e : KeyIndex) (msg : LayerMsg) :
    ProbComp ((EncAns × EncSt) × QueryLog EncSpec) :=
  match s.cache (e, msg) with
  | some v => pure ((v, s), lg)
  | none => ($ᵗ Randomizer) >>= fun r0 ↦
      pure ((grindAt h P e msg r0, s.record e msg (grindAt h P e msg r0)),
        logUpd s lg e msg (grindAt h P e msg r0))

section Run

variable {W} (tab : W.Tab)

theorem run_simulateQ_lift {S α : Type} (oa : OracleComp W.Oracles α) (lg : S) :
    (simulateQ (fun t ↦ (StateT.lift (W.eager tab t) : StateT S ProbComp _)) oa).run lg =
      (fun a ↦ (a, lg)) <$> simulateQ (W.eager tab) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih => simp [StateT.run_bind, StateT.run_lift, ih]

/-- A reduction's classical algorithm over the world's oracles alone keeps the transcript. -/
theorem run_simulateQ_logImpl_liftComp {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp W.Oracles α) (lg : QueryLog R') :
    (simulateQ (logImpl tab ans) (liftL (s₂ := R') oa)).run lg =
      (fun a ↦ (a, lg)) <$> simulateQ (W.eager tab) oa := by
  have h := QueryImpl.simulateQ_liftComp_left_eq_of_apply (spec₂' := R') (logImpl tab ans)
    (fun t ↦ StateT.lift (W.eager tab t)) (fun _ ↦ rfl) oa
  exact (congrArg (fun x ↦ StateT.run x lg) h).trans (run_simulateQ_lift tab oa lg)

variable (hW : W.CoinsFair) (P : PublicParameter)
include hW

/-- **B2's encoding step against the EncTCR$ challenger** at a fixed table. -/
theorem encStep_run (s : EncSt) (lg : QueryLog EncSpec) (e : KeyIndex) (msg : LayerMsg) :
    (simulateQ (logImpl tab (encAnswer W P)) (encStep W P s e msg)).run lg =
      stepNF (W.hashOf tab) P s lg e msg := by
  unfold encStep stepNF
  cases hc : s.cache (e, msg) with
  | some v => simp
  | none =>
    simp only
    by_cases hs : (s.sent (msg.layer, e)).isNone = true
    · simp only [hs, ↓reduceIte, simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
      change ((fun a ↦ (a, lg ++ [⟨((msg.layer, e), msg.mb), a⟩])) <$>
        simulateQ (W.eager tab) (do
          let r0 ← sample W Randomizer
          xmssEnc.grind W P (msg.layer, e) msg.mb r0 0 xmssEnc.limit)) >>= _ = _
      simp only [simulateQ_bind, W.simulateQ_sample hW, simulateQ_xmssEnc_encode, map_bind,
        map_pure, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, logUpd, hs,
        ↓reduceIte]
      rfl
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, StateT.run_bind,
        run_simulateQ_logImpl_liftComp, W.simulateQ_sample hW, simulateQ_xmssEnc_encode,
        map_bind, map_pure, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, logUpd]
      rfl

/-- **B2's handler against the EncTCR$ challenger** at a fixed table: two encoding steps, the
signature with their encodings. -/
theorem encSign_run (s : EncSt) (lg : QueryLog EncSpec) (r : SigningRequest) :
    (simulateQ (logImpl tab (encAnswer W P)) (encSign W P s r)).run lg =
      stepNF (W.hashOf tab) P s lg (keyIndexOnLayer r.leafIndex bottomLayer) (.inl r.message)
        >>= fun q1 ↦ stepNF (W.hashOf tab) P q1.1.2 q1.2 (keyIndexOnLayer r.leafIndex topLayer)
          (.inr (Gen.treeNode (iOps (W.hashOf tab) P s.starts noEnc) bottomLayer layerHeight
            (keyIndexOnLayer r.leafIndex topLayer).val)) >>= fun q2 ↦
          pure ((Gen.sign (iOps (W.hashOf tab) P s.starts (pairEnc q1.1.1 q2.1.1)) r.leafIndex
              r.message,
            q2.1.2.signed r (Gen.sign (iOps (W.hashOf tab) P s.starts (pairEnc q1.1.1 q2.1.1))
              r.leafIndex r.message)), q2.2) := by
  simp only [encSign, simulateQ_bind, StateT.run_bind, run_simulateQ_logImpl_liftComp,
    simulateQ_hOps_treeNode, simulateQ_hOps_sign, map_pure, pure_bind, encStep_run tab hW,
    simulateQ_pure, StateT.run_pure]

end Run

/-! ## The lazy kernel: B2's handler against the oracle of the randomizer bases -/

/-- The points of the randomizer bases: a key and a layer message. -/
abbrev GDom := KeyIndex × LayerMsg

/-- The randomizer bases as an oracle. -/
abbrev GSpec := GDom →ₒ Randomizer

/-- A probabilistic computation with the same values through `f` and agreeing continuations
on its support. -/
theorem bind_sim {α β δ : Type} {m₁ : ProbComp α} {m₂ : ProbComp β} (f : α → β)
    (hm : f <$> m₁ = m₂) {k₁ : α → ProbComp δ} {k₂ : β → ProbComp δ}
    (hk : ∀ a ∈ support m₁, k₁ a = k₂ (f a)) : m₁ >>= k₁ = m₂ >>= k₂ := by
  rw [← hm, bind_map_left]
  exact OracleComp.bind_congr_of_forall_mem_support m₁ hk

theorem EncSt.record_cache (s : EncSt) (e : KeyIndex) (msg : LayerMsg) (v : EncAns) :
    (s.record e msg v).cache = Function.update s.cache (e, msg) (some v) :=
  rfl

theorem EncSt.signed_cache (s : EncSt) (r : SigningRequest) (sig : Option Signature) :
    (s.signed r sig).cache = s.cache :=
  rfl

section Lazy

variable (h : HashInput → HashOutput) (P : PublicParameter)

/-- One encoding step against the oracle of the bases: cached, else grinding from the base of
`(e, msg)`. -/
noncomputable def encStepL (sx : EncSt × QueryLog EncSpec) (e : KeyIndex) (msg : LayerMsg) :
    OracleComp (unifSpec + GSpec) (EncAns × (EncSt × QueryLog EncSpec)) :=
  match sx.1.cache (e, msg) with
  | some v => pure (v, sx)
  | none => do
    let u ← (liftM ((unifSpec + GSpec).query (.inr (e, msg))) :
      OracleComp (unifSpec + GSpec) Randomizer)
    pure (grindAt h P e msg u, (sx.1.record e msg (grindAt h P e msg u),
      logUpd sx.1 sx.2 e msg (grindAt h P e msg u)))

/-- **B2's handler against the oracle of the bases**, with the challenger transcript in the
state. -/
noncomputable def encK (sx : EncSt × QueryLog EncSpec) (r : SigningRequest) :
    OracleComp (unifSpec + GSpec) (Option Signature × (EncSt × QueryLog EncSpec)) := do
  let p1 ← encStepL h P sx (keyIndexOnLayer r.leafIndex bottomLayer) (.inl r.message)
  let p2 ← encStepL h P p1.2 (keyIndexOnLayer r.leafIndex topLayer)
    (.inr (Gen.treeNode (iOps h P sx.1.starts noEnc) bottomLayer layerHeight
      (keyIndexOnLayer r.leafIndex topLayer).val))
  pure (Gen.sign (iOps h P sx.1.starts (pairEnc p1.1 p2.1)) r.leafIndex r.message,
    (p2.2.1.signed r (Gen.sign (iOps h P sx.1.starts (pairEnc p1.1 p2.1)) r.leafIndex
      r.message), p2.2.2))

/-- The lazily sampled encoding step, explicitly. -/
noncomputable def lazyNF (sx : EncSt × QueryLog EncSpec) (gc : GSpec.QueryCache) (e : KeyIndex)
    (msg : LayerMsg) : ProbComp ((EncAns × (EncSt × QueryLog EncSpec)) × GSpec.QueryCache) :=
  match sx.1.cache (e, msg) with
  | some v => pure ((v, sx), gc)
  | none => ($ᵗ Randomizer) >>= fun u ↦
      pure ((grindAt h P e msg u, (sx.1.record e msg (grindAt h P e msg u),
        logUpd sx.1 sx.2 e msg (grindAt h P e msg u))), gc.cacheQuery (e, msg) u)

/-- **The lazy state follows B2's**: a base was sampled only for a cached encoding. -/
def InvL (x : (EncSt × QueryLog EncSpec) × GSpec.QueryCache) : Prop :=
  ∀ d, x.1.1.cache d = none → x.2 d = none

theorem encStepL_run (sx : EncSt × QueryLog EncSpec) (gc : GSpec.QueryCache) (e : KeyIndex)
    (msg : LayerMsg) (hI : InvL (sx, gc)) :
    (simulateQ (lazyFunOracles GDom Randomizer) (encStepL h P sx e msg)).run gc =
      lazyNF h P sx gc e msg := by
  unfold encStepL lazyNF
  cases hc : sx.1.cache (e, msg) with
  | some v => simp
  | none =>
    have hg : gc (e, msg) = none := hI (e, msg) hc
    have hq : (lazyFunOracles GDom Randomizer (.inr (e, msg))).run gc =
        ($ᵗ Randomizer) >>= fun u ↦ pure (u, gc.cacheQuery (e, msg) u) := by
      rw [lazyFunOracles, randomOracle.run_eq, hg]
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, hq, simulateQ_pure,
      StateT.run_pure, bind_assoc, pure_bind]

theorem lazyNF_map (sx : EncSt × QueryLog EncSpec) (gc : GSpec.QueryCache) (e : KeyIndex)
    (msg : LayerMsg) :
    (fun p ↦ ((p.1.1, p.1.2.1), p.1.2.2)) <$> lazyNF h P sx gc e msg =
      stepNF h P sx.1 sx.2 e msg := by
  unfold lazyNF stepNF
  cases sx.1.cache (e, msg) <;> simp

theorem lazyNF_inv (sx : EncSt × QueryLog EncSpec) (gc : GSpec.QueryCache) (e : KeyIndex)
    (msg : LayerMsg) (hI : InvL (sx, gc)) :
    ∀ p ∈ support (lazyNF h P sx gc e msg), InvL (p.1.2, p.2) := by
  intro p hp
  unfold lazyNF at hp
  cases hc : sx.1.cache (e, msg) with
  | some v =>
    rw [hc, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact hI
  | none =>
    rw [hc, mem_support_bind_iff] at hp
    obtain ⟨u, -, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    intro d hd
    change (Function.update sx.1.cache (e, msg) _) d = none at hd
    by_cases hde : d = (e, msg)
    · subst hde
      rw [Function.update_self] at hd
      exact absurd hd (Option.some_ne_none _)
    · rw [Function.update_of_ne hde] at hd
      change (gc.cacheQuery (e, msg) u) d = none
      rw [QueryCache.cacheQuery_of_ne _ _ hde]
      exact hI d hd

variable {W} (tab : W.Tab) (hW : W.CoinsFair)
include hW

/-- **B2's kernel is the lazy kernel**, through forgetting the cache of the bases. -/
theorem lazyKernel_encK (x : (EncSt × QueryLog EncSpec) × GSpec.QueryCache) (hx : InvL x)
    (r : SigningRequest) :
    Prod.map id Prod.fst <$> lazyKernel (encK (W.hashOf tab) P) x r =
      hKernel tab (encAnswer W P) (encSign W P) x.1 r := by
  obtain ⟨⟨s, lg⟩, gc⟩ := x
  simp only [lazyKernel, hKernel, encSign_run tab hW, encK, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, map_bind, map_pure]
  rw [encStepL_run _ _ _ _ _ _ hx]
  refine bind_sim _ (lazyNF_map _ _ _ _ _ _) fun q1 hq1 ↦ ?_
  rw [encStepL_run _ _ _ _ _ _ (lazyNF_inv _ _ _ _ _ _ hx q1 hq1)]
  exact bind_sim _ (lazyNF_map _ _ _ _ _ _) fun q2 _ ↦ rfl

omit hW in
/-- The lazy kernel keeps the lazy state following B2's. -/
theorem lazyKernel_encK_inv (x : (EncSt × QueryLog EncSpec) × GSpec.QueryCache) (hx : InvL x)
    (r : SigningRequest) :
    ∀ p ∈ support (lazyKernel (encK (W.hashOf tab) P) x r), InvL p.2 := by
  obtain ⟨⟨s, lg⟩, gc⟩ := x
  intro p hp
  simp only [lazyKernel, encK, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    support_map, Set.mem_image] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  rw [encStepL_run _ _ _ _ _ _ hx, mem_support_bind_iff] at ha
  obtain ⟨q1, hq1, ha⟩ := ha
  rw [encStepL_run _ _ _ _ _ _ (lazyNF_inv _ _ _ _ _ _ hx q1 hq1), mem_support_bind_iff] at ha
  obtain ⟨q2, hq2, ha⟩ := ha
  rw [support_pure, Set.mem_singleton_iff] at ha
  subst ha
  exact lazyNF_inv _ _ _ _ _ _ (lazyNF_inv _ _ _ _ _ _ hx q1 hq1) q2 hq2

end Lazy

/-! ## The eager kernel: the ideal signer -/

theorem EncSt.record_sent_new (s : EncSt) (e : KeyIndex) (msg : LayerMsg) (v : EncAns)
    (hs : (s.sent (msg.layer, e)).isNone = true) :
    (s.record e msg v).sent = Function.update s.sent (msg.layer, e) (some (msg.mb, v)) := by
  simp only [EncSt.record, hs, ↓reduceIte]

theorem EncSt.record_sent_old (s : EncSt) (e : KeyIndex) (msg : LayerMsg) (v : EncAns)
    (hs : ¬(s.sent (msg.layer, e)).isNone = true) : (s.record e msg v).sent = s.sent := by
  simp only [EncSt.record, hs, Bool.false_eq_true, ↓reduceIte]

theorem logUpd_new (s : EncSt) (lg : QueryLog EncSpec) (e : KeyIndex) (msg : LayerMsg)
    (v : EncAns) (hs : (s.sent (msg.layer, e)).isNone = true) :
    logUpd s lg e msg v = lg ++ [⟨((msg.layer, e), msg.mb), v⟩] := by
  simp only [logUpd, hs, ↓reduceIte]

theorem logUpd_old (s : EncSt) (lg : QueryLog EncSpec) (e : KeyIndex) (msg : LayerMsg)
    (v : EncAns) (hs : ¬(s.sent (msg.layer, e)).isNone = true) : logUpd s lg e msg v = lg := by
  simp only [logUpd, hs, Bool.false_eq_true, ↓reduceIte]

theorem EncSt.signed_log (s : EncSt) (r : SigningRequest) (sig : Option Signature) :
    (s.signed r sig).log = s.log ++ [⟨r, sig⟩] :=
  rfl

theorem EncSt.signed_sent (s : EncSt) (r : SigningRequest) (sig : Option Signature) :
    (s.signed r sig).sent = s.sent :=
  rfl

theorem EncSt.signed_starts (s : EncSt) (r : SigningRequest) (sig : Option Signature) :
    (s.signed r sig).starts = s.starts :=
  rfl

section Eager

variable (h : HashInput → HashOutput) (P : PublicParameter) (c : Starts) (H : GDom → Randomizer)

/-- The encoding step at the fixed bases `H`. -/
def eagerStep (sx : EncSt × QueryLog EncSpec) (e : KeyIndex) (msg : LayerMsg) :
    EncAns × (EncSt × QueryLog EncSpec) :=
  match sx.1.cache (e, msg) with
  | some v => (v, sx)
  | none => (grindAt h P e msg (H (e, msg)), (sx.1.record e msg (grindAt h P e msg (H (e, msg))),
      logUpd sx.1 sx.2 e msg (grindAt h P e msg (H (e, msg)))))

theorem simulateQ_eager_encStepL (sx : EncSt × QueryLog EncSpec) (e : KeyIndex)
    (msg : LayerMsg) :
    simulateQ (eagerFunOracles H) (encStepL h P sx e msg) = pure (eagerStep h P H sx e msg) := by
  unfold encStepL eagerStep
  cases sx.1.cache (e, msg) with
  | some v => simp
  | none => simp [eagerFunOracles]

/-- B2's handler at the fixed bases `H`. -/
def eagerReq (sx : EncSt × QueryLog EncSpec) (r : SigningRequest) :
    Option Signature × (EncSt × QueryLog EncSpec) :=
  let p1 := eagerStep h P H sx (keyIndexOnLayer r.leafIndex bottomLayer) (.inl r.message)
  let p2 := eagerStep h P H p1.2 (keyIndexOnLayer r.leafIndex topLayer)
    (.inr (Gen.treeNode (iOps h P sx.1.starts noEnc) bottomLayer layerHeight
      (keyIndexOnLayer r.leafIndex topLayer).val))
  (Gen.sign (iOps h P sx.1.starts (pairEnc p1.1 p2.1)) r.leafIndex r.message,
    (p2.2.1.signed r (Gen.sign (iOps h P sx.1.starts (pairEnc p1.1 p2.1)) r.leafIndex
      r.message), p2.2.2))

theorem eagerKernel_encK (sx : EncSt × QueryLog EncSpec) (r : SigningRequest) :
    eagerKernel (encK h P) H sx r = pure (eagerReq h P H sx r) := by
  simp only [eagerKernel, encK, simulateQ_bind, simulateQ_eager_encStepL, pure_bind,
    simulateQ_pure]
  rfl

/-- The message key `keyIndexOnLayer r.leafIndex l` signs for the request `r`. -/
def reqMsg (r : SigningRequest) (l : Layer) : LayerMsg :=
  if l = bottomLayer then .inl r.message
  else .inr (Gen.treeNode (iOps h P c noEnc) bottomLayer layerHeight
    (keyIndexOnLayer r.leafIndex topLayer).val)

theorem reqMsg_layer (r : SigningRequest) (l : Layer) : (reqMsg h P c r l).layer = l := by
  unfold reqMsg
  split_ifs with hl
  · exact hl.symm
  · exact (Quantum.Xmss.eq_topLayer hl).symm

/-- **The invariant of the encoding steps** for the requests `L`: cached encodings are ideal and
their tweaks sent; a sent tweak is in the challenger transcript with the ideal encoding of a
request's message; the transcript has distinct tweaks, all sent. -/
structure InvS (L : List SigningRequest) (sx : EncSt × QueryLog EncSpec) : Prop where
  cache : ∀ e msg v, sx.1.cache (e, msg) = some v →
    v = idealEnc h P H e msg ∧ (sx.1.sent (msg.layer, e)).isSome
  sent : ∀ l e M v, sx.1.sent (l, e) = some (M, v) →
    (⟨((l, e), M), v⟩ : (t : EncSpec.Domain) × EncSpec.Range t) ∈ sx.2 ∧
      ∃ x ∈ L, keyIndexOnLayer x.leafIndex l = e ∧ M = (reqMsg h P c x l).mb ∧
        v = idealEnc h P H e (reqMsg h P c x l)
  valid : EncSaltValid sx.2
  tweaks : ∀ y ∈ sx.2, (sx.1.sent y.1.1).isSome

theorem InvS.mono {L L' : List SigningRequest} (hL : ∀ x ∈ L, x ∈ L')
    {sx : EncSt × QueryLog EncSpec} (hI : InvS h P c H L sx) : InvS h P c H L' sx where
  cache := hI.cache
  sent l e M v hs := by
    obtain ⟨hm, x, hx, hk⟩ := hI.sent l e M v hs
    exact ⟨hm, x, hL x hx, hk⟩
  valid := hI.valid
  tweaks := hI.tweaks

/-- **An encoding step for a request** keeps the invariant, gives the ideal encoding, sends the
tweak, only adds sent tweaks, and keeps the chain starts and the signing transcript. -/
theorem eagerStep_spec (L : List SigningRequest) (sx : EncSt × QueryLog EncSpec)
    (hI : InvS h P c H L sx) (r : SigningRequest) (hr : r ∈ L) (l : Layer) (msg : LayerMsg)
    (hmsg : msg = reqMsg h P c r l) :
    (eagerStep h P H sx (keyIndexOnLayer r.leafIndex l) msg).1 =
        idealEnc h P H (keyIndexOnLayer r.leafIndex l) msg ∧
      InvS h P c H L (eagerStep h P H sx (keyIndexOnLayer r.leafIndex l) msg).2 ∧
      ((eagerStep h P H sx (keyIndexOnLayer r.leafIndex l) msg).2.1.sent
        (l, keyIndexOnLayer r.leafIndex l)).isSome ∧
      (∀ t, (sx.1.sent t).isSome →
        ((eagerStep h P H sx (keyIndexOnLayer r.leafIndex l) msg).2.1.sent t).isSome) ∧
      (eagerStep h P H sx (keyIndexOnLayer r.leafIndex l) msg).2.1.log = sx.1.log ∧
      (eagerStep h P H sx (keyIndexOnLayer r.leafIndex l) msg).2.1.starts = sx.1.starts := by
  set e := keyIndexOnLayer r.leafIndex l
  have hl : msg.layer = l := hmsg ▸ reqMsg_layer h P c r l
  unfold eagerStep
  cases hc : sx.1.cache (e, msg) with
  | some v =>
    obtain ⟨hv, hs⟩ := hI.cache e msg v hc
    exact ⟨hv, hI, hl ▸ hs, fun _ ht ↦ ht, rfl, rfl⟩
  | none =>
    simp only
    set v := grindAt h P e msg (H (e, msg))
    have hcache : ∀ e' msg' v', (sx.1.record e msg v).cache (e', msg') = some v' →
        (e', msg') ≠ (e, msg) → sx.1.cache (e', msg') = some v' := fun e' msg' v' h' hne ↦ by
      rwa [EncSt.record_cache, Function.update_of_ne hne] at h'
    by_cases hs : (sx.1.sent (msg.layer, e)).isNone = true
    · have hsent := EncSt.record_sent_new sx.1 e msg v hs
      have hlog := logUpd_new sx.1 sx.2 e msg v hs
      have hmono : ∀ t, (sx.1.sent t).isSome → ((sx.1.record e msg v).sent t).isSome := by
        intro t ht
        rw [hsent]
        by_cases hte : t = (msg.layer, e)
        · rw [hte, Function.update_self]
          rfl
        · rwa [Function.update_of_ne hte]
      have hnew : ((sx.1.record e msg v).sent (msg.layer, e)) = some (msg.mb, v) := by
        rw [hsent, Function.update_self]
      refine ⟨rfl, ⟨?_, ?_, ?_, ?_⟩, by rw [← hl, hnew]; rfl, hmono, rfl, rfl⟩
      · intro e' msg' v' h'
        by_cases hne : (e', msg') = (e, msg)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hne
          rw [EncSt.record_cache, Function.update_self] at h'
          obtain rfl := Option.some.inj h'
          exact ⟨rfl, by rw [hnew]; rfl⟩
        · obtain ⟨hv, hs'⟩ := hI.cache e' msg' v' (hcache e' msg' v' h' hne)
          exact ⟨hv, hmono _ hs'⟩
      · intro l' e' M v' h'
        rw [hlog]
        by_cases hte : (l', e') = (msg.layer, e)
        · rw [hte, hnew] at h'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hte
          refine ⟨List.mem_append_right _ (List.mem_singleton_self _), r, hr, ?_, ?_, ?_⟩
          all_goals (rw [hl]; try rw [← hmsg]; try rfl)
        · rw [hsent, Function.update_of_ne hte] at h'
          obtain ⟨hm, hx⟩ := hI.sent l' e' M v' h'
          exact ⟨List.mem_append_left _ hm, hx⟩
      · rw [hlog]
        unfold EncSaltValid
        rw [List.map_append, List.nodup_append]
        refine ⟨hI.valid, List.nodup_singleton _, ?_⟩
        intro a ha b hb hab
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb hab
        obtain ⟨y, hy, hya⟩ := List.mem_map.mp ha
        have h1 := hI.tweaks y hy
        rw [hya] at h1
        rw [Option.isNone_iff_eq_none] at hs
        rw [hs] at h1
        exact absurd h1 (by decide)
      · intro y hy
        rw [hlog] at hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hmono _ (hI.tweaks y hy)
        · rw [List.mem_singleton] at hy
          subst hy
          rw [hnew]
          rfl
    · have hsent := EncSt.record_sent_old sx.1 e msg v hs
      have hlog := logUpd_old sx.1 sx.2 e msg v hs
      have hs' : (sx.1.sent (msg.layer, e)).isSome := by
        cases hx : sx.1.sent (msg.layer, e) <;> simp_all
      refine ⟨rfl, ⟨?_, ?_, ?_, ?_⟩, by rw [hsent, ← hl]; exact hs', fun t ht ↦ by rwa [hsent],
        rfl, rfl⟩
      · intro e' msg' v' h'
        rw [hsent]
        by_cases hne : (e', msg') = (e, msg)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hne
          rw [EncSt.record_cache, Function.update_self] at h'
          obtain rfl := Option.some.inj h'
          exact ⟨rfl, hs'⟩
        · exact hI.cache e' msg' v' (hcache e' msg' v' h' hne)
      · intro l' e' M v' h'
        rw [hsent] at h'
        rw [hlog]
        exact hI.sent l' e' M v' h'
      · rw [hlog]
        exact hI.valid
      · intro y hy
        rw [hlog] at hy
        rw [hsent]
        exact hI.tweaks y hy

/-- **The invariant of the eager kernel** at the ideal secret `(P, c, H)`: the chain starts are
`c`, the steps' invariant for the signed requests, and every signed request's tweaks sent. -/
structure InvE (sx : EncSt × QueryLog EncSpec) : Prop where
  starts : sx.1.starts = c
  steps : InvS h P c H (sx.1.log.map Sigma.fst) sx
  req : ∀ x ∈ sx.1.log, ∀ l, (sx.1.sent (l, keyIndexOnLayer x.1.leafIndex l)).isSome

/-- **B2's handler at the bases `H` is the ideal signer** and keeps the invariant. -/
theorem eagerReq_spec (sx : EncSt × QueryLog EncSpec) (hI : InvE h P c H sx)
    (r : SigningRequest) :
    (eagerReq h P H sx r).1 = idealSign h (P, c, H) r ∧
      (eagerReq h P H sx r).2.1.log = sx.1.log ++ [⟨r, idealSign h (P, c, H) r⟩] ∧
      InvE h P c H (eagerReq h P H sx r).2 := by
  have hr : r ∈ sx.1.log.map Sigma.fst ++ [r] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have hI0 : InvS h P c H (sx.1.log.map Sigma.fst ++ [r]) sx :=
    hI.steps.mono h P c H fun x hx ↦ List.mem_append_left _ hx
  have hm1 : (Sum.inl r.message : LayerMsg) = reqMsg h P c r bottomLayer := by
    simp only [reqMsg, ↓reduceIte]
  have hm2 : (Sum.inr (Gen.treeNode (iOps h P sx.1.starts noEnc) bottomLayer layerHeight
      (keyIndexOnLayer r.leafIndex topLayer).val) : LayerMsg) = reqMsg h P c r topLayer := by
    simp only [reqMsg, show topLayer ≠ bottomLayer by decide, ↓reduceIte, hI.starts]
  obtain ⟨hv1, hI1, hs1, hmono1, hlog1, hst1⟩ :=
    eagerStep_spec h P c H _ sx hI0 r hr bottomLayer _ hm1
  obtain ⟨hv2, hI2, hs2, hmono2, hlog2, hst2⟩ :=
    eagerStep_spec h P c H _ _ hI1 r hr topLayer _ hm2
  simp only [eagerReq]
  set p1 := eagerStep h P H sx (keyIndexOnLayer r.leafIndex bottomLayer) (.inl r.message)
  set p2 := eagerStep h P H p1.2 (keyIndexOnLayer r.leafIndex topLayer)
    (.inr (Gen.treeNode (iOps h P sx.1.starts noEnc) bottomLayer layerHeight
      (keyIndexOnLayer r.leafIndex topLayer).val))
  have hsig : Gen.sign (iOps h P sx.1.starts (pairEnc p1.1 p2.1)) r.leafIndex r.message =
      idealSign h (P, c, H) r := by
    rw [hv1, hv2, hI.starts]
    exact sign_iOps_pairEnc h P c H r _ _ rfl rfl
  have hL : ∀ sig, (p2.2.1.signed r sig).log.map Sigma.fst = sx.1.log.map Sigma.fst ++ [r] :=
    fun sig ↦ by rw [EncSt.signed_log, hlog2, hlog1, List.map_append]; rfl
  refine ⟨hsig, by rw [EncSt.signed_log, hlog2, hlog1, hsig], ?_, ?_, ?_⟩
  · exact (hst2.trans hst1).trans hI.starts
  · dsimp only
    rw [hL]
    exact ⟨hI2.cache, hI2.sent, hI2.valid, hI2.tweaks⟩
  · intro x hx l
    dsimp only at hx ⊢
    rw [EncSt.signed_log, hlog2, hlog1] at hx
    rw [EncSt.signed_sent]
    rcases List.mem_append.mp hx with hx | hx
    · exact hmono2 _ (hmono1 _ (hI.req x hx l))
    · rw [List.mem_singleton] at hx
      subst hx
      by_cases hl : l = bottomLayer
      · subst hl
        exact hmono2 _ hs1
      · obtain rfl := Quantum.Xmss.eq_topLayer hl
        exact hs2

end Eager

/-! ## B2's decision -/

section Decision

variable (h : HashInput → HashOutput) (P : PublicParameter)

/-- The digest of an output at the hash `h`. -/
def outDigest (out : EncOut) : Digest :=
  Qrom.Xmss.Over.messageDigest (m := Id) h P out.1.1 out.1.2 out.2.1.1 out.2.2

/-- **The EncTCR$ judge at the hash `h`.** -/
noncomputable def judgeId (lg : QueryLog EncSpec) (out : EncOut) : Bool :=
  holds (EncSaltValid lg ∧ ∃ x ∈ lg, ∃ ρ, x.2 = some (ρ, outDigest h P out) ∧ x.1.1 = out.1 ∧
    (x.1.2, ρ) ≠ out.2)

/-- **B2's decision at the hash `h`**: the judge on B2's output. -/
noncomputable def decB (y : Forgery × (EncSt × QueryLog EncSpec)) : Bool :=
  judgeId h P y.2.2 (encOut (m := Id) h P y.1 y.2.1)

/-- A collision with a sent answer wins. -/
theorem judgeId_of_winsAt (s : EncSt) (lg : QueryLog EncSpec) (hv : EncSaltValid lg)
    (hsent : ∀ l e M v, s.sent (l, e) = some (M, v) →
      (⟨((l, e), M), v⟩ : (t : EncSpec.Domain) × EncSpec.Range t) ∈ lg)
    (l : Layer) (e : KeyIndex) (M : LayerMsg) (ρ' : Randomizer)
    (hw : winsAt s l e M ρ' (Qrom.Xmss.Over.messageDigest (m := Id) h P l e M.bytes ρ') = true) :
    judgeId h P lg ((l, e), M.mb, ρ') = true := by
  unfold winsAt at hw
  rcases hs : s.sent (l, e) with _ | ⟨M0, _ | ⟨ρ, D⟩⟩
  · rw [hs] at hw
    exact absurd hw Bool.false_ne_true
  · rw [hs] at hw
    exact absurd hw Bool.false_ne_true
  · rw [hs] at hw
    obtain ⟨hD, hne⟩ := of_decide_eq_true hw
    exact holds_eq_true.mpr ⟨hv, _, hsent l e M0 _ hs, ρ, by rw [hD]; rfl, rfl, hne⟩

variable (c : Starts) (H : GDom → Randomizer)

theorem reqMsg_of_requestMsg {r : SigningRequest} {l : Layer} {M : LayerMsg}
    (hM : requestMsg (IdealKey.ops h (P, c, H)) r l = some M) : M = reqMsg h P c r l := by
  by_cases hl : l = bottomLayer
  · subst hl
    rw [Extract.requestMsg_bottom hM]
    simp only [reqMsg, ↓reduceIte]
  · obtain rfl := Quantum.Xmss.eq_topLayer hl
    rw [Extract.requestMsg_top hM]
    simp only [reqMsg, show topLayer ≠ bottomLayer by decide, ↓reduceIte]
    exact congrArg Sum.inr (treeNode_iOps h P c (idealEnc h P H) noEnc _ _ _)

/-- **The EncTCR$ event makes B2 win**: on a state of the eager kernel, the event on its signing
transcript is B2's win. -/
theorem decB_of_encDec (sx : EncSt × QueryLog EncSpec) (hI : InvE h P c H sx) (F : Forgery)
    (he : encDec h (P, c, H) (F, sx.1.log) = true) : decB h P (F, sx) = true := by
  obtain ⟨hreuse, -, l, M', hM', M, ρ, D, ⟨x, hx, hk, hreq⟩, henc, hne, hD⟩ :=
    holds_eq_true.mp he
  have hsome := hI.req x hx l
  rw [hk] at hsome
  obtain ⟨⟨M0, v0⟩, hs⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨-, x', hx', hk', hM0, hv0⟩ := hI.steps.sent l _ M0 v0 hs
  have hMx := reqMsg_of_requestMsg h P c H hreq
  have hxx : reqMsg h P c x' l = reqMsg h P c x.1 l := by
    by_cases hl : l = bottomLayer
    · subst hl
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx'
      have hidx : y.1.leafIndex = x.1.leafIndex := Fin.ext (by
        have := congrArg Fin.val (hk'.trans hk.symm)
        simpa [keyIndexOnLayer, bottomLayer] using this)
      rw [List.inj_on_of_nodup_map hreuse hy hx hidx]
    · obtain rfl := Quantum.Xmss.eq_topLayer hl
      simp only [reqMsg, show topLayer ≠ bottomLayer by decide, ↓reduceIte, hk', hk]
  rw [hxx, ← hMx] at hM0 hv0
  have hv : v0 = some (ρ, D) := hv0.trans henc
  subst hv hM0
  have hsent : ∀ l e M v, sx.1.sent (l, e) = some (M, v) →
      (⟨((l, e), M), v⟩ : (t : EncSpec.Domain) × EncSpec.Range t) ∈ sx.2 :=
    fun l e M v hs ↦ (hI.steps.sent l e M v hs).1
  have hne' : ∀ M'' : LayerMsg, M'' = M' →
      (M.mb, ρ) ≠ (M''.mb, (F.signature.layers l).randomizer) :=
    fun M'' hM'' heq ↦ hne (by
      subst hM''
      rw [show M''.bytes = M.bytes from (congrArg Subtype.val (Prod.mk.inj heq).1).symm,
        (Prod.mk.inj heq).2])
  unfold decB encOut
  simp only [Extract.id_bind]
  by_cases hb : winsAt sx.1 bottomLayer (forgedKey F bottomLayer) (.inl F.message)
      (F.signature.layers bottomLayer).randomizer
      (Qrom.Xmss.Over.messageDigest (m := Id) h P bottomLayer (forgedKey F bottomLayer)
        (LayerMsg.bytes (.inl F.message)) (F.signature.layers bottomLayer).randomizer) = true
  · rw [ite_eq_left hb]
    exact judgeId_of_winsAt h P sx.1 sx.2 hI.steps.valid hsent _ _ _ _ hb
  · rw [ite_eq_right hb]
    by_cases hl : l = bottomLayer
    · subst hl
      refine absurd ?_ hb
      have hM : M' = .inl F.message := (Option.some.inj
        ((ite_eq_left rfl : forgedMsg h P F bottomLayer = _).symm.trans hM')).symm
      unfold winsAt
      rw [hs]
      exact decide_eq_true ⟨by rw [← hD, hM]; rfl, hne' _ hM.symm⟩
    · obtain rfl := Quantum.Xmss.eq_topLayer hl
      have hM := hM'
      unfold forgedMsg at hM
      rw [ite_eq_right (show topLayer ≠ bottomLayer by decide), Option.map_eq_some_iff] at hM
      obtain ⟨x0, hroot, rfl⟩ := hM
      rw [show Qrom.Xmss.Over.layerRoot (m := Id) h P bottomLayer (forgedKey F bottomLayer)
        (littleEndianBytes 32 F.message) (F.signature.layers bottomLayer) = some x0 from hroot]
      refine judgeId_of_winsAt h P sx.1 sx.2 hI.steps.valid hsent _ _ _ _ ?_
      unfold winsAt
      rw [hs]
      exact decide_eq_true ⟨hD.symm, hne' _ rfl⟩

end Decision

/-! ## Probabilities at a fixed table -/

section Prob

variable {W} (tab : W.Tab)

/-- A decision of a canonical run is the canonical run with the decision in its leaves. -/
theorem map_kRunQ {Q : Type} {R : OracleSpec.{0, 0} Q} {St : Type} (K : Kernel R St) {α γ : Type}
    (x : QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) α) (s : St) (d : α × St → γ) :
    (kRunQ W K x s).map d =
      kRun W K (X := QuantumComp₂.Leaf (QReg.of Unit) α)
        (fun _ l s ↦ (⟨l.1, d (l.2, s)⟩ : QuantumComp₂.Leaf (QReg.of Unit) γ _)) x s :=
  imap_kRun W K _ d x s

/-- **Lazy sampling of a decision of a canonical run**: the number of functions times the
probability against the lazily sampled kernel from the empty cache is the sum over all functions
of the probabilities against the eagerly sampled kernel, when the decision does not read the
cache. -/
theorem card_mul_probAt_lazy {Q : Type} {R : OracleSpec.{0, 0} Q} {St D U : Type} [Fintype D]
    [DecidableEq D] [Fintype U] [SampleableType U]
    (k : St → (q : Q) → OracleComp (unifSpec + (D →ₒ U)) (R.Range q × St)) {α : Type}
    (x : QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) α) (s : St)
    (d : α × St → Bool) :
    (Fintype.card (D → U) : ℝ≥0∞) *
        W.probAt tab ((kRunQ W (lazyKernel k) x (s, ∅)).map fun p ↦ d (p.1, p.2.1)) =
      ∑ H : D → U, W.probAt tab ((kRunQ W (eagerKernel k H) x s).map d) := by
  set Rt := W.runtime tab
  set ρ := ((SubState.basis ()).prod Rt.init).matrix
  have hc := card_smul_branch_kRun_lazy W Rt k
    (fun u l sc ↦ (⟨l.1, d (l.2, sc.1)⟩ : QuantumComp₂.Leaf (QReg.of Unit) Bool u))
    (fun _ u l s ↦ (⟨l.1, d (l.2, s)⟩ : QuantumComp₂.Leaf (QReg.of Unit) Bool u))
    (fun _ _ _ _ _ ↦ rfl) x s ∅ ⟨QReg.of Unit, rfl, true⟩ ρ
  simp only [tableExtending_empty] at hc
  have hre := congrArg (fun M ↦ (Matrix.trace M).re) hc
  simp only [Matrix.trace_smul, Matrix.trace_sum, Complex.re_sum, smul_eq_mul,
    show ((Fintype.card (D → U) : ℂ)) = ((Fintype.card (D → U) : ℝ) : ℂ) by norm_cast,
    Complex.re_ofReal_mul] at hre
  simp only [probAt_eq_ofReal_trace]
  simp only [QuantumRuntime.branch_run₂]
  simp only [map_kRunQ]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_sum_of_nonneg fun H _ ↦
      DSubInstrument.trace_re_branch_apply_nonneg _ _ ((SubState.basis ()).prod Rt.init).posSemidef]
  exact congrArg ENNReal.ofReal hre

end Prob

/-! ## B2's output and the judge at a fixed table -/

section Output

variable {m n : Type → Type} [Monad m] [Monad n] (F : m →ᵐ n)

theorem mmap_encOut (hash : HashInput → m HashOutput) (P : PublicParameter) (Fg : Forgery)
    (s : EncSt) : F (encOut hash P Fg s) = encOut (fun x ↦ F (hash x)) P Fg s := by
  simp only [encOut, F.mmap_bind, Over.mmap_messageDigest]
  congr 1
  funext db
  simp only [F.mmap_ite, F.mmap_pure, F.mmap_bind, Over.mmap_layerRoot]
  congr 1
  exact bind_congr fun root ↦ by cases root <;> simp only [F.mmap_pure]

end Output

section Game

variable {W} (tab : W.Tab) (hW : W.CoinsFair) (P : PublicParameter)

theorem simulateQ_encOut (Fg : Forgery) (s : EncSt) :
    simulateQ (W.eager tab) (encOut W.hash P Fg s) =
      pure (encOut (m := Id) (W.hashOf tab) P Fg s) := by
  change simulateQ' (W.eager tab) _ = _
  rw [mmap_encOut, Over.comp_eq_pure _ W.hash (W.hashOf tab) (W.simulateQ_hash tab),
    ← mmap_encOut]
  rfl

theorem simulateQ_encJudge (lg : QueryLog EncSpec) (out : EncOut) :
    simulateQ (W.eager tab) (encJudge W P lg out) =
      pure (judgeId (W.hashOf tab) P lg out) := by
  obtain ⟨⟨l, e⟩, M, ρ⟩ := out
  change simulateQ (W.eager tab) (xmssEnc.hash.eval W () P (l, e) (M, ρ) >>= _) = _
  rw [simulateQ_bind, simulateQ_xmssEnc_hash, pure_bind, simulateQ_pure]
  rfl

include hW in
/-- B2's setup at a fixed table: uniform chain starts and the honest root. -/
theorem encPre_run :
    (simulateQ (logImpl tab (encAnswer W P)) (encPre W P)).run [] =
      ($ᵗ Starts) >>= fun c ↦ pure ((c, Gen.root (iOps (W.hashOf tab) P c noEnc)), []) := by
  rw [encPre, run_simulateQ_logImpl_liftComp]
  simp only [simulateQ_bind, W.simulateQ_sample hW, simulateQ_hOps_root, pure_bind,
    simulateQ_pure, map_bind, map_pure]

/-- **B2's game at a fixed table, after the setup**: the decision `decB` of the canonical run
against B2's kernel. -/
theorem probAt_encGame (s0 : Starts × Digest)
    (x : QComp (advSpec W.spec SigningOracleSpec) (QReg.of Unit) (QReg.of Unit) Forgery) :
    W.probAt tab (QuantumComp₂.bind (QuantumComp₂.bind
      (kRunL W (hKernel tab (encAnswer W P) (encSign W P)) x (encSt0 s0) [])
        fun r ↦ ((simulateQ (logImpl tab (encAnswer W P))
          (liftL (encOut W.hash P r.1.1 r.1.2))).run r.2).toQuantumAt (QComp.coinImpl W.spec _))
        fun r ↦ (simulateQ (W.eager tab) (encJudge W P r.2 r.1)).toQuantumAt
          (QComp.coinImpl W.spec _)) =
      W.probAt tab ((kRunQ W (hKernel tab (encAnswer W P) (encSign W P)) x
        (encSt0 s0, [])).map (decB (W.hashOf tab) P)) := by
  refine probAt_eq_of_run₂ W tab ?_
  have hL : (kRunQ W (hKernel tab (encAnswer W P) (encSign W P)) x
      (encSt0 s0, [])).map (decB (W.hashOf tab) P) =
      (kRunL W (hKernel tab (encAnswer W P) (encSign W P)) x (encSt0 s0)
        []).map fun r ↦ decB (W.hashOf tab) P (r.1.1, (r.1.2, r.2)) := by
    rw [kRunL_eq_map]
    simp only [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
    rfl
  rw [hL, QuantumComp₂.bind_assoc, QuantumComp₂.map_eq_bind_pure]
  refine run₂_bind_congr rfl fun r ↦ ?_
  obtain ⟨⟨Fg, s⟩, lg⟩ := r
  dsimp only
  rw [run_simulateQ_logImpl_liftComp, simulateQ_encOut, map_pure,
    run₂_bind_of_classicalOn_pure _ (classicalOn_coinImpl_toQuantumAt _ _)]
  dsimp only
  rw [simulateQ_encJudge]
  exact run₂_eq_of_classicalOn (classicalOn_coinImpl_toQuantumAt _ _) (classicalOn_pure _)

include hW in
/-- A uniform sample of the challenger, followed by a program. -/
theorem probAt_bind_sample (α : Type) [SampleableType α] [Fintype α]
    (k : α → QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
    W.probAt tab (QuantumComp₂.bind ((simulateQ (W.eager tab) (sample W α)).toQuantumAt
      (QComp.coinImpl W.spec _)) k) = ∑' a, (Fintype.card α : ℝ≥0∞)⁻¹ * W.probAt tab (k a) := by
  rw [probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _),
    W.simulateQ_sample hW tab]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton]

variable (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery)

include hW in
/-- B2's game at a fixed table and parameter: the average over uniform chain starts. -/
theorem probAt_slNormal_enc :
    W.probAt tab (QuantumComp₂.bind (slNormal tab (encAnswer W P) (encPre W P)
        (fun s0 ↦ A ⟨s0.2, P⟩) encSt0 (encSign W P) (encPost W P))
      fun r ↦ (simulateQ (W.eager tab) (encJudge W P r.2 r.1)).toQuantumAt
        (QComp.coinImpl W.spec _)) =
      ∑' c, (Fintype.card Starts : ℝ≥0∞)⁻¹ *
        W.probAt tab ((kRunQ W (hKernel tab (encAnswer W P) (encSign W P))
          (A ⟨Gen.root (iOps (W.hashOf tab) P c noEnc), P⟩)
          (encSt0 (c, Gen.root (iOps (W.hashOf tab) P c noEnc)), [])).map
            (decB (W.hashOf tab) P)) := by
  rw [slNormal, QuantumComp₂.bind_assoc,
    probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _), encPre_run tab hW P,
    tsum_prEvent_bind_mul]
  refine tsum_congr fun c ↦ ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, tsum_prEvent_pure_mul]
  exact congrArg _ (probAt_encGame tab P _ _)

include hW in
/-- **B2's success at a fixed table** in normal form: the average over a uniform `P` and uniform
chain starts of the decision of the canonical run against B2's kernel. -/
theorem encTcrSaltSucc_encRed :
    Props.encTcrSaltSucc W xmssEnc tab (encRed W A) =
      ∑' P, (Fintype.card PublicParameter : ℝ≥0∞)⁻¹ * ∑' c, (Fintype.card Starts : ℝ≥0∞)⁻¹ *
        W.probAt tab ((kRunQ W (hKernel tab (encAnswer W P) (encSign W P))
          (A ⟨Gen.root (iOps (W.hashOf tab) P c noEnc), P⟩)
          (encSt0 (c, Gen.root (iOps (W.hashOf tab) P c noEnc)), [])).map
            (decB (W.hashOf tab) P)) := by
  have h1 := probAt_eq_of_run₂ W tab (run₂_game_slRed tab (encTcrSalt W xmssEnc) (encPre W)
    (fun P s0 ↦ A ⟨s0.2, P⟩) (fun _ ↦ encSt0) (encSign W)
    (encPost W))
  refine h1.trans ((probAt_bind_sample tab hW PublicParameter _).trans ?_)
  exact tsum_congr fun P ↦ congrArg _ (probAt_slNormal_enc tab hW P A)

end Game

/-! ## The bound -/

/-- A uniform triple is a uniform first component, then a uniform second, then a uniform
third. -/
theorem sum_triple {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (F : α × β × γ → ℝ≥0∞) :
    ∑ k, (Fintype.card (α × β × γ) : ℝ≥0∞)⁻¹ * F k =
      ∑' a, (Fintype.card α : ℝ≥0∞)⁻¹ * ∑' b, (Fintype.card β : ℝ≥0∞)⁻¹ *
        ((Fintype.card γ : ℝ≥0∞)⁻¹ * ∑ g, F (a, b, g)) := by
  simp only [tsum_fintype, Finset.mul_sum, Fintype.sum_prod_type, Fintype.card_prod,
    Nat.cast_mul]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun g _ ↦ ?_
  rw [ENNReal.mul_inv (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.natCast_ne_top _))) (Or.inl (ENNReal.natCast_ne_top _)),
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [mul_assoc]

/-- An average over `n` choices bounded through `n` times a probability. -/
theorem le_of_card_mul {n : ℕ} (hn : n ≠ 0) {a S T : ℝ≥0∞} (h : (n : ℝ≥0∞) * a = S)
    (hT : T ≤ S) : (n : ℝ≥0∞)⁻¹ * T ≤ a := by
  calc (n : ℝ≥0∞)⁻¹ * T ≤ (n : ℝ≥0∞)⁻¹ * S := by gcongr
    _ = a := by
      rw [← h, ← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn)
        (ENNReal.natCast_ne_top _), one_mul]

section Bound

variable {W} (tab : W.Tab) (hW : W.CoinsFair) (P : PublicParameter) (c : Starts)
  (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery)

theorem idealPk_eq (H : GDom → Randomizer) (h : HashInput → HashOutput) :
    idealPk h (P, c, H) = ⟨Gen.root (iOps h P c noEnc), P⟩ :=
  congrArg (PublicKey.mk · P) (treeNode_iOps h P c (idealEnc h P H) noEnc _ _ _)

theorem invE_init (h : HashInput → HashOutput) (H : GDom → Randomizer) (root : Digest) :
    InvE h P c H (encSt0 (c, root), []) where
  starts := rfl
  steps :=
    { cache := fun _ _ _ hc ↦ by simp [encSt0] at hc
      sent := fun _ _ _ _ hs ↦ by simp [encSt0] at hs
      valid := List.nodup_nil
      tweaks := fun _ hy ↦ absurd hy List.not_mem_nil }
  req := fun _ hx ↦ absurd hx List.not_mem_nil

include hW in
/-- **The bound at fixed `P` and chain starts**: the average over the bases of the ideal EncTCR$
event is at most B2's decision against its kernel. -/
theorem ideal_le_encGame :
    (Fintype.card (GDom → Randomizer) : ℝ≥0∞)⁻¹ * ∑ H : GDom → Randomizer,
        W.probAt tab ((idealRun W tab (P, c, H) A).map (encDec (W.hashOf tab) (P, c, H))) ≤
      W.probAt tab ((kRunQ W (hKernel tab (encAnswer W P) (encSign W P))
        (A ⟨Gen.root (iOps (W.hashOf tab) P c noEnc), P⟩)
        (encSt0 (c, Gen.root (iOps (W.hashOf tab) P c noEnc)), [])).map
          (decB (W.hashOf tab) P)) := by
  set h := W.hashOf tab
  set root := Gen.root (iOps h P c noEnc)
  set x := A ⟨root, P⟩
  have h1 := probAt_eq_of_run₂ W tab (run₂_map_kRunQ_sim (W.runtime tab)
    (hKernel tab (encAnswer W P) (encSign W P)) (lazyKernel (encK h P)) InvL
    Prod.fst (fun s hs q ↦ lazyKernel_encK P tab hW s hs q)
    (fun s hs q ↦ lazyKernel_encK_inv P tab s hs q) x ((encSt0 (c, root), []), ∅)
    (fun _ _ ↦ rfl) (decB h P) (fun p ↦ decB h P (p.1, p.2.1)) fun _ _ _ ↦ rfl)
  have h2 := card_mul_probAt_lazy tab (encK h P) x (encSt0 (c, root), []) (decB h P)
  refine le_of_card_mul Fintype.card_ne_zero
    ((congrArg ((Fintype.card (GDom → Randomizer) : ℝ≥0∞) * ·) h1).symm.trans h2)
    (Finset.sum_le_sum fun H _ ↦ ?_)
  have h3 := probAt_eq_of_run₂ W tab (run₂_map_kRunQ_sim (W.runtime tab)
    (idealKernel h (P, c, H)) (eagerKernel (encK h P) H) (InvE h P c H) (fun sx ↦ sx.1.log)
    (fun sx hs r ↦ by
      rw [eagerKernel_encK, map_pure]
      obtain ⟨hs1, hs2, -⟩ := eagerReq_spec h P c H sx hs r
      change pure ((eagerReq h P H sx r).1, (eagerReq h P H sx r).2.1.log) = _
      rw [hs1, hs2]
      rfl)
    (fun sx hs r p hp ↦ by
      rw [eagerKernel_encK, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact (eagerReq_spec h P c H sx hs r).2.2)
    x (encSt0 (c, root), []) (invE_init P c h H root) (encDec h (P, c, H))
    (fun p ↦ holds (InvE h P c H p.2 ∧ encDec h (P, c, H) (p.1, p.2.1.log) = true))
    fun a s hs ↦ by
      change holds (InvE h P c H s ∧ encDec h (P, c, H) (a, s.1.log) = true) =
        encDec h (P, c, H) (a, s.1.log)
      cases hb : encDec h (P, c, H) (a, s.1.log)
      · cases hh : holds (InvE h P c H s ∧ false = true)
        · rfl
        · exact absurd (holds_eq_true.mp hh).2 Bool.false_ne_true
      · exact holds_eq_true.mpr ⟨hs, rfl⟩)
  rw [idealRun, idealPk_eq]
  refine (le_of_eq h3.symm).trans ?_
  refine (probAt_map_le_sum W tab _ _ {()} (fun _ ↦ decB h P) fun g hg ↦
    ⟨(), Finset.mem_singleton_self _, decB_of_encDec h P c H g.2 (holds_eq_true.mp hg).1 g.1
      (holds_eq_true.mp hg).2⟩).trans_eq (Finset.sum_singleton _ _)

end Bound

/-- **The EncTCR$ reduction (B2)**: at every table of a world with fair coins, the averaged
probability of the EncTCR$ event of the ideal leanXMSS game is at most B2's EncTCR$ success. -/
theorem idealProb_enc_le (hW : W.CoinsFair) (tab : W.Tab)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    idealProb W tab A (fun k ↦ encDec (W.hashOf tab) k) ≤
      Props.encTcrSaltSucc W xmssEnc tab (encRed W A) := by
  rw [encTcrSaltSucc_encRed tab hW A, idealProb,
    sum_triple fun k ↦ W.probAt tab ((idealRun W tab k A).map (encDec (W.hashOf tab) k))]
  refine ENNReal.tsum_le_tsum fun P ↦ ?_
  gcongr with c
  exact ideal_le_encGame tab hW P c A

attribute [local irreducible] encSign encPre encPost hOps in
/-- **The hash calls of B2**: `A`'s hash calls plus the honest work of its setup (`c₀`), of
each signing request (`k`) and of its output (`c₁`). -/
theorem isChargeBound_encRed
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) {c₀ c₁ k n m : ℕ}
    (hpre : ∀ P, QueryCostAtMost (encPre W P) (hcallCost W (R' := EncSpec)) c₀)
    (hσ : ∀ P s q, QueryCostAtMost (encSign W P s q) (hcallCost W (R' := EncSpec)) k)
    (hpost : ∀ P s0 F s, QueryCostAtMost (encPost W P s0 F s) (hcallCost W (R' := EncSpec)) c₁)
    (hn : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m)
    (P : PublicParameter) :
    IPFunctor.IFreeM.IsChargeBound (encRed W A P) (cmdCharge hashCharge)
      (c₀ + ((n + k * m) + c₁)) :=
  isChargeBound_slRed_hash W (encPre W P) (fun s0 ↦ A ⟨s0.2, P⟩) encSt0 (encSign W P)
    (encPost W P) (hpre P) (hσ P) (hpost P) (fun _ ↦ hn _) (fun _ ↦ hm _)

end Quantum.StdModel.Xmss

end
