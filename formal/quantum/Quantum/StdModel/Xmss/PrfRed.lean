module

public import Quantum.StdModel.Xmss.Ideal
public import Quantum.StdModel.Xmss.Eval
public import Quantum.StdModel.Xmss.PrfInst

@[expose] public section

/-!
# B1: the KIM-PRF reduction of leanXMSS (design G0 to G1)

`prfRed W A` is a straight-line reduction against the derived-key KIM-PRF challenger of
leanXMSS (`PrfInst`). Its setup queries the PRF at the parameter format for `P` and computes the
top root with the abstract signer over `prfOps P`, whose secrets are PRF answers (chain starts
from the chain-pair formats, randomizer bases from the randomizer formats) and whose honest work
is the world's Keccak-256; it runs `A` on `⟨root, P⟩`, answers each signing request by the
abstract signer over `prfOps P` (its state: `P` and the signing transcript), and outputs whether
the forgery verifies and wins against the transcript.

* `prfReal_prfRed`: against the real PRF (seed `S_0` uniform), B1 outputs `true` with the SUF-CMA
  winning probability of `A` at the table.
* `prfIdeal_prfRed`: against the ideal PRF, B1 outputs `true` with the ideal winning probability
  `idealProb` (the PRF view of a uniform function is a uniform ideal secret, `sum_prfView`).
* `isChargeBound_prfRed`: B1's hash calls are `A`'s plus its honest work.

Both games collapse onto the ideal run of the PRF view of the answers (`probAt_prfNormal`): at a
fixed table the answers are a function `F` of the formats, the operations answer as
`prfViewOps h F P`, which are the ideal operations of `prfView F`.
-/

open IPFunctor OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss Common
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props

/-! ## The reduction -/

section Red

variable (W : OracleWorld)

/-- The oracles of B1's classical code: the world's and the PRF port. -/
abbrev PrfOracles :=
  W.Oracles + (PrfDom →ₒ HashOutput)

/-- B1's handler state: the public parameter and the signing transcript. -/
abbrev PrfSt :=
  PublicParameter × QueryLog SigningOracleSpec

/-- A computation on the left oracles, lifted to the sum. -/
noncomputable def prfLiftLeft {ι₁ ι₂ : Type} {s₁ : OracleSpec.{0, 0} ι₁}
    {s₂ : OracleSpec.{0, 0} ι₂} {α : Type} (oa : OracleComp s₁ α) : OracleComp (s₁ + s₂) α :=
  liftComp oa (s₁ + s₂)

/-- Keccak-256 in B1's classical code. -/
noncomputable def prfHash (x : HashInput) : OracleComp (PrfOracles W) HashOutput :=
  prfLiftLeft (W.hash x)

/-- A classical query of the PRF at the format `x`. -/
def prfCall (x : PrfDom) : OracleComp (PrfOracles W) HashOutput :=
  liftM ((PrfOracles W).query (.inr x))

/-- **B1's operations** under the parameter `P`: chain starts and randomizer bases from PRF
answers, the rest honest. -/
noncomputable def prfOps (P : PublicParameter) : Ops (OracleComp (PrfOracles W)) where
  chain l e i μ := do
    let o ← prfCall W (.inr (.inl (P, l, e, chainPair i)))
    Qrom.Xmss.Over.chainWalk (prfHash W) P l e i 0 μ (hashHalfForChain i.val o)
  leaf l e ends := Qrom.Xmss.Over.leafHash (prfHash W) P l e ends
  node l k j a b :=
    Qrom.Xmss.Over.tweakableHash (prfHash W) P (.node l (k + 1) j) (nodePayload a b)
  encode e msg := do
    let o ← prfCall W (.inr (.inr (P, e, msg)))
    grind (prfHash W) P msg.layer e msg.bytes (truncateHash o) randomizerAttemptLimit 0

/-- **B1's setup**: the parameter from the PRF, the top root over `prfOps`. -/
noncomputable def prfPre : OracleComp (PrfOracles W) PublicKey := do
  let o ← prfCall W (.inl ())
  let root ← Gen.root (prfOps W (truncateHash o))
  return ⟨root, truncateHash o⟩

/-- B1's initial handler state: the parameter and the empty transcript. -/
def prfSt0 (pk : PublicKey) : PrfSt :=
  (pk.parameter, [])

/-- **B1's signer**: the abstract signer over `prfOps`, logged. -/
noncomputable def prfSigner :
    HHandler W SigningOracleSpec (PrfDom →ₒ HashOutput) PrfSt := fun s r ↦ do
  let a ← Gen.sign (prfOps W s.1) r.leafIndex r.message
  return (a, (s.1, s.2 ++ [⟨r, a⟩]))

/-- **B1's output**: the forgery verifies under the public key and wins against the
transcript. -/
noncomputable def prfPost (pk : PublicKey) (F : Forgery) (s : PrfSt) :
    OracleComp (PrfOracles W) Bool := do
  let v ← Qrom.Xmss.Over.verify (prfHash W) pk F.message F.signature
  return RandomPermutationModel.sufCmaScheme.winningCondition s.2 F && v

/-- **B1, the KIM-PRF reduction**. -/
noncomputable def prfRed (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    Props.Adversary W (PrfDom →ₒ HashOutput) Unit Bool :=
  fun _ ↦ slRed W (prfPre W) A prfSt0 (prfSigner W) (prfPost W)

/-- **B1's hash calls**: `A`'s hash calls, plus the honest work of the setup (`c₀`), of each
signing request (`k`) and of the output (`c₁`). -/
theorem isChargeBound_prfRed
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) {c₀ c₁ k n m : ℕ}
    (hpre : QueryCostAtMost (prfPre W) (hcallCost W (R' := PrfDom →ₒ HashOutput)) c₀)
    (hσ : ∀ s q, QueryCostAtMost (prfSigner W s q) (hcallCost W (R' := PrfDom →ₒ HashOutput)) k)
    (hpost : ∀ pk F s,
      QueryCostAtMost (prfPost W pk F s) (hcallCost W (R' := PrfDom →ₒ HashOutput)) c₁)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (prfRed W A u) (cmdCharge hashCharge) (c₀ + ((n + k * m) + c₁)) :=
  isChargeBound_slRed_hash W (prfPre W) A prfSt0 (prfSigner W) (prfPost W) hpre hσ hpost hn hm

end Red

/-! ## Pure evaluation of the operations -/

section Pure

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {r : Type → Type} [Monad r] [LawfulMonad r]
  (impl : QueryImpl spec r) (hash : HashInput → OracleComp spec HashOutput)
  (h : HashInput → HashOutput) (hh : ∀ x, simulateQ impl (hash x) = pure (h x))
include hh

theorem prfSim_chainWalk (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (start steps : ℕ) (v : Digest) :
    simulateQ impl (Qrom.Xmss.Over.chainWalk hash P l e i start steps v) =
      pure (Qrom.Xmss.Over.chainWalk (m := Id) h P l e i start steps v) := by
  rw [← simulateQ'_apply, Over.mmap_chainWalk, Over.comp_eq_pure (simulateQ' impl) hash h hh,
    ← Over.mmap_chainWalk]
  rfl

theorem prfSim_leafHash (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (ends : ChainIndex → Digest) :
    simulateQ impl (Qrom.Xmss.Over.leafHash hash P l e ends) =
      pure (Qrom.Xmss.Over.leafHash (m := Id) h P l e ends) := by
  rw [← simulateQ'_apply, Over.mmap_leafHash, Over.comp_eq_pure (simulateQ' impl) hash h hh,
    ← Over.mmap_leafHash]
  rfl

theorem prfSim_tweakableHash (P : PublicParameter) (d : LeanXmss.HashDomain) (payload : HashInput) :
    simulateQ impl (Qrom.Xmss.Over.tweakableHash hash P d payload) =
      pure (Qrom.Xmss.Over.tweakableHash (m := Id) h P d payload) := by
  rw [← simulateQ'_apply, Over.mmap_tweakableHash, Over.comp_eq_pure (simulateQ' impl) hash h hh,
    ← Over.mmap_tweakableHash]
  rfl

theorem prfSim_grind (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : HashInput)
    (r0 : Randomizer) (k t : ℕ) :
    simulateQ impl (grind hash P l e M r0 k t) = pure (grind (m := Id) h P l e M r0 k t) := by
  rw [← simulateQ'_apply, mmap_grind, Over.comp_eq_pure (simulateQ' impl) hash h hh,
    ← mmap_grind]
  rfl

theorem prfSim_verify (pk : PublicKey) (msg : Message) (σ : Signature) :
    simulateQ impl (Qrom.Xmss.Over.verify hash pk msg σ) =
      pure (Qrom.Xmss.Over.verify (m := Id) h pk msg σ) := by
  rw [← simulateQ'_apply]
  exact Over.mmap_verify_of_pure (simulateQ' impl) hash h hh pk msg σ

end Pure

/-! ## B1 against answers that are a function of the formats -/

/-- The operations of a function `F` on the formats under the parameter `P`: chain starts and
randomizer bases read off `F` as `prfView` does. -/
def prfViewOps (h : HashInput → HashOutput) (F : PrfDom → HashOutput) (P : PublicParameter) :
    Ops Id :=
  idealOps h P (fun l e i ↦ hashHalfForChain i.val (F (.inr (.inl (P, l, e, chainPair i)))))
    (fun eM ↦ truncateHash (F (.inr (.inr (P, eM)))))

theorem prfViewOps_prfView (h : HashInput → HashOutput) (F : PrfDom → HashOutput) :
    prfViewOps h F (prfView F).1 = (prfView F).ops h :=
  rfl

section Answers

variable (W : OracleWorld) (tab : W.Tab)
  (ans : (x : PrfDom) → OracleComp W.Oracles ((PrfDom →ₒ HashOutput).Range x))
  (F : PrfDom → HashOutput) (hans : ∀ x, simulateQ (W.eager tab) (ans x) = pure (F x))

theorem prfSim_hash (x : HashInput) :
    simulateQ (plainImpl tab ans) (prfHash W x) = pure (W.hashOf tab x) :=
  (QueryImpl.simulateQ_liftComp_left_eq_of_apply (plainImpl tab ans) (W.eager tab)
    (fun _ ↦ rfl) (W.hash x)).trans (W.simulateQ_hash tab x)

theorem prfSim_post (pk : PublicKey) (G : Forgery) (s : PrfSt) :
    simulateQ (plainImpl tab ans) (prfPost W pk G s) =
      pure (RandomPermutationModel.sufCmaScheme.winningCondition s.2 G &&
        Qrom.Xmss.Over.verify (m := Id) (W.hashOf tab) pk G.message G.signature) := by
  simp only [prfPost, simulateQ_bind, prfSim_verify _ _ _ (prfSim_hash W tab ans), pure_bind,
    simulateQ_pure]

include hans

theorem prfSim_call (x : PrfDom) :
    simulateQ (plainImpl tab ans) (prfCall W x) = pure (F x) := by
  rw [prfCall, simulateQ_spec_query]
  exact hans x

theorem prfSim_chain (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex) (μ : ℕ) :
    simulateQ (plainImpl tab ans) ((prfOps W P).chain l e i μ) =
      pure ((prfViewOps (W.hashOf tab) F P).chain l e i μ) := by
  change simulateQ _ (prfCall W _ >>= _) = _
  rw [simulateQ_bind, prfSim_call W tab ans F hans, pure_bind,
    prfSim_chainWalk _ _ _ (prfSim_hash W tab ans)]
  rfl

theorem prfSim_encode (P : PublicParameter) (e : KeyIndex) (msg : LayerMsg) :
    simulateQ (plainImpl tab ans) ((prfOps W P).encode e msg) =
      pure ((prfViewOps (W.hashOf tab) F P).encode e msg) := by
  change simulateQ _ (prfCall W _ >>= _) = _
  rw [simulateQ_bind, prfSim_call W tab ans F hans, pure_bind,
    prfSim_grind _ _ _ (prfSim_hash W tab ans)]
  rfl

theorem prfSim_sign (P : PublicParameter) (idx : LeafIndex) (msg : Message) :
    simulateQ (plainImpl tab ans) (Gen.sign (prfOps W P) idx msg) =
      pure (Gen.sign (prfViewOps (W.hashOf tab) F P) idx msg) :=
  Gen.simulateQ_sign (plainImpl tab ans) (prfOps W P) (prfViewOps (W.hashOf tab) F P)
    (prfSim_chain W tab ans F hans P)
    (fun l e ends ↦ prfSim_leafHash _ _ _ (prfSim_hash W tab ans) P l e ends)
    (fun _ _ _ _ _ ↦ prfSim_tweakableHash _ _ _ (prfSim_hash W tab ans) P _ _)
    (prfSim_encode W tab ans F hans P) idx msg

theorem prfSim_root (P : PublicParameter) :
    simulateQ (plainImpl tab ans) (Gen.root (prfOps W P)) =
      pure (Gen.root (prfViewOps (W.hashOf tab) F P)) :=
  Gen.simulateQ_root (plainImpl tab ans) (prfOps W P) (prfViewOps (W.hashOf tab) F P)
    (prfSim_chain W tab ans F hans P)
    (fun l e ends ↦ prfSim_leafHash _ _ _ (prfSim_hash W tab ans) P l e ends)
    (fun _ _ _ _ _ ↦ prfSim_tweakableHash _ _ _ (prfSim_hash W tab ans) P _ _)
    (prfSim_encode W tab ans F hans P)

theorem prfSim_pre :
    simulateQ (plainImpl tab ans) (prfPre W) = pure (idealPk (W.hashOf tab) (prfView F)) := by
  rw [prfPre, simulateQ_bind, prfSim_call W tab ans F hans, pure_bind, simulateQ_bind,
    prfSim_root W tab ans F hans (truncateHash (F (.inl ()))), pure_bind, simulateQ_pure, idealPk,
    ← prfViewOps_prfView]
  rfl

theorem prfSim_signer (s : PrfSt) (q : SigningRequest) :
    simulateQ (plainImpl tab ans) (prfSigner W s q) =
      pure (Gen.sign (prfViewOps (W.hashOf tab) F s.1) q.leafIndex q.message,
        (s.1, s.2 ++ [⟨q, Gen.sign (prfViewOps (W.hashOf tab) F s.1) q.leafIndex q.message⟩])) := by
  simp only [prfSigner, simulateQ_bind, prfSim_sign W tab ans F hans, pure_bind, simulateQ_pure]

end Answers

/-! ## Collapsing B1's game -/

theorem prf_fst_eq_of_map_fst {α β : Type} {X : ProbComp (α × β)} {a : α}
    (h : Prod.fst <$> X = pure a) {x : α × β} (hx : x ∈ support X) : x.1 = a := by
  have hm : x.1 ∈ support (Prod.fst <$> X) := by
    rw [support_map]
    exact ⟨x, hx, rfl⟩
  rwa [h, support_pure, Set.mem_singleton_iff] at hm

/-- A classical prefix whose first component is determined, followed by programs whose
probabilities at that component do not depend on the second. -/
theorem probAt_bind_fst_prf (W : OracleWorld) (tab : W.Tab) {α β : Type}
    {x : QComp W.spec (QReg.of Unit) (QReg.of Unit) (α × β)} {pa : ProbComp (α × β)}
    (hx : ClassicalOn (W.runtime tab) x pa LinearMap.id) {a : α} (hpa : Prod.fst <$> pa = pure a)
    (k : α × β → QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) {c : ℝ≥0∞}
    (hk : ∀ b, W.probAt tab (k (a, b)) = c) : W.probAt tab (x.bind k) = c := by
  rw [probAt_bind_classicalOn W tab hx k]
  have hp : ∀ p, Pr{let z ← pa}[z = p] * W.probAt tab (k p) = Pr{let z ← pa}[z = p] * c := by
    intro p
    by_cases hp : p ∈ support pa
    · obtain ⟨p1, p2⟩ := p
      have h1 : p1 = a := prf_fst_eq_of_map_fst hpa hp
      subst h1
      rw [hk]
    · rw [prEvent_eq_zero_of_not_mem_support pa hp, zero_mul, zero_mul]
  rw [tsum_congr hp, ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

/-- A uniform classical prefix: the average over its values. -/
theorem probAt_bind_uniform_prf (W : OracleWorld) (tab : W.Tab) {α : Type} [Fintype α]
    {x : QComp W.spec (QReg.of Unit) (QReg.of Unit) α} {pa : ProbComp α}
    (hx : ClassicalOn (W.runtime tab) x pa LinearMap.id)
    (hpa : ∀ a, Pr{let z ← pa}[z = a] = (Fintype.card α : ℝ≥0∞)⁻¹)
    (k : α → QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
    W.probAt tab (x.bind k) = ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * W.probAt tab (k a) := by
  rw [probAt_bind_classicalOn W tab hx k, tsum_fintype]
  simp only [hpa]

/-- The law of a uniform sample, for any sampler instance. -/
theorem prEvent_uniformSample_prf {α : Type} (inst : SampleableType α) [Fintype α] (a : α) :
    Pr{let z ← @uniformSample α inst}[z = a] = (Fintype.card α : ℝ≥0∞)⁻¹ :=
  @SampleableType.prEvent_uniformSample_eq_singleton α inst _ a

theorem simulateQ_prfIdeal_setup (W : OracleWorld) (hW : W.CoinsFair) (tab : W.Tab)
    {Dom U Rng : Type} [Fintype Dom] [SampleableType U] (post : Dom → U → Rng) :
    simulateQ (W.eager tab) (Props.prfIdeal W post).setup = $ᵗ (Dom → U) :=
  W.simulateQ_sample hW tab (Dom → U)

theorem simulateQ_prfReal_setup (W : OracleWorld) (hW : W.CoinsFair) (tab : W.Tab)
    {Key Dom Rng : Type} [SampleableType Key] (F : Key → Dom → OracleComp W.Oracles Rng) :
    simulateQ (W.eager tab) (Props.prfReal W F).setup = $ᵗ Key :=
  W.simulateQ_sample hW tab Key

section Collapse

variable (W : OracleWorld) (tab : W.Tab)
  (ans : (x : PrfDom) → OracleComp W.Oracles ((PrfDom →ₒ HashOutput).Range x))
  (F : PrfDom → HashOutput) (hans : ∀ x, simulateQ (W.eager tab) (ans x) = pure (F x))
include hans

/-- **B1's kernel is the ideal kernel** of the PRF view on the transcript, while its parameter is
the view's. -/
theorem prfKernel_sim (s : PrfSt × QueryLog (PrfDom →ₒ HashOutput)) (hs : s.1.1 = (prfView F).1)
    (q : SigningRequest) :
    Prod.map id (fun s : PrfSt × QueryLog (PrfDom →ₒ HashOutput) ↦ s.1.2) <$>
        hKernel tab ans (prfSigner W) s q =
      idealKernel (W.hashOf tab) (prfView F) s.1.2 q := by
  have e := fst_run_logImpl tab ans (prfSigner W s.1 q) s.2
  rw [prfSim_signer W tab ans F hans, hs, prfViewOps_prfView] at e
  calc Prod.map id (fun s : PrfSt × QueryLog (PrfDom →ₒ HashOutput) ↦ s.1.2) <$>
        hKernel tab ans (prfSigner W) s q =
      (fun a : Option Signature × PrfSt ↦ (a.1, a.2.2)) <$>
        (Prod.fst <$> (simulateQ (logImpl tab ans) (prfSigner W s.1 q)).run s.2) := by
        simp only [hKernel, Functor.map_map]
        rfl
    _ = _ := by
        rw [e, map_pure]
        rfl

theorem prfKernel_inv (s : PrfSt × QueryLog (PrfDom →ₒ HashOutput)) (hs : s.1.1 = (prfView F).1)
    (q : SigningRequest) : ∀ p ∈ support (hKernel tab ans (prfSigner W) s q),
      p.2.1.1 = (prfView F).1 := by
  intro p hp
  have e := fst_run_logImpl tab ans (prfSigner W s.1 q) s.2
  rw [prfSim_signer W tab ans F hans] at e
  simp only [hKernel, support_map, Set.mem_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  rw [prf_fst_eq_of_map_fst e hx]
  exact hs

/-- **B1's game at answers `F`**: B1's normal form followed by the PRF judge wins with the
ideal winning probability at the PRF view of `F`. -/
theorem probAt_prfNormal (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    W.probAt tab (QuantumComp₂.bind (slNormal tab ans (prfPre W) A prfSt0 (prfSigner W)
      (prfPost W)) fun r ↦
        (simulateQ (W.eager tab) (pure r.1 : OracleComp W.Oracles Bool)).toQuantumAt
          (QComp.coinImpl W.spec _)) =
      W.probAt tab ((idealRun W tab (prfView F) A).map (idealWin (W.hashOf tab) (prfView F))) := by
  have hpre : Prod.fst <$> (simulateQ (logImpl tab ans) (prfPre W)).run [] =
      pure (idealPk (W.hashOf tab) (prfView F)) := by
    rw [fst_run_logImpl, prfSim_pre W tab ans F hans]
  unfold slNormal
  rw [QuantumComp₂.bind_assoc]
  refine probAt_bind_fst_prf W tab (classicalOn_coinImpl_toQuantumAt _ _) hpre _ fun b ↦ ?_
  dsimp only
  refine probAt_eq_of_run₂ W tab ?_
  rw [QuantumComp₂.bind_assoc]
  set pk := idealPk (W.hashOf tab) (prfView F)
  let d : (Forgery × PrfSt) × QueryLog (PrfDom →ₒ HashOutput) → Bool := fun r ↦
    RandomPermutationModel.sufCmaScheme.winningCondition r.1.2.2 r.1.1 &&
      Qrom.Xmss.Over.verify (m := Id) (W.hashOf tab) pk r.1.1.message r.1.1.signature
  have hpost : ∀ r : (Forgery × PrfSt) × QueryLog (PrfDom →ₒ HashOutput),
      (W.runtime tab).run₂ .instruments
        (QuantumComp₂.bind (((simulateQ (logImpl tab ans) (prfPost W pk r.1.1 r.1.2)).run
          r.2).toQuantumAt (QComp.coinImpl W.spec (QReg.of Unit))) fun r' ↦
          (simulateQ (W.eager tab) (pure r'.1 : OracleComp W.Oracles Bool)).toQuantumAt
            (QComp.coinImpl W.spec (QReg.of Unit))) =
        (W.runtime tab).run₂ .instruments
          (QuantumComp₂.pure (d r) : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) := by
    intro r
    refine run₂_eq_of_classicalOn (((classicalOn_coinImpl_toQuantumAt _ _).bind_id fun r' ↦
      classicalOn_coinImpl_toQuantumAt _ _).congr ?_ rfl) (classicalOn_pure (d r))
    simp only [simulateQ_pure]
    rw [bind_pure_comp, fst_run_logImpl, prfSim_post W tab ans]
  refine (run₂_bind_congr rfl hpost).trans ?_
  have e : (kRunL W (hKernel tab ans (prfSigner W)) (A pk) (prfSt0 pk) b).bind
      (fun r ↦ QuantumComp₂.pure (d r)) =
        (kRunQ W (hKernel tab ans (prfSigner W)) (A pk) (prfSt0 pk, b)).map
          (fun r ↦ d ((r.1, r.2.1), r.2.2)) := by
    rw [kRunL_eq_map, QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure,
      QuantumComp₂.bind_assoc]
    simp only [QuantumComp₂.pure_bind]
  rw [e]
  exact run₂_map_kRunQ_sim (W.runtime tab) (idealKernel (W.hashOf tab) (prfView F))
    (hKernel tab ans (prfSigner W)) (fun s ↦ s.1.1 = (prfView F).1) (fun s ↦ s.1.2)
    (prfKernel_sim W tab ans F hans) (fun s hs q ↦ prfKernel_inv W tab ans F hans s hs q)
    (A pk) (prfSt0 pk, b) rfl (idealWin (W.hashOf tab) (prfView F)) _ fun _ _ _ ↦ rfl

end Collapse

/-! ## The ideal side -/

/-- **B1 against the ideal PRF** wins with the ideal winning probability. -/
theorem prfIdeal_prfRed (W : OracleWorld) (hW : W.CoinsFair) (tab : W.Tab)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    (Props.prfIdeal W prfTrunc).succAt tab (prfRed W A) =
      idealProb W tab A (fun k ↦ idealWin (W.hashOf tab) k) := by
  unfold Experiment.succAt prfRed
  rw [probAt_eq_of_run₂ W tab (run₂_game_slRed tab (Props.prfIdeal W prfTrunc)
      (fun _ ↦ prfPre W) (fun _ ↦ A) (fun _ ↦ prfSt0) (fun _ ↦ prfSigner W) (fun _ ↦ prfPost W))]
  refine (probAt_bind_uniform_prf W tab (α := PrfDom → HashOutput)
    (classicalOn_coinImpl_toQuantumAt _ _) (fun f ↦ ?_) _).trans
      ((Finset.sum_congr rfl fun f _ ↦ ?_).trans (sum_prfView fun k ↦
        W.probAt tab ((idealRun W tab k A).map (idealWin (W.hashOf tab) k))))
  · rw [simulateQ_prfIdeal_setup W hW tab prfTrunc]
    exact prEvent_uniformSample_prf _ f
  refine congrArg _ ((probAt_prfNormal W tab (fun x ↦ pure (prfTrunc x (f x)))
    (fun x ↦ prfTrunc x (f x)) (fun x ↦ simulateQ_pure _ _) A).trans ?_)
  rw [prfView_prfTrunc]

/-! ## The real side -/

/-- The real PRF's answers at a fixed table, from the derived key `S`. -/
def prfRealAns (h : HashInput → HashOutput) (S : HashOutput) (x : PrfDom) : HashOutput :=
  prfTrunc x (h ((prfFmt x).1 ++ prfKey S ++ (prfFmt x).2))

theorem simulateQ_derivedKimFn (W : OracleWorld) (tab : W.Tab) (S0 : MasterSeed) (x : PrfDom) :
    simulateQ (W.eager tab)
        (Props.derivedKimFn W seedTag prfSeedBytes prfKey prfFmt prfTrunc S0 x) =
      pure (prfRealAns (W.hashOf tab) (W.hashOf tab (seedTag ++ prfSeedBytes S0)) x) := by
  simp only [Props.derivedKimFn, Props.kimFn, simulateQ_bind, simulateQ_map,
    OracleWorld.simulateQ_hash, pure_bind, map_pure]
  rfl

theorem prfView_realAns_fst (h : HashInput → HashOutput) (S : HashOutput) :
    (prfView (prfRealAns h S)).1 =
      truncateHash (h (thInput 0 (keygenDomainFields .parameter) (littleEndianBytes 32 S))) := by
  change truncateHash (prfTrunc (.inl ()) (h ((prfFmt (.inl ())).1 ++ prfKey S ++
    (prfFmt (.inl ())).2))) = _
  rw [truncateHash_prfTrunc, prfInput_param]

theorem prfView_realAns_ops (h : HashInput → HashOutput) (S : HashOutput) :
    (prfView (prfRealAns h S)).ops h = realOps h S (prfView (prfRealAns h S)).1 := by
  set P := (prfView (prfRealAns h S)).1
  have hc : (prfView (prfRealAns h S)).2.1 = fun l e i ↦ hashHalfForChain i.val
      (h (thInput P (keygenDomainFields (.oneTimeChainPair l e (chainPair i)))
        (littleEndianBytes 32 S))) := by
    funext l e i
    change hashHalfForChain i.val (prfTrunc (.inr (.inl (P, l, e, chainPair i)))
      (h ((prfFmt (.inr (.inl (P, l, e, chainPair i)))).1 ++ prfKey S ++
        (prfFmt (.inr (.inl (P, l, e, chainPair i)))).2))) = _
    rw [prfTrunc_chainPair, prfInput_chainPair]
  have hg : (prfView (prfRealAns h S)).2.2 = fun eM ↦ truncateHash
      (h (thInput P (tweakFields 7 0 (layerHi eM.2.layer 0) eM.1)
        (littleEndianBytes 32 S ++ eM.2.bytes))) := by
    funext eM
    change truncateHash (prfTrunc (.inr (.inr (P, eM.1, eM.2)))
      (h ((prfFmt (.inr (.inr (P, eM.1, eM.2)))).1 ++ prfKey S ++
        (prfFmt (.inr (.inr (P, eM.1, eM.2)))).2))) = _
    rw [truncateHash_prfTrunc, prfInput_rnd]
  change idealOps h P (prfView (prfRealAns h S)).2.1 (prfView (prfRealAns h S)).2.2 = _
  rw [hc, hg]
  rfl

/-- **The SUF-CMA game at a seed** is the ideal game at the PRF view of the real answers. -/
theorem probAt_sufGame_prfView (W : OracleWorld) (tab : W.Tab) (S0 : MasterSeed)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    W.probAt tab (game W (xmssScheme W) S0 A) =
      W.probAt tab ((idealRun W tab
        (prfView (prfRealAns (W.hashOf tab) (W.hashOf tab (seedTag ++ prfSeedBytes S0)))) A).map
          (idealWin (W.hashOf tab) (prfView
            (prfRealAns (W.hashOf tab) (W.hashOf tab (seedTag ++ prfSeedBytes S0)))))) := by
  set S := W.hashOf tab (seedTag ++ prfSeedBytes S0)
  set k := prfView (prfRealAns (W.hashOf tab) S)
  have hP := prfView_realAns_fst (W.hashOf tab) S
  have hops := prfView_realAns_ops (W.hashOf tab) S
  have hkeys : Qrom.Xmss.Over.keygenFromSeed (m := Id) (W.hashOf tab) S0 =
      (idealPk (W.hashOf tab) k, ⟨S0, k.1⟩) := by
    have e := keygenFromSeed_id (W.hashOf tab) S0
    simp only at e
    rw [idealPk, hops, hP]
    exact e
  have hker : signKernel W (xmssScheme W) ⟨S0, k.1⟩ tab = idealKernel (W.hashOf tab) k := by
    funext log q
    simp only [signKernel, simulateQ_xmssOver_sign, map_pure, idealKernel, idealSign]
    have hops' : realOps (W.hashOf tab) (W.hashOf tab (seedTag ++ littleEndianBytes 32 S0)) k.1 =
        k.ops (W.hashOf tab) :=
      hops.symm
    rw [sign_id, hops']
  refine probAt_eq_of_run₂ W tab ?_
  rw [run₂_sufGame]
  simp only [simulateQ_xmssOver_generateKeys, toQuantumAt_pure, QuantumComp₂.pure_bind, hkeys,
    hker, simulateQ_xmssOver_verify]
  rw [idealRun, QuantumComp₂.map_eq_bind_pure]
  rfl

/-- **B1 against the real PRF** wins with the SUF-CMA winning probability of `A`. -/
theorem prfReal_prfRed (W : OracleWorld) (hW : W.CoinsFair) (tab : W.Tab)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    (Props.prfReal W (Props.derivedKimFn W seedTag prfSeedBytes prfKey prfFmt prfTrunc)).succAt
      tab (prfRed W A) = winProbAt W (xmssScheme W) tab A := by
  unfold Experiment.succAt winProbAt prfRed
  rw [probAt_eq_of_run₂ W tab (run₂_game_slRed tab
      (Props.prfReal W (Props.derivedKimFn W seedTag prfSeedBytes prfKey prfFmt prfTrunc))
      (fun _ ↦ prfPre W) (fun _ ↦ A) (fun _ ↦ prfSt0) (fun _ ↦ prfSigner W) (fun _ ↦ prfPost W))]
  refine (probAt_bind_uniform_prf W tab (α := MasterSeed)
    (classicalOn_coinImpl_toQuantumAt _ _) (fun S0 ↦ ?_) _).trans
      (Finset.sum_congr rfl fun S0 _ ↦ ?_)
  · rw [simulateQ_prfReal_setup W hW tab]
    exact prEvent_uniformSample_prf _ S0
  rw [show (xmssScheme W).sampleSeed = sampleMasterSeed from rfl, sampleMasterSeed,
    prEvent_uniformSample_prf, probAt_sufGame_prfView W tab S0 A]
  exact congrArg _ (probAt_prfNormal W tab _ _ (simulateQ_derivedKimFn W tab S0) A)

end Quantum.StdModel.Xmss

end
