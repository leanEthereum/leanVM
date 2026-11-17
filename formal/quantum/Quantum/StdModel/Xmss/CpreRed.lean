module

public import Quantum.StdModel.Xmss.Ideal
public import Quantum.StdModel.Xmss.Inst
public import Quantum.StdModel.Xmss.Eval
public import Quantum.StdModel.Xmss.PrfInst
public import Mathlib.Control.Monad.Writer
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# leanXMSS's CPRE reduction B3

`cpreRed W A` is the straight-line reduction from leanXMSS's ideal game to CPRE with adaptive
openings (`Props.cpre W xmssChains noEval`). Its setup reveals `P`, samples the randomizer bases
`g` from its coins and computes the top root from the chain ends (`value j 3`) and honest leaf and
node hashes. Its handler signs with `Gen.sign` over operations whose chain values are `value`
queries and whose encoding is `grind` with `W.hash`, keeping the signing transcript and a copy of
its CPRE transcript. Its output queries the ends of the forged keys' chains and picks a layer and
chain whose forged value walks to the end and either differs from the value it knows at the forged
digit (from an opening at or below it) or has no such opening.

* `idealProb_cpre_le`: at every table of a world with fair coins, the ideal CPRE event is at most
  CPRE success of `cpreRed W A`. The challenger's `P` and chain starts and the reduction's `g` form
  the uniform ideal key; at a fixed table the reduction's kernel is deterministic and collapses onto
  `idealKernel`, its openings are `Opened` of the transcript, and on the event the judge accepts.
* `isChargeBound_cpreRed`: the reduction's hash calls.

The fixed-table evaluation runs the signer over a writer monad of CPRE transcript entries (`LW`):
the reduction's operations, read by the challenger, are the writer operations `oW` sent through
`toSt`, so that a handler call answers as the ideal signer and appends what `oW` writes.
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props

namespace CpreRed

/-! ## The CPRE game of leanXMSS -/

/-- The chains: layer, key and chain index. -/
abbrev CJ := Layer × KeyIndex × ChainIndex

/-- The CPRE queries. -/
abbrev CQ := CpreQuery CJ XTw Empty (fun _ ↦ Unit)

/-- The CPRE ports. -/
abbrev CSpec := CpreSpec PublicParameter XTw CJ Digest Empty (fun _ ↦ Unit) Digest

/-- A CPRE transcript. -/
abbrev CLog := QueryLog CSpec

/-- An entry of a CPRE transcript. -/
abbrev CEnt := (q : CQ) × CSpec.Range q

/-- The chain, position and answer of a value entry. -/
def valEntry : CEnt → Option (CJ × ℕ × Digest)
  | ⟨.value j μ, v⟩ => some (j, μ, v)
  | _ => none

theorem asValue_eq (e : CEnt) : e.1.asValue = (valEntry e).map fun t ↦ (t.1, t.2.1) := by
  rcases e with ⟨q | l | _, _⟩
  · rfl
  · exact l.elim
  · rfl

/-- The entry of a `reveal` query. -/
def revealEnt (P : PublicParameter) : CEnt :=
  ⟨.reveal, P⟩

/-- The entry of a value query. -/
def valEnt (j : CJ) (μ : ℕ) (v : Digest) : CEnt :=
  ⟨.value j μ, v⟩

/-- The chain starts as an ideal secret's starts. -/
def cOf (s : CJ → Digest) : Layer → KeyIndex → ChainIndex → Digest :=
  fun l e i ↦ s (l, e, i)

/-- The chain starts of the CPRE challenger and of the ideal secret. -/
def startsEquiv : (CJ → Digest) ≃ (Layer → KeyIndex → ChainIndex → Digest) where
  toFun := cOf
  invFun c j := c j.1 j.2.1 j.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Chain walks -/

/-- A walk of `k` more steps continues a walk of `n` steps. -/
theorem walkChain_add_id {K : ℕ} (step : Fin K → Digest → Id Digest) (start n : ℕ) :
    ∀ (k : ℕ) (x : Digest),
      walkChain step start (n + k) x = walkChain step (start + n) k (walkChain step start n x)
  | 0, _ => rfl
  | k + 1, x => by
    rw [show n + (k + 1) = n + k + 1 from rfl, walkChain_succ_id, walkChain_succ_id,
      walkChain_add_id step start n k x, Nat.add_assoc start n k]

theorem chainWalk_split (h : HashInput → HashOutput) (P : PublicParameter) (l : Layer)
    (e : KeyIndex) (i : ChainIndex) {ν μ : ℕ} (hνμ : ν ≤ μ) (x : Digest) :
    Qrom.Xmss.Over.chainWalk (m := Id) h P l e i ν (μ - ν)
        (Qrom.Xmss.Over.chainWalk (m := Id) h P l e i 0 ν x) =
      Qrom.Xmss.Over.chainWalk (m := Id) h P l e i 0 μ x := by
  have h1 := walkChain_add_id (fun step value ↦ Qrom.Xmss.Over.tweakableHash (m := Id) h P
    (.chain l e step) (Verification.chainPayload i value)) 0 ν (μ - ν) x
  rw [Nat.add_sub_cancel' hνμ, Nat.zero_add] at h1
  exact h1.symm

/-- A walk from the start past the chain end gives `0`. -/
theorem chainWalk_beyond (h : HashInput → HashOutput) (P : PublicParameter) (l : Layer)
    (e : KeyIndex) (i : ChainIndex) {μ : ℕ} (hμ : chainLength - 1 < μ) (x : Digest) :
    Qrom.Xmss.Over.chainWalk (m := Id) h P l e i 0 μ x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, μ = n + 1 := ⟨μ - 1, by omega⟩
  unfold Qrom.Xmss.Over.chainWalk
  simp only [walkChain_succ_id, show ¬(0 + n < chainLength - 1) by omega, ↓reduceDIte]
  rfl

/-- The CPRE walk evaluated with a hash function. -/
def walkT (h : HashInput → HashOutput) (P : PublicParameter) (j : CJ) : ℕ → ℕ → Digest → Digest
  | _, 0, x => x
  | μ, n + 1, x =>
    walkT h P j (μ + 1) n (truncateHash (h (xmssChains.step.layout () P (xmssChains.tweak j μ) x)))

theorem simulateQ_walk (W : OracleWorld) (tab : W.Tab) (P : PublicParameter) (j : CJ) :
    ∀ (μ n : ℕ) (x : Digest), simulateQ (W.eager tab) (xmssChains.walk W P j μ n x) =
      pure (walkT (W.hashOf tab) P j μ n x)
  | μ, 0, x => by
    rw [Props.Chains.walk, simulateQ_pure]
    rfl
  | μ, n + 1, x => by
    rw [Props.Chains.walk, simulateQ_bind, simulateQ_eval, pure_bind, simulateQ_walk W tab P j]
    rfl

theorem walkT_eq (W : OracleWorld) (tab : W.Tab) (P : PublicParameter) (j : CJ) (μ n : ℕ)
    (x : Digest) (h : μ + n ≤ chainLength - 1) :
    walkT (W.hashOf tab) P j μ n x =
      Qrom.Xmss.Over.chainWalk (m := Id) (W.hashOf tab) P j.1 j.2.1 j.2.2 μ n x := by
  have h1 := (simulateQ_walk W tab P j μ n x).symm.trans
    (simulateQ_xmssChains_walk W tab P j.1 j.2.1 j.2.2 μ n x h)
  exact (OracleComp.pure_inj _ _).mp h1

/-! ## The reduction's operations, over any monad -/

section Ops

variable {m : Type → Type} [Monad m]

/-- **The reduction's operations**: chain values below the end by `val`, the leaf and node by
`hash`, the encoding by grinding with `hash` from the base `g`. -/
def bOps (hash : HashInput → m HashOutput) (val : CJ → ℕ → m Digest) (P : PublicParameter)
    (g : KeyIndex × LayerMsg → Randomizer) : Ops m where
  chain l e i μ := if μ ≤ chainLength - 1 then val (l, e, i) μ else pure 0
  leaf l e ends := Qrom.Xmss.Over.leafHash hash P l e ends
  node l k j a b := Qrom.Xmss.Over.tweakableHash hash P (.node l (k + 1) j) (nodePayload a b)
  encode e msg := grind hash P msg.layer e msg.bytes (g (e, msg)) randomizerAttemptLimit 0

theorem bOps_map {n : Type → Type} [Monad n] (F : m →ᵐ n) (hash : HashInput → m HashOutput)
    (val : CJ → ℕ → m Digest) (P : PublicParameter) (g : KeyIndex × LayerMsg → Randomizer) :
    (bOps hash val P g).map F = bOps (fun x ↦ F (hash x)) (fun j μ ↦ F (val j μ)) P g := by
  unfold Ops.map bOps
  congr 1
  · funext l e i μ
    by_cases hμ : μ ≤ chainLength - 1
    · simp only [hμ, ↓reduceIte]
    · simp only [hμ, ↓reduceIte, F.mmap_pure]
  · funext l e ends
    exact Over.mmap_leafHash F hash P l e ends
  · funext l k j a b
    exact Over.mmap_tweakableHash F hash P _ _
  · funext e msg
    exact mmap_grind F hash P _ e _ _ _ _

end Ops

/-- The chain value the challenger answers to `value j μ`. -/
def vAt (h : HashInput → HashOutput) (P : PublicParameter) (s : CJ → Digest) (j : CJ) (μ : ℕ) :
    Digest :=
  Qrom.Xmss.Over.chainWalk (m := Id) h P j.1 j.2.1 j.2.2 0 (min μ (chainLength - 1)) (s j)

theorem bOps_id (h : HashInput → HashOutput) (P : PublicParameter) (s : CJ → Digest)
    (g : KeyIndex × LayerMsg → Randomizer) :
    bOps (m := Id) h (vAt h P s) P g = idealOps h P (cOf s) g := by
  unfold bOps idealOps
  congr 1
  funext l e i μ
  by_cases hμ : μ ≤ chainLength - 1
  · simp only [hμ, ↓reduceIte]
    unfold vAt
    rw [min_eq_left hμ]
    rfl
  · simp only [hμ, ↓reduceIte]
    exact (chainWalk_beyond h P l e i (Nat.lt_of_not_le hμ) _).symm

/-! ## The writer monad of transcript entries -/

/-- Programs that write CPRE transcript entries. -/
abbrev LW := WriterT CLog Id

/-- The value and the written entries. -/
def lw {α : Type} (x : LW α) : α × CLog :=
  x.run

/-- The program with value `a` writing `w`. -/
def mkW {α : Type} (a : α) (w : CLog) : LW α :=
  WriterT.mk ((a, w) : α × CLog)

theorem lw_pure {α : Type} (a : α) : lw (pure a : LW α) = (a, []) :=
  rfl

theorem lw_bind {α β : Type} (x : LW α) (f : α → LW β) :
    lw (x >>= f) = ((lw (f (lw x).1)).1, (lw x).2 ++ (lw (f (lw x).1)).2) :=
  rfl

theorem lw_mkW {α : Type} (a : α) (w : CLog) : lw (mkW a w) = (a, w) :=
  rfl

theorem lw_pure_bind {α β : Type} (a : α) (f : α → LW β) : (pure a >>= f : LW β) = f a :=
  rfl

/-- The value of a writer program. -/
def fstH : LW →ᵐ Id where
  toFun _ x := (lw x).1
  toFun_pure' _ := rfl
  toFun_bind' _ _ := rfl

theorem fstH_apply {α : Type} (x : LW α) : fstH x = (lw x).1 :=
  rfl

/-- **A writer program run against the challenger**: its value and entries, the entries appended
to the challenger's transcript. -/
noncomputable def toSt : LW →ᵐ WriterT CLog (StateT CLog ProbComp) where
  toFun _ x := WriterT.mk (fun log ↦ pure (lw x, log ++ (lw x).2) : StateT CLog ProbComp _)
  toFun_pure' a := by
    refine StateT.ext fun log ↦ ?_
    show (pure ((a, []), log ++ []) : ProbComp _) = pure ((a, []), log)
    rw [List.append_nil]
  toFun_bind' x f := by
    refine StateT.ext fun log ↦ ?_
    show (pure (lw (x >>= f), log ++ (lw (x >>= f)).2) : ProbComp _) =
      (pure ((lw x), log ++ (lw x).2) : ProbComp _) >>= fun p ↦
        (fun q ↦ ((q.1.1, p.1.2 ++ q.1.2), q.2)) <$>
          (pure (lw (f p.1.1), p.2 ++ (lw (f p.1.1)).2) : ProbComp _)
    rw [pure_bind, map_pure, lw_bind, List.append_assoc]

/-- A morphism of monads under the writer. -/
def wLift {M N : Type → Type} [Monad M] [Monad N] [LawfulMonad M] [LawfulMonad N] (F : M →ᵐ N) :
    WriterT CLog M →ᵐ WriterT CLog N where
  toFun _ x := WriterT.mk (F x.run)
  toFun_pure' a := F.mmap_pure (a, [])
  toFun_bind' x f := by
    show F (x.run >>= fun p ↦ (fun q ↦ (q.1, p.2 ++ q.2)) <$> (f p.1).run) =
      F x.run >>= fun p ↦ (fun q ↦ (q.1, p.2 ++ q.2)) <$> F (f p.1).run
    rw [F.mmap_bind]
    congr 1
    funext p
    exact F.mmap_map _ _

/-! ## Entries written by programs -/

/-- Every entry the program writes satisfies `Q`. -/
def Wr (Q : CEnt → Prop) {α : Type} (x : LW α) : Prop :=
  ∀ e ∈ (lw x).2, Q e

theorem wr_pure (Q : CEnt → Prop) {α : Type} (a : α) : Wr Q (pure a : LW α) := by
  intro e he
  rw [lw_pure] at he
  exact absurd he List.not_mem_nil

theorem wr_bind {Q : CEnt → Prop} {α β : Type} {x : LW α} {f : α → LW β} (hx : Wr Q x)
    (hf : Wr Q (f (lw x).1)) : Wr Q (x >>= f) := by
  intro e he
  rw [lw_bind] at he
  rcases List.mem_append.mp he with he | he
  · exact hx e he
  · exact hf e he

theorem wr_mono {Q Q' : CEnt → Prop} (hQ : ∀ e, Q e → Q' e) {α : Type} {x : LW α}
    (hx : Wr Q x) : Wr Q' x :=
  fun e he ↦ hQ e (hx e he)

theorem wr_sequenceFin {Q : CEnt → Prop} {α : Type} :
    ∀ {n : ℕ} (c : Fin n → LW α), (∀ i, Wr Q (c i)) → Wr Q (sequenceFin c)
  | 0, _, _ => wr_pure Q _
  | _ + 1, _, hc => wr_bind (hc 0) (wr_bind (wr_sequenceFin _ fun i ↦ hc i.succ) (wr_pure Q _))

theorem fst_sequenceFin {α : Type} {n : ℕ} (c : Fin n → LW α) :
    (lw (sequenceFin c)).1 = fun i ↦ (lw (c i)).1 :=
  (mmap_sequenceFin fstH c).trans (Extract.sequenceFin_id _)

theorem wr_of_eq_pure (Q : CEnt → Prop) {α : Type} {x : LW α} {a : α} (hx : x = pure a) :
    Wr Q x :=
  hx ▸ wr_pure Q a

/-! ## The reduction -/

/-- The randomizer bases. -/
abbrev Bases := KeyIndex × LayerMsg → Randomizer

/-- The handler state: `P`, the bases, the signing transcript and the copy of the CPRE
transcript. -/
abbrev St := PublicParameter × Bases × QueryLog SigningOracleSpec × CLog

/-- The setup's output: `P`, the bases, the public key and the CPRE transcript so far. -/
abbrev S0 := PublicParameter × Bases × PublicKey × CLog

section Red

variable (W : OracleWorld)

/-- A world computation in the reduction's algorithms. -/
def liftR {α : Type} (oa : OracleComp W.Oracles α) : OracleComp (W.Oracles + CSpec) α :=
  simulateQ (fun t ↦ liftM ((W.Oracles + CSpec).query (.inl t))) oa

/-- A world hash call of the reduction. -/
noncomputable def hashB (x : HashInput) : OracleComp (W.Oracles + CSpec) HashOutput :=
  liftR W (W.hash x)

/-- A CPRE query of the reduction. -/
def queryB (q : CQ) : OracleComp (W.Oracles + CSpec) (CSpec.Range q) :=
  liftM ((W.Oracles + CSpec).query (.inr q))

/-- The `reveal` query. -/
def queryReveal : OracleComp (W.Oracles + CSpec) PublicParameter :=
  queryB W .reveal

/-- A world hash call, writing nothing. -/
noncomputable def hashC (x : HashInput) :
    WriterT CLog (OracleComp (W.Oracles + CSpec)) HashOutput :=
  WriterT.mk ((fun a ↦ (a, ([] : CLog))) <$> hashB W x)

/-- A CPRE query, writing its entry. -/
def queryC (q : CQ) : WriterT CLog (OracleComp (W.Oracles + CSpec)) (CSpec.Range q) :=
  WriterT.mk (queryB W q >>= fun a ↦ pure (a, [⟨q, a⟩]))

/-- A value query, writing its entry. -/
def queryV (j : CJ) (μ : ℕ) : WriterT CLog (OracleComp (W.Oracles + CSpec)) Digest :=
  queryC W (.value j μ)

/-- **The reduction's operations**: chain values by `value` queries, hashes by `W.hash`, each
query copied. -/
noncomputable def cOps (P : PublicParameter) (g : Bases) :
    Ops (WriterT CLog (OracleComp (W.Oracles + CSpec))) :=
  bOps (hashC W) (queryV W) P g

/-- **The setup**: reveal `P`, sample the bases, compute the root. -/
noncomputable def pre : OracleComp (W.Oracles + CSpec) S0 := do
  let P ← queryReveal W
  let g ← liftR W (sample W Bases)
  let p ← (Gen.root (cOps W P g)).run
  pure (P, g, ⟨p.1, P⟩, [revealEnt P] ++ p.2)

/-- The handler's initial state. -/
def st0 (s0 : S0) : St :=
  (s0.1, s0.2.1, [], s0.2.2.2)

/-- **The handler**: the signer over the reduction's operations, the answer and the copied
entries kept. -/
noncomputable def handler : HHandler W SigningOracleSpec CSpec St := fun st r ↦ do
  let p ← (Gen.sign (cOps W st.1 st.2.1) r.leafIndex r.message).run
  pure (p.1, (st.1, st.2.1, st.2.2.1 ++ [⟨r, p.1⟩], st.2.2.2 ++ p.2))

/-- The chain ends of the forged keys. -/
noncomputable def endsQ (F : Forgery) :
    OracleComp (W.Oracles + CSpec) (Layer → ChainIndex → Digest) :=
  Prod.fst <$> (sequenceFin fun l : Layer ↦ sequenceFin fun i : ChainIndex ↦
    queryV W (l, forgedKey F l, i) (chainLength - 1)).run

end Red

/-! ## The reduction at a fixed table -/

theorem simulateQ_stateLift {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec ProbComp) (oa : OracleComp spec α) :
    simulateQ (fun t ↦ (StateT.lift (impl t) : StateT σ ProbComp (spec.Range t))) oa =
      StateT.lift (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    refine StateT.ext fun s ↦ ?_
    simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query]
    refine StateT.ext fun s ↦ ?_
    simp [StateT.run_bind, ih]

section Table

variable (W : OracleWorld) (tab : W.Tab)

theorem simulateQ_logImpl_liftR (ans : (q : CQ) → OracleComp W.Oracles (CSpec.Range q))
    {α : Type} (oa : OracleComp W.Oracles α) :
    simulateQ (logImpl tab ans) (liftR W oa) = StateT.lift (simulateQ (W.eager tab) oa) := by
  refine Eq.trans ?_ (simulateQ_stateLift (W.eager tab) oa)
  induction oa using OracleComp.inductionOn with
  | pure a => simp [liftR]
  | query_bind t k ih =>
    simp only [liftR, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    simp only [ih]
    rfl

theorem simulateQ_logImpl_queryB (ans : (q : CQ) → OracleComp W.Oracles (CSpec.Range q))
    (q : CQ) :
    simulateQ (logImpl tab ans) (queryB W q) =
      fun log ↦ (fun a ↦ (a, log ++ [⟨q, a⟩])) <$> simulateQ (W.eager tab) (ans q) :=
  simulateQ_spec_query (impl := logImpl tab ans) (Sum.inr q)

variable (P0 : PublicParameter) (s : CJ → Digest)

/-- The CPRE challenger's state for the parameter `P0` and the starts `s`. -/
def stC : (cpre W xmssChains noEval).State :=
  (P0, s)

/-- The CPRE challenger's answers for the parameter `P0` and the starts `s`. -/
noncomputable abbrev ansC : (q : CQ) → OracleComp W.Oracles (CSpec.Range q) :=
  (cpre W xmssChains noEval).answer (stC W P0 s)

/-- The reduction's oracles against the challenger, as a monad morphism. -/
noncomputable abbrev FL : OracleComp (W.Oracles + CSpec) →ᵐ StateT CLog ProbComp :=
  simulateQ' (logImpl tab (ansC W P0 s))

/-- A value entry with the challenger's answer. -/
def valW (j : CJ) (μ : ℕ) : LW Digest :=
  mkW (vAt (W.hashOf tab) P0 s j μ) [valEnt j μ (vAt (W.hashOf tab) P0 s j μ)]

/-- **The reduction's operations read by the challenger**, as writer programs. -/
def oW (g : Bases) : Ops LW :=
  bOps (fun x ↦ pure (W.hashOf tab x)) (valW W tab P0 s) P0 g

theorem wLift_hashC (x : HashInput) :
    wLift (FL W tab P0 s) (hashC W x) = toSt (pure (W.hashOf tab x)) := by
  refine StateT.ext fun log ↦ ?_
  show (simulateQ (logImpl tab (ansC W P0 s)) ((fun a ↦ (a, ([] : CLog))) <$> hashB W x)).run
      log = pure ((W.hashOf tab x, []), log ++ [])
  rw [simulateQ_map, hashB, simulateQ_logImpl_liftR, W.simulateQ_hash, List.append_nil]
  simp

theorem ansC_value (j : CJ) (μ : ℕ) :
    simulateQ (W.eager tab) (ansC W P0 s (.value j μ)) = pure (vAt (W.hashOf tab) P0 s j μ) :=
  simulateQ_xmssChains_walk W tab P0 j.1 j.2.1 j.2.2 0 _ (s j)
    (by rw [Nat.zero_add]; exact min_le_right _ _)

theorem queryC_run (q : CQ) :
    (queryC W q).run = queryB W q >>= fun a ↦ pure (a, [(⟨q, a⟩ : CEnt)]) :=
  rfl

theorem wLift_queryV (j : CJ) (μ : ℕ) :
    wLift (FL W tab P0 s) (queryV W j μ) = toSt (valW W tab P0 s j μ) := by
  refine StateT.ext fun log ↦ ?_
  show (simulateQ (logImpl tab (ansC W P0 s)) (queryC W (.value j μ)).run).run log =
    (pure (lw (valW W tab P0 s j μ), log ++ (lw (valW W tab P0 s j μ)).2) : ProbComp _)
  rw [queryC_run, simulateQ_bind, simulateQ_logImpl_queryB, ansC_value]
  simp
  rfl

theorem cOps_map (g : Bases) :
    (cOps W P0 g).map (wLift (FL W tab P0 s)) = (oW W tab P0 s g).map toSt := by
  rw [cOps, oW, bOps_map, bOps_map]
  have h1 : (fun x ↦ wLift (FL W tab P0 s) (hashC W x)) =
      fun x ↦ toSt (pure (W.hashOf tab x)) :=
    funext (wLift_hashC W tab P0 s)
  have h2 : (fun j μ ↦ wLift (FL W tab P0 s) (queryV W j μ)) =
      fun j μ ↦ toSt (valW W tab P0 s j μ) :=
    funext fun j ↦ funext (wLift_queryV W tab P0 s j)
  rw [h1, h2]

theorem oW_fst (g : Bases) : (oW W tab P0 s g).map fstH = idealOps (W.hashOf tab) P0 (cOf s) g :=
  (bOps_map fstH _ _ P0 g).trans (bOps_id (W.hashOf tab) P0 s g)

theorem run_wLift {α : Type} (x : WriterT CLog (OracleComp (W.Oracles + CSpec)) α) :
    simulateQ (logImpl tab (ansC W P0 s)) x.run = (wLift (FL W tab P0 s) x).run :=
  rfl

theorem run_toSt {α : Type} (x : LW α) :
    (toSt x).run = fun log ↦ pure (lw x, log ++ (lw x).2) :=
  rfl

theorem run_run_toSt {α : Type} (x : LW α) (log : CLog) :
    StateT.run (toSt x).run log = pure (lw x, log ++ (lw x).2) :=
  rfl

theorem simulateQ_sign (g : Bases) (idx : LeafIndex) (M : Message) :
    simulateQ (logImpl tab (ansC W P0 s)) (Gen.sign (cOps W P0 g) idx M).run =
      (toSt (Gen.sign (oW W tab P0 s g) idx M)).run := by
  rw [run_wLift, Gen.mmap_sign, cOps_map, ← Gen.mmap_sign]

theorem simulateQ_root (g : Bases) :
    simulateQ (logImpl tab (ansC W P0 s)) (Gen.root (cOps W P0 g)).run =
      (toSt (Gen.root (oW W tab P0 s g))).run := by
  rw [run_wLift, Gen.mmap_root, cOps_map, ← Gen.mmap_root]

theorem fst_sign (g : Bases) (idx : LeafIndex) (M : Message) :
    (lw (Gen.sign (oW W tab P0 s g) idx M)).1 =
      Gen.sign (idealOps (W.hashOf tab) P0 (cOf s) g) idx M := by
  rw [← fstH_apply, Gen.mmap_sign, oW_fst]

theorem fst_root (g : Bases) :
    (lw (Gen.root (oW W tab P0 s g))).1 = Gen.root (idealOps (W.hashOf tab) P0 (cOf s) g) := by
  rw [← fstH_apply, Gen.mmap_root, oW_fst]

/-- **The handler at the table**: the ideal signer's answer, the entries of `oW` appended. -/
theorem hKernel_handler (st : St) (log : CLog) (r : SigningRequest) (hP : st.1 = P0) :
    hKernel tab (ansC W P0 s) (handler W) (st, log) r =
      pure ((lw (Gen.sign (oW W tab P0 s st.2.1) r.leafIndex r.message)).1,
        ((st.1, st.2.1, st.2.2.1 ++
          [⟨r, (lw (Gen.sign (oW W tab P0 s st.2.1) r.leafIndex r.message)).1⟩],
          st.2.2.2 ++ (lw (Gen.sign (oW W tab P0 s st.2.1) r.leafIndex r.message)).2),
          log ++ (lw (Gen.sign (oW W tab P0 s st.2.1) r.leafIndex r.message)).2)) := by
  obtain ⟨P, g, sl, rec⟩ := st
  dsimp only at hP
  subst hP
  unfold hKernel handler
  rw [simulateQ_bind, StateT.run_bind, simulateQ_sign, run_toSt]
  simp
  exact map_pure _ _

/-- The forged keys' chain ends, as a writer program. -/
def endsW (F : Forgery) : LW (Layer → ChainIndex → Digest) :=
  sequenceFin fun l : Layer ↦ sequenceFin fun i : ChainIndex ↦
    valW W tab P0 s (l, forgedKey F l, i) (chainLength - 1)

theorem wLift_ends (F : Forgery) :
    wLift (FL W tab P0 s) (sequenceFin fun l : Layer ↦ sequenceFin fun i : ChainIndex ↦
      queryV W (l, forgedKey F l, i) (chainLength - 1)) = toSt (endsW W tab P0 s F) := by
  rw [endsW, mmap_sequenceFin, mmap_sequenceFin]
  refine congrArg sequenceFin (funext fun l ↦ ?_)
  rw [mmap_sequenceFin, mmap_sequenceFin]
  exact congrArg sequenceFin (funext fun i ↦ wLift_queryV W tab P0 s _ _)

theorem simulateQ_endsQ (F : Forgery) :
    simulateQ (logImpl tab (ansC W P0 s)) (endsQ W F) =
      Prod.fst <$> (toSt (endsW W tab P0 s F)).run := by
  rw [endsQ, simulateQ_map, run_wLift, wLift_ends]

end Table

/-! ## The output -/

/-- An opening of chain `j` at or below `μ` in the transcript, with its position and value. -/
def recOpen (rec : CLog) (j : CJ) (μ : ℕ) : Option (ℕ × Digest) :=
  rec.findSome? fun e ↦ match valEntry e with
    | some (j', ν, v) => if j' = j ∧ ν ≤ μ then some (ν, v) else none
    | none => none

theorem recOpen_some {rec : CLog} {j : CJ} {μ ν : ℕ} {v : Digest}
    (h : recOpen rec j μ = some (ν, v)) : ∃ e ∈ rec, valEntry e = some (j, ν, v) ∧ ν ≤ μ := by
  obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨e, he, ?_⟩
  cases hv : valEntry e with
  | none => simp [hv] at hf
  | some t =>
    obtain ⟨j', ν', v'⟩ := t
    simp only [hv] at hf
    split_ifs at hf with hc
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hf)
      exact ⟨by rw [hc.1], hc.2⟩

theorem recOpen_none {rec : CLog} {j : CJ} {μ : ℕ} (h : recOpen rec j μ = none) :
    ∀ e ∈ rec, ∀ ν v, valEntry e = some (j, ν, v) → μ < ν := by
  intro e he ν v hv
  have hf := List.findSome?_eq_none_iff.mp h e he
  by_contra hν
  have hle : ν ≤ μ := Nat.le_of_not_lt hν
  simp [hv, hle] at hf

theorem openedAtOrBelow_iff (log : CLog) (j : CJ) (μ : ℕ) :
    OpenedAtOrBelow log j μ ↔ ∃ e ∈ log, ∃ ν v, valEntry e = some (j, ν, v) ∧ ν ≤ μ := by
  unfold OpenedAtOrBelow
  constructor
  · rintro ⟨ν, hν, hm⟩
    obtain ⟨e, he, hv⟩ := List.mem_filterMap.mp hm
    rw [asValue_eq] at hv
    obtain ⟨⟨j', ν', v⟩, ht, hjν⟩ := Option.map_eq_some_iff.mp hv
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hjν
    exact ⟨e, he, ν', v, ht, hν⟩
  · rintro ⟨e, he, ν, v, hv, hν⟩
    refine ⟨ν, hν, List.mem_filterMap.mpr ⟨e, he, ?_⟩⟩
    rw [asValue_eq, hv]
    rfl

/-- The reading of a layer of the forgery: its codeword, its chain values walked to the end and
the values the reduction knows at the codeword's digits. -/
abbrev Data := Encoding × (ChainIndex → Digest) × (ChainIndex → Option Digest)

section Pick

variable {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput) (P : PublicParameter)
  (F : Forgery) (rec : CLog)

/-- The forged message of layer `l`. -/
def forgedMsgG (l : Layer) : m (Option LayerMsg) :=
  if l = bottomLayer then pure (some (.inl F.message))
  else (fun r ↦ r.map .inr) <$> Qrom.Xmss.Over.layerRoot hash P bottomLayer
    (keyIndexOnLayer F.signature.leafIndex bottomLayer) (littleEndianBytes 32 F.message)
    (F.signature.layers bottomLayer)

/-- The value of chain `j` at `μ`, walked up from a recorded opening at or below `μ`. -/
def knownG (j : CJ) (μ : ℕ) : m (Option Digest) :=
  match recOpen rec j μ with
  | none => pure none
  | some (ν, v) => some <$> Qrom.Xmss.Over.chainWalk hash P j.1 j.2.1 j.2.2 ν (μ - ν) v

/-- The reading of layer `l` for its codeword `x`. -/
def decodeData (l : Layer) (x : Encoding) : m (Option Data) := do
  let ws ← sequenceFin fun i ↦ Qrom.Xmss.Over.recoverChain hash P l (forgedKey F l) i (x i)
    ((F.signature.layers l).chainValues i)
  let cs ← sequenceFin fun i ↦ knownG hash P rec (l, forgedKey F l, i) (x i).val
  pure (some (x, ws, cs))

/-- The reading of layer `l` for its message `M`. -/
def layerData (l : Layer) (M : LayerMsg) : m (Option Data) :=
  Qrom.Xmss.Over.messageDigest hash P l (forgedKey F l) M.bytes
    (F.signature.layers l).randomizer >>= fun d ↦
      match Codeword.decode d with
      | none => pure none
      | some x => decodeData hash P F rec l x

/-- The reading of layer `l`. -/
def chainData (l : Layer) : m (Option Data) :=
  forgedMsgG hash P F l >>= fun mo ↦
    match mo with
    | none => pure none
    | some M => layerData hash P F rec l M

/-- A winning chain `(l, i)`: the forged value walks to the end and differs from the known value
or none is known. -/
def Cand (ends : Layer → ChainIndex → Digest) (ds : Layer → Option Data)
    (li : Layer × ChainIndex) : Prop :=
  ∃ x ws cs, ds li.1 = some (x, ws, cs) ∧ (x li.2).val < chainLength - 1 ∧
    ws li.2 = ends li.1 li.2 ∧
    (cs li.2 = none ∨ ∃ c, cs li.2 = some c ∧ (F.signature.layers li.1).chainValues li.2 ≠ c)

/-- The output for the chain `(l, i)`. -/
def outOf (ds : Layer → Option Data) (li : Layer × ChainIndex) : CJ × ℕ × Digest :=
  ((li.1, forgedKey F li.1, li.2),
    (match ds li.1 with
      | some d => (d.1 li.2).val
      | none => 0),
    (F.signature.layers li.1).chainValues li.2)

/-- The output when no chain wins. -/
def dfltOut : CJ × ℕ × Digest :=
  ((bottomLayer, keyAt 0, ⟨0, by decide⟩), 0, 0)

/-- **The choice of the output**: a winning chain if there is one. -/
noncomputable def choose3 (ends : Layer → ChainIndex → Digest) (ds : Layer → Option Data) :
    CJ × ℕ × Digest :=
  @dite _ (∃ li, Cand F ends ds li) (Classical.propDecidable _)
    (fun h ↦ outOf F ds (Classical.choose h)) fun _ ↦ dfltOut

/-- **The output's honest work**: read both layers, then choose. -/
noncomputable def pickG (ends : Layer → ChainIndex → Digest) : m (CJ × ℕ × Digest) :=
  sequenceFin (fun l : Layer ↦ chainData hash P F rec l) >>= fun ds ↦ pure (choose3 F ends ds)

variable {n : Type → Type} [Monad n] [LawfulMonad m] [LawfulMonad n] (Φ : m →ᵐ n)

theorem forgedMsgG_map (l : Layer) :
    Φ (forgedMsgG hash P F l) = forgedMsgG (fun x ↦ Φ (hash x)) P F l := by
  unfold forgedMsgG
  by_cases hl : l = bottomLayer
  · simp only [hl, ↓reduceIte, Φ.mmap_pure]
  · simp only [hl, ↓reduceIte, MonadHom.mmap_map, Over.mmap_layerRoot]

theorem knownG_map (j : CJ) (μ : ℕ) :
    Φ (knownG hash P rec j μ) = knownG (fun x ↦ Φ (hash x)) P rec j μ := by
  unfold knownG
  cases recOpen rec j μ with
  | none => exact Φ.mmap_pure _
  | some p => simp only [MonadHom.mmap_map, Over.mmap_chainWalk]

theorem decodeData_map (l : Layer) (x : Encoding) :
    Φ (decodeData hash P F rec l x) = decodeData (fun x ↦ Φ (hash x)) P F rec l x := by
  simp only [decodeData, Φ.mmap_bind, Φ.mmap_pure, mmap_sequenceFin, Over.mmap_recoverChain,
    knownG_map]

theorem layerData_map (l : Layer) (M : LayerMsg) :
    Φ (layerData hash P F rec l M) = layerData (fun x ↦ Φ (hash x)) P F rec l M := by
  unfold layerData
  rw [Φ.mmap_bind, Over.mmap_messageDigest]
  congr 1
  funext d
  cases Codeword.decode d with
  | none => exact Φ.mmap_pure _
  | some x => exact decodeData_map hash P F rec Φ l x

theorem chainData_map (l : Layer) :
    Φ (chainData hash P F rec l) = chainData (fun x ↦ Φ (hash x)) P F rec l := by
  unfold chainData
  rw [Φ.mmap_bind, forgedMsgG_map]
  congr 1
  funext mo
  cases mo with
  | none => exact Φ.mmap_pure _
  | some M => exact layerData_map hash P F rec Φ l M

theorem pickG_map (ends : Layer → ChainIndex → Digest) :
    Φ (pickG hash P F rec ends) = pickG (fun x ↦ Φ (hash x)) P F rec ends := by
  simp only [pickG, Φ.mmap_bind, Φ.mmap_pure, mmap_sequenceFin, chainData_map]

end Pick

/-- **The output**: query the forged keys' chain ends, then choose. -/
noncomputable def post (W : OracleWorld) (_s0 : S0) (F : Forgery) (st : St) :
    OracleComp (W.Oracles + CSpec) (CJ × ℕ × Digest) :=
  endsQ W F >>= fun ends ↦ liftR W (pickG W.hash st.1 F st.2.2.2 ends)

end CpreRed

/-- **The CPRE reduction B3** against the SUF-CMA adversary `A`. -/
noncomputable def cpreRed (W : OracleWorld)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    Props.Adversary W CpreRed.CSpec Unit (CpreRed.CJ × ℕ × Digest) :=
  fun _ ↦ slRed W (CpreRed.pre W) (fun s0 ↦ A s0.2.2.1) CpreRed.st0 (CpreRed.handler W)
    (CpreRed.post W)

namespace CpreRed

section Table2

variable (W : OracleWorld) (tab : W.Tab) (P0 : PublicParameter) (s : CJ → Digest)

theorem simulateQ_pickG (P : PublicParameter) (F : Forgery) (rec : CLog)
    (ends : Layer → ChainIndex → Digest) :
    simulateQ (W.eager tab) (pickG W.hash P F rec ends) =
      pure (pickG (m := Id) (W.hashOf tab) P F rec ends) := by
  rw [← simulateQ'_apply, pickG_map]
  simp only [W.simulateQ_hash]
  exact (pickG_map (m := Id) (W.hashOf tab) P F rec (MonadHom.pure ProbComp) ends).symm

theorem post_run (s0 : S0) (F : Forgery) (st : St) (log : CLog) :
    (simulateQ (logImpl tab (ansC W P0 s)) (post W s0 F st)).run log =
      pure (pickG (m := Id) (W.hashOf tab) st.1 F st.2.2.2 (lw (endsW W tab P0 s F)).1,
        log ++ (lw (endsW W tab P0 s F)).2) := by
  simp only [post, simulateQ_bind, StateT.run_bind, simulateQ_endsQ, StateT.run_map,
    run_run_toSt, map_pure, pure_bind, simulateQ_logImpl_liftR, StateT.run_lift, simulateQ_pickG]

/-- The judge's decision at the table. -/
noncomputable def judgeB (h : HashInput → HashOutput) (log : CLog) (out : CJ × ℕ × Digest) :
    Bool :=
  holds (CpreValid xmssChains log ∧ out.2.1 < chainLength - 1 ∧
    walkT h P0 out.1 out.2.1 (chainLength - 1 - out.2.1) out.2.2 =
      walkT h P0 out.1 0 (chainLength - 1) (s out.1) ∧
    (out.2.2 ≠ walkT h P0 out.1 0 out.2.1 (s out.1) ∨ ¬ OpenedAtOrBelow log out.1 out.2.1))

theorem simulateQ_judge (log : CLog) (out : CJ × ℕ × Digest) :
    simulateQ (W.eager tab) ((cpre W xmssChains noEval).judge (stC W P0 s) log out) =
      pure (judgeB P0 s (W.hashOf tab) log out) := by
  simp only [cpre, stC, simulateQ_bind, simulateQ_walk, pure_bind, simulateQ_pure]
  rfl

theorem run_queryReveal (log : CLog) :
    (simulateQ (logImpl tab (ansC W P0 s)) (queryReveal W)).run log =
      pure (P0, log ++ [revealEnt P0]) := by
  have h := simulateQ_logImpl_queryB W tab (ansC W P0 s) .reveal
  exact (congrArg (fun f ↦ StateT.run f log) h).trans (map_pure _ _)

theorem pre_run (hW : W.CoinsFair) :
    (simulateQ (logImpl tab (ansC W P0 s)) (pre W)).run [] =
      $ᵗ Bases >>= fun g ↦ pure ((P0, g, ⟨(lw (Gen.root (oW W tab P0 s g))).1, P0⟩,
        [revealEnt P0] ++ (lw (Gen.root (oW W tab P0 s g))).2),
        [revealEnt P0] ++ (lw (Gen.root (oW W tab P0 s g))).2) := by
  rw [pre, simulateQ_bind, StateT.run_bind, run_queryReveal, pure_bind, simulateQ_bind,
    simulateQ_logImpl_liftR, OracleWorld.simulateQ_sample hW, StateT.run_bind_lift]
  refine bind_congr fun g ↦ ?_
  rw [simulateQ_bind, StateT.run_bind, simulateQ_root, run_run_toSt, pure_bind, simulateQ_pure,
    StateT.run_pure, List.nil_append]

end Table2

/-! ## The writes of the signer -/

section Writes

variable (W : OracleWorld) (tab : W.Tab) (P0 : PublicParameter) (s : CJ → Digest) (g : Bases)

/-- An entry at a chain end with the challenger's answer. -/
def EndE (e : CEnt) : Prop :=
  ∀ j μ v, valEntry e = some (j, μ, v) → v = vAt (W.hashOf tab) P0 s j μ ∧ μ = chainLength - 1

/-- An entry with the challenger's answer, an opening of the transcript `slog` when below the
end. -/
def GoodE (slog : QueryLog SigningOracleSpec) (e : CEnt) : Prop :=
  ∀ j μ v, valEntry e = some (j, μ, v) → v = vAt (W.hashOf tab) P0 s j μ ∧
    (μ < chainLength - 1 → Opened (idealOps (W.hashOf tab) P0 (cOf s) g) slog j.1 j.2.1 j.2.2 μ)

/-- An entry with the challenger's answer, below the end an opening by the encoding of `msg`
under key `e`. -/
def SlE (e : KeyIndex) (msg : LayerMsg) (ent : CEnt) : Prop :=
  ∀ j μ v, valEntry ent = some (j, μ, v) → v = vAt (W.hashOf tab) P0 s j μ ∧
    (μ < chainLength - 1 → j.1 = msg.layer ∧ j.2.1 = e ∧ ∃ ρ D xx,
      (idealOps (W.hashOf tab) P0 (cOf s) g).encode e msg = some (ρ, D) ∧
        Codeword.decode D = some xx ∧ (xx j.2.2).val ≤ μ)

theorem valEntry_valEnt (j : CJ) (μ : ℕ) (v : Digest) : valEntry (valEnt j μ v) = some (j, μ, v) :=
  rfl

theorem wr_valW {Q : CEnt → Prop} (j : CJ) (μ : ℕ)
    (hQ : Q (valEnt j μ (vAt (W.hashOf tab) P0 s j μ))) : Wr Q (valW W tab P0 s j μ) := by
  intro e he
  rw [valW, lw_mkW] at he
  rw [List.mem_singleton.mp he]
  exact hQ

theorem endE_valEnt (j : CJ) :
    EndE W tab P0 s (valEnt j (chainLength - 1) (vAt (W.hashOf tab) P0 s j (chainLength - 1))) := by
  intro j' μ v hv
  simp only [valEntry_valEnt, Option.some.injEq, Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  exact ⟨rfl, rfl⟩

theorem goodE_of_endE (slog : QueryLog SigningOracleSpec) (e : CEnt) (h : EndE W tab P0 s e) :
    GoodE W tab P0 s g slog e := by
  intro j μ v hv
  obtain ⟨h1, h2⟩ := h j μ v hv
  exact ⟨h1, fun hμ ↦ absurd h2 (Nat.ne_of_lt hμ)⟩

theorem oW_chain (l : Layer) (e : KeyIndex) (i : ChainIndex) (μ : ℕ) :
    (oW W tab P0 s g).chain l e i μ =
      if μ ≤ chainLength - 1 then valW W tab P0 s (l, e, i) μ else pure 0 :=
  rfl

theorem oW_leaf (l : Layer) (e : KeyIndex) (ends : ChainIndex → Digest) :
    (oW W tab P0 s g).leaf l e ends =
      pure ((idealOps (W.hashOf tab) P0 (cOf s) g).leaf l e ends) :=
  rfl

theorem oW_node (l : Layer) (k j : ℕ) (a b : Digest) :
    (oW W tab P0 s g).node l k j a b =
      pure ((idealOps (W.hashOf tab) P0 (cOf s) g).node l k j a b) :=
  rfl

theorem grind_lw (h : HashInput → HashOutput) (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (M : HashInput) (r0 : Randomizer) :
    ∀ n t : ℕ, grind (m := LW) (fun x ↦ pure (h x)) P l e M r0 n t =
      pure (grind (m := Id) h P l e M r0 n t)
  | 0, _ => rfl
  | n + 1, t => by
    rw [grind_succ_id]
    show (Qrom.Xmss.Over.messageDigest (m := LW) (fun x ↦ pure (h x)) P l e M
        (r0 + BitVec.ofNat digestBits t) >>= fun d ↦
          if (Codeword.decode d).isSome then pure (some (r0 + BitVec.ofNat digestBits t, d))
          else grind (m := LW) (fun x ↦ pure (h x)) P l e M r0 n (t + 1)) = _
    rw [show Qrom.Xmss.Over.messageDigest (m := LW) (fun x ↦ pure (h x)) P l e M
        (r0 + BitVec.ofNat digestBits t) = pure (Qrom.Xmss.Over.messageDigest (m := Id) h P l e M
          (r0 + BitVec.ofNat digestBits t)) from rfl, lw_pure_bind]
    split_ifs
    · rfl
    · exact grind_lw h P l e M r0 n (t + 1)

theorem oW_encode (e : KeyIndex) (msg : LayerMsg) :
    (oW W tab P0 s g).encode e msg = pure ((idealOps (W.hashOf tab) P0 (cOf s) g).encode e msg) :=
  grind_lw (W.hashOf tab) P0 msg.layer e msg.bytes (g (e, msg)) randomizerAttemptLimit 0

theorem fst_treeNode (l : Layer) (k j : ℕ) :
    (lw (Gen.treeNode (oW W tab P0 s g) l k j)).1 =
      Gen.treeNode (idealOps (W.hashOf tab) P0 (cOf s) g) l k j := by
  rw [← fstH_apply, Gen.mmap_treeNode, oW_fst]

theorem fst_signLayer (e : KeyIndex) (msg : LayerMsg) :
    (lw (Gen.signLayer (oW W tab P0 s g) e msg)).1 =
      Gen.signLayer (idealOps (W.hashOf tab) P0 (cOf s) g) e msg := by
  rw [← fstH_apply, Gen.mmap_signLayer, oW_fst]

theorem wr_treeNode (l : Layer) :
    ∀ k j, Wr (EndE W tab P0 s) (Gen.treeNode (oW W tab P0 s g) l k j)
  | 0, j => by
    show Wr _ (Gen.otsPublicKey (oW W tab P0 s g) l (keyAt j) >>= fun ends ↦
      (oW W tab P0 s g).leaf l (keyAt j) ends)
    refine wr_bind (wr_sequenceFin _ fun i ↦ ?_) (wr_of_eq_pure _ (oW_leaf W tab P0 s g _ _ _))
    rw [oW_chain]
    simp only [le_refl, ↓reduceIte]
    exact wr_valW W tab P0 s _ _ (endE_valEnt W tab P0 s _)
  | k + 1, j => by
    show Wr _ (Gen.treeNode (oW W tab P0 s g) l k (2 * j) >>= fun left ↦
      Gen.treeNode (oW W tab P0 s g) l k (2 * j + 1) >>= fun right ↦
        (oW W tab P0 s g).node l k j left right)
    exact wr_bind (wr_treeNode l k _) (wr_bind (wr_treeNode l k _)
      (wr_of_eq_pure _ (oW_node W tab P0 s g _ _ _ _ _)))

theorem wr_treePath (l : Layer) (e : KeyIndex) :
    Wr (EndE W tab P0 s) (Gen.treePath (oW W tab P0 s g) l e) :=
  wr_sequenceFin _ fun _ ↦ wr_treeNode W tab P0 s g l _ _

theorem wr_signLayer (e : KeyIndex) (msg : LayerMsg) :
    Wr (SlE W tab P0 s g e msg) (Gen.signLayer (oW W tab P0 s g) e msg) := by
  unfold Gen.signLayer
  refine wr_bind (wr_of_eq_pure _ (oW_encode W tab P0 s g e msg)) ?_
  rw [oW_encode, lw_pure]
  dsimp only
  split
  next ρ d henc =>
    split
    next x hdec =>
      refine wr_bind (wr_sequenceFin _ fun i ↦ ?_)
        (wr_bind (wr_mono (fun ent h ↦ ?_) (wr_treePath W tab P0 s g _ e)) (wr_pure _ _))
      · rw [oW_chain]
        simp only [show (x i).val ≤ chainLength - 1 by have := (x i).isLt; omega, ↓reduceIte]
        refine wr_valW W tab P0 s _ _ fun j μ v hv ↦ ?_
        simp only [valEntry_valEnt, Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl, rfl⟩ := hv
        exact ⟨rfl, fun _ ↦ ⟨rfl, rfl, ρ, d, x, henc, hdec, le_rfl⟩⟩
      · intro j μ v hv
        obtain ⟨h1, h2⟩ := h j μ v hv
        exact ⟨h1, fun hμ ↦ absurd h2 (Nat.ne_of_lt hμ)⟩
    next => exact wr_pure _ _
  next => exact wr_pure _ _

theorem signLayer_isSome {o : Ops Id} {e : KeyIndex} {msg : LayerMsg} {σ : LayerSignature}
    (h : Gen.signLayer o e msg = some σ) : (o.encode e msg).isSome = true := by
  cases he : o.encode e msg with
  | none => simp [Gen.signLayer, Extract.id_bind, he] at h
  | some _ => rfl

theorem opened_append_left {o : Ops Id} {log : QueryLog SigningOracleSpec}
    (log' : QueryLog SigningOracleSpec) {l : Layer} {e : KeyIndex} {i : ChainIndex} {μ : ℕ}
    (h : Opened o log l e i μ) : Opened o (log ++ log') l e i μ := by
  obtain ⟨x, hx, rest⟩ := h
  exact ⟨x, List.mem_append_left _ hx, rest⟩

theorem opened_append_right {o : Ops Id} (log : QueryLog SigningOracleSpec)
    {log' : QueryLog SigningOracleSpec} {l : Layer} {e : KeyIndex} {i : ChainIndex} {μ : ℕ}
    (h : Opened o log' l e i μ) : Opened o (log ++ log') l e i μ := by
  obtain ⟨x, hx, rest⟩ := h
  exact ⟨x, List.mem_append_right _ hx, rest⟩

theorem wr_sign (r : SigningRequest) (a : Option Signature) :
    Wr (GoodE W tab P0 s g [⟨r, a⟩]) (Gen.sign (oW W tab P0 s g) r.leafIndex r.message) := by
  set o := idealOps (W.hashOf tab) P0 (cOf s) g
  unfold Gen.sign
  dsimp only
  refine wr_bind (wr_mono (fun ent h ↦ ?_) (wr_signLayer W tab P0 s g _ (.inl r.message))) ?_
  · intro j μ v hv
    obtain ⟨h1, h2⟩ := h j μ v hv
    refine ⟨h1, fun hμ ↦ ?_⟩
    obtain ⟨hl, he, ρ, D, xx, henc, hdec, hle⟩ := h2 hμ
    obtain ⟨l, e, i⟩ := j
    dsimp only at hl he hle ⊢
    subst hl he
    exact ⟨⟨r, a⟩, List.mem_singleton_self _, rfl, .inl r.message, ite_eq_left rfl, ρ, D, xx, henc,
      hdec, hle⟩
  rw [fst_signLayer]
  split
  next bottom hb =>
    have hsome := signLayer_isSome hb
    refine wr_bind (wr_mono (fun ent h ↦ goodE_of_endE W tab P0 s g _ ent h)
      (wr_treeNode W tab P0 s g _ _ _)) ?_
    rw [fst_treeNode]
    refine wr_bind (wr_mono (fun ent h ↦ ?_) (wr_signLayer W tab P0 s g _ _)) ?_
    · intro j μ v hv
      obtain ⟨h1, h2⟩ := h j μ v hv
      refine ⟨h1, fun hμ ↦ ?_⟩
      obtain ⟨hl, he, ρ, D, xx, henc, hdec, hle⟩ := h2 hμ
      obtain ⟨l, e, i⟩ := j
      dsimp only at hl he hle ⊢
      subst hl he
      refine ⟨⟨r, a⟩, List.mem_singleton_self _, rfl, _, ?_, ρ, D, xx, henc, hdec, hle⟩
      simp only [requestMsg, LayerMsg.layer, show topLayer ≠ bottomLayer by decide, ↓reduceIte,
        hsome]
    split <;> exact wr_pure _ _
  next => exact wr_pure _ _

/-- **The invariant of the handler state** against the challenger's transcript. -/
def Inv (p : St × CLog) : Prop :=
  p.1.1 = P0 ∧ p.1.2.1 = g ∧ p.1.2.2.2 = p.2 ∧ ∀ e ∈ p.2, GoodE W tab P0 s g p.1.2.2.1 e

/-- The signing transcript of a state. -/
def πSt (p : St × CLog) : QueryLog SigningOracleSpec :=
  p.1.2.2.1

/-- The ideal key of the challenger's sample and the bases. -/
def keyOf : IdealKey :=
  (P0, cOf s, g)

theorem hK (p : St × CLog) (hp : Inv W tab P0 s g p) (r : SigningRequest) :
    Prod.map id πSt <$> hKernel tab (ansC W P0 s) (handler W) p r =
      idealKernel (W.hashOf tab) (keyOf P0 s g) (πSt p) r := by
  obtain ⟨⟨P, g', sl, rec⟩, log⟩ := p
  obtain ⟨hP, hg, -, -⟩ := hp
  dsimp only at hP hg
  subst hg
  rw [hKernel_handler W tab P0 s _ log r hP, map_pure, fst_sign]
  rfl

theorem hInv (p : St × CLog) (hp : Inv W tab P0 s g p) (r : SigningRequest) :
    ∀ q ∈ support (hKernel tab (ansC W P0 s) (handler W) p r), Inv W tab P0 s g q.2 := by
  obtain ⟨⟨P, g', sl, rec⟩, log⟩ := p
  obtain ⟨hP, hg, hrec, hlog⟩ := hp
  dsimp only at hP hg hrec hlog
  subst hg hrec
  intro q hq
  rw [hKernel_handler W tab P0 s _ rec r hP, support_pure, Set.mem_singleton_iff] at hq
  subst hq
  refine ⟨hP, rfl, rfl, fun e he ↦ ?_⟩
  rcases List.mem_append.mp he with he | he
  · intro j μ v hv
    obtain ⟨h1, h2⟩ := hlog e he j μ v hv
    exact ⟨h1, fun hμ ↦ opened_append_left _ (h2 hμ)⟩
  · intro j μ v hv
    obtain ⟨h1, h2⟩ := wr_sign W tab P0 s g' r _ e he j μ v hv
    exact ⟨h1, fun hμ ↦ opened_append_right _ (h2 hμ)⟩

end Writes

/-! ## On the event the judge accepts -/

section Judge

theorem cpreValid_all (log : CLog) : CpreValid xmssChains log := by
  refine ⟨fun t ht ↦ ?_, fun _ _ _ _ _ ↦ rfl⟩
  obtain ⟨⟨q, a⟩, _, hq⟩ := List.mem_filterMap.mp ht
  cases q with
  | value => exact absurd hq (by simp [CpreQuery.evalTweak])
  | eval l => exact l.elim
  | reveal => exact absurd hq (by simp [CpreQuery.evalTweak])

theorem vAt_eq (h : HashInput → HashOutput) (P : PublicParameter) (s : CJ → Digest) (j : CJ)
    {μ : ℕ} (hμ : μ ≤ chainLength - 1) :
    vAt h P s j μ = Qrom.Xmss.Over.chainWalk (m := Id) h P j.1 j.2.1 j.2.2 0 μ (s j) := by
  unfold vAt
  rw [min_eq_left hμ]

theorem opened_mono {o : Ops Id} {log : QueryLog SigningOracleSpec} {l : Layer} {e : KeyIndex}
    {i : ChainIndex} {ν μ : ℕ} (hνμ : ν ≤ μ) (h : Opened o log l e i ν) : Opened o log l e i μ := by
  obtain ⟨x, hx, hk, M, hM, ρ, D, xx, he, hd, hle⟩ := h
  exact ⟨x, hx, hk, M, hM, ρ, D, xx, he, hd, hle.trans hνμ⟩

variable (h : HashInput → HashOutput) (P : PublicParameter) (F : Forgery) (rec : CLog)

theorem pickG_id (ends : Layer → ChainIndex → Digest) :
    pickG (m := Id) h P F rec ends = choose3 F ends fun l ↦ chainData (m := Id) h P F rec l := by
  show choose3 F ends (sequenceFin fun l ↦ chainData (m := Id) h P F rec l) = _
  rw [Extract.sequenceFin_id]

theorem forgedMsgG_id (l : Layer) : forgedMsgG (m := Id) h P F l = forgedMsg h P F l := by
  unfold forgedMsgG forgedMsg
  rfl

theorem knownG_id_none {j : CJ} {μ : ℕ} (hr : recOpen rec j μ = none) :
    knownG (m := Id) h P rec j μ = none := by
  unfold knownG
  rw [hr]
  rfl

theorem knownG_id_some {j : CJ} {μ ν : ℕ} {v : Digest} (hr : recOpen rec j μ = some (ν, v)) :
    knownG (m := Id) h P rec j μ =
      some (Qrom.Xmss.Over.chainWalk (m := Id) h P j.1 j.2.1 j.2.2 ν (μ - ν) v) := by
  unfold knownG
  rw [hr]
  rfl

theorem chainData_id_of {l : Layer} {M : LayerMsg} {x : Encoding}
    (hM : forgedMsg h P F l = some M) (hx : Codeword.decode (forgedDigest h P F l M) = some x) :
    chainData (m := Id) h P F rec l = some (x,
      fun i ↦ Qrom.Xmss.Over.recoverChain (m := Id) h P l (forgedKey F l) i (x i)
        ((F.signature.layers l).chainValues i),
      fun i ↦ knownG (m := Id) h P rec (l, forgedKey F l, i) (x i).val) := by
  have hx' : Codeword.decode (Qrom.Xmss.Over.messageDigest (m := Id) h P l (forgedKey F l)
      M.bytes (F.signature.layers l).randomizer) = some x := hx
  simp only [chainData, layerData, decodeData, Extract.id_bind, forgedMsgG_id, hM, hx',
    Extract.sequenceFin_id, Extract.id_pure]

theorem chainData_id_inv {l : Layer} {x : Encoding} {ws : ChainIndex → Digest}
    {cs : ChainIndex → Option Digest} (hd : chainData (m := Id) h P F rec l = some (x, ws, cs)) :
    ∃ M, forgedMsg h P F l = some M ∧ Codeword.decode (forgedDigest h P F l M) = some x ∧
      ws = (fun i ↦ Qrom.Xmss.Over.recoverChain (m := Id) h P l (forgedKey F l) i (x i)
        ((F.signature.layers l).chainValues i)) ∧
      cs = fun i ↦ knownG (m := Id) h P rec (l, forgedKey F l, i) (x i).val := by
  cases hM : forgedMsg h P F l with
  | none => simp [chainData, Extract.id_bind, forgedMsgG_id, hM] at hd
  | some M =>
    cases hx : Codeword.decode (forgedDigest h P F l M) with
    | none =>
      have hx' : Codeword.decode (Qrom.Xmss.Over.messageDigest (m := Id) h P l (forgedKey F l)
          M.bytes (F.signature.layers l).randomizer) = none := hx
      simp [chainData, layerData, Extract.id_bind, forgedMsgG_id, hM, hx'] at hd
    | some x' =>
      rw [chainData_id_of h P F rec hM hx] at hd
      obtain ⟨h1, h23⟩ := Prod.mk.inj (Option.some.inj hd)
      obtain ⟨h2, h3⟩ := Prod.mk.inj h23
      subst h1 h2 h3
      exact ⟨M, rfl, hx, rfl, rfl⟩

end Judge

section Accept

variable (W : OracleWorld) (tab : W.Tab) (P0 : PublicParameter) (s : CJ → Digest) (g : Bases)

theorem endsW_fst (F : Forgery) (l : Layer) (i : ChainIndex) :
    (lw (endsW W tab P0 s F)).1 l i =
      vAt (W.hashOf tab) P0 s (l, forgedKey F l, i) (chainLength - 1) := by
  simp only [endsW, fst_sequenceFin]
  rfl

theorem wr_endsW (F : Forgery) : Wr (EndE W tab P0 s) (endsW W tab P0 s F) :=
  wr_sequenceFin _ fun _ ↦ wr_sequenceFin _ fun _ ↦
    wr_valW W tab P0 s _ _ (endE_valEnt W tab P0 s _)

/-- **On the CPRE event the judge accepts the reduction's output.** -/
theorem judge_of_event (F : Forgery) (st : St) (log : CLog) (hp : Inv W tab P0 s g (st, log))
    (hev : CpreEv (W.hashOf tab) P0 (idealOps (W.hashOf tab) P0 (cOf s) g) st.2.2.1 F) :
    judgeB P0 s (W.hashOf tab) (log ++ (lw (endsW W tab P0 s F)).2)
      (pickG (m := Id) (W.hashOf tab) st.1 F st.2.2.2 (lw (endsW W tab P0 s F)).1) = true := by
  obtain ⟨hP, -, hrec, hlog⟩ := hp
  dsimp only at hP hrec hlog
  rw [hP, hrec]
  obtain ⟨l, M', hM', x, hx, i, hi, hwalk, hcase⟩ := hev
  have hends := endsW_fst W tab P0 s F
  have hcand : ∃ li, Cand F (lw (endsW W tab P0 s F)).1
      (fun l ↦ chainData (m := Id) (W.hashOf tab) P0 F log l) li := by
    refine ⟨(l, i), x, _, _, chainData_id_of _ _ _ _ hM' hx, hi, ?_, ?_⟩
    · show Qrom.Xmss.Over.chainWalk (m := Id) (W.hashOf tab) P0 l (forgedKey F l) i (x i).val
        (chainLength - 1 - (x i).val) _ = _
      rw [hwalk, hends, vAt_eq _ _ _ _ le_rfl]
      rfl
    · cases hro : recOpen log (l, forgedKey F l, i) (x i).val with
      | none => exact .inl (knownG_id_none _ _ _ hro)
      | some p =>
        obtain ⟨ν, v⟩ := p
        refine .inr ⟨_, knownG_id_some _ _ _ hro, ?_⟩
        obtain ⟨e, he, hv, hνμ⟩ := recOpen_some hro
        obtain ⟨hvv, hop⟩ := hlog e he _ _ _ hv
        have hν3 : ν < chainLength - 1 := Nat.lt_of_le_of_lt hνμ hi
        rw [hvv, vAt_eq _ _ _ _ hν3.le]
        dsimp only
        rw [chainWalk_split _ _ _ _ _ hνμ]
        rcases hcase with hne | hno
        · exact hne
        · exact absurd (opened_mono hνμ (hop hν3)) hno
  obtain ⟨x', ws, cs, hds, hlt, hwe, hcs⟩ := Classical.choose_spec hcand
  obtain ⟨M2, -, -, rfl, rfl⟩ := chainData_id_inv _ _ _ _ hds
  rw [pickG_id]
  unfold choose3
  rw [dite_eq_left hcand]
  generalize Classical.choose hcand = li at hds hlt hwe hcs
  obtain ⟨l2, i2⟩ := li
  dsimp only at hds hlt hwe hcs
  have hout : outOf F (fun l ↦ chainData (m := Id) (W.hashOf tab) P0 F log l) (l2, i2) =
      ((l2, forgedKey F l2, i2), (x' i2).val, (F.signature.layers l2).chainValues i2) := by
    simp only [outOf, hds]
  rw [hout]
  unfold judgeB
  refine holds_eq_true.mpr ⟨cpreValid_all _, hlt, ?_, ?_⟩
  · dsimp only
    rw [walkT_eq W tab P0 _ _ _ _ (by omega), walkT_eq W tab P0 _ _ _ _ (by omega)]
    rw [hends, vAt_eq _ _ _ _ le_rfl] at hwe
    exact hwe
  · dsimp only
    cases hro : recOpen log (l2, forgedKey F l2, i2) (x' i2).val with
    | none =>
      refine .inr ?_
      rw [openedAtOrBelow_iff]
      rintro ⟨e, he, ν, v, hv, hνμ⟩
      rcases List.mem_append.mp he with he | he
      · exact absurd hνμ (Nat.not_le.mpr (recOpen_none hro e he ν v hv))
      · have h3 := (wr_endsW W tab P0 s F e he _ _ _ hv).2
        omega
    | some p =>
      obtain ⟨ν, v⟩ := p
      refine .inl ?_
      rw [knownG_id_some _ _ _ hro] at hcs
      rcases hcs with hn | ⟨c, hc, hne⟩
      · exact absurd hn (by simp)
      · obtain ⟨e, he, hv, hνμ⟩ := recOpen_some hro
        obtain ⟨hvv, -⟩ := hlog e he _ _ _ hv
        rw [walkT_eq W tab P0 _ _ _ _ (by omega)]
        intro heq
        apply hne
        rw [← Option.some.inj hc, hvv, vAt_eq _ _ _ _ (by omega)]
        dsimp only
        rw [chainWalk_split _ _ _ _ _ hνμ]
        exact heq

end Accept

/-! ## The probability -/

section Prob

variable (W : OracleWorld) (tab : W.Tab)

/-- The law of the CPRE challenger's setup: a uniform parameter and uniform starts. -/
theorem tsum_cpre_setup (hW : W.CoinsFair) (tab : W.Tab) {Par Tw J Val Fn Out : Type}
    {Msg : Fn → Type} [SampleableType Par] [Fintype J] [SampleableType Val]
    (ch : Chains Par Tw J Val) (C : TwColl Par Tw Fn Msg Out)
    (f : Par × (J → Val) → ℝ≥0∞) :
    ∑' a : Par × (J → Val), Pr{let z ← simulateQ (W.eager tab) (cpre W ch C).setup}[z = a] * f a =
      ∑' P, Pr{let z ← $ᵗ Par}[z = P] * ∑' s, Pr{let z ← $ᵗ (J → Val)}[z = s] * f (P, s) := by
  simp only [cpre, simulateQ_bind, OracleWorld.simulateQ_sample hW, simulateQ_pure,
    tsum_prEvent_bind_mul, tsum_prEvent_pure_mul]

theorem tsum_unif {α : Type} [SampleableType α] [Fintype α] (Φ : α → ℝ≥0∞) :
    ∑' a, Pr{let z ← $ᵗ α}[z = a] * Φ a = unifAvg Φ := by
  rw [tsum_fintype]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, unifAvg]

theorem unifAvg_mono {α : Type} [Fintype α] {F G : α → ℝ≥0∞} (h : ∀ a, F a ≤ G a) :
    unifAvg F ≤ unifAvg G :=
  Finset.sum_le_sum fun a _ ↦ mul_le_mul' le_rfl (h a)

variable (P0 : PublicParameter) (s : CJ → Digest)

/-- The reduction's game decision on the canonical run: its output and the judge. -/
noncomputable def dRed (r : Forgery × St × CLog) : Bool :=
  judgeB P0 s (W.hashOf tab) (r.2.2 ++ (lw (endsW W tab P0 s r.1)).2)
    (pickG (m := Id) (W.hashOf tab) r.2.1.1 r.1 r.2.1.2.2.2 (lw (endsW W tab P0 s r.1)).1)

/-- After the setup, the reduction's game is a decision on the canonical run. -/
theorem probAt_round (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery)
    (p : S0 × CLog) :
    W.probAt tab ((QuantumComp₂.bind (kRunL W (hKernel tab (ansC W P0 s) (handler W))
        (A p.1.2.2.1) (st0 p.1) p.2) fun r ↦
          ((simulateQ (logImpl tab (ansC W P0 s)) (post W p.1 r.1.1 r.1.2)).run r.2).toQuantumAt
            (QComp.coinImpl W.spec _)).bind fun r ↦
        (simulateQ (W.eager tab)
          ((cpre W xmssChains noEval).judge (stC W P0 s) r.2 r.1)).toQuantumAt
            (QComp.coinImpl W.spec _)) =
      W.probAt tab ((kRunQ W (hKernel tab (ansC W P0 s) (handler W)) (A p.1.2.2.1)
        (st0 p.1, p.2)).map (dRed W tab P0 s)) := by
  refine probAt_eq_of_run₂ W tab ?_
  rw [QuantumComp₂.bind_assoc, kRunL_eq_map, QuantumComp₂.map_eq_bind_pure (dRed W tab P0 s),
    QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
  simp only [QuantumComp₂.pure_bind]
  refine run₂_bind_congr rfl fun a ↦ ?_
  rw [post_run]
  refine (run₂_bind_of_classicalOn_pure _ (classicalOn_coinImpl_toQuantumAt _ _) _).trans ?_
  rw [simulateQ_judge]
  exact run₂_eq_of_classicalOn (classicalOn_coinImpl_toQuantumAt _ _) (classicalOn_pure _)

/-- The setup's output for the bases `g`. -/
noncomputable def s0Of (g : Bases) : S0 :=
  (P0, g, ⟨(lw (Gen.root (oW W tab P0 s g))).1, P0⟩,
    [revealEnt P0] ++ (lw (Gen.root (oW W tab P0 s g))).2)

theorem inv_init (g : Bases) :
    Inv W tab P0 s g (st0 (s0Of W tab P0 s g), (s0Of W tab P0 s g).2.2.2) := by
  refine ⟨rfl, rfl, rfl, fun e he ↦ ?_⟩
  rcases List.mem_append.mp he with he | he
  · rw [List.mem_singleton.mp he]
    intro j μ v hv
    exact absurd hv (by simp [revealEnt, valEntry])
  · exact goodE_of_endE W tab P0 s g [] e (wr_treeNode W tab P0 s g topLayer layerHeight 0 e he)

/-- **One key**: the ideal CPRE event is at most the reduction's game decision. -/
theorem round_ge (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery)
    (g : Bases) :
    W.probAt tab ((idealRun W tab (keyOf P0 s g) A).map
        (cpreDec (W.hashOf tab) (keyOf P0 s g))) ≤
      W.probAt tab ((kRunQ W (hKernel tab (ansC W P0 s) (handler W))
        (A (s0Of W tab P0 s g).2.2.1) (st0 (s0Of W tab P0 s g), (s0Of W tab P0 s g).2.2.2)).map
          (dRed W tab P0 s)) := by
  have hpk : (s0Of W tab P0 s g).2.2.1 = idealPk (W.hashOf tab) (keyOf P0 s g) := by
    show (⟨(lw (Gen.root (oW W tab P0 s g))).1, P0⟩ : PublicKey) = _
    rw [fst_root]
    rfl
  let d₂ : Forgery × St × CLog → Bool := fun r ↦
    holds (Inv W tab P0 s g r.2) && cpreDec (W.hashOf tab) (keyOf P0 s g) (r.1, πSt r.2)
  have hsim := run₂_map_kRunQ_sim (W.runtime tab) (idealKernel (W.hashOf tab) (keyOf P0 s g))
    (hKernel tab (ansC W P0 s) (handler W)) (Inv W tab P0 s g) πSt (hK W tab P0 s g)
    (hInv W tab P0 s g) (A (s0Of W tab P0 s g).2.2.1)
    (st0 (s0Of W tab P0 s g), (s0Of W tab P0 s g).2.2.2) (inv_init W tab P0 s g)
    (cpreDec (W.hashOf tab) (keyOf P0 s g)) d₂ fun a st hst ↦ by
      simp only [d₂, holds_eq_true.mpr hst, Bool.true_and]
  have h1 : W.probAt tab ((idealRun W tab (keyOf P0 s g) A).map
      (cpreDec (W.hashOf tab) (keyOf P0 s g))) =
      W.probAt tab ((kRunQ W (hKernel tab (ansC W P0 s) (handler W)) (A (s0Of W tab P0 s g).2.2.1)
        (st0 (s0Of W tab P0 s g), (s0Of W tab P0 s g).2.2.2)).map d₂) := by
    rw [idealRun, ← hpk]
    exact (probAt_eq_of_run₂ W tab hsim).symm
  rw [h1]
  have hle := probAt_map_le_sum W tab (kRunQ W (hKernel tab (ansC W P0 s) (handler W))
    (A (s0Of W tab P0 s g).2.2.1) (st0 (s0Of W tab P0 s g), (s0Of W tab P0 s g).2.2.2)) d₂
    {()} (fun _ ↦ dRed W tab P0 s) fun r hr ↦ ⟨(), Finset.mem_singleton_self _, ?_⟩
  · simpa using hle
  simp only [d₂, Bool.and_eq_true, holds_eq_true] at hr
  obtain ⟨hI, hc⟩ := hr
  have hev := (holds_eq_true.mp hc).2.2
  exact judge_of_event W tab P0 s g r.1 r.2.1 r.2.2 hI hev

/-- The reduction's game after the challenger's sample `(P0, s)`. -/
theorem round_tsum_ge (hW : W.CoinsFair)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    unifAvg (fun g : Bases ↦ W.probAt tab ((idealRun W tab (keyOf P0 s g) A).map
        (cpreDec (W.hashOf tab) (keyOf P0 s g)))) ≤
      W.probAt tab (QuantumComp₂.bind (slNormal tab (ansC W P0 s) (pre W)
        (fun s0 ↦ A s0.2.2.1) st0 (handler W) (post W)) fun r ↦
          (simulateQ (W.eager tab)
            ((cpre W xmssChains noEval).judge (stC W P0 s) r.2 r.1)).toQuantumAt
              (QComp.coinImpl W.spec _)) := by
  rw [← tsum_unif]
  unfold slNormal
  rw [QuantumComp₂.bind_assoc, probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _),
    pre_run W tab P0 s hW, tsum_prEvent_bind_mul]
  simp only [tsum_prEvent_pure_mul]
  refine ENNReal.tsum_le_tsum fun g ↦ mul_le_mul' le_rfl ?_
  exact (round_ge W tab P0 s A g).trans_eq (probAt_round W tab P0 s A (s0Of W tab P0 s g,
    (s0Of W tab P0 s g).2.2.2)).symm

end Prob

end CpreRed

open CpreRed in
/-- **The CPRE event of the ideal game is at most CPRE success of B3**, at every table of a world
with fair coins. -/
theorem idealProb_cpre_le (W : OracleWorld) (hW : W.CoinsFair) (tab : W.Tab)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    idealProb W tab A (fun k ↦ cpreDec (W.hashOf tab) k) ≤
      Props.cpreSucc W xmssChains noEval tab (cpreRed W A) := by
  have hideal : idealProb W tab A (fun k ↦ cpreDec (W.hashOf tab) k) =
      unifAvg fun P : PublicParameter ↦ unifAvg fun s : CJ → Digest ↦ unifAvg fun g : Bases ↦
        W.probAt tab ((idealRun W tab (keyOf P s g) A).map
          (cpreDec (W.hashOf tab) (keyOf P s g))) := by
    show unifAvg (fun k : IdealKey ↦ W.probAt tab ((idealRun W tab k A).map
      (cpreDec (W.hashOf tab) k))) = _
    rw [unifAvg_prod]
    refine unifAvg_congr fun P ↦ ?_
    rw [unifAvg_prod, ← unifAvg_equiv startsEquiv]
    rfl
  rw [hideal]
  refine le_of_le_of_eq ?_ ((probAt_eq_of_run₂ W tab (run₂_game_slRed tab
    (cpre W xmssChains noEval) (fun _ ↦ pre W) (fun _ s0 ↦ A s0.2.2.1) (fun _ ↦ st0)
    (fun _ ↦ handler W) (fun _ ↦ post W))).trans ((probAt_bind_classicalOn W tab
      (classicalOn_coinImpl_toQuantumAt _ _) _).trans
        (tsum_cpre_setup W hW tab xmssChains noEval _))).symm
  simp only [tsum_unif]
  exact unifAvg_mono fun P ↦ unifAvg_mono fun s ↦ round_tsum_ge W tab P s hW A

open IPFunctor Common CpreRed in
/-- **B3's hash calls**: `A`'s hash calls plus the honest work of its setup (`c₀`), of each
signing call (`k`) and of its output (`c₁`). -/
theorem isChargeBound_cpreRed (W : OracleWorld)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) {c₀ k c₁ n m : ℕ}
    (hpre : QueryCostAtMost (pre W) (hcallCost W (R' := CSpec)) c₀)
    (hσ : ∀ st r, QueryCostAtMost (handler W st r) (hcallCost W (R' := CSpec)) k)
    (hpost : ∀ s0 F st, QueryCostAtMost (post W s0 F st) (hcallCost W (R' := CSpec)) c₁)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (cpreRed W A ()) (cmdCharge hashCharge) (c₀ + ((n + k * m) + c₁)) :=
  isChargeBound_slRed_hash W (pre W) (fun s0 ↦ A s0.2.2.1) st0 (handler W) (post W) hpre hσ hpost
    (fun _ ↦ hn _) (fun _ ↦ hm _)

end Quantum.StdModel.Xmss

end
