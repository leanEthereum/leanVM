module

public import Quantum.Qrom.Xmss.HonestTable
public import Quantum.Qrom.Xmss.NoReuse
public import Quantum.Qrom.SufCma.Classical
public import Quantum.Xmss.GameReads

@[expose] public section

/-!
# leanXMSS's game with honest read ports, in the QROM

The QROM game's honest hashing (key generation, each signature, the forgery's verification) is a
classical computation: against a fixed function `H`, each hash is one basis call of the port. Here
it becomes a program of the classical read ports of runtime 1 (`hwReadSpec`, port `readH`), with
the adversary's calls lifted to port `h` (`liftH`). The generic intertwining machinery is the
QRPM's (`Quantum.Xmss.GameReads`, namespace `Quantum.Sponge`: `ReadsTo`, `readCall`, `hwAt`,
`intertwines_substitute`, `evalDistMap_eq_of_intertwines`), at `X := HashOutput`,
`Z := HashDomain`.

* `IsHash`, `isHash_verify`: verification only hashes (never flips a coin).
* `romReadImpl M B`, `readsProgram M B x`: a computation over the model's oracles with every hash
  a read port at its input, logging the inputs. `readsTo_readsProgram`: on the block `(W, m)`
  against `t`, a computation that only hashes returns `honestEval (overwrite W t).1 x` with
  certainty.
* `signReads`, `challengeReads`, `challengedReads`, `gameReads M A keys`: the game after key
  generation with the keys `keys`, signing and verification as read programs.
* `intertwines_game`, `evalDistMap_game_eq_reads`: against `(overwrite W t).1`, consistent with a
  table `v` at `S_0`, the game has the law of `gameReads M A (v.publicKey, v.secretKey S0)`
  against `spongeFnReadRuntime HashOutput HashDomain t W m`.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open LeanXmss HashSig HashSig.OverPermutation
open Quantum.Sponge (Hw HwRead hwReadSpec hwReadCmdSpec spongeFnReadRuntime spongeFnHw overwrite
  ReadsTo readsTo_pure ReadsTo.bind ReadsTo.map readCall readsTo_readCall keepMem hwAt hwCol
  hwAt_basis conjTranspose_hwCol_mul_self intertwines_run_spongeFnHw intertwines_run_pure
  intertwines_run₂_pure intertwines_run₂_bind intertwines_run₂_act_bind intertwines_run_of_run₂
  intertwines_run₂_of_run intertwines_run_bind intertwines_substitute run₂_bind_of_classicalOn_pure
  evalDistMap_eq_of_intertwines)
open Quantum.SufCma (QueriesSatisfy trace trace_query_bind queriesSatisfy_pure queriesSatisfy_bind
  queriesSatisfy_sequenceFin)

/-! ## Verification only hashes -/

section isHash

variable {f : QueryImpl RomOracles Id}

theorem isHash_th (P : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    QueriesSatisfy f IsHash (Over.th hashQ P fields payload) :=
  queriesSatisfy_bind (isHash_hashQ _) (queriesSatisfy_pure _)

theorem isHash_walkChain {n : ℕ} {step : Fin n → Digest → OracleComp RomOracles Digest}
    (hs : ∀ i d, QueriesSatisfy f IsHash (step i d)) :
    ∀ start steps value, QueriesSatisfy f IsHash (walkChain step start steps value)
  | _, 0, _ => queriesSatisfy_pure _
  | start, steps + 1, value => by
    rw [walkChain]
    refine queriesSatisfy_bind (isHash_walkChain hs start steps value) ?_
    split
    · exact hs _ _
    · exact queriesSatisfy_pure _

theorem isHash_foldPath {node : ℕ → ℕ → HashInput → OracleComp RomOracles Digest}
    (hn : ∀ l i p, QueriesSatisfy f IsHash (node l i p)) (leafIndex : ℕ)
    (sibling : ℕ → Digest) :
    ∀ levels value, QueriesSatisfy f IsHash (foldPath node leafIndex sibling levels value)
  | 0, _ => queriesSatisfy_pure _
  | levels + 1, value => by
    rw [foldPath]
    exact queriesSatisfy_bind (isHash_foldPath hn leafIndex sibling levels value) (hn _ _ _)

theorem isHash_otsLeaf (P : PublicParameter) (l : Layer) (e : KeyIndex) (message : HashInput)
    (randomizer : Randomizer) (values : ChainIndex → Digest) :
    QueriesSatisfy f IsHash (Over.otsLeaf hashQ P l e message randomizer values) := by
  rw [Over.otsLeaf]
  refine queriesSatisfy_bind (isHash_th _ _ _) ?_
  split
  · exact queriesSatisfy_bind (queriesSatisfy_sequenceFin fun _ ↦
      isHash_walkChain (fun _ _ ↦ isHash_th _ _ _) _ _ _)
      (queriesSatisfy_bind (isHash_th _ _ _) (queriesSatisfy_pure _))
  · exact queriesSatisfy_pure _

theorem isHash_layerRoot (P : PublicParameter) (l : Layer) (e : KeyIndex) (message : HashInput)
    (sig : LayerSignature) :
    QueriesSatisfy f IsHash (Over.layerRoot hashQ P l e message sig) := by
  rw [Over.layerRoot]
  refine queriesSatisfy_bind (isHash_otsLeaf _ _ _ _ _ _) ?_
  split
  · exact queriesSatisfy_bind
      (isHash_foldPath (fun _ _ _ ↦ isHash_th _ _ _) _ _ _ _) (queriesSatisfy_pure _)
  · exact queriesSatisfy_pure _

/-- **Verification only hashes.** -/
theorem isHash_verify (pk : PublicKey) (forgery : Forgery) :
    QueriesSatisfy f IsHash (xmssRom.verify pk forgery) := by
  change QueriesSatisfy f IsHash (Over.verify hashQ pk forgery.message forgery.signature)
  rw [Over.verify]
  refine queriesSatisfy_bind (isHash_layerRoot _ _ _ _ _) ?_
  split
  · refine queriesSatisfy_bind (isHash_layerRoot _ _ _ _ _) ?_
    split <;> exact queriesSatisfy_pure _
  · exact queriesSatisfy_pure _

end isHash

/-! ## Hashes as read ports -/

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The model's oracles by read ports** beside a held register `B`: a hash of `x` is the read
port of `h` at `x` (keeping the memory), logging `x`; coins are uniform coins. -/
noncomputable def romReadImpl (B : QReg) :
    QueryImpl RomOracles
      (StateT (List HashDomain) (QComp (hwReadSpec HashOutput HashDomain M) B B))
  | .inl n => liftM (QComp.coinImpl (hwReadSpec HashOutput HashDomain M) B n)
  | .inr x => fun log ↦ (readCall (.readH x keepMem) B).bind fun r ↦
      QuantumComp₂.pure (r.1.getD 0, log ++ [x])

/-- **A computation over the model's oracles as a program of read ports**: its result and the
inputs it hashes. -/
noncomputable def readsProgram (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    QComp (hwReadSpec HashOutput HashDomain M) B B (α × List HashDomain) :=
  (simulateQ (romReadImpl M B) x).run []

variable {M} {t : (HashDomain → HashOutput) × (HashOutput → HashDomain) ×
  (HashOutput → HashDomain)} {W : Hw HashOutput HashDomain} {m : M} {B : QReg}

theorem readsTo_run_simulateQ {P : RomOracles.Domain → Prop} (hP : ∀ n, ¬P (.inl n))
    {α : Type} (x : OracleComp RomOracles α)
    (hx : QueriesSatisfy (romAnswers (overwrite W t).1) P x) (log : List HashDomain) :
    ReadsTo t W m ((simulateQ (romReadImpl M B) x).run log)
      (evalWithAnswerFn (romAnswers (overwrite W t).1) x,
        log ++ trace (romAnswers (overwrite W t).1) hashRead x) := by
  induction x using OracleComp.inductionOn generalizing log with
  | pure a =>
    rw [Quantum.SufCma.trace_pure, List.append_nil]
    exact readsTo_pure (a, log)
  | query_bind q k ih =>
    have hq := trace_query_bind (romAnswers (overwrite W t).1) (fun t ↦ [t]) q k
    have hPq : P q := hx q (by
      rw [Quantum.SufCma.queries, hq]
      exact List.mem_append_left _ (List.mem_singleton_self q))
    have hk : QueriesSatisfy (romAnswers (overwrite W t).1) P
        (k (romAnswers (overwrite W t).1 q)) := fun q' hq' ↦ hx q' (by
      rw [Quantum.SufCma.queries, hq]
      exact List.mem_append_right _ hq')
    rcases q with n | y
    · exact absurd hPq (hP n)
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind,
        evalWithAnswerFn_liftM_query, trace_query_bind, ← List.append_assoc]
      have h1 : ReadsTo t W m ((romReadImpl M B (.inr y)).run log)
          ((overwrite W t).1 y, log ++ [y]) :=
        show ReadsTo t W m ((readCall (.readH y keepMem) B).bind fun r ↦
            QuantumComp₂.pure (r.1.getD 0, log ++ [y])) _ from
          (readsTo_readCall (.readH y keepMem) rfl B).bind (readsTo_pure _)
      exact h1.bind (ih _ hk (log ++ [y]))

/-- **The read program returns the honest evaluation with certainty**: on the block `(W, m)`
against `t`, the read program of a computation that only hashes returns
`honestEval (overwrite W t).1 x`, its result and the inputs it hashes. -/
theorem readsTo_readsProgram {P : RomOracles.Domain → Prop} (hP : ∀ n, ¬P (.inl n))
    {α : Type} (x : OracleComp RomOracles α)
    (hx : QueriesSatisfy (romAnswers (overwrite W t).1) P x) :
    ReadsTo t W m (readsProgram M B x) (honestEval (overwrite W t).1 x) := by
  have h := readsTo_run_simulateQ (m := m) (B := B) hP x hx []
  rw [List.nil_append] at h
  exact h

/-! ## The challenger with honest reads -/

variable (M)

/-- The signer's answer to the request `r` as reads: relabel the adversary's register, then run
the read program of the signer. -/
noncomputable def signReads (sk : SecretKey) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    QComp (hwReadSpec HashOutput HashDomain M) A
      (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
      (Option Signature) :=
  (QComp.act (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ (readsProgram M _ (xmssRom.sign sk r)).map Prod.fst

/-- **The challenger with honest reads**: a local operation and a hash call are the challenger's,
lifted to port `h` and to the read signature; a signing request is answered by the read program
of the signer (`signReads`). -/
noncomputable def challengeReads (sk : SecretKey) :
    CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0}
        (SufCma.advSpec SigningRequest (Option Signature)))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec HashOutput HashDomain M))
  | A, .prim o => (liftH (SufCma.challenge xmssRom sk A (.prim o))).liftOrdinary
  | A, .query .hash E ℓ => (liftH (SufCma.challenge xmssRom sk A (.query .hash E ℓ))).liftOrdinary
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (signReads M sk r E ℓ) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program with the challenger with honest reads substituted. -/
noncomputable def challengedReads (sk : SecretKey) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpec SigningRequest (Option Signature)) A B α) :
    QComp (hwReadSpec HashOutput HashDomain M) A B α :=
  IFreeM.substitute (challengeReads M sk) x

/-- **The game with honest reads, after key generation**: from the keys, the adversary against
`challengeReads` with its signing transcript, the verification of its forgery as a read program,
and the winning condition. -/
noncomputable def gameReads (A : Adversary) (keys : PublicKey × SecretKey) :
    QComp (hwReadSpec HashOutput HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool :=
  (challengedReads M keys.2 (SufCma.withSignLog (A keys.1))).bind fun run ↦
    ((readsProgram M _ (xmssRom.verify keys.1 run.1)).map Prod.fst).bind
      fun verified ↦ QuantumComp₂.pure (xmssRom.winningCondition run.2 run.1 && verified)

variable {M}

/-! ## The game and its reads intertwine -/

variable (t W m)

/-- A program over the random oracle against `(overwrite W t).1` intertwines with its lift to
port `h` and the read signature on the block `(W, m)`. -/
theorem intertwines_liftH {Y : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} romSpec Y A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, Y u ↦ (hwAt W m).amplifyLeft p.1)
      ((additiveOracleRuntime (overwrite W t).1).run .instruments x)
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run .instruments
        ((liftH x).liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain M))) := by
  have e := run_spongeFnRuntime_liftH (overwrite W t).1 (overwrite W t).2.1 (overwrite W t).2.2
    LocalSig.Interp.instruments x
  have hsim := intertwines_run_spongeFnHw t W m LocalSig.Interp.instruments.{0} (liftH x)
  rw [e] at hsim
  have h : (spongeFnReadRuntime HashOutput HashDomain t W m).run .instruments
      ((liftH x).liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain M)) =
        (spongeFnHw HashOutput HashDomain t W m).toRuntime.run .instruments (liftH x) :=
    QuantumRuntime.run_liftOrdinary _ _ _ _
  rw [h]
  exact hsim

/-- An honest computation that returns `v` with certainty against `(overwrite W t).1`
intertwines with a read program that returns `v` with certainty on the block. -/
theorem intertwines_of_classicalOn_readsTo {α : Type}
    {x₁ : QComp romSpec B B α} {x₂ : QComp (hwReadSpec HashOutput HashDomain M) B B α} {a₀ : α}
    (h₁ : ClassicalOn (additiveOracleRuntime (overwrite W t).1) x₁ (pure a₀) LinearMap.id)
    (h₂ : ReadsTo t W m x₂ a₀) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft B)
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments x₁)
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments x₂) := by
  classical
  intro a
  rw [h₁ a, prEvent_pure]
  by_cases ha : a = a₀
  · subst ha
    refine h₂.1.trans ?_
    rw [ite_eq_left rfl, ENNReal.toReal_one, Complex.ofReal_one, one_smul]
    exact (LinearMap.comp_id _).symm
  · refine (h₂.2 a ha).trans ?_
    rw [ite_eq_right (Ne.symm ha), ENNReal.toReal_zero, Complex.ofReal_zero, zero_smul]
    exact (LinearMap.comp_zero _).symm

variable {t W m}

/-- The honest classical computations against the oracle of `H`. -/
theorem classicalOn_toQuantumAt_romImpl (H : HashDomain → HashOutput) (B : QReg) {α : Type}
    (oa : OracleComp RomOracles α) :
    ClassicalOn (additiveOracleRuntime H) (oa.toQuantumAt (SufCma.romImpl B))
      (simulateQ (eagerFunOracles H) oa) LinearMap.id := by
  rw [SufCma.romImpl_eq_funImpl]
  exact classicalOn_toQuantumAt_funImpl B H oa

/-- A computation that only hashes, run classically against the oracle of `H`, returns its
evaluation with certainty. -/
theorem classicalOn_toQuantumAt_romImpl_pure {H : HashDomain → HashOutput} {B : QReg}
    {P : RomOracles.Domain → Prop} (hP : ∀ n, ¬P (.inl n)) {α : Type}
    (oa : OracleComp RomOracles α) (hx : QueriesSatisfy (romAnswers H) P oa) :
    ClassicalOn (additiveOracleRuntime H) (oa.toQuantumAt (SufCma.romImpl B))
      (pure (evalWithAnswerFn (romAnswers H) oa)) LinearMap.id :=
  (classicalOn_toQuantumAt_romImpl H B oa).congr
    (simulateQ_eq_pure_of_queriesSatisfy (fun _ ↦ rfl) hP oa hx) rfl

/-- A computation that only hashes intertwines with its read program. -/
theorem intertwines_readsProgram {P : RomOracles.Domain → Prop} (hP : ∀ n, ¬P (.inl n))
    {α : Type} (oa : OracleComp RomOracles α)
    (hx : QueriesSatisfy (romAnswers (overwrite W t).1) P oa) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft B)
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments
        (oa.toQuantumAt (SufCma.romImpl B)))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments
        ((readsProgram M B oa).map Prod.fst)) :=
  intertwines_of_classicalOn_readsTo t W m (classicalOn_toQuantumAt_romImpl_pure hP oa hx)
    ((readsTo_readsProgram hP oa hx).map Prod.fst)

/-- **The challenger and the challenger with honest reads intertwine on every command**, for the
secret key of a table consistent with `(overwrite W t).1`. -/
theorem intertwines_challenge {S0 : MasterSeed} {v : QTable}
    (hv : Consistent S0 v (overwrite W t).1) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (SufCma.advSpec SigningRequest (Option Signature))).A A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0}
          (SufCma.advSpec SigningRequest (Option Signature))).B A c //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0}
          (SufCma.advSpec SigningRequest (Option Signature))).src A c b = u} ↦
        (hwAt W m).amplifyLeft p.1)
      ((additiveOracleRuntime (overwrite W t).1).run .instruments
        (SufCma.challenge xmssRom (v.secretKey S0) A c))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run .instruments
        (challengeReads M (v.secretKey S0) A c)) := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact intertwines_liftH t W m _
  · exact intertwines_liftH t W m _
  · change DSubInstrument.Intertwines _ _
      ((additiveOracleRuntime (overwrite W t).1).run .instruments
        (QuantumComp.bind (SufCma.signTree xmssRom (v.secretKey S0) r E ℓ) _))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run .instruments
        (QuantumComp.bind (signReads M (v.secretKey S0) r E ℓ) _))
    refine intertwines_run_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
      (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
      (intertwines_run_of_run₂ (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) ?_) fun p ↦ ?_
    · rw [SufCma.signTree, signReads]
      exact intertwines_run₂_act_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) (A := A)
        (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E)) _
        fun _ ↦ intertwines_readsProgram QTable.not_signRead_inl _ (QTable.signReads_sign hv r)
    · exact intertwines_run_pure (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) _

/-- **The game and its reads intertwine** on the block `(W, m)`: against `(overwrite W t).1`,
consistent with the table `v` at `S_0`, the game runs as `gameReads` from the table's keys. -/
theorem intertwines_game {S0 : MasterSeed} {v : QTable} (hv : Consistent S0 v (overwrite W t).1)
    (A : Adversary) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt W m).amplifyLeft (QReg.of Unit))
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments (SufCma.game xmssRom S0 A))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments
        (gameReads M A (v.publicKey, v.secretKey S0))) := by
  rw [SufCma.game, run₂_bind_of_classicalOn_pure
    ((classicalOn_toQuantumAt_romImpl_pure QTable.not_tableRead_inl _
      (QTable.cellReads_generateKeys hv)).congr
      (congrArg pure (QTable.eval_generateKeys hv)) rfl)]
  dsimp only
  refine intertwines_run₂_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
    (intertwines_run₂_of_run (intertwines_substitute
      (spec₀ := SufCma.advSpec SigningRequest (Option Signature))
      (R₁ := additiveOracleRuntime (overwrite W t).1)
      (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
      (fun A c ↦ intertwines_challenge hv A c) _))
    fun run ↦ ?_
  exact intertwines_run₂_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
    (intertwines_readsProgram not_isHash_inl _ (isHash_verify _ _))
    fun _ ↦ intertwines_run₂_pure _

/-- **The game is its reads at a fixed function**: against `(overwrite W t).1`, consistent with
the table `v` at `S_0`, the game has the law of `gameReads M A (v.publicKey, v.secretKey S0)`
against the classical reads of `t` with the hardwired cells `W`. -/
theorem evalDistMap_game_eq_reads {S0 : MasterSeed} {v : QTable}
    (hv : Consistent S0 v (overwrite W t).1) (A : Adversary) (ρ : SubState (QReg.of Unit))
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (additiveOracleRuntime (overwrite W t).1).evalDistMap .instruments
        (SufCma.game xmssRom S0 A) ρ f =
      (spongeFnReadRuntime HashOutput HashDomain t W m).evalDistMap .instruments
        (gameReads M A (v.publicKey, v.secretKey S0)) ρ f :=
  evalDistMap_eq_of_intertwines (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (K := hwCol W m)
    (conjTranspose_hwCol_mul_self W m) (hwAt_basis W m)
    (intertwines_run_of_run₂ (intertwines_game hv A)) ρ f

end Quantum.Qrom.Xmss

end
