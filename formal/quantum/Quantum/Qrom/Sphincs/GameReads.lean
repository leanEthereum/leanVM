module

public import Quantum.Qrom.Sphincs.HonestTable
public import Quantum.Qrom.Xmss.GameReads

@[expose] public section

/-!
# leanSPHINCS's game with honest read ports, in the QROM

The QROM game's honest hashing (key generation, each signature, the forgery's verification) is a
classical computation: against a fixed function `H`, each hash is one basis call of the port. With
the two `H_msg` calls of a message regrouped into one cell (`Quantum.Qrom.Regroup`, `hmsgRoute`),
the game against `H = regroup hmsgRoute F` runs as its regrouped calls against `F` with pair
answers. Here the honest hashing becomes a program of the classical read ports of runtime 1 over
`F` (`hwReadSpec PairOut HashDomain M`, port `readH`): a hash of `x` reads `F` at the cell of
`x` and takes the component of `x`'s slot. The adversary's calls are regrouped and lifted to port
`h` (`liftH (regroupCalls hmsgRoute _)`). The generic intertwining machinery is the QRPM's
(`Quantum.Xmss.GameReads`), at `X := PairOut`, `Z := HashDomain`.

* `isHash_verify`: verification only hashes (never flips a coin).
* `romReadImpl M B`, `readsProgram M B x`: a computation over the model's oracles with every hash
  a read port at its regrouped cell, logging the inputs. `readsTo_readsProgram`: on the block
  `(W, m)` against `t`, a computation that only hashes returns
  `honestEval (regroup hmsgRoute (overwrite W t).1) x` with certainty.
* `signReads`, `challengeReads`, `challengedReads`, `gameReads M A keys`: the game after key
  generation with the keys `keys`, signing and verification as read programs.
* `intertwines_game`, `evalDistMap_game_eq_reads`: against `regroup hmsgRoute (overwrite W t).1`,
  with `(overwrite W t).1` consistent with a table `v` at `S_0`, the game has the law of
  `gameReads M A (v.publicKey, S0)` against `spongeFnReadRuntime PairOut HashDomain t W m`.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig hiding PublicKey
open HashSig.OverPermutation (sequenceFin walkChain foldPath)
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum.Sponge (Hw hwReadSpec hwReadCmdSpec spongeFnReadRuntime spongeFnHw overwrite
  ReadsTo readsTo_pure ReadsTo.bind ReadsTo.map readCall readsTo_readCall keepMem hwAt hwCol
  hwAt_basis conjTranspose_hwCol_mul_self intertwines_run_spongeFnHw intertwines_run_pure
  intertwines_run₂_pure intertwines_run₂_bind intertwines_run₂_act_bind intertwines_run_of_run₂
  intertwines_run₂_of_run intertwines_run_bind intertwines_substitute run₂_bind_of_classicalOn_pure
  evalDistMap_eq_of_intertwines)
open Quantum.SufCma (QueriesSatisfy trace trace_query_bind queriesSatisfy_pure queriesSatisfy_bind
  queriesSatisfy_sequenceFin)
open Quantum.Qrom.Xmss (romAnswers hashRead honestEval IsHash not_isHash_inl isHash_hashQ
  isHash_walkChain isHash_foldPath classicalOn_toQuantumAt_romImpl_pure)

/-- The answers of the regrouped random function: pairs of hash outputs. -/
abbrev PairOut : Type :=
  HashOutput × HashOutput

/-! ## Verification only hashes -/

section isHash

variable {f : QueryImpl RomOracles Id}

theorem isHash_addressedHash (seed : PublicParameter) (address : Address) (payload : HashInput) :
    QueriesSatisfy f IsHash (LeanSphincsOver.addressedHash hashQ seed address payload) :=
  queriesSatisfy_bind (isHash_hashQ _) (queriesSatisfy_pure _)

theorem isHash_encode (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (message : Digest) (counter : EncodingCounter) :
    QueriesSatisfy f IsHash (LeanSphincsOver.encode hashQ seed l τ e message counter) :=
  queriesSatisfy_bind (isHash_addressedHash _ _ _) (queriesSatisfy_pure _)

theorem isHash_otsLeaf (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (message : Digest) (counter : EncodingCounter) (values : ChainIndex → Digest) :
    QueriesSatisfy f IsHash (LeanSphincsOver.otsLeaf hashQ seed l τ e message counter values) := by
  rw [LeanSphincsOver.otsLeaf]
  refine queriesSatisfy_bind (isHash_encode _ _ _ _ _ _) ?_
  split
  · exact queriesSatisfy_bind (queriesSatisfy_sequenceFin fun _ ↦
      isHash_walkChain (fun _ _ ↦ isHash_addressedHash _ _ _) _ _ _)
      (queriesSatisfy_bind (isHash_addressedHash _ _ _) (queriesSatisfy_pure _))
  · exact queriesSatisfy_pure _

theorem isHash_treeFold (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (path : ℕ → Digest) (levels : ℕ) (value : Digest) :
    QueriesSatisfy f IsHash (LeanSphincsOver.treeFold hashQ seed l τ e path levels value) :=
  isHash_foldPath (fun _ _ _ ↦ isHash_addressedHash _ _ _) _ _ _ _

theorem isHash_verifyLayers (seed : PublicParameter) (idx : Index) (signature : Signature) :
    ∀ layersLeft message, QueriesSatisfy f IsHash
      (LeanSphincsOver.verifyLayers hashQ seed idx signature layersLeft message)
  | 0, _ => queriesSatisfy_pure _
  | layersLeft + 1, message => by
    rw [LeanSphincsOver.verifyLayers]
    split
    · refine queriesSatisfy_bind (isHash_otsLeaf _ _ _ _ _ _ _) ?_
      split
      · refine queriesSatisfy_bind (isHash_treeFold _ _ _ _ _ _ _) ?_
        split
        · exact queriesSatisfy_pure _
        · exact isHash_verifyLayers seed idx signature layersLeft _
      · exact queriesSatisfy_pure _
    · exact queriesSatisfy_pure _

theorem isHash_messageDigest (pk : PublicKey) (randomizer : Randomizer) (message : Message) :
    QueriesSatisfy f IsHash (LeanSphincsOver.messageDigest hashQ pk randomizer message) :=
  queriesSatisfy_bind (queriesSatisfy_sequenceFin fun _ ↦ isHash_hashQ _) (queriesSatisfy_pure _)

theorem isHash_forsRecover (seed : PublicParameter) (idx : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    QueriesSatisfy f IsHash (LeanSphincsOver.forsRecover hashQ seed idx leaves opening) :=
  queriesSatisfy_bind (queriesSatisfy_sequenceFin fun _ ↦
    queriesSatisfy_bind (isHash_addressedHash _ _ _)
      (isHash_foldPath (fun _ _ _ ↦ isHash_addressedHash _ _ _) _ _ _ _))
    (isHash_addressedHash _ _ _)

/-- **Verification only hashes.** -/
theorem isHash_verify (pk : PublicKey) (forgery : Forgery) :
    QueriesSatisfy f IsHash (sphincsRom.verify pk forgery) := by
  change QueriesSatisfy f IsHash
    (LeanSphincsOver.verify hashQ pk forgery.message forgery.signature)
  rw [LeanSphincsOver.verify]
  refine queriesSatisfy_bind (isHash_messageDigest _ _ _) ?_
  refine queriesSatisfy_bind (isHash_forsRecover _ _ _ _) ?_
  refine queriesSatisfy_bind (isHash_verifyLayers _ _ _ _ _) ?_
  split <;> exact queriesSatisfy_pure _

end isHash

/-! ## Hashes as read ports of the regrouped function -/

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The model's oracles by read ports of the regrouped function** beside a held register `B`:
a hash of `x` reads `F` at the cell `c` with `hmsgRoute (x, false) = (c, b)` (keeping the memory)
and answers component `b`, logging `x`; coins are uniform coins. -/
noncomputable def romReadImpl (B : QReg) :
    QueryImpl RomOracles
      (StateT (List Qrom.HashDomain) (QComp (hwReadSpec PairOut Qrom.HashDomain M) B B))
  | .inl n => liftM (QComp.coinImpl (hwReadSpec PairOut Qrom.HashDomain M) B n)
  | .inr x => fun log ↦ (readCall (.readH (hmsgRoute (x, false)).1 keepMem) B).bind fun r ↦
      QuantumComp₂.pure (pairPart (hmsgRoute (x, false)).2 (r.1.getD 0), log ++ [x])

/-- **A computation over the model's oracles as a program of read ports**: its result and the
inputs it hashes. -/
noncomputable def readsProgram (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    QComp (hwReadSpec PairOut Qrom.HashDomain M) B B (α × List Qrom.HashDomain) :=
  (simulateQ (romReadImpl M B) x).run []

variable {M} {t : (Qrom.HashDomain → PairOut) × (PairOut → Qrom.HashDomain) ×
  (PairOut → Qrom.HashDomain)} {W : Hw PairOut Qrom.HashDomain} {m : M} {B : QReg}

theorem readsTo_run_simulateQ {P : RomOracles.Domain → Prop} (hP : ∀ n, ¬P (.inl n))
    {α : Type} (x : OracleComp RomOracles α)
    (hx : QueriesSatisfy (romAnswers (regroup hmsgRoute (overwrite W t).1)) P x)
    (log : List Qrom.HashDomain) :
    ReadsTo t W m ((simulateQ (romReadImpl M B) x).run log)
      (evalWithAnswerFn (romAnswers (regroup hmsgRoute (overwrite W t).1)) x,
        log ++ trace (romAnswers (regroup hmsgRoute (overwrite W t).1)) hashRead x) := by
  induction x using OracleComp.inductionOn generalizing log with
  | pure a =>
    rw [Quantum.SufCma.trace_pure, List.append_nil]
    exact readsTo_pure (a, log)
  | query_bind q k ih =>
    have hq := trace_query_bind (romAnswers (regroup hmsgRoute (overwrite W t).1))
      (fun t ↦ [t]) q k
    have hPq : P q := hx q (by
      rw [Quantum.SufCma.queries, hq]
      exact List.mem_append_left _ (List.mem_singleton_self q))
    have hk : QueriesSatisfy (romAnswers (regroup hmsgRoute (overwrite W t).1)) P
        (k (romAnswers (regroup hmsgRoute (overwrite W t).1) q)) := fun q' hq' ↦ hx q' (by
      rw [Quantum.SufCma.queries, hq]
      exact List.mem_append_right _ hq')
    rcases q with n | y
    · exact absurd hPq (hP n)
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind,
        evalWithAnswerFn_liftM_query, trace_query_bind, ← List.append_assoc]
      have h1 : ReadsTo t W m ((romReadImpl M B (.inr y)).run log)
          (regroup hmsgRoute (overwrite W t).1 y, log ++ [y]) :=
        show ReadsTo t W m ((readCall (.readH (hmsgRoute (y, false)).1 keepMem) B).bind fun r ↦
            QuantumComp₂.pure (pairPart (hmsgRoute (y, false)).2 (r.1.getD 0), log ++ [y])) _ from
          (readsTo_readCall (.readH (hmsgRoute (y, false)).1 keepMem) rfl B).bind
            (readsTo_pure _)
      exact h1.bind (ih _ hk (log ++ [y]))

/-- **The read program returns the honest evaluation with certainty**: on the block `(W, m)`
against `t`, the read program of a computation that only hashes returns
`honestEval (regroup hmsgRoute (overwrite W t).1) x`, its result and the inputs it hashes. -/
theorem readsTo_readsProgram {P : RomOracles.Domain → Prop} (hP : ∀ n, ¬P (.inl n))
    {α : Type} (x : OracleComp RomOracles α)
    (hx : QueriesSatisfy (romAnswers (regroup hmsgRoute (overwrite W t).1)) P x) :
    ReadsTo t W m (readsProgram M B x) (honestEval (regroup hmsgRoute (overwrite W t).1) x) := by
  have h := readsTo_run_simulateQ (m := m) (B := B) hP x hx []
  rw [List.nil_append] at h
  exact h

/-! ## The challenger with honest reads -/

variable (M)

/-- The signer's answer to the request `r` as reads: relabel the adversary's register, then run
the read program of the signer. -/
noncomputable def signReads (sk : SecretKey) (r : Message) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec Message (Option Signature)).In (.sign r) × E) :
    QComp (hwReadSpec PairOut Qrom.HashDomain M) A
      (QReg.of ((SufCma.advSpec Message (Option Signature)).Out (.sign r) × E))
      (Option Signature) :=
  (QComp.act (B := QReg.of ((SufCma.advSpec Message (Option Signature)).Out (.sign r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ (readsProgram M _ (sphincsRom.sign sk r)).map Prod.fst

/-- **The challenger with honest reads**: a local operation and a hash call are the challenger's,
regrouped and lifted to port `h` and to the read signature; a signing request is answered by the
read program of the signer (`signReads`). -/
noncomputable def challengeReads (sk : SecretKey) :
    CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0}
        (SufCma.advSpec Message (Option Signature)))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0}
        (hwReadSpec PairOut Qrom.HashDomain M))
  | A, .prim o =>
      (liftH (regroupCalls hmsgRoute (SufCma.challenge sphincsRom sk A (.prim o)))).liftOrdinary
  | A, .query .hash E ℓ =>
      (liftH (regroupCalls hmsgRoute
        (SufCma.challenge sphincsRom sk A (.query .hash E ℓ)))).liftOrdinary
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (signReads M sk r E ℓ) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program with the challenger with honest reads substituted. -/
noncomputable def challengedReads (sk : SecretKey) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpec Message (Option Signature)) A B α) :
    QComp (hwReadSpec PairOut Qrom.HashDomain M) A B α :=
  IFreeM.substitute (challengeReads M sk) x

/-- **The game with honest reads, after key generation**: from the keys, the adversary against
`challengeReads` with its signing transcript, the verification of its forgery as a read program,
and the winning condition. -/
noncomputable def gameReads (A : SufCma.Adversary PublicKey Message (Option Signature) Forgery)
    (keys : PublicKey × SecretKey) :
    QComp (hwReadSpec PairOut Qrom.HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool :=
  (challengedReads M keys.2 (SufCma.withSignLog (A keys.1))).bind fun run ↦
    ((readsProgram M _ (sphincsRom.verify keys.1 run.1)).map Prod.fst).bind
      fun verified ↦ QuantumComp₂.pure (sphincsRom.winningCondition run.2 run.1 && verified)

variable {M}

/-! ## The game and its reads intertwine -/

variable (t W m)

/-- A program over the random oracle against `regroup hmsgRoute (overwrite W t).1` intertwines
with its regrouped calls lifted to port `h` and the read signature on the block `(W, m)`. -/
theorem intertwines_liftH {Y : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} romSpec Y A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, Y u ↦ (hwAt W m).amplifyLeft p.1)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run .instruments x)
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run .instruments
        ((liftH (regroupCalls hmsgRoute x)).liftOrdinary
          (t := hwReadCmdSpec PairOut Qrom.HashDomain M))) := by
  rw [← run_regroup_eq]
  have e := run_spongeFnRuntime_liftH (overwrite W t).1 (overwrite W t).2.1 (overwrite W t).2.2
    LocalSig.Interp.instruments (regroupCalls hmsgRoute x)
  have hsim := intertwines_run_spongeFnHw t W m LocalSig.Interp.instruments.{0}
    (liftH (regroupCalls hmsgRoute x))
  rw [e] at hsim
  have h : (spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run .instruments
      ((liftH (regroupCalls hmsgRoute x)).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain M)) =
        (spongeFnHw PairOut Qrom.HashDomain t W m).toRuntime.run .instruments
          (liftH (regroupCalls hmsgRoute x)) :=
    QuantumRuntime.run_liftOrdinary _ _ _ _
  rw [h]
  exact hsim

/-- An honest computation that returns `a₀` with certainty against the regrouped function
intertwines with a read program that returns `a₀` with certainty on the block. -/
theorem intertwines_of_classicalOn_readsTo {α : Type}
    {x₁ : QComp romSpec B B α} {x₂ : QComp (hwReadSpec PairOut Qrom.HashDomain M) B B α} {a₀ : α}
    (h₁ : ClassicalOn (additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)) x₁ (pure a₀)
      LinearMap.id)
    (h₂ : ReadsTo t W m x₂ a₀) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft B)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments x₁)
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run₂ .instruments x₂) := by
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

/-- A computation that only hashes intertwines with its read program. -/
theorem intertwines_readsProgram {P : RomOracles.Domain → Prop} (hP : ∀ n, ¬P (.inl n))
    {α : Type} (oa : OracleComp RomOracles α)
    (hx : QueriesSatisfy (romAnswers (regroup hmsgRoute (overwrite W t).1)) P oa) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft B)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments
        (oa.toQuantumAt (SufCma.romImpl B)))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run₂ .instruments
        ((readsProgram M B oa).map Prod.fst)) :=
  intertwines_of_classicalOn_readsTo t W m (classicalOn_toQuantumAt_romImpl_pure hP oa hx)
    ((readsTo_readsProgram hP oa hx).map Prod.fst)

/-- **The challenger and the challenger with honest reads intertwine on every command**, for the
secret key `S_0` of a table consistent with `(overwrite W t).1`. -/
theorem intertwines_challenge {S0 : MasterSeed} {v : QTable}
    (hv : Consistent S0 v (overwrite W t).1) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (SufCma.advSpec Message (Option Signature))).A A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0}
          (SufCma.advSpec Message (Option Signature))).B A c //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0}
          (SufCma.advSpec Message (Option Signature))).src A c b = u} ↦
        (hwAt W m).amplifyLeft p.1)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run .instruments
        (SufCma.challenge sphincsRom S0 A c))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run .instruments
        (challengeReads M S0 A c)) := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact intertwines_liftH t W m _
  · exact intertwines_liftH t W m _
  · change DSubInstrument.Intertwines _ _
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run .instruments
        (QuantumComp.bind (SufCma.signTree sphincsRom S0 r E ℓ) _))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run .instruments
        (QuantumComp.bind (signReads M S0 r E ℓ) _))
    refine intertwines_run_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
      (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m)
      (intertwines_run_of_run₂ (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m) ?_) fun p ↦ ?_
    · rw [SufCma.signTree, signReads]
      exact intertwines_run₂_act_bind
        (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m) (A := A)
        (B := QReg.of ((SufCma.advSpec Message (Option Signature)).Out (.sign r) × E)) _
        fun _ ↦ intertwines_readsProgram (not_romRead_inl _) _
          (signReads_sign (agrees_regroup hv) r)
    · exact intertwines_run_pure
        (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m) _

/-- **The game and its reads intertwine** on the block `(W, m)`: against
`regroup hmsgRoute (overwrite W t).1`, with `(overwrite W t).1` consistent with the table `v` at
`S_0`, the game runs as `gameReads` from the table's keys. -/
theorem intertwines_game {S0 : MasterSeed} {v : QTable} (hv : Consistent S0 v (overwrite W t).1)
    (A : SufCma.Adversary PublicKey Message (Option Signature) Forgery) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt W m).amplifyLeft (QReg.of Unit))
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments
        (SufCma.game sphincsRom S0 A))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run₂ .instruments
        (gameReads M A (v.publicKey, S0))) := by
  rw [SufCma.game, run₂_bind_of_classicalOn_pure
    ((classicalOn_toQuantumAt_romImpl_pure (not_romRead_inl _) _
      (cellReads_generateKeys (agrees_regroup hv))).congr
      (congrArg pure (eval_generateKeys (agrees_regroup hv))) rfl)]
  dsimp only
  refine intertwines_run₂_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m)
    (intertwines_run₂_of_run (intertwines_substitute
      (spec₀ := SufCma.advSpec Message (Option Signature))
      (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
      (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m)
      (fun A c ↦ intertwines_challenge hv A c) _))
    fun run ↦ ?_
  exact intertwines_run₂_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m)
    (intertwines_readsProgram not_isHash_inl _ (isHash_verify _ _))
    fun _ ↦ intertwines_run₂_pure _

/-- **The game is its reads at a fixed function**: against `regroup hmsgRoute (overwrite W t).1`,
with `(overwrite W t).1` consistent with the table `v` at `S_0`, the game has the law of
`gameReads M A (v.publicKey, S0)` against the classical reads of `t` with the hardwired cells
`W`. -/
theorem evalDistMap_game_eq_reads {S0 : MasterSeed} {v : QTable}
    (hv : Consistent S0 v (overwrite W t).1)
    (A : SufCma.Adversary PublicKey Message (Option Signature) Forgery)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).evalDistMap .instruments
        (SufCma.game sphincsRom S0 A) ρ f =
      (spongeFnReadRuntime PairOut Qrom.HashDomain t W m).evalDistMap .instruments
        (gameReads M A (v.publicKey, S0)) ρ f :=
  evalDistMap_eq_of_intertwines
    (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (K := hwCol W m)
    (conjTranspose_hwCol_mul_self W m) (hwAt_basis W m)
    (intertwines_run_of_run₂ (intertwines_game hv A)) ρ f

end Quantum.Qrom.Sphincs

end
