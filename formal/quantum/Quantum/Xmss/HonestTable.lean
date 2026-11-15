module

public import Quantum.Xmss.Keccak
public import Quantum.Sponge.Assembly.Prep
public import Common.WithHashBridge

@[expose] public section

/-!
# leanXMSS's honest computations as sponge reads

For a fixed sponge view, the keys `t = (h, k, k')` and the inner permutation `π` (so
`φ = spongePerm t π`), leanXMSS's honest key generation and signing are deterministic classical
computations.

* `honestEval t π x`: a hash-query computation (the statement's scheme in its hash-query form,
  `LeanXmss.RandomPermutationModel.schemeWithHashFromSeed`) with every hash an evaluation of the
  sponge through logged reads of `h`, `k`, `k'` (`Quantum.Sponge.spongeEvalM` on `blocks input`).
  Its result is the evaluation with the honest hash `spongeOut φ` (`fst_honestEval`), its reads
  are the sponge reads of the queried inputs in order (`snd_honestEval`), and it depends on `t`
  only through the values it reads (`honestEval_congr`).
* `simulateQ_schemeHash`, `simulateQ_generateKeys`, `simulateQ_sign`, `simulateQ_verify`: the
  statement's `sufCmaScheme` over the permutation `statePerm φ` of `KeccakState` (which
  `keccakStateEquiv` transports to `φ`) returns what `honestEval` returns.
* `HonestTable`: the keys, `π` and the master seed `S_0`. Its values (`seed`, `param`,
  `chainValue`, `treeValue`, `select`, `signature`) are functions, never an enumeration;
  `eval_keygen`, `eval_sign`: they are what key generation and signing return, so
  `simulateQ_generateKeys_eq`, `simulateQ_sign_eq`: the statement's algorithms return them.
* `honestInput`, `honestTail`, `target`: the honest input of each chain, leaf and node slot of the
  keygen table (`InTable`), its Msponge tail and its digest, the value at the slot's output
  (`target_eq_some`). `slotOf_honestTail`: the tail lies in its slot; `honestTail_eq_some_iff`: a
  tweakable-hash input has the honest tail of a slot exactly when its address and payload are the
  honest ones; `honestQueries_keygen`, `honestQueries_sign`: every hash call of key generation and
  of the signer whose tail lies in a chain, leaf or node slot is that slot's honest input.
* `Known D`, `Public D`: the table positions computable from the disclosed positions `D` (least
  fixed point, `known_iff`, `known_subset`) and the slots of the table whose payload is computable;
  `disclosedBy L r`: the positions the signature of request `r` discloses, `disclosures L reqs`
  those of the public key and the requests. Monotone in `D` (`known_mono`, `public_mono`) and in
  the requests (`disclosures_mono`).
-/

open OracleComp OracleSpec

namespace Quantum.Xmss

open Quantum.Sponge HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel
open LeanVM.Semantics (KeccakState)

/-! ## Computations answered by functions -/

section Answers

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- Answered by pure values in a lawful monad, a computation returns its evaluation with those
answers. -/
theorem simulateQ_eq_pure_evalWithAnswerFn {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl spec r) (f : QueryImpl spec Id) (h : ∀ t, impl t = pure (f t))
    (x : OracleComp spec α) : simulateQ impl x = pure (evalWithAnswerFn f x) := by
  induction x using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, h, pure_bind, ih, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query]

variable {ρ : Type}

/-- Answer each query `t` with `f t` and append `g t` to a log. -/
def traceImpl (f : QueryImpl spec Id) (g : spec.Domain → List ρ) :
    QueryImpl spec (StateM (List ρ)) :=
  fun t ↦ modifyGet fun l ↦ (f t, l ++ g t)

/-- The log of `x` answered by `f`, each query `t` logging `g t`. -/
def trace (f : QueryImpl spec Id) (g : spec.Domain → List ρ) (x : OracleComp spec α) : List ρ :=
  ((simulateQ (traceImpl f g) x).run []).2

/-- The queries `x` makes when answered by `f`, in order. -/
def queries (f : QueryImpl spec Id) (x : OracleComp spec α) : List spec.Domain :=
  trace f (fun t ↦ [t]) x

theorem trace_pure (f : QueryImpl spec Id) (g : spec.Domain → List ρ) (a : α) :
    trace f g (pure a : OracleComp spec α) = [] :=
  rfl

theorem run_simulateQ_traceImpl_query_bind (f : QueryImpl spec Id) (g : spec.Domain → List ρ)
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) (l : List ρ) :
    (simulateQ (traceImpl f g) ((liftM (spec.query t) : OracleComp spec _) >>= k)).run l =
      (simulateQ (traceImpl f g) (k (f t))).run (l ++ g t) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rfl

/-- **The logged evaluation**: the evaluation with the answers `f`, and the log appended. -/
theorem run_simulateQ_traceImpl (f : QueryImpl spec Id) (g : spec.Domain → List ρ)
    (x : OracleComp spec α) (l : List ρ) :
    (simulateQ (traceImpl f g) x).run l = (evalWithAnswerFn f x, l ++ trace f g x) := by
  induction x using OracleComp.inductionOn generalizing l with
  | pure a => exact Prod.ext rfl (List.append_nil l).symm
  | query_bind t k ih =>
    rw [trace, run_simulateQ_traceImpl_query_bind, run_simulateQ_traceImpl_query_bind, ih, ih,
      evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]
    simp

theorem trace_query_bind (f : QueryImpl spec Id) (g : spec.Domain → List ρ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    trace f g ((liftM (spec.query t) : OracleComp spec _) >>= k) = g t ++ trace f g (k (f t)) := by
  rw [trace, run_simulateQ_traceImpl_query_bind, run_simulateQ_traceImpl]
  rfl

/-- A log is the concatenation of the logs of the queries. -/
theorem trace_eq_flatMap (f : QueryImpl spec Id) (g : spec.Domain → List ρ)
    (x : OracleComp spec α) : trace f g x = (queries f x).flatMap g := by
  induction x using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih => rw [queries, trace_query_bind, trace_query_bind, ih, queries]; simp

theorem trace_bind (f : QueryImpl spec Id) (g : spec.Domain → List ρ) {β : Type}
    (x : OracleComp spec α) (k : α → OracleComp spec β) :
    trace f g (x >>= k) = trace f g x ++ trace f g (k (evalWithAnswerFn f x)) := by
  rw [trace, simulateQ_bind, StateT.run_bind, run_simulateQ_traceImpl]
  change ((simulateQ (traceImpl f g) (k (evalWithAnswerFn f x))).run ([] ++ trace f g x)).2 = _
  rw [run_simulateQ_traceImpl, List.nil_append]

theorem queries_hasQuery (f : QueryImpl spec Id) (t : spec.Domain) :
    queries f (HasQuery.query (spec := spec) (m := OracleComp spec) t) = [t] := by
  have h := trace_query_bind f (fun t ↦ [t]) t pure
  rw [bind_pure] at h
  rw [HasQuery.instOfMonadLift_query]
  exact h

/-- Every query `x` makes when answered by `f` satisfies `P`. -/
def QueriesSatisfy (f : QueryImpl spec Id) (P : spec.Domain → Prop) (x : OracleComp spec α) :
    Prop :=
  ∀ q ∈ queries f x, P q

variable {f : QueryImpl spec Id} {P : spec.Domain → Prop}

theorem queriesSatisfy_pure (a : α) : QueriesSatisfy f P (pure a : OracleComp spec α) := by
  intro q hq
  rw [queries, trace_pure] at hq
  exact absurd hq List.not_mem_nil

theorem queriesSatisfy_bind {β : Type} {x : OracleComp spec α} {k : α → OracleComp spec β}
    (hx : QueriesSatisfy f P x) (hk : QueriesSatisfy f P (k (evalWithAnswerFn f x))) :
    QueriesSatisfy f P (x >>= k) := by
  intro q hq
  rw [queries, trace_bind, List.mem_append] at hq
  exact hq.elim (hx q) (hk q)

theorem queriesSatisfy_query {t : spec.Domain} (h : P t) :
    QueriesSatisfy f P (HasQuery.query (spec := spec) (m := OracleComp spec) t) := by
  intro q hq
  rw [queries_hasQuery, List.mem_singleton] at hq
  exact hq ▸ h

theorem queriesSatisfy_map {β : Type} {x : OracleComp spec α} (g : α → β)
    (hx : QueriesSatisfy f P x) : QueriesSatisfy f P (g <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact queriesSatisfy_bind hx (queriesSatisfy_pure _)

theorem queriesSatisfy_sequenceFin {β : Type} :
    ∀ {n : ℕ} {c : Fin n → OracleComp spec β}, (∀ i, QueriesSatisfy f P (c i)) →
      QueriesSatisfy f P (sequenceFin c)
  | 0, _, _ => queriesSatisfy_pure _
  | n + 1, c, h => by
    simp only [sequenceFin]
    exact queriesSatisfy_bind (h 0)
      (queriesSatisfy_bind (queriesSatisfy_sequenceFin fun i ↦ h i.succ) (queriesSatisfy_pure _))

end Answers

/-! ## The honest hash as sponge reads -/

section Reads

variable (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))

/-- The hash output of the sponge `φ` on an input: `out256` of the sponge hash of its blocks. -/
def spongeOut (φ : Equiv.Perm (X × Z)) (input : HashInput) : HashOutput :=
  out256 (spongeHash φ (blocks input))

/-- The permutation of the Keccak state that `keccakStateEquiv` transports to `φ`. -/
def statePerm (φ : Equiv.Perm (X × Z)) : Equiv.Perm KeccakState :=
  keccakStateEquiv.symm.permCongr φ

theorem spongeView_statePerm (φ : Equiv.Perm (X × Z)) : spongeView (statePerm φ) = φ := by
  ext s : 1
  simp [spongeView, statePerm, Equiv.permCongr_apply]

/-- The statement's `keccakHash` over `statePerm φ` is `spongeOut φ`. -/
theorem keccakHash_statePerm (φ : Equiv.Perm (X × Z)) (input : HashInput) :
    Id.run (keccakHash (fun s ↦ (pure (statePerm φ s) : Id KeccakState)) input) =
      spongeOut φ input := by
  rw [keccakHash_eq_spongeHash, spongeView_statePerm]
  rfl

/-- **The honest hash through reads**: hash an input by evaluating the sponge on its blocks through
logged reads of `h`, `k`, `k'` (three per block, `spongeEvalM`). -/
def readHash : QueryImpl LeanXmss.HashSpec (StateM (List (SpongeRead X Z))) :=
  fun input ↦ out256 <$> spongeEvalM π (readH t.1) (readK t.2.1) (readK' t.2.2) (blocks input)

/-- The reads of hashing `input`. -/
def inputReads (input : HashInput) : List (SpongeRead X Z) :=
  spongeReads π t.1 t.2.1 t.2.2 (blocks input)

theorem snd_foldl_logStep (msg : List X) (s : X × Z) (l : List (SpongeRead X Z)) :
    (msg.foldl (logStep π t.1 t.2.1 t.2.2) (s, l)).2 =
      l ++ (msg.foldl (logStep π t.1 t.2.1 t.2.2) (s, [])).2 := by
  induction msg generalizing s l with
  | nil => simp
  | cons b msg ih =>
    simp only [List.foldl_cons, logStep]
    rw [ih, ih (l := [] ++ _)]
    simp

theorem readHash_eq_traceImpl :
    readHash t π = traceImpl (spongeOut (spongePerm t π)) (inputReads t π) := by
  funext input
  refine StateT.ext fun l ↦ ?_
  rw [readHash, StateT.run_map, spongeEvalM, StateT.run_map, run_foldlM_log]
  refine Prod.ext ?_ ?_
  · change out256 (List.foldl (logStep π t.1 t.2.1 t.2.2) ((0, 0), l) (blocks input)).1.1 = _
    rw [fst_foldl_logStep]
    rfl
  · change (List.foldl (logStep π t.1 t.2.1 t.2.2) ((0, 0), l) (blocks input)).2 = l ++ _
    rw [snd_foldl_logStep]
    rfl

/-- **The honest evaluation**: a hash-query computation with every hash evaluated through logged
reads of `t`; its result and its reads. -/
def honestEval {α : Type} (x : OracleComp LeanXmss.HashSpec α) : α × List (SpongeRead X Z) :=
  (simulateQ (readHash t π) x).run []

/-- The honest evaluation returns the evaluation with the honest hash. -/
theorem fst_honestEval {α : Type} (x : OracleComp LeanXmss.HashSpec α) :
    (honestEval t π x).1 = evalWithAnswerFn (spongeOut (spongePerm t π)) x := by
  rw [honestEval, readHash_eq_traceImpl, run_simulateQ_traceImpl]

/-- **The honest reads are the sponge reads of the queried inputs**, in order. -/
theorem snd_honestEval {α : Type} (x : OracleComp LeanXmss.HashSpec α) :
    (honestEval t π x).2 =
      (queries (spongeOut (spongePerm t π)) x).flatMap (inputReads t π) := by
  rw [honestEval, readHash_eq_traceImpl, run_simulateQ_traceImpl, List.nil_append,
    trace_eq_flatMap]

/-- Every honest read is answered by `t`. -/
def _root_.Quantum.Sponge.SpongeRead.AnsweredBy (t : SpongeKeys X Z) : SpongeRead X Z → Prop
  | .h z a => t.1 z = a
  | .k x a => t.2.1 x = a
  | .k' x a => t.2.2 x = a

variable {t} in
/-- Keys agreeing with `t` on the reads of a message have the same reads and the same state. -/
theorem spongeReads_congr {t' : SpongeKeys X Z} (msg : List X)
    (h : ∀ e ∈ spongeReads π t.1 t.2.1 t.2.2 msg, e.AnsweredBy t') :
    spongeReads π t'.1 t'.2.1 t'.2.2 msg = spongeReads π t.1 t.2.1 t.2.2 msg ∧
      absorb (spongePerm t' π) msg = absorb (spongePerm t π) msg := by
  obtain ⟨h1, k1, k1'⟩ := t
  obtain ⟨h2, k2, k2'⟩ := t'
  induction msg using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton msg b ih =>
    rw [spongeReads_append_singleton] at h
    obtain ⟨ih1, ih2⟩ := ih fun e he ↦ h e (List.mem_append_left _ he)
    have hr := fun e he ↦ h e (List.mem_append_right _ he)
    simp only [roundReads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, SpongeRead.AnsweredBy] at hr
    obtain ⟨hk, hk', hh⟩ := hr
    refine ⟨?_, ?_⟩
    · rw [spongeReads_append_singleton, spongeReads_append_singleton, ih1, ih2]
      simp only [roundReads, hk, hk', hh]
    · rw [absorb_append_singleton, absorb_append_singleton, ih2, absorbStep, absorbStep,
        spongePerm_apply, spongePerm_apply]
      simp only [hk, hk', hh]

variable {t} in
/-- **The honest evaluation depends on the keys only through what it reads**: keys answering every
read of the evaluation under `t` as `t` does give the same result and the same reads. -/
theorem honestEval_congr {t' : SpongeKeys X Z} {α : Type} (x : OracleComp LeanXmss.HashSpec α)
    (h : ∀ e ∈ (honestEval t π x).2, e.AnsweredBy t') :
    honestEval t' π x = honestEval t π x := by
  rw [honestEval, honestEval, readHash_eq_traceImpl, readHash_eq_traceImpl,
    run_simulateQ_traceImpl, run_simulateQ_traceImpl]
  rw [honestEval, readHash_eq_traceImpl, run_simulateQ_traceImpl] at h
  simp only [List.nil_append] at h ⊢
  induction x using OracleComp.inductionOn with
  | pure a => rw [evalWithAnswerFn_pure, evalWithAnswerFn_pure, trace_pure, trace_pure]
  | query_bind input k ih =>
    rw [trace_query_bind] at h
    obtain ⟨hr, hs⟩ := spongeReads_congr π (blocks input)
      fun e he ↦ h e (List.mem_append_left _ he)
    have ho : spongeOut (spongePerm t' π) input = spongeOut (spongePerm t π) input := by
      rw [spongeOut, spongeOut, spongeHash, spongeHash, hs]
    obtain ⟨ih1, ih2⟩ := Prod.mk.inj (ih (spongeOut (spongePerm t π) input)
      fun e he ↦ h e (List.mem_append_right _ he))
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_liftM_query, trace_query_bind, trace_query_bind, ho, ih1, ih2]
    simp only [inputReads, hr]

end Reads

/-! ## The statement's scheme returns the honest evaluation -/

section Scheme

variable (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) {r : Type → Type} [Monad r] [LawfulMonad r]
  (impl : QueryImpl RandomPermutationOracles r)

local notation "σ" => schemeHashOverPermutation

theorem schemeHashOverPermutation_apply (input : HashInput) :
    σ input = keccakHash queryPermutation input := by
  rw [← Verification.simulateQ_oracleHashWithHash, Verification.oracleHashWithHash,
    simulateQ_HasQuery_query]

/-- **A hash-query computation over `π`, the honest evaluation**: answered by a simulation whose
forward calls are `statePerm (spongePerm t π)`, a hash-query computation over the statement's
permutation (`schemeHashOverPermutation`) returns what `honestEval` returns. -/
theorem simulateQ_schemeHash
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm (spongePerm t π) s)) {α : Type}
    (x : OracleComp LeanXmss.HashSpec α) :
    simulateQ impl (simulateQ σ x) = pure (honestEval t π x).1 := by
  rw [← QueryImpl.simulateQ_compose, fst_honestEval]
  refine simulateQ_eq_pure_evalWithAnswerFn _ _ (fun input ↦ ?_) x
  rw [QueryImpl.apply_compose, schemeHashOverPermutation_apply,
    simulateQ_keccakHash impl _ himpl, spongeView_statePerm]
  rfl

/-- **`honest_eq_scheme`, key generation**: the statement's key generation from `S_0` over
`statePerm (spongePerm t π)` returns the honest evaluation's keys. -/
theorem simulateQ_generateKeys
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm (spongePerm t π) s))
    (S0 : MasterSeed) :
    simulateQ impl (sufCmaScheme.generateKeys S0) =
      pure (honestEval t π (schemeWithHashFromSeed.keygen S0)).1 := by
  rw [scheme_eq]
  exact simulateQ_schemeHash t π impl himpl _

/-- **`honest_eq_scheme`, signing**: the statement's signer of request `req` over
`statePerm (spongePerm t π)` returns the honest evaluation's signature. -/
theorem simulateQ_sign
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm (spongePerm t π) s))
    (sk : SecretKey) (req : SigningRequest) :
    simulateQ impl (sufCmaScheme.sign sk req) =
      pure (honestEval t π (schemeWithHashFromSeed.sign sk req)).1 := by
  rw [scheme_eq]
  exact simulateQ_schemeHash t π impl himpl _

/-- The statement's verifier over `statePerm (spongePerm t π)` returns the honest evaluation's
verdict. -/
theorem simulateQ_verify
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm (spongePerm t π) s))
    (pk : PublicKey) (forgery : Forgery) :
    simulateQ impl (sufCmaScheme.verify pk forgery) =
      pure (honestEval t π (schemeWithHashFromSeed.verify pk forgery)).1 := by
  rw [scheme_eq]
  exact simulateQ_schemeHash t π impl himpl _

end Scheme

/-! ## The honest table -/

theorem evalWithAnswerFn_sequenceFin {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (f : QueryImpl spec Id) {β : Type} :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec β),
      evalWithAnswerFn f (sequenceFin c) = fun i ↦ evalWithAnswerFn f (c i)
  | 0, _ => funext fun i ↦ i.elim0
  | n + 1, c => by
    simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      evalWithAnswerFn_sequenceFin]
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- The bits of a key index of layer `l`: `32` on the bottom layer, `16` on the top. -/
def keyBits (l : Layer) : ℕ :=
  layerHeight * (layerCount - l.val)

/-- The keys of layer `l`: `2^32` on the bottom layer, `2^16` on the top. -/
def keyCount (l : Layer) : ℕ :=
  2 ^ keyBits l

theorem keyBits_le (l : Layer) : keyBits l ≤ 32 := by
  fin_cases l <;> simp [keyBits, layerHeight, layerCount]

theorem le_keyBits (l : Layer) : 16 ≤ keyBits l := by
  fin_cases l <;> simp [keyBits, layerHeight, layerCount]

theorem keyCount_le (l : Layer) : keyCount l ≤ 2 ^ 32 :=
  Nat.pow_le_pow_right (by norm_num) (keyBits_le l)

theorem keyIndexOnLayer_lt (index : LeafIndex) (l : Layer) :
    (keyIndexOnLayer index l).val < keyCount l := by
  have h : index.val < 2 ^ 32 := index.isLt
  fin_cases l <;> simp [keyIndexOnLayer, keyCount, keyBits, layerHeight, layerCount] <;> omega

/-- The key of a leaf index, as `treeNode` takes it. -/
def leafKey (index : ℕ) : KeyIndex :=
  ⟨index % lifetime, Nat.mod_lt _ (by decide)⟩

theorem leafKey_val (e : KeyIndex) : leafKey e.val = e :=
  Fin.ext (Nat.mod_eq_of_lt e.isLt)

/-- **The honest table**: the keys `h, k, k'` and the inner permutation `π` of the sponge view, and
the master seed `S_0`. Every value of leanXMSS's honest computations is a function of these. -/
structure HonestTable where
  /-- The keys `t = (h, k, k')`. -/
  keys : SpongeKeys X Z
  /-- The inner permutation `π`. -/
  perm : Equiv.Perm (X × Z)
  /-- The master seed `S_0`. -/
  masterSeed : MasterSeed

namespace HonestTable

variable (L : HonestTable)

/-- The sponge view `φ = spongePerm t π`. -/
def view : Equiv.Perm (X × Z) :=
  spongePerm L.keys L.perm

/-- The honest hash `H`. -/
def hash : QueryImpl LeanXmss.HashSpec Id :=
  spongeOut L.view

/-- `Truncate_16` of the honest hash. -/
def digest (input : HashInput) : Digest :=
  truncateHash (L.hash input)

/-- The scheme seed `S = H("leanXMSS" ‖ S_0)`. -/
def seed : MasterSeed :=
  L.hash (seedTag ++ littleEndianBytes 32 L.masterSeed)

/-- The public parameter `P`. -/
def param : PublicParameter :=
  L.digest (thInput 0 (keygenDomainFields .parameter) (littleEndianBytes 32 L.seed))

/-- The start of chain `i` of key `e` of layer `l`: a half of a seed derivation. -/
def chainStart (l : Layer) (e : KeyIndex) (i : ChainIndex) : Digest :=
  hashHalfForChain i.val (L.hash (thInput L.param
    (keygenDomainFields (.oneTimeChainPair l e (chainPair i))) (littleEndianBytes 32 L.seed)))

/-- Position `j` of chain `i` of key `e` of layer `l` (`0` past the end, as `walkChain`). -/
def chainValue (l : Layer) (e : KeyIndex) (i : ChainIndex) : ℕ → Digest
  | 0 => L.chainStart l e i
  | j + 1 => if h : j < chainLength - 1 then
      L.digest (thInput L.param (hashDomainFields (.chain l e ⟨j, h⟩))
        (Verification.chainPayload i (chainValue l e i j)))
    else 0

/-- The chain ends of key `e` of layer `l`. -/
def endpoints (l : Layer) (e : KeyIndex) (i : ChainIndex) : Digest :=
  L.chainValue l e i (chainLength - 1)

/-- The tree value of layer `l` at `level`, index `index`: the leaf of key `leafKey index` at level
`0`, else the node. -/
def treeValue (l : Layer) : ℕ → ℕ → Digest
  | 0, index => L.digest (thInput L.param (hashDomainFields (.leaf l (leafKey index)))
      (digestsPayload (L.endpoints l (leafKey index))))
  | level + 1, index => L.digest (thInput L.param (hashDomainFields (.node l (level + 1) index))
      (nodePayload (treeValue l level (2 * index)) (treeValue l level (2 * index + 1))))

/-- The public key: the top root and `P`. -/
def publicKey : PublicKey :=
  ⟨L.treeValue topLayer layerHeight 0, L.param⟩

/-- The secret key: `S_0` and `P`. -/
def secretKey : SecretKey :=
  ⟨L.masterSeed, L.param⟩

/-- The randomizer base `R0` of key `e` of layer `l` for `message`. -/
def randomizerBase (l : Layer) (e : KeyIndex) (message : HashInput) : Randomizer :=
  L.digest (thInput L.param (tweakFields 7 0 (layerHi l 0) e)
    (littleEndianBytes 32 L.seed ++ message))

/-- The message digest of key `e` of layer `l` for `message` and a randomizer. -/
def messageDigest (l : Layer) (e : KeyIndex) (message : HashInput) (randomizer : Randomizer) :
    Digest :=
  L.digest (thInput L.param (hashDomainFields (.message l e))
    (message ++ littleEndianBytes 16 randomizer))

/-- The randomizer trials from `trial`, `attempts` of them: the first codeword's randomizer and
word. -/
def selectFrom (l : Layer) (e : KeyIndex) (message : HashInput) (base : Randomizer) :
    ℕ → ℕ → Option (Randomizer × Encoding)
  | 0, _ => none
  | attempts + 1, trial =>
    match Codeword.decode (L.messageDigest l e message (base + BitVec.ofNat digestBits trial)) with
    | some x => some (base + BitVec.ofNat digestBits trial, x)
    | none => selectFrom l e message base attempts (trial + 1)

/-- **The selection** of key `e` of layer `l` for `message`: the first of the `2^32` trials from
`R0` whose digest is a codeword, its randomizer and word. -/
def select (l : Layer) (e : KeyIndex) (message : HashInput) : Option (Randomizer × Encoding) :=
  L.selectFrom l e message (L.randomizerBase l e message) randomizerAttemptLimit 0

/-- The authentication path of key `e` of layer `l`. -/
def authPath (l : Layer) (e : KeyIndex) (level : Fin layerHeight) : Digest :=
  L.treeValue l level.val (Nat.xor (e.val / 2 ^ level.val) 1)

/-- The signature of key `e` of layer `l` on `message`: the selection, the chains opened to its
word, and the path. -/
def layerSignature (l : Layer) (e : KeyIndex) (message : HashInput) : Option LayerSignature :=
  (L.select l e message).map fun sel ↦
    ⟨sel.1, fun i ↦ L.chainValue l e i (sel.2 i).val, L.authPath l e⟩

/-- The root of the bottom tree of a leaf index. -/
def bottomRoot (index : LeafIndex) : Digest :=
  L.treeValue bottomLayer layerHeight (keyIndexOnLayer index topLayer).val

/-- **The honest signature** of a request. -/
def signature (req : SigningRequest) : Option Signature :=
  (L.layerSignature bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (littleEndianBytes 32 req.message)).bind fun bottom ↦
    (L.layerSignature topLayer (keyIndexOnLayer req.leafIndex topLayer)
        (littleEndianBytes 16 (L.bottomRoot req.leafIndex))).map fun top ↦
      ⟨req.leafIndex, fun lay ↦ if lay = bottomLayer then bottom else top⟩

theorem trunc128_spongeHash (input : HashInput) :
    trunc128 (spongeHash L.view (blocks input)) = L.digest input :=
  rfl

theorem chainValue_succ (l : Layer) (e : KeyIndex) (i : ChainIndex) (step : ChainStep) :
    L.chainValue l e i (step.val + 1) = L.digest (thInput L.param (hashDomainFields (.chain l e step))
      (Verification.chainPayload i (L.chainValue l e i step.val))) := by
  rw [chainValue, dite_eq_left step.isLt]

theorem treeValue_succ (l : Layer) (level index : ℕ) :
    L.treeValue l (level + 1) index = L.digest (thInput L.param
      (hashDomainFields (.node l (level + 1) index))
      (nodePayload (L.treeValue l level (2 * index)) (L.treeValue l level (2 * index + 1)))) := by
  rw [treeValue]

/-! ### The honest computations return the table's values -/

open Verification KeyGenerationAndSigning

local notation "Comp" => OracleComp LeanXmss.HashSpec

theorem eval_oracleHash (input : HashInput) :
    evalWithAnswerFn L.hash (oracleHashWithHash (m := Comp) input) = L.hash input :=
  simulateQ_HasQuery_query (r := Id) L.hash input

theorem eval_th (Q : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    evalWithAnswerFn L.hash (thWithHash (m := Comp) Q fields payload) =
      L.digest (thInput Q fields payload) := by
  simp only [thWithHash, evalWithAnswerFn_bind, eval_oracleHash, evalWithAnswerFn_pure]
  rfl

theorem eval_schemeSeed :
    evalWithAnswerFn L.hash (taggedSeedWithHash (m := Comp) seedTag L.masterSeed) = L.seed :=
  L.eval_oracleHash _

theorem eval_param :
    evalWithAnswerFn L.hash (thWithHash (m := Comp) 0 (keygenDomainFields .parameter)
      (littleEndianBytes 32 L.seed)) = L.param :=
  L.eval_th _ _ _

theorem eval_chainWalk (l : Layer) (e : KeyIndex) (i : ChainIndex) :
    ∀ j, evalWithAnswerFn L.hash
      (chainWalkWithHash (m := Comp) L.param l e i 0 j (L.chainStart l e i)) = L.chainValue l e i j
  | 0 => rfl
  | j + 1 => by
    have ih := eval_chainWalk l e i j
    rw [chainWalkWithHash] at ih ⊢
    rw [walkChain, evalWithAnswerFn_bind, ih, chainValue]
    by_cases h : j < chainLength - 1
    · rw [dite_eq_left (by omega), dite_eq_left h, eval_th]
      simp only [Nat.zero_add]
    · rw [dite_eq_right (by omega), dite_eq_right h]
      rfl

theorem eval_otsSecrets (l : Layer) (e : KeyIndex) :
    evalWithAnswerFn L.hash (otsSecretsWithHash (m := Comp) L.param l e L.seed) =
      L.chainStart l e := by
  simp only [otsSecretsWithHash, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    thPairWithHash, eval_oracleHash, evalWithAnswerFn_pure]
  rfl

theorem eval_oneTimePublicKey (l : Layer) (e : KeyIndex) :
    evalWithAnswerFn L.hash (oneTimePublicKeyWithHash (m := Comp) L.param l e L.seed) =
      L.endpoints l e := by
  simp only [oneTimePublicKeyWithHash, evalWithAnswerFn_bind, eval_otsSecrets,
    evalWithAnswerFn_sequenceFin, eval_chainWalk]
  rfl

theorem eval_treeNode (l : Layer) : ∀ level index,
    evalWithAnswerFn L.hash (treeNodeWithHash (m := Comp) L.param l L.seed level index) =
      L.treeValue l level index
  | 0, index => by
    simp only [treeNodeWithHash, buildTree, evalWithAnswerFn_bind, eval_oneTimePublicKey,
      leafHashWithHash, tweakableHashWithHash, eval_th]
    rfl
  | level + 1, index => by
    have h1 := eval_treeNode l level (2 * index)
    have h2 := eval_treeNode l level (2 * index + 1)
    simp only [treeNodeWithHash] at h1 h2 ⊢
    simp only [buildTree, evalWithAnswerFn_bind, h1, h2, tweakableHashWithHash, eval_th]
    rfl

theorem eval_treePath (l : Layer) (e : KeyIndex) :
    evalWithAnswerFn L.hash (treePathWithHash (m := Comp) L.param l L.seed e) = L.authPath l e := by
  simp only [treePathWithHash, evalWithAnswerFn_sequenceFin, eval_treeNode]
  rfl

/-- **Key generation returns the table's keys.** -/
theorem eval_keygen :
    evalWithAnswerFn L.hash (schemeWithHashFromSeed.keygen L.masterSeed) =
      (L.publicKey, L.secretKey) := by
  simp only [schemeWithHashFromSeed, KeptKey.scheme, keptKey, deriveSchemeSeedKey, keygenRest,
    evalWithAnswerFn_bind, evalWithAnswerFn_map, evalWithAnswerFn_pure, eval_schemeSeed,
    eval_param, eval_treeNode]
  rfl

theorem eval_otsSignFrom (l : Layer) (e : KeyIndex) (message : HashInput) (base : Randomizer) :
    ∀ attempts trial, evalWithAnswerFn L.hash
      (otsSignFromWithHash (m := Comp) L.param l e L.seed message base attempts trial) =
      (L.selectFrom l e message base attempts trial).map fun sel ↦
        (sel.1, fun i ↦ L.chainValue l e i (sel.2 i).val)
  | 0, _ => rfl
  | attempts + 1, trial => by
    rw [otsSignFromWithHash, evalWithAnswerFn_bind, messageDigestWithHash, tweakableHashWithHash,
      eval_th, selectFrom]
    cases hd : Codeword.decode (L.messageDigest l e message (base + BitVec.ofNat digestBits trial))
      with
    | none =>
      simp only [messageDigest] at hd
      simp only [hd]
      exact eval_otsSignFrom l e message base attempts (trial + 1)
    | some x =>
      simp only [messageDigest] at hd
      simp only [hd, evalWithAnswerFn_bind, eval_otsSecrets, evalWithAnswerFn_sequenceFin,
        eval_chainWalk, evalWithAnswerFn_pure, Option.map_some]

theorem eval_signLayer (l : Layer) (e : KeyIndex) (message : HashInput) :
    evalWithAnswerFn L.hash
      (signLayerWithHash (m := Comp) ⟨L.seed, L.param⟩ l e message) =
      L.layerSignature l e message := by
  simp only [signLayerWithHash, otsSignWithHash, evalWithAnswerFn_bind, eval_th]
  rw [show L.digest _ = L.randomizerBase l e message from rfl, eval_otsSignFrom]
  rw [layerSignature, select]
  cases L.selectFrom l e message (L.randomizerBase l e message) randomizerAttemptLimit 0 with
  | none => rfl
  | some sel =>
    simp only [Option.map_some, evalWithAnswerFn_bind, eval_treePath, evalWithAnswerFn_pure]

/-- **Signing returns the table's signature.** -/
theorem eval_sign (req : SigningRequest) :
    evalWithAnswerFn L.hash (schemeWithHashFromSeed.sign L.secretKey req) = L.signature req := by
  simp only [schemeWithHashFromSeed, KeptKey.scheme, keptKey, rederiveSchemeSeedKey,
    schemeWithHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_oracleHash,
    taggedSeedWithHash]
  change evalWithAnswerFn L.hash (signWithHash (m := Comp) ⟨L.seed, L.param⟩ req.leafIndex
    req.message) = _
  simp only [signWithHash, evalWithAnswerFn_bind, eval_signLayer, signature]
  cases L.layerSignature bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (littleEndianBytes 32 req.message) with
  | none => rfl
  | some bottom =>
    simp only [Option.bind_some, evalWithAnswerFn_bind, eval_treeNode, eval_signLayer]
    rw [show L.treeValue bottomLayer layerHeight (keyIndexOnLayer req.leafIndex topLayer).val =
      L.bottomRoot req.leafIndex from rfl]
    cases L.layerSignature topLayer (keyIndexOnLayer req.leafIndex topLayer)
        (littleEndianBytes 16 (L.bottomRoot req.leafIndex)) with
    | none => rfl
    | some top => rfl

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl RandomPermutationOracles r)

/-- **`honest_eq_scheme`, key generation**: the statement's key generation from `S_0` over
`statePerm φ` returns the table's keys. -/
theorem simulateQ_generateKeys_eq
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm L.view s)) :
    simulateQ impl (sufCmaScheme.generateKeys L.masterSeed) = pure (L.publicKey, L.secretKey) := by
  rw [simulateQ_generateKeys L.keys L.perm impl himpl, fst_honestEval]
  exact congrArg pure L.eval_keygen

/-- **`honest_eq_scheme`, signing**: the statement's signer with the table's secret key over
`statePerm φ` returns the table's signature. -/
theorem simulateQ_sign_eq
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm L.view s)) (req : SigningRequest) :
    simulateQ impl (sufCmaScheme.sign L.secretKey req) = pure (L.signature req) := by
  rw [simulateQ_sign L.keys L.perm impl himpl, fst_honestEval]
  exact congrArg pure (L.eval_sign req)

/-- The reads of the honest key generation. -/
noncomputable def keygenReads : List (SpongeRead X Z) :=
  (honestEval L.keys L.perm (schemeWithHashFromSeed.keygen L.masterSeed)).2

/-- The reads of the honest signer of a request. -/
noncomputable def signReads (req : SigningRequest) : List (SpongeRead X Z) :=
  (honestEval L.keys L.perm (schemeWithHashFromSeed.sign L.secretKey req)).2

/-- **The honest reads of a game**: key generation's, then the signer's for each request, a
function of the keys, `π`, `S_0` and the requests. -/
noncomputable def honestReads (reqs : List SigningRequest) : List (SpongeRead X Z) :=
  L.keygenReads ++ reqs.flatMap L.signReads

theorem fst_honestEval_keygen :
    (honestEval L.keys L.perm (schemeWithHashFromSeed.keygen L.masterSeed)).1 =
      (L.publicKey, L.secretKey) :=
  (fst_honestEval _ _ _).trans L.eval_keygen

theorem fst_honestEval_sign (req : SigningRequest) :
    (honestEval L.keys L.perm (schemeWithHashFromSeed.sign L.secretKey req)).1 = L.signature req :=
  (fst_honestEval _ _ _).trans (L.eval_sign req)

end HonestTable

/-! ## Structural slots and their honest inputs -/

/-- **The structural slots of the keygen table**: the chains and leaves of the layer's keys, and
the nodes at levels `1` to `16` of the layer's trees. -/
def InTable : Slot → Prop
  | .chain l e _ _ => e.val < keyCount l
  | .leaf l e => e.val < keyCount l
  | .node l level index => 1 ≤ level ∧ level ≤ layerHeight ∧ index < 2 ^ (keyBits l - level)
  | _ => False

instance : DecidablePred InTable := fun s ↦ by
  cases s <;> unfold InTable <;> infer_instance

/-- The address of a structural slot's hash call. -/
def slotFields : Slot → TweakFields
  | .chain l e step _ => hashDomainFields (.chain l e step)
  | .leaf l e => hashDomainFields (.leaf l e)
  | .node l level index => hashDomainFields (.node l level index)
  | _ => tweakFields 0 0 0 0

namespace HonestTable

variable (L : HonestTable)

/-- The honest payload of a structural slot. -/
def payload : Slot → HashInput
  | .chain l e step i => Verification.chainPayload i (L.chainValue l e i step.val)
  | .leaf l e => digestsPayload (L.endpoints l e)
  | .node l level index =>
      nodePayload (L.treeValue l (level - 1) (2 * index)) (L.treeValue l (level - 1) (2 * index + 1))
  | _ => []

/-- **The honest input of a slot**: for a structural slot of the table, the tweakable-hash input
under `P` at its address with its honest payload. -/
def honestInput (s : Slot) : Option HashInput :=
  if InTable s then some (thInput L.param (slotFields s) (L.payload s)) else none

/-- The Msponge tail of a slot's honest input. -/
def honestTail (s : Slot) : Option (List X) :=
  (L.honestInput s).map fun input ↦ absorbTail L.view (blocks input)

/-- **The target of a slot**: the digest of its honest input. -/
def target (s : Slot) : Option Digest :=
  (L.honestInput s).map fun input ↦ trunc128 (spongeHash L.view (blocks input))

/-- **The honest tail lies in its slot.** -/
theorem slotOf_honestTail {s : Slot} {tail : List X} (h : L.honestTail s = some tail) :
    slotOf L.param tail = some s := by
  simp only [honestTail, honestInput] at h
  split_ifs at h with hs
  swap
  · simp at h
  rw [Option.map_some, Option.some.injEq] at h
  subst h
  cases s with
  | chain l e step i => exact slotOf_chain _ _ l e step i _
  | leaf l e => exact slotOf_leaf _ _ l e _
  | node l level index =>
    obtain ⟨-, h2, h3⟩ := hs
    have hk : 2 ^ (keyBits l - level) ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by have := keyBits_le l; omega)
    exact slotOf_node _ _ l level index (by simp only [layerHeight] at h2; omega)
      (lt_of_lt_of_le h3 hk) _ _
  | msg => exact hs.elim
  | prf => exact hs.elim
  | rnd => exact hs.elim
  | param => exact hs.elim
  | seed => exact hs.elim

/-- Distinct slots have distinct honest tails. -/
theorem honestTail_injective {s s' : Slot} {tail : List X} (h : L.honestTail s = some tail)
    (h' : L.honestTail s' = some tail) : s = s' :=
  Option.some.inj ((L.slotOf_honestTail h).symm.trans (L.slotOf_honestTail h'))

/-- **One honest input per slot**: a tweakable-hash input under `P` has the honest tail of a slot
exactly when the slot is in the table and the input's address and payload are the honest ones. -/
theorem honestTail_eq_some_iff {s : Slot} {fields : TweakFields} {p : HashInput} :
    L.honestTail s = some (absorbTail L.view (blocks (thInput L.param fields p))) ↔
      InTable s ∧ fields = slotFields s ∧ p = L.payload s := by
  simp only [honestTail, honestInput]
  split_ifs with hs
  · rw [Option.map_some, Option.some.injEq]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := absorbTail_blocks_thInput_injective L.view L.param h
      exact ⟨hs, h1.symm, h2.symm⟩
    · rintro ⟨-, rfl, rfl⟩
      rfl
  · simp [hs]

end HonestTable

/-- The structural slots: chain steps, leaves and nodes. -/
def Structural : Slot → Prop
  | .chain .. | .leaf .. | .node .. => True
  | _ => False

namespace HonestTable

variable (L : HonestTable)

/-! ### Every honest hash call at a structural slot is its honest input -/

/-- A hash input agrees with the table: if its tail lies in a chain, leaf or node slot, it is that
slot's honest input. -/
def HonestQuery (input : HashInput) : Prop :=
  ∀ s, slotOf L.param (absorbTail L.view (blocks input)) = some s → Structural s →
    L.honestInput s = some input

/-- Every hash call of a computation agrees with the table. -/
def HonestQueries {α : Type} (x : OracleComp LeanXmss.HashSpec α) : Prop :=
  QueriesSatisfy L.hash L.HonestQuery x

/-- An honest query's tail at a structural slot is the slot's honest tail. -/
theorem honestTail_of_honestQuery {input : HashInput} (h : L.HonestQuery input) {s : Slot}
    (hs : slotOf L.param (absorbTail L.view (blocks input)) = some s) (hst : Structural s) :
    L.honestTail s = some (absorbTail L.view (blocks input)) := by
  rw [honestTail, h s hs hst, Option.map_some]

variable {L}

theorem honestQuery_of_slotOf {input : HashInput} {s : Slot}
    (h : slotOf L.param (absorbTail L.view (blocks input)) = some s) (hs : ¬Structural s) :
    L.HonestQuery input := fun _ h' hs' ↦ by
  obtain rfl := Option.some.inj (h.symm.trans h')
  exact absurd hs' hs

theorem honestQuery_of_honestInput {input : HashInput} {s : Slot}
    (h : L.honestInput s = some input) : L.HonestQuery input := fun _ h' _ ↦ by
  have hs := L.slotOf_honestTail (s := s) (tail := absorbTail L.view (blocks input))
    (by rw [honestTail, h, Option.map_some])
  obtain rfl := Option.some.inj (hs.symm.trans h')
  exact h

theorem honestInput_chain {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) (step : ChainStep)
    (i : ChainIndex) :
    L.honestInput (.chain l e step i) = some (thInput L.param (hashDomainFields (.chain l e step))
      (Verification.chainPayload i (L.chainValue l e i step.val))) := by
  rw [honestInput, ite_eq_left (show InTable (.chain l e step i) from he)]
  rfl

theorem honestInput_leaf {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) :
    L.honestInput (.leaf l e) =
      some (thInput L.param (hashDomainFields (.leaf l e)) (digestsPayload (L.endpoints l e))) := by
  rw [honestInput, ite_eq_left (show InTable (.leaf l e) from he)]
  rfl

theorem honestInput_node {l : Layer} {level index : ℕ} (hl : level + 1 ≤ layerHeight)
    (hi : index < 2 ^ (keyBits l - (level + 1))) :
    L.honestInput (.node l (level + 1) index) =
      some (thInput L.param (hashDomainFields (.node l (level + 1) index))
        (nodePayload (L.treeValue l level (2 * index)) (L.treeValue l level (2 * index + 1)))) := by
  rw [honestInput, ite_eq_left (show InTable (.node l (level + 1) index) from ⟨by omega, hl, hi⟩)]
  rfl

variable (L)

open Verification KeyGenerationAndSigning

local notation "Comp" => OracleComp LeanXmss.HashSpec

theorem honestQueries_th {Q : PublicParameter} {fields : TweakFields} {payload : HashInput}
    (h : L.HonestQuery (thInput Q fields payload)) :
    L.HonestQueries (thWithHash (m := Comp) Q fields payload) :=
  queriesSatisfy_bind (queriesSatisfy_query h) (queriesSatisfy_pure _)

theorem honestQueries_chainWalk {l : Layer} {e : KeyIndex} (he : e.val < keyCount l)
    (i : ChainIndex) :
    ∀ j, L.HonestQueries (chainWalkWithHash (m := Comp) L.param l e i 0 j (L.chainStart l e i))
  | 0 => queriesSatisfy_pure _
  | j + 1 => by
    have ih := honestQueries_chainWalk he i j
    have hv := L.eval_chainWalk l e i j
    rw [chainWalkWithHash] at ih hv ⊢
    rw [walkChain]
    refine queriesSatisfy_bind ih ?_
    rw [hv]
    by_cases h : j < chainLength - 1
    · rw [dite_eq_left (show 0 + j < chainLength - 1 by omega)]
      simp only [Nat.zero_add]
      exact L.honestQueries_th (honestQuery_of_honestInput (L.honestInput_chain he ⟨j, h⟩ i))
    · rw [dite_eq_right (show ¬(0 + j < chainLength - 1) by omega)]
      exact queriesSatisfy_pure _

theorem honestQueries_otsSecrets (l : Layer) (e : KeyIndex) :
    L.HonestQueries (otsSecretsWithHash (m := Comp) L.param l e L.seed) :=
  queriesSatisfy_bind (queriesSatisfy_sequenceFin fun pair ↦ queriesSatisfy_query
    (honestQuery_of_slotOf (slotOf_prf L.view L.param l e pair L.seed) fun h ↦ h))
    (queriesSatisfy_pure _)

theorem honestQueries_oneTimePublicKey {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) :
    L.HonestQueries (oneTimePublicKeyWithHash (m := Comp) L.param l e L.seed) := by
  refine queriesSatisfy_bind (L.honestQueries_otsSecrets l e) ?_
  rw [L.eval_otsSecrets]
  exact queriesSatisfy_sequenceFin fun i ↦ L.honestQueries_chainWalk he i _

theorem honestQueries_treeNode (l : Layer) : ∀ level index, level ≤ layerHeight →
    index < 2 ^ (keyBits l - level) →
    L.HonestQueries (treeNodeWithHash (m := Comp) L.param l L.seed level index)
  | 0, index, _, hi => by
    have hk : (leafKey index).val = index :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le hi (keyCount_le l))
    have he : (leafKey index).val < keyCount l := by
      rw [hk]
      exact hi
    simp only [treeNodeWithHash, buildTree]
    refine queriesSatisfy_bind (L.honestQueries_oneTimePublicKey he) ?_
    rw [L.eval_oneTimePublicKey]
    exact L.honestQueries_th (honestQuery_of_honestInput (L.honestInput_leaf he))
  | level + 1, index, hl, hi => by
    have hK := le_keyBits l
    have hLH : layerHeight = 16 := rfl
    have h2 : 2 ^ (keyBits l - level) = 2 * 2 ^ (keyBits l - (level + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    have c1 := honestQueries_treeNode l level (2 * index) (by omega) (by omega)
    have c2 := honestQueries_treeNode l level (2 * index + 1) (by omega) (by omega)
    have v1 := L.eval_treeNode l level (2 * index)
    have v2 := L.eval_treeNode l level (2 * index + 1)
    simp only [treeNodeWithHash] at c1 c2 v1 v2 ⊢
    rw [buildTree]
    refine queriesSatisfy_bind c1 ?_
    rw [v1]
    refine queriesSatisfy_bind c2 ?_
    rw [v2]
    exact L.honestQueries_th (honestQuery_of_honestInput (L.honestInput_node hl hi))

theorem sibling_lt {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) (level : Fin layerHeight) :
    Nat.xor (e.val / 2 ^ level.val) 1 < 2 ^ (keyBits l - level.val) := by
  have hK := le_keyBits l
  have hlv : level.val < 16 := level.isLt
  have h1 : e.val / 2 ^ level.val < 2 ^ (keyBits l - level.val) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
    exact he
  exact Nat.xor_lt_two_pow h1 (Nat.one_lt_two_pow (by omega))

theorem honestQueries_treePath {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) :
    L.HonestQueries (treePathWithHash (m := Comp) L.param l L.seed e) :=
  queriesSatisfy_sequenceFin fun level ↦
    L.honestQueries_treeNode l _ _ level.isLt.le (sibling_lt he level)

/-- **Key generation's hash calls agree with the table.** -/
theorem honestQueries_keygen : L.HonestQueries (schemeWithHashFromSeed.keygen L.masterSeed) := by
  simp only [schemeWithHashFromSeed, KeptKey.scheme, keptKey, deriveSchemeSeedKey, keygenRest]
  refine queriesSatisfy_bind (queriesSatisfy_bind (queriesSatisfy_query
    (honestQuery_of_slotOf (slotOf_seed L.view L.param L.masterSeed) fun h ↦ h)) ?_) ?_
  · rw [L.eval_schemeSeed]
    exact queriesSatisfy_bind
      (L.honestQueries_th (honestQuery_of_slotOf (slotOf_param L.view L.param L.seed) fun h ↦ h))
      (queriesSatisfy_pure _)
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_schemeSeed, eval_param]
    exact queriesSatisfy_map _ (queriesSatisfy_bind
      (L.honestQueries_treeNode topLayer layerHeight 0 le_rfl (by positivity))
      (queriesSatisfy_pure _))

theorem honestQueries_otsSignFrom {l : Layer} {e : KeyIndex} (he : e.val < keyCount l)
    {message : HashInput} (hm : 16 ≤ message.length) (base : Randomizer) :
    ∀ attempts trial, L.HonestQueries
      (otsSignFromWithHash (m := Comp) L.param l e L.seed message base attempts trial)
  | 0, _ => queriesSatisfy_pure _
  | attempts + 1, trial => by
    rw [otsSignFromWithHash]
    refine queriesSatisfy_bind (L.honestQueries_th (honestQuery_of_slotOf
      (slotOf_msg L.view L.param l e message hm _) fun h ↦ h)) ?_
    rw [messageDigestWithHash, tweakableHashWithHash, eval_th]
    cases hd : Codeword.decode (L.messageDigest l e message (base + BitVec.ofNat digestBits trial))
      with
    | none =>
      simp only [messageDigest] at hd
      simp only [hd]
      exact honestQueries_otsSignFrom he hm base attempts (trial + 1)
    | some x =>
      simp only [messageDigest] at hd
      simp only [hd]
      refine queriesSatisfy_bind (L.honestQueries_otsSecrets l e) ?_
      rw [L.eval_otsSecrets]
      exact queriesSatisfy_bind
        (queriesSatisfy_sequenceFin fun i ↦ L.honestQueries_chainWalk he i _)
        (queriesSatisfy_pure _)

theorem honestQueries_signLayer {l : Layer} {e : KeyIndex} (he : e.val < keyCount l)
    {message : HashInput} (hm : 16 ≤ message.length) :
    L.HonestQueries (signLayerWithHash (m := Comp) ⟨L.seed, L.param⟩ l e message) := by
  rw [signLayerWithHash]
  refine queriesSatisfy_bind (queriesSatisfy_bind (L.honestQueries_th (honestQuery_of_slotOf
    (slotOf_rnd L.view L.param l e L.seed message) fun h ↦ h))
    (L.honestQueries_otsSignFrom he hm _ _ _)) ?_
  split
  · exact queriesSatisfy_bind (L.honestQueries_treePath he) (queriesSatisfy_pure _)
  · exact queriesSatisfy_pure _

/-- **The signer's hash calls agree with the table.** -/
theorem honestQueries_sign (req : SigningRequest) :
    L.HonestQueries (schemeWithHashFromSeed.sign L.secretKey req) := by
  simp only [schemeWithHashFromSeed, KeptKey.scheme, keptKey, rederiveSchemeSeedKey,
    schemeWithHash]
  refine queriesSatisfy_bind (queriesSatisfy_bind (queriesSatisfy_query
    (honestQuery_of_slotOf (slotOf_seed L.view L.param L.masterSeed) fun h ↦ h))
    (queriesSatisfy_pure _)) ?_
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_oracleHash, taggedSeedWithHash]
  change L.HonestQueries (signWithHash (m := Comp) ⟨L.seed, L.param⟩ req.leafIndex req.message)
  rw [signWithHash]
  refine queriesSatisfy_bind (L.honestQueries_signLayer (keyIndexOnLayer_lt _ _)
    (by rw [length_littleEndianBytes]; omega)) ?_
  rw [L.eval_signLayer]
  cases L.layerSignature bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (littleEndianBytes 32 req.message) with
  | none => exact queriesSatisfy_pure _
  | some bottom =>
    refine queriesSatisfy_bind (L.honestQueries_treeNode bottomLayer layerHeight _ le_rfl
      (keyIndexOnLayer_lt req.leafIndex topLayer)) ?_
    rw [L.eval_treeNode]
    refine queriesSatisfy_bind (L.honestQueries_signLayer (keyIndexOnLayer_lt _ _)
      (length_littleEndianBytes 16 _).ge) ?_
    split <;> exact queriesSatisfy_pure _

end HonestTable

/-- A position of the honest table: position `position` of chain `chain` of key `key`, or the tree
value at `level`, index `index` (leaves at level `0`). -/
inductive Pos where
  /-- Position `position` of chain `chain` of key `key` of layer `layer`. -/
  | chain (layer : Layer) (key : KeyIndex) (chain : ChainIndex) (position : ℕ)
  /-- The tree value of layer `layer` at `level`, index `index`. -/
  | tree (layer : Layer) (level index : ℕ)
  deriving DecidableEq

/-- The position a structural slot's hash call outputs. -/
def slotOutput : Slot → Option Pos
  | .chain l e step i => some (.chain l e i (step.val + 1))
  | .leaf l e => some (.tree l 0 e.val)
  | .node l level index => if level = 0 then none else some (.tree l level index)
  | _ => none

/-- The positions of a structural slot's payload all satisfy `K`. -/
def PayloadIn (K : Pos → Prop) : Slot → Prop
  | .chain l e step i => K (.chain l e i step.val)
  | .leaf l e => ∀ i, K (.chain l e i (chainLength - 1))
  | .node l level index =>
      level ≠ 0 ∧ K (.tree l (level - 1) (2 * index)) ∧ K (.tree l (level - 1) (2 * index + 1))
  | _ => False

theorem PayloadIn.mono {K K' : Pos → Prop} (h : ∀ p, K p → K' p) {s : Slot}
    (hs : PayloadIn K s) : PayloadIn K' s := by
  cases s with
  | chain => exact h _ hs
  | leaf => exact fun i ↦ h _ (hs i)
  | node => exact ⟨hs.1, h _ hs.2.1, h _ hs.2.2⟩
  | msg => exact hs.elim
  | prf => exact hs.elim
  | rnd => exact hs.elim
  | param => exact hs.elim
  | seed => exact hs.elim

/-- **The positions computable from the disclosed positions `D`**: the least set containing `D`
and the output of every structural slot whose payload it contains (`known_iff`,
`known_subset`). -/
inductive Known (D : Set Pos) : Pos → Prop
  /-- A disclosed position. -/
  | disclosed (p : Pos) : p ∈ D → Known D p
  /-- A chain step's output. -/
  | chain (l : Layer) (e : KeyIndex) (i : ChainIndex) (step : ChainStep) :
      Known D (.chain l e i step.val) → Known D (.chain l e i (step.val + 1))
  /-- A leaf, from the chain ends. -/
  | leaf (l : Layer) (e : KeyIndex) :
      (∀ i, Known D (.chain l e i (chainLength - 1))) → Known D (.tree l 0 e.val)
  /-- A node, from its children. -/
  | node (l : Layer) (level index : ℕ) : Known D (.tree l level (2 * index)) →
      Known D (.tree l level (2 * index + 1)) → Known D (.tree l (level + 1) index)

/-- **The fixed point**: a position is computable when it is disclosed or the output of a slot
whose payload is computable. -/
theorem known_iff {D : Set Pos} {p : Pos} :
    Known D p ↔ p ∈ D ∨ ∃ s, slotOutput s = some p ∧ PayloadIn (Known D) s := by
  constructor
  · intro h
    cases h with
    | disclosed p hp => exact Or.inl hp
    | chain l e i step h => exact Or.inr ⟨.chain l e step i, rfl, h⟩
    | leaf l e h => exact Or.inr ⟨.leaf l e, rfl, h⟩
    | node l level index h1 h2 =>
      exact Or.inr ⟨.node l (level + 1) index, rfl, Nat.succ_ne_zero _, h1, h2⟩
  · rintro (h | ⟨s, hs, hk⟩)
    · exact .disclosed p h
    · cases s with
      | chain l e step i =>
        obtain rfl := Option.some.inj hs
        exact .chain l e i step hk
      | leaf l e =>
        obtain rfl := Option.some.inj hs
        exact .leaf l e hk
      | node l level index =>
        obtain ⟨hl, h1, h2⟩ := hk
        obtain ⟨k, rfl⟩ : ∃ k, level = k + 1 := ⟨level - 1, by omega⟩
        obtain rfl := Option.some.inj hs
        exact .node l k index h1 h2
      | msg => exact hk.elim
      | prf => exact hk.elim
      | rnd => exact hk.elim
      | param => exact hk.elim
      | seed => exact hk.elim

/-- **Least**: every set containing `D` and closed under the outputs of slots whose payload it
contains contains the computable positions. -/
theorem known_subset {D K : Set Pos} (hD : D ⊆ K)
    (hK : ∀ s p, slotOutput s = some p → PayloadIn (· ∈ K) s → p ∈ K) {p : Pos}
    (h : Known D p) : p ∈ K := by
  induction h with
  | disclosed p hp => exact hD hp
  | chain l e i step _ ih => exact hK (.chain l e step i) _ rfl ih
  | leaf l e _ ih => exact hK (.leaf l e) _ rfl ih
  | node l level index _ _ ih1 ih2 =>
    exact hK (.node l (level + 1) index) _ rfl ⟨Nat.succ_ne_zero _, ih1, ih2⟩

theorem known_mono {D D' : Set Pos} (h : D ⊆ D') {p : Pos} (hp : Known D p) : Known D' p :=
  known_subset (K := {p | Known D' p}) (fun _ hq ↦ .disclosed _ (h hq))
    (fun _ _ hs hk ↦ known_iff.2 (Or.inr ⟨_, hs, hk⟩)) hp

/-- **The public slots**: the structural slots of the table whose payload is computable from the
disclosed positions `D`. -/
def Public (D : Set Pos) : Set Slot :=
  {s | InTable s ∧ PayloadIn (Known D) s}

theorem public_mono {D D' : Set Pos} (h : D ⊆ D') : Public D ⊆ Public D' :=
  fun _ hs ↦ ⟨hs.1, hs.2.mono fun _ ↦ known_mono h⟩

/-- The positions one layer's signature by key `e` with word `x` discloses: the opened chain
positions and the path. -/
def layerDisclosed (l : Layer) (e : KeyIndex) (x : Encoding) : Set Pos :=
  {p | (∃ i, p = .chain l e i (x i).val) ∨
    ∃ level : Fin layerHeight, p = .tree l level.val (Nat.xor (e.val / 2 ^ level.val) 1)}

namespace HonestTable

variable (L : HonestTable)

/-- The value at a position. -/
def value : Pos → Digest
  | .chain l e i j => L.chainValue l e i j
  | .tree l level index => L.treeValue l level index

/-- **The target of a structural slot is the value at its output.** -/
theorem target_eq_some {s : Slot} (hs : InTable s) {p : Pos} (hp : slotOutput s = some p) :
    L.target s = some (L.value p) := by
  simp only [target, honestInput, hs, ↓reduceIte, Option.map_some, trunc128_spongeHash,
    Option.some.injEq]
  cases s with
  | chain l e step i =>
    obtain rfl := Option.some.inj hp
    rw [value, chainValue_succ]
    rfl
  | leaf l e =>
    obtain rfl := Option.some.inj hp
    rw [value, treeValue, leafKey_val]
    rfl
  | node l level index =>
    obtain ⟨k, rfl⟩ : ∃ k, level = k + 1 := ⟨level - 1, by have := hs.1; omega⟩
    obtain rfl := Option.some.inj hp
    rw [value, treeValue_succ]
    rfl
  | msg => exact hs.elim
  | prf => exact hs.elim
  | rnd => exact hs.elim
  | param => exact hs.elim
  | seed => exact hs.elim

/-- **The positions the signature of a request discloses**: both layers' opened chain positions
and paths, when the signer returns a signature; none otherwise. -/
def disclosedBy (req : SigningRequest) : Set Pos :=
  match L.select bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (littleEndianBytes 32 req.message),
    L.select topLayer (keyIndexOnLayer req.leafIndex topLayer)
      (littleEndianBytes 16 (L.bottomRoot req.leafIndex)) with
  | some bottom, some top =>
      layerDisclosed bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer) bottom.2 ∪
        layerDisclosed topLayer (keyIndexOnLayer req.leafIndex topLayer) top.2
  | _, _ => ∅

/-- The positions disclosed after the requests `reqs`: the public key's root and each request's
signature. -/
def disclosures (reqs : List SigningRequest) : Set Pos :=
  {.tree topLayer layerHeight 0} ∪ ⋃ req ∈ reqs, L.disclosedBy req

theorem disclosures_mono {reqs reqs' : List SigningRequest} (h : reqs ⊆ reqs') :
    L.disclosures reqs ⊆ L.disclosures reqs' :=
  Set.union_subset_union_right _ (Set.biUnion_subset_biUnion_left fun _ hr ↦ h hr)

/-- A signature is returned exactly when the request discloses positions. -/
theorem signature_isSome_iff (req : SigningRequest) :
    (L.signature req).isSome ↔ L.disclosedBy req ≠ ∅ := by
  simp only [signature, disclosedBy, layerSignature]
  cases L.select bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (littleEndianBytes 32 req.message) with
  | none => simp
  | some bottom =>
    cases L.select topLayer (keyIndexOnLayer req.leafIndex topLayer)
        (littleEndianBytes 16 (L.bottomRoot req.leafIndex)) with
    | none => simp
    | some top =>
      simp only [Option.map_some, Option.bind_some, Option.isSome_some, ne_eq, true_iff]
      exact Set.Nonempty.ne_empty ⟨_, Or.inl (Or.inl ⟨⟨0, by decide⟩, rfl⟩)⟩

end HonestTable

end Quantum.Xmss

end
