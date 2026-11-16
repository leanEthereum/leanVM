module

public import Quantum.Xmss.Keccak
public import Quantum.Sponge.Assembly.Prep
public import Common.WithHashBridge

@[expose] public section

/-!
# Honest computations of a hash-query scheme as sponge reads

For a fixed sponge view, the keys `t = (h, k, k')` and the inner permutation `π` (so
`φ = spongePerm t π`), the honest computations of a hash-query scheme
(`Common.SufCma.SchemeWithHash`) are deterministic classical computations.

* `trace f g x`, `queries f x`, `QueriesSatisfy f P x`: a computation answered by the functions
  `f`, its log and its queries in order.
* `honestEval t π x`: a hash-query computation with every hash an evaluation of the sponge through
  logged reads of `h`, `k`, `k'` (`Quantum.Sponge.spongeEvalM` on `blocks input`). Its result is
  the evaluation with the honest hash `spongeOut φ` (`fst_honestEval`), its reads are the sponge
  reads of the queried inputs in order (`snd_honestEval`), and it depends on `t` only through the
  values it reads (`honestEval_congr`).
* `simulateQ_schemeHash`, `simulateQ_overPermutation_generateKeys`,
  `simulateQ_overPermutation_sign`, `simulateQ_overPermutation_verify`: a hash-query scheme over
  `π` (`SchemeWithHash.overPermutation`), simulated with the permutation `statePerm φ` of
  `KeccakState` (which `keccakStateEquiv` transports to `φ`), returns what `honestEval` returns.
-/

open OracleComp OracleSpec

namespace Quantum.SufCma

open Quantum.Sponge HashSig HashSig.OverPermutation Common Common.SufCma
open Quantum.Xmss (X Z keccakStateEquiv blocks out256 spongeView keccakHash_eq_spongeHash
  simulateQ_keccakHash)
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
def readHash : QueryImpl SchemeHashSpec (StateM (List (SpongeRead X Z))) :=
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
def honestEval {α : Type} (x : OracleComp SchemeHashSpec α) : α × List (SpongeRead X Z) :=
  (simulateQ (readHash t π) x).run []

/-- The honest evaluation returns the evaluation with the honest hash. -/
theorem fst_honestEval {α : Type} (x : OracleComp SchemeHashSpec α) :
    (honestEval t π x).1 = evalWithAnswerFn (spongeOut (spongePerm t π)) x := by
  rw [honestEval, readHash_eq_traceImpl, run_simulateQ_traceImpl]

/-- **The honest reads are the sponge reads of the queried inputs**, in order. -/
theorem snd_honestEval {α : Type} (x : OracleComp SchemeHashSpec α) :
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
theorem honestEval_congr {t' : SpongeKeys X Z} {α : Type} (x : OracleComp SchemeHashSpec α)
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

/-! ## A hash-query scheme over `π` returns the honest evaluation -/

section Scheme

variable (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) {r : Type → Type} [Monad r] [LawfulMonad r]
  (impl : QueryImpl RandomPermutationOracles r)

local notation "σ" => schemeHashOverPermutation

theorem schemeHashOverPermutation_apply (input : HashInput) :
    σ input = keccakHash queryPermutation input := by
  rw [← LeanXmss.Verification.simulateQ_oracleHashWithHash,
    LeanXmss.Verification.oracleHashWithHash, simulateQ_HasQuery_query]

/-- **A hash-query computation over `π`, the honest evaluation**: answered by a simulation whose
forward calls are `statePerm (spongePerm t π)`, a hash-query computation over the statement's
permutation (`schemeHashOverPermutation`) returns what `honestEval` returns. -/
theorem simulateQ_schemeHash
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm (spongePerm t π) s)) {α : Type}
    (x : OracleComp SchemeHashSpec α) :
    simulateQ impl (simulateQ σ x) = pure (honestEval t π x).1 := by
  rw [← QueryImpl.simulateQ_compose, fst_honestEval]
  refine simulateQ_eq_pure_evalWithAnswerFn _ _ (fun input ↦ ?_) x
  rw [QueryImpl.apply_compose, schemeHashOverPermutation_apply,
    simulateQ_keccakHash impl _ himpl, spongeView_statePerm]
  rfl

variable {Seed PK SK Req Resp F : Type} (Sch : SchemeWithHash Seed PK SK Req Resp F)

/-- **Key generation over `π`** returns the honest evaluation's keys. -/
theorem simulateQ_overPermutation_generateKeys
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm (spongePerm t π) s)) (S0 : Seed) :
    simulateQ impl (Sch.overPermutation.generateKeys S0) =
      pure (honestEval t π (Sch.keygen S0)).1 :=
  simulateQ_schemeHash t π impl himpl _

/-- **The signer over `π`** returns the honest evaluation's answer. -/
theorem simulateQ_overPermutation_sign
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm (spongePerm t π) s)) (sk : SK)
    (req : Req) :
    simulateQ impl (Sch.overPermutation.sign sk req) = pure (honestEval t π (Sch.sign sk req)).1 :=
  simulateQ_schemeHash t π impl himpl _

/-- **The verifier over `π`** returns the honest evaluation's verdict. -/
theorem simulateQ_overPermutation_verify
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm (spongePerm t π) s)) (pk : PK)
    (forgery : F) :
    simulateQ impl (Sch.overPermutation.verify pk forgery) =
      pure (honestEval t π (Sch.verify pk forgery)).1 :=
  simulateQ_schemeHash t π impl himpl _

end Scheme

end Quantum.SufCma

end
