import Whir.TypedFiatShamirGame

/-! Causal, bounded typed-oracle programs. Only requested projections reach the
strategy. Ancestor completion and the terminal completion share one cache. -/
namespace Whir.TypedOracleCompiler
open TypedFiatShamirGame
open FiatShamirGame (average average_mono average_const)

universe u v w

/-- A lazy-sampling computation with a return value and a worst-case draw cap. -/
inductive Sampling (Key : Type u) (Answer : Key → Type v) (R : Type w) : Nat → Type (max u v w) where
  | ret {n} (value : R) : Sampling Key Answer R n
  | draw {n} (key : Key) (next : Answer key → Sampling Key Answer R n) :
      Sampling Key Answer R (n + 1)

namespace Sampling
variable {Key : Type u} {Answer : Key → Type v} {R : Type w}

def pad {n m} (h : n ≤ m) : Sampling Key Answer R n → Sampling Key Answer R m
  | .ret r => .ret r
  | .draw k next => match m with
    | 0 => False.elim (by omega)
    | m + 1 => .draw k (fun a => pad (by omega) (next a))

def bind {T : Type*} {n m} (t : Sampling Key Answer R n)
    (f : R → Sampling Key Answer T m) : Sampling Key Answer T (n + m) :=
  match t with
  | .ret r => pad (by omega) (f r)
  | @draw _ _ _ n k next =>
    pad (by omega) (.draw k (fun a => bind (next a) f))

def erase {n} : Sampling Key Answer R n → Game Key Answer n
  | .ret _ => .stop
  | .draw k next => .draw k (fun a => erase (next a))

/-- This evaluator is a denotational reference, never an argument to a strategy. -/
def eval (oracle : (k : Key) → Answer k) {n} : Sampling Key Answer R n → R
  | .ret r => r
  | .draw k next => eval oracle (next (oracle k))

@[simp] theorem eval_pad (oracle : (k : Key) → Answer k) {n m} (h : n ≤ m)
    (t : Sampling Key Answer R n) : eval oracle (pad h t) = eval oracle t := by
  induction t generalizing m with
  | ret => simp [pad, eval]
  | draw k next ih =>
    cases m with
    | zero => omega
    | succ m => exact ih _ _

@[simp] theorem eval_bind (oracle : (k : Key) → Answer k) {T : Type*} {n m}
    (t : Sampling Key Answer R n) (f : R → Sampling Key Answer T m) :
    eval oracle (bind t f) = eval oracle (f (eval oracle t)) := by
  induction t with
  | ret r => simp [bind, eval]
  | draw k next ih => simpa [bind, eval] using ih (oracle k)

/-- Operational traces list only actually allocated full vectors, in order. -/
inductive Runs : {n : Nat} → Sampling Key Answer R n → List (Sigma Answer) → R → Prop where
  | ret {n} (r : R) : Runs (.ret (n := n) r) [] r
  | draw {n k} {next : Answer k → Sampling Key Answer R n} {trace r}
      (a : Answer k) : Runs (next a) trace r → Runs (.draw k next) (⟨k,a⟩ :: trace) r

theorem Runs.length_le {n} {t : Sampling Key Answer R n} {trace r}
    (h : Runs t trace r) : trace.length ≤ n := by
  induction h with
  | ret => simp
  | draw a h ih => simpa using Nat.succ_le_succ ih

/-- A universal operational postcondition, with no reference oracle. -/
def Every (predicate : R → Prop) {n} : Sampling Key Answer R n → Prop
  | .ret r => predicate r
  | .draw _ next => ∀ a, Every predicate (next a)

theorem Every.mono {P Q : R → Prop} {n} {t : Sampling Key Answer R n}
    (h : Every P t) (imp : ∀ r, P r → Q r) : Every Q t := by
  induction t with
  | ret r => exact imp r h
  | draw k next ih => exact fun a => ih a (h a)

@[simp] theorem every_pad (P : R → Prop) {n m} (h : n ≤ m)
    (t : Sampling Key Answer R n) : Every P (pad h t) ↔ Every P t := by
  induction t generalizing m with
  | ret => simp [pad, Every]
  | draw k next ih =>
    cases m with
    | zero => omega
    | succ m => simp only [pad, Every, ih]

@[simp] theorem every_bind {T : Type*} (P : T → Prop) {n m}
    (t : Sampling Key Answer R n) (f : R → Sampling Key Answer T m) :
    Every P (bind t f) ↔ Every (fun r => Every P (f r)) t := by
  induction t with
  | ret r => simp [bind, Every]
  | draw k next ih => simp only [bind, every_pad, Every, ih]

theorem Runs.postcondition {P : R → Prop} {n} {t : Sampling Key Answer R n}
    {trace r} (run : Runs t trace r) (h : Every P t) : P r := by
  induction run with
  | ret => exact h
  | draw a run ih => exact ih (h a)

@[simp] theorem runs_pad {n m} (h : n ≤ m) (t : Sampling Key Answer R n) {trace r} :
    Runs (pad h t) trace r ↔ Runs t trace r := by
  induction t generalizing m trace r with
  | ret value =>
    simp only [pad]
    constructor <;> intro run <;> cases run <;> exact .ret _
  | draw k next ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [pad]
      constructor
      · intro run
        cases run with
        | draw a hr => exact .draw a ((ih a _).mp hr)
      · intro run
        cases run with
        | draw a hr => exact .draw a ((ih a _).mpr hr)

theorem runs_bind {T : Type*} {n m} (t : Sampling Key Answer R n)
    (f : R → Sampling Key Answer T m) {trace result} :
    Runs (bind t f) trace result ↔
      ∃ before value after, trace = before ++ after ∧
        Runs t before value ∧ Runs (f value) after result := by
  induction t generalizing trace result with
  | ret value =>
    simp only [bind, runs_pad]
    constructor
    · intro run
      exact ⟨[], value, trace, rfl, .ret _, run⟩
    · rintro ⟨before, value', after, ht, first, last⟩
      cases first
      simpa using ht ▸ last
  | draw k next ih =>
    simp only [bind, runs_pad]
    constructor
    · intro run
      cases run with
      | draw a hr =>
        obtain ⟨before, value, after, ht, first, last⟩ := (ih a).mp hr
        exact ⟨⟨k,a⟩ :: before, value, after, by simp [ht], .draw a first, last⟩
    · rintro ⟨before, value, after, ht, first, last⟩
      cases first with
      | draw a hr =>
        subst trace
        exact .draw a ((ih a).mpr ⟨_, value, after, rfl, hr, last⟩)

def execute (oracle : (k : Key) → Answer k) {n} :
    Sampling Key Answer R n → R × List (Sigma Answer)
  | .ret r => (r, [])
  | .draw k next =>
    let result := execute oracle (next (oracle k))
    (result.1, ⟨k, oracle k⟩ :: result.2)

theorem execute_runs (oracle : (k : Key) → Answer k) {n}
    (t : Sampling Key Answer R n) : Runs t (execute oracle t).2 (execute oracle t).1 := by
  induction t with
  | ret r => exact .ret r
  | draw k next ih => exact .draw (oracle k) (ih (oracle k))

@[simp] theorem execute_value (oracle : (k : Key) → Answer k) {n}
    (t : Sampling Key Answer R n) : (execute oracle t).1 = eval oracle t := by
  induction t with
  | ret => rfl
  | draw k next ih => exact ih (oracle k)

@[simp] theorem execute_pad (oracle : (k : Key) → Answer k) {n m} (h : n ≤ m)
    (t : Sampling Key Answer R n) : execute oracle (pad h t) = execute oracle t := by
  induction t generalizing m with
  | ret => simp [pad, execute]
  | draw k next ih =>
    cases m with
    | zero => omega
    | succ m => simp only [pad, execute, ih]

theorem execute_bind (oracle : (k : Key) → Answer k) {T : Type*} {n m}
    (t : Sampling Key Answer R n) (f : R → Sampling Key Answer T m) :
    execute oracle (bind t f) =
      ((execute oracle (f (eval oracle t))).1,
       (execute oracle t).2 ++ (execute oracle (f (eval oracle t))).2) := by
  induction t with
  | ret r => simp only [bind, execute_pad, execute, eval, List.nil_append]
  | draw k next ih => simp [bind, execute, eval, ih]

variable [∀ k, Fintype (Answer k)] [∀ k, Nonempty (Answer k)]

/-- Exact expectation in the operational experiment: sample a fresh selected
fiber uniformly, then continue with that answer, and no other oracle data. -/
noncomputable def expectation (payoff : R → ℚ) {n} : Sampling Key Answer R n → ℚ
  | .ret r => payoff r
  | .draw _k next => average (fun a => expectation payoff (next a))

omit [∀ k, Nonempty (Answer k)] in
@[simp] theorem expectation_pad (payoff : R → ℚ) {n m} (h : n ≤ m)
    (t : Sampling Key Answer R n) :
    expectation payoff (pad h t) = expectation payoff t := by
  induction t generalizing m with
  | ret => simp [pad, expectation]
  | draw k next ih =>
    cases m with
    | zero => omega
    | succ m => simp only [pad, expectation, ih]

omit [∀ k, Nonempty (Answer k)] in
theorem expectation_bind {T : Type*} (payoff : T → ℚ) {n m}
    (t : Sampling Key Answer R n) (f : R → Sampling Key Answer T m) :
    expectation payoff (bind t f) =
      expectation (fun r => expectation payoff (f r)) t := by
  induction t with
  | ret r => simp [bind, expectation]
  | draw k next ih => simp only [bind, expectation_pad, expectation, ih]

noncomputable def failureProbability (failure : R → Prop) {n}
    (t : Sampling Key Answer R n) : ℚ := by
  classical
  exact expectation (fun r => if failure r then 1 else 0) t

noncomputable def badProbability (bad : (k : Key) → Answer k → Prop) {n} :
    Sampling Key Answer R n → ℚ
  | .ret _ => 0
  | .draw k next => by
    classical
    exact average (fun a => if bad k a then 1 else badProbability bad (next a))

omit [∀ k, Nonempty (Answer k)] in
/-- Erasure preserves the exact probability of an allocated bad vector, not
merely its upper bound. Deterministic work and cache hits do not draw. -/
theorem distribution_correspondence (bad : (k : Key) → Answer k → Prop) {n}
    (t : Sampling Key Answer R n) : badProbability bad t = risk bad (erase t) := by
  induction t with
  | ret => rfl
  | draw k next ih => simp only [badProbability, erase, risk, ih]

theorem expectation_le_one (payoff : R → ℚ) (h : ∀ r, payoff r ≤ 1) {n}
    (t : Sampling Key Answer R n) : expectation payoff t ≤ 1 := by
  induction t with
  | ret r => exact h r
  | draw k next ih =>
    exact (average_mono ih).trans_eq (average_const 1)

/-- A terminal cover is checked on operational executions, including early
stops. No successful-path budget or oracle tape is supplied to the strategy. -/
theorem failure_le_risk (bad : (k : Key) → Answer k → Prop) (failure : R → Prop)
    {n} (t : Sampling Key Answer R n)
    (cover : ∀ trace r, Runs t trace r → failure r →
      ∃ ka ∈ trace, bad ka.1 ka.2) :
    failureProbability failure t ≤ risk bad (erase t) := by
  classical
  induction t with
  | ret r =>
    have hf : ¬ failure r := by
      intro h
      obtain ⟨ka, hk, _⟩ := cover [] r (.ret r) h
      simp at hk
    simp [failureProbability, expectation, erase, risk, hf]
  | draw k next ih =>
    change average (fun a => expectation (fun r => if failure r then 1 else 0) (next a)) ≤ _
    rw [erase, risk]
    apply average_mono
    intro a
    by_cases hb : bad k a
    · simp only [ite_eq_left hb]
      exact expectation_le_one _ (by intro r; split <;> norm_num) _
    · simp only [ite_eq_right hb]
      apply ih a
      intro trace r hr hf
      obtain ⟨ka, hk, hbad⟩ := cover _ r (.draw a hr) hf
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact (hb hbad).elim
      · exact ⟨ka, hk, hbad⟩

end Sampling

section Compiler
variable {S M Q : Type u} {A : Q → Type u}
variable [DecidableEq S] [DecidableEq M]
variable (query : S × List M → Q)

abbrev History := List (M × Sigma A)
abbrev RawCache := Cache (S × List M) (fun key => A (query key))
abbrev FullKey := FullInput S M Q A
abbrev Fiber (key : FullKey (S := S) (M := M) (A := A)) :=
  A (query (key.statement, key.messages))
abbrev Computation (R : Type u) (n : Nat) :=
  Sampling (FullKey (S := S) (M := M) (A := A)) (Fiber query) R n

/-- A syntax-level bound on every request, even abandoned and rejecting branches. -/
structure Request (S M : Type u) (B : Nat) where
  statement : S
  messages : List M
  bounded : messages.length ≤ B

/-- `stop` requests invisible final verification completion. The continuation
receives only the requested projection, never the cache or a total oracle. -/
inductive Machine (S M : Type u) (A : Q → Type u) (B : Nat) : Nat → Type (u+1) where
  | stop {K} (final : Request S M B) : Machine S M A B K
  | ask {K} (request : Request S M B) (R : Type u)
      (project : History (M := M) (A := A) → R)
      (next : R → Machine S M A B K) : Machine S M A B (K+1)

/-- Recursive ancestor completion. Raw cache keys are globally shared; a miss
samples the full canonical key containing the ancestors just completed. -/
def completeCausal (s : S) : (p : List M) → RawCache (A := A) query →
    Computation (A := A) query (Allocation query A) p.length
  | [], cache => .ret ⟨[], cache, 0⟩
  | m :: p, cache =>
    Sampling.bind (completeCausal s p cache) (fun past =>
      match past.cache (s, m :: p) with
      | some a => .ret ⟨(m, ⟨query (s,m::p),a⟩) :: past.history, past.cache, past.fresh⟩
      | none => .draw ⟨s, m :: p, past.history⟩ (fun a =>
        .ret ⟨(m, ⟨query (s,m::p),a⟩) :: past.history,
          put past.cache (s,m::p) a, past.fresh + 1⟩))

theorem completeCausal_reference (oracle : Oracle (A := A) query) (s : S) (p : List M)
    (cache : RawCache (A := A) query) :
    Sampling.eval oracle (completeCausal query s p cache) = allocate query oracle s p cache := by
  induction p generalizing cache with
  | nil => rfl
  | cons m p ih =>
    rw [completeCausal, Sampling.eval_bind, ih]
    simp only [allocate]
    split <;> rename_i h <;> simp [h, Sampling.eval, put]

/-- The deterministic reference invariant therefore holds for the causal
interpreter, without exposing the reference oracle to any continuation. -/
theorem completeCausal_correct (oracle : Oracle (A := A) query) (s : S) (p : List M)
    (cache : RawCache (A := A) query) (correct : CacheCorrect query oracle cache) :
    (Sampling.eval oracle (completeCausal query s p cache)).history = complete query oracle s p ∧
    CacheCorrect query oracle (Sampling.eval oracle (completeCausal query s p cache)).cache := by
  rw [completeCausal_reference]
  exact allocate_correct query oracle s p cache correct

/-- Existing entries are immutable, independently of the statement or clone
currently being completed. This property does not need cache correctness. -/
theorem allocate_preserves (oracle : Oracle (A := A) query) (s : S) (p : List M)
    (cache : RawCache (A := A) query) (key : S × List M) (x : A (query key))
    (hit : cache key = some x) :
    (allocate query oracle s p cache).cache key = some x := by
  induction p with
  | nil => exact hit
  | cons m p ih =>
    simp only [allocate]
    split
    · exact ih
    · rename_i miss
      have ne : key ≠ (s,m::p) := by
        intro he
        subst key
        rw [ih] at miss
        contradiction
      simpa only [Function.update_of_ne ne] using ih

/-- Exact allocation count for the executable interpreter. A cache hit adds
zero trace entries; a miss adds exactly one full-vector entry. -/
theorem completeCausal_count (oracle : Oracle (A := A) query) (s : S) (p : List M)
    (cache : RawCache (A := A) query) :
    (Sampling.execute oracle (completeCausal query s p cache)).2.length =
      (allocate query oracle s p cache).fresh := by
  induction p generalizing cache with
  | nil => rfl
  | cons m p ih =>
    rw [completeCausal, Sampling.execute_bind, completeCausal_reference]
    simp only [allocate]
    split <;> rename_i h <;> simp [h, Sampling.execute, ih]

theorem completeCausal_preserves_every (s : S) (p : List M)
    (cache : RawCache (A := A) query) (key : S × List M) (x : A (query key))
    (hit : cache key = some x) :
    Sampling.Every (fun a => a.cache key = some x) (completeCausal query s p cache) := by
  induction p with
  | nil => exact hit
  | cons m p ih =>
    rw [completeCausal, Sampling.every_bind]
    apply ih.mono
    intro past hp
    split
    · exact hp
    · rename_i miss
      intro a
      have ne : key ≠ (s,m::p) := by
        intro he
        subst key
        rw [hp] at miss
        contradiction
      simpa only [Sampling.Every, put_other _ _ _ _ ne] using hp

structure Terminal (B : Nat) where
  request : Request S M B
  allocation : Allocation query A

def completeRequest {B} (request : Request S M B) (cache : RawCache (A := A) query) :
    Computation (A := A) query (Allocation query A) B :=
  Sampling.pad request.bounded (completeCausal query request.statement request.messages cache)

def compile {B K} (machine : Machine S M A B K) (cache : RawCache (A := A) query) :
    Computation (A := A) query (Terminal (A := A) query B) (B * (K+1)) :=
  match machine with
  | .stop final =>
    Sampling.pad (by simp only [Nat.mul_add, Nat.mul_one]; omega) (Sampling.bind (completeRequest query final cache)
      (fun a => Sampling.ret (n := 0) ⟨final,a⟩))
  | @Machine.ask _ _ _ _ _ K request R project next =>
    Sampling.pad (by simp only [Nat.mul_add, Nat.mul_one]; omega) (Sampling.bind (completeRequest query request cache)
      (fun a => compile (next (project a.history)) a.cache))

/-- Functional reference execution of the same adaptive syntax. -/
def reference (oracle : Oracle (A := A) query) {B K}
    (machine : Machine S M A B K) (cache : RawCache (A := A) query) :
    Terminal (A := A) query B :=
  match machine with
  | .stop final => ⟨final, allocate query oracle final.statement final.messages cache⟩
  | .ask request _ project next =>
    let a := allocate query oracle request.statement request.messages cache
    reference oracle (next (project a.history)) a.cache

theorem compile_reference (oracle : Oracle (A := A) query) {B K}
    (machine : Machine S M A B K) (cache : RawCache (A := A) query) :
    Sampling.eval oracle (compile query machine cache) = reference query oracle machine cache := by
  induction machine generalizing cache with
  | stop final => simp [compile, reference, completeRequest, completeCausal_reference, Sampling.eval]
  | ask request R project next ih =>
    simp only [compile, Sampling.eval_pad, Sampling.eval_bind, completeRequest,
      completeCausal_reference, reference]
    exact ih _ _

/-- One global cache survives all adaptive requests and final completion.
In particular, switching statements or selecting a clone cannot reset it. -/
theorem compile_preserves (oracle : Oracle (A := A) query) {B K}
    (machine : Machine S M A B K) (cache : RawCache (A := A) query)
    (key : S × List M) (x : A (query key)) (hit : cache key = some x) :
    (Sampling.eval oracle (compile query machine cache)).allocation.cache key = some x := by
  rw [compile_reference]
  induction machine generalizing cache with
  | stop final => exact allocate_preserves query oracle _ _ cache key x hit
  | ask request R project next ih =>
    exact ih _ _ (allocate_preserves query oracle _ _ cache key x hit)

theorem compile_correct (oracle : Oracle (A := A) query) {B K}
    (machine : Machine S M A B K) (cache : RawCache (A := A) query)
    (correct : CacheCorrect query oracle cache) :
    CacheCorrect query oracle
      (Sampling.eval oracle (compile query machine cache)).allocation.cache := by
  rw [compile_reference]
  induction machine generalizing cache with
  | stop final => exact (allocate_correct query oracle _ _ cache correct).2
  | ask request R project next ih =>
    exact ih _ _ (allocate_correct query oracle _ _ cache correct).2

theorem compile_preserves_every {B K} (machine : Machine S M A B K)
    (cache : RawCache (A := A) query) (key : S × List M) (x : A (query key))
    (hit : cache key = some x) :
    Sampling.Every (fun r => r.allocation.cache key = some x) (compile query machine cache) := by
  induction machine generalizing cache with
  | stop final =>
    simp only [compile, Sampling.every_pad, Sampling.every_bind, completeRequest, Sampling.Every]
    exact completeCausal_preserves_every query _ _ cache key x hit
  | ask request R project next ih =>
    simp only [compile, Sampling.every_pad, Sampling.every_bind, completeRequest]
    exact (completeCausal_preserves_every query _ _ cache key x hit).mono
      (fun past hp => ih _ past.cache hp)

/-- Global-cache immutability for every operational branch, not only those
evaluated against a preselected oracle table. -/
theorem compile_runs_preserves {B K} (machine : Machine S M A B K)
    (cache : RawCache (A := A) query) (key : S × List M) (x : A (query key))
    (hit : cache key = some x) {trace result}
    (run : Sampling.Runs (compile query machine cache) trace result) :
    result.allocation.cache key = some x :=
  run.postcondition (compile_preserves_every query machine cache key x hit)

/-- All executions have the resource cap, not just accepted terminal paths. -/
theorem compile_cap {B K} (machine : Machine S M A B K) (cache : RawCache (A := A) query)
    {trace result} (run : Sampling.Runs (compile query machine cache) trace result) :
    trace.length ≤ B * (K+1) := run.length_le

/-- A completed history can be read solely from the current partial cache. -/
inductive CachedHistory (cache : RawCache (A := A) query) (s : S) :
    List M → History (M := M) (A := A) → Prop where
  | nil : CachedHistory cache s [] []
  | cons {m p history} (a : A (query (s,m::p)))
      (older : CachedHistory cache s p history) (hit : cache (s,m::p) = some a) :
      CachedHistory cache s (m::p) ((m,⟨query (s,m::p),a⟩)::history)

omit [DecidableEq S] [DecidableEq M] in
theorem CachedHistory.mono {cache next : RawCache (A := A) query} {s p history}
    (h : CachedHistory query cache s p history)
    (growth : ∀ key a, cache key = some a → next key = some a) :
    CachedHistory query next s p history := by
  induction h with
  | nil => exact .nil
  | cons a older hit ih => exact .cons a ih (growth _ _ hit)

omit [DecidableEq S] [DecidableEq M] in
theorem CachedHistory.unique {cache : RawCache (A := A) query} {s p left right}
    (hl : CachedHistory query cache s p left) (hr : CachedHistory query cache s p right) :
    left = right := by
  induction hl generalizing right with
  | nil => cases hr; rfl
  | cons a older hit ih =>
    cases hr with
    | cons b prior hb =>
      have hab : a = b := Option.some.inj (hit.symm.trans hb)
      subst b
      rw [ih prior]

/-- Every cached answer remembers an actual earlier allocation at its exact
full key. Ancestors are read from the same immutable global cache. -/
def CacheRecorded (cache : RawCache (A := A) query)
    (trace : List (Sigma (Fiber (A := A) query))) : Prop :=
  ∀ s m p a, cache (s,m::p) = some a →
    ∃ history, CachedHistory query cache s p history ∧
      (⟨⟨s,m::p,history⟩,a⟩ : Sigma (Fiber query)) ∈ trace

omit [DecidableEq S] [DecidableEq M] in
theorem empty_cache_recorded :
    CacheRecorded (A := A) query (fun _ => none) [] := by
  intro s m p a h
  cases h

omit [DecidableEq S] [DecidableEq M] in
theorem CacheRecorded.mono_trace {cache : RawCache (A := A) query} {trace more}
    (h : CacheRecorded query cache trace) (subset : ∀ x ∈ trace, x ∈ more) :
    CacheRecorded query cache more := by
  intro s m p a hit
  obtain ⟨history, hc, ht⟩ := h s m p a hit
  exact ⟨history,hc,subset _ ht⟩

theorem CacheRecorded.insert {cache : RawCache (A := A) query} {trace s m p history}
    (h : CacheRecorded query cache trace) (past : CachedHistory query cache s p history)
    (miss : cache (s,m::p) = none) (a : A (query (s,m::p))) :
    CacheRecorded query (put cache (s,m::p) a)
      (trace ++ [⟨⟨s,m::p,history⟩,a⟩]) := by
  have growth : ∀ key x, cache key = some x → put cache (s,m::p) a key = some x := by
    intro key x hx
    have ne : key ≠ (s,m::p) := by
      intro he
      subst key
      rw [miss] at hx
      contradiction
    simpa only [put_other _ _ _ _ ne] using hx
  intro t n q b hb
  by_cases he : (t,n::q) = (s,m::p)
  · cases he
    simp only [put_self, Option.some.injEq] at hb
    subst b
    exact ⟨history,CachedHistory.mono query past growth,by simp⟩
  · rw [put_other _ _ _ _ he] at hb
    obtain ⟨older, hc, ht⟩ := h t n q b hb
    exact ⟨older,CachedHistory.mono query hc growth,List.mem_append_left _ ht⟩

/-- Completion preserves the trace provenance invariant and reconstructs the
returned history from the final cache, on every operational branch. -/
theorem completeCausal_recorded (s : S) (p : List M)
    (cache : RawCache (A := A) query) {before trace result}
    (recorded : CacheRecorded query cache before)
    (run : Sampling.Runs (completeCausal query s p cache) trace result) :
    CachedHistory query result.cache s p result.history ∧
      CacheRecorded query result.cache (before ++ trace) := by
  induction p generalizing cache before trace result with
  | nil =>
    cases run
    exact ⟨.nil, by simpa using recorded⟩
  | cons m p ih =>
    rw [completeCausal, Sampling.runs_bind] at run
    obtain ⟨firstTrace, past, lastTrace, ht, first, last⟩ := run
    obtain ⟨hp, hs⟩ := ih cache recorded first
    subst trace
    split at last
    · rename_i a hit
      cases last
      exact ⟨.cons a hp hit, by simpa using hs⟩
    · rename_i miss
      cases last with
      | draw a rest =>
        cases rest
        have growth : ∀ key x, past.cache key = some x →
            put past.cache (s,m::p) a key = some x := by
          intro key x hx
          have ne : key ≠ (s,m::p) := by
            intro he
            subst key
            rw [miss] at hx
            contradiction
          simpa only [put_other _ _ _ _ ne] using hx
        exact ⟨.cons a (CachedHistory.mono query hp growth) (put_self _ _ _),
          by simpa only [List.append_assoc] using CacheRecorded.insert query hs hp miss a⟩

/-- Full-key/value membership, recursively for every ancestor in a completed
history. Unlike raw-key coverage this also fixes the completed ancestor vector. -/
inductive HistoryRecorded (s : S) (trace : List (Sigma (Fiber (A := A) query))) :
    List M → History (M := M) (A := A) → Prop where
  | nil : HistoryRecorded s trace [] []
  | cons {m p history} (a : A (query (s,m::p)))
      (older : HistoryRecorded s trace p history)
      (allocated : (⟨⟨s,m::p,history⟩,a⟩ : Sigma (Fiber query)) ∈ trace) :
      HistoryRecorded s trace (m::p) ((m,⟨query (s,m::p),a⟩)::history)

omit [DecidableEq S] [DecidableEq M] in
theorem HistoryRecorded.erases {s trace p history}
    (h : HistoryRecorded (A := A) query s trace p history) : history.map Prod.fst = p := by
  induction h with
  | nil => rfl
  | cons a older allocated ih => simp [ih]

omit [DecidableEq S] [DecidableEq M] in
theorem HistoryRecorded.at_index {s trace p history}
    (h : HistoryRecorded (A := A) query s trace p history) (i : Nat) (hi : i < p.length) :
    ∃ m tail past, ∃ a : A (query (s,m::tail)),
      p.drop i = m::tail ∧ history.drop i = (m,⟨query (s,m::tail),a⟩)::past ∧
      (⟨⟨s,m::tail,past⟩,a⟩ : Sigma (Fiber query)) ∈ trace := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons m p history a older allocated ih =>
    cases i with
    | zero => exact ⟨m,p,history,a,rfl,rfl,allocated⟩
    | succ i =>
      simpa only [List.drop_succ_cons] using ih i (by simpa using hi)

omit [DecidableEq S] [DecidableEq M] in
theorem CachedHistory.recorded {cache : RawCache (A := A) query} {s p history trace}
    (hc : CachedHistory query cache s p history) (ht : CacheRecorded query cache trace) :
    HistoryRecorded query s trace p history := by
  induction hc with
  | nil => exact .nil
  | @cons m p history a older hit ih =>
    obtain ⟨past,hp,hm⟩ := ht s m p a hit
    have he := CachedHistory.unique query hp older
    subst past
    exact .cons a ih hm

theorem compile_recorded {B K} (machine : Machine S M A B K)
    (cache : RawCache (A := A) query) {before trace result}
    (recorded : CacheRecorded query cache before)
    (run : Sampling.Runs (compile query machine cache) trace result) :
    HistoryRecorded query result.request.statement (before ++ trace)
      result.request.messages result.allocation.history := by
  induction machine generalizing cache before trace result with
  | stop final =>
    simp only [compile, Sampling.runs_pad, Sampling.runs_bind] at run
    obtain ⟨firstTrace, past, lastTrace, ht, first, last⟩ := run
    cases last
    simp only [completeRequest, Sampling.runs_pad] at first
    obtain ⟨hc,hr⟩ := completeCausal_recorded query _ _ cache recorded first
    simpa only [ht, List.append_nil] using CachedHistory.recorded query hc hr
  | ask request R project next ih =>
    simp only [compile, Sampling.runs_pad, Sampling.runs_bind] at run
    obtain ⟨firstTrace, past, lastTrace, ht, first, last⟩ := run
    simp only [completeRequest, Sampling.runs_pad] at first
    obtain ⟨_,hr⟩ := completeCausal_recorded query _ _ cache recorded first
    have hf := ih _ past.cache hr last
    simpa only [ht, List.append_assoc] using hf

/-- Every final ancestor, including cache hits allocated on earlier branches,
has its exact canonical full-key/value pair in the actual allocation trace. -/
theorem final_history_in_trace {B K} (machine : Machine S M A B K) {trace result}
    (run : Sampling.Runs (compile query machine (fun _ => none)) trace result) :
    HistoryRecorded query result.request.statement trace
      result.request.messages result.allocation.history := by
  simpa using compile_recorded query machine _ (empty_cache_recorded query) run

theorem final_ancestor_allocated {B K} (machine : Machine S M A B K) {trace result}
    (run : Sampling.Runs (compile query machine (fun _ => none)) trace result)
    (i : Nat) (hi : i < result.request.messages.length) :
    ∃ m tail past, ∃ a : A (query (result.request.statement,m::tail)),
      result.request.messages.drop i = m::tail ∧
      result.allocation.history.drop i =
        (m,⟨query (result.request.statement,m::tail),a⟩)::past ∧
      (⟨⟨result.request.statement,m::tail,past⟩,a⟩ : Sigma (Fiber query)) ∈ trace :=
  HistoryRecorded.at_index query (final_history_in_trace query machine run) i hi

variable [∀ q, Fintype (A q)] [∀ q, Nonempty (A q)]
open Classical

/-- Direct lazy-sampling semantics of the adaptive machine. Ancestors are
completed before the projected answer is passed to the continuation. -/
noncomputable def operationalExpectation {B K} (payoff : Terminal (A := A) query B → ℚ)
    (machine : Machine S M A B K) (cache : RawCache (A := A) query) : ℚ :=
  match machine with
  | .stop final =>
    Sampling.expectation (fun a => payoff ⟨final, a⟩)
      (completeCausal query final.statement final.messages cache)
  | .ask request _ project next =>
    Sampling.expectation
      (fun a => operationalExpectation payoff (next (project a.history)) a.cache)
      (completeCausal query request.statement request.messages cache)

omit [∀ q, Nonempty (A q)] in
/-- Exact equality for every terminal payoff, hence the entire terminal
distribution, between the direct machine interpreter and its compiled tree. -/
theorem compile_distribution {B K} (payoff : Terminal (A := A) query B → ℚ)
    (machine : Machine S M A B K) (cache : RawCache (A := A) query) :
    Sampling.expectation payoff (compile query machine cache) =
      operationalExpectation query payoff machine cache := by
  induction machine generalizing cache with
  | stop final =>
    simp [compile, Sampling.expectation_bind, Sampling.expectation, completeRequest,
      operationalExpectation]
  | ask request R project next ih =>
    simp only [compile, Sampling.expectation_pad, Sampling.expectation_bind,
      completeRequest, ih, operationalExpectation]

theorem compiler_risk_bound {B K} (machine : Machine S M A B K)
    (bad : (key : FullKey (S := S) (M := M) (A := A)) → Fiber query key → Prop)
    (epsilon : ℚ) (nonneg : 0 ≤ epsilon)
    (sparse : ∀ key, average (fun a => if bad key a then 1 else 0) ≤ epsilon) :
    Sampling.badProbability bad (compile query machine (fun _ => none)) ≤
      (B * (K+1)) * epsilon := by
  rw [Sampling.distribution_correspondence]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    risk_bound bad epsilon nonneg sparse (Sampling.erase (compile query machine (fun _ => none)))

theorem compiler_failure_bound {B K} (machine : Machine S M A B K)
    (bad : (key : FullKey (S := S) (M := M) (A := A)) → Fiber query key → Prop)
    (failure : Terminal (A := A) query B → Prop)
    (epsilon : ℚ) (nonneg : 0 ≤ epsilon)
    (sparse : ∀ key, average (fun a => if bad key a then 1 else 0) ≤ epsilon)
    (cover : ∀ trace result, Sampling.Runs (compile query machine (fun _ => none)) trace result →
      failure result → ∃ ka ∈ trace, bad ka.1 ka.2) :
    Sampling.failureProbability failure (compile query machine (fun _ => none)) ≤
      ((B * (K+1) : Nat) : ℚ) * epsilon :=
  (Sampling.failure_le_risk bad failure _ cover).trans
    (risk_bound bad epsilon nonneg sparse _)

end Compiler
end Whir.TypedOracleCompiler
