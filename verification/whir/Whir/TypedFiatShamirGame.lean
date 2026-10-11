import Whir.FiatShamirGame

/-! Dependent-alphabet lazy sampling. The request is selected before its answer;
only the selected fiber is sampled. A sigma of heterogeneous answers is never
sampled uniformly. Stopping is built into the finite experiment. -/
namespace Whir.TypedFiatShamirGame
open scoped BigOperators
open FiatShamirGame
open Classical

variable {Key : Type*} {Answer : Key → Type*}
variable [∀ k, Fintype (Answer k)] [∀ k, Nonempty (Answer k)]

/-- A finite allocation experiment. Deterministic work, cache hits, clone
selection and partial-slice projections are compiled into the continuation;
only a fresh whole-vector allocation uses `draw`. -/
inductive Game (Key : Type*) (Answer : Key → Type*) : Nat → Type _ where
  | stop {n} : Game Key Answer n
  | draw {n} (key : Key) (next : Answer key → Game Key Answer n) : Game Key Answer (n+1)

noncomputable def risk (bad : (k : Key) → Answer k → Prop) :
    {n : Nat} → Game Key Answer n → ℚ
  | _, .stop => 0
  | _, .draw k next => by
    classical
    exact average (fun a => if bad k a then 1 else risk bad (next a))

theorem risk_nonneg (bad : (k : Key) → Answer k → Prop) {n : Nat}
    (g : Game Key Answer n) : 0 ≤ risk bad g := by
  induction g with
  | stop => exact le_rfl
  | draw k next ih =>
    classical
    rw [risk, ← average_const (C := Answer k) 0]
    apply average_mono
    intro a
    split
    · norm_num
    · exact ih a

theorem risk_le_one (bad : (k : Key) → Answer k → Prop) {n : Nat}
    (g : Game Key Answer n) : risk bad g ≤ 1 := by
  induction g with
  | stop => norm_num [risk]
  | draw k next ih =>
    classical
    calc
      _ ≤ average (fun _ : Answer k => (1 : ℚ)) := by
        apply average_mono
        intro a
        split
        · exact le_rfl
        · exact ih a
      _ = 1 := average_const 1

/-- Optional stopping never requires a successful-path depth bound: every branch
has the index cap, and an early stop contributes zero additional failure. -/
theorem risk_bound (bad : (k : Key) → Answer k → Prop) (epsilon : ℚ)
    (nonneg : 0 ≤ epsilon)
    (sparse : ∀ k, average (fun a => if bad k a then 1 else 0) ≤ epsilon)
    {n : Nat} (g : Game Key Answer n) : risk bad g ≤ n * epsilon := by
  induction g with
  | @stop n => simpa [risk] using mul_nonneg (show (0 : ℚ) ≤ n by positivity) nonneg
  | @draw n k next ih =>
    classical
    rw [risk]
    calc
      _ ≤ average (fun a => (if bad k a then 1 else 0) + n * epsilon) := by
        apply average_mono
        intro a
        split
        · have hn : (0 : ℚ) ≤ n * epsilon := mul_nonneg (by positivity) nonneg
          linarith
        · simpa using ih a
      _ = average (fun a => if bad k a then 1 else 0) + n * epsilon := by
        rw [average_add, average_const]
      _ ≤ epsilon + n * epsilon := by have h := sparse k; linarith
      _ = (n+1 : Nat) * epsilon := by push_cast; ring

/-- A single global, dependent cache. Its key includes the statement and full
canonical history in applications. Repeated slices all project this same value. -/
abbrev Cache (Key : Type*) (Answer : Key → Type*) := (k : Key) → Option (Answer k)

def put [DecidableEq Key] (cache : Cache Key Answer)
    (k : Key) (a : Answer k) : Cache Key Answer := Function.update cache k (some a)

omit [∀ k, Fintype (Answer k)] [∀ k, Nonempty (Answer k)] in
@[simp] theorem put_self [DecidableEq Key] (cache : Cache Key Answer)
    (k : Key) (a : Answer k) : put cache k a k = some a := by
  simp [put]

omit [∀ k, Fintype (Answer k)] [∀ k, Nonempty (Answer k)] in
@[simp] theorem put_other [DecidableEq Key] (cache : Cache Key Answer)
    (k j : Key) (a : Answer k) (h : j ≠ k) : put cache k a j = cache j := by
  simp [put, h]

/-- A hit, clone, repeated request or partial-coordinate request has no sampling
operation at all. The projection may consume any overlapping part of the vector. -/
def readPart {R : Type*} (cache : Cache Key Answer) (k : Key)
    (project : Answer k → R) : Option R := (cache k).map project

omit [∀ k, Fintype (Answer k)] [∀ k, Nonempty (Answer k)] in
theorem readPart_put [DecidableEq Key] {R : Type*} (cache : Cache Key Answer)
    (k : Key) (a : Answer k) (project : Answer k → R) :
    readPart (put cache k a) k project = some (project a) := by simp [readPart]

omit [∀ k, Nonempty (Answer k)] in
/-- Exact conditional uniformity of a fresh dependent table fiber. This identity
is an integration statement, not an interface exposing the other table entries. -/
theorem fresh_coordinate [Fintype Key] [DecidableEq Key] (k : Key)
    (f : ((j : {j : Key // j ≠ k}) → Answer j) → Answer k → ℚ) :
    average (fun table : (j : Key) → Answer j => f (fun j => table j) (table k)) =
      average (fun rest : (j : {j : Key // j ≠ k}) → Answer j => average (f rest)) := by
  let e := Equiv.piSplitAt k Answer
  have hs : (∑ table : (j : Key) → Answer j, f (fun j => table j) (table k)) =
      ∑ pair : Answer k × ((j : {j : Key // j ≠ k}) → Answer j), f pair.2 pair.1 :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hc := Fintype.card_congr e
  unfold average
  rw [hs, hc, Fintype.card_prod, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Nat.cast_mul, ← Finset.sum_div]
  ring

section Ancestors
variable {S M Q : Type*} {A : Q → Type*}

/-- A canonical full input records both the raw prefix key and every completed
ancestor answer. Equality therefore includes the statement and all history. -/
structure FullInput (S M Q : Type*) (A : Q → Type*) where
  statement : S
  messages : List M
  ancestors : List (M × Sigma A)

abbrev Oracle (query : S × List M → Q) :=
  (input : FullInput S M Q A) → A (query (input.statement, input.messages))

def complete (query : S × List M → Q) (oracle : Oracle (A := A) query) (s : S) :
    List M → List (M × Sigma A)
  | [] => []
  | m :: older =>
    let past := complete query oracle s older
    (m, ⟨query (s, m :: older), oracle ⟨s, m :: older, past⟩⟩) :: past

theorem complete_erases (query : S × List M → Q) (oracle : Oracle (A := A) query)
    (s : S) (p : List M) : (complete query oracle s p).map Prod.fst = p := by
  induction p with
  | nil => rfl
  | cons m p ih => simp [complete, ih]

structure Allocation (query : S × List M → Q) (A : Q → Type*) where
  history : List (M × Sigma A)
  cache : Cache (S × List M) (fun key => A (query key))
  fresh : Nat

/-- Ancestor completion uses one shared dependent cache across all statements,
branches and clones. No unused component of another alphabet is sampled. -/
def allocate [DecidableEq S] [DecidableEq M]
    (query : S × List M → Q) (oracle : Oracle (A := A) query) (s : S) :
    List M → Cache (S × List M) (fun key => A (query key)) → Allocation query A
  | [], cache => ⟨[], cache, 0⟩
  | m :: p, cache =>
    let a := allocate query oracle s p cache
    match a.cache (s, m :: p) with
    | some x => ⟨(m, ⟨query (s, m :: p), x⟩) :: a.history, a.cache, a.fresh⟩
    | none =>
      let x := oracle ⟨s, m :: p, a.history⟩
      ⟨(m, ⟨query (s, m :: p), x⟩) :: a.history,
        Function.update a.cache (s, m :: p) (some x), a.fresh + 1⟩

def canonicalAnswer (query : S × List M → Q) (oracle : Oracle (A := A) query)
    (key : S × List M) : Option (A (query key)) :=
  match key.2 with
  | [] => none
  | _m :: p => some (oracle ⟨key.1, key.2, complete query oracle key.1 p⟩)

def CacheCorrect (query : S × List M → Q) (oracle : Oracle (A := A) query)
    (cache : Cache (S × List M) (fun key => A (query key))) : Prop :=
  ∀ key x, cache key = some x → canonicalAnswer query oracle key = some x

theorem empty_cache_correct (query : S × List M → Q) (oracle : Oracle (A := A) query) :
    CacheCorrect query oracle (fun _ => none) := by
  intro key x h
  cases h

theorem allocate_correct [DecidableEq S] [DecidableEq M]
    (query : S × List M → Q) (oracle : Oracle (A := A) query) (s : S) (p : List M)
    (cache : Cache (S × List M) (fun key => A (query key)))
    (correct : CacheCorrect query oracle cache) :
    (allocate query oracle s p cache).history = complete query oracle s p ∧
      CacheCorrect query oracle (allocate query oracle s p cache).cache := by
  induction p generalizing cache with
  | nil => exact ⟨rfl, correct⟩
  | cons m p ih =>
    obtain ⟨hh, hc⟩ := ih cache correct
    have ho : oracle ⟨s, m :: p, (allocate query oracle s p cache).history⟩ =
        oracle ⟨s, m :: p, complete query oracle s p⟩ := by
      congr 1
      rw [hh]
    simp only [allocate]
    split
    next x h =>
      have he := hc (s, m :: p) x h
      simp only [canonicalAnswer, Option.some.injEq] at he
      exact ⟨by simp [complete, hh, he], hc⟩
    next h =>
      constructor
      · simp [complete, hh, ho]
      · intro key x he
        by_cases hk : key = (s, m :: p)
        · subst key
          simp only [Function.update_self, Option.some.injEq] at he
          simp only [canonicalAnswer, Option.some.injEq]
          exact ho.symm.trans he
        · exact hc key x (by simpa only [Function.update_of_ne hk] using he)

theorem allocate_fresh_le [DecidableEq S] [DecidableEq M]
    (query : S × List M → Q) (oracle : Oracle (A := A) query) (s : S) (p : List M)
    (cache : Cache (S × List M) (fun key => A (query key))) :
    (allocate query oracle s p cache).fresh ≤ p.length := by
  induction p with
  | nil => simp [allocate]
  | cons m p ih =>
    simp only [allocate]
    split <;> simp only [List.length_cons] <;> omega

def serve [DecidableEq S] [DecidableEq M]
    (query : S × List M → Q) (oracle : Oracle (A := A) query) :
    List (S × List M) → Cache (S × List M) (fun key => A (query key)) →
      Cache (S × List M) (fun key => A (query key)) × Nat
  | [], cache => (cache, 0)
  | key :: rest, cache =>
    let a := allocate query oracle key.1 key.2 cache
    let b := serve query oracle rest a.cache
    (b.1, a.fresh + b.2)

theorem serve_correct [DecidableEq S] [DecidableEq M]
    (query : S × List M → Q) (oracle : Oracle (A := A) query)
    (requests : List (S × List M)) (cache : Cache (S × List M) (fun key => A (query key)))
    (correct : CacheCorrect query oracle cache) :
    CacheCorrect query oracle (serve query oracle requests cache).1 := by
  induction requests generalizing cache with
  | nil => exact correct
  | cons key rest ih =>
    exact ih _ (allocate_correct query oracle key.1 key.2 cache correct).2

theorem serve_cost_le [DecidableEq S] [DecidableEq M]
    (query : S × List M → Q) (oracle : Oracle (A := A) query)
    (requests : List (S × List M)) (cache : Cache (S × List M) (fun key => A (query key))) :
    (serve query oracle requests cache).2 ≤ allocationWork (requests.map Prod.snd) := by
  induction requests generalizing cache with
  | nil => simp [serve, allocationWork]
  | cons key rest ih =>
    have ha := allocate_fresh_le query oracle key.1 key.2 cache
    have hb := ih (allocate query oracle key.1 key.2 cache).cache
    simpa only [serve, allocationWork, List.map_cons, List.sum_cons, ancestors_length]
      using Nat.add_le_add ha hb

/-- Pointwise for arbitrary queried branches, including rejecting ones. Applied
to every leaf of an adaptive request tree, this is a deterministic stopping cap. -/
theorem serve_cap [DecidableEq S] [DecidableEq M]
    (query : S × List M → Q) (oracle : Oracle (A := A) query)
    (B K : Nat) (requests : List (S × List M)) (final : S × List M)
    (cache : Cache (S × List M) (fun key => A (query key)))
    (budget : requests.length ≤ K) (bounded : ∀ key ∈ requests, key.2.length ≤ B)
    (finalBound : final.2.length ≤ B) :
    (serve query oracle (requests ++ [final]) cache).2 ≤ B * (K+1) := by
  apply (serve_cost_le query oracle _ cache).trans
  simp only [List.map_append, List.map_cons, List.map_nil]
  apply allocation_cap B K (requests.map Prod.snd) final.2
  · simpa using budget
  · intro p hp
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hp
    exact bounded key hk
  · exact finalBound

end Ancestors

end Whir.TypedFiatShamirGame
