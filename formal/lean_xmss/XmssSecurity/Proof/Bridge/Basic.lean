import XmssSecurity.Proof.Deterministic.Preparation

/-!
# Deterministic executions, query counts and query domains

Generic facts about oracle computations under a cache: a computation every query of which the cache
answers (`Resolves`), one that makes the same number of queries on every path (`QueryCount`), and one
that queries only inputs of a given set (`OnlyQueries`).
-/

open OracleComp OracleSpec

namespace DeterministicSigning

set_option backward.isDefEq.respectTransparency false

variable {D R : Type}

/-- The first query of a computation and its continuation. -/
def headQuery {α : Type} : OracleComp (D →ₒ R) α → Option (D × (R → OracleComp (D →ₒ R) α))
  | .pure _ => none
  | .liftBind x k => some (x, k)

theorem query_bind_inj {α : Type} {x y : D} {f g : R → OracleComp (D →ₒ R) α}
    (h : (liftM ((D →ₒ R).query x) >>= f : OracleComp (D →ₒ R) α) = liftM ((D →ₒ R).query y) >>= g) :
    x = y ∧ f = g := by
  have := congrArg headQuery h
  change some (x, f) = some (y, g) at this
  simpa using this

theorem query_bind_ne_pure {α : Type} {x : D} {f : R → OracleComp (D →ₒ R) α} {a : α} :
    (liftM ((D →ₒ R).query x) >>= f : OracleComp (D →ₒ R) α) ≠ Pure.pure a := by
  intro h
  have := congrArg headQuery h
  exact Option.some_ne_none _ this

theorem Resolves.query_inv {α : Type} {cache : QueryCache (D →ₒ R)} {x : D}
    {next : R → OracleComp (D →ₒ R) α} {v : α}
    (h : Resolves cache (liftM ((D →ₒ R).query x) >>= next) v) :
    ∃ a, cache x = some a ∧ Resolves cache (next a) v := by
  generalize hc : (liftM ((D →ₒ R).query x) >>= next : OracleComp (D →ₒ R) α) = c at h
  cases h with
  | pure value => exact absurd hc query_bind_ne_pure
  | query input answer hanswer next' value tail =>
      obtain ⟨rfl, rfl⟩ := query_bind_inj hc
      exact ⟨answer, hanswer, tail⟩

theorem Resolves.pure_inv {α : Type} {cache : QueryCache (D →ₒ R)} {a v : α}
    (h : Resolves cache (Pure.pure a : OracleComp (D →ₒ R) α) v) : a = v := by
  generalize hc : (Pure.pure a : OracleComp (D →ₒ R) α) = c at h
  cases h with
  | pure value => exact (OracleComp.pure_inj _ _).1 hc
  | query input answer hanswer next' value tail => exact absurd hc.symm query_bind_ne_pure

theorem Resolves.bind {α β : Type} {cache : QueryCache (D →ₒ R)} {c : OracleComp (D →ₒ R) α}
    {f : α → OracleComp (D →ₒ R) β} {a : α} {v : β} (hc : Resolves cache c a)
    (hf : Resolves cache (f a) v) : Resolves cache (c >>= f) v := by
  induction hc with
  | pure value => simpa only [pure_bind] using hf
  | query input answer hanswer next value _ ih =>
      rw [bind_assoc]
      exact .query input answer hanswer _ v (ih hf)

theorem Resolves.of_bind {α β : Type} {cache : QueryCache (D →ₒ R)} {c : OracleComp (D →ₒ R) α}
    {f : α → OracleComp (D →ₒ R) β} {v : β} (h : Resolves cache (c >>= f) v) :
    ∃ a, Resolves cache c a ∧ Resolves cache (f a) v := by
  induction c using OracleComp.inductionOn generalizing v with
  | pure a => exact ⟨a, .pure a, by simpa only [pure_bind] using h⟩
  | query_bind x next ih =>
      rw [bind_assoc] at h
      obtain ⟨answer, hx, htail⟩ := h.query_inv
      obtain ⟨a, h1, h2⟩ := ih answer htail
      exact ⟨a, .query x answer hx next a h1, h2⟩

theorem Resolves.unique {α : Type} {cache : QueryCache (D →ₒ R)} {c : OracleComp (D →ₒ R) α}
    {v w : α} (h1 : Resolves cache c v) (h2 : Resolves cache c w) : v = w := by
  induction h1 with
  | pure value => exact h2.pure_inv
  | query input answer hanswer next value _ ih =>
      obtain ⟨answer', hx, htail⟩ := h2.query_inv
      rw [hanswer, Option.some.injEq] at hx
      subst answer'
      exact ih htail

theorem Resolves.map {α β : Type} {cache : QueryCache (D →ₒ R)} {c : OracleComp (D →ₒ R) α}
    {v : α} (h : Resolves cache c v) (g : α → β) : Resolves cache (g <$> c) (g v) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind (.pure _)

theorem Resolves.of_map {α β : Type} {cache : QueryCache (D →ₒ R)} {c : OracleComp (D →ₒ R) α}
    {g : α → β} {w : β} (h : Resolves cache (g <$> c) w) : ∃ v, Resolves cache c v ∧ g v = w := by
  rw [map_eq_bind_pure_comp] at h
  obtain ⟨v, hv, hw⟩ := h.of_bind
  exact ⟨v, hv, hw.pure_inv⟩

theorem Resolves.sequenceFin {α : Type} {cache : QueryCache (D →ₒ R)} {n : Nat}
    {c : Fin n → OracleComp (D →ₒ R) α} {v : Fin n → α} (h : ∀ i, Resolves cache (c i) (v i)) :
    Resolves cache (XmssSecurity.Concrete.sequenceFin c) v := by
  induction n with
  | zero =>
      have hv : v = Fin.elim0 := funext fun i => i.elim0
      subst hv
      exact .pure _
  | succ n ih =>
      simp only [XmssSecurity.Concrete.sequenceFin]
      refine (h 0).bind ((ih (fun i => h i.succ)).bind ?_)
      have hv : (Fin.cases (v 0) fun i => v i.succ : Fin (n + 1) → α) = v := by
        funext i
        cases i using Fin.cases <;> rfl
      rw [hv]
      exact .pure _

theorem Resolves.of_sequenceFin {α : Type} {cache : QueryCache (D →ₒ R)} {n : Nat}
    {c : Fin n → OracleComp (D →ₒ R) α} {v : Fin n → α}
    (h : Resolves cache (XmssSecurity.Concrete.sequenceFin c) v) : ∀ i, Resolves cache (c i) (v i) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
      simp only [XmssSecurity.Concrete.sequenceFin] at h
      obtain ⟨head, hhead, h⟩ := h.of_bind
      obtain ⟨tail, htail, h⟩ := h.of_bind
      have hv := h.pure_inv
      intro i
      cases i using Fin.cases with
      | zero => rw [← hv]; exact hhead
      | succ i => rw [← hv]; exact ih htail i

theorem eval_liftM_query (f : QueryImpl (D →ₒ R) Id) (x : D) :
    evalWithAnswerFn f (liftM ((D →ₒ R).query x) : OracleComp (D →ₒ R) R) = f x :=
  evalWithAnswerFn_query f x

/-- A resolved computation evaluates to its value under any answer function that agrees with the
cache. -/
theorem Resolves.eval {α : Type} {cache : QueryCache (D →ₒ R)} {c : OracleComp (D →ₒ R) α}
    {v : α} (h : Resolves cache c v) (f : QueryImpl (D →ₒ R) Id)
    (hf : ∀ x a, cache x = some a → f x = a) : evalWithAnswerFn f c = v := by
  induction h with
  | pure value => rfl
  | query input answer hanswer next value _ ih =>
      rw [evalWithAnswerFn_bind, eval_liftM_query, hf input answer hanswer]
      exact ih

end DeterministicSigning

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

variable {D R : Type}

theorem Erases.mono {α : Type} {known known' : QueryCache (D →ₒ R)}
    {left right : OracleComp (D →ₒ R) α} (h : Erases known left right) (hle : known ≤ known') :
    Erases known' left right := by
  induction h with
  | pure value => exact .pure value
  | query input left right _ ih => exact .query input left right ih
  | skip input answer hknown next right _ ih => exact .skip input answer (hle hknown) next right ih
  | cached input answer hknown left right _ ih => exact .cached input answer (hle hknown) left right ih
  | trans _ _ first second => exact .trans first second

/-- An erasure of known queries resolves wherever its result resolves. -/
theorem Erases.resolves {α : Type} {known cache : QueryCache (D →ₒ R)}
    {left right : OracleComp (D →ₒ R) α} (h : Erases known left right) (hle : known ≤ cache)
    {v : α} (hr : Resolves cache right v) : Resolves cache left v := by
  induction h generalizing v with
  | pure value => exact hr
  | query input left right _ ih =>
      obtain ⟨answer, hx, htail⟩ := hr.query_inv
      exact .query input answer hx left v (ih answer htail)
  | skip input answer hknown next right _ ih =>
      exact .query input answer (hle hknown) next v (ih hr)
  | cached input answer hknown left right _ ih =>
      obtain ⟨answer', hx, htail⟩ := hr.query_inv
      rw [hle hknown, Option.some.injEq] at hx
      subst answer'
      exact .query input answer (hle hknown) left v (ih htail)
  | trans _ _ first second => exact first (second hr)

theorem Erases.sequenceFin {α : Type} {known : QueryCache (D →ₒ R)} {n : Nat}
    {left right : Fin n → OracleComp (D →ₒ R) α} (h : ∀ i, Erases known (left i) (right i)) :
    Erases known (Concrete.sequenceFin left) (Concrete.sequenceFin right) := by
  induction n with
  | zero => exact .pure _
  | succ n ih =>
      simp only [Concrete.sequenceFin]
      exact (h 0).bind _ _ fun head =>
        (ih fun i => h i.succ).bind _ _ fun tail => .pure _

end XmssSecurity.Seeded

namespace XmssSecurity.Bridge

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-! ## Exact query counts -/

section QueryCount

variable {ι : Type} {spec : OracleSpec ι}

/-- Every path of the computation makes exactly `n` queries. -/
inductive QueryCount {α : Type} : OracleComp spec α → Nat → Prop
  | pure (a : α) : QueryCount (pure a) 0
  | query (x : spec.Domain) (next : spec.Range x → OracleComp spec α) (n : Nat)
      (h : ∀ a, QueryCount (next a) n) : QueryCount (liftM (spec.query x) >>= next) (n + 1)

theorem QueryCount.bind {α β : Type} {c : OracleComp spec α} {n m : Nat}
    (hc : QueryCount c n) {f : α → OracleComp spec β} (hf : ∀ a, QueryCount (f a) m) :
    QueryCount (c >>= f) (n + m) := by
  induction hc with
  | pure a => simpa only [pure_bind, Nat.zero_add] using hf a
  | query x next n _ ih =>
      rw [bind_assoc, show n + 1 + m = n + m + 1 by omega]
      exact .query x _ _ ih

theorem QueryCount.map {α β : Type} {c : OracleComp spec α} {n : Nat} (hc : QueryCount c n)
    (g : α → β) : QueryCount (g <$> c) n := by
  rw [map_eq_bind_pure_comp]
  have h := hc.bind (f := Pure.pure ∘ g) fun a => QueryCount.pure (g a)
  rwa [Nat.add_zero] at h

theorem QueryCount.sequenceFin {α : Type} {k n : Nat} {c : Fin k → OracleComp spec α}
    (h : ∀ i, QueryCount (c i) n) : QueryCount (Concrete.sequenceFin c) (k * n) := by
  induction k with
  | zero =>
      simp only [Concrete.sequenceFin, Nat.zero_mul]
      exact .pure _
  | succ k ih =>
      simp only [Concrete.sequenceFin]
      have h' := (h 0).bind fun head => (ih fun i => h i.succ).bind
        (f := fun tail => (Pure.pure (Fin.cases head tail) : OracleComp spec (Fin (k + 1) → α)))
        fun tail => QueryCount.pure _
      have hn : n + (k * n + 0) = (k + 1) * n := by rw [Nat.add_zero, Nat.succ_mul, Nat.add_comm]
      exact hn ▸ h'

end QueryCount

/-- A resolved computation with an exact count runs, counted and lifted, to its value without
touching the cache. -/
theorem run_countHashQueries_lift_of_resolves {α : Type} {c : OracleComp HashSpec α} {n : Nat}
    (hcount : QueryCount c n) {cache : QueryCache HashSpec} {v : α} (hres : Resolves cache c v) :
    (simulateQ romImpl (countHashQueries (liftM c : OracleComp OracleWorld α))).run cache =
      pure ((v, n), cache) := by
  induction hcount generalizing v with
  | pure a =>
      rw [hres.pure_inv]
      rfl
  | query x next m h ih =>
      obtain ⟨answer, hanswer, htail⟩ := hres.query_inv
      rw [liftM_bind]
      change (simulateQ romImpl (countHashQueries
        (liftM (OracleWorld.query (.inr x)) >>= _))).run cache = _
      rw [countHashQueries_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind]
      change ((randomOracle (spec := HashSpec) x).run cache >>= _) = _
      rw [QueryImpl.withCaching_run_some _ hanswer, pure_bind, ih answer htail]
      simp only [pure_bind, StateT.run_pure]
      congr 2
      change (v, 1 + m) = (v, m + 1)
      rw [Nat.add_comm]

/-! ## Query domains -/

section OnlyQueries

variable {D R : Type}

/-- Every query of the computation, on every path, lies in `S`. -/
inductive OnlyQueries (S : D → Prop) {α : Type} : OracleComp (D →ₒ R) α → Prop
  | pure (a : α) : OnlyQueries S (pure a)
  | query (x : D) (hx : S x) (next : R → OracleComp (D →ₒ R) α)
      (h : ∀ a, OnlyQueries S (next a)) : OnlyQueries S (liftM ((D →ₒ R).query x) >>= next)

variable {S : D → Prop}

theorem OnlyQueries.bind {α β : Type} {c : OracleComp (D →ₒ R) α} (hc : OnlyQueries S c)
    {f : α → OracleComp (D →ₒ R) β} (hf : ∀ a, OnlyQueries S (f a)) : OnlyQueries S (c >>= f) := by
  induction hc with
  | pure a => simpa only [pure_bind] using hf a
  | query x hx next _ ih =>
      rw [bind_assoc]
      exact .query x hx _ ih

theorem OnlyQueries.map {α β : Type} {c : OracleComp (D →ₒ R) α} (hc : OnlyQueries S c)
    (g : α → β) : OnlyQueries S (g <$> c) := by
  rw [map_eq_bind_pure_comp]
  exact hc.bind fun a => .pure (g a)

theorem OnlyQueries.sequenceFin {α : Type} {n : Nat} {c : Fin n → OracleComp (D →ₒ R) α}
    (h : ∀ i, OnlyQueries S (c i)) : OnlyQueries S (Concrete.sequenceFin c) := by
  induction n with
  | zero => exact .pure _
  | succ n ih =>
      simp only [Concrete.sequenceFin]
      exact (h 0).bind fun _ => (ih fun i => h i.succ).bind fun _ => .pure _

theorem OnlyQueries.withQueryLog {α : Type} {c : OracleComp (D →ₒ R) α} (hc : OnlyQueries S c) :
    OnlyQueries S c.withQueryLog := by
  induction hc with
  | pure a => exact .pure _
  | query x hx next _ ih =>
      change OnlyQueries S (simulateQ loggingOracle (liftM ((D →ₒ R).query x) >>= next)).run
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind]
      exact .query x hx _ fun a => (ih a).map _

theorem OnlyQueries.eval_congr {α : Type} {c : OracleComp (D →ₒ R) α} (hc : OnlyQueries S c)
    {f g : QueryImpl (D →ₒ R) Id} (hfg : ∀ x, S x → f x = g x) :
    evalWithAnswerFn f c = evalWithAnswerFn g c := by
  induction hc with
  | pure a => rfl
  | query x hx next _ ih =>
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, DeterministicSigning.eval_liftM_query,
        DeterministicSigning.eval_liftM_query, hfg x hx]
      exact ih _

theorem Resolves.congr {α : Type} {cache cache' : QueryCache (D →ₒ R)}
    {c : OracleComp (D →ₒ R) α} {v : α} (h : Resolves cache c v) (hc : OnlyQueries S c)
    (hagree : ∀ x, S x → cache' x = cache x) : Resolves cache' c v := by
  induction hc generalizing v with
  | pure a => rw [h.pure_inv]; exact .pure v
  | query x hx next _ ih =>
      obtain ⟨answer, hanswer, htail⟩ := h.query_inv
      exact .query x answer ((hagree x hx).trans hanswer) next v (ih answer htail)

/-- `E` laid over `C`: `E`'s entries, and `C`'s where `E` has none. -/
def overlay (E C : QueryCache (D →ₒ R)) : QueryCache (D →ₒ R) :=
  QueryCache.ofFn fun x => match E x with
    | some a => some a
    | none => C x

theorem overlay_of_none {E C : QueryCache (D →ₒ R)} {x : D} (hx : E x = none) :
    overlay E C x = C x := by
  simp [overlay, hx]

theorem overlay_empty (E : QueryCache (D →ₒ R)) : overlay E ∅ = E := by
  refine QueryCache.ext fun x => ?_
  cases h : E x <;> simp [overlay, h]

theorem overlay_cacheQuery [DecidableEq D] {E C : QueryCache (D →ₒ R)} {x : D} (hx : E x = none) (a : R) :
    (overlay E C).cacheQuery x a = overlay E (C.cacheQuery x a) := by
  refine QueryCache.ext fun y => ?_
  by_cases hy : y = x
  · subst y
    simp [overlay, hx]
  · rw [QueryCache.cacheQuery_of_ne _ _ hy]
    simp only [overlay]
    cases E y <;> simp [QueryCache.cacheQuery_of_ne _ _ hy]

variable [SampleableType R]

/-- A computation that never queries `E`'s inputs runs over `E` laid on a cache as it runs on the
cache, with `E` laid over the result. -/
theorem OnlyQueries.run_overlay [DecidableEq D] {α : Type} {c : OracleComp (D →ₒ R) α} (hc : OnlyQueries S c)
    {E : QueryCache (D →ₒ R)} (hE : ∀ x, S x → E x = none) (C : QueryCache (D →ₒ R)) :
    (simulateQ randomOracle c).run (overlay E C) =
      (fun p => (p.1, overlay E p.2)) <$> (simulateQ randomOracle c).run C := by
  induction hc generalizing C with
  | pure a => simp
  | query x hx next _ ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      cases hC : C x with
      | none =>
          rw [QueryImpl.withCaching_run_none _ (by rw [overlay_of_none (hE x hx), hC]),
            QueryImpl.withCaching_run_none _ hC, bind_map_left, bind_map_left]
          apply bind_congr
          intro a
          rw [overlay_cacheQuery (hE x hx), ih a]
      | some a =>
          rw [QueryImpl.withCaching_run_some _ (by rw [overlay_of_none (hE x hx), hC]),
            QueryImpl.withCaching_run_some _ hC, pure_bind, pure_bind, ih a]

end OnlyQueries

/-! ## Logged runs -/

theorem randomOracle_run_cache_eq (input : HashInput) (initial middle : QueryCache HashSpec)
    (output : HashOutput)
    (hmem : (output, middle) ∈ support ((randomOracle (spec := HashSpec) input).run initial)) :
    middle = initial.cacheQuery input output := by
  cases hcached : initial input with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcached, support_map, Set.mem_image] at hmem
      obtain ⟨sampled, _, heq⟩ := hmem
      cases heq
      rfl
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcached, support_pure, Set.mem_singleton_iff] at hmem
      cases hmem
      refine QueryCache.ext fun candidate => ?_
      by_cases heq : candidate = input
      · subst candidate
        rw [QueryCache.cacheQuery_self, hcached]
      · rw [QueryCache.cacheQuery_of_ne _ _ heq]

/-- The cache after a logged run is the initial cache extended by the log. -/
theorem withQueryLog_finalCache {α : Type} (computation : OracleComp HashSpec α)
    (initial : QueryCache HashSpec) (result : (α × QueryLog HashSpec) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ randomOracle computation.withQueryLog).run initial)) :
    result.2 = extendHashCacheWithLog initial result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing initial result with
  | pure value =>
      simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      rfl
  | query_bind input next ih =>
      change result ∈ support ((simulateQ randomOracle
        ((simulateQ loggingOracle (liftM (OracleSpec.query input) >>= next)).run)).run initial) at hmem
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middle⟩, hquery, hrest⟩ := hmem
      rw [simulateQ_map, StateT.run_map, support_map] at hrest
      obtain ⟨continuation, hcontinuation, rfl⟩ := hrest
      rw [extendHashCacheWithLog, ← randomOracle_run_cache_eq input initial middle output
        (by simpa only [simulateQ_spec_query] using hquery)]
      exact ih output middle continuation hcontinuation

theorem withQueryLog_run_forget {α : Type} (computation : OracleComp HashSpec α)
    (initial : QueryCache HashSpec) :
    (fun result : (α × QueryLog HashSpec) × QueryCache HashSpec => (result.1.1, result.2)) <$>
        (simulateQ randomOracle computation.withQueryLog).run initial =
      (simulateQ randomOracle computation).run initial := by
  rw [← StateT.run_map, ← simulateQ_map,
    show Prod.fst <$> computation.withQueryLog = computation from
      loggingOracle.fst_map_run_simulateQ computation]

/-- A log's entries at an input do not depend on the cache it extends. -/
theorem extendHashCacheWithLog_congr (log : QueryLog HashSpec) {left right : QueryCache HashSpec}
    {x : HashInput} (h : left x = right x) :
    extendHashCacheWithLog left log x = extendHashCacheWithLog right log x := by
  induction log generalizing left right with
  | nil => exact h
  | cons entry log ih =>
      apply ih
      by_cases hx : x = entry.1
      · subst x
        simp
      · simp [QueryCache.cacheQuery_of_ne _ _ hx, h]

end XmssSecurity.Bridge
