import FORS.Reduction.NoRepeat
import FORS.Reduction.Internalize

section

/-! Adversaries that never request a signature on the same message twice stay so when their long
hash inputs are internalized. -/

open OracleComp OracleSpec

namespace FORS.Security.ForsPotential

variable [Params]

open Internalize Short

theorem noRepeat_map {α β : Type} (g : α → β) :
    ∀ (M : OracleComp AdvSpec α) (S : List Message), NoRepeat M S → NoRepeat (g <$> M) S := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a => intro S _; exact trivial
  | query_bind t next ih =>
      intro S h
      rw [map_bind]
      rcases t with t | m
      · exact fun v => ih v S (h v)
      · exact ⟨h.1, fun r => ih r _ (h.2 r)⟩

theorem noRepeat_liftWorld_bind {α β : Type} :
    ∀ (x : OracleComp OracleWorld α) (k : α → OracleComp AdvSpec β) (S : List Message),
      (∀ a, NoRepeat (k a) S) → NoRepeat (liftWorld x >>= k) S := by
  intro x
  induction x using OracleComp.inductionOn with
  | pure a =>
      intro k S h
      simp only [liftWorld, simulateQ_pure, pure_bind]
      exact h a
  | query_bind t next ih =>
      intro k S h
      simp only [liftWorld, simulateQ_bind, simulateQ_spec_query, bind_assoc]
      exact fun v => ih v k S h

theorem noRepeat_map_liftWorld_bind {α β γ : Type} (f : α → β) (x : OracleComp OracleWorld α)
    (k : β → OracleComp AdvSpec γ) (S : List Message) (h : ∀ a, NoRepeat (k (f a)) S) :
    NoRepeat ((f <$> liftWorld x) >>= k) S := by
  rw [bind_map_left]
  exact noRepeat_liftWorld_bind x _ S h

theorem noRepeat_internalize {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (S : List Message) (cache : QueryCache HashSpec),
      NoRepeat M S → NoRepeat ((simulateQ internalImpl M).run cache) S := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a =>
      intro S cache _
      simp only [simulateQ_pure, StateT.run_pure]
      exact trivial
  | query_bind t next ih =>
      intro S cache h
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rcases t with (draw | input) | m
      · change NoRepeat ((forward (.inl (.inl draw))).run cache >>= _) S
        simp only [forward, StateT.run, bind_map_left]
        exact fun v => ih v S cache (h v)
      · change NoRepeat ((if IsShort input then forward (.inl (.inr input)) else privateRead input).run cache >>= _) S
        split_ifs with hs
        · simp only [forward, StateT.run, bind_map_left]
          exact fun v => ih v S cache (h v)
        · simp only [privateRead, StateT.run]
          cases hc : cache input with
          | some answer =>
              exact ih answer S cache (h answer)
          | none =>
              exact noRepeat_map_liftWorld_bind _ _ _ S fun v => ih v S _ (h v)
      · change NoRepeat ((forward (.inr m)).run cache >>= _) S
        simp only [forward, StateT.run, bind_map_left]
        exact ⟨h.1, fun r => ih r _ cache (h.2 r)⟩

theorem noRepeat_internalize_adversary (adversary : Adversary) (h : adversary.NoRepeat) :
    (internalize adversary).NoRepeat := by
  intro pk
  exact noRepeat_map _ _ [] (noRepeat_internalize _ [] ∅ (h pk))

end FORS.Security.ForsPotential

end

section

/-! The memoizing adversary: it answers a repeated signing request from its own record of earlier
answers and forwards everything else unchanged. It never repeats a request, and memoizing
commutes with internalizing long hash inputs. -/

open OracleComp OracleSpec

namespace FORS.Security.Memo

variable [Params]

open Internalize Short ForsPotential

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The answers recorded so far, by message. -/
abbrev Record := Message → Option (Option Signature)

def emptyRecord : Record := fun _ => none

noncomputable def memoImpl : QueryImpl AdvSpec (StateT Record (OracleComp AdvSpec))
  | .inl t => fun record =>
      (fun answer => (answer, record)) <$> (liftM (AdvSpec.query (.inl t)) : OracleComp AdvSpec _)
  | .inr m => fun record =>
      match record m with
      | some signature => pure (signature, record)
      | none => (fun signature => (signature, Function.update record m (some signature))) <$>
          (liftM (AdvSpec.query (.inr m)) : OracleComp AdvSpec _)

/-- The adversary that answers repeated signing requests from its own record. -/
noncomputable def memoAdv (adversary : Adversary) : Adversary :=
  ⟨fun publicKey => (simulateQ memoImpl (adversary.main publicKey)).run' emptyRecord⟩

theorem memoImpl_world (t : OracleWorld.Domain) (record : Record) :
    (memoImpl (.inl t)).run record =
      (fun answer => (answer, record)) <$> (liftM (AdvSpec.query (.inl t)) : OracleComp AdvSpec _) := rfl

theorem memoImpl_sign_some (m : Message) (record : Record) (signature : Option Signature)
    (h : record m = some signature) :
    (memoImpl (.inr m)).run record = pure (signature, record) := by
  change (match record m with
      | some signature => pure (signature, record)
      | none => (fun signature => (signature, Function.update record m (some signature))) <$>
          (liftM (AdvSpec.query (.inr m)) : OracleComp AdvSpec _)) = _
  rw [h]

theorem memoImpl_sign_none (m : Message) (record : Record) (h : record m = none) :
    (memoImpl (.inr m)).run record =
      (fun signature => (signature, Function.update record m (some signature))) <$>
        (liftM (AdvSpec.query (.inr m)) : OracleComp AdvSpec _) := by
  change (match record m with
      | some signature => pure (signature, record)
      | none => (fun signature => (signature, Function.update record m (some signature))) <$>
          (liftM (AdvSpec.query (.inr m)) : OracleComp AdvSpec _)) = _
  rw [h]

theorem noRepeat_memo {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (record : Record) (S : List Message),
      (∀ m, m ∈ S ↔ (record m).isSome) → NoRepeat ((simulateQ memoImpl M).run record) S := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a => intro record S _; exact trivial
  | query_bind t next ih =>
      intro record S hinv
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rcases t with t | m
      · rw [memoImpl_world, bind_map_left]
        exact fun v => ih v record S hinv
      · cases hm : record m with
        | some signature =>
            rw [memoImpl_sign_some m record signature hm, pure_bind]
            exact ih signature record S hinv
        | none =>
            rw [memoImpl_sign_none m record hm, bind_map_left]
            refine ⟨fun hmem => ?_, fun r => ih r _ _ fun m' => ?_⟩
            · have := (hinv m).1 hmem
              rw [hm] at this
              exact absurd this (by simp)
            · rw [List.mem_append, List.mem_singleton, hinv m']
              by_cases heq : m' = m
              · subst heq
                simp
              · simp [heq]

/-- **The memoizing adversary never repeats a signing request.** -/
theorem memoAdv_noRepeat (adversary : Adversary) : (memoAdv adversary).NoRepeat := by
  intro pk
  change NoRepeat ((simulateQ memoImpl (adversary.main pk)).run' emptyRecord) []
  rw [StateT.run'_eq]
  exact noRepeat_map _ _ [] (noRepeat_memo _ emptyRecord [] (fun m => by simp [emptyRecord]))

/-! ### Memoizing commutes with internalizing -/

theorem memo_run_query_bind {β : Type} (t : AdvSpec.Domain) (k : AdvSpec.Range t → OracleComp AdvSpec β)
    (record : Record) :
    (simulateQ memoImpl ((liftM (AdvSpec.query t) : OracleComp AdvSpec _) >>= k)).run record =
      (memoImpl t).run record >>= fun p => (simulateQ memoImpl (k p.1)).run p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem internal_run_query_bind {β : Type} (t : AdvSpec.Domain) (k : AdvSpec.Range t → OracleComp AdvSpec β)
    (cache : QueryCache HashSpec) :
    (simulateQ internalImpl ((liftM (AdvSpec.query t) : OracleComp AdvSpec _) >>= k)).run cache =
      (internalImpl t).run cache >>= fun p => (simulateQ internalImpl (k p.1)).run p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem memo_liftWorld {α : Type} (x : OracleComp OracleWorld α) (record : Record) :
    (simulateQ memoImpl (liftWorld x)).run record = (fun a => (a, record)) <$> liftWorld x := by
  induction x using OracleComp.inductionOn with
  | pure a => simp [liftWorld]
  | query_bind t next ih =>
      have hlift : liftWorld ((liftM (OracleWorld.query t) : OracleComp OracleWorld _) >>= next) =
          (liftM (AdvSpec.query (.inl t)) : OracleComp AdvSpec _) >>= fun a => liftWorld (next a) := by
        rw [liftWorld, simulateQ_bind, simulateQ_spec_query]
        rfl
      rw [hlift, memo_run_query_bind, memoImpl_world, bind_map_left, map_bind]
      exact bind_congr fun v => ih v

theorem memo_privateRead (bytes : HashInput) (cache : QueryCache HashSpec) (record : Record) :
    (simulateQ memoImpl ((privateRead bytes).run cache)).run record =
      (fun p => (p, record)) <$> (privateRead bytes).run cache := by
  change (simulateQ memoImpl (privateRead bytes cache)).run record = _ <$> privateRead bytes cache
  unfold privateRead
  split
  · simp
  · rw [simulateQ_map, StateT.run_map, memo_liftWorld, Functor.map_map, Functor.map_map]

theorem internal_forward_run (t : AdvSpec.Domain) (h : internalImpl t = forward t)
    (cache : QueryCache HashSpec) :
    (internalImpl t).run cache =
      (fun a => (a, cache)) <$> (liftM (AdvSpec.query t) : OracleComp AdvSpec _) := by
  rw [h]
  rfl

theorem internal_memo_comm {α : Type} :
    ∀ (M : OracleComp AdvSpec α) (record : Record) (cache : QueryCache HashSpec),
      (simulateQ internalImpl ((simulateQ memoImpl M).run record)).run cache =
        (fun p => ((p.1.1, p.2), p.1.2)) <$>
          (simulateQ memoImpl ((simulateQ internalImpl M).run cache)).run record := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure a => intro record cache; simp
  | query_bind t next ih =>
      intro record cache
      rw [memo_run_query_bind, internal_run_query_bind]
      rcases t with (draw | bytes) | m
      · rw [memoImpl_world, bind_map_left, internal_run_query_bind,
          internal_forward_run _ rfl, bind_map_left, bind_map_left, simulateQ_bind, StateT.run_bind,
          simulateQ_spec_query, memoImpl_world, bind_map_left, map_bind]
        exact bind_congr fun v => ih v record cache
      · by_cases hshort : IsShort bytes
        · have hint : internalImpl (.inl (.inr bytes)) = forward (.inl (.inr bytes)) := by
            simp only [internalImpl, hshort, ↓reduceIte]
          rw [memoImpl_world, bind_map_left, internal_run_query_bind,
            internal_forward_run _ hint, bind_map_left, bind_map_left, simulateQ_bind, StateT.run_bind,
            simulateQ_spec_query, memoImpl_world, bind_map_left, map_bind]
          exact bind_congr fun v => ih v record cache
        · have hint : internalImpl (.inl (.inr bytes)) = privateRead bytes := by
            simp only [internalImpl, hshort, ↓reduceIte]
          rw [memoImpl_world, bind_map_left, internal_run_query_bind, hint, simulateQ_bind,
            StateT.run_bind, memo_privateRead, bind_map_left, map_bind]
          exact bind_congr fun p => ih p.1 record p.2
      · rw [internal_forward_run _ rfl, bind_map_left]
        cases hm : record m with
        | some signature =>
            rw [memoImpl_sign_some m record signature hm, pure_bind, ih signature record cache,
              memo_run_query_bind, memoImpl_sign_some m record signature hm, pure_bind]
        | none =>
            rw [memoImpl_sign_none m record hm, bind_map_left, internal_run_query_bind,
              internal_forward_run _ rfl, bind_map_left, memo_run_query_bind,
              memoImpl_sign_none m record hm, bind_map_left, map_bind]
            exact bind_congr fun v => ih v _ cache

/-- Internalizing the memoizing adversary gives the memoizing adversary of the internalized one. -/
theorem internalize_memoAdv_main (adversary : Adversary) (pk : PublicKey) :
    (internalize (memoAdv adversary)).main pk = (memoAdv (internalize adversary)).main pk := by
  change (simulateQ internalImpl ((simulateQ memoImpl (adversary.main pk)).run' emptyRecord)).run' ∅ =
    (simulateQ memoImpl ((simulateQ internalImpl (adversary.main pk)).run' ∅)).run' emptyRecord
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, internal_memo_comm, Functor.map_map]

theorem internalize_memoAdv (adversary : Adversary) :
    internalize (memoAdv adversary) = memoAdv (internalize adversary) := by
  cases h : internalize (memoAdv adversary) with
  | mk main =>
      cases h' : memoAdv (internalize adversary) with
      | mk main' =>
          congr 1
          funext pk
          have := internalize_memoAdv_main adversary pk
          rw [h, h'] at this
          exact this

end FORS.Security.Memo

end
