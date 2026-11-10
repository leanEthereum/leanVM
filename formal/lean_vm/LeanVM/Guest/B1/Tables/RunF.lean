/-
  LeanVM.Guest.B1.Tables.RunF

  The Spec's programs run on the carried sponge, and a run of a sequence split at its `bind`:
  what the completeness direction takes from an accepting run (`RunsTo`).
-/

module

public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Protocol.WithHash

/-!
# Runs on the carried sponge, split

`runT p st`: `Compile.run` (Keccak-256, Keccak-f) with the sponge replaced by the `Fs` the guest
carries and the ground challenge a grind leaves (`TCar`). It splits at a `bind` (`runT_bind`),
keeps any stream and openings past what it reads (`runT_frame`), and is the deployed run on every
sponge the state carries (`runT_of_runId`, `runId_of_runT`).

`RunsTo.unbindX`: an accepting run of `p >>= f` from a state some sponge carries is a run of `p`
on a prefix of the words, to a sponge carried with a ground challenge `g` (`RunsToX`), and of
`f a` on the rest from there (`RunsFromX`). `runsToX_det`: against a known run of `p`, `g` is
`none`; `RunsTo.unbind_at` splits so where a run of `p` is known.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The state of a carried run: the carried sponge, the ground challenge a grind left (the next
sample returns it), the words and openings left, the roots. -/
structure TSt where
  sponge : Fs
  ground : Option E
  stream : List E
  openings : List (List Opening)
  roots : List (Digest × ℕ × ℕ)

/-- The Spec's sponge `sp` is the one the guest carries as `s`, with the ground challenge `g`. -/
def TCar (s : Fs) (g : Option E) (sp : Sponge) : Prop :=
  capOf sp.state = s.cap ∧ sp.pending = s.pend ∧ sp.ground = g

theorem tcar_none {s : Fs} {sp : Sponge} : TCar s none sp ↔ s.Carries sp := Iff.rfl

/-- **A run on the carried sponge.** -/
def runT {α : Type} : VerifierProgram α → TSt → Option (α × TSt)
  | .ret a, s => some (a, s)
  | .fail, _ => none
  | .read k, s => match s.stream, s.ground with
    | x :: xs, none => runT (k x) { s with sponge := s.sponge.absorb x dsObserve, stream := xs }
    | _, _ => none
  | .sample k, s => match s.ground with
    | some c => runT (k c) { s with ground := none }
    | none => runT (k s.sponge.squeeze.1) { s with sponge := s.sponge.squeeze.2 }
  | .grind bits k, s => match s.stream, s.ground with
    | n :: xs, none =>
      if powOk bits (Keccak.lane (s.sponge.nonceState n) 2) then
        runT k { s with
          sponge := Fs.mk (capOf (s.sponge.nonceState n)) []
          ground := some (challengeOf (s.sponge.nonceState n))
          stream := xs }
      else none
    | _, _ => none
  | .commit height width k, s => match s.stream, s.ground with
    | x0 :: x1 :: xs, none =>
      runT k { s with
        sponge := (s.sponge.absorb x0 dsObserve).absorb x1 dsObserve
        stream := xs
        roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)] }
    | _, _ => none
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
      | some rows => runT (k rows) { s with openings := rest }
      | none => none
    | _, _ => none

theorem runT_bind {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) (st : TSt) :
    runT (p.bind f) st = (runT p st).bind (fun r ↦ runT (f r.1) r.2) := by
  induction p generalizing st with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    obtain ⟨s, g, _ | ⟨x, xs⟩, os, R⟩ := st
    · rfl
    · cases g
      · exact ih _ _
      · rfl
  | sample k ih =>
    obtain ⟨s, g, stream, os, R⟩ := st
    cases g
    · exact ih _ _
    · exact ih _ _
  | grind b k ih =>
    obtain ⟨s, g, _ | ⟨n, xs⟩, os, R⟩ := st
    · rfl
    · cases g
      · simp only [VerifierProgram.bind, runT]
        split
        · exact ih _
        · rfl
      · rfl
  | commit h w k ih =>
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, none => exact ih _
    | _ :: _ :: _, some _ => rfl
  | query i ps k ih =>
    simp only [VerifierProgram.bind, runT]
    split
    · split
      · exact ih _ _
      · rfl
    · rfl

/-- **A run keeps the words and openings it does not read.** -/
theorem runT_frame {α : Type} (p : VerifierProgram α) : ∀ (st : TSt) (a : α) (st' : TSt),
    runT p st = some (a, st') → ∃ pre opre, st.stream = pre ++ st'.stream ∧
      st.openings = opre ++ st'.openings ∧ ∀ zs orest,
        runT p { st with stream := pre ++ zs, openings := opre ++ orest } =
          some (a, { st' with stream := zs, openings := orest }) := by
  induction p with
  | ret b =>
    intro st a st' h
    simp only [runT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], rfl, rfl, fun zs orest => rfl⟩
  | fail => intro st a st' h; simp [runT] at h
  | read k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | x :: xs, none, h =>
      obtain ⟨pre, opre, h1, h2, hf⟩ := ih x _ a st' h
      refine ⟨x :: pre, opre, by simp only [List.cons_append] at h1 ⊢; rw [h1], h2,
        fun zs orest => ?_⟩
      exact hf zs orest
  | sample k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases g with
    | none =>
      obtain ⟨pre, opre, h1, h2, hf⟩ := ih _ _ a st' h
      exact ⟨pre, opre, h1, h2, fun zs orest => hf zs orest⟩
    | some c =>
      obtain ⟨pre, opre, h1, h2, hf⟩ := ih _ _ a st' h
      exact ⟨pre, opre, h1, h2, fun zs orest => hf zs orest⟩
  | grind b k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | n :: xs, none, h =>
      simp only [runT] at h
      split at h
      · rename_i hp
        obtain ⟨pre, opre, h1, h2, hf⟩ := ih _ a st' h
        refine ⟨n :: pre, opre, by simp only [List.cons_append] at h1 ⊢; rw [h1], h2,
          fun zs orest => ?_⟩
        simp only [runT, List.cons_append, hp, ↓reduceIte]
        exact hf zs orest
      · simp at h
  | commit hh ww k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | [_], _, h => simp [runT] at h
    | _ :: _ :: _, some _, h => simp [runT] at h
    | x0 :: x1 :: xs, none, h =>
      obtain ⟨pre, opre, h1, h2, hf⟩ := ih _ a st' h
      refine ⟨x0 :: x1 :: pre, opre, by simp only [List.cons_append] at h1 ⊢; rw [h1], h2,
        fun zs orest => ?_⟩
      exact hf zs orest
  | query i ps k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [runT, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runT, hR] at h
      | cons phase rest =>
        simp only [runT, hR] at h
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h
          obtain ⟨pre, opre, h1, h2, hf⟩ := ih rows _ a st' h
          refine ⟨pre, phase :: opre, h1, by simp only at h2 ⊢; rw [h2]; rfl, fun zs orest => ?_⟩
          simp only [runT, hR, List.cons_append, hop]
          exact hf zs orest

/-- The `Fs` a sponge's carrier is. -/
def fsOfT (sp : Sponge) : Fs := ⟨capOf sp.state, sp.pending⟩

theorem eq_fsOfT {s : Fs} {g : Option E} {sp : Sponge} (h : TCar s g sp) :
    s = fsOfT sp ∧ g = sp.ground := by
  obtain ⟨h1, h2, h3⟩ := h
  cases s
  simp only [fsOfT, Fs.mk.injEq]
  exact ⟨⟨h1.symm, h2.symm⟩, h3.symm⟩

/-- **The carried run is the deployed run** on every sponge the state carries. -/
theorem runId_of_runT {α : Type} (p : VerifierProgram α) : ∀ (st : TSt) (sp : Sponge),
    TCar st.sponge st.ground sp →
    ∀ (a : α) (st' : TSt), runT p st = some (a, st') →
      ∃ sp', TCar st'.sponge st'.ground sp' ∧
        runId p ⟨sp, st.stream, st.openings, st.roots⟩ =
          some (a, ⟨sp', st'.stream, st'.openings, st'.roots⟩) := by
  induction p with
  | ret b =>
    intro st sp hs a st' h
    simp only [runT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨sp, hs, rfl⟩
  | fail => intro st sp hs a st' h; simp [runT] at h
  | read k ih =>
    intro st sp hs a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | x :: xs, none, h =>
      obtain ⟨S, P, G⟩ := sp
      obtain ⟨h1, h2, h3⟩ := hs
      simp only at h1 h2 h3
      subst G
      exact ih x ⟨s.absorb x dsObserve, none, xs, os, R⟩ _
        (carries_absorb (s := s) (sp := ⟨S, P, none⟩) ⟨h1, h2, rfl⟩ x dsObserve) a st' h
  | sample k ih =>
    intro st sp hs a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    obtain ⟨S, P, G⟩ := sp
    obtain ⟨h1, h2, h3⟩ := hs
    simp only at h1 h2 h3
    subst G
    cases g with
    | some c =>
      exact ih c ⟨s, none, stream, os, R⟩ ⟨S, P, none⟩ ⟨h1, h2, rfl⟩ a st' h
    | none =>
      have hs' : s.Carries ⟨S, P, none⟩ := ⟨h1, h2, rfl⟩
      obtain ⟨e1, e2⟩ := carries_squeeze hs'
      obtain ⟨sp', c1, c2⟩ := ih (s.squeeze.1) ⟨s.squeeze.2, none, stream, os, R⟩ _ e2 a st' h
      refine ⟨sp', c1, ?_⟩
      show runId (k (Id.run (Compile.squeeze (m := Id) keccakF1600 ⟨S, P, none⟩)).1)
        ⟨(Id.run (Compile.squeeze (m := Id) keccakF1600 ⟨S, P, none⟩)).2, stream, os, R⟩ = _
      rw [e1]; exact c2
  | grind b k ih =>
    intro st sp hs a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | n :: xs, none, h =>
      simp only [runT] at h
      split at h
      · rename_i hp
        obtain ⟨sp', c1, c2⟩ := ih _ ⟨s.nonceState n, [], some (challengeOf (s.nonceState n))⟩
          ⟨rfl, rfl, rfl⟩ a st' h
        refine ⟨sp', c1, ?_⟩
        rw [run_grind_carried b k (s := s) hs n xs os R, ite_eq_left hp]
        exact c2
      · simp at h
  | commit hh ww k ih =>
    intro st sp hs a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | [_], _, h => simp [runT] at h
    | _ :: _ :: _, some _, h => simp [runT] at h
    | x0 :: x1 :: xs, none, h =>
      obtain ⟨S, P, G⟩ := sp
      obtain ⟨h1, h2, h3⟩ := hs
      simp only at h1 h2 h3
      subst G
      have c1 := carries_absorb (s := s) (sp := ⟨S, P, none⟩) ⟨h1, h2, rfl⟩ x0 dsObserve
      have c2 := carries_absorb c1 x1 dsObserve
      exact ih ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, os,
        R ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ _ c2 a st' h
  | query i ps k ih =>
    intro st sp hs a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [runT, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runT, hR] at h
      | cons phase rest =>
        simp only [runT, hR] at h
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h
          obtain ⟨sp', c1, c2⟩ := ih rows ⟨s, g, stream, rest, R⟩ sp hs a st' h
          refine ⟨sp', c1, ?_⟩
          simp only [Id.run] at hop
          simp only [runId, Compile.runWithHash, bind, hR, hop]
          exact c2

/-- **The deployed run is the carried run.** -/
theorem runT_of_runId {α : Type} (p : VerifierProgram α) : ∀ (st : TSt) (sp : Sponge),
    TCar st.sponge st.ground sp →
    ∀ (a : α) (t : VerifierProgramState), runId p ⟨sp, st.stream, st.openings, st.roots⟩ = some
        (a, t) →
      runT p st = some (a, ⟨fsOfT t.sponge, t.sponge.ground, t.stream, t.openings, t.roots⟩) := by
  induction p with
  | ret a =>
    intro st sp hs a' t h
    simp only [runId, Compile.runWithHash, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, e2⟩ := eq_fsOfT hs
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only at e1 e2
    subst e1 e2
    rfl
  | fail =>
    intro st sp hs a t h
    simp [runId, Compile.runWithHash, pure] at h
  | read k ih =>
    intro st sp hs a t h
    obtain ⟨s, g, stream, os, roots⟩ := st
    obtain ⟨S, P, G⟩ := sp
    obtain ⟨h1, h2, h3⟩ := hs
    simp only at h1 h2 h3
    subst G
    match stream, g, h with
    | [], _, h => simp [runId, Compile.runWithHash, pure] at h
    | _ :: _, some _, h => simp [runId, Compile.runWithHash, pure] at h
    | x :: xs, none, h =>
      exact ih x ⟨s.absorb x dsObserve, none, xs, os, roots⟩ _
        (carries_absorb (s := s) (sp := ⟨S, P, none⟩) ⟨h1, h2, rfl⟩ x dsObserve) a t h
  | sample k ih =>
    intro st sp hs a t h
    obtain ⟨s, g, stream, os, R⟩ := st
    obtain ⟨S, P, G⟩ := sp
    obtain ⟨h1, h2, h3⟩ := hs
    simp only at h1 h2 h3
    subst G
    cases g with
    | some c =>
      exact ih c ⟨s, none, stream, os, R⟩ ⟨S, P, none⟩ ⟨h1, h2, rfl⟩ a t h
    | none =>
      have hs' : s.Carries ⟨S, P, none⟩ := ⟨h1, h2, rfl⟩
      obtain ⟨e1, e2⟩ := carries_squeeze hs'
      have := ih ((Id.run (Compile.squeeze (m := Id) keccakF1600 ⟨S, P, none⟩)).1)
        ⟨s.squeeze.2, none, stream, os, R⟩ _ e2 a t h
      simpa [runT, e1] using this
  | grind b k ih =>
    intro st sp hs a t h
    obtain ⟨s, g, stream, os, roots⟩ := st
    obtain ⟨S, P, G⟩ := sp
    obtain ⟨h1, h2, h3⟩ := hs
    simp only at h1 h2 h3
    subst G
    match stream, g, h with
    | [], _, h => simp [runId, Compile.runWithHash, pure] at h
    | _ :: _, some _, h => simp [runId, Compile.runWithHash, pure] at h
    | n :: xs, none, h =>
      have hs' : s.Carries ⟨S, P, none⟩ := ⟨h1, h2, rfl⟩
      rw [run_grind_carried b k hs' n xs os roots] at h
      by_cases hp : powOk b (Keccak.lane (s.nonceState n) 2) = true
      · simp only [hp, ↓reduceIte] at h
        have e := ih ⟨Fs.mk (capOf (s.nonceState n)) [], some (challengeOf (s.nonceState n)), xs, os,
          roots⟩ ⟨s.nonceState n, [], some (challengeOf (s.nonceState n))⟩ ⟨rfl, rfl, rfl⟩ a t h
        show (if powOk b (Keccak.lane (s.nonceState n) 2) = true then
          runT k ⟨Fs.mk (capOf (s.nonceState n)) [], some (challengeOf (s.nonceState n)), xs, os,
            roots⟩ else none) = _
        simp only [hp, ↓reduceIte]
        exact e
      · simp [hp] at h
  | commit hh ww k ih =>
    intro st sp hs a t h
    obtain ⟨s, g, stream, os, roots⟩ := st
    obtain ⟨S, P, G⟩ := sp
    obtain ⟨h1, h2, h3⟩ := hs
    simp only at h1 h2 h3
    subst G
    match stream, g, h with
    | [], _, h => simp [runId, Compile.runWithHash, pure] at h
    | [_], _, h => simp [runId, Compile.runWithHash, pure] at h
    | _ :: _ :: _, some _, h => simp [runId, Compile.runWithHash, pure] at h
    | x0 :: x1 :: xs, none, h =>
      have c1 := carries_absorb (s := s) (sp := ⟨S, P, none⟩) ⟨h1, h2, rfl⟩ x0 dsObserve
      have c2 := carries_absorb c1 x1 dsObserve
      exact ih ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, os,
        roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ _ c2 a t h
  | query i ps k ih =>
    intro st sp hs a t h
    obtain ⟨s, g, stream, os, roots⟩ := st
    simp only [runId, Compile.runWithHash, bind] at h
    simp only [runT]
    cases hr : roots[i]? with
    | none => simp [hr, pure] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [hr, pure] at h
      | cons phase rest =>
        simp only [hr] at h ⊢
        cases ho : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none =>
          simp only [Id.run] at ho
          simp [ho, pure] at h
        | some rows =>
          simp only [Id.run] at ho
          simp only [ho] at h
          exact ih rows ⟨s, g, stream, rest, roots⟩ sp hs a t h

/-- The roots only grow. -/
theorem runT_roots {α : Type} (p : VerifierProgram α) : ∀ (st : TSt) (a : α) (st' : TSt),
    runT p st = some (a, st') → ∃ C, st'.roots = st.roots ++ C := by
  induction p with
  | ret b =>
    intro st a st' h
    simp only [runT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp⟩
  | fail => intro st a st' h; simp [runT] at h
  | read k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | x :: xs, none, h => exact ih x ⟨s.absorb x dsObserve, none, xs, os, R⟩ a st' h
  | sample k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases g with
    | none => exact ih _ ⟨s.squeeze.2, none, stream, os, R⟩ a st' h
    | some c => exact ih c ⟨s, none, stream, os, R⟩ a st' h
  | grind b k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | n :: xs, none, h =>
      simp only [runT] at h
      split at h
      · exact ih ⟨Fs.mk (capOf (s.nonceState n)) [], some (challengeOf (s.nonceState n)), xs, os, R⟩ a st' h
      · simp at h
  | commit hh ww k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | [_], _, h => simp [runT] at h
    | _ :: _ :: _, some _, h => simp [runT] at h
    | x0 :: x1 :: xs, none, h =>
      obtain ⟨C, hC⟩ := ih ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, os, R ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ a st' h
      exact ⟨[(digestFromHalves (x0, x1), hh, ww)] ++ C, by
        simp only at hC ⊢; rw [hC, List.append_assoc]⟩
  | query i ps k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [runT, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runT, hR] at h
      | cons phase rest =>
        simp only [runT, hR] at h
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h
          exact ih rows ⟨s, g, stream, rest, R⟩ a st' h

/-- A run from no roots to no roots runs from any roots. -/
theorem runT_noRoots {α : Type} (p : VerifierProgram α) : ∀ (st : TSt) (a : α) (st' : TSt),
    st.roots = [] → st'.roots = [] → runT p st = some (a, st') →
      ∀ R, runT p { st with roots := R } = some (a, { st' with roots := R }) := by
  induction p with
  | ret b =>
    intro st a st' h0 h1 h R
    simp only [runT, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | fail => intro st a st' _ _ h; simp [runT] at h
  | read k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, g, stream, os, R0⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | x :: xs, none, h => exact ih x ⟨s.absorb x dsObserve, none, xs, os, R0⟩ a st' h0 h1 h R
  | sample k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, g, stream, os, R0⟩ := st
    cases g with
    | none => exact ih _ ⟨s.squeeze.2, none, stream, os, R0⟩ a st' h0 h1 h R
    | some c => exact ih c ⟨s, none, stream, os, R0⟩ a st' h0 h1 h R
  | grind b k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, g, stream, os, R0⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | _ :: _, some _, h => simp [runT] at h
    | n :: xs, none, h =>
      simp only [runT] at h ⊢
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih ⟨Fs.mk (capOf (s.nonceState n)) [], some (challengeOf (s.nonceState n)), xs, os, R0⟩ a st' h0 h1 h R
      · simp at h
  | commit hh ww k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, g, stream, os, R0⟩ := st
    match stream, g, h with
    | [], _, h => simp [runT] at h
    | [_], _, h => simp [runT] at h
    | _ :: _ :: _, some _, h => simp [runT] at h
    | x0 :: x1 :: xs, none, h =>
      have h' : runT k ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, os,
          R0 ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ = some (a, st') := h
      obtain ⟨C, hC⟩ := runT_roots _ _ a st' h'
      simp only at h0 hC
      rw [h1, h0] at hC
      simp at hC
  | query i ps k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, g, stream, os, R0⟩ := st
    simp only at h0
    subst h0
    simp [runT] at h

/-- `RunsTo` from a carried sponge to a sponge carried with the ground challenge `g`. -/
def RunsToX {α : Type} (p : VerifierProgram α) (s : Fs) (xs : List E) (a : α) (s' : Fs)
    (g : Option E) : Prop :=
  ∀ sp : Sponge, s.Carries sp → ∀ (rest : List E) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)), ∃ sp' : Sponge, TCar s' g sp' ∧
      runId p ⟨sp, xs ++ rest, os, roots⟩ = some (a, ⟨sp', rest, os, roots⟩)

/-- `RunsTo` from a sponge carried with the ground challenge `g`. -/
def RunsFromX {α : Type} (p : VerifierProgram α) (s : Fs) (g : Option E) (xs : List E) (a : α)
    (s' : Fs) : Prop :=
  ∀ sp : Sponge, TCar s g sp → ∀ (rest : List E) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)), ∃ sp' : Sponge, s'.Carries sp' ∧
      runId p ⟨sp, xs ++ rest, os, roots⟩ = some (a, ⟨sp', rest, os, roots⟩)

theorem RunsToX.toRunsTo {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsToX p s xs a s' none) : RunsTo p s xs a s' := h

theorem RunsFromX.toRunsTo {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsFromX p s none xs a s') : RunsTo p s xs a s' := h

/-- The sponge after a run from a carried one is carried. -/
theorem RunsTo.carries {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') (hc : ∃ sp, s.Carries sp) : ∃ sp, s'.Carries sp := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp', hc', -⟩ := h sp hsp [] [] []
  exact ⟨sp', hc'⟩

/-- **An accepting run of a sequence splits**, at a sponge carried with a ground challenge `g`
(`none` unless `p` ends right after a grind). -/
theorem RunsTo.unbindX {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {s s'' : Fs} {xs : List E} {b : β}
    (h : RunsTo (p >>= f) s xs b s'') (hc : ∃ sp, s.Carries sp) :
    ∃ (a : α) (xs1 xs2 : List E) (s1 : Fs) (g : Option E), xs = xs1 ++ xs2 ∧
      RunsToX p s xs1 a s1 g ∧ RunsFromX (f a) s1 g xs2 b s'' := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp'', hc'', he⟩ := h sp hsp [] [] []
  simp only [List.append_nil] at he
  have hT := runT_of_runId (p >>= f) ⟨s, none, xs, [], []⟩ sp hsp b _ he
  rw [prog_bind_eq, runT_bind] at hT
  obtain ⟨⟨a, st1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp hT
  obtain ⟨C1, hC1⟩ := runT_roots _ _ a st1 h1
  obtain ⟨C2, hC2⟩ := runT_roots _ _ b _ h2
  simp only [List.nil_append] at hC1 hC2
  have hr1 : st1.roots = [] := by
    rw [hC1] at hC2 ⊢; exact (List.append_eq_nil_iff.mp hC2.symm).1
  obtain ⟨pre1, opre1, hs1, ho1, hf1⟩ := runT_frame p _ a st1 h1
  obtain ⟨pre2, opre2, hs2, ho2, hf2⟩ := runT_frame (f a) st1 b _ h2
  simp only at hs1 ho1 hs2 ho2
  have ho1' : opre1 = [] ∧ st1.openings = [] := List.append_eq_nil_iff.mp ho1.symm
  have ho2' : opre2 = [] := by rw [List.append_nil] at ho2; rw [← ho2, ho1'.2]
  rw [List.append_nil] at hs2
  have hg'' : sp''.ground = none := hc''.2.2
  refine ⟨a, pre1, st1.stream, st1.sponge, st1.ground, by rw [hs1], ?_, ?_⟩
  · intro sp0 hs0 rest os R
    have e := hf1 rest os
    rw [ho1'.1, List.nil_append] at e
    have e2 := runT_noRoots p _ a _ rfl (by simp [hr1]) e R
    obtain ⟨sp1, c1, c2⟩ := runId_of_runT p _ sp0 (by exact hs0) a _ e2
    exact ⟨sp1, c1, c2⟩
  · intro sp0 hs0 rest os R
    have e := hf2 rest os
    rw [ho2', List.nil_append, ← hs2] at e
    have e' : runT (f a) ⟨st1.sponge, st1.ground, st1.stream ++ rest, os, []⟩ =
        some (b, ⟨fsOfT sp'', sp''.ground, rest, os, []⟩) := by
      simp only [hr1] at e; exact e
    have e2 := runT_noRoots (f a) _ b _ rfl rfl e' R
    obtain ⟨sp1, c1, c2⟩ := runId_of_runT (f a) ⟨st1.sponge, st1.ground, st1.stream ++ rest, os, R⟩
      sp0 hs0 b ⟨fsOfT sp'', sp''.ground, rest, os, R⟩ e2
    refine ⟨sp1, ?_, c2⟩
    have e3 := (eq_fsOfT hc'').1
    rw [e3]
    simp only [hg''] at c1
    exact c1

/-- **Runs of one program from one sponge on one stream agree**, the first ending at a ground
challenge `g`: it is the second's, so `g = none`. -/
theorem runsToX_det {α : Type} {p : VerifierProgram α} {s t1 t2 : Fs} {g : Option E}
    {xs1 xs2 r1 r2 : List E} {a b : α}
    (h1 : RunsToX p s xs1 a t1 g) (h2 : RunsTo p s xs2 b t2) (hc : ∃ sp, s.Carries sp)
    (he : xs1 ++ r1 = xs2 ++ r2) : a = b ∧ t1 = t2 ∧ g = none ∧ r1 = r2 := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp1, c1, e1⟩ := h1 sp hsp r1 [] []
  obtain ⟨sp2, c2, e2⟩ := h2 sp hsp r2 [] []
  rw [he, e2] at e1
  simp only [Option.some.injEq, Prod.mk.injEq, VerifierProgramState.mk.injEq] at e1
  obtain ⟨rfl, rfl, rfl, -⟩ := e1
  obtain ⟨c1a, c1b, c1c⟩ := c1
  obtain ⟨c2a, c2b, c2c⟩ := c2
  refine ⟨rfl, ?_, c1c.symm.trans c2c, rfl⟩
  cases t1; cases t2
  simp only [Fs.mk.injEq]
  exact ⟨c1a.symm.trans c2a, c1b.symm.trans c2b⟩

/-- **An accepting run of a sequence splits** where a run of its first part is known. -/
theorem RunsTo.unbind_at {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {s s'' t : Fs} {xs ys : List E} {a : α} {b : β}
    (h : RunsTo (p >>= f) s xs b s'') (hc : ∃ sp, s.Carries sp) (hp : RunsTo p s ys a t)
    (hpre : ∃ r, xs = ys ++ r) : ∃ xs2, xs = ys ++ xs2 ∧ RunsTo (f a) t xs2 b s'' := by
  obtain ⟨a1, xs1, xs2, s1, g, he, r1, k1⟩ := RunsTo.unbindX h hc
  obtain ⟨r, hr⟩ := hpre
  obtain ⟨ea, es, eg, er⟩ := runsToX_det r1 hp hc (r1 := xs2) (r2 := r) (by rw [← he, hr])
  subst ea es eg er
  exact ⟨xs2, hr, k1.toRunsTo⟩

end
end LeanVM.Guest.B1.Tables
