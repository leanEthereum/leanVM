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
carries (B1-b's `Whir.runF`, here for B1-c). It splits at a `bind` (`runT_bind`), keeps any
stream and openings past what it reads (`runT_frame`), and is the deployed run on every sponge
the state carries (`runT_of_runId`, `runId_of_runT`).

`RunsTo.unbind`: an accepting run of `p >>= f` from a state some sponge carries is a run of `p`
on a prefix of the words and of `f a` on the rest.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The state of a carried run: the carried sponge, the words and openings left, the roots. -/
structure TSt where
  sponge : Fs
  stream : List E
  openings : List (List Opening)
  roots : List (Digest × ℕ × ℕ)

/-- **A run on the carried sponge.** -/
def runT {α : Type} : VerifierProgram α → TSt → Option (α × TSt)
  | .ret a, s => some (a, s)
  | .fail, _ => none
  | .read k, s => match s.stream with
    | [] => none
    | x :: xs => runT (k x) { s with sponge := s.sponge.absorb x dsObserve, stream := xs }
  | .sample k, s => runT (k s.sponge.squeeze.1) { s with sponge := s.sponge.squeeze.2 }
  | .grind bits k, s => match s.stream with
    | [] => none
    | n :: xs =>
      let sq := (s.sponge.absorb n dsPowNonce).squeeze
      if powOk bits sq.1 then runT k { s with sponge := sq.2, stream := xs } else none
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs =>
      match digestFromHalves (x0, x1) with
      | some root =>
        runT k { s with
          sponge := (s.sponge.absorb x0 dsObserve).absorb x1 dsObserve
          stream := xs
          roots := s.roots ++ [(root, height, width)] }
      | none => none
    | _ => none
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
    simp only [VerifierProgram.bind, runT]
    split
    · rfl
    · exact ih _ _
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [VerifierProgram.bind, runT]
    split
    · rfl
    · split
      · exact ih _
      · rfl
  | commit h w k ih =>
    simp only [VerifierProgram.bind, runT]
    split
    · split
      · exact ih _
      · rfl
    · rfl
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
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => simp [runT] at h
    | cons x xs =>
      obtain ⟨pre, opre, h1, h2, hf⟩ := ih x _ a st' h
      refine ⟨x :: pre, opre, by simp only [List.cons_append] at h1 ⊢; rw [h1], h2,
        fun zs orest => ?_⟩
      exact hf zs orest
  | sample k ih =>
    intro st a st' h
    obtain ⟨pre, opre, h1, h2, hf⟩ := ih _ _ a st' h
    exact ⟨pre, opre, h1, h2, fun zs orest => hf zs orest⟩
  | grind b k ih =>
    intro st a st' h
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => simp [runT] at h
    | cons n xs =>
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
    obtain ⟨s, stream, os, R⟩ := st
    match stream, h with
    | [], h => simp [runT] at h
    | [_], h => simp [runT] at h
    | x0 :: x1 :: xs, h =>
      simp only [runT] at h
      split at h
      · rename_i root hr
        obtain ⟨pre, opre, h1, h2, hf⟩ := ih _ a st' h
        refine ⟨x0 :: x1 :: pre, opre, by simp only [List.cons_append] at h1 ⊢; rw [h1], h2,
          fun zs orest => ?_⟩
        simp only [runT, List.cons_append, hr]
        exact hf zs orest
      · simp at h
  | query i ps k ih =>
    intro st a st' h
    obtain ⟨s, stream, os, R⟩ := st
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

theorem eq_fsOfT {s : Fs} {sp : Sponge} (h : s.Carries sp) : s = fsOfT sp := by
  obtain ⟨h1, h2⟩ := h
  cases s
  simp only [fsOfT, Fs.mk.injEq]
  exact ⟨h1.symm, h2.symm⟩

/-- **The carried run is the deployed run** on every sponge the state carries. -/
theorem runId_of_runT {α : Type} (p : VerifierProgram α) : ∀ (st : TSt) (sp : Sponge),
    st.sponge.Carries sp →
    ∀ (a : α) (st' : TSt), runT p st = some (a, st') →
      ∃ sp', st'.sponge.Carries sp' ∧
        runId p ⟨sp, st.stream, st.openings, st.roots⟩ = some (a, ⟨sp', st'.stream, st'.openings, st'.roots⟩) := by
  induction p with
  | ret b =>
    intro st sp hs a st' h
    simp only [runT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨sp, hs, rfl⟩
  | fail => intro st sp hs a st' h; simp [runT] at h
  | read k ih =>
    intro st sp hs a st' h
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => simp [runT] at h
    | cons x xs =>
      exact ih x ⟨s.absorb x dsObserve, xs, os, R⟩ _ (carries_absorb hs x dsObserve) a st' h
  | sample k ih =>
    intro st sp hs a st' h
    obtain ⟨e1, e2⟩ := carries_squeeze hs
    have := ih (st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, st.stream, st.openings, st.roots⟩ _ e2 a st' h
    obtain ⟨sp', h1, h2⟩ := this
    refine ⟨sp', h1, ?_⟩
    show runId (k (Id.run (Compile.squeeze (m := Id) keccakF1600 sp)).1)
      ⟨(Id.run (Compile.squeeze (m := Id) keccakF1600 sp)).2, st.stream, st.openings, st.roots⟩ = _
    rw [e1]; exact h2
  | grind b k ih =>
    intro st sp hs a st' h
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => simp [runT] at h
    | cons n xs =>
      have ha := carries_absorb hs n dsPowNonce
      obtain ⟨e1, e2⟩ := carries_squeeze ha
      simp only [runT] at h
      split at h
      · rename_i hp
        obtain ⟨sp', h1, h2⟩ := ih ⟨(s.absorb n dsPowNonce).squeeze.2, xs, os, R⟩ _ e2 a st' h
        refine ⟨sp', h1, ?_⟩
        show (if powOk b (Id.run (Compile.squeeze (m := Id) keccakF1600
              (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).1 = true then
            runId k ⟨(Id.run (Compile.squeeze (m := Id) keccakF1600
              (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).2, xs, os, R⟩
          else none) = _
        rw [e1]; simp only [hp, ↓reduceIte]; exact h2
      · simp at h
  | commit hh ww k ih =>
    intro st sp hs a st' h
    obtain ⟨s, stream, os, R⟩ := st
    match stream, h with
    | [], h => simp [runT] at h
    | [_], h => simp [runT] at h
    | x0 :: x1 :: xs, h =>
      have h1 := carries_absorb hs x0 dsObserve
      have h2 := carries_absorb h1 x1 dsObserve
      simp only [runT] at h
      split at h
      · rename_i root hr
        obtain ⟨sp', c1, c2⟩ := ih _ _ h2 a st' h
        refine ⟨sp', c1, ?_⟩
        show (match digestFromHalves (x0, x1) with
            | some root => runId k ⟨Id.run (Compile.absorb (m := Id) keccakF1600
                (Id.run (Compile.absorb (m := Id) keccakF1600 sp x0 dsObserve)) x1 dsObserve), xs, os,
                R ++ [(root, hh, ww)]⟩
            | none => none) = _
        rw [hr]; exact c2
      · simp at h
  | query i ps k ih =>
    intro st sp hs a st' h
    obtain ⟨s, stream, os, R⟩ := st
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
          obtain ⟨sp', c1, c2⟩ := ih rows ⟨s, stream, rest, R⟩ sp hs a st' h
          refine ⟨sp', c1, ?_⟩
          simp only [Id.run] at hop
          simp only [runId, Compile.runWithHash, bind, hR, hop]
          exact c2

/-- **The deployed run is the carried run.** -/
theorem runT_of_runId {α : Type} (p : VerifierProgram α) : ∀ (st : TSt) (sp : Sponge),
    st.sponge.Carries sp →
    ∀ (a : α) (t : VerifierProgramState), runId p ⟨sp, st.stream, st.openings, st.roots⟩ = some
        (a, t) →
      runT p st = some (a, ⟨fsOfT t.sponge, t.stream, t.openings, t.roots⟩) := by
  induction p with
  | ret a =>
    intro st sp hs a' t h
    simp only [runId, Compile.runWithHash, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [← eq_fsOfT hs]
    rfl
  | fail =>
    intro st sp hs a t h
    simp [runId, Compile.runWithHash, pure] at h
  | read k ih =>
    intro st sp hs a t h
    obtain ⟨s, stream, os, roots⟩ := st
    cases stream with
    | nil => simp [runId, Compile.runWithHash, pure] at h
    | cons x xs =>
      exact ih x ⟨s.absorb x dsObserve, xs, os, roots⟩ _ (carries_absorb hs x dsObserve) a t h
  | sample k ih =>
    intro st sp hs a t h
    obtain ⟨e1, e2⟩ := carries_squeeze hs
    have := ih ((Id.run (Compile.squeeze (m := Id) keccakF1600 sp)).1)
      ⟨st.sponge.squeeze.2, st.stream, st.openings, st.roots⟩ _ e2 a t h
    simpa [runT, e1] using this
  | grind b k ih =>
    intro st sp hs a t h
    obtain ⟨s, stream, os, roots⟩ := st
    cases stream with
    | nil => simp [runId, Compile.runWithHash, pure] at h
    | cons n xs =>
      have ha := carries_absorb hs n dsPowNonce
      obtain ⟨e1, e2⟩ := carries_squeeze ha
      have key : runId (VerifierProgram.grind b k) ⟨sp, n :: xs, os, roots⟩ =
          (if powOk b (Id.run (Compile.squeeze (m := Id) keccakF1600
              (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).1 = true then
            runId k ⟨(Id.run (Compile.squeeze (m := Id) keccakF1600
              (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).2, xs, os, roots⟩
          else none) := rfl
      rw [key, e1] at h
      simp only [runT]
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih ⟨(s.absorb n dsPowNonce).squeeze.2, xs, os, roots⟩ _ e2 a t h
      · simp at h
  | commit hh ww k ih =>
    intro st sp hs a t h
    obtain ⟨s, stream, os, roots⟩ := st
    match stream with
    | [] => simp [runId, Compile.runWithHash, pure] at h
    | [_] => simp [runId, Compile.runWithHash, pure] at h
    | x0 :: x1 :: xs =>
      have h1 := carries_absorb hs x0 dsObserve
      have h2 := carries_absorb h1 x1 dsObserve
      have key : runId (VerifierProgram.commit hh ww k) ⟨sp, x0 :: x1 :: xs, os, roots⟩ =
          (match digestFromHalves (x0, x1) with
            | some root => runId k ⟨Id.run (Compile.absorb (m := Id) keccakF1600
                (Id.run (Compile.absorb (m := Id) keccakF1600 sp x0 dsObserve)) x1 dsObserve), xs, os,
                roots ++ [(root, hh, ww)]⟩
            | none => none) := rfl
      rw [key] at h
      split at h
      · rename_i root hr
        simp only [runT, hr]
        exact ih ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, xs, os, roots ++ [(root, hh, ww)]⟩
          _ h2 a t h
      · simp at h
  | query i ps k ih =>
    intro st sp hs a t h
    obtain ⟨s, stream, os, roots⟩ := st
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
          exact ih rows ⟨s, stream, rest, roots⟩ sp hs a t h


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
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => simp [runT] at h
    | cons x xs => simp only [runT] at h; exact ih x ⟨s.absorb x dsObserve, xs, os, R⟩ a st' h
  | sample k ih =>
    intro st a st' h; simp only [runT] at h
    exact ih _ ⟨st.sponge.squeeze.2, st.stream, st.openings, st.roots⟩ a st' h
  | grind b k ih =>
    intro st a st' h
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => simp [runT] at h
    | cons n xs =>
      simp only [runT] at h
      split at h
      · exact ih ⟨(s.absorb n dsPowNonce).squeeze.2, xs, os, R⟩ a st' h
      · simp at h
  | commit hh ww k ih =>
    intro st a st' h
    obtain ⟨s, stream, os, R⟩ := st
    match stream, h with
    | [], h => simp [runT] at h
    | [_], h => simp [runT] at h
    | x0 :: x1 :: xs, h =>
      simp only [runT] at h
      split at h
      · rename_i root _
        obtain ⟨C, hC⟩ := ih _ a st' h
        exact ⟨[(root, hh, ww)] ++ C, by simp only at hC ⊢; rw [hC, List.append_assoc]⟩
      · simp at h
  | query i ps k ih =>
    intro st a st' h
    obtain ⟨s, stream, os, R⟩ := st
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
          exact ih rows ⟨s, stream, rest, R⟩ a st' h

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
    obtain ⟨s, stream, os, R0⟩ := st
    cases stream with
    | nil => simp [runT] at h
    | cons x xs =>
      simp only [runT] at h ⊢; exact ih x ⟨s.absorb x dsObserve, xs, os, R0⟩ a st' h0 h1 h R
  | sample k ih =>
    intro st a st' h0 h1 h R; simp only [runT] at h ⊢
    exact ih _ ⟨st.sponge.squeeze.2, st.stream, st.openings, st.roots⟩ a st' h0 h1 h R
  | grind b k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, stream, os, R0⟩ := st
    cases stream with
    | nil => simp [runT] at h
    | cons n xs =>
      simp only [runT] at h ⊢
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih ⟨(s.absorb n dsPowNonce).squeeze.2, xs, os, R0⟩ a st' h0 h1 h R
      · simp at h
  | commit hh ww k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, stream, os, R0⟩ := st
    match stream, h with
    | [], h => simp [runT] at h
    | [_], h => simp [runT] at h
    | x0 :: x1 :: xs, h =>
      simp only [runT] at h
      split at h
      · obtain ⟨C, hC⟩ := runT_roots _ _ a st' h
        simp only at h0 hC
        rw [h1, h0] at hC
        simp at hC
      · simp at h
  | query i ps k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, stream, os, R0⟩ := st
    simp only at h0
    subst h0
    simp [runT] at h

/-- The sponge after a run from a carried one is carried. -/
theorem RunsTo.carries {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') (hc : ∃ sp, s.Carries sp) : ∃ sp, s'.Carries sp := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp', hc', -⟩ := h sp hsp [] [] []
  exact ⟨sp', hc'⟩

/-- **An accepting run of a sequence splits.** -/
theorem RunsTo.unbind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {s s'' : Fs}
    {xs : List E} {b : β}
    (h : RunsTo (p >>= f) s xs b s'') (hc : ∃ sp, s.Carries sp) :
    ∃ (a : α) (xs1 xs2 : List E) (s1 : Fs), xs = xs1 ++ xs2 ∧ RunsTo p s xs1 a s1 ∧
      RunsTo (f a) s1 xs2 b s'' := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp'', hc'', he⟩ := h sp hsp [] [] []
  simp only [List.append_nil] at he
  have hT := runT_of_runId (p >>= f) ⟨s, xs, [], []⟩ sp hsp b _ he
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
  refine ⟨a, pre1, st1.stream, st1.sponge, by rw [hs1], ?_, ?_⟩
  · intro sp0 hs0 rest os R
    have e := hf1 rest os
    rw [ho1'.1, List.nil_append] at e
    have e2 := runT_noRoots p _ a _ rfl (by simp [hr1]) e R
    obtain ⟨sp1, c1, c2⟩ := runId_of_runT p _ sp0 hs0 a _ e2
    exact ⟨sp1, c1, c2⟩
  · intro sp0 hs0 rest os R
    have e := hf2 rest os
    rw [ho2', List.nil_append, ← hs2] at e
    have e' : runT (f a) ⟨st1.sponge, st1.stream ++ rest, os, []⟩ =
        some (b, ⟨fsOfT sp'', rest, os, []⟩) := by
      simp only [hr1] at e; exact e
    have e2 := runT_noRoots (f a) _ b _ rfl rfl e' R
    obtain ⟨sp1, c1, c2⟩ := runId_of_runT (f a) ⟨st1.sponge, st1.stream ++ rest, os, R⟩ sp0 hs0 b
      ⟨fsOfT sp'', rest, os, R⟩ e2
    refine ⟨sp1, ?_, c2⟩
    rw [eq_fsOfT hc'']; exact c1

end
end LeanVM.Guest.B1.Tables
