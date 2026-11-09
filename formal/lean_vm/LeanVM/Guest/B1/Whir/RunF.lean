/-
  LeanVM.Guest.B1.Whir.RunF

  The Spec's programs run on the carried sponge: a deterministic reading of `Compile.run`, and
  the facts the completeness direction takes from an accepting run.
-/

module

public import LeanVM.Guest.B1.Whir.CompleteIface
public import LeanVM.Guest.B1.Whir.Run
public import LeanVM.Protocol.WithHash

/-!
# Runs on the carried sponge

`runF p st`: `Compile.run` (Keccak-256, Keccak-f) with the sponge replaced by the `Fs` the guest
carries. It is a function of `st`, so an accepting run is unique (`runF_det`) and splits at a
`bind` (`runF_bind`); a run of `RunsWith` is one (`runF_of_runsWith`). `queryStepsOf` splits the
same way (`queriesOf_bind`). `Ref p' p`: `p'` refines `p` (every run of `p'` is one of `p`, with
its query steps); `whirOpenNZ` refines `whirOpen` (`whirOpenNZ_ref`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A run on the carried sponge.** -/
def runF {α : Type} : VerifierProgram α → FSt → Option (α × FSt)
  | .ret a, s => some (a, s)
  | .fail, _ => none
  | .read k, s => match s.stream with
    | [] => none
    | x :: xs => runF (k x) { s with sponge := s.sponge.absorb x dsObserve, stream := xs }
  | .sample k, s => runF (k s.sponge.squeeze.1) { s with sponge := s.sponge.squeeze.2 }
  | .grind bits k, s => match s.stream with
    | [] => none
    | n :: xs =>
      let sq := (s.sponge.absorb n dsPowNonce).squeeze
      if powOk bits n sq.1 then runF k { s with sponge := sq.2, stream := xs } else none
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs =>
      match digestFromHalves (x0, x1) with
      | some root =>
        runF k { s with
          sponge := (s.sponge.absorb x0 dsObserve).absorb x1 dsObserve
          stream := xs
          roots := s.roots ++ [(root, height, width)] }
      | none => none
    | _ => none
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
      | some rows => runF (k rows) { s with openings := rest }
      | none => none
    | _, _ => none

theorem runF_bind {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) (st : FSt) :
    runF (p.bind f) st = (runF p st).bind (fun r ↦ runF (f r.1) r.2) := by
  induction p generalizing st with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [VerifierProgram.bind, runF]
    split
    · rfl
    · exact ih _ _
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [VerifierProgram.bind, runF]
    split
    · rfl
    · split
      · exact ih _
      · rfl
  | commit h w k ih =>
    simp only [VerifierProgram.bind, runF]
    split
    · split
      · exact ih _
      · rfl
    · rfl
  | query i ps k ih =>
    simp only [VerifierProgram.bind, runF]
    split
    · split
      · exact ih _ _
      · rfl
    · rfl

theorem runF_bind_some {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {st : FSt}
    {r : β × FSt}
    (h : runF (p.bind f) st = some r) :
    ∃ a st', runF p st = some (a, st') ∧ runF (f a) st' = some r := by
  rw [runF_bind] at h
  obtain ⟨⟨a, st'⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨a, st', h1, h2⟩

/-- The `Fs` a sponge's carrier is. -/
def fsOf (sp : Sponge) : Fs := ⟨capOf sp.state, sp.pending⟩

theorem eq_fsOf {s : Fs} {sp : Sponge} (h : s.Carries sp) : s = fsOf sp := by
  obtain ⟨h1, h2⟩ := h
  cases s
  simp only [fsOf, Fs.mk.injEq]
  exact ⟨h1.symm, h2.symm⟩

/-- **The deployed run is the carried run.** -/
theorem runF_of_runId {α : Type} (p : VerifierProgram α) : ∀ (st : FSt) (sp : Sponge),
    st.sponge.Carries sp →
    ∀ (a : α) (t : VerifierProgramState), runId p ⟨sp, st.stream, st.openings, st.roots⟩ = some
        (a, t) →
      runF p st = some (a, ⟨fsOf t.sponge, t.stream, t.openings, t.roots⟩) := by
  induction p with
  | ret a =>
    intro st sp hs a' t h
    simp only [runId, Compile.runWithHash, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [← eq_fsOf hs]
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
    simpa [runF, e1] using this
  | grind b k ih =>
    intro st sp hs a t h
    obtain ⟨s, stream, os, roots⟩ := st
    cases stream with
    | nil => simp [runId, Compile.runWithHash, pure] at h
    | cons n xs =>
      have ha := carries_absorb hs n dsPowNonce
      obtain ⟨e1, e2⟩ := carries_squeeze ha
      have key : runId (VerifierProgram.grind b k) ⟨sp, n :: xs, os, roots⟩ =
          (if powOk b n (Id.run (Compile.squeeze (m := Id) keccakF1600
              (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).1 = true then
            runId k ⟨(Id.run (Compile.squeeze (m := Id) keccakF1600
              (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).2, xs, os, roots⟩
          else none) := rfl
      rw [key, e1] at h
      simp only [runF]
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
        simp only [runF, hr]
        exact ih ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, xs, os, roots ++ [(root, hh, ww)]⟩
          _ h2 a t h
      · simp at h
  | query i ps k ih =>
    intro st sp hs a t h
    obtain ⟨s, stream, os, roots⟩ := st
    simp only [runId, Compile.runWithHash, bind] at h
    simp only [runF]
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

/-- **An accepting run is a carried run.** -/
theorem runF_of_runsWith {α : Type} {p : VerifierProgram α} {s : Fs} {xs : List E}
    {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : α} {s' : Fs} {R' : List (Digest × ℕ × ℕ)}
    (h : RunsWith p s xs os R a s' R') {sp : Sponge} (hs : s.Carries sp) :
    runF p ⟨s, xs, os, R⟩ = some (a, ⟨s', [], [], R'⟩) := by
  obtain ⟨sp', hc, he⟩ := h sp hs [] []
  simp only [List.append_nil] at he
  have := runF_of_runId p ⟨s, xs, os, R⟩ sp hs a _ he
  rw [this, ← eq_fsOf hc]

/-- A run is unique. -/
theorem runF_det {α : Type} {p : VerifierProgram α} {st : FSt} {r r' : α × FSt} (h : runF p st =
    some r)
    (h' : runF p st = some r') : r = r' := Option.some.inj (h.symm.trans h')

/-! ## Query steps -/

theorem queriesOf_bind {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) (st : FSt) :
    queryStepsOf (p.bind f) st = queryStepsOf p st ++
      (match runF p st with
        | some r => queryStepsOf (f r.1) r.2
        | none => []) := by
  induction p generalizing st with
  | ret a => simp [VerifierProgram.bind, queryStepsOf, runF]
  | fail => simp [VerifierProgram.bind, queryStepsOf, runF]
  | read k ih =>
    obtain ⟨s, stream, os, roots⟩ := st
    cases stream with
    | nil => simp [VerifierProgram.bind, queryStepsOf, runF]
    | cons x xs => exact ih _ _
  | sample k ih => exact ih _ _
  | grind b k ih =>
    obtain ⟨s, stream, os, roots⟩ := st
    cases stream with
    | nil => simp [VerifierProgram.bind, queryStepsOf, runF]
    | cons n xs =>
      simp only [VerifierProgram.bind, queryStepsOf, runF]
      split
      · exact ih _
      · simp
  | commit h w k ih =>
    obtain ⟨s, stream, os, roots⟩ := st
    match stream with
    | [] => simp [VerifierProgram.bind, queryStepsOf, runF]
    | [_] => simp [VerifierProgram.bind, queryStepsOf, runF]
    | x0 :: x1 :: xs =>
      cases hd : digestFromHalves (x0, x1) with
      | none => simp [VerifierProgram.bind, queryStepsOf, runF, hd]
      | some root =>
        simp only [VerifierProgram.bind, queryStepsOf, runF, hd]
        exact ih _
  | query i ps k ih =>
    obtain ⟨s, stream, os, roots⟩ := st
    cases hr : roots[i]? with
    | none => simp [VerifierProgram.bind, queryStepsOf, runF, hr]
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [VerifierProgram.bind, queryStepsOf, runF, hr]
      | cons phase rest =>
        cases ho : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none =>
          simp only [Id.run] at ho
          simp [VerifierProgram.bind, queryStepsOf, runF, hr, ho, Id.run]
        | some rows =>
          simp only [Id.run] at ho
          simp only [VerifierProgram.bind, queryStepsOf, runF, hr, ho, ih, Id.run,
            List.cons_append]

/-! ## Refinement -/

/-- `p'` refines `p`: every run of `p'` is a run of `p`, with the same query steps. -/
def Ref {α : Type} (p' p : VerifierProgram α) : Prop :=
  ∀ st r, runF p' st = some r → runF p st = some r ∧ queryStepsOf p' st = queryStepsOf p st

theorem Ref.refl {α : Type} (p : VerifierProgram α) : Ref p p := fun _ _ h ↦ ⟨h, rfl⟩

theorem Ref.bind {α β : Type} {p' p : VerifierProgram α} {f' f : α → VerifierProgram β} (h :
    Ref p' p)
    (hf : ∀ a, Ref (f' a) (f a)) : Ref (p'.bind f') (p.bind f) := by
  intro st r hr
  obtain ⟨a, st', h1, h2⟩ := runF_bind_some hr
  obtain ⟨e1, q1⟩ := h st _ h1
  obtain ⟨e2, q2⟩ := hf a st' r h2
  refine ⟨by rw [runF_bind, e1]; exact e2, ?_⟩
  rw [queriesOf_bind, queriesOf_bind, q1, h1, e1]
  simp only [q2]

/-- A `require` before a program refines the program. -/
theorem Ref.require {α : Type} (c : Prop) [Decidable c] {p' p : VerifierProgram α} (h : Ref p' p) :
    Ref ((VerifierProgram.require c).bind fun _ ↦ p') p := by
  intro st r hr
  by_cases hc : c
  · have e : (VerifierProgram.require c).bind (fun _ ↦ p') = p' := by
      simp only [VerifierProgram.require, hc, ↓reduceIte]; rfl
    rw [e] at hr ⊢
    exact h st r hr
  · simp [VerifierProgram.require, hc, VerifierProgram.bind, runF] at hr

end
end LeanVM.Guest.B1.Whir
