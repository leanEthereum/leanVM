/-
  LeanVM.Guest.B1.VerifySub.NZRun

  Carried runs of the Spec's programs, for the completeness direction: B1-b's `runF` is B1-c's
  `runT`, so a carried run that reads all it is given is a `RunsWith`; the deployed query steps are
  the carried ones.
-/

module

public import LeanVM.Guest.B1.Whir.SpecNZ
public import LeanVM.Guest.B1.Tables.RunF
public import LeanVM.Guest.Limits
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# Carried runs, for completeness

* `runF_eq_runT`: B1-b's carried run (`Whir.runF`) is B1-c's (`Tables.runT`), field for field.
* `runsWith_of_runF`: a carried run that consumes all the words and openings it is given is a
  `RunsWith` (`Tables.runT_frame` for any rest, `Tables.runId_of_runT` for every sponge carried).
* `queriesOf_eq_steps`: the deployed run's query steps (`Limits.queryStepsOf`) are the carried run's
  (`Whir.queryStepsOf`); `batchAgrees_of` turns G7's `Limits.OpeningsAgree` into B1-b's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## B1-b's carried run is B1-c's -/

/-- A `Whir.FSt` as a `Tables.TSt`. -/
def toT (st : Whir.FSt) : Tables.TSt := ⟨st.sponge, st.stream, st.openings, st.roots⟩

/-- A `Tables.TSt` as a `Whir.FSt`. -/
def ofT (st : Tables.TSt) : Whir.FSt := ⟨st.sponge, st.stream, st.openings, st.roots⟩

theorem runF_eq_runT {α : Type} (p : VerifierProgram α) : ∀ st : Whir.FSt,
    Whir.runF p st = (Tables.runT p (toT st)).map fun r ↦ (r.1, ofT r.2) := by
  induction p with
  | ret a => intro st; rfl
  | fail => intro st; rfl
  | read k ih =>
    intro st
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => rfl
    | cons x xs =>
      simp only [Whir.runF, Tables.runT]
      exact ih x _
  | sample k ih =>
    intro st
    simp only [Whir.runF, Tables.runT]
    exact ih _ _
  | grind b k ih =>
    intro st
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => rfl
    | cons n xs =>
      simp only [Whir.runF, Tables.runT, toT]
      split
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih _
      · rename_i hp
        simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  | commit h w k ih =>
    intro st
    obtain ⟨s, stream, os, R⟩ := st
    match stream with
    | [] => rfl
    | [_] => rfl
    | x0 :: x1 :: xs =>
      simp only [Whir.runF, Tables.runT, toT]
      split
      · rename_i root hr
        simp only [hr]
        exact ih _
      · rename_i hr
        simp only [hr, Option.map_none]
  | query i ps k ih =>
    intro st
    obtain ⟨s, stream, os, R⟩ := st
    simp only [Whir.runF, Tables.runT, toT]
    cases hr : R[i]? with
    | none => rfl
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => rfl
      | cons phase rest =>
        simp only
        cases ho : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none =>
          simp only [Option.map_none]
        | some rows =>
          simp only
          exact ih rows _

/-- **A carried run consuming all it is given is a `RunsWith`.** -/
theorem runsWith_of_runF {α : Type} {p : VerifierProgram α} {s : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : α} {s' : Fs} {R' : List (Digest × ℕ × ℕ)}
    (h : Whir.runF p ⟨s, xs, os, R⟩ = some (a, ⟨s', [], [], R'⟩)) :
    Whir.RunsWith p s xs os R a s' R' := by
  intro sp hs rest orest
  rw [runF_eq_runT] at h
  obtain ⟨⟨a', t⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨ts, tstream, tos, tR⟩ := t
  simp only [ofT, Prod.mk.injEq, Whir.FSt.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
  obtain ⟨pre, opre, hs1, ho1, hf⟩ := Tables.runT_frame p _ _ _ ht
  simp only [toT, List.append_nil] at hs1 ho1
  subst hs1 ho1
  have e := hf rest orest
  obtain ⟨sp', hc, hr⟩ := Tables.runId_of_runT p _ sp hs _ _ e
  exact ⟨sp', hc, hr⟩

/-! ## Query steps -/

/-- **The deployed run's query steps are the carried run's.** -/
theorem queriesOf_eq_steps {α : Type} (p : VerifierProgram α) : ∀ (st : Whir.FSt) (sp : Sponge),
    st.sponge.Carries sp →
      Limits.queryStepsOf p ⟨sp, st.stream, st.openings, st.roots⟩ = Whir.queryStepsOf p st := by
  induction p with
  | ret a => intro st sp hs; rfl
  | fail => intro st sp hs; rfl
  | read k ih =>
    intro st sp hs
    obtain ⟨s, stream, os, roots⟩ := st
    cases stream with
    | nil => rfl
    | cons x xs =>
      exact ih x ⟨s.absorb x dsObserve, xs, os, roots⟩ _ (carries_absorb hs x dsObserve)
  | sample k ih =>
    intro st sp hs
    obtain ⟨e1, e2⟩ := carries_squeeze hs
    have := ih ((Id.run (Compile.squeeze (m := Id) keccakF1600 sp)).1)
      ⟨st.sponge.squeeze.2, st.stream, st.openings, st.roots⟩ _ e2
    simpa [Limits.queryStepsOf, Whir.queryStepsOf, e1] using this
  | grind b k ih =>
    intro st sp hs
    obtain ⟨s, stream, os, roots⟩ := st
    cases stream with
    | nil => rfl
    | cons n xs =>
      have ha := carries_absorb hs n dsPowNonce
      obtain ⟨e1, e2⟩ := carries_squeeze ha
      have key : Limits.queryStepsOf (VerifierProgram.grind b k) ⟨sp, n :: xs, os, roots⟩ =
          (if powOk b n (Id.run (Compile.squeeze (m := Id) keccakF1600
              (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).1 = true then
            Limits.queryStepsOf k ⟨(Id.run (Compile.squeeze (m := Id) keccakF1600
              (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).2, xs, os, roots⟩
          else []) := rfl
      rw [key, e1]
      simp only [Whir.queryStepsOf]
      split
      · exact ih ⟨(s.absorb n dsPowNonce).squeeze.2, xs, os, roots⟩ _ e2
      · rfl
  | commit hh ww k ih =>
    intro st sp hs
    obtain ⟨s, stream, os, roots⟩ := st
    match stream with
    | [] => rfl
    | [_] => rfl
    | x0 :: x1 :: xs =>
      have h1 := carries_absorb hs x0 dsObserve
      have h2 := carries_absorb h1 x1 dsObserve
      have key : Limits.queryStepsOf (VerifierProgram.commit hh ww k) ⟨sp, x0 :: x1 :: xs, os,
          roots⟩ =
          (match digestFromHalves (x0, x1) with
            | some root => Limits.queryStepsOf k ⟨Id.run (Compile.absorb (m := Id) keccakF1600
                (Id.run (Compile.absorb (m := Id) keccakF1600 sp x0 dsObserve)) x1 dsObserve), xs, os,
                roots ++ [(root, hh, ww)]⟩
            | none => []) := rfl
      rw [key]
      simp only [Whir.queryStepsOf]
      split
      · rename_i root hr
        simp only [hr]
        exact ih ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, xs, os, roots ++ [(root, hh, ww)]⟩
          _ h2
      · rename_i hr
        simp only [hr]
  | query i ps k ih =>
    intro st sp hs
    obtain ⟨s, stream, os, roots⟩ := st
    simp only [Limits.queryStepsOf, Whir.queryStepsOf]
    cases hr : roots[i]? with
    | none => rfl
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => rfl
      | cons phase rest =>
        simp only [Compile.openPhase_eq_withHash, keccak256With_keccakF1600]
        cases ho : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => rfl
        | some rows =>
          exact congrArg _ (ih rows ⟨s, stream, rest, roots⟩ sp hs)

/-- G7's agreement of a query step's openings is B1-b's. -/
theorem batchAgrees_of {d : ℕ} {qs : List (ℕ × Opening)} (h : Limits.OpeningsAgree d qs) :
    Whir.BatchAgrees d qs := by
  simp only [Limits.OpeningsAgree, Limits.OpeningGivesNode, Guest.Limits.climbTo_eq_withHash] at h
  exact h

end
end LeanVM.Guest.B1.VerifySub
