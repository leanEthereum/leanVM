/-
  LeanVM.Guest.B1.VerifySub.NoCommit

  The deferring verifier's phases before its stacked opening commit nothing and query nothing:
  a carried run of one keeps the roots and the openings, and is a run between grounds.
-/

module

public import LeanVM.Protocol.Verifier.NoCommit
public import LeanVM.Guest.B1.Tables.RunF
public import LeanVM.Guest.B1.VerifySub.Split

/-!
# Phases without commitments

`NoCommit p` (`LeanVM.Protocol.Verifier.NoCommit`): on every path, `p` has no `commit` and no
`query` step. A carried run of such a program keeps the roots and the openings and runs
on any (`runT_any_of_noCommitA`), so a deployed run of it is a run between grounds on the words it
reads (`runsG_of_runId`). Every phase of the deferring verifier before its stacked opening but the
stack's commitment is one (`LeanVM.Protocol.Verifier.NoCommit` proves it phase by phase); the
segment `verify_tables` runs, the bus's rest, the table sumcheck and the public input, is one
here (`noCommit_tablesSeg`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Carried runs without commitments -/

/-- **A carried run without commitments keeps the roots and the openings, and runs on any.** -/
theorem runT_any_of_noCommitA {α : Type} (p : VerifierProgram α) : NoCommitA p →
    ∀ (st : Tables.TSt) (a : α) (st' : Tables.TSt), Tables.runT p st = some (a, st') →
      st'.roots = st.roots ∧ st'.openings = st.openings ∧ ∀ O2 R2,
        Tables.runT p { st with openings := O2, roots := R2 } =
          some (a, { st' with openings := O2, roots := R2 }) := by
  induction p with
  | ret b =>
    intro _ st a st' h
    simp only [Tables.runT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun _ _ ↦ rfl⟩
  | fail => intro _ st a st' h; simp [Tables.runT] at h
  | read k ih =>
    intro hp st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [Tables.runT] at h
    | _ :: _, some _, h => simp [Tables.runT] at h
    | x :: xs, none, h =>
      obtain ⟨h1, h2, h3⟩ := ih x (hp x) ⟨s.absorb x dsObserve, none, xs, os, R⟩ a st' h
      exact ⟨h1, h2, fun O2 R2 ↦ h3 O2 R2⟩
  | sample k ih =>
    intro hp st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases g with
    | some c =>
      obtain ⟨h1, h2, h3⟩ := ih c (hp c) ⟨s, none, stream, os, R⟩ a st' h
      exact ⟨h1, h2, fun O2 R2 ↦ h3 O2 R2⟩
    | none =>
      obtain ⟨h1, h2, h3⟩ := ih _ (hp _) ⟨s.squeeze.2, none, stream, os, R⟩ a st' h
      exact ⟨h1, h2, fun O2 R2 ↦ h3 O2 R2⟩
  | grind b k ih =>
    intro hp st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [Tables.runT] at h
    | _ :: _, some _, h => simp [Tables.runT] at h
    | n :: xs, none, h =>
      simp only [Tables.runT] at h ⊢
      split at h
      · rename_i hpow
        simp only [hpow, ↓reduceIte]
        obtain ⟨h1, h2, h3⟩ := ih hp _ a st' h
        exact ⟨h1, h2, fun O2 R2 ↦ h3 O2 R2⟩
      · simp at h
  | commit _ _ _ _ => intro hp; exact hp.elim
  | query _ _ _ _ => intro hp; exact hp.elim

/-- **A deployed run without commitments is a run between grounds** on the words it reads, from
the carried state of the sponge it starts from to the carried state of the one it ends with. -/
theorem runsG_of_runId {α : Type} {p : VerifierProgram α} (hp : NoCommit p) {s : Fs}
    {g : Option E} {sp : Sponge} (hs : Tables.TCar s g sp) {T : List E}
    {O : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {a : α} {t : VerifierProgramState}
    (h : runId p ⟨sp, T, O, R⟩ = some (a, t)) :
    ∃ xs, T = xs ++ t.stream ∧ t.openings = O ∧ t.roots = R ∧
      Tables.RunsG p s g xs a (Tables.fsOfT t.sponge) t.sponge.ground := by
  have hT := Tables.runT_of_runId p ⟨s, g, T, O, R⟩ sp hs a t h
  obtain ⟨hR, hO, hany⟩ := runT_any_of_noCommitA p ((noCommit_iff _).1 hp) _ a _ hT
  obtain ⟨pre, opre, hs1, ho1, hf⟩ := Tables.runT_frame p _ a _ hT
  simp only at hR hO hs1 ho1
  have hopre : opre = [] := by
    have := congrArg List.length ho1
    rw [List.length_append, hO] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hopre
  refine ⟨pre, hs1, hO, hR, fun sp2 hs2 rest os roots ↦ ?_⟩
  have e1 := hf rest O
  simp only [List.nil_append] at e1
  obtain ⟨-, -, e2⟩ := runT_any_of_noCommitA p ((noCommit_iff _).1 hp) _ a _ e1
  have e3 := e2 os roots
  obtain ⟨sp', hc, hr⟩ := Tables.runId_of_runT p _ sp2 hs2 a _ e3
  exact ⟨sp', hc, hr⟩

theorem tcar_fsOfT (sp : Sponge) : Tables.TCar (Tables.fsOfT sp) sp.ground sp :=
  ⟨rfl, rfl, rfl⟩

/-! ## The tables segment -/

theorem noCommit_tablesSeg (c : BytecodeClaim) (L : Layout) (pi : Digest) (weights : List E)
    (beta : E) (point tv : List E) :
    NoCommit (Tables.tablesSeg (claimedBytecodeValue c) L pi weights beta point tv) := by
  unfold Tables.tablesSeg
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_busRest (noCommit_claimedBytecodeValue c) _ _ _ _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_tablePhase _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_publicInputPhase _ _) fun _ ↦ ?_
  exact noCommit_ret _

end
end LeanVM.Guest.B1.VerifySub
