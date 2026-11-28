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

`runTK p st`: `Compile.run` (Keccak-256, Keccak-f) with the sponge replaced by the `Fs` the guest
carries and the ground challenge a grind leaves (`TCarK`). It splits at a `bind` (`runT_bindK`),
keeps any stream and openings past what it reads (`runT_frameK`), and is the deployed run on every
sponge the state carries (`runT_of_runIdK`, `runId_of_runTK`).

Packed reads and draws are not carried (`runTK` rejects them): `runT_of_runIdK` takes a program
with none (`PackedFree`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The state of a carried run: the carried sponge, the ground challenge a grind left (the next
sample returns it), the words and openings left, the roots. -/
structure TStK where
  sponge : Fs
  ground : Option E
  stream : List E
  openings : List (List Opening)
  roots : List (Digest × ℕ × ℕ)

/-- The Spec's sponge `sp` is the one the guest carries as `s`, with the ground challenge `g`. -/
def TCarK (s : Fs) (g : Option E) (sp : Sponge) : Prop :=
  capOf sp.state = s.cap ∧ sp.pending = s.pend ∧ sp.ground = g

theorem tcar_noneK {s : Fs} {sp : Sponge} : TCarK s none sp ↔ s.Carries sp := Iff.rfl

/-- **A run on the carried sponge.** -/
def runTK {α : Type} : VerifierProgram α → TStK → Option (α × TStK)
  | .ret a, s => some (a, s)
  | .fail, _ => none
  | .read k, s => match s.stream, s.ground with
    | x :: xs, none => runTK (k x) { s with sponge := s.sponge.absorb x dsObserve, stream := xs }
    | _, _ => none
  | .sample k, s => match s.ground with
    | some c => runTK (k c) { s with ground := none }
    | none => runTK (k s.sponge.squeeze.1) { s with sponge := s.sponge.squeeze.2 }
  | .readPacked _ _, _ => none
  | .samplePacked _ _, _ => none
  | .grind bits k, s => match s.stream, s.ground with
    | n :: xs, none =>
      if powOk bits (Keccak.lane (s.sponge.nonceState n) 2) then
        runTK k { s with
          sponge := Fs.mk (capOf (s.sponge.nonceState n)) []
          ground := some (challengeOf (s.sponge.nonceState n))
          stream := xs }
      else none
    | _, _ => none
  | .commit height width k, s => match s.stream, s.ground with
    | x0 :: x1 :: xs, none =>
      runTK k { s with
        sponge := (s.sponge.absorb x0 dsObserve).absorb x1 dsObserve
        stream := xs
        roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)] }
    | _, _ => none
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
      | some rows => runTK (k rows) { s with openings := rest }
      | none => none
    | _, _ => none

theorem runT_bindK {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) (st : TStK) :
    runTK (p.bind f) st = (runTK p st).bind (fun r ↦ runTK (f r.1) r.2) := by
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
      · simp only [VerifierProgram.bind, runTK]
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
    simp only [VerifierProgram.bind, runTK]
    split
    · split
      · exact ih _ _
      · rfl
    · rfl
  | readPacked n k ih => rfl
  | samplePacked n k ih => rfl

/-- **A run keeps the words and openings it does not read.** -/
theorem runT_frameK {α : Type} (p : VerifierProgram α) : ∀ (st : TStK) (a : α) (st' : TStK),
    runTK p st = some (a, st') → ∃ pre opre, st.stream = pre ++ st'.stream ∧
      st.openings = opre ++ st'.openings ∧ ∀ zs orest,
        runTK p { st with stream := pre ++ zs, openings := opre ++ orest } =
          some (a, { st' with stream := zs, openings := orest }) := by
  induction p with
  | ret b =>
    intro st a st' h
    simp only [runTK, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], rfl, rfl, fun zs orest => rfl⟩
  | fail => intro st a st' h; simp [runTK] at h
  | readPacked n k ih => intro st a st' h; simp [runTK] at h
  | samplePacked n k ih => intro st a st' h; simp [runTK] at h
  | read k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTK] at h
    | _ :: _, some _, h => simp [runTK] at h
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
    | [], _, h => simp [runTK] at h
    | _ :: _, some _, h => simp [runTK] at h
    | n :: xs, none, h =>
      simp only [runTK] at h
      split at h
      · rename_i hp
        obtain ⟨pre, opre, h1, h2, hf⟩ := ih _ a st' h
        refine ⟨n :: pre, opre, by simp only [List.cons_append] at h1 ⊢; rw [h1], h2,
          fun zs orest => ?_⟩
        simp only [runTK, List.cons_append, hp, ↓reduceIte]
        exact hf zs orest
      · simp at h
  | commit hh ww k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTK] at h
    | [_], _, h => simp [runTK] at h
    | _ :: _ :: _, some _, h => simp [runTK] at h
    | x0 :: x1 :: xs, none, h =>
      obtain ⟨pre, opre, h1, h2, hf⟩ := ih _ a st' h
      refine ⟨x0 :: x1 :: pre, opre, by simp only [List.cons_append] at h1 ⊢; rw [h1], h2,
        fun zs orest => ?_⟩
      exact hf zs orest
  | query i ps k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [runTK, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runTK, hR] at h
      | cons phase rest =>
        simp only [runTK, hR] at h
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h
          obtain ⟨pre, opre, h1, h2, hf⟩ := ih rows _ a st' h
          refine ⟨pre, phase :: opre, h1, by simp only at h2 ⊢; rw [h2]; rfl, fun zs orest => ?_⟩
          simp only [runTK, hR, List.cons_append, hop]
          exact hf zs orest

/-- The `Fs` a sponge's carrier is. -/
def fsOfTK (sp : Sponge) : Fs := ⟨capOf sp.state, sp.pending⟩

theorem eq_fsOfTK {s : Fs} {g : Option E} {sp : Sponge} (h : TCarK s g sp) :
    s = fsOfTK sp ∧ g = sp.ground := by
  obtain ⟨h1, h2, h3⟩ := h
  cases s
  simp only [fsOfTK, Fs.mk.injEq]
  exact ⟨⟨h1.symm, h2.symm⟩, h3.symm⟩

/-- **The carried run is the deployed run** on every sponge the state carries. -/
theorem runId_of_runTK {α : Type} (p : VerifierProgram α) : ∀ (st : TStK) (sp : Sponge),
    TCarK st.sponge st.ground sp →
    ∀ (a : α) (st' : TStK), runTK p st = some (a, st') →
      ∃ sp', TCarK st'.sponge st'.ground sp' ∧
        runId p ⟨sp, st.stream, st.openings, st.roots⟩ =
          some (a, ⟨sp', st'.stream, st'.openings, st'.roots⟩) := by
  induction p with
  | ret b =>
    intro st sp hs a st' h
    simp only [runTK, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨sp, hs, rfl⟩
  | fail => intro st sp hs a st' h; simp [runTK] at h
  | readPacked n k ih => intro st sp hs a st' h; simp [runTK] at h
  | samplePacked n k ih => intro st sp hs a st' h; simp [runTK] at h
  | read k ih =>
    intro st sp hs a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTK] at h
    | _ :: _, some _, h => simp [runTK] at h
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
    | [], _, h => simp [runTK] at h
    | _ :: _, some _, h => simp [runTK] at h
    | n :: xs, none, h =>
      simp only [runTK] at h
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
    | [], _, h => simp [runTK] at h
    | [_], _, h => simp [runTK] at h
    | _ :: _ :: _, some _, h => simp [runTK] at h
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
    | none => simp [runTK, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runTK, hR] at h
      | cons phase rest =>
        simp only [runTK, hR] at h
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

/-- **A program with no packed read or draw** (the carried run has none). -/
inductive PackedFree : {α : Type} → VerifierProgram α → Prop
  | ret {α : Type} (a : α) : PackedFree (.ret a)
  | fail {α : Type} : PackedFree (.fail : VerifierProgram α)
  | read {α : Type} {k : E → VerifierProgram α} : (∀ x, PackedFree (k x)) → PackedFree (.read k)
  | sample {α : Type} {k : E → VerifierProgram α} : (∀ x, PackedFree (k x)) → PackedFree (.sample k)
  | grind {α : Type} {b : ℕ} {k : VerifierProgram α} : PackedFree k → PackedFree (.grind b k)
  | commit {α : Type} {h w : ℕ} {k : VerifierProgram α} : PackedFree k → PackedFree (.commit h w k)
  | query {α : Type} {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} :
      (∀ rows, PackedFree (k rows)) → PackedFree (.query i ps k)

/-- **The deployed run is the carried run.** -/
theorem runT_of_runIdK {α : Type} (p : VerifierProgram α) (hpf : PackedFree p) : ∀ (st : TStK) (sp : Sponge),
    TCarK st.sponge st.ground sp →
    ∀ (a : α) (t : VerifierProgramState), runId p ⟨sp, st.stream, st.openings, st.roots⟩ = some
        (a, t) →
      runTK p st = some (a, ⟨fsOfTK t.sponge, t.sponge.ground, t.stream, t.openings, t.roots⟩) := by
  induction hpf with
  | @ret a =>
    intro st sp hs a' t h
    simp only [runId, Compile.runWithHash, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, e2⟩ := eq_fsOfTK hs
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only at e1 e2
    subst e1 e2
    rfl
  | fail =>
    intro st sp hs a t h
    simp [runId, Compile.runWithHash, pure] at h
  | @read k _ ih =>
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
  | @sample k _ ih =>
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
      simpa [runTK, e1] using this
  | @grind b k _ ih =>
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
          runTK k ⟨Fs.mk (capOf (s.nonceState n)) [], some (challengeOf (s.nonceState n)), xs, os,
            roots⟩ else none) = _
        simp only [hp, ↓reduceIte]
        exact e
      · simp [hp] at h
  | @commit hh ww k _ ih =>
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
  | @query i ps k _ ih =>
    intro st sp hs a t h
    obtain ⟨s, g, stream, os, roots⟩ := st
    simp only [runId, Compile.runWithHash, bind] at h
    simp only [runTK]
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
theorem runT_rootsK {α : Type} (p : VerifierProgram α) : ∀ (st : TStK) (a : α) (st' : TStK),
    runTK p st = some (a, st') → ∃ C, st'.roots = st.roots ++ C := by
  induction p with
  | ret b =>
    intro st a st' h
    simp only [runTK, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp⟩
  | fail => intro st a st' h; simp [runTK] at h
  | readPacked n k ih => intro st a st' h; simp [runTK] at h
  | samplePacked n k ih => intro st a st' h; simp [runTK] at h
  | read k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTK] at h
    | _ :: _, some _, h => simp [runTK] at h
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
    | [], _, h => simp [runTK] at h
    | _ :: _, some _, h => simp [runTK] at h
    | n :: xs, none, h =>
      simp only [runTK] at h
      split at h
      · exact ih ⟨Fs.mk (capOf (s.nonceState n)) [], some (challengeOf (s.nonceState n)), xs, os, R⟩ a st' h
      · simp at h
  | commit hh ww k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTK] at h
    | [_], _, h => simp [runTK] at h
    | _ :: _ :: _, some _, h => simp [runTK] at h
    | x0 :: x1 :: xs, none, h =>
      obtain ⟨C, hC⟩ := ih ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, os, R ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ a st' h
      exact ⟨[(digestFromHalves (x0, x1), hh, ww)] ++ C, by
        simp only at hC ⊢; rw [hC, List.append_assoc]⟩
  | query i ps k ih =>
    intro st a st' h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [runTK, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runTK, hR] at h
      | cons phase rest =>
        simp only [runTK, hR] at h
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h
          exact ih rows ⟨s, g, stream, rest, R⟩ a st' h

/-- A run from no roots to no roots runs from any roots. -/
theorem runT_noRootsK {α : Type} (p : VerifierProgram α) : ∀ (st : TStK) (a : α) (st' : TStK),
    st.roots = [] → st'.roots = [] → runTK p st = some (a, st') →
      ∀ R, runTK p { st with roots := R } = some (a, { st' with roots := R }) := by
  induction p with
  | ret b =>
    intro st a st' h0 h1 h R
    simp only [runTK, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | fail => intro st a st' _ _ h; simp [runTK] at h
  | readPacked n k ih => intro st a st' _ _ h; simp [runTK] at h
  | samplePacked n k ih => intro st a st' _ _ h; simp [runTK] at h
  | read k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, g, stream, os, R0⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTK] at h
    | _ :: _, some _, h => simp [runTK] at h
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
    | [], _, h => simp [runTK] at h
    | _ :: _, some _, h => simp [runTK] at h
    | n :: xs, none, h =>
      simp only [runTK] at h ⊢
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih ⟨Fs.mk (capOf (s.nonceState n)) [], some (challengeOf (s.nonceState n)), xs, os, R0⟩ a st' h0 h1 h R
      · simp at h
  | commit hh ww k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, g, stream, os, R0⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTK] at h
    | [_], _, h => simp [runTK] at h
    | _ :: _ :: _, some _, h => simp [runTK] at h
    | x0 :: x1 :: xs, none, h =>
      have h' : runTK k ⟨(s.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, os,
          R0 ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ = some (a, st') := h
      obtain ⟨C, hC⟩ := runT_rootsK _ _ a st' h'
      simp only at h0 hC
      rw [h1, h0] at hC
      simp at hC
  | query i ps k ih =>
    intro st a st' h0 h1 h R
    obtain ⟨s, g, stream, os, R0⟩ := st
    simp only at h0
    subst h0
    simp [runTK] at h

end
end LeanVM.Guest.B1.Tables
