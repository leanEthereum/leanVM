/-
  LeanVM.Guest.B1.Whir.CRecQueries

  The queries `Hints.recordQueries` records on an accepting run are the run's query steps (`Limits.queryStepsOf`), so a child's Merkle hints (`Hints.merkleHints` of `Hints.childQueries`) are `Hints.levelHints` of its query steps, one level per step.
-/

module

public import LeanVM.Guest.B1.Whir.CCapsRun
public import LeanVM.Guest.Hints

/-!
# The recorded queries are the query steps

* `RecOk`, `runId_recordQueries`: on a run of `p` to `(a, st')`, `recordQueries p` runs to `(a, Q)` and `st'`, the roots only grow, `Q`'s heights at the final roots and positions are the query steps' (`stepQ`), and the steps' phases are the openings consumed;
* `childQueries_eq`: a child's queries are its deferring verifier's query steps;
* `stepsHints`, `merkleHints_steps`: `Hints.merkleHints` over the steps and the openings they consume is `Hints.levelHints` per step, the first `first`;
* `childMerkleHints_eq`: a child's Merkle hints are `stepsHints true` of its query steps; `levelHints_zip`: a step's level is its phase's.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub (runId_query runId_query_none queryStepsOf_query)
open LeanVM.Node

@[expose] public section

variable {α : Type}

/-- A query step's height and positions. -/
def stepQ (s : ℕ × List (ℕ × Opening)) : ℕ × List ℕ := (s.1, s.2.map Prod.fst)

/-- Recorded queries with their commitments' heights at the roots `R`. -/
def heightsAt (R : List (Digest × ℕ × ℕ)) (Q : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Q.map fun q => ((R[q.1]?.map (·.2.1)).getD 0, q.2)

/-- **What `recordQueries` records on a run of `p` from `st` to `(a, st')`.** -/
def RecOk (p : VerifierProgram α) (st : VerifierProgramState) (a : α) (st' : VerifierProgramState) : Prop :=
  ∃ Q, runId (Hints.recordQueries p) st = some ((a, Q), st') ∧ st.roots <+: st'.roots ∧
    heightsAt st'.roots Q = (Limits.queryStepsOf p st).map stepQ ∧
    st.openings = (Limits.queryStepsOf p st).map (fun s => s.2.map Prod.snd) ++ st'.openings

/-- **`recordQueries` records the run's query steps.** -/
theorem runId_recordQueries : ∀ (p : VerifierProgram α) (st : VerifierProgramState) (a : α)
    (st' : VerifierProgramState), runId p st = some (a, st') → RecOk p st a st'
  | .ret b, st, a, st', h => by
    have e : runId (VerifierProgram.ret b) st = some (b, st) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, List.prefix_refl _, rfl, rfl⟩
  | .fail, _, _, _, h => absurd h (by rintro ⟨⟩)
  | .read k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x :: xs, none, h => exact runId_recordQueries (k x) _ a st' h
  | .sample k, st, a, st', h => runId_recordQueries (k _) _ a st' h
  | .grind bits k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | n :: xs, none, h =>
      simp only [runId, Compile.runWithHash] at h
      unfold RecOk
      simp only [Hints.recordQueries, runId, Compile.runWithHash, Limits.queryStepsOf]
      generalize absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n = N at h ⊢
      obtain ⟨pw, sp'⟩ := N
      change (if powOk bits pw = true then _ else _) = _ at h
      split at h
      · rename_i hp
        obtain ⟨Q, h1, h2, h3, h4⟩ := runId_recordQueries k _ a st' h
        refine ⟨Q, ?_, h2, ?_, ?_⟩
        · change (if powOk bits pw = true then _ else _) = _
          simp only [hp, ↓reduceIte]
          exact h1
        · change _ = List.map stepQ (if powOk bits pw = true then _ else _)
          simp only [hp, ↓reduceIte]
          exact h3
        · change _ = List.map _ (if powOk bits pw = true then _ else _) ++ _
          simp only [hp, ↓reduceIte]
          exact h4
      · exact absurd h (by rintro ⟨⟩)
  | .commit hh ww k, ⟨⟨S0, P0, g⟩, stream, os, R⟩, a, st', h => by
    match stream, g, h with
    | [], _, h => exact absurd h (by rintro ⟨⟩)
    | [_], _, h => exact absurd h (by rintro ⟨⟩)
    | _ :: _ :: _, some _, h => exact absurd h (by rintro ⟨⟩)
    | x0 :: x1 :: xs, none, h =>
      obtain ⟨Q, h1, h2, h3, h4⟩ := runId_recordQueries k _ a st' h
      exact ⟨Q, h1, (List.prefix_append _ _).trans h2, h3, h4⟩
  | .query i ps k, ⟨sp, stream, os, R⟩, a, st', h => by
    cases hR : R[i]? with
    | none =>
      rw [runId_query_none _ _ _ _ (Or.inl hR)] at h
      exact absurd h (by rintro ⟨⟩)
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil =>
        rw [runId_query_none _ _ _ _ (Or.inr rfl)] at h
        exact absurd h (by rintro ⟨⟩)
      | cons phase rest =>
        rw [runId_query _ _ _ _ _ _ _ _ hR] at h
        unfold RecOk
        rw [show Hints.recordQueries (VerifierProgram.query i ps k) = VerifierProgram.query i ps fun rows ↦
            (Hints.recordQueries (k rows)).bind fun r ↦ .ret (r.1, (i, ps) :: r.2) from rfl,
          runId_query _ _ _ _ _ _ _ _ hR, queryStepsOf_query _ _ _ _ _ _ _ _ hR]
        split at h
        · rename_i rows hrows
          obtain ⟨Q, h1, h2, h3, h4⟩ := runId_recordQueries (k rows) _ a st' h
          obtain ⟨hlen, -, -, -⟩ := phase_of_some hrows
          obtain ⟨t, ht⟩ := h2
          have hi : i < R.length := (List.getElem?_eq_some_iff.mp hR).1
          refine ⟨(i, ps) :: Q, ?_, ⟨t, ht⟩, ?_, ?_⟩
          · rw [run_bind, h1]; rfl
          · simp only [heightsAt, List.map_cons] at h3 ⊢
            rw [h3, ← ht, List.getElem?_append_left hi, hR, stepQ, List.map_fst_zip (by omega)]
            rfl
          · simp only at h4 ⊢
            rw [List.map_cons, List.cons_append, ← h4, List.map_snd_zip (by omega)]
        · exact absurd h (by rintro ⟨⟩)

/-- **A child's queries are its deferring verifier's query steps**, on an accepting run. -/
theorem childQueries_eq {bytecode : List K} {seed : Digest} {c : Child} {a : Bool}
    {st' : VerifierProgramState}
    (h : runId (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) = some (a, st')) :
    Hints.childQueries bytecode seed c = (Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c)).map stepQ := by
  obtain ⟨Q, h1, -, h3, -⟩ := runId_recordQueries _ _ _ _ h
  unfold Hints.childQueries
  rw [Compile.run_eq_withHash, keccak256With_keccakF1600]
  have h1' : Id.run (Compile.runWithHash (m := Id) keccak256 keccakF1600 (Hints.recordQueries
      (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement)))
      (Coverage.childVerifierStart seed c)) = some ((a, Q), st') := h1
  rw [h1']
  exact h3

/-- The Merkle hints of query steps: `Hints.levelHints` per step, at its height, query count and phase, the first
`first`. -/
def stepsHints : Bool → List (ℕ × List (ℕ × Opening)) → List (String × Hints.Entry)
  | _, [] => []
  | first, s :: ss => Hints.levelHints first s.1 s.2.length (s.2.map Prod.snd) ++ stepsHints false ss

/-- **`Hints.merkleHints` over query steps and the openings they consume** is `stepsHints`. -/
theorem merkleHints_steps : ∀ (first : Bool) (steps : List (ℕ × List (ℕ × Opening))) (rest : List (List Opening)),
    Hints.merkleHints first (steps.map stepQ) (steps.map (fun s => s.2.map Prod.snd) ++ rest) = stepsHints first steps
  | _, [], _ => by simp [Hints.merkleHints, stepsHints]
  | first, s :: ss, rest => by
    rw [List.map_cons, List.map_cons, List.cons_append, Hints.merkleHints, merkleHints_steps false ss rest, stepsHints,
      stepQ, List.length_map]


/-- **A child's Merkle hints are its query steps' levels**, on an accepting run. -/
theorem childMerkleHints_eq {bytecode : List K} {seed : Digest} {c : Child} {a : Bool}
    {st' : VerifierProgramState}
    (h : runId (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c) = some (a, st')) :
    Hints.merkleHints true (Hints.childQueries bytecode seed c) c.proof.openings =
      stepsHints true (Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
        (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c)) := by
  obtain ⟨-, -, -, -, h4⟩ := runId_recordQueries _ _ _ _ h
  have ho : c.proof.openings = (Coverage.childVerifierStart seed c).openings := rfl
  rw [childQueries_eq h, ho, h4, merkleHints_steps]

/-- A step at the positions `ps` of the phase `phase`, as long, is the level of `phase`. -/
theorem levelHints_zip (first : Bool) (depth : ℕ) {ps : List ℕ} {phase : List Opening}
    (hlen : phase.length = ps.length) :
    Hints.levelHints first depth (ps.zip phase).length ((ps.zip phase).map Prod.snd) =
      Hints.levelHints first depth ps.length phase := by
  rw [List.length_zip, List.map_snd_zip (by omega), hlen, Nat.min_self]
end
end LeanVM.Guest.B1.Whir
