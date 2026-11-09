/-
  LeanVM.Protocol.Compile.Rom.History

  The interactive history of a compiled verifier's run under recorded random-oracle answers:
  the run with every commitment replaced by the word extracted from the answers, the seeded
  verifier, and the facts relating the history to the run.
-/

module

public import LeanVM.Protocol.Compile.Rom.Extract
public import LeanVM.Protocol.RunWithHash

/-!
# The extracted history of a run

The random-oracle theorem bounds the probability that the compiled verifier accepts a proof
whose *extracted history* passes through a doomed boundary. The extracted history is the
interactive history (`List Ev`, `LeanVM.Protocol.Compile.VerifierProgram`) of the compiled run, with
every
commitment's word read off the oracles' answers (`extract`): `xrun` is `run` with the hash and
the permutation answered by partial functions `H : Bytes → Option Digest` and
`F : KState → Option KState` (the oracles' answers, a missing answer stopping the run), recording the scalars read, the challenges squeezed, the proofs of
work, the commitments with their extracted words, and the rows the openings return.

* `xrun_of_run`: an accepting run in `Option` has an extracted history.
* `xrun_prefix`: the history extends the history the run starts from.
* `answer_of_openPhase`: when the answers are injective (no collision), the rows an accepted
  phase of openings returns are the rows the extracted word holds (`answer`), so the extracted history of
  an accepted run is an interactive run of the program (`LeanVM.Protocol.Compile.Rom.Final`).

The verifier of the random-oracle theorem seeds its sponge by the seeding `σ` and runs `P`
(`verify`); `extractedFrom` is the extracted history of that run from a given history,
`[]` if it does not run to a verdict.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom

@[expose] public section

/-! ## The seeded verifier -/

/-- The verifier of the random-oracle theorem: seed the sponge by `σ`, then run `P` on the
proof. -/
def verify {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState) (σ : Seed)
    (P : VerifierProgram Bool) (π : Proof) : m Bool := do
  let seed ← σ.run H F
  runProofWithHash H F P seed π

/-! ## The run with its history -/

section XRun

variable (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)

/-- The compiled run under the answers `H` and `F`, with its extracted history: every commitment
holds the word extracted for its root, every opening the rows it returned. `none` on rejection or
on a missing answer. -/
noncomputable def xrun {α : Type} : VerifierProgram α → VerifierProgramState → List Ev → Option (α ×
    VerifierProgramState × List Ev)
  | .ret a, s, h => some (a, s, h)
  | .fail, _, _ => none
  | .read k, s, h => match s.stream, s.sponge.ground with
    | x :: xs, none => (absorb (m := Option) F s.sponge x dsObserve).bind fun sp ↦
      xrun (k x) { s with sponge := sp, stream := xs } (h ++ [Ev.read x])
    | _, _ => none
  | .sample k, s, h => (squeeze (m := Option) F s.sponge).bind fun r ↦
      xrun (k r.1) { s with sponge := r.2 } (h ++ [Ev.sample r.1])
  | .grind bits k, s, h => match s.stream, s.sponge.ground with
    | n :: xs, none => (absorbNonce (m := Option) F s.sponge n).bind fun r ↦
      if powOk bits r.1 then
        xrun k { s with sponge := r.2, stream := xs } (h ++ [Ev.grind bits])
      else none
    | _, _ => none
  | .commit height width k, s, h => match s.stream, s.sponge.ground with
    | x0 :: x1 :: xs, none => (absorb (m := Option) F s.sponge x0 dsObserve).bind fun sp0 ↦
      (absorb (m := Option) F sp0 x1 dsObserve).bind fun sp1 ↦
      let root := digestFromHalves (x0, x1)
      xrun k { s with sponge := sp1, stream := xs, roots := s.roots ++ [(root, height, width)] }
        (h ++ [Ev.commit height width (extract H root height width)])
    | _, _ => none
  | .query i ps k, s, h => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest =>
      match openPhaseWithHash H root height width ps phase with
      | some (some rows) => xrun (k rows) { s with openings := rest } (h ++ [Ev.query rows])
      | _ => none
    | _, _ => none

/-- An accepting run in `Option` has an extracted history, ending at the same state. -/
theorem xrun_of_run {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev) {a : α} {s' :
        VerifierProgramState},
      runWithHash (m := Option) H F p s = some (some (a, s')) → ∃ hist, xrun H F p s h = some (a, s', hist)
  | .ret a, s, h, _, _, hr => by
    simp only [runWithHash, pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨h, rfl⟩
  | .fail, s, h, _, _, hr => by simp [runWithHash, pure] at hr
  | .read k, s, h, _, _, hr => by
    simp only [runWithHash] at hr
    split at hr
    · rename_i x xs hs hg
      simp only [bind, Option.bind_eq_some_iff] at hr
      obtain ⟨sp, hsp, hr⟩ := hr
      obtain ⟨hist, hh⟩ := xrun_of_run (k x) _ (h ++ [Ev.read x]) hr
      refine ⟨hist, ?_⟩
      simp only [xrun, hs, hg, hsp, Option.bind_some, hh]
    · simp [pure] at hr
  | .sample k, s, h, _, _, hr => by
    simp only [runWithHash, bind, Option.bind_eq_some_iff] at hr
    obtain ⟨r, hr0, hr⟩ := hr
    obtain ⟨hist, hh⟩ := xrun_of_run _ _ (h ++ [Ev.sample r.1]) hr
    exact ⟨hist, by simp only [xrun, hr0, Option.bind_some, hh]⟩
  | .grind bits k, s, h, _, _, hr => by
    simp only [runWithHash] at hr
    split at hr
    · rename_i n xs hs hg
      simp only [bind, Option.bind_eq_some_iff] at hr
      obtain ⟨r, hr0, hr⟩ := hr
      split at hr
      · rename_i hp
        obtain ⟨hist, hh⟩ := xrun_of_run k _ (h ++ [Ev.grind bits]) hr
        exact ⟨hist, by simp only [xrun, hs, hg, hr0, Option.bind_some, hp, ↓reduceIte, hh]⟩
      · simp [pure] at hr
    · simp [pure] at hr
  | .commit height width k, s, h, _, _, hr => by
    simp only [runWithHash] at hr
    split at hr
    · rename_i x0 x1 xs hs hg
      simp only [bind, Option.bind_eq_some_iff] at hr
      obtain ⟨sp0, h0, sp1, h1, hr⟩ := hr
      obtain ⟨hist, hh⟩ := xrun_of_run k _
        (h ++ [Ev.commit height width (extract H (digestFromHalves (x0, x1)) height width)]) hr
      exact ⟨hist, by simp only [xrun, hs, hg, h0, h1, Option.bind_some, hh]⟩
    · simp [pure] at hr
  | .query i ps k, s, h, _, _, hr => by
    simp only [runWithHash] at hr
    split at hr
    · next root height width phase rest hroot hopen =>
      simp only [bind, Option.bind_eq_some_iff] at hr
      obtain ⟨o, ho, hr⟩ := hr
      rcases o with _ | rows
      · simp [pure] at hr
      · obtain ⟨hist, hh⟩ := xrun_of_run (k rows) _ (h ++ [Ev.query rows]) hr
        exact ⟨hist, by simp only [xrun, hroot, hopen, ho, hh]⟩
    · simp [pure] at hr

/-- The extracted history extends the history the run starts from. -/
theorem xrun_prefix {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev) {a : α} {s' :
        VerifierProgramState} {hist : List Ev},
      xrun H F p s h = some (a, s', hist) → h <+: hist
  | .ret a, s, h, _, _, _, hr => by
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hr
    rw [← hr.2.2]
  | .fail, s, h, _, _, _, hr => by simp [xrun] at hr
  | .read k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, hr⟩ := hr
      exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
    · simp at hr
  | .sample k, s, h, _, _, _, hr => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨_, _, hr⟩ := hr
    exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
  | .grind bits k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, hr⟩ := hr
      split at hr
      · exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
      · simp at hr
    · simp at hr
  | .commit height width k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, _, _, hr⟩ := hr
      exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
    · simp at hr
  | .query i ps k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · split at hr
      · exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
      · simp at hr
    · simp at hr

end XRun

/-! ## Openings read the extracted rows -/

/-- With injective answers, the rows of an accepted run of openings are the rows the extracted
word holds at the positions. -/
theorem rows_of_openAll {H : Bytes → Option Digest} (hH : AnswersInj H) (root : Digest)
    (ht w : ℕ) :
    ∀ (ps : List ℕ) (os : List Opening) {rows : List (List K)} {rest : List Opening},
      openAllWithHash (m := Option) H root ht w ps os = some (some (rows, rest)) →
        rows = ps.map fun q ↦ extract H root ht w (q % 2 ^ ht)
  | [], os, rows, rest, h => by
    simp only [openAllWithHash, pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | _ :: _, [], _, _, h => by simp [openAllWithHash, pure] at h
  | q :: qs, o :: os, rows, rest, h => by
    simp only [openAllWithHash, bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b
    · simp [pure] at h
    · simp only [↓reduceIte, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨r, hr, hrows⟩ := h
      rcases r with _ | ⟨rows', rest'⟩
      · simp at hrows
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrows
        rw [← hrows.1, List.map_cons, extract_eq_of_openOne hH hb,
          rows_of_openAll hH root ht w qs os hr]

/-- With injective answers, the rows of an accepted phase are the rows the extracted word holds
at the positions. -/
theorem rows_of_openPhase {H : Bytes → Option Digest} (hH : AnswersInj H) (root : Digest)
    (ht w : ℕ) (ps : List ℕ) (phase : List Opening) {rows : List (List K)}
    (h : openPhaseWithHash (m := Option) H root ht w ps phase = some (some rows)) :
    rows = ps.map fun q ↦ extract H root ht w (q % 2 ^ ht) := by
  unfold openPhaseWithHash at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨o, ho, h⟩ := h
    rcases o with _ | ⟨rows', rest⟩
    · simp [pure] at h
    · simp only [pure, Option.some.injEq] at h
      rw [← h]
      exact rows_of_openAll hH root ht w ps phase ho
  · simp [pure] at h

/-- The roots a run holds, as the commitments of its extracted history. -/
def RootsInv (H : Bytes → Option Digest) (s : VerifierProgramState) (h : List Ev) : Prop :=
  commits h = s.roots.map fun r ↦ (r.2.1, r.2.2, extract H r.1 r.2.1 r.2.2)

/-- **Openings answer from the extracted words.** With injective answers, an accepted phase
of openings of the `i`-th root returns the rows the `i`-th commitment of the extracted history
holds. -/
theorem answer_of_openPhase {H : Bytes → Option Digest} (hH : AnswersInj H)
    {s : VerifierProgramState} {h : List Ev} (hR : RootsInv H s h) {i : ℕ} {root : Digest}
    {ht w : ℕ} (hi : s.roots[i]? = some (root, ht, w)) {ps : List ℕ} {rows : List (List K)}
    {phase : List Opening}
    (ho : openPhaseWithHash (m := Option) H root ht w ps phase = some (some rows)) :
    answer h i ps = some rows := by
  rw [answer, hR, List.getElem?_map, hi, rows_of_openPhase hH root ht w ps phase ho]
  rfl

theorem rootsInv_append_query {H : Bytes → Option Digest} {s : VerifierProgramState} {h : List Ev}
    (hR : RootsInv H s h) (rows : List (List K)) (rest : List (List Opening)) :
    RootsInv H { s with openings := rest } (h ++ [Ev.query rows]) := by
  simp only [RootsInv, commits_append, commits, List.append_nil]
  exact hR

theorem rootsInv_append_sample {H : Bytes → Option Digest} {s : VerifierProgramState} {h : List Ev}
    (hR : RootsInv H s h) (c : E) (sp : Sponge) :
    RootsInv H { s with sponge := sp } (h ++ [Ev.sample c]) := by
  simp only [RootsInv, commits_append, commits, List.append_nil]
  exact hR

theorem rootsInv_append_read {H : Bytes → Option Digest} {s : VerifierProgramState} {h : List Ev}
    (hR : RootsInv H s h) (x : E) (sp : Sponge) (xs : List E) :
    RootsInv H { s with sponge := sp, stream := xs } (h ++ [Ev.read x]) := by
  simp only [RootsInv, commits_append, commits, List.append_nil]
  exact hR

theorem rootsInv_append_grind {H : Bytes → Option Digest} {s : VerifierProgramState} {h : List Ev}
    (hR : RootsInv H s h) (b : ℕ) (sp : Sponge) (xs : List E) :
    RootsInv H { s with sponge := sp, stream := xs } (h ++ [Ev.grind b]) := by
  simp only [RootsInv, commits_append, commits, List.append_nil]
  exact hR

theorem rootsInv_append_commit {H : Bytes → Option Digest} {s : VerifierProgramState} {h : List Ev}
    (hR : RootsInv H s h) (root : Digest) (ht w : ℕ) (sp : Sponge) (xs : List E) :
    RootsInv H { s with sponge := sp, stream := xs, roots := s.roots ++ [(root, ht, w)] }
      (h ++ [Ev.commit ht w (extract H root ht w)]) := by
  simp only [RootsInv, commits_append, commits, List.map_append, List.map_cons, List.map_nil]
  rw [hR]

/-! ## The extracted history of the seeded verifier -/

/-- The extracted history of the seeded verifier's run of the node `p` on `π` from the history
`h₀`, under the answers `H` and `F`; `[]` if the run stops before a verdict. -/
noncomputable def extractedFrom (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)
    (σ : Seed) (p : VerifierProgram Bool) (h₀ : List Ev) (π : Proof) : List Ev :=
  match σ.run H F with
  | some seed => match xrun H F p ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ h₀ with
    | some (_, _, hist) => hist
    | none => []
  | none => []

/-- The extracted history of the seeded verifier's run from the empty history. -/
noncomputable def extractedHistory (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)
    (σ : Seed) (P : VerifierProgram Bool) (π : Proof) : List Ev :=
  extractedFrom H F σ P [] π

/-- An accepting seeded run has an extracted history from any history, at the seed. -/
theorem xrun_of_verify_from {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState} {σ : Seed}
    {p : VerifierProgram Bool} {π : Proof} (h₀ : List Ev) (hv : verify H F σ p π = some true) :
    ∃ seed s, σ.run H F = some seed ∧
      xrun H F p ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ h₀ =
        some (true, s, extractedFrom H F σ p h₀ π) := by
  simp only [verify, bind, Option.bind_eq_some_iff] at hv
  obtain ⟨seed, hseed, hv⟩ := hv
  simp only [runProofWithHash, bind, Option.bind_eq_some_iff] at hv
  obtain ⟨r, hr, hv⟩ := hv
  rcases r with _ | ⟨_ | _, s⟩
  · simp [pure] at hv
  · simp [pure] at hv
  · obtain ⟨hist, hh⟩ := xrun_of_run H F p _ h₀ hr
    refine ⟨seed, s, hseed, ?_⟩
    simp only [extractedFrom, hseed, hh]

/-- An accepting seeded run has an extracted history from the empty history, at the seed. -/
theorem xrun_of_verify {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState} {σ : Seed}
    {P : VerifierProgram Bool} {π : Proof} (hv : verify H F σ P π = some true) :
    ∃ seed s, σ.run H F = some seed ∧
      xrun H F P ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ [] =
        some (true, s, extractedHistory H F σ P π) :=
  xrun_of_verify_from [] hv

end
end LeanVM.Protocol.Compile.Rom
