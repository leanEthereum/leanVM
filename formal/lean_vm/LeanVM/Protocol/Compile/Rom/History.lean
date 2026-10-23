/-
  LeanVM.Protocol.Compile.Rom.History

  The interactive history of a compiled verifier's run under recorded random-oracle answers:
  the run with every commitment replaced by the word extracted from the answers, the seeded
  verifier, and the facts relating the history to the run.
-/

module

public import LeanVM.Protocol.Compile.Rom.Extract
public import LeanVM.Protocol.Compile.Prover

/-!
# The extracted history of a run

The random-oracle theorem bounds the probability that the compiled verifier accepts a proof
whose *extracted history* passes through a doomed boundary. The extracted history is the
interactive history (`List Ev`, `LeanVM.Protocol.Compile.Prog`) of the compiled run, with every
commitment's word read off the oracle's answers (`extract`): `xrun` is `run` with the hash
answered by a partial function `H : Bytes → Option Digest` (the oracle's answers, a missing
answer stopping the run), recording the scalars read, the challenges squeezed, the proofs of
work, the commitments with their extracted words, and the rows the openings return.

* `xrun_of_run`: an accepting run in `Option` has an extracted history.
* `xrun_prefix`: the history extends the history the run starts from.
* `answer_of_openAll`: when the answers are injective (no collision), the rows an accepted
  opening returns are the rows the extracted word holds (`answer`), so the extracted history of
  an accepted run is an interactive run of the program (`LeanVM.Protocol.Compile.Rom.Final`).

The verifier of the random-oracle theorem seeds its chain by the seeding `σ` and runs `P`
(`verify`); `extractedHistory` is the extracted history of that run, `[]` if it does not run
to a verdict.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom

@[expose] public section

/-! ## The seeded verifier -/

/-- The verifier of the random-oracle theorem: seed the chain by `σ`, then run `P` on the
proof. -/
def verify {m : Type → Type} [Monad m] (H : Bytes → m Digest) (σ : Seed) (P : Prog Bool)
    (π : Proof) : m Bool := do
  let seed ← σ.run H
  runProof H P seed π

/-! ## The run with its history -/

section XRun

variable (H : Bytes → Option Digest)

/-- The compiled run under the answers `H`, with its extracted history: every commitment holds
the word extracted for its root, every opening the rows it returned. `none` on rejection or on a
missing answer. -/
noncomputable def xrun {α : Type} : Prog α → St → List Ev → Option (α × St × List Ev)
  | .ret a, s, h => some (a, s, h)
  | .fail, _, _ => none
  | .read k, s, h => match s.stream with
    | [] => none
    | x :: xs => (absorbBlock H s.cv (blockOf x 1)).bind fun cv ↦
      xrun (k x) { s with cv := cv, stream := xs } (h ++ [Ev.read x])
  | .sample k, s, h => (absorbBlock H s.cv (blockOf 0 2)).bind fun cv ↦
      xrun (k (challengeOf cv)) { s with cv := cv } (h ++ [Ev.sample (challengeOf cv)])
  | .grind bits k, s, h => match s.stream with
    | [] => none
    | n :: xs => (absorbBlock H s.cv (blockOf 0 3)).bind fun base ↦
      (absorbBlock H base (blockOf n 4)).bind fun d ↦
      (absorbBlock H s.cv (blockOf n 4)).bind fun cv ↦
      if powOk bits n d then xrun k { s with cv := cv, stream := xs } (h ++ [Ev.grind bits])
      else none
  | .commit height width k, s, h => match s.stream with
    | x0 :: x1 :: xs => (absorbBlock H s.cv (blockOf x0 1)).bind fun cv0 ↦
      (absorbBlock H cv0 (blockOf x1 1)).bind fun cv1 ↦
      match digestOfScalars (x0, x1) with
      | some root =>
        xrun k { s with cv := cv1, stream := xs, roots := s.roots ++ [(root, height, width)] }
          (h ++ [Ev.commit height width (extract H root height width)])
      | none => none
    | _ => none
  | .query i ps k, s, h => match s.roots[i]? with
    | none => none
    | some (root, height, width) => match openAll H root height width ps s.openings with
      | some (some (rows, rest)) => xrun (k rows) { s with openings := rest } (h ++ [Ev.query rows])
      | _ => none

theorem absorbBlock_option (cv : Digest) (blk : Bytes) :
    absorbBlock (m := Option) H cv blk = H (digestBytes cv ++ blk) := rfl

/-- An accepting run in `Option` has an extracted history, ending at the same state. -/
theorem xrun_of_run {α : Type} :
    ∀ (p : Prog α) (s : St) (h : List Ev) {a : α} {s' : St},
      run (m := Option) H p s = some (some (a, s')) → ∃ hist, xrun H p s h = some (a, s', hist)
  | .ret a, s, h, _, _, hr => by
    simp only [run, pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨h, rfl⟩
  | .fail, s, h, _, _, hr => by simp [run, pure] at hr
  | .read k, s, h, _, _, hr => by
    simp only [run] at hr
    split at hr
    · simp [pure] at hr
    · rename_i x xs hs
      simp only [bind, Option.bind_eq_some_iff] at hr
      obtain ⟨cv, hcv, hr⟩ := hr
      obtain ⟨hist, hh⟩ := xrun_of_run (k x) _ (h ++ [Ev.read x]) hr
      refine ⟨hist, ?_⟩
      simp only [xrun, hs, hcv, Option.bind_some, hh]
  | .sample k, s, h, _, _, hr => by
    simp only [run, bind, Option.bind_eq_some_iff] at hr
    obtain ⟨cv, hcv, hr⟩ := hr
    obtain ⟨hist, hh⟩ := xrun_of_run _ _ (h ++ [Ev.sample (challengeOf cv)]) hr
    exact ⟨hist, by simp only [xrun, hcv, Option.bind_some, hh]⟩
  | .grind bits k, s, h, _, _, hr => by
    simp only [run] at hr
    split at hr
    · simp [pure] at hr
    · rename_i n xs hs
      simp only [bind, Option.bind_eq_some_iff] at hr
      obtain ⟨base, hb, d, hd, cv, hcv, hr⟩ := hr
      split at hr
      · rename_i hp
        obtain ⟨hist, hh⟩ := xrun_of_run k _ (h ++ [Ev.grind bits]) hr
        exact ⟨hist, by simp only [xrun, hs, hb, hd, hcv, Option.bind_some, hp, ↓reduceIte, hh]⟩
      · simp [pure] at hr
  | .commit height width k, s, h, _, _, hr => by
    simp only [run] at hr
    split at hr
    · rename_i x0 x1 xs hs
      simp only [bind, Option.bind_eq_some_iff] at hr
      obtain ⟨cv0, h0, cv1, h1, hr⟩ := hr
      split at hr
      · rename_i root hroot
        obtain ⟨hist, hh⟩ := xrun_of_run k _
          (h ++ [Ev.commit height width (extract H root height width)]) hr
        exact ⟨hist, by simp only [xrun, hs, h0, h1, Option.bind_some, hroot, hh]⟩
      · simp [pure] at hr
    · simp [pure] at hr
  | .query i ps k, s, h, _, _, hr => by
    simp only [run] at hr
    split at hr
    · simp [pure] at hr
    · rename_i root height width hroot
      simp only [bind, Option.bind_eq_some_iff] at hr
      obtain ⟨o, ho, hr⟩ := hr
      rcases o with _ | ⟨rows, rest⟩
      · simp [pure] at hr
      · obtain ⟨hist, hh⟩ := xrun_of_run (k rows) _ (h ++ [Ev.query rows]) hr
        exact ⟨hist, by simp only [xrun, hroot, ho, hh]⟩

/-- The extracted history extends the history the run starts from. -/
theorem xrun_prefix {α : Type} :
    ∀ (p : Prog α) (s : St) (h : List Ev) {a : α} {s' : St} {hist : List Ev},
      xrun H p s h = some (a, s', hist) → h <+: hist
  | .ret a, s, h, _, _, _, hr => by
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hr
    rw [← hr.2.2]
  | .fail, s, h, _, _, _, hr => by simp [xrun] at hr
  | .read k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, hr⟩ := hr
      exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
  | .sample k, s, h, _, _, _, hr => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨_, _, hr⟩ := hr
    exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
  | .grind bits k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, _, _, _, _, hr⟩ := hr
      split at hr
      · exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
      · simp at hr
  | .commit height width k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, _, _, hr⟩ := hr
      split at hr
      · exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
      · simp at hr
    · simp at hr
  | .query i ps k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · split at hr
      · exact (List.prefix_append _ _).trans (xrun_prefix _ _ _ hr)
      · simp at hr

end XRun

/-! ## Openings read the extracted rows -/

/-- With injective answers, the rows of an accepted run of openings are the rows the extracted
word holds at the positions. -/
theorem rows_of_openAll {H : Bytes → Option Digest} (hH : AnswersInj H) (root : Digest)
    (ht w : ℕ) :
    ∀ (ps : List ℕ) (os : List Opening) {rows : List (List K)} {rest : List Opening},
      openAll (m := Option) H root ht w ps os = some (some (rows, rest)) →
        rows = ps.map fun q ↦ extract H root ht w (q % 2 ^ ht)
  | [], os, rows, rest, h => by
    simp only [openAll, pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | _ :: _, [], _, _, h => by simp [openAll, pure] at h
  | q :: qs, o :: os, rows, rest, h => by
    simp only [openAll, bind, Option.bind_eq_some_iff] at h
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

/-- The roots a run holds, as the commitments of its extracted history. -/
def RootsInv (H : Bytes → Option Digest) (s : St) (h : List Ev) : Prop :=
  commits h = s.roots.map fun r ↦ (r.2.1, r.2.2, extract H r.1 r.2.1 r.2.2)

/-- **Openings answer from the extracted words.** With injective answers, an accepted opening
of the `i`-th root returns the rows the `i`-th commitment of the extracted history holds. -/
theorem answer_of_openAll {H : Bytes → Option Digest} (hH : AnswersInj H) {s : St}
    {h : List Ev} (hR : RootsInv H s h) {i : ℕ} {root : Digest} {ht w : ℕ}
    (hi : s.roots[i]? = some (root, ht, w)) {ps : List ℕ} {rows : List (List K)}
    {rest : List Opening}
    (ho : openAll (m := Option) H root ht w ps s.openings = some (some (rows, rest))) :
    answer h i ps = some rows := by
  rw [answer, hR, List.getElem?_map, hi, rows_of_openAll hH root ht w ps s.openings ho]
  rfl

theorem rootsInv_append_query {H : Bytes → Option Digest} {s : St} {h : List Ev}
    (hR : RootsInv H s h) (rows : List (List K)) (rest : List Opening) :
    RootsInv H { s with openings := rest } (h ++ [Ev.query rows]) := by
  simp only [RootsInv, commits_append, commits, List.append_nil]
  exact hR

theorem rootsInv_append_sample {H : Bytes → Option Digest} {s : St} {h : List Ev}
    (hR : RootsInv H s h) (c : E) (cv : Digest) :
    RootsInv H { s with cv := cv } (h ++ [Ev.sample c]) := by
  simp only [RootsInv, commits_append, commits, List.append_nil]
  exact hR

theorem rootsInv_append_read {H : Bytes → Option Digest} {s : St} {h : List Ev}
    (hR : RootsInv H s h) (x : E) (cv : Digest) (xs : List E) :
    RootsInv H { s with cv := cv, stream := xs } (h ++ [Ev.read x]) := by
  simp only [RootsInv, commits_append, commits, List.append_nil]
  exact hR

theorem rootsInv_append_grind {H : Bytes → Option Digest} {s : St} {h : List Ev}
    (hR : RootsInv H s h) (b : ℕ) (cv : Digest) (xs : List E) :
    RootsInv H { s with cv := cv, stream := xs } (h ++ [Ev.grind b]) := by
  simp only [RootsInv, commits_append, commits, List.append_nil]
  exact hR

theorem rootsInv_append_commit {H : Bytes → Option Digest} {s : St} {h : List Ev}
    (hR : RootsInv H s h) (root : Digest) (ht w : ℕ) (cv : Digest) (xs : List E) :
    RootsInv H { s with cv := cv, stream := xs, roots := s.roots ++ [(root, ht, w)] }
      (h ++ [Ev.commit ht w (extract H root ht w)]) := by
  simp only [RootsInv, commits_append, commits, List.map_append, List.map_cons, List.map_nil]
  rw [hR]

/-! ## The extracted history of the seeded verifier -/

/-- The extracted history of the seeded verifier's run on `π` under the answers `H`; `[]` if the
run stops before a verdict. -/
noncomputable def extractedHistory (H : Bytes → Option Digest) (σ : Seed) (P : Prog Bool)
    (π : Proof) : List Ev :=
  match σ.run H with
  | some seed => match xrun H P ⟨seed, π.stream, π.openings, []⟩ [] with
    | some (_, _, hist) => hist
    | none => []
  | none => []

/-- An accepting seeded run has an extracted history from the empty history, at the seed. -/
theorem xrun_of_verify {H : Bytes → Option Digest} {σ : Seed} {P : Prog Bool} {π : Proof}
    (hv : verify H σ P π = some true) :
    ∃ seed s, σ.run H = some seed ∧
      xrun H P ⟨seed, π.stream, π.openings, []⟩ [] = some (true, s, extractedHistory H σ P π) := by
  simp only [verify, bind, Option.bind_eq_some_iff] at hv
  obtain ⟨seed, hseed, hv⟩ := hv
  simp only [runProof, bind, Option.bind_eq_some_iff] at hv
  obtain ⟨r, hr, hv⟩ := hv
  rcases r with _ | ⟨_ | _, s⟩
  · simp [pure] at hv
  · simp [pure] at hv
  · obtain ⟨hist, hh⟩ := xrun_of_run H P _ [] hr
    refine ⟨seed, s, hseed, ?_⟩
    simp only [extractedHistory, hseed, hh]

/-- The extracted history of the seeded verifier's run of the node `p` on `π` from the history
`h₀`, under the answers `H`; `[]` if the run stops before a verdict. -/
noncomputable def extractedFrom (H : Bytes → Option Digest) (σ : Seed) (p : Prog Bool)
    (h₀ : List Ev) (π : Proof) : List Ev :=
  match σ.run H with
  | some seed => match xrun H p ⟨seed, π.stream, π.openings, []⟩ h₀ with
    | some (_, _, hist) => hist
    | none => []
  | none => []

/-- An accepting seeded run has an extracted history from any history, at the seed. -/
theorem xrun_of_verify_from {H : Bytes → Option Digest} {σ : Seed} {p : Prog Bool} {π : Proof}
    (h₀ : List Ev) (hv : verify H σ p π = some true) :
    ∃ seed s, σ.run H = some seed ∧
      xrun H p ⟨seed, π.stream, π.openings, []⟩ h₀ =
        some (true, s, extractedFrom H σ p h₀ π) := by
  simp only [verify, bind, Option.bind_eq_some_iff] at hv
  obtain ⟨seed, hseed, hv⟩ := hv
  simp only [runProof, bind, Option.bind_eq_some_iff] at hv
  obtain ⟨r, hr, hv⟩ := hv
  rcases r with _ | ⟨_ | _, s⟩
  · simp [pure] at hv
  · simp [pure] at hv
  · obtain ⟨hist, hh⟩ := xrun_of_run H p _ h₀ hr
    refine ⟨seed, s, hseed, ?_⟩
    simp only [extractedFrom, hseed, hh]

end
end LeanVM.Protocol.Compile.Rom
