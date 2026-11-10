/-
  LeanVM.Protocol.Compile.Rom.Ideal

  The ideal failure probability of a verifier program against an interactive strategy, every
  challenge uniform and independent, and the honest prover's transcript along a program: where
  that transcript passes every check of a program refining the honest one, the compiled verifier
  of that program accepts the honest proof.
-/

module

public import LeanVM.Protocol.Compile.Prover
public import LeanVM.Guest.LimitsNZ

/-!
# The ideal failure probability and the honest transcript

`S.failFrom P h g`: the probability that `P`, run from the history `h` against the strategy `S`,
fails, every challenge uniform in `E` and independent of the others (`g`, a challenge already
drawn and waiting, as a proof of work's permutation leaves one). The proof of work is free here:
its challenge is drawn at the `grind` node and taken at the next `sample`.

`traceOk H F S fuel P sp h`: the honest prover's run from the sponge `sp` and the history `h`,
with the hash `H` and the permutation `F`, passes every check of `P` (its proofs of work find
their nonces, nothing waits where `P` absorbs, every committed word is well shaped, every opening
is of a committed word, and `P` returns `true`). For `P` refining the program `Q` the prover
follows (`Limits.Refines`), the compiled verifier of `P` then accepts the prover's proof
(`run_proveFrom_trace`, `runProof_prove_trace`): the transcript's challenges are the ones the
verifier squeezes, so the only failures left are those of the interactive run.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol
open scoped ENNReal

@[expose] public section

/-! ## The ideal failure probability -/

/-- The uniform average over `E`; irreducible, so that no unification unfolds it into a sum over
the `2^128` elements. -/
@[irreducible] noncomputable def avgE (f : E → ℝ≥0∞) : ℝ≥0∞ := (∑ c : E, f c) / Fintype.card E

/-- `|E|⁻¹`, the probability of one value of a uniform challenge. -/
@[irreducible] noncomputable def epsE : ℝ≥0∞ := (Fintype.card E : ℝ≥0∞)⁻¹

namespace Strategy

open Classical in
/-- **The ideal failure probability** of a program from a history, every challenge uniform in `E`
and independent, the challenge `g` waiting; the verifier's run fails where something is
absorbed while a challenge waits. -/
noncomputable def failFrom (S : Strategy) : VerifierProgram Bool → List Ev → Option E → ℝ≥0∞
  | .ret b, _, _ => if b = true then 0 else 1
  | .fail, _, _ => 1
  | .read k, h, g => if g.isSome then 1 else
      failFrom S (k (S.msg h)) (h ++ [Ev.read (S.msg h)]) none
  | .sample k, h, g => match g with
    | some c => failFrom S (k c) (h ++ [Ev.sample c]) none
    | none => avgE fun c ↦ failFrom S (k c) (h ++ [Ev.sample c]) none
  | .grind b k, h, g => if g.isSome then 1 else
      avgE fun c ↦ failFrom S k (h ++ [Ev.grind b]) (some c)
  | .commit ht w k, h, g => if g.isSome ∨ ¬ WellShaped w (S.word h) then 1 else
      failFrom S k (h ++ [Ev.commit ht w (S.word h)]) none
  | .query i ps k, h, g => match answer h i ps with
    | some rows => failFrom S (k rows) (h ++ [Ev.query rows]) g
    | none => 1

end Strategy

/-! ## The honest transcript -/

section Trace

variable (H : Bytes → Digest) (F : KeccakState → KeccakState)

/-- **The honest prover's transcript passes every check of `P`**, from the sponge `sp` and the
history `h`: the prover's moves, its sponge and its proof-of-work searches as `proveFrom` makes
them. -/
def traceOk (S : Strategy) (fuel : ℕ) : VerifierProgram Bool → Sponge → List Ev → Prop
  | .ret b, _, _ => b = true
  | .fail, _, _ => False
  | .read k, sp, h => sp.ground = none ∧
      traceOk S fuel (k (S.msg h)) (absorbI F sp (S.msg h) dsObserve) (h ++ [Ev.read (S.msg h)])
  | .sample k, sp, h =>
      traceOk S fuel (k (squeezeI F sp).1) (squeezeI F sp).2 (h ++ [Ev.sample (squeezeI F sp).1])
  | .grind b k, sp, h => sp.ground = none ∧ ∃ n, findNonce F b sp fuel = some n ∧
      traceOk S fuel k (powStep F sp n).2 (h ++ [Ev.grind b])
  | .commit ht w k, sp, h => sp.ground = none ∧ WellShaped w (S.word h) ∧
      traceOk S fuel k
        (absorbI F (absorbI F sp (digestHalves (treeRoot H ht (S.word h))).1 dsObserve)
          (digestHalves (treeRoot H ht (S.word h))).2 dsObserve)
        (h ++ [Ev.commit ht w (S.word h)])
  | .query i ps k, sp, h => ∃ rows, answer h i ps = some rows ∧
      traceOk S fuel (k rows) sp (h ++ [Ev.query rows])

/-- **The simulation, for a refining program.** If the honest prover's run along `p` from `h` at
the sponge `sp` outputs `(xs, os)` and its transcript passes every check of `p'`, a refinement of
`p`, the compiled verifier of `p'` from sponge `sp` with the roots of `h`'s trees accepts on any
stream and openings that start with `xs` and `os`, leaving exactly what follows them. -/
theorem run_proveFrom_trace (S : Strategy) (fuel : ℕ) {p' p : VerifierProgram Bool}
    (hR : Guest.Limits.Refines p' p) :
    ∀ (h : List Ev) (sp : Sponge) (xs : List E) (os : List (List Opening)) (restS : List E)
      (restO : List (List Opening)),
      traceOk H F S fuel p' sp h → (∀ c ∈ commits h, WellShaped c.2.1 c.2.2) →
      proveFrom H F S fuel p sp h = some (xs, os) →
      ∃ s', runWithHash (m := Id) H F p' ⟨sp, xs ++ restS, os ++ restO, rootsOf H (commits h)⟩ =
          some (true, s') ∧ s'.stream = restS ∧ s'.openings = restO := by
  induction hR with
  | fail p =>
    intro h sp xs os restS restO ht
    exact absurd ht id
  | ret b =>
    intro h sp xs os restS restO ht _ hp
    simp only [traceOk] at ht
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨_, by rw [ht]; rfl, rfl, rfl⟩
  | @read k k' _ ih =>
    intro h sp xs os restS restO ht hws hp
    obtain ⟨hg0, ht⟩ := ht
    simp only [proveFrom] at hp
    obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hws' : ∀ c ∈ commits (h ++ [Ev.read (S.msg h)]), WellShaped c.2.1 c.2.2 := by
      simpa [commits_append, commits] using hws
    obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ _ t.1 t.2 restS restO ht hws' htt
    refine ⟨s', ?_, hs1, hs2⟩
    rw [← hrun]
    simp [runWithHash, commits_append, commits, hg0]
    rfl
  | @sample k k' _ ih =>
    intro h sp xs os restS restO ht hws hp
    simp only [proveFrom] at hp
    have hws' : ∀ c ∈ commits (h ++ [Ev.sample (squeezeI F sp).1]), WellShaped c.2.1 c.2.2 := by
      simpa [commits_append, commits] using hws
    obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ _ xs os restS restO ht hws' hp
    refine ⟨s', ?_, hs1, hs2⟩
    rw [← hrun]
    simp [runWithHash, commits_append, commits]
    rfl
  | @grind b k k' _ ih =>
    intro h sp xs os restS restO ht hws hp
    obtain ⟨hg0, n, hn, ht⟩ := ht
    simp only [proveFrom, hn] at hp
    obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hws' : ∀ c ∈ commits (h ++ [Ev.grind b]), WellShaped c.2.1 c.2.2 := by
      simpa [commits_append, commits] using hws
    obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ t.1 t.2 restS restO ht hws' htt
    refine ⟨s', ?_, hs1, hs2⟩
    have hpow := powOk_of_findNonce F hn
    rw [← hrun]
    simp only [commits_append, commits, List.append_nil] at *
    simp only [runWithHash, List.cons_append, hg0]
    show (if powOk b (powStep F sp n).1 = true then _ else pure none) = _
    simp only [hpow, ↓reduceIte]
    rfl
  | @commit ht w k k' _ ih =>
    intro h sp xs os restS restO htr hws hp
    obtain ⟨hg0, hw, htr⟩ := htr
    simp only [proveFrom] at hp
    obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hws' : ∀ c ∈ commits (h ++ [Ev.commit ht w (S.word h)]), WellShaped c.2.1 c.2.2 := by
      simp only [commits_append, commits, List.mem_append, List.mem_singleton]
      rintro c (hc | rfl)
      · exact hws c hc
      · exact hw
    obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ t.1 t.2 restS restO htr hws' htt
    refine ⟨s', ?_, hs1, hs2⟩
    rw [← hrun]
    have hroots : rootsOf H (commits (h ++ [Ev.commit ht w (S.word h)])) =
        rootsOf H (commits h) ++ [(treeRoot H ht (S.word h), ht, w)] := by
      simp [rootsOf, commits_append, commits]
    simp only [runWithHash, List.cons_append, hg0]
    rw [digestOfScalars_digestScalars, hroots]
    rfl
  | @query i ps k k' _ ih =>
    intro h sp xs os restS restO htr hws hp
    obtain ⟨rows, hans, htr⟩ := htr
    simp only [proveFrom] at hp
    split at hp
    · rename_i hc
      simp [answer, hc] at hans
    · rename_i ht w word hc
      obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hrows : rows = ps.map fun q ↦ word (q % 2 ^ ht) := by
        simp only [answer, hc, Option.map_some, Option.some.injEq] at hans
        exact hans.symm
      subst hrows
      have hws' : ∀ c ∈ commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]),
          WellShaped c.2.1 c.2.2 := by
        simpa [commits_append, commits] using hws
      have hw : WellShaped w word := hws _ (List.mem_of_getElem? hc)
      obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ _ t.1 t.2 restS restO htr hws' htt
      refine ⟨s', ?_, hs1, hs2⟩
      rw [← hrun]
      have hroot : (rootsOf H (commits h))[i]? = some (treeRoot H ht word, ht, w) := by
        simp [rootsOf, hc]
      have hopen := openPhase_openingAt H hw (height := ht) ps
      simp only [runWithHash, hroot, List.cons_append]
      simp only [bind] at hopen ⊢
      rw [hopen]
      simp [commits_append, commits]

/-- **The compiled verifier of a refining program accepts the honest proof** wherever the honest
transcript passes its checks. -/
theorem runProof_prove_trace (S : Strategy) (fuel : ℕ) {P' P : VerifierProgram Bool}
    (hR : Guest.Limits.Refines P' P) (seed : KeccakState) {π : Proof}
    (ht : traceOk H F S fuel P' ⟨seed, [], none⟩ [])
    (hπ : prove H F P S seed fuel = some π) :
    runProofWithHash (m := Id) H F P' seed π = true := by
  obtain ⟨t, htt, rfl⟩ := Option.map_eq_some_iff.mp hπ
  obtain ⟨s', hrun, hs1, hs2⟩ :=
    run_proveFrom_trace H F S fuel hR [] ⟨seed, [], none⟩ t.1 t.2 [] [] ht (by simp [commits]) htt
  simp only [List.append_nil] at hrun
  simp only [runProofWithHash, bind]
  show (match runWithHash (m := Id) H F P' ⟨⟨seed, [], none⟩, t.1, t.2, rootsOf H (commits [])⟩ with
    | some (true, s) => _ | _ => _) = true
  rw [hrun]
  simp [hs1, hs2]
  rfl

end Trace

end
end LeanVM.Protocol.Compile
