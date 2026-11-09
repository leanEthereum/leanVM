/-
  LeanVM.Guest.B1.VerifySub.NoCommit

  The deferring verifier's phases before its stacked opening commit nothing and query nothing:
  a carried run of one keeps the roots and the openings.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.VerifySub.NZRun
public import LeanVM.Guest.B1.VerifySub.Split

/-!
# Phases without commitments

`NoCommit p`: on every path, `p` has no `commit` and no `query` step. It is closed under `bind`
(`NoCommit.bind`), and a carried run of such a program keeps the roots and the openings
(`NoCommit.runF`). Every phase of the deferring verifier before its stacked opening but the
stack's commitment is one: `readAnnouncedSizes`, the bus's GKR (`Tables.gkrPhase`), the bus's rest,
the table sumcheck and the public input (`Tables.tablesSeg`), the Keccak reduction (`keccakSeg`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- No `commit` and no `query` on any path (the recursion). -/
def NoCommitA {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoCommitA (k x)
  | .sample k => ∀ c, NoCommitA (k c)
  | .grind _ k => NoCommitA k
  | .commit _ _ _ => False
  | .query _ _ _ => False

/-- **No `commit` and no `query` on any path.** Irreducible: unfolding it on a large program would
evaluate the program. -/
@[irreducible] def NoCommit {α : Type} (p : VerifierProgram α) : Prop := NoCommitA p

theorem noCommit_iff {α : Type} (p : VerifierProgram α) : NoCommit p ↔ NoCommitA p := by
  unfold NoCommit; rfl

theorem NoCommitA.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} (hp :
    NoCommitA p)
    (hf : ∀ a, NoCommitA (f a)) : NoCommitA (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit _ _ _ _ => exact hp.elim
  | query _ _ _ _ => exact hp.elim

theorem NoCommit.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} (hp :
    NoCommit p)
    (hf : ∀ a, NoCommit (f a)) : NoCommit (p.bind f) :=
  (noCommit_iff _).2 (NoCommitA.bind ((noCommit_iff _).1 hp) fun a ↦ (noCommit_iff _).1 (hf a))

theorem NoCommitA.runF {α : Type} (p : VerifierProgram α) : NoCommitA p → ∀ (st : Whir.FSt) (a : α)
    (st' : Whir.FSt), Whir.runF p st = some (a, st') →
      st'.roots = st.roots ∧ st'.openings = st.openings := by
  induction p with
  | ret b =>
    intro _ st a st' h
    simp only [Whir.runF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | fail => intro _ st a st' h; simp [Whir.runF] at h
  | read k ih =>
    intro hp st a st' h
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => simp [Whir.runF] at h
    | cons x xs =>
      simp only [Whir.runF] at h
      exact ih x (hp x) ⟨s.absorb x dsObserve, xs, os, R⟩ a st' h
  | sample k ih =>
    intro hp st a st' h
    exact ih _ (hp _) ⟨st.sponge.squeeze.2, st.stream, st.openings, st.roots⟩ a st' h
  | grind b k ih =>
    intro hp st a st' h
    obtain ⟨s, stream, os, R⟩ := st
    cases stream with
    | nil => simp [Whir.runF] at h
    | cons n xs =>
      simp only [Whir.runF] at h
      split at h
      · exact ih hp ⟨(s.absorb n dsPowNonce).squeeze.2, xs, os, R⟩ a st' h
      · simp at h
  | commit _ _ _ _ => intro hp; exact hp.elim
  | query _ _ _ _ => intro hp; exact hp.elim

/-- **A carried run without commitments keeps the roots and the openings.** -/
theorem NoCommit.runF {α : Type} {p : VerifierProgram α} (hp : NoCommit p) {st : Whir.FSt} {a : α}
    {st' : Whir.FSt} (h : Whir.runF p st = some (a, st')) :
    st'.roots = st.roots ∧ st'.openings = st.openings :=
  NoCommitA.runF p ((noCommit_iff _).1 hp) st a st' h

/-! ## The primitives -/

theorem noCommit_ret {α : Type} (a : α) : NoCommit (VerifierProgram.ret a) := (noCommit_iff _).2
    trivial

theorem noCommit_fail {α : Type} : NoCommit (VerifierProgram.fail : VerifierProgram α) :=
    (noCommit_iff _).2 trivial

theorem noCommit_readE : NoCommit VerifierProgram.readScalar := (noCommit_iff _).2 fun _ ↦ trivial

theorem noCommit_sampleE : NoCommit VerifierProgram.sampleChallenge := (noCommit_iff _).2 fun _ ↦
    trivial

theorem noCommit_readN : ∀ n, NoCommit (VerifierProgram.readScalars n)
  | 0 => noCommit_ret _
  | n + 1 => by
    simp only [VerifierProgram.readScalars, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommit.bind noCommit_readE fun _ ↦ ?_
    refine NoCommit.bind (noCommit_readN n) fun _ ↦ ?_
    exact noCommit_ret _

theorem noCommit_sampleN : ∀ n, NoCommit (VerifierProgram.sampleChallenges n)
  | 0 => noCommit_ret _
  | n + 1 => by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
    refine NoCommit.bind (noCommit_sampleN n) fun _ ↦ ?_
    exact noCommit_ret _

theorem noCommit_require (c : Prop) [Decidable c] : NoCommit (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split
  · exact noCommit_ret _
  · exact noCommit_fail

theorem noCommit_liftOption {α : Type} (o : Option α) : NoCommit (liftOption o) := by
  cases o
  · exact noCommit_fail
  · exact noCommit_ret _

/-- A search for `NoCommit` through binds, the primitives, matches and `if`s. -/
macro "nc" : tactic => `(tactic| repeat (first
  | (refine NoCommit.bind ?_ fun _ ↦ ?_)
  | exact noCommit_ret _
  | exact noCommit_readE
  | exact noCommit_sampleE
  | exact noCommit_readN _
  | exact noCommit_sampleN _
  | exact noCommit_require _
  | exact noCommit_liftOption _
  | exact noCommit_fail
  | (simp only [Prog.bind_eq, Prog.pure_eq])
  | split
  | (intro _)))

theorem noCommit_sumcheckRoundPoly (count : ℕ) (claim : E) (e : Option E) :
    NoCommit (sumcheckRoundPoly count claim e) := by
  cases e <;> (unfold sumcheckRoundPoly; nc)

theorem noCommit_sumcheck (claim : E) (count : ℕ) : ∀ eqs : List (Option E),
    NoCommit (sumcheck claim count eqs) := by
  intro eqs
  induction eqs generalizing claim with
  | nil => exact noCommit_ret _
  | cons e eqs ih =>
    unfold sumcheck
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommit.bind (noCommit_sumcheckRoundPoly _ _ _) fun _ ↦ ?_
    refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
    exact NoCommit.bind (ih _) fun _ ↦ noCommit_ret _

/-! ## The phases -/

theorem noCommit_readSizes (bytecode : List K) : NoCommit (readAnnouncedSizes bytecode) := by
  unfold readAnnouncedSizes
  nc

theorem noCommit_gkrStep (step : ℕ) (s : GkrState) : NoCommit (gkrStep step s) := by
  unfold gkrStep
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_sumcheck _ _ _) fun _ ↦ ?_
  nc

theorem noCommit_gkrLayers : ∀ (n : ℕ) (s : GkrState), NoCommit (gkrLayers n s)
  | 0, _ => noCommit_ret _
  | 1, s => by
    unfold gkrLayers
    simp only [VerifierProgram.bind_eq]
    exact NoCommit.bind (noCommit_gkrStep _ _) fun _ ↦ noCommit_gkrLayers 0 _
  | n + 2, s => by
    unfold gkrLayers
    split
    · simp only [VerifierProgram.bind_eq]
      exact NoCommit.bind (noCommit_gkrStep _ _) fun _ ↦ noCommit_gkrLayers (n + 1) _
    · simp only [VerifierProgram.bind_eq]
      exact NoCommit.bind (noCommit_gkrStep _ _) fun _ ↦ noCommit_gkrLayers n _

theorem noCommit_gkrPhase (depth : ℕ) : NoCommit (Tables.gkrPhase depth) := by
  unfold Tables.gkrPhase verifyGkrGrandProducts
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc]
  refine NoCommit.bind noCommit_readE fun _ ↦ NoCommit.bind noCommit_readE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_gkrLayers _ _) fun _ ↦ ?_
  nc

theorem noCommit_tableTerms (cP fP point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), NoCommit (tableTermsClaims cP fP point rows cursor final claims)
  | [], _, _, _ => noCommit_ret _
  | (table, height, forms, weight) :: rest, cursor, final, claims => by
    unfold tableTermsClaims
    simp only [VerifierProgram.bind_eq]
    exact NoCommit.bind (noCommit_readN _) fun _ ↦ noCommit_tableTerms cP fP point rest _ _ _

theorem noCommit_tablePhase (layout : Layout) (bus : BusResult) :
    NoCommit (tablePhaseClaims layout bus) := by
  unfold tablePhaseClaims tableSumcheckClaims
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc]
  refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sumcheck _ _ _
  intro r
  refine NoCommit.bind ?_ ?_
  · exact noCommit_tableTerms _ _ _ _ _ _ _
  intro r
  nc

theorem noCommit_tablesSeg (c : BytecodeClaim) (L : Layout) (pi : Digest) (alphas : List E)
    (beta : E) (point tv : List E) :
    NoCommit (Tables.tablesSeg (claimedBytecodeValue c) L pi alphas beta point tv) := by
  unfold Tables.tablesSeg
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind ?_ fun _ ↦ NoCommit.bind (noCommit_tablePhase _ _) fun _ ↦ ?_
  · unfold Tables.busRest
    simp only [claimedBytecodeValue]
    nc
  · unfold publicInputPhase
    nc

theorem noCommit_keccakPackRounds : ∀ (rs : List E) (value scale : E),
    NoCommit (keccakPackRounds rs value scale)
  | [], _, _ => noCommit_ret _
  | r :: rs, value, scale => by
    unfold keccakPackRounds
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommit.bind (noCommit_sumcheckRoundPoly _ _ _) fun _ ↦ ?_
    refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
    refine NoCommit.bind ?_ ?_
    · exact noCommit_keccakPackRounds rs _ _
    intro r
    exact noCommit_ret _

theorem noCommit_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    NoCommit (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind ?_ ?_
  · exact noCommit_readN _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_require _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleE
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_keccakPackRounds _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sumcheck _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_readN _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_require _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleE
  intro _
  exact noCommit_ret _

theorem noCommit_keccakLayers (logSteps : ℕ) (steps : List ℕ) :
    ∀ claim : KeccakClaim, NoCommit (keccakLayers logSteps steps claim) := by
  induction steps with
  | nil => intro _; exact noCommit_ret _
  | cons step steps ih =>
    intro claim
    unfold keccakLayers
    simp only [VerifierProgram.bind_eq]
    refine NoCommit.bind ?_ ?_
    · exact noCommit_verifyKeccakLayer logSteps step claim
    intro _
    exact ih _

theorem noCommit_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    NoCommit (keccakOpen logSteps claim first count value) := by
  unfold keccakOpen
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sumcheck _ _ _
  intro _
  exact noCommit_ret _

theorem noCommit_keccakSeg (logSteps : ℕ) (inst output : List E) :
    NoCommit (keccakSeg logSteps inst output) := by
  have h1 : 1 < keccakSegments := by decide
  unfold keccakSeg verifyKeccak
  simp only [h1, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleN _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleN _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_readE
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_keccakLayers _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_keccakOpen _ _ _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_readE
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_require _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sumcheck _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_keccakOpen _ _ _ _ _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_readN _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_require _
  intro _
  refine NoCommit.bind ?_ ?_
  · exact noCommit_sampleE
  intro _
  exact noCommit_ret _

end
end LeanVM.Guest.B1.VerifySub
