/-
  LeanVM.Guest.B1.VerifySub.NoCommit

  The deferring verifier's phases before its stacked opening commit nothing and query nothing:
  a carried run of one keeps the roots and the openings, and is a run between grounds.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Tables.RunF
public import LeanVM.Guest.B1.VerifySub.Split

/-!
# Phases without commitments

`NoCommit p`: on every path, `p` has no `commit` and no `query` step. It is closed under `bind`
(`NoCommit.bind`), and a carried run of such a program keeps the roots and the openings and runs
on any (`NoCommitA.runT_any`), so a deployed run of it is a run between grounds on the words it
reads (`runsG_of_runId`). Every phase of the deferring verifier before its stacked opening but the
stack's commitment is one: the announced sizes, the out-of-domain sample, the bus's challenges,
its GKR (`Tables.gkrPhase`), the bus's rest, the table sumcheck and the public input
(`Tables.tablesSeg`), the Keccak reduction (`keccakPhaseClaims`) and the ring switch.
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

theorem NoCommitA.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : NoCommitA p) (hf : ∀ a, NoCommitA (f a)) : NoCommitA (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit _ _ _ _ => exact hp.elim
  | query _ _ _ _ => exact hp.elim

theorem NoCommit.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : NoCommit p) (hf : ∀ a, NoCommit (f a)) : NoCommit (p.bind f) :=
  (noCommit_iff _).2 (NoCommitA.bind ((noCommit_iff _).1 hp) fun a ↦ (noCommit_iff _).1 (hf a))

/-! ## Carried runs without commitments -/

/-- **A carried run without commitments keeps the roots and the openings, and runs on any.** -/
theorem NoCommitA.runT_any {α : Type} (p : VerifierProgram α) : NoCommitA p →
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
  obtain ⟨hR, hO, hany⟩ := NoCommitA.runT_any p ((noCommit_iff _).1 hp) _ a _ hT
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
  obtain ⟨-, -, e2⟩ := NoCommitA.runT_any p ((noCommit_iff _).1 hp) _ a _ e1
  have e3 := e2 os roots
  obtain ⟨sp', hc, hr⟩ := Tables.runId_of_runT p _ sp2 hs2 a _ e3
  exact ⟨sp', hc, hr⟩

theorem tcar_fsOfT (sp : Sponge) : Tables.TCar (Tables.fsOfT sp) sp.ground sp :=
  ⟨rfl, rfl, rfl⟩

/-! ## The primitives -/

theorem noCommit_ret {α : Type} (a : α) : NoCommit (VerifierProgram.ret a) :=
  (noCommit_iff _).2 trivial

theorem noCommit_fail {α : Type} : NoCommit (VerifierProgram.fail : VerifierProgram α) :=
  (noCommit_iff _).2 trivial

theorem noCommit_readE : NoCommit VerifierProgram.readScalar := (noCommit_iff _).2 fun _ ↦ trivial

theorem noCommit_sampleE : NoCommit VerifierProgram.sampleChallenge :=
  (noCommit_iff _).2 fun _ ↦ trivial

theorem noCommit_grind (bits : ℕ) : NoCommit (VerifierProgram.grindProofOfWork bits) := by
  unfold VerifierProgram.grindProofOfWork
  split
  · exact noCommit_ret _
  · exact (noCommit_iff _).2 trivial

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
  | exact noCommit_grind _
  | exact noCommit_readN _
  | exact noCommit_sampleN _
  | exact noCommit_require _
  | exact noCommit_liftOption _
  | exact noCommit_fail
  | (simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq])
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

theorem noCommit_readOod (μ : ℕ) : NoCommit (readOod μ) := by
  unfold readOod
  nc

theorem noCommit_busChallenges (d : ℕ) : NoCommit (busChallenges d) := by
  unfold busChallenges
  nc

theorem noCommit_gkrStep (step : ℕ) (last : Bool) (s : GkrState) :
    NoCommit (gkrStep step last s) := by
  unfold gkrStep
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_grind _) fun _ ↦ ?_
  refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_sumcheck _ _ _) fun _ ↦ ?_
  nc

theorem noCommit_gkrLayers : ∀ (n : ℕ) (s : GkrState), NoCommit (gkrLayers n s)
  | 0, _ => noCommit_ret _
  | 1, s => by
    unfold gkrLayers
    simp only [VerifierProgram.bind_eq]
    exact NoCommit.bind (noCommit_gkrStep _ _ _) fun _ ↦ noCommit_gkrLayers 0 _
  | n + 2, s => by
    unfold gkrLayers
    split
    · simp only [VerifierProgram.bind_eq]
      exact NoCommit.bind (noCommit_gkrStep _ _ _) fun _ ↦ noCommit_gkrLayers (n + 1) _
    · simp only [VerifierProgram.bind_eq]
      exact NoCommit.bind (noCommit_gkrStep _ _ _) fun _ ↦ noCommit_gkrLayers n _

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
  refine NoCommit.bind (noCommit_grind _) fun _ ↦ ?_
  refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_sumcheck _ _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_tableTerms _ _ _ _ _ _ _) fun _ ↦ ?_
  nc

theorem noCommit_bytecodeShare (weights low : List E) : NoCommit (bytecodeShare weights low) := by
  unfold bytecodeShare
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind noCommit_readE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_sumcheck _ _ _) fun _ ↦ ?_
  nc

theorem noCommit_busRest (c : BytecodeClaim) (L : Layout) (weights : List E) (beta : E)
    (point tv : List E) :
    NoCommit (Tables.busRest (claimedBytecodeValue c) L weights beta point tv) := by
  unfold Tables.busRest
  simp only [claimedBytecodeValue, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_readN _) fun _ ↦ ?_
  refine NoCommit.bind noCommit_readE fun _ ↦ ?_
  refine NoCommit.bind noCommit_readE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_bytecodeShare _ _) fun _ ↦ ?_
  nc

theorem noCommit_publicInputPhase (layout : Layout) (pi : Digest) :
    NoCommit (publicInputPhase layout pi) := by
  unfold publicInputPhase
  nc

theorem noCommit_tablesSeg (c : BytecodeClaim) (L : Layout) (pi : Digest) (weights : List E)
    (beta : E) (point tv : List E) :
    NoCommit (Tables.tablesSeg (claimedBytecodeValue c) L pi weights beta point tv) := by
  unfold Tables.tablesSeg
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_busRest _ _ _ _ _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_tablePhase _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_publicInputPhase _ _) fun _ ↦ ?_
  exact noCommit_ret _

theorem noCommit_keccakPackRounds : ∀ (rs : List E) (value scale : E),
    NoCommit (keccakPackRounds rs value scale)
  | [], _, _ => noCommit_ret _
  | r :: rs, value, scale => by
    unfold keccakPackRounds
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommit.bind (noCommit_sumcheckRoundPoly _ _ _) fun _ ↦ ?_
    refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
    exact NoCommit.bind (noCommit_keccakPackRounds rs _ _) fun _ ↦ noCommit_ret _

theorem noCommit_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    NoCommit (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_readN _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_require _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_grind _) fun _ ↦ ?_
  refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_keccakPackRounds _ _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_sumcheck _ _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_readN _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_require _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_grind _) fun _ ↦ ?_
  refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
  exact noCommit_ret _

theorem noCommit_keccakLayers (logSteps : ℕ) (steps : List ℕ) :
    ∀ claim : KeccakClaim, NoCommit (keccakLayers logSteps steps claim) := by
  induction steps with
  | nil => intro _; exact noCommit_ret _
  | cons step steps ih =>
    intro claim
    unfold keccakLayers
    simp only [VerifierProgram.bind_eq]
    exact NoCommit.bind (noCommit_verifyKeccakLayer logSteps step claim) fun _ ↦ ih _

theorem noCommit_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    NoCommit (keccakOpen logSteps claim first count value) := by
  unfold keccakOpen
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact NoCommit.bind (noCommit_sumcheck _ _ _) fun _ ↦ noCommit_ret _

/-- The search `nc` with the recursive phases. -/
macro "nck" : tactic => `(tactic| repeat' (first
    | with_reducible exact noCommit_ret _
    | with_reducible exact noCommit_readE
    | with_reducible exact noCommit_sampleE
    | with_reducible exact noCommit_grind _
    | with_reducible exact noCommit_readN _
    | with_reducible exact noCommit_sampleN _
    | with_reducible exact noCommit_require _
    | with_reducible exact noCommit_sumcheck _ _ _
    | with_reducible exact noCommit_keccakOpen _ _ _ _ _
    | with_reducible (refine NoCommit.bind (noCommit_keccakOpen _ _ _ _ _) fun _ ↦ ?_)
    | with_reducible (refine NoCommit.bind (noCommit_sumcheck _ _ _) fun _ ↦ ?_)
    | with_reducible (refine NoCommit.bind (noCommit_readN _) fun _ ↦ ?_)
    | with_reducible (refine NoCommit.bind noCommit_readE fun _ ↦ ?_)
    | with_reducible (refine NoCommit.bind (noCommit_require _) fun _ ↦ ?_)
    | with_reducible (refine NoCommit.bind (noCommit_ret _) fun _ ↦ ?_)
    | split
    | (intro _)))

theorem noCommit_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    NoCommit (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  generalize List.range keccakDepth = steps
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_grind _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_sampleN _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_sampleN _) fun _ ↦ ?_
  refine NoCommit.bind noCommit_readE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_keccakLayers logSteps steps _) fun _ ↦ ?_
  nck

theorem noCommit_keccakPhaseClaims (layout : Layout) (claims : List ColumnClaim) :
    NoCommit (keccakPhaseClaims layout claims) := by
  unfold keccakPhaseClaims
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_require _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_verifyKeccak _ _ _) fun _ ↦ ?_
  nc

theorem noCommit_ringSwitch (point s : List E) : NoCommit (ringSwitch point s) := by
  unfold ringSwitch
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_grind _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_sampleN _) fun _ ↦ ?_
  exact noCommit_ret _

end
end LeanVM.Guest.B1.VerifySub
