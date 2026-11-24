/-
  LeanVM.Protocol.Verifier.NoCommit

  The verifier's phases before its stacked opening commit nothing and open nothing.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.Verifier.KeccakPack
public import LeanVM.Protocol.Verifier.Phases.Bus

/-!
# Phases without commitments or openings

`NoCommit p`: on every path, `p` has no `commit` and no `query` step. It is closed under `bind`
(`NoCommit.bind`), and the tactic `no_commit` proves it of a program built from the primitives by
binds, matches and `if`s. Every phase of the verifier before its stacked opening but the stack's
commitment is one: the announced sizes, the out-of-domain sample, the bus (for a check of the
fixed polynomial that is one, `noCommit_verifyBusBalance`), the table sumcheck, the public input,
the Keccak reduction and the ring switch; so are a WHIR level's fold rounds and query sampling.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile

@[expose] public section

variable {α β : Type}

/-- No `commit` and no `query` on any path (the recursion). -/
def NoCommitA : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoCommitA (k x)
  | .sample k => ∀ c, NoCommitA (k c)
  | .grind _ k => NoCommitA k
  | .commit _ _ _ => False
  | .query _ _ _ => False

/-- **No `commit` and no `query` on any path.** Irreducible: unfolding it on a large program would
evaluate the program. -/
@[irreducible] def NoCommit (p : VerifierProgram α) : Prop := NoCommitA p

theorem noCommit_iff (p : VerifierProgram α) : NoCommit p ↔ NoCommitA p := by
  unfold NoCommit; rfl

theorem NoCommitA.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoCommitA p)
    (hf : ∀ a, NoCommitA (f a)) : NoCommitA (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit _ _ _ _ => exact hp.elim
  | query _ _ _ _ => exact hp.elim

theorem NoCommit.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoCommit p)
    (hf : ∀ a, NoCommit (f a)) : NoCommit (p.bind f) :=
  (noCommit_iff _).2 (NoCommitA.bind ((noCommit_iff _).1 hp) fun a ↦ (noCommit_iff _).1 (hf a))

/-! ## The primitives -/

theorem noCommit_ret (a : α) : NoCommit (VerifierProgram.ret a) := (noCommit_iff _).2 trivial

theorem noCommit_fail : NoCommit (VerifierProgram.fail : VerifierProgram α) :=
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
    exact NoCommit.bind noCommit_readE fun _ ↦ NoCommit.bind (noCommit_readN n) fun _ ↦
      noCommit_ret _

theorem noCommit_sampleN : ∀ n, NoCommit (VerifierProgram.sampleChallenges n)
  | 0 => noCommit_ret _
  | n + 1 => by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact NoCommit.bind noCommit_sampleE fun _ ↦ NoCommit.bind (noCommit_sampleN n) fun _ ↦
      noCommit_ret _

theorem noCommit_require (c : Prop) [Decidable c] : NoCommit (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split
  · exact noCommit_ret _
  · exact noCommit_fail

theorem noCommit_liftOption (o : Option α) : NoCommit (liftOption o) := by
  cases o
  · exact noCommit_fail
  · exact noCommit_ret _

theorem noCommit_sumcheckRoundPoly (count : ℕ) (claim : E) (e : Option E) :
    NoCommit (sumcheckRoundPoly count claim e) := by
  cases e <;> (unfold sumcheckRoundPoly; simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq])
  · exact NoCommit.bind noCommit_readE fun _ ↦ NoCommit.bind (noCommit_readN _) fun _ ↦
      NoCommit.bind (noCommit_grind _) fun _ ↦ noCommit_ret _
  · exact NoCommit.bind (noCommit_readN _) fun _ ↦ NoCommit.bind (noCommit_grind _) fun _ ↦
      noCommit_ret _

theorem noCommit_sumcheck (claim : E) (count : ℕ) (eqs : List (Option E)) :
    NoCommit (sumcheck claim count eqs) := by
  induction eqs generalizing claim with
  | nil => exact noCommit_ret _
  | cons e eqs ih =>
    unfold sumcheck
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact NoCommit.bind (noCommit_sumcheckRoundPoly _ _ _) fun _ ↦ NoCommit.bind noCommit_sampleE
      fun _ ↦ NoCommit.bind (ih _) fun _ ↦ noCommit_ret _

/-- A search for `NoCommit` through binds, the primitives, matches and `if`s. -/
macro "no_commit" : tactic => `(tactic| repeat (first
  | exact noCommit_ret _
  | exact noCommit_readE
  | exact noCommit_sampleE
  | exact noCommit_grind _
  | exact noCommit_readN _
  | exact noCommit_sampleN _
  | exact noCommit_require _
  | exact noCommit_liftOption _
  | exact noCommit_fail
  | exact (noCommit_iff _).2 trivial
  | exact noCommit_sumcheckRoundPoly _ _ _
  | exact noCommit_sumcheck _ _ _
  | (refine NoCommit.bind ?_ fun _ ↦ ?_)
  | (simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq])
  | split
  | (intro _)))

/-! ## The phases before the stacked opening -/

theorem noCommit_readSizes (bytecode : List K) : NoCommit (readAnnouncedSizes bytecode) := by
  unfold readAnnouncedSizes
  no_commit

theorem noCommit_readOod (stackLog : ℕ) : NoCommit (readOod stackLog) := by
  rw [readOod_eq]
  exact NoCommit.bind (noCommit_grind _) fun _ ↦ NoCommit.bind (noCommit_sampleN _) fun _ ↦
    NoCommit.bind noCommit_readE fun _ ↦ noCommit_liftOption _

theorem noCommit_gkrStep (step : ℕ) (last : Bool) (s : GkrState) :
    NoCommit (gkrStep step last s) := by
  unfold gkrStep
  no_commit

theorem noCommit_gkrLayers : ∀ (n : ℕ) (s : GkrState), NoCommit (gkrLayers n s)
  | 0, _ => noCommit_ret _
  | 1, s => by
    unfold gkrLayers
    simp only [VerifierProgram.bind_eq]
    exact NoCommit.bind (noCommit_gkrStep _ _ _) fun _ ↦ noCommit_gkrLayers 0 _
  | n + 2, s => by
    unfold gkrLayers
    split <;> simp only [VerifierProgram.bind_eq]
    · exact NoCommit.bind (noCommit_gkrStep _ _ _) fun _ ↦ noCommit_gkrLayers (n + 1) _
    · exact NoCommit.bind (noCommit_gkrStep _ _ _) fun _ ↦ noCommit_gkrLayers n _

theorem noCommit_verifyGkr (depth : ℕ) : NoCommit (verifyGkrGrandProducts depth) := by
  unfold verifyGkrGrandProducts
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact NoCommit.bind noCommit_readE fun _ ↦ NoCommit.bind noCommit_readE fun _ ↦
    NoCommit.bind (noCommit_gkrLayers _ _) fun _ ↦ noCommit_ret _

theorem noCommit_bytecodeShare (weights bytecodeLow : List E) :
    NoCommit (bytecodeShare weights bytecodeLow) := by
  unfold bytecodeShare
  no_commit

theorem noCommit_busChallenges (d : ℕ) : NoCommit (busChallenges d) := by
  unfold busChallenges
  no_commit

theorem noCommit_gkrPhase (depth : ℕ) : NoCommit (gkrPhase depth) := by
  unfold gkrPhase
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact NoCommit.bind (noCommit_verifyGkr _) fun _ ↦ NoCommit.bind (noCommit_require _) fun _ ↦
    noCommit_ret _

theorem noCommit_busRest {ev : List K → List E → E → VerifierProgram Unit}
    (hev : ∀ w p v, NoCommit (ev w p v)) (L : Layout) (weights : List E) (beta : E)
    (point tv : List E) : NoCommit (busRest ev L weights beta point tv) := by
  unfold busRest
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_readN _) fun _ ↦ NoCommit.bind noCommit_readE fun _ ↦ ?_
  refine NoCommit.bind noCommit_readE fun _ ↦ NoCommit.bind (noCommit_bytecodeShare _ _) fun _ ↦ ?_
  refine NoCommit.bind (hev _ _ _) fun _ ↦ ?_
  no_commit

/-- **The bus**, for a check of the fixed polynomial's value that commits and opens nothing. -/
theorem noCommit_verifyBusBalance {ev : List K → List E → E → VerifierProgram Unit}
    (hev : ∀ w p v, NoCommit (ev w p v)) (layout : Layout) :
    NoCommit (verifyBusBalance ev layout) := by
  rw [verifyBusBalance_split]
  exact NoCommit.bind (noCommit_require _) fun _ ↦ NoCommit.bind (noCommit_grind _) fun _ ↦
    NoCommit.bind (noCommit_sampleN _) fun _ ↦ NoCommit.bind noCommit_sampleE fun _ ↦
    NoCommit.bind (noCommit_gkrPhase _) fun _ ↦ noCommit_busRest hev _ _ _ _ _

theorem noCommit_computedBytecodeValue (w : List K) (p : List E) (v : E) :
    NoCommit (computedBytecodeValue w p v) := noCommit_require _

theorem noCommit_claimedBytecodeValue (c : BytecodeClaim) (w : List K) (p : List E) (v : E) :
    NoCommit (claimedBytecodeValue c w p v) := noCommit_require _

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
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_grind _) fun _ ↦ NoCommit.bind noCommit_sampleE fun _ ↦ ?_
  refine NoCommit.bind (NoCommit.bind (noCommit_sumcheck _ _ _) fun x ↦ ?_) fun _ ↦ noCommit_ret _
  obtain ⟨_, _⟩ := x
  refine NoCommit.bind (noCommit_tableTerms _ _ _ _ _ _ _) fun y ↦ ?_
  obtain ⟨_, _⟩ := y
  exact NoCommit.bind (noCommit_require _) fun _ ↦ noCommit_ret _

theorem noCommit_publicInputPhase (layout : Layout) (pi : Digest) :
    NoCommit (publicInputPhase layout pi) := by
  rw [publicInputPhase_eq]
  exact NoCommit.bind noCommit_sampleE fun _ ↦ noCommit_liftOption _

theorem noCommit_keccakPackRounds : ∀ (rs : List E) (value : E),
    NoCommit (keccakPackRounds rs value)
  | [], _ => noCommit_ret _
  | r :: rs, value => by
    unfold keccakPackRounds
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact NoCommit.bind (noCommit_sumcheckRoundPoly _ _ _) fun _ ↦ NoCommit.bind noCommit_sampleE
      fun _ ↦ NoCommit.bind (noCommit_keccakPackRounds rs _) fun _ ↦ noCommit_ret _

theorem noCommit_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    NoCommit (verifyKeccakLayer logSteps step claim) := by
  rw [verifyKeccakLayer_packed]
  unfold verifyKeccakLayerPacked
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_readN _) fun _ ↦ NoCommit.bind (noCommit_require _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_grind _) fun _ ↦ NoCommit.bind noCommit_sampleE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_keccakPackRounds _ _) fun x ↦ ?_
  obtain ⟨_, _⟩ := x
  refine NoCommit.bind (noCommit_sumcheck _ _ _) fun y ↦ ?_
  obtain ⟨_, _⟩ := y
  refine NoCommit.bind (noCommit_readN _) fun _ ↦ NoCommit.bind (noCommit_require _) fun _ ↦ ?_
  exact NoCommit.bind (noCommit_grind _) fun _ ↦ NoCommit.bind noCommit_sampleE fun _ ↦
    noCommit_ret _

theorem noCommit_keccakLayers (logSteps : ℕ) (steps : List ℕ) (claim : KeccakClaim) :
    NoCommit (keccakLayers logSteps steps claim) := by
  induction steps generalizing claim with
  | nil => exact noCommit_ret _
  | cons step steps ih =>
    unfold keccakLayers
    simp only [VerifierProgram.bind_eq]
    exact NoCommit.bind (noCommit_verifyKeccakLayer logSteps step claim) fun _ ↦ ih _

theorem noCommit_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    NoCommit (keccakOpen logSteps claim first count value) := by
  unfold keccakOpen
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact NoCommit.bind (noCommit_sumcheck _ _ _) fun _ ↦ noCommit_ret _

theorem noCommit_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    NoCommit (verifyKeccak logSteps inst output) := by
  have h1 : 1 < keccakSegments := by decide
  unfold verifyKeccak
  simp only [h1, ↓reduceIte]
  refine NoCommit.bind (noCommit_grind _) fun _ ↦ NoCommit.bind (noCommit_sampleN _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_sampleN _) fun _ ↦ NoCommit.bind noCommit_readE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_keccakLayers _ _ _) fun _ ↦ ?_
  -- `refine` names the `q_keccak` openings' programs only by a goal of their own: unified inside a
  -- bind, `keccakOpen` is unfolded.
  refine NoCommit.bind ?_ fun _ ↦ ?_
  · exact noCommit_keccakOpen _ _ _ _ _
  refine NoCommit.bind noCommit_readE fun _ ↦ NoCommit.bind (noCommit_require _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_ret _) fun _ ↦ NoCommit.bind (noCommit_sumcheck _ _ _) fun _ ↦ ?_
  refine NoCommit.bind ?_ fun _ ↦ ?_
  · exact noCommit_keccakOpen _ _ _ _ _
  exact NoCommit.bind (noCommit_readN _) fun _ ↦ NoCommit.bind (noCommit_require _) fun _ ↦
    noCommit_ret _

theorem noCommit_keccakPhaseClaims (layout : Layout) (claims : List ColumnClaim) :
    NoCommit (keccakPhaseClaims layout claims) := by
  unfold keccakPhaseClaims
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_require _) fun _ ↦
    NoCommit.bind (noCommit_verifyKeccak _ _ _) fun x ↦ ?_
  obtain ⟨_, _, _⟩ := x
  exact noCommit_ret _

theorem noCommit_ringSwitch (point s : List E) : NoCommit (ringSwitch point s) := by
  rw [ringSwitch_eq]
  exact NoCommit.bind (noCommit_grind _) fun _ ↦ NoCommit.bind (noCommit_sampleN _) fun _ ↦
    noCommit_liftOption _

/-! ## A WHIR level's fold rounds and query sampling -/

theorem noCommit_foldRound (s : WhirState) : NoCommit (foldRound s) := by
  unfold foldRound
  no_commit

theorem noCommit_foldRounds : ∀ (n : ℕ) (s : WhirState), NoCommit (foldRounds n s)
  | 0, _ => noCommit_ret _
  | n + 1, s => by
    unfold foldRounds
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommit.bind (noCommit_foldRound s) fun x ↦ ?_
    obtain ⟨_, _⟩ := x
    refine NoCommit.bind (noCommit_foldRounds n _) fun y ↦ ?_
    obtain ⟨_, _⟩ := y
    exact noCommit_ret _

theorem noCommit_sampleQueriesAux (depth : ℕ) : ∀ (fuel remaining : ℕ),
    NoCommit (sampleQueriesAux depth fuel remaining)
  | 0, _ => noCommit_ret _
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    split
    · exact noCommit_ret _
    · exact NoCommit.bind noCommit_sampleE fun _ ↦ NoCommit.bind
        (noCommit_sampleQueriesAux depth fuel _) fun _ ↦ noCommit_ret _

end
end LeanVM.Protocol.Verifier
