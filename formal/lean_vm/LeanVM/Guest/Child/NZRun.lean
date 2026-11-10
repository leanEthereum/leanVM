/-
  LeanVM.Guest.Child.NZRun

  Where no challenge is zero, the verifier refusing a zero challenge runs as the verifier: with a
  permutation none of whose outputs has a zero challenge, their runs are equal.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.Child.Fresh
public import LeanVM.Protocol.WithHash

/-!
# Refusing a zero challenge changes nothing where none is zero

`NZ p' p`: `p'` is `p` with, after some challenges, a check that the challenge is not zero; at a
nonzero challenge the two continue alike. The verifier program refusing a zero fold, tail or
level batching challenge is such a `p'` of the verifier program (`nz_program`). A compiled run
draws every challenge as `challengeOf` of a permutation output, so with a permutation that
never outputs a zero challenge the two runs are the same run (`run_nz`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **`p'` is `p` refusing zero challenges**: step for step, the continuations after a nonzero
challenge related. -/
inductive NZ {α : Type} : VerifierProgram α → VerifierProgram α → Prop
  | ret (a : α) : NZ (.ret a) (.ret a)
  | fail : NZ .fail .fail
  | read {k k' : E → VerifierProgram α} : (∀ x, NZ (k' x) (k x)) → NZ (.read k') (.read k)
  | sample {k k' : E → VerifierProgram α} : (∀ c, c ≠ 0 → NZ (k' c) (k c)) → NZ (.sample k')
      (.sample k)
  | grind {b : ℕ} {k k' : VerifierProgram α} : NZ k' k → NZ (.grind b k') (.grind b k)
  | commit {h w : ℕ} {k k' : VerifierProgram α} : NZ k' k → NZ (.commit h w k') (.commit h w k)
  | query {i : ℕ} {ps : List ℕ} {k k' : List (List K) → VerifierProgram α} :
      (∀ r, NZ (k' r) (k r)) → NZ (.query i ps k') (.query i ps k)

namespace NZ

variable {α β : Type}

theorem refl : ∀ p : VerifierProgram α, NZ p p
  | .ret a => .ret a
  | .fail => .fail
  | .read k => .read fun x ↦ refl (k x)
  | .sample k => .sample fun c _ ↦ refl (k c)
  | .grind _ k => .grind (refl k)
  | .commit _ _ k => .commit (refl k)
  | .query _ _ k => .query fun r ↦ refl (k r)

theorem bind {p' p : VerifierProgram α} (h : NZ p' p) {f' f : α → VerifierProgram β} (hf : ∀ a, NZ
    (f' a) (f a)) :
    NZ (p'.bind f') (p.bind f) := by
  induction h with
  | ret a => exact hf a
  | fail => exact .fail
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih

/-- A challenge, then programs related at every nonzero challenge. -/
theorem sample_bind {f' f : E → VerifierProgram β} (hf : ∀ c, c ≠ 0 → NZ (f' c) (f c)) :
    NZ (VerifierProgram.sampleChallenge.bind f') (VerifierProgram.sampleChallenge.bind f) :=
  .sample hf

/-- A check that holds, then related programs. -/
theorem require_bind_of {c : Prop} [Decidable c] (hc : c) {k' k : VerifierProgram α} (h : NZ k' k) :
    NZ ((VerifierProgram.require c).bind fun _ ↦ k') k := by
  unfold VerifierProgram.require
  simp only [hc, ↓reduceIte]
  exact h

end NZ

/-! ## The programs -/

theorem nz_foldRounds (b : ℕ) : ∀ (n : ℕ) (s : WhirStateT) (lf : List E),
    NZ (Limits.foldRoundsNZ b n s lf) (foldRoundsT b n s lf)
  | 0, s, lf => NZ.refl _
  | n + 1, s, lf => by
    unfold Limits.foldRoundsNZ foldRoundsT
    refine NZ.bind (NZ.refl _) fun _ ↦ ?_
    refine NZ.sample_bind fun c hc ↦ ?_
    refine NZ.require_bind_of hc ?_
    exact NZ.bind (NZ.refl _) fun _ ↦ nz_foldRounds b n _ _

theorem nz_tailRounds : ∀ (n : ℕ) (t : E) (quad : List E),
    NZ (Limits.tailRoundsNZ n t quad) (tailRoundsT n t quad)
  | 0, t, quad => NZ.refl _
  | n + 1, t, quad => by
    unfold Limits.tailRoundsNZ tailRoundsT
    refine NZ.sample_bind fun c hc ↦ ?_
    refine NZ.require_bind_of hc ?_
    split
    · exact NZ.refl _
    · exact NZ.bind (NZ.refl _) fun _ ↦ NZ.bind (nz_tailRounds n _ _) fun _ ↦ NZ.refl _

/-- The first program of a bind: the same, or one refusing zero challenges. -/
local macro "nz_head" : tactic => `(tactic| first
  | with_reducible exact NZ.refl _
  | exact nz_foldRounds _ _ _ _
  | exact nz_tailRounds _ _ _)

/-- One step between two programs written alike. -/
local macro "nz_step" : tactic => `(tactic| first
  | with_reducible exact NZ.refl _
  | (apply NZ.require_bind_of (by assumption))
  | (refine NZ.sample_bind fun _ _ ↦ ?_)
  | (refine NZ.bind ?h fun _ ↦ ?k; case h => nz_head)
  | split
  | dsimp only
  | exact NZ.refl _)

theorem nz_whirLevels (logN laneFolds : ℕ) (eb : List E → E) (levels : List Whir.Level) :
    ∀ (index : ℕ) (s : WhirStateT),
      NZ (Limits.whirLevelsNZ logN laneFolds eb index levels s)
        (whirLevelsT logN laneFolds eb index levels s) := by
  induction levels with
  | nil => intro index s; exact NZ.refl _
  | cons level rest ih =>
    intro index s
    unfold Limits.whirLevelsNZ whirLevelsT
    apply NZ.bind (nz_foldRounds _ _ _ _)
    intro p
    obtain ⟨s', lf⟩ := p
    dsimp only
    cases rest with
    | nil =>
      dsimp only
      repeat nz_step
    | cons next rest' =>
      dsimp only
      repeat (first | exact ih _ _ | nz_step)

theorem nz_verifyWhir (logN logInvRate : ℕ) (target : E) (eb : List E → E) :
    NZ (Limits.verifyWhirNZ logN logInvRate target eb) (verifyWhirT logN logInvRate target eb) := by
  unfold Limits.verifyWhirNZ verifyWhirT
  repeat (first | exact nz_whirLevels _ _ _ _ _ _ | nz_step)

theorem nz_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    NZ (Limits.verifyStackedOpeningNZ stackLog logInvRate claims)
      (verifyStackedOpening stackLog logInvRate claims) := by
  unfold Limits.verifyStackedOpeningNZ verifyStackedOpening
  simp only [verifyWhir_eq_target]
  repeat (first | exact nz_verifyWhir _ _ _ _ | nz_step)

/-- **The verifier refusing zero challenges is the verifier refusing zero challenges.** -/
theorem nz_program (ev : (List K → List E → VerifierProgram E)) (bytecode : List K) (publicInput :
    Digest) :
    NZ ((execWith ev Limits.verifyStackedOpeningNZ bytecode publicInput).bind
        fun _ ↦ VerifierProgram.ret true)
      ((execWith ev verifyStackedOpening bytecode publicInput).bind fun _ ↦ VerifierProgram.ret
          true) := by
  refine NZ.bind ?_ fun _ ↦ NZ.refl _
  unfold execWith
  refine NZ.bind (NZ.refl _) fun ls ↦ ?_
  obtain ⟨layout, r⟩ := ls
  refine NZ.bind (NZ.refl _) fun _ ↦ ?_
  refine NZ.bind (NZ.refl _) fun bus ↦ ?_
  refine NZ.bind (NZ.refl _) fun claims ↦ ?_
  refine NZ.bind (NZ.refl _) fun pub ↦ ?_
  refine NZ.bind (NZ.refl _) fun kr ↦ ?_
  obtain ⟨cl, kp, ks⟩ := kr
  refine NZ.bind (NZ.refl _) fun rs ↦ ?_
  obtain ⟨rt, rw⟩ := rs
  exact nz_verifyStackedOpening _ _ _

/-! ## The runs -/

/-- **With a permutation that never outputs a zero challenge, the runs agree.** -/
theorem run_nz (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    (hF : ∀ s, challengeOf (Id.run (F s)) ≠ 0) {α : Type} {p' p : VerifierProgram α} (h : NZ p' p) :
    ∀ st : VerifierProgramState, Compile.runWithHash H F p' st = Compile.runWithHash H F p st := by
  induction h with
  | ret a => intro st; rfl
  | fail => intro st; rfl
  | read _ ih =>
    intro st
    unfold Compile.runWithHash
    cases st.stream with
    | nil => rfl
    | cons x xs => exact ih x _
  | sample _ ih =>
    intro st
    unfold Compile.runWithHash
    exact ih _ (hF _) _
  | grind _ ih =>
    intro st
    unfold Compile.runWithHash
    simp only [ih]
  | commit _ ih =>
    intro st
    unfold Compile.runWithHash
    simp only [ih]
  | query _ ih =>
    intro st
    unfold Compile.runWithHash
    simp only [ih]

theorem runProof_nz (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    (hF : ∀ s, challengeOf (Id.run (F s)) ≠ 0) {p' p : VerifierProgram Bool} (h : NZ p' p) (seed :
        KeccakState)
    (π : Proof) : runProofWithHash H F p' seed π = runProofWithHash H F p seed π := by
  unfold runProofWithHash
  rw [run_nz H F hF h]

end
end LeanVM.Guest.Child
