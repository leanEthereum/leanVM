/-
  LeanVM.Guest.B1.Whir.SpecNZ

  The no-zero-challenge programs refine the Spec's: a run of `whirOpenNZ` is a run of `whirOpen`,
  with the same query steps.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.SpecPrim

/-!
# No zero challenge refines the opening

`foldRoundsNZ_ref`, `tailRoundsNZ_ref`, `whirLevelsOpenNZ_ref`, `whirOpenNZ_ref`: each NZ program
refines its Spec program (`Ref`: every accepting run is one of the Spec program, with the same
query steps): it is the Spec program with `require`s inserted.

`nz_run`: on an accepting run of `whirOpen` with no zero challenge (`NoZeroChallenge`), the run of
`whirOpenNZ` on the same words and openings accepts with the same end, and its query steps are the
Spec program's (so `CapsAgree` speaks of them).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem Ref.bind_refl {α β : Type} (p : VerifierProgram α) {f' f : α → VerifierProgram β} (hf : ∀ a,
    Ref (f' a) (f a)) :
    Ref (p.bind f') (p.bind f) := Ref.bind (Ref.refl p) hf

/-- **`foldRoundsNZ` refines `foldRounds`.** -/
theorem foldRoundsNZ_ref (b : ℕ) : ∀ (n : ℕ) (s : WhirStateT) (lf : List E),
    Ref (foldRoundsNZ b n s lf) (foldRoundsT b n s lf)
  | 0, s, lf => Ref.refl _
  | n + 1, s, lf => by
    simp only [foldRoundsNZ, foldRoundsT, VerifierProgram.bind_eq]
    refine Ref.bind_refl _ fun _ ↦ Ref.bind_refl _ fun c ↦ Ref.require _ (Ref.bind_refl _ fun q ↦ ?_)
    exact foldRoundsNZ_ref b n _ _

/-- **`tailRoundsNZ` refines `tailRounds`.** -/
theorem tailRoundsNZ_ref : ∀ (n : ℕ) (t : E) (quad : List E),
    Ref (tailRoundsNZ n t quad) (tailRoundsT n t quad)
  | 0, t, quad => Ref.refl _
  | n + 1, t, quad => by
    simp only [tailRoundsNZ, tailRoundsT, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine Ref.bind_refl _ fun c ↦ Ref.require _ ?_
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]; exact Ref.refl _
    · simp only [hn, ↓reduceIte]
      exact Ref.bind_refl _ fun q ↦ Ref.bind (tailRoundsNZ_ref n _ _) fun _ ↦ Ref.refl _

/-- **`whirLevelsOpenNZ` refines `whirLevelsOpen`.** -/
theorem whirLevelsOpenNZ_ref (logN lane : ℕ) : ∀ (index : ℕ) (levels : List Whir.Level)
    (s : WhirStateT), Ref (whirLevelsOpenNZ logN lane index levels s)
      (whirLevelsOpen logN lane index levels s)
  | _, [], _ => Ref.refl _
  | index, level :: rest, s => by
    simp only [whirLevelsOpenNZ, whirLevelsOpen, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine Ref.bind (foldRoundsNZ_ref _ _ _ _) fun p ↦ ?_
    obtain ⟨s1, lf⟩ := p
    rcases rest with _ | ⟨next, rest⟩
    all_goals simp only [VerifierProgram.ret_bind]
    all_goals repeat' (first
      | with_reducible exact Ref.refl _
      | with_reducible exact whirLevelsOpenNZ_ref logN lane (index + 1) _ _
      | with_reducible refine Ref.bind (tailRoundsNZ_ref _ _ _) fun _ ↦ ?_
      | with_reducible refine Ref.require _ ?_
      | with_reducible refine Ref.bind_refl _ fun _ ↦ ?_)

/-- **`whirOpenNZ` refines `whirOpen`.** -/
theorem whirOpenNZ_ref (logN logInvRate : ℕ) (target : E) :
    Ref (whirOpenNZ logN logInvRate target) (whirOpen logN logInvRate target) := by
  simp only [whirOpenNZ, whirOpen, VerifierProgram.bind_eq]
  exact Ref.bind_refl _ fun config ↦ Ref.bind_refl _ fun quad ↦ whirLevelsOpenNZ_ref _ _ _ _ _

/-- The start of `open_stacked`'s run: the caller's sponge state, nothing waiting, the stack's
root committed. -/
def osStart (μ r : ℕ) (S : KeccakState) (xs : List E) (os : List (List Opening)) (root : Digest) : FSt :=
  ⟨⟨capOf S, []⟩, xs, os, [(root, stackShape μ r)]⟩

theorem start_carries (S : KeccakState) : (⟨capOf S, []⟩ : Fs).Carries ⟨S, []⟩ := ⟨rfl, rfl⟩

/-- **The run with no zero challenge**: the accepting run of `whirOpen` is, read with no zero
challenge, an accepting run of `whirOpenNZ` with the same end, and the same query steps. -/
theorem nz_run {μ r : ℕ} {target : E} {S : KeccakState} {xs : List E} {os : List (List Opening)}
    {root : Digest} {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s'
      roots')
    (hnz : NoZeroChallenge μ r target S xs os root) :
    runF (whirOpenNZ μ r target) (osStart μ r S xs os root) = some (w, ⟨s', [], [], roots'⟩) ∧
      queryStepsOf (whirOpenNZ μ r target) (osStart μ r S xs os root) =
        queryStepsOf (whirOpen μ r target) (osStart μ r S xs os root) := by
  obtain ⟨w', s'', roots'', hnzr⟩ := hnz
  have h1 := runF_of_runsWith hnzr (start_carries S)
  have h2 := runF_of_runsWith hrun (start_carries S)
  obtain ⟨e, q⟩ := whirOpenNZ_ref μ r target _ _ h1
  have := runF_det e h2
  rw [this] at h1
  exact ⟨h1, q⟩

end
end LeanVM.Guest.B1.Whir
