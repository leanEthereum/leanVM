/-
  LeanVM.Protocol.EndToEnd.Sound.SkelLeaves

  Skeletons with postconditions, and the skeletons of the verifier's leaves: reads, samples,
  proofs of work, checks, sumchecks, query positions.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Skeleton

/-!
# The leaves' skeletons

`SkelP p sk Q`: `p` has skeleton `sk` and returns only values satisfying `Q`. The postcondition
carries what a later part's skeleton depends on, a length (`readScalars`, `sumcheck`), as the cost
calculus's does. Sequencing (`SkelP.bind`) gives the continuation the first part's postcondition.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier

@[expose] public section

/-- **A skeleton with a postcondition.** -/
def SkelP {α : Type} (p : VerifierProgram α) (sk : List Op) (Q : α → Prop) : Prop :=
  Skel p sk ∧ ∀ a, VerifierProgram.Returns p a → Q a

namespace SkelP

variable {α β : Type}

theorem ret {a : α} {Q : α → Prop} (h : Q a) : SkelP (.ret a) [] Q :=
  ⟨Skel.ret a, fun b hb ↦ by rw [VerifierProgram.returns_ret hb]; exact h⟩

theorem fail (sk : List Op) (Q : α → Prop) : SkelP (.fail : VerifierProgram α) sk Q :=
  ⟨Skel.fail sk, fun _ h ↦ by cases h⟩

theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {sk₁ sk₂ : List Op}
    {Q₁ : α → Prop} {Q₂ : β → Prop} (hp : SkelP p sk₁ Q₁) (hf : ∀ a, Q₁ a → SkelP (f a) sk₂ Q₂) :
    SkelP (p.bind f) (sk₁ ++ sk₂) Q₂ :=
  ⟨Skel.bind hp.1 fun a ha ↦ (hf a (hp.2 a ha)).1, fun b hb ↦ by
    obtain ⟨a, ha, hfa⟩ := VerifierProgram.returns_bind hb
    exact (hf a (hp.2 a ha)).2 b hfa⟩

theorem mono {p : VerifierProgram α} {sk sk' : List Op} {Q Q' : α → Prop} (h : SkelP p sk Q)
    (e : sk = sk') (hQ : ∀ a, Q a → Q' a) : SkelP p sk' Q' :=
  ⟨e ▸ h.1, fun a ha ↦ hQ a (h.2 a ha)⟩

theorem read {k : E → VerifierProgram α} {sk : List Op} {Q : α → Prop}
    (hk : ∀ x, SkelP (k x) sk Q) : SkelP (.read k) (.read :: sk) Q :=
  ⟨Skel.read fun x ↦ (hk x).1, fun b hb ↦ by cases hb with | read x h => exact (hk x).2 b h⟩

theorem sample {k : E → VerifierProgram α} {sk : List Op} {Q : α → Prop}
    (hk : ∀ x, SkelP (k x) sk Q) : SkelP (.sample k) (.sample :: sk) Q :=
  ⟨Skel.sample fun x ↦ (hk x).1, fun b hb ↦ by cases hb with | sample x h => exact (hk x).2 b h⟩

theorem grind {bits : ℕ} {k : VerifierProgram α} {sk : List Op} {Q : α → Prop}
    (hk : SkelP k sk Q) : SkelP (.grind bits k) (.grind bits :: sk) Q :=
  ⟨Skel.grind hk.1, fun b hb ↦ by cases hb with | grind _ h => exact hk.2 b h⟩

theorem commit {height width : ℕ} {k : VerifierProgram α} {sk : List Op} {Q : α → Prop}
    (hk : SkelP k sk Q) : SkelP (.commit height width k) (.commit height width :: sk) Q :=
  ⟨Skel.commit hk.1, fun b hb ↦ by cases hb with | commit _ _ h => exact hk.2 b h⟩

theorem query {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} {sk : List Op}
    {Q : α → Prop} (hk : ∀ rows, SkelP (k rows) sk Q) : SkelP (.query i ps k) (.query :: sk) Q :=
  ⟨Skel.query fun r ↦ (hk r).1, fun b hb ↦ by cases hb with | query _ _ r h => exact (hk r).2 b h⟩

theorem weaken {p : VerifierProgram α} {sk : List Op} {Q : α → Prop} (h : SkelP p sk Q) :
    SkelP p sk fun _ ↦ True := h.mono rfl fun _ _ ↦ trivial

end SkelP

/-! ## The leaves -/

/-- The skeleton of a proof of work of `bits` bits: none when `bits = 0`. -/
def skGrind (bits : ℕ) : List Op := if bits = 0 then [] else [.grind bits]

theorem skel_readScalar : SkelP VerifierProgram.readScalar [.read] fun _ ↦ True :=
  SkelP.read fun _ ↦ SkelP.ret trivial

theorem skel_sampleChallenge : SkelP VerifierProgram.sampleChallenge [.sample] fun _ ↦ True :=
  SkelP.sample fun _ ↦ SkelP.ret trivial

theorem skel_readScalars : ∀ n, SkelP (VerifierProgram.readScalars n) (List.replicate n .read)
    fun xs ↦ xs.length = n
  | 0 => SkelP.ret rfl
  | n + 1 => by
    unfold VerifierProgram.readScalars
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine (skel_readScalar.bind fun _ _ ↦ (skel_readScalars n).bind fun xs hxs ↦
      SkelP.ret (Q := fun ys : List E ↦ ys.length = n + 1) (by simp [hxs])).mono ?_ fun _ h ↦ h
    simp [List.replicate_succ]

theorem skel_sampleChallenges : ∀ n, SkelP (VerifierProgram.sampleChallenges n)
    (List.replicate n .sample) fun xs ↦ xs.length = n
  | 0 => SkelP.ret rfl
  | n + 1 => by
    unfold VerifierProgram.sampleChallenges
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine (skel_sampleChallenge.bind fun _ _ ↦ (skel_sampleChallenges n).bind fun xs hxs ↦
      SkelP.ret (Q := fun ys : List E ↦ ys.length = n + 1) (by simp [hxs])).mono ?_ fun _ h ↦ h
    simp [List.replicate_succ]

theorem skel_grindProofOfWork (bits : ℕ) :
    SkelP (VerifierProgram.grindProofOfWork bits) (skGrind bits) fun _ ↦ True := by
  unfold VerifierProgram.grindProofOfWork skGrind
  split
  · exact SkelP.ret trivial
  · exact SkelP.grind (SkelP.ret trivial)

theorem skel_require (c : Prop) [Decidable c] :
    SkelP (VerifierProgram.require c) [] fun _ ↦ c := by
  unfold VerifierProgram.require
  split
  · rename_i h; exact SkelP.ret h
  · exact SkelP.fail _ _

theorem skel_liftOption {α : Type} (o : Option α) : SkelP (liftOption o) [] fun a ↦ o = some a := by
  cases o with
  | none => exact SkelP.fail _ _
  | some a => exact SkelP.ret rfl

theorem skel_queryOpenings (i : ℕ) (ps : List ℕ) :
    SkelP (VerifierProgram.queryOpenings i ps) [.query] fun _ ↦ True :=
  SkelP.query fun _ ↦ SkelP.ret trivial

theorem skel_readCommitment (height width : ℕ) :
    SkelP (VerifierProgram.readCommitment height width) [.commit height width] fun _ ↦ True :=
  SkelP.commit (SkelP.ret trivial)

/-- The skeleton of one sumcheck round of `count` coefficients, with an equality factor or
without. -/
def skRound (count : ℕ) : Bool → List Op
  | false => .read :: List.replicate (count - 2) .read ++ skGrind (grindingBits (count - 1))
  | true => List.replicate (count - 1) .read ++ skGrind (grindingBits (count - 1 + 1))

theorem skel_sumcheckRoundPoly (count : ℕ) (claim : E) (e : Option E) :
    SkelP (sumcheckRoundPoly count claim e) (skRound count e.isSome) fun _ ↦ True := by
  cases e with
  | none =>
    unfold sumcheckRoundPoly
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine (skel_readScalar.bind fun _ _ ↦ (skel_readScalars _).bind fun _ _ ↦
      (skel_grindProofOfWork _).bind fun _ _ ↦ SkelP.ret trivial).mono ?_ fun _ h ↦ h
    simp [skRound]
  | some f =>
    unfold sumcheckRoundPoly
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine ((skel_readScalars _).bind fun _ _ ↦
      (skel_grindProofOfWork _).bind fun _ _ ↦ SkelP.ret trivial).mono ?_ fun _ h ↦ h
    simp [skRound]

/-- The skeleton of a sumcheck of `count` coefficients a round, its rounds' equality factors
present or absent as `eqs`. -/
def skSum (count : ℕ) (eqs : List Bool) : List Op :=
  eqs.flatMap fun b ↦ skRound count b ++ [.sample]

theorem skel_sumcheck (count : ℕ) : ∀ (claim : E) (eqs : List (Option E)),
    SkelP (sumcheck claim count eqs) (skSum count (eqs.map Option.isSome))
      fun r ↦ r.1.length = eqs.length
  | claim, [] => SkelP.ret rfl
  | claim, e :: eqs => by
    unfold sumcheck
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine ((skel_sumcheckRoundPoly count claim e).bind fun m _ ↦ skel_sampleChallenge.bind
      fun c _ ↦ (skel_sumcheck count _ eqs).bind fun r hr ↦
        SkelP.ret (Q := fun r' : List E × E ↦ r'.1.length = (e :: eqs).length)
          (by simp [hr])).mono ?_ fun _ h ↦ h
    simp [skSum, List.flatMap_cons, List.append_assoc]

/-- The samples of the query positions' loop. -/
def sqSamples (depth : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, remaining =>
    if remaining = 0 then 0 else 1 + sqSamples depth fuel (remaining - min (128 / depth) remaining)

theorem skel_sampleQueriesAux (depth : ℕ) : ∀ (fuel remaining : ℕ),
    SkelP (sampleQueriesAux depth fuel remaining)
      (List.replicate (sqSamples depth fuel remaining) .sample) fun _ ↦ True
  | 0, _ => SkelP.ret trivial
  | fuel + 1, remaining => by
    unfold sampleQueriesAux sqSamples
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    split
    · exact SkelP.ret trivial
    · refine (skel_sampleChallenge.bind fun _ _ ↦ (skel_sampleQueriesAux depth fuel _).bind
        fun _ _ ↦ SkelP.ret trivial).mono ?_ fun _ h ↦ h
      rw [Nat.add_comm 1, List.replicate_succ]
      simp

theorem skel_sampleQueries (depth count : ℕ) :
    SkelP (sampleQueries depth count) (List.replicate (sqSamples depth count count) .sample)
      fun _ ↦ True :=
  skel_sampleQueriesAux depth count count

end
end LeanVM.Protocol.EndToEnd.Sound
