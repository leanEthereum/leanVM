/-
  LeanVM.Protocol.Whir.Sound.Generic

  Specifications of the verifier's prover moves for doom predicates that are functions of the
  commitments of the history: scalars, round polynomials, proofs of work and commitments keep
  them.
-/

module

public import LeanVM.Protocol.Whir.Sound.State
public import LeanVM.Protocol.Compile.SpecRules.Leaves

/-!
# Moves under a commitment invariant

The WHIR doom predicates (`LeanVM.Protocol.Whir.Sound.Level`) depend on a history only through
its commitments (the oracles' words) and on values the program carries (its state, the
challenges). A scalar, a proof of work, a sample and an opening commit nothing, so such a
predicate is kept by every move but a commitment, where the new word is appended.

* `readInv`, `readNInv`, `roundPolyInv`: scalars and the round polynomial
  `sumcheckRoundPoly 3 σ none` keep the invariant; the round polynomial comes out in the form
  `QuadOK q σ`.
* `grindInv`: a proof of work of `b > 0` bits keeps it, the follower's lead discounted by `2^-b`.
* `commitInv`: a commitment appends its word.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier VerifierProgram

@[expose] public section

/-! ## Commitments of histories -/

@[simp] theorem commits_read (h : List Ev) (x : E) : commits (h ++ [Ev.read x]) = commits h := by
  simp [commits_append, commits]

@[simp] theorem commits_grind (h : List Ev) (b : ℕ) : commits (h ++ [Ev.grind b]) = commits h := by
  simp [commits_append, commits]

@[simp] theorem commits_sample (h : List Ev) (c : E) :
    commits (h ++ [Ev.sample c]) = commits h := by
  simp [commits_append, commits]

@[simp] theorem commits_commit (h : List Ev) (ht wd : ℕ) (W : Word) :
    commits (h ++ [Ev.commit ht wd W]) = commits h ++ [(ht, wd, W)] := by
  simp [commits_append, commits]

/-! ## Moves -/

/-- An invariant of the commitments. -/
abbrev CInv : Type := List (ℕ × ℕ × Word) → Prop

variable {εmax T : ENNReal}

/-- A scalar keeps a commitment invariant. -/
noncomputable def readInv (I : CInv) (hT : T ≤ εmax) :
    Spec readScalar (fun h ↦ I (commits h)) (fun _ h ↦ I (commits h)) εmax 0 T :=
  Spec.readE (fun h₀ x hI ↦ by simpa using hI) hT

/-- `n` scalars keep a commitment invariant (lead at most the follower's). -/
noncomputable def readNInv (I : CInv) (hT : T ≤ εmax) :
    (n : ℕ) → Spec (readScalars n) (fun h ↦ I (commits h))
      (fun xs h ↦ xs.length = n ∧ I (commits h)) εmax T T
  | 0 => (Spec.ret (Post := fun xs h ↦ xs.length = 0 ∧ I (commits h)) []).mono
      (fun _ h ↦ ⟨rfl, h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1 => ((readInv I (T := T) hT).bind' fun x ↦
      (readNInv I hT n).bind' fun xs ↦
        (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-- The round polynomial has three coefficients and `q(0) + q(1) = σ`. -/
def QuadOK (quad : List E) (σ : E) : Prop :=
  ∃ c₀ c₁ c₂, quad = [c₀, c₁, c₂] ∧ polyEval quad 0 + polyEval quad 1 = σ

/-- The quadratic `sumcheckRoundPoly 3 σ none` builds from `c₀` and `[c₂]` has `q(0)+q(1) = σ`. -/
theorem quadOK_roundPoly (σ c₀ c₂ : E) :
    QuadOK (c₀ :: (σ + sumE [c₂]) :: [c₂]) σ := by
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [polyEval_three, sumE, List.foldl_cons, List.foldl_nil, zero_add]
  ring_nf
  rw [show (2 : E) = 0 from CharTwo.two_eq_zero]
  ring

/-- **A round polynomial** keeps a commitment invariant and has `q(0) + q(1) = σ`; its grind,
for degree two, is of `0` bits. -/
noncomputable def roundPolyInv (I : CInv) (σ : E) (hT : T ≤ εmax) :
    Spec (sumcheckRoundPoly 3 σ none) (fun h ↦ I (commits h))
      (fun q h ↦ QuadOK q σ ∧ I (commits h)) εmax 0 T :=
  have hb0 : grindingBits (3 - 1) = 0 := by decide
  (readInv I (T := T) hT).bind' fun c₀ ↦
    (readNInv I hT 1).bind' fun tail ↦
      ((Spec.grindP (Pre := fun h ↦ tail.length = 1 ∧ I (commits h))
        (Post := fun _ h ↦ tail.length = 1 ∧ I (commits h)) (grindingBits (3 - 1))
        (fun h₀ hp ↦ by simpa [Spec.grindEvs, hb0] using hp)
        (T := T) (by simpa [hb0] using hT)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
          (by simp [hb0]) le_rfl).bind' fun _ ↦
      (Spec.ret (c₀ :: (σ + sumE tail) :: tail)).mono
        (fun h hI ↦ ⟨by
          obtain ⟨hl, -⟩ := hI
          match tail, hl with
          | [c₂], _ => exact quadOK_roundPoly σ c₀ c₂, hI.2⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- A proof of work of `b ≥ 1` bits keeps a commitment invariant. -/
noncomputable def grindInv (I : CInv) {b : ℕ} (hb : b ≠ 0) (hT : (2 : ENNReal)⁻¹ ^ b * T ≤ εmax) :
    Spec (grindProofOfWork b) (fun h ↦ I (commits h)) (fun _ h ↦ I (commits h)) εmax 0 T :=
  Spec.grindPos hb (fun h₀ hI ↦ by simpa using hI) hT

/-- A commitment appends its word. -/
noncomputable def commitInv (I I' : CInv) (ht wd : ℕ)
    (hI : ∀ cs W, I cs → WellShaped wd W → I' (cs ++ [(ht, wd, W)])) (hT : T ≤ εmax) :
    Spec (readCommitment ht wd) (fun h ↦ I (commits h)) (fun _ h ↦ I' (commits h)) εmax 0 T :=
  Spec.commitP ht wd (fun h₀ W hI0 hW ↦ by simpa using hI _ W hI0 hW) hT

end
end LeanVM.Protocol.Whir.Sound
