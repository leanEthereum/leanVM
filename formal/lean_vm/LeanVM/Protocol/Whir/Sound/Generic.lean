/-
  LeanVM.Protocol.Whir.Sound.Generic

  Specifications of the verifier's prover moves for doom predicates that are functions of the
  commitments of the history: scalars, round polynomials, proofs of work and commitments keep
  them.
-/

module

public import LeanVM.Protocol.Whir.Sound.State

/-!
# Moves under a commitment invariant

The WHIR doom predicates (`LeanVM.Protocol.Whir.Sound.Level`) depend on a history only through
its commitments (the oracles' words) and on values the program carries (its state, the
challenges). A scalar, a proof of work, a sample and an opening commit nothing, so such a
predicate is kept by every move but a commitment, where the new word is appended.

* `readInv`, `readNInv`, `roundPolyInv`: scalars and the round polynomial
  `sumcheckRoundPoly 3 σ none` keep the invariant; the round polynomial comes out in the form
  `QuadOK q σ`.
* `grindInv`: a proof of work keeps it, the follower's lead discounted by `2^-b`.
* `commitInv`: a commitment appends its word.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Prog

@[expose] public section

/-! ## Commitments of histories -/

theorem commits_append (h l : List Ev) : commits (h ++ l) = commits h ++ commits l := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [commits, ih]

@[simp] theorem commits_read (h : List Ev) (x : E) : commits (h ++ [Ev.read x]) = commits h := by
  simp [commits_append, commits]

@[simp] theorem commits_grind (h : List Ev) (b : ℕ) : commits (h ++ [Ev.grind b]) = commits h := by
  simp [commits_append, commits]

@[simp] theorem commits_sample (h : List Ev) (c : E) :
    commits (h ++ [Ev.sample c]) = commits h := by
  simp [commits_append, commits]

@[simp] theorem commits_query (h : List Ev) (rows : List (List K)) :
    commits (h ++ [Ev.query rows]) = commits h := by
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
    Spec readE (fun h ↦ I (commits h)) (fun _ h ↦ I (commits h)) εmax 0 T :=
  Spec.readE (fun h₀ x hI ↦ by simpa using hI) hT

/-- `n` scalars keep a commitment invariant (lead at most the follower's). -/
noncomputable def readNInv (I : CInv) (hT : T ≤ εmax) :
    (n : ℕ) → Spec (readN n) (fun h ↦ I (commits h))
      (fun xs h ↦ xs.length = n ∧ I (commits h)) εmax T T
  | 0 => (Spec.ret (Post := fun xs h ↦ xs.length = 0 ∧ I (commits h)) []).mono
      (fun _ h ↦ ⟨rfl, h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1 => ((readInv I (T := T) hT).bind' fun x ↦
      (readNInv I hT n).bind' fun xs ↦
        (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-- **A round polynomial** keeps a commitment invariant and has `q(0) + q(1) = σ`. -/
noncomputable def roundPolyInv (I : CInv) (σ : E) (hT : T ≤ εmax) :
    Spec (sumcheckRoundPoly 3 σ none) (fun h ↦ I (commits h))
      (fun q h ↦ QuadOK q σ ∧ I (commits h)) εmax 0 T :=
  (readInv I (T := T) hT).bind' fun c₀ ↦
    (readNInv I hT 1).bind' fun tail ↦
      (Spec.ret (c₀ :: (σ + sumE tail) :: tail)).mono
        (fun h hI ↦ ⟨by
          obtain ⟨hl, -⟩ := hI
          match tail, hl with
          | [c₂], _ => exact quadOK_roundPoly σ c₀ c₂, hI.2⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- A proof of work keeps a commitment invariant. -/
noncomputable def grindInv (I : CInv) (b : ℕ) (hT : (2 : ENNReal)⁻¹ ^ b * T ≤ εmax) :
    Spec (grindP b) (fun h ↦ I (commits h)) (fun _ h ↦ I (commits h)) εmax 0 T :=
  Spec.grindP b (fun h₀ hI ↦ by simpa using hI) hT

/-- A commitment appends its word. -/
noncomputable def commitInv (I I' : CInv) (ht wd : ℕ)
    (hI : ∀ cs W, I cs → WellShaped wd W → I' (cs ++ [(ht, wd, W)])) (hT : T ≤ εmax) :
    Spec (commitP ht wd) (fun h ↦ I (commits h)) (fun _ h ↦ I' (commits h)) εmax 0 T :=
  Spec.commitP ht wd (fun h₀ W hI0 hW ↦ by simpa using hI _ W hI0 hW) hT

end
end LeanVM.Protocol.Whir.Sound
