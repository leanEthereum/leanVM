/-
  LeanVM.Prover.Complete.CostCalc

  The events of a verifier program that the wire's stream count does not see: challenges, packed
  messages, proofs of work and commitments, with the commitments' shapes.
-/

module

public import LeanVM.Wire.HonestShape

/-!
# Counting a program's other events

`LeanVM.Wire.Wired` bounds, along every run of a program, the stream it reads (a scalar one, a packed
message its length, a nonce one, a root two) and its openings. The queries of a run also pay for
what the stream does not count: a challenge (a permutation), a packed draw (a permutation per
challenge at most), a packed message's first permutation, a proof of work's permutation, and
for the prover each commitment's tree. `SampLE p n`: along every run of `p` there are at most
`n` such events (a challenge `1`, a packed draw of `m` its `m`, a packed message `1`, a proof of
work `1`, a commitment `1`), and every commitment has height at most `commitMaxHeight` and width at most `commitMaxWidth`.
It composes over a bind, the continuation at the values the first part may return
(`SampLE.bind`, `SampLE.seq`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

variable {α β : Type}

/-- The greatest height of a commitment: the wire's `MAX_HEIGHT`. -/
def commitMaxHeight : ℕ := 32

/-- The greatest width of a commitment: `2 · 2^6` words. -/
def commitMaxWidth : ℕ := 128

/-- **At most `n` events besides the stream on every run, the commitments within the bounds.** -/
def SampLE : VerifierProgram α → ℕ → Prop
  | .ret _, _ => True
  | .fail, _ => True
  | .read k, n => True ∧ ∀ x, SampLE (k x) n
  | .sample k, n => 1 ≤ n ∧ ∀ x, SampLE (k x) (n - 1)
  | .readPacked _ k, n => 1 ≤ n ∧ ∀ xs, SampLE (k xs) (n - 1)
  | .samplePacked m k, n => m ≤ n ∧ ∀ xs, SampLE (k xs) (n - m)
  | .grind _ k, n => 1 ≤ n ∧ SampLE k (n - 1)
  | .commit h w k, n => h ≤ commitMaxHeight ∧ w ≤ commitMaxWidth ∧ 1 ≤ n ∧ SampLE k (n - 1)
  | .query _ _ k, n => True ∧ ∀ rows, SampLE (k rows) n

namespace SampLE

theorem mono {p : VerifierProgram α} {n m : ℕ} (h : SampLE p n) (hnm : n ≤ m) :
    SampLE p m := by
  induction p generalizing n m with
  | ret a => trivial
  | fail => trivial
  | read k ih => exact ⟨trivial, fun x ↦ ih x (h.2 x) hnm⟩
  | sample k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | readPacked k_n k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | samplePacked m' k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | grind b k ih => exact ⟨by have := h.1; omega, ih h.2 (by omega)⟩
  | commit ht w k ih => exact ⟨h.1, h.2.1, by have := h.2.2.1; omega, ih h.2.2.2 (by omega)⟩
  | query i ps k ih => exact ⟨trivial, fun r ↦ ih r (h.2 r) hnm⟩

/-- **Sequencing**: the counts add, the continuation at the values the first part may return. -/
theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {a b : ℕ}
    (hp : SampLE p a) (hf : ∀ x, VerifierProgram.ReturnsAny p x → SampLE (f x) b) :
    SampLE (p.bind f) (a + b) := by
  induction p generalizing a with
  | ret x => exact (hf x (.ret x)).mono (by omega)
  | fail => trivial
  | read k ih => exact ⟨trivial, fun x ↦ ih x (hp.2 x) fun y hy ↦ hf y (.read x hy)⟩
  | sample k ih =>
    refine ⟨by have := hp.1; omega, fun x ↦ ?_⟩
    have := ih x (hp.2 x) fun y hy ↦ hf y (.sample x hy)
    rwa [show a - 1 + b = a + b - 1 by have := hp.1; omega] at this
  | readPacked m k ih =>
    refine ⟨by have := hp.1; omega, fun xs ↦ ?_⟩
    have := ih xs (hp.2 xs) fun y hy ↦ hf y (.readPacked m xs hy)
    rwa [show a - 1 + b = a + b - 1 by have := hp.1; omega] at this
  | samplePacked m k ih =>
    refine ⟨by have := hp.1; omega, fun xs ↦ ?_⟩
    have := ih xs (hp.2 xs) fun y hy ↦ hf y (.samplePacked m xs hy)
    rwa [show a - m + b = a + b - m by have := hp.1; omega] at this
  | grind bits k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2 fun y hy ↦ hf y (.grind bits hy)
    rwa [show a - 1 + b = a + b - 1 by have := hp.1; omega] at this
  | commit ht w k ih =>
    refine ⟨hp.1, hp.2.1, by have := hp.2.2.1; omega, ?_⟩
    have := ih hp.2.2.2 fun y hy ↦ hf y (.commit ht w hy)
    rwa [show a - 1 + b = a + b - 1 by have := hp.2.2.1; omega] at this
  | query i ps k ih => exact ⟨trivial, fun r ↦ ih r (hp.2 r) fun y hy ↦ hf y (.query i ps r hy)⟩

/-- Sequencing against a fixed budget: the first part spends `a` of `n`. -/
theorem seq {p : VerifierProgram α} {f : α → VerifierProgram β} {a n : ℕ} (hp : SampLE p a)
    (hf : ∀ x, VerifierProgram.ReturnsAny p x → SampLE (f x) (n - a)) (ha : a ≤ n) :
    SampLE (p >>= f) n :=
  (bind hp hf).mono (by omega)

theorem ret' (a : α) (n : ℕ) : SampLE (VerifierProgram.ret a) n := trivial

theorem pure' (a : α) (n : ℕ) : SampLE (pure a : VerifierProgram α) n := trivial

theorem readE : SampLE VerifierProgram.readScalar 0 := ⟨trivial, fun _ ↦ trivial⟩

theorem sampleE : SampLE VerifierProgram.sampleChallenge 1 := ⟨le_rfl, fun _ ↦ trivial⟩

theorem readN : ∀ n, SampLE (VerifierProgram.readScalars n) 0
  | 0 => trivial
  | n + 1 => seq readE (fun _ _ ↦ seq (readN n) (fun _ _ ↦ trivial) le_rfl) le_rfl

theorem sampleN : ∀ n, SampLE (VerifierProgram.sampleChallenges n) n
  | 0 => trivial
  | n + 1 => seq sampleE (fun _ _ ↦ seq (sampleN n) (fun _ _ ↦ trivial) (by omega)) (by omega)

theorem readPackedP (m : ℕ) : SampLE (VerifierProgram.readScalarsPacked m) 1 :=
  ⟨le_rfl, fun _ ↦ trivial⟩

theorem samplePackedP (m : ℕ) : SampLE (VerifierProgram.sampleChallengesPacked m) m :=
  ⟨le_rfl, fun _ ↦ trivial⟩

theorem grindP (bits : ℕ) : SampLE (VerifierProgram.grindProofOfWork bits) 1 := by
  unfold VerifierProgram.grindProofOfWork
  split
  · trivial
  · exact ⟨le_rfl, trivial⟩

theorem commitP {h w : ℕ} (hh : h ≤ commitMaxHeight) (hw : w ≤ commitMaxWidth) :
    SampLE (VerifierProgram.readCommitment h w) 1 := ⟨hh, hw, le_rfl, trivial⟩

theorem queryP (i : ℕ) (ps : List ℕ) : SampLE (VerifierProgram.queryOpenings i ps) 0 :=
  ⟨trivial, fun _ ↦ trivial⟩

theorem require (c : Prop) [Decidable c] : SampLE (VerifierProgram.require c) 0 := by
  unfold VerifierProgram.require
  split <;> trivial

theorem liftOptionP (o : Option α) : SampLE (liftOption o) 0 := by
  cases o <;> trivial

theorem ite {c : Prop} [Decidable c] {p q : VerifierProgram α} {n : ℕ} (hp : SampLE p n)
    (hq : SampLE q n) : SampLE (if c then p else q) n := by
  split
  · exact hp
  · exact hq

theorem sumcheckRoundPolyP (count : ℕ) (claim : E) (e : Option E) :
    SampLE (sumcheckRoundPoly count claim e) 1 := by
  cases e with
  | none =>
    exact seq readE (fun _ _ ↦ seq (readN _) (fun _ _ ↦ seq (grindP _) (fun _ _ ↦ trivial)
      le_rfl) (Nat.zero_le _)) (Nat.zero_le _)
  | some r =>
    exact seq (readN _) (fun _ _ ↦ seq (grindP _) (fun _ _ ↦ trivial) le_rfl) (Nat.zero_le _)

theorem sumcheckP (count : ℕ) : ∀ (claim : E) (eqs : List (Option E)),
    SampLE (sumcheck claim count eqs) (eqs.length * 2)
  | _, [] => trivial
  | claim, e :: es => by
    have hl : (e :: es).length * 2 = es.length * 2 + 2 := by
      simp only [List.length_cons, Nat.succ_mul]
    refine seq (sumcheckRoundPolyP count claim e) (fun _ _ ↦ seq sampleE (fun _ _ ↦
      seq (sumcheckP count _ es) (fun _ _ ↦ trivial) ?_) ?_) ?_ <;> omega

end SampLE

end LeanVM.Prover.Complete.Cost

end
