import LeanVM.Protocol.ToArkLib.Typed.SendChecked
import LeanVM.Protocol.ToArkLib.Typed.SampleChallenge
import LeanVM.Protocol.ToArkLib.Typed.Append
import LeanVM.Protocol.Field

/-!
# The typed one-round components

* **A checked message** over `ℕ`: the statement is a target, the witness the value the prover
  sends, the check that the message is the target, the verdict its successor. Completeness, and
  knowledge soundness at no error with the extractor that keeps the witness, have inhabitants;
  the verdict and the extractor compute. Without its check the same message has no security:
  a message carries a statement with no witness into the output relation.
* **A checked challenge** over `E`: the statement is a claimed value, true when zero, and the
  challenge scales it. Completeness, and knowledge soundness at `1 / |E|` (a nonzero claim scales
  to zero at one challenge), have inhabitants. Scaling by nothing (the verdict zero at every
  challenge) has no security below error one.
* **In sequence**: a checked message that the claim is zero, then the challenge that scales it.
  Completeness and knowledge soundness compose (`Complete.append`, `Security.append`, at the two
  errors side by side), the composed verdict and extractor compute.

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanVMTests.Protocol.Typed

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Typed
open scoped NNReal

/-- No oracles. -/
abbrev NoO : Fin 0 → Type := fun _ ↦ Unit

/-- The empty family of oracles. -/
def noO : ∀ i, NoO i := fun i ↦ i.elim0

/-! ## A checked message -/

/-- The prover sends its witness; the verifier checks it is the target and outputs its
successor. -/
def say1 : Def NoO ℕ ℕ ℕ ℕ (saySlot ℕ) :=
  sendChecked NoO ℕ (fun p ↦ p.2) (fun s m ↦ s == m) (fun _ m ↦ m + 1)

/-- The input relation: the target is the witness. -/
def sayIn : Set ((ℕ × ∀ i, NoO i) × ℕ) := {p | p.1.1 = p.2}

/-- The output relation: the statement is the witness's successor. -/
def sayOut : Set ((ℕ × ∀ i, NoO i) × ℕ) := {p | p.1.1 = p.2 + 1}

/-- Completeness. -/
theorem say1Complete : Complete say1 sayIn sayOut :=
  sendCheckedComplete fun s _ w h ↦ ⟨by simp [show s = w from h], rfl⟩

/-- Knowledge soundness at no error. -/
def say1Security : Security say1 sayIn sayOut (sayErrors ℕ) :=
  sendCheckedSecurity fun s _ w m hc hout ↦ by
    have hm : s = m := by simpa using hc
    have hw : m + 1 = w + 1 := hout
    show s = w
    omega

-- The verdict: the successor of the target when the message is the target, a rejection
-- otherwise.
#guard say1.verdict 3 ⟨3, PUnit.unit⟩ == some 4
#guard say1.verdict 3 ⟨2, PUnit.unit⟩ == none

/-- The extractor's backward map at the message `3`. -/
def sayBack (w : ℕ) : ℕ := ((say1Security.extractor 3 noO) 3).2.1 w

-- The extractor computes, and keeps the witness.
#guard sayBack 7 == 7

/-- Without the check, a message carries a statement with no witness (none is related to the
target in the empty relation) into the output relation: there is no security. -/
theorem say1_unchecked_no_security {err : Errors (sayTree ℕ) (sayRoles ℕ)}
    (S : Security (sendChecked NoO ℕ (fun p ↦ p.2) (fun _ _ ↦ true) (fun _ m ↦ m + 1))
      (∅ : Set ((ℕ × ∀ i, NoO i) × ℕ)) sayOut err) : False :=
  sendChecked_no_security S 3 noO (fun _ h ↦ h) 5 rfl 5 rfl

/-! ## A checked challenge -/

/-- The verifier scales the claim by the challenge. -/
def draw1 : Def NoO E Unit E Unit (drawSlot E) :=
  sampleChallenge NoO E (fun _ ↦ true) fun a c ↦ a * c

/-- The claim is true when zero. -/
def zeroRel : Set ((E × ∀ i, NoO i) × Unit) := {p | p.1.1 = 0}

/-- Completeness: zero scales to zero. -/
theorem draw1Complete : Complete draw1 zeroRel zeroRel :=
  sampleChallengeComplete fun s _ _ h ↦ ⟨rfl, fun c ↦ by
    show s * c = 0
    rw [show s = 0 from h, zero_mul]⟩

/-- A nonzero claim scales to zero at one challenge only, zero. -/
theorem draw1_bad (s : E) (o : ∀ i, NoO i) :
    Nat.card {c // badChallenge (f := fun a c ↦ a * c) (relIn := zeroRel) (relOut := zeroRel)
      s o c} ≤ 1 := by
  have h : ∀ c : {c // badChallenge (f := fun a c ↦ a * c) (relIn := zeroRel)
      (relOut := zeroRel) s o c}, c.1 = 0 := by
    rintro ⟨c, w, hs, hc⟩
    have hs : s ≠ 0 := hs
    have hc : s * c = 0 := hc
    exact (mul_eq_zero.mp hc).resolve_left hs
  calc Nat.card {c // badChallenge (f := fun a c ↦ a * c) (relIn := zeroRel)
          (relOut := zeroRel) s o c}
      ≤ Nat.card Unit :=
        Nat.card_le_card_of_injective (fun _ ↦ ()) fun x y _ ↦
          Subtype.ext ((h x).trans (h y).symm)
    _ = 1 := by simp

/-- Knowledge soundness at `1 / |E|`. -/
def draw1Security :
    Security draw1 zeroRel zeroRel (drawErrors E ((1 : ℕ) / (Nat.card E : ℝ≥0))) :=
  sampleChallengeSecurity 1 fun s o _ ↦ draw1_bad s o

/-- The extractor's backward map at the challenge `0`. -/
def drawBack (w : Unit) : Unit := ((draw1Security.extractor 1 noO) 0).2.1 w

-- The extractor computes.
#guard drawBack () == ()

/-- Scaling by nothing carries the nonzero claim `1` to zero at every challenge: no security is
below error one. -/
theorem drawZero_one_le {e : ℝ≥0}
    (S : Security (sampleChallenge NoO E (fun _ ↦ true) fun (_ _ : E) ↦ (0 : E)) zeroRel zeroRel
      (drawErrors E e)) : 1 ≤ e :=
  sampleChallenge_one_le S 1 noO (fun _ h ↦ one_ne_zero (h : (1 : E) = 0)) rfl
    fun _ ↦ ⟨(), rfl⟩

/-! ## In sequence -/

/-- The prover sends the claim; the verifier checks it is the statement and records it. -/
def sayZero : Def NoO E Unit E Unit (saySlot E) :=
  sendChecked NoO E (fun p ↦ p.1.1) (fun a m ↦ a == m) fun _ m ↦ m

/-- The message's security: a message equal to the claim, recorded as zero, means a zero
claim. -/
def sayZeroSecurity : Security sayZero zeroRel zeroRel (sayErrors E) :=
  sendCheckedSecurity fun a _ _ m hc hout ↦ by
    have hm : a = m := by simpa using hc
    have h0 : m = 0 := hout
    show a = 0
    rw [hm, h0]

/-- The message, then the challenge. -/
def twoSteps : Def NoO E Unit E Unit ((saySlot E).append (drawSlot E)) := sayZero.append draw1

/-- Completeness in sequence. -/
theorem twoStepsComplete : Complete twoSteps zeroRel zeroRel :=
  (sendCheckedComplete fun s _ _ h ↦ ⟨by simp, h⟩).append draw1Complete

/-- Knowledge soundness in sequence, at no error on the message and `1 / |E|` on the
challenge. -/
def twoStepsSecurity :
    Security twoSteps zeroRel zeroRel (Errors.append sayZero.tree sayZero.roles (sayErrors E)
      (drawErrors E ((1 : ℕ) / (Nat.card E : ℝ≥0)))) :=
  sayZeroSecurity.append draw1Security

/-- The composed verdict on the path that sends `m` and draws `c`. -/
def twoVerdict (a m c : E) : Option E := twoSteps.verdict a ⟨m, c, PUnit.unit⟩

-- A message equal to the claim is accepted and scaled; another is rejected before the challenge.
#guard twoVerdict 1 1 1 == some 1
#guard twoVerdict 1 0 1 == none

/-- The composed extractor's backward map at the message `0`. -/
def twoBack (w : Unit) : Unit := ((twoStepsSecurity.extractor 0 noO) 0).2.1 w

-- The composed extractor computes.
#guard twoBack () == ()

end LeanVMTests.Protocol.Typed
