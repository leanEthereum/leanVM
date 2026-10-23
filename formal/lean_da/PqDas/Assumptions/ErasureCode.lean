/-
# Erasure codes

We abstract an erasure code as a plain encoding function and define the code as
the image of the encoding map. This is all the security proofs of the erasure
code commitment scheme need: reconstruction-style properties (e.g., "any `k`
symbols uniquely determine the codeword") only matter when compiling an erasure
code commitment into a full data availability sampling scheme, which is not
formalized here. Compare Foundations of Data Availability Sampling
(eprint 2023/1079), Section 6.

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import VCVio.CryptoFoundations.CommitmentScheme

namespace PqDas

/-- An erasure code with message alphabet `Γ`, code alphabet `Λ`, message
length `k`, and code length `n`, given by its encoding function. -/
structure ErasureCode (Γ Λ : Type) (k n : ℕ) where
  /-- The encoding function of the code. -/
  encode : (Fin k → Γ) → (Fin n → Λ)

namespace ErasureCode

variable {Γ Λ : Type} {k n : ℕ}

/-- The code itself: the set of codewords, i.e. the image of `encode`. -/
def code (C : ErasureCode Γ Λ k n) : Set (Fin n → Λ) := Set.range C.encode

/-- Codeword membership is decidable for finite alphabets. This is used to
state the winning conditions of security games as `Bool`s. -/
instance decidableMemCode (C : ErasureCode Γ Λ k n) [Fintype Γ] [DecidableEq Λ] :
    DecidablePred (· ∈ C.code) := fun c =>
  decidable_of_iff (∃ m, C.encode m = c) Set.mem_range

@[simp]
lemma encode_mem_code (C : ErasureCode Γ Λ k n) (m : Fin k → Γ) :
    C.encode m ∈ C.code := Set.mem_range_self m

/-- A list of position/symbol pairs is *consistent* with the code if some
codeword agrees with all of them. The winning condition of the code-binding
game is the negation of this, for the pairs the adversary opened. -/
def Consistent (C : ErasureCode Γ Λ k n) (openings : List (Fin n × Λ)) : Prop :=
  ∃ m : Fin k → Γ, ∀ p ∈ openings, C.encode m p.1 = p.2

/-- Consistency is decidable for finite alphabets. -/
instance decidableConsistent (C : ErasureCode Γ Λ k n) [Fintype Γ] [DecidableEq Λ]
    (openings : List (Fin n × Λ)) : Decidable (C.Consistent openings) :=
  decidable_of_iff (∃ m : Fin k → Γ, ∀ p ∈ openings, C.encode m p.1 = p.2) Iff.rfl

lemma consistent_iff_exists_codeword (C : ErasureCode Γ Λ k n)
    (openings : List (Fin n × Λ)) :
    C.Consistent openings ↔ ∃ c ∈ C.code, ∀ p ∈ openings, c p.1 = p.2 := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨C.encode m, C.encode_mem_code m, hm⟩
  · rintro ⟨c, ⟨m, rfl⟩, hc⟩
    exact ⟨m, hc⟩

end ErasureCode

end PqDas
