/-
# Erasure codes

We abstract an erasure code as a plain encoding function and define the code as
the image of the encoding map. This is all the security proofs of the erasure
code commitment scheme need: reconstruction-style properties (e.g., "any `k`
symbols uniquely determine the codeword") only matter when compiling an erasure
code commitment into a full data availability sampling scheme, which is not
formalized here. Compare Foundations of Data Availability Sampling
(eprint 2023/1079), Section 6.

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified for VCVio afa6593.
-/
module

public import VCVio.CryptoFoundations.CommitmentScheme
public import PqDas.Defs

@[expose] public section

namespace PqDas

namespace ErasureCode

variable {Γ Λ : Type} {k n : ℕ}

@[simp]
lemma encode_mem_code (C : ErasureCode Γ Λ k n) (m : Fin k → Γ) :
    C.encode m ∈ C.code := Set.mem_range_self m

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
