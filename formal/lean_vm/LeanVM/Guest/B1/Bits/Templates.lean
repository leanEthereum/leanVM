/-
  LeanVM.Guest.B1.Bits.Templates

  The expansions of the guest's inline field-packing helpers as statement templates.
-/

module

public import LeanVM.Guest.B1.Common.Basic

/-!
# The inline field-packing helpers (TRIAGE G #1-4)

* `canonicalLimbsT w b` (`canonical_limbs(w)`, G:569-575; also the body of `assert_canonical`,
  G:558-565): the hinted low limb `b`, the derived high limb `b + 3`; `holds_canonicalLimbsT`: it
  holds exactly when `w` is canonical and the limbs are its limbs (`split_iff`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- `canonical_limbs(w)`'s atoms from the value `b`. -/
def canonicalLimbsT (w : V) (b : ℕ) : List Stmt :=
  [.atom (.hint (.limbs w [.n b])), .atom (.add (.n (b + 1)) w (.n b)),
    .atom (.const (.n (b + 2)) (word 1 0 1)), .atom (.mul (.n (b + 3)) (.n (b + 1)) (.n (b + 2))),
    .atom (.assertInK (.n b) (.n (b + 3)))]

/-- **`canonical_limbs`** (TRIAGE #2, #3): the block holds exactly when `w` is canonical and the
hinted limb is its low limb; the derived `.n (b + 3)` is then its high limb. -/
theorem holds_canonicalLimbsT (w : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (canonicalLimbsT w b) next kret ↔
      (IsCanonical128 (σ w) ∧ σ (.n b) = ofK ((σ w).limb 0) ∧ σ (.n (b + 1)) = σ w + σ (.n b) ∧
        σ (.n (b + 2)) = word 1 0 1 ∧ σ (.n (b + 3)) = ofK ((σ w).limb 1)) ∧ next := by
  simp only [canonicalLimbsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  constructor
  · rintro ⟨h1, h2, h3, ⟨hlo, hhi⟩, hn⟩
    rw [h3, h2, h1, word_y_inv] at hhi
    obtain ⟨hc, hl⟩ := (split_iff _ _).mp ⟨hlo, hhi⟩
    refine ⟨⟨hc, hl, h1, h2, ?_⟩, hn⟩
    rw [h3, h2, h1, hl, word_y_inv, split_hi hc]
  · rintro ⟨⟨hc, hl, h1, h2, h3⟩, hn⟩
    refine ⟨h1, h2, ?_, ⟨?_, ?_⟩, hn⟩
    · rw [h3, h2, h1, hl, word_y_inv, split_hi hc]
    · rw [hl]; exact ofK_isInK _
    · rw [h3]; exact ofK_isInK _

/-- The honest values of `canonicalLimbsT` on a canonical word `w`: its low limb, `w + w₀`, `y⁻¹`,
its high limb. -/
def canonicalLimbsVals (w : E) : ℕ → E
  | 0 => ofK (w.limb 0)
  | 1 => w + ofK (w.limb 0)
  | 2 => word 1 0 1
  | _ => ofK (w.limb 1)

end
end LeanVM.Guest.B1
