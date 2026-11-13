/-
  LeanVM.Guest.B1.Bits.Templates

  The expansions of the guest's inline field-packing helpers as statement templates.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreData

/-!
# The inline field-packing helpers (TRIAGE G #1-4)

* `splitLimbsT w b` (`split_limbs(w)`): the hinted low limb `b`, the derived high limb `b + 3`;
  `holds_splitLimbsT`: it holds exactly when the limbs are `w`'s limbs (`split_iff`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- `split_limbs(w)`'s atoms from the value `b`: the hinted low limb `b`, `w + lo` at `b + 1`,
`Y_INV` at `b + 2`, the derived high limb `b + 3`, both asserted in `K`. -/
def splitLimbsT (w : V) (b : ℕ) : List Stmt :=
  [.atom (.hint (.limbs w [.n b])), .atom (.add (.n (b + 1)) w (.n b)),
    .atom (.const (.n (b + 2)) (word 2 1)), .atom (.mul (.n (b + 3)) (.n (b + 1)) (.n (b + 2))),
    .atom (.assertInK (.n b) (.n (b + 3)))]

/-- **`split_limbs`**: the block holds exactly when the hinted limb is `w`'s low limb; the derived
`.n (b + 3)` is then its high limb. Every word splits. -/
theorem holds_splitLimbsT (w : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (splitLimbsT w b) next kret ↔
      (σ (.n b) = ofK ((σ w).limb 0) ∧ σ (.n (b + 1)) = σ w + σ (.n b) ∧
        σ (.n (b + 2)) = word 2 1 ∧ σ (.n (b + 3)) = ofK ((σ w).limb 1)) ∧ next := by
  simp only [splitLimbsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  constructor
  · rintro ⟨h1, h2, h3, ⟨hlo, hhi⟩, hn⟩
    rw [h3, h2, h1, word_y_inv] at hhi
    have hl := (split_iff _ _).mp ⟨hlo, hhi⟩
    refine ⟨⟨hl, h1, h2, ?_⟩, hn⟩
    rw [h3, h2, h1, hl, word_y_inv, split_hi]
  · rintro ⟨⟨hl, h1, h2, h3⟩, hn⟩
    refine ⟨h1, h2, ?_, ⟨?_, ?_⟩, hn⟩
    · rw [h3, h2, h1, hl, word_y_inv, split_hi]
    · rw [hl]; exact ofK_isInK _
    · rw [h3]; exact ofK_isInK _

/-- The honest values of `splitLimbsT` on a word `w`: its low limb, `w + w₀`, `y⁻¹`, its high
limb. -/
def splitLimbsVals (w : E) : ℕ → E
  | 0 => ofK (w.limb 0)
  | 1 => w + ofK (w.limb 0)
  | 2 => word 2 1
  | _ => ofK (w.limb 1)

/-- `pack64x2(a, b)`'s atoms from the value `b0`: both limbs asserted in `K`, `Y_TOWER` at `b0`,
`y·b` at `b0 + 1`, the cell `a + y·b` at `b0 + 2`. -/
def pack64x2T (a b : V) (b0 : ℕ) : List Stmt :=
  [.atom (.assertInK a b), .atom (.const (.n b0) (word 0 1)), .atom (.mul (.n (b0 + 1)) (.n b0) b),
    .atom (.add (.n (b0 + 2)) a (.n (b0 + 1)))]

/-- **`pack64x2`**: the block holds exactly when both limbs lie in `K`; the cell is then the word
with those limbs. -/
theorem holds_pack64x2T (a b : V) (b0 : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (pack64x2T a b b0) next kret ↔
      (IsInK (σ a) ∧ IsInK (σ b) ∧ σ (.n b0) = word 0 1 ∧ σ (.n (b0 + 1)) = σ (.n b0) * σ b ∧
        σ (.n (b0 + 2)) = σ a + σ (.n (b0 + 1))) ∧ next := by
  simp only [pack64x2T, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

/-- The cell `pack64x2` builds, from its block. -/
theorem pack64x2T_cell {a b : V} {b0 : ℕ}
    (h : IsInK (σ a) ∧ IsInK (σ b) ∧ σ (.n b0) = word 0 1 ∧ σ (.n (b0 + 1)) = σ (.n b0) * σ b ∧
      σ (.n (b0 + 2)) = σ a + σ (.n (b0 + 1))) :
    σ (.n (b0 + 2)) = E.ofLimbs ((σ a).limb 0) ((σ b).limb 0) := by
  obtain ⟨ha, hb, h0, h1, h2⟩ := h
  rw [h2, h1, h0, word_y, pack64x2_eq ha hb]

end
end LeanVM.Guest.B1
