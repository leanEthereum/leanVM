/-
  LeanVM.Guest.B1.Da.PaddingComplete

  `da_padding`, completely: a row count `1 ≤ r ≤ LeanDa.maxRows` gives the core IR relation
  (TRIAGE G #91).
-/

module

public import LeanVM.Guest.B1.Da.Padding
public import LeanVM.Guest.B1.Digest.CompleteSmall
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# `da_padding`, completely

On a memory image (its range check reads below `2^16`), `da_padding(g^r)` holds for
`1 ≤ r ≤ LeanDa.maxRows`, returning `g^(LeanDa.maxRows - r)`: the hinted inverse of `g^r + 1`
(nonzero, `r ≠ 0`), the quotient `g^(LeanDa.maxRows - r)`, the range check within its bound.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- `da_padding`'s meaning gives its core IR, on a memory defined below `2^16`. -/
def da_padding_complete_Spec : Prop :=
  ∀ (rd : Reader), Sig.MemOK rd (2 ^ 16) → ∀ r : ℕ, 1 ≤ r → r ≤ LeanDa.maxRows →
    coreProgram.Rel rd "da_padding" [gen ^ r] [gen ^ (LeanDa.maxRows - r)]

theorem da_padding_body : Fn.body fn% «da_padding» = [
    .atom (.const (.n 1) (word 1 0)), .atom (.add (.n 2) (.n 0) (.n 1)),
    .atom (.hint (.inverse (.n 2) (.n 3))), .atom (.assertNe (.n 2) (.n 3) (.n 4)),
    .atom (.const (.n 5) (word (2 ^ guest_const% DA_MAX_ROWS) 0)),
    .atom (.rangeCheck (.n 0) (.n 6) (.n 7) (.n 8) (.n 5)),
    .atom (.const (.n 9) (word (2 ^ guest_const% DA_MAX_ROWS) 0)),
    .atom (.mul (.n 9) (.n 10) (.n 0)), .atom (.copy (.n 11) (.n 10)), .ret [.n 11]] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 10000 in
/-- **`da_padding` is complete** on a memory defined below `2^16`. -/
theorem da_padding_complete : da_padding_complete_Spec := by
  intro rd hm r hr1 hr
  have hr' : r ≤ guest_const% DA_MAX_ROWS := hr
  obtain ⟨t7, t8, h7, e6, h8⟩ := rc_holds' hm (k := r) (K := guest_const% DA_MAX_ROWS) (by omega) (by norm_num)
  have hne : gen ^ r + word 1 0 ≠ 0 := by
    rw [word_one, Ne, e_add_eq_zero_iff, ← pow_zero gen]
    intro h
    have := gen_pow_inj' (by omega) (by omega) h
    omega
  refine (rel_iff_sem find_da_padding _ _).mpr ⟨Val.ofArgs [gen ^ r, word 1 0, gen ^ r + word 1 0,
    (gen ^ r + word 1 0)⁻¹, (gen ^ r + word 1 0) * (gen ^ r + word 1 0)⁻¹,
    word (2 ^ guest_const% DA_MAX_ROWS) 0, gen ^ (guest_const% DA_MAX_ROWS - r), t7, t8,
    word (2 ^ guest_const% DA_MAX_ROWS) 0, gen ^ (LeanDa.maxRows - r), gen ^ (LeanDa.maxRows - r)], rfl, ?_⟩
  rw [da_padding_body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨trivial, trivial, trivial, ⟨trivial, mul_inv_cancel₀ hne⟩, trivial,
    ⟨h7, by rw [word_gMax]; exact e6, h8⟩, trivial, ?_, trivial, trivial⟩
  rw [word_gMax, ← pow_add, maxRows_eq]
  congr 1
  omega

end
end LeanVM.Guest.B1.Da
