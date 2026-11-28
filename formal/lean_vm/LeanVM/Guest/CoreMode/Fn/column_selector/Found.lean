/-
  LeanVM.Guest.CoreMode.Fn.column_selector.Found

  `column_selector__L{n}_L{κ}`, `κ < 4n`, and `stack_selectors__L{n}`, `4 ≤ n ≤ 8`, found, of their templates.
-/

module

public import LeanVM.Guest.B1.Stack.StkSel
public import Mathlib.Tactic.IntervalCases

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1.Whir

@[expose] public section

/-- `stack_selectors`' specialization at `n` nibbles. -/
def stsName (n : ℕ) : String := "stack_selectors__L" ++ natStr n

set_option maxRecDepth 100000 in
/-- **`column_selector__L{n}_L{κ}`, found**, `κ < 4n`: its parameters and its template. -/
theorem cs_found : ∀ n κ, 4 ≤ n → n ≤ 8 → κ < 4 * n → κ < 31 → ∃ fn, coreProgram.find? (cselName n κ) = some fn ∧
    fn.params = [.n 0, .n 1, .n 2] ∧ fn.body = cselBody n κ := by
  intro n κ h4 h8 hκn hκ
  interval_cases n <;> interval_cases κ
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L0») rfl, rfl, csel_body_L4_L0⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L1») rfl, rfl, csel_body_L4_L1⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L2») rfl, rfl, csel_body_L4_L2⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L3») rfl, rfl, csel_body_L4_L3⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L4») rfl, rfl, csel_body_L4_L4⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L5») rfl, rfl, csel_body_L4_L5⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L6») rfl, rfl, csel_body_L4_L6⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L7») rfl, rfl, csel_body_L4_L7⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L8») rfl, rfl, csel_body_L4_L8⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L9») rfl, rfl, csel_body_L4_L9⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L10») rfl, rfl, csel_body_L4_L10⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L11») rfl, rfl, csel_body_L4_L11⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L12») rfl, rfl, csel_body_L4_L12⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L13») rfl, rfl, csel_body_L4_L13⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L14») rfl, rfl, csel_body_L4_L14⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L4_L15») rfl, rfl, csel_body_L4_L15⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L0») rfl, rfl, csel_body_L5_L0⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L1») rfl, rfl, csel_body_L5_L1⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L2») rfl, rfl, csel_body_L5_L2⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L3») rfl, rfl, csel_body_L5_L3⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L4») rfl, rfl, csel_body_L5_L4⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L5») rfl, rfl, csel_body_L5_L5⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L6») rfl, rfl, csel_body_L5_L6⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L7») rfl, rfl, csel_body_L5_L7⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L8») rfl, rfl, csel_body_L5_L8⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L9») rfl, rfl, csel_body_L5_L9⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L10») rfl, rfl, csel_body_L5_L10⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L11») rfl, rfl, csel_body_L5_L11⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L12») rfl, rfl, csel_body_L5_L12⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L13») rfl, rfl, csel_body_L5_L13⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L14») rfl, rfl, csel_body_L5_L14⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L15») rfl, rfl, csel_body_L5_L15⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L16») rfl, rfl, csel_body_L5_L16⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L17») rfl, rfl, csel_body_L5_L17⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L18») rfl, rfl, csel_body_L5_L18⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L5_L19») rfl, rfl, csel_body_L5_L19⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L0») rfl, rfl, csel_body_L6_L0⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L1») rfl, rfl, csel_body_L6_L1⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L2») rfl, rfl, csel_body_L6_L2⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L3») rfl, rfl, csel_body_L6_L3⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L4») rfl, rfl, csel_body_L6_L4⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L5») rfl, rfl, csel_body_L6_L5⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L6») rfl, rfl, csel_body_L6_L6⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L7») rfl, rfl, csel_body_L6_L7⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L8») rfl, rfl, csel_body_L6_L8⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L9») rfl, rfl, csel_body_L6_L9⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L10») rfl, rfl, csel_body_L6_L10⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L11») rfl, rfl, csel_body_L6_L11⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L12») rfl, rfl, csel_body_L6_L12⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L13») rfl, rfl, csel_body_L6_L13⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L14») rfl, rfl, csel_body_L6_L14⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L15») rfl, rfl, csel_body_L6_L15⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L16») rfl, rfl, csel_body_L6_L16⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L17») rfl, rfl, csel_body_L6_L17⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L18») rfl, rfl, csel_body_L6_L18⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L19») rfl, rfl, csel_body_L6_L19⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L20») rfl, rfl, csel_body_L6_L20⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L21») rfl, rfl, csel_body_L6_L21⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L22») rfl, rfl, csel_body_L6_L22⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L6_L23») rfl, rfl, csel_body_L6_L23⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L0») rfl, rfl, csel_body_L7_L0⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L1») rfl, rfl, csel_body_L7_L1⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L2») rfl, rfl, csel_body_L7_L2⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L3») rfl, rfl, csel_body_L7_L3⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L4») rfl, rfl, csel_body_L7_L4⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L5») rfl, rfl, csel_body_L7_L5⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L6») rfl, rfl, csel_body_L7_L6⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L7») rfl, rfl, csel_body_L7_L7⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L8») rfl, rfl, csel_body_L7_L8⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L9») rfl, rfl, csel_body_L7_L9⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L10») rfl, rfl, csel_body_L7_L10⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L11») rfl, rfl, csel_body_L7_L11⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L12») rfl, rfl, csel_body_L7_L12⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L13») rfl, rfl, csel_body_L7_L13⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L14») rfl, rfl, csel_body_L7_L14⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L15») rfl, rfl, csel_body_L7_L15⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L16») rfl, rfl, csel_body_L7_L16⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L17») rfl, rfl, csel_body_L7_L17⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L18») rfl, rfl, csel_body_L7_L18⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L19») rfl, rfl, csel_body_L7_L19⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L20») rfl, rfl, csel_body_L7_L20⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L21») rfl, rfl, csel_body_L7_L21⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L22») rfl, rfl, csel_body_L7_L22⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L23») rfl, rfl, csel_body_L7_L23⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L24») rfl, rfl, csel_body_L7_L24⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L25») rfl, rfl, csel_body_L7_L25⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L26») rfl, rfl, csel_body_L7_L26⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L7_L27») rfl, rfl, csel_body_L7_L27⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L0») rfl, rfl, csel_body_L8_L0⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L1») rfl, rfl, csel_body_L8_L1⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L2») rfl, rfl, csel_body_L8_L2⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L3») rfl, rfl, csel_body_L8_L3⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L4») rfl, rfl, csel_body_L8_L4⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L5») rfl, rfl, csel_body_L8_L5⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L6») rfl, rfl, csel_body_L8_L6⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L7») rfl, rfl, csel_body_L8_L7⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L8») rfl, rfl, csel_body_L8_L8⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L9») rfl, rfl, csel_body_L8_L9⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L10») rfl, rfl, csel_body_L8_L10⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L11») rfl, rfl, csel_body_L8_L11⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L12») rfl, rfl, csel_body_L8_L12⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L13») rfl, rfl, csel_body_L8_L13⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L14») rfl, rfl, csel_body_L8_L14⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L15») rfl, rfl, csel_body_L8_L15⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L16») rfl, rfl, csel_body_L8_L16⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L17») rfl, rfl, csel_body_L8_L17⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L18») rfl, rfl, csel_body_L8_L18⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L19») rfl, rfl, csel_body_L8_L19⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L20») rfl, rfl, csel_body_L8_L20⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L21») rfl, rfl, csel_body_L8_L21⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L22») rfl, rfl, csel_body_L8_L22⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L23») rfl, rfl, csel_body_L8_L23⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L24») rfl, rfl, csel_body_L8_L24⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L25») rfl, rfl, csel_body_L8_L25⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L26») rfl, rfl, csel_body_L8_L26⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L27») rfl, rfl, csel_body_L8_L27⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L28») rfl, rfl, csel_body_L8_L28⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L29») rfl, rfl, csel_body_L8_L29⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «column_selector__L8_L30») rfl, rfl, csel_body_L8_L30⟩

/-- **`stack_selectors__L{n}`, found**: its parameters and its template. -/
theorem sts_found : ∀ n, 4 ≤ n → n ≤ 8 → ∃ fn, coreProgram.find? (stsName n) = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧ fn.body = stsBody n := by
  intro n h4 h8
  interval_cases n
  · exact ⟨_, coreProgram_find?_at (j := idx% «stack_selectors__L4») rfl, rfl, stack_selectors_L4_body⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «stack_selectors__L5») rfl, rfl, stack_selectors_L5_body⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «stack_selectors__L6») rfl, rfl, stack_selectors_L6_body⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «stack_selectors__L7») rfl, rfl, stack_selectors_L7_body⟩
  · exact ⟨_, coreProgram_find?_at (j := idx% «stack_selectors__L8») rfl, rfl, stack_selectors_L8_body⟩

end
end LeanVM.Guest.B1.Stack
