import LeanVM.Guest.B1.Stack.Certify
import LeanVM.Guest.B1.Stack.SelTables
import LeanVM.Guest.B1.Stack.ColSelAll
import LeanVM.Guest.B1.Stack.StkSel
import LeanVM.Guest.B1.Stack.Section

/-!
# The stack in the circuit, pinned

`certify_stack`'s soundness against the layout's stack (`LeanVM.Guest.B1.Stack.certify_stack_sound`),
`log2_ceil_in_the_exponent`'s meaning, the selectors' (`selector_tables`, `column_selector`,
`stack_selectors`), `check_stack_terminal`'s against the stacked claims' basis, the section's statement
(`stack_section_sound`) and the verifier's memory term and public claims as their pure forms, on
Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.Stack.certify_stack_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Stack.certify_stack_sound

/-- info: 'LeanVM.Guest.B1.log2_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.log2_holds

/-- info: 'LeanVM.Guest.B1.Stack.selector_tables_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Stack.selector_tables_holds

/-- info: 'LeanVM.Guest.B1.Stack.column_selector_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Stack.column_selector_holds

/-- info: 'LeanVM.Guest.B1.Stack.stack_selectors_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Stack.stack_selectors_holds

/-- info: 'LeanVM.Guest.B1.Stack.check_stack_terminal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Stack.check_stack_terminal_sound

/-- info: 'LeanVM.Guest.B1.Stack.stack_section_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Stack.stack_section_sound

/-- info: 'LeanVM.Guest.B1.Stack.memoryTermClaim_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Stack.memoryTermClaim_eq

/-- info: 'LeanVM.Guest.B1.Stack.bindPublicInput_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Stack.bindPublicInput_eq
