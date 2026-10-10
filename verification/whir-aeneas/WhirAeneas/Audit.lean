import WhirAeneas.Generated.Verifier.Funs
import WhirAeneas.Toolchain.StringLiteral
import Lean.Util.CollectAxioms

#print axioms PcsSource.whir.verify.verify_with_basis
#print axioms PcsSource.whir.verify.verify_protocol_with_basis
#print axioms PcsSource.whir.commit.verify_record_binding
#print axioms PcsSource.whir.anchor.anchor_eq_at
#print axioms WhirAeneas.StdBulk.collect_owned
#print axioms WhirAeneas.StdBulk.extend_owned
#print axioms WhirAeneas.StdBulk.rotate_zero
#print axioms WhirAeneas.StdBulk.rotate_at_length
#print axioms WhirAeneas.StdBulk.rotate_content
#print axioms WhirAeneas.StdBulk.rotate_out_of_bounds
#print axioms WhirAeneas.StdBulk.truncate_content
#print axioms WhirAeneas.StdBulk.truncate_beyond_length
#print axioms Aeneas.Std.WrappingShiftRhs.amount_unsigned_lhs_mask
#print axioms Aeneas.Std.WrappingShiftRhs.amount_signed_lhs_mask
#print axioms Aeneas.Std.WrappingShiftRhs.signed_amount_unsigned_lhs
#print axioms WhirAeneas.StdGuards.option_some_eq
#print axioms WhirAeneas.StdGuards.option_none_eq
#print axioms WhirAeneas.StdGuards.option_some_none
#print axioms WhirAeneas.StdGuards.option_none_some
#print axioms WhirAeneas.StdGuards.first_empty
#print axioms WhirAeneas.StdGuards.first_nonempty
#print axioms Aeneas.Std.WrappingShiftRhs.signed_amount_signed_lhs

open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (declarationName, declarationInfo) in environment.constants.toList do
    if (`WhirAeneas).isPrefixOf declarationName ||
        (`Aeneas.Std.WrappingShiftRhs).isPrefixOf declarationName then
      match declarationInfo with
      | .thmInfo _ =>
        let axioms ← collectAxioms declarationName
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom in {declarationName}: {axiomName}"
        logInfo m!"{declarationName}: {axioms}"
        count := count + 1
      | .axiomInfo _ => throwError "project declares an axiom: {declarationName}"
      | _ => pure ()
  unless count > 0 do
    throwError "no extraction project theorems audited"
  logInfo m!"Audited {count} extraction helper theorems; only propext, Classical.choice and Quot.sound permitted."
