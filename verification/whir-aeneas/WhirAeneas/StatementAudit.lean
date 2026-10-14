import WhirAeneas.Statement
import Lean.Util.CollectAxioms

/-! Axiom audit of the statement extraction. It is separate from `Audit` because the
statement and verifier generated namespaces declare the same top-level instance names. -/

#print axioms StatementSource.stack.StackClaim.is_well_formed
#print axioms StatementSource.stack.Statement.check
#print axioms WhirAeneas.Claim.guard_eq_occupied
#print axioms WhirAeneas.Claim.guard_accept_iff
#print axioms WhirAeneas.Claim.guard_reject_iff
#print axioms WhirAeneas.Claim.guard_accept_implies_model_accept
#print axioms WhirAeneas.Claim.guard_full_cube_eq
#print axioms WhirAeneas.Statement.check_eq
#print axioms WhirAeneas.Statement.check_accept_iff
#print axioms WhirAeneas.Statement.check_accept_model
#print axioms WhirAeneas.Statement.check_accept_of_model

open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (declarationName, declarationInfo) in environment.constants.toList do
    if (`WhirAeneas).isPrefixOf declarationName ||
        (`StatementSource).isPrefixOf declarationName then
      match declarationInfo with
      | .thmInfo _ =>
        let axioms ← collectAxioms declarationName
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom in {declarationName}: {axiomName}"
        count := count + 1
      | .axiomInfo _ => throwError "project declares an axiom: {declarationName}"
      | _ => pure ()
  unless count > 0 do
    throwError "no statement theorems audited"
  logInfo m!"Audited {count} statement theorems; only propext, Classical.choice and Quot.sound permitted."
