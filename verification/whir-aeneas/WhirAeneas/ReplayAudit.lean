import WhirAeneas.Replay
import WhirAeneas.Compose
import WhirAeneas.Sampling
import Lean.Util.CollectAxioms

/-! Axiom audit of the replay extraction and its proofs. It is separate from the other
audits because the generated namespaces declare the same top-level instance names. -/

#print axioms ReplaySource.whir.verify.verify
#print axioms ReplaySource.whir.query.sample_queries
#print axioms ReplaySource.ring_switch.RingMap.close
#print axioms WhirAeneas.Fold.quad_eval
#print axioms WhirAeneas.Fold.quad_fold
#print axioms WhirAeneas.Fold.close_eq
#print axioms WhirAeneas.Fold.term_eq
#print axioms WhirAeneas.Replay.fold_rounds_eq
#print axioms WhirAeneas.Replay.replay_all_eq
#print axioms WhirAeneas.Replay.begin_query_eq
#print axioms WhirAeneas.Replay.open_e_rows_eq
#print axioms WhirAeneas.Replay.affine_factors_eq
#print axioms WhirAeneas.Replay.basis_at_eq
#print axioms WhirAeneas.Replay.terminal_eq
#print axioms WhirAeneas.Replay.tail_loop_eq
#print axioms WhirAeneas.Replay.terminal_link
#print axioms WhirAeneas.Replay.last_level_eq
#print axioms WhirAeneas.Replay.verifyLevel_ok
#print axioms WhirAeneas.Replay.check_config_shape_ok
#print axioms WhirAeneas.Replay.level_facts
#print axioms WhirAeneas.Fold.basis_product_eq
#print axioms WhirAeneas.Query.base_enforced_eq
#print axioms WhirAeneas.Query.ext_enforced_eq
#print axioms WhirAeneas.Query.finish_query_eq
#print axioms WhirAeneas.Replay.mid_level_eq
#print axioms WhirAeneas.Replay.last_iter_eq
#print axioms WhirAeneas.Replay.verify_loop3_eq
#print axioms WhirAeneas.Replay.verify_loop4_eq
#print axioms WhirAeneas.Replay.lane_fold_eq
#print axioms WhirAeneas.Replay.replay_eq
#print axioms WhirAeneas.Replay.verify_eq
#print axioms WhirAeneas.Replay.read_eq
#print axioms ReplaySource.fiat_shamir.arith.Verifier.read_round.default
#print axioms ReplaySource.whir.sumcheck.RoundQuad.read
#print axioms WhirAeneas.Sampling.sample_queries_eq

open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (declarationName, declarationInfo) in environment.constants.toList do
    if (`WhirAeneas.Fold).isPrefixOf declarationName ||
        (`WhirAeneas.Query).isPrefixOf declarationName ||
        (`WhirAeneas.Replay).isPrefixOf declarationName ||
        (`WhirAeneas.Sampling).isPrefixOf declarationName ||
        (`ReplaySource).isPrefixOf declarationName then
      match declarationInfo with
      | .thmInfo _ =>
        let axioms ← collectAxioms declarationName
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom in {declarationName}: {axiomName}"
        count := count + 1
      | .axiomInfo _ => throwError "project declares an axiom: {declarationName}"
      | .defnInfo _ =>
        let axioms ← collectAxioms declarationName
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom in {declarationName}: {axiomName}"
      | _ => pure ()
  unless count > 0 do
    throwError "no replay theorems audited"
  logInfo m!"Audited {count} replay theorems; only propext, Classical.choice and Quot.sound permitted."
