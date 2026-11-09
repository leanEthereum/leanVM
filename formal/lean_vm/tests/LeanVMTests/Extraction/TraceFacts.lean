import LeanVM.Protocol.Extraction.Extractor
import LeanVM.Protocol.Extraction.Extract

/-!
# Tests: the extractor's trace facts are theorems only; the extractor's axioms

The section of `LeanVM/Protocol/Extraction/Extractor.lean` a reader may skip, the facts the root finder needs
(`traceCtx`'s proof fields, namespaces `LeanVM.Extraction.Words` and `LeanVM.Extraction.Bf64Trace`):
by proof irrelevance nothing in it can change what the extractor computes or what a statement says,
as long as every constant it declares is a proof. `#propsOnly` checks that: it fails if a constant
of those namespaces has a type that is not a proposition.

Then the axioms of the extractor's data (its decoder context carries proofs) and of the theorems
that relate it to the knowledge-soundness proof: Lean's three.
-/

open Lean Elab Command

/-- Fails unless every constant of the given namespaces (internal names aside) has a proposition
as its type. -/
elab "#propsOnly " nss:ident* : command => do
  let env ← getEnv
  for ns in nss do
    let mut bad : Array Name := #[]
    let mut n : Nat := 0
    for (name, ci) in env.constants.toList do
      if ns.getId.isPrefixOf name && !name.isInternal then
        n := n + 1
        unless ← liftTermElabM (Meta.isProp ci.type) do bad := bad.push name
    unless bad.isEmpty do throwError "{ns.getId}: not a proof: {bad}"
    if n == 0 then throwError "{ns.getId}: no constants"

#propsOnly LeanVM.Extraction.Words LeanVM.Extraction.Bf64Trace

/-- info: 'LeanVM.Extraction.extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.extract

/-- info: 'LeanVM.Extraction.gsContext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.gsContext

/-- info: 'LeanVM.Extraction.Bf64Trace.tracePowerSum_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.Bf64Trace.tracePowerSum_separates

/-- info: 'LeanVM.Extraction.PruneProofs.candidates_subset_decodeStacks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.PruneProofs.candidates_subset_decodeStacks

/-- info: 'LeanVM.Extraction.MerkleProofs.committedWordC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.MerkleProofs.committedWordC_eq

/-- info: 'LeanVM.Extraction.ExtractProofs.extract_of_candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.ExtractProofs.extract_of_candidate

/-- info: 'LeanVM.Extraction.ExtractProofs.extractorRpm_eq_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.ExtractProofs.extractorRpm_eq_extract
