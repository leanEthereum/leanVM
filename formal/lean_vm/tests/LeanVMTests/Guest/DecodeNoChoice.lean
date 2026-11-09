import LeanVM.Guest.EndFinal

/-!
# Tests: the decoder chooses nothing and runs no verifier

`LeanVM.Guest.End.decode` reads its witness off the memory, through the sorted table of its
addresses, and off the frames the replayed run entered. The traversal below follows every definition
`decode` unfolds to (its value, not the proofs it carries) through this repository and the
schemes it imports (`LeanVM`, `LeanXmss`, `Sphincs`, `LeanDa`).

* **Classical constructs.** No definition `decode` unfolds to mentions `Classical.choose`,
  `Classical.epsilon`, `Exists.choose`, `Classical.indefiniteDescription`,
  `Classical.propDecidable`, `Classical.choice` or `Nat.find`. In particular it reaches neither
  `Semantics.addressIndex?` (the address index by `Classical.choose`, the specification's), nor
  `MemoryImage.read` or `LeanIsaProgram.fetch`, which use it: the memory and the bytecode are read
  through the sorted tables of their addresses (`Located.readTable`, `Extraction.Fast.gLogTable`),
  and B1's exponent of a power of `g` by a search (`B1.Main.indexSearch`).
* **Positive controls.** The traversal reaches the replay through the extractor's address tables
  (`Located.statesTable`, `Extraction.Fast.stepTable`, the machine's step `Semantics.executeWith`),
  the entries' table (`Located.entryTable`), the decided precondition `Located.preTest`, and
  B1-d's child proof `VerifySub.piOfW`, not the replay through the hash-map index
  (`Located.statesIn`, `Extraction.powIndex`), which the proofs use; and it flags a definition that does choose (`VerifySub.valOf`, the word
  at an address by `Exists.choose`, which `decode` does not use).
* **No verifier.** No definition `decode` unfolds to mentions a signature scheme's verifier, the
  deferring verifier, the DA opening or the batching. (It runs the machine, whose `KECCAK`
  instruction checks Keccak-f[1600], the guest's own in-circuit check.)
-/

open Lean Meta Elab Command

/-- The prefixes the traversals follow. -/
def followed : List Name := [`LeanVM, `LeanXmss, `Sphincs, `LeanDa]

/-- A name ends with one of the suffixes. -/
def endsWithAny (n : Name) (suffixes : List String) : Bool :=
  suffixes.any fun s ↦ n.toString.endsWith s

/-- The definitions reachable from `root` through values, following `followed`, and the pairs
(definition, constant) for every constant a visited definition's value mentions that `bad`
flags. -/
def traverse (root : Name) (bad : Name → Bool) : MetaM (NameSet × Array (Name × Name)) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut hits : Array (Name × Name) := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    -- follow definitions (and instances), not theorems: a proof is not part of the decoder
    let some v := ci.value? | continue
    if ci matches .thmInfo _ then continue
    if ← isProp ci.type then continue
    for c in v.getUsedConstants do
      if bad c then hits := hits.push (n, c)
      else if followed.any (·.isPrefixOf c) && !seen.contains c then todo := todo.push c
  return (seen, hits)

/-- The classical constructs that could pick a witness. -/
def classical : NameSet :=
  [``Classical.choose, ``Classical.epsilon, ``Exists.choose, ``Classical.indefiniteDescription,
    ``Classical.propDecidable, ``Classical.choice, ``Nat.find].foldl NameSet.insert {}

/-- The hits, sorted, as a string. -/
def showHits (hits : Array (Name × Name)) : String :=
  toString ((hits.map fun p ↦ s!"{p.1} uses {p.2}").qsort (· < ·)).toList

/-- info: [] -/
#guard_msgs in
run_meta do
  let (_, hits) ← traverse ``LeanVM.Guest.End.decode classical.contains
  logInfo (showHits hits)

/-- info: [] -/
#guard_msgs in
run_meta do
  let reads : List Name := [``LeanVM.Semantics.addressIndex?, ``LeanVM.Semantics.MemoryImage.read,
    ``LeanVM.Semantics.LeanIsaProgram.fetch, ``LeanVM.Guest.Located.frameOf]
  let (_, hits) ← traverse ``LeanVM.Guest.End.decode (reads.contains ·)
  logInfo (showHits hits)

/-! ## Positive controls -/

/-- info: statesTable: true, stepTable: true, executeWith: true, entryTable: true, preTest: true, piOfW: true, powIndex: false, statesIn: false -/
#guard_msgs in
run_meta do
  let (seen, _) ← traverse ``LeanVM.Guest.End.decode classical.contains
  logInfo s!"statesTable: {seen.contains ``LeanVM.Guest.Located.statesTable}, stepTable: {seen.contains ``LeanVM.Extraction.Fast.stepTable}, executeWith: {seen.contains ``LeanVM.Semantics.executeWith}, entryTable: {seen.contains ``LeanVM.Guest.Located.entryTable}, preTest: {seen.contains ``LeanVM.Guest.Located.preTest}, piOfW: {seen.contains ``LeanVM.Guest.B1.VerifySub.piOfW}, powIndex: {seen.contains ``LeanVM.Extraction.powIndex}, statesIn: {seen.contains ``LeanVM.Guest.Located.statesIn}"

/-- info: [LeanVM.Guest.B1.VerifySub.valOf uses Classical.propDecidable, LeanVM.Guest.B1.VerifySub.valOf uses Exists.choose] -/
#guard_msgs in
run_meta do
  let (_, hits) ← traverse ``LeanVM.Guest.B1.VerifySub.valOf classical.contains
  logInfo (showHits hits)

/-! ## No verifier -/

/-- info: [] -/
#guard_msgs in
run_meta do
  let forbidden := ["xmssVerify", "sphincsVerify", "LeanXmss.verify", "Sphincs.verify",
    "verifyDeferred", "verifyDeferredWith", "Verifier.verify", "verifyWith",
    "MatrixWitness.Opens", "Node.batch"]
  let (_, hits) ← traverse ``LeanVM.Guest.End.decode (endsWithAny · forbidden)
  logInfo (showHits hits)
