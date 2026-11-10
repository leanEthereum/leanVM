module

public import Qrom.QromSearch
public import Qrom.OvSearch
public import Qrom.HidingMain
public import Qrom.Deferral
public import Qrom.Presample
public import Qrom.Verify
public import Qrom.Assembly
public import Qrom.Cells
public import Qrom.Sphincs.Numeric
public import Qrom.Sphincs.EndStatement

/-! # leanSPHINCS in the quantum random-oracle model

The proof of the end statement `Sphincs.QuantumRandomOracleModel.LeanSphincsQromStronglyUnforgeable`
(`Qrom.Sphincs.leanSphincsQrom`): Keccak-256 is a random function on the byte strings of at most
`maxLen` bytes, which the adversary queries in superposition through the XOR oracle, on VCVio's
quantum layer (compressed oracle, instability,
square-root hybrid). `Qrom.Sphincs.winProb_le_h26`: for the parameters of `FORS.h26_layered`, an
adversary given the public key and making at most `n` calls in all (hash queries, quantum or
classical, and signing requests) forges with probability at most `((n + 2048) / 2^61.8)²`.

## Generic results

* `Qrom.qrom_search_le`: a program making at most `t` calls and outputting at most `k` inputs outputs
  one whose value is good with probability at most `λ (√6 t + 2 k)²`, where every input has a
  fraction at most `λ` of good values (`EventBound`, `Bridge`, `Cell`, `PiKron`, `Search`, `Leaf`).
* `Qrom.OvGame.ov_search_le`: the same for games whose hash answers some inputs from fixed data,
  depending on a classical side state, beside classical side ports such as a signing oracle, with
  `t` the number of calls in all (`Override`, `OvBridge`, `OvEvent`, `OvSearch`).
* `Qrom.OvGame.search_cells_le`: the same for a predicate on the whole value of a cell of inputs, by
  simulating the oracle on cells, a call to a component being one call to the cell with the other
  components on uniform superpositions (`Cells`).
* `Qrom.OvGame.hiding_le`: answering by `G` the inputs that carry data not yet revealed costs
  `√Pr₁ ≤ √Pr₂ + n √(4 ε tr ρ)`, when at most a fraction `ε` of the unrevealed values protect any
  input (`Blocks`, `OvBlocks`, `Hiding`, `HidingAvg`, `HidingMain`).

## The leanSPHINCS proof

The adversary is a program whose calls go to the hash or to the classical ports (the public key,
signing); the signer and key generation hash classically through the same random function.

1. Presampling (`Sphincs/Presampled`): the honest computation reads the hash at distinct points, so
   the game is the average over data `d` of one whose hash is a fresh `G` overridden by `d`.
2. Hiding (`Sphincs/Hidden`, `Sphincs/HidingStep`): the inputs reading unrevealed data are answered
   by `G`, at a cost of `n √(4 · 2^-128 tr ρ)` on the square root.
3. Classification (`Sphincs/Classify`, `Sphincs/Bound/Split`): a winning forgery is a protected read,
   a hit of `G` on an honest value or an encoding collision read at a counter the signer did not
   take, or a digest from `G` covered by the logged digests.
4. Bounds (`Sphincs/Bound`): protected reads cost `verifyQueries · 2^-128` (`Terms`). Hits and
   encoding collisions cost `2^-128 (√(2 + 4 · 2^-128) (n + 1 + verifyQueries) + 2 verifyQueries)²`
   (`Swap`): exchanging the data above the found counters with `G` is an involution of the pairs
   `(d, G)` that makes a collision a hit. Covered digests go through the deferral of the signed
   digests to presampled ones (`Defer`) and a search with the digest calls of one message and
   randomizer as one cell (`DigCells`, `CoverCells`), costing `λ_δ (√(2 + 4 λ_δ) (n + 1) + 2)²` for
   presampled digests covering a fraction `λ_δ`; averaged with the first and second moments of
   `λ_δ` (`LamCov`, `LamCov2`) that is at most `1123 · 2^-137 (√2 (n + 1) + 2)²` for h26.

The search constant `2 + 4 λ` (against VCVio's `6` from the commutators) comes from the
one-directional hybrid (`Fwd`): only the weight a call moves into the search event is charged, and
on the databases the compressed oracle reaches, whose written cells are orthogonal to the uniform
superposition, one call moves at most `λ (2 + 4 λ)` of it (`FwdCell`, `FwdOracle`, `FwdGame`,
`FwdEvent`).

The bound reaches 1/2 at about `2^61.3` calls; Grover's search for a covered digest reaches it at
about `2^63`, at 2 hash calls an iteration. The remaining gap is the search constant `2` against
Grover's `1` and the hiding term, which a hybrid charges at twice the amplitude of a query.

The build fails if the axiom footprints below grow beyond Lean's three. -/

/-- info: 'Qrom.qrom_search_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.qrom_search_le

/-- info: 'Qrom.OvGame.tsum_eventWeight_compressed_le_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.tsum_eventWeight_compressed_le_fwd

/-- info: 'Qrom.OvGame.ov_search_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.ov_search_le

/-- info: 'Qrom.OvGame.hiding_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.hiding_le

/-- info: 'Qrom.OvGame.hiding_side_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.hiding_side_le

/-- info: 'Qrom.OvGame.sum_sideW_protHit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.sum_sideW_protHit_le

/-- info: 'Qrom.OvGame.deferral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.deferral_le

/-- info: 'Qrom.sum_eq_sum_override' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.sum_eq_sum_override

/-- info: 'Qrom.OvGame.sideW_withVerifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.sideW_withVerifier

/-- info: 'Qrom.OvGame.search_withVerifier_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.search_withVerifier_le

/-- info: 'Qrom.OvGame.search_cells_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.OvGame.search_cells_le

/-- info: 'Qrom.Sphincs.winProb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.Sphincs.winProb_le

/-- info: 'Qrom.Sphincs.winProb_le_h26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.Sphincs.winProb_le_h26

example : Sphincs.QuantumRandomOracleModel.LeanSphincsQromStronglyUnforgeable :=
  Qrom.Sphincs.leanSphincsQrom

/-- info: 'Qrom.Sphincs.leanSphincsQrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.Sphincs.leanSphincsQrom
