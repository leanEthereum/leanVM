import LeanDa.End
import LeanDa.Code
import LeanDa.RpmScheme
import LeanDa.Commitment
import LeanDa.Subspace
import PqDas

/-!
# LeanDA's security

LeanDA as `crates/lean_da` computes it, in the random-permutation model (`H` Keccak-256 over a
random permutation `π`, the membership challenge the deployed duplex over `π`), with no argument
system (`LeanDa/End.lean`): it is complete for every function `π` (`leanDa_complete`);
position binding holds with the bound `(Q + 1)² · 2^-256` for every number `Q` of permutation
calls (`leanDa_positionBinding_rpm`, from `Q² / 2^256 + Q² / 2^508`); and its membership test is
sound (`leanDa_membershipSound_rpm`): an adversary of `Q` permutation calls outputs a root and a
matrix that satisfy the relation, the matrix not one of codewords, with probability at most
`(Q + 2^10) · 2^-125 + (Q + 2^19)² · 2^-247`. The grind discounts the membership test's soundness
`(2^13 - 1) / 2^128`: a draw the adversary's call makes is selected and accepting with probability
at most `2^-10` of that, and the check's own nonce search for the root is one fresh try
(`LeanDa.StraightBad`).

The proofs build on Benedikt Wagner's framework for erasure code commitments (`PqDas`, ported from
https://github.com/b-wagn/fv-pq-da; his post:
https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746). Position binding is his
vector commitment's notion, proved by reduction to a collision of `H`. The membership test's soundness is his
committed soundness, proved by a straight-line argument built on his framework and games
(`LeanDa.Straight`, `LeanDa.StraightBound`): the adversary is read as a code-binding adversary that
opens no cell, for the argument that accepts everything and the extractor that returns its proof,
and a win is a bad event of `H` and the draws, lazily sampled per root and nonce. His code-binding
theorem, his reductions and his forking route are not in this repository; his repository has
them.
-/

/-! ## The end theorems

Each proves a proposition of `Statement/LeanDa.lean`, all three in `LeanDa/End.lean`:
`leanDa_complete : LeanDaComplete`, `leanDa_positionBinding_rpm : LeanDaPositionBinding` and
`leanDa_membershipSound_rpm : LeanDaMembershipSound`; the axioms are pinned at the end of this
file. -/

example : LeanDa.LeanDaComplete := LeanDa.leanDa_complete

example : LeanDa.LeanDaPositionBinding := LeanDa.leanDa_positionBinding_rpm

example : LeanDa.LeanDaMembershipSound := LeanDa.leanDa_membershipSound_rpm

/-! The build fails if a front-page theorem's axiom footprint ever grows beyond Lean's three
standard axioms. -/

/-- info: 'LeanDa.leanDa_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_complete

/-- info: 'LeanDa.leanDa_positionBinding_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_positionBinding_rpm

/-- info: 'LeanDa.leanDa_membershipSound_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_membershipSound_rpm

/-- info: 'LeanDa.commitCodewords_eq_commitCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.commitCodewords_eq_commitCells

/-- info: 'LeanDa.dualCodeword_eq_dualCodewordAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.dualCodeword_eq_dualCodewordAt

