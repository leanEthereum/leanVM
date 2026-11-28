/-
  LeanVM.Protocol.Link

  The soundness of `verify_link`'s sum-checks, in the sample model, and its axioms.
-/

module

public import LeanVM.Protocol.Link.Sample
public import LeanVM.Protocol.Link.Sumcheck
public import LeanVM.Protocol.Link.Skeleton
public import LeanVM.Protocol.Link.Errors
public import LeanVM.Protocol.Link.Index
public import LeanVM.Protocol.Link.Sound

/-!
# The link's sum-checks

`verifyLink` (`Statement/Verifier/Link.lean`, `crates/verifier/src/link.rs`'s `verify_link`) read
as a public-coin protocol (`Sample.lean`'s `win`, every challenge uniform, the prover unbounded):

* `Sample.lean`: the sample model, averages over uniform challenges, and the counting lemmas
  (Schwartz-Zippel at the challenges' positions, an affine form's zeros);
* `Sumcheck.lean`: the statement's plain `sumcheck`, its challenges uniform (`win_sumcheck_le`) and
  sound at `rounds·(count − 1)/|E|` (`win_sumcheck_le_of_ne`);
* `Skeleton.lean`: `verifyLink` cut at its moves, by `rfl` (`verifyLink_eq_linkSkeleton`);
* `Errors.lean`: the Schwartz-Zippel counts of the link's error from `StateLink.lean` and
  `Lookup.lean` (the memory's with its `μ`, the program's at `μ = 1`), batched by `η`
  (`card_linkError_le`), and of the mirror certificate, one table's (`card_mirror_le`) and over
  the tables (`card_mirrorTables_le`);
* `Index.lean`: the index side's claim is the state link's right side (`indexClaim_eq_scalarRhs`);
* `Sound.lean`: `verifyLink_sound`, the paper's Theorem 5.4 against `verifyLink`, from the
  arithmetization's facts and those counts; `verifyLink_sound_computedSplit`, the deployed
  verifier's.

`notes/hotwire-port.md` (H4) says what the theorem takes as hypotheses and what is left to discharge
them.

`verifyLink_sound` covers `thm:link`'s first two cases (a pointer not one-hot, a link failing). Its
third, every link holding and a `JUMP` constraint failing, is
`LeanVM.Protocol.Relation.card_notDoom_of_not_constraints` (`Relation/Link/GroupJump.lean`): the
link's relation includes `JUMP`'s constraints (`ConstraintsHold`), and the link's interface
(`linkIfaceOfLinks`, hence `linkIface` and leanVM's knowledge soundness) bounds that case through it.
-/

/-- info: 'LeanVM.Protocol.Link.verifyLink_eq_linkSkeleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Link.verifyLink_eq_linkSkeleton

/-- info: 'LeanVM.Protocol.Link.win_sumcheck_le_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Link.win_sumcheck_le_of_ne

/-- info: 'LeanVM.Protocol.Link.verifyLink_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Link.verifyLink_sound

/-- info: 'LeanVM.Protocol.Link.verifyLink_sound_computedSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Link.verifyLink_sound_computedSplit

/-- info: 'LeanVM.Protocol.Link.card_linkError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Link.card_linkError_le

/-- info: 'LeanVM.Protocol.Link.card_mirror_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Link.card_mirror_le

/-- info: 'LeanVM.Protocol.Link.card_mirrorTables_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Link.card_mirrorTables_le

/-- info: 'LeanVM.Protocol.Link.indexClaim_eq_scalarRhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Link.indexClaim_eq_scalarRhs
