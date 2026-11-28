/-
  LeanVM.Protocol.Hotwire

  Hotwire's evaluation lemmas, its state link, mirror test and lookup link, over a commutative ring,
  and their axioms.
-/

module

public import LeanVM.Protocol.Hotwire.Eq
public import LeanVM.Protocol.Hotwire.ShiftEq
public import LeanVM.Protocol.Hotwire.Window
public import LeanVM.Protocol.Hotwire.StateLink
public import LeanVM.Protocol.Hotwire.Mirror
public import LeanVM.Protocol.Hotwire.Lookup

/-!
# Hotwire

The lemmas behind Hotwire's link phase (`crates/verifier/src/link.rs`, `verify_link`), generic
over the field; `LeanVM/Facts/Hotwire.lean` instantiates them at leanVM's `E` and ties them to the
statement's definitions.

* `Eq.lean`: the equality weights `eq1`, `eqAt` (the verifier's `eq_at`), `eqPt` (`eq_eval`), the
  multilinear extension `mle`, and `sum_eqAt_mul_eqAt`;
* `ShiftEq.lean`: `shiftEq_eq_shiftSum`, the verifier's `shift_eq` is the shifted equality weight
  summed out, and `shiftForm_fold`, the prover's `ShiftEq::fold`;
* `Window.lean`: `chunksEval_eq`, one-hot chunks read at the index point, `window_read` and
  `sum_window_read`, a pointer read `s` cells further inside its window;
* `StateLink.lean`: the state link's soundness `linkHolds_sound`, completeness
  `linkHolds_complete`, polynomial form `stateIdentity_iff` and Schwartz-Zippel bound
  `card_scalarIdentity_le` (its axioms pinned there);
* `Mirror.lean`: the mirror test, `mirrorCert_eq_zero_of_oneHot` (completeness),
  `mirrorPoly_eq_zero_iff` (a chunk passes as a polynomial exactly when it is one-hot) and the
  Schwartz-Zippel bounds `card_mirrorCert_eq_zero_le`, `card_batchedCert_eq_zero_le` (axioms pinned
  there);
* `Lookup.lean`: the lookup link's identity, its completeness `identity_eq_zero`, the reads'
  cancellation `identity_eq_plain`, soundness `card_identity_zero_le_independent`,
  `card_identity_zero_le_eqWeights` and the window's `sum_eqAt_mul_access` (axioms pinned there).
-/

/-! The evaluation lemmas use Lean's three standard axioms at most. -/

/-- info: 'LeanVM.Protocol.Hotwire.sum_eqAt_mul_eqAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.sum_eqAt_mul_eqAt

/-- info: 'LeanVM.Protocol.Hotwire.shiftEq_eq_shiftSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.shiftEq_eq_shiftSum

/-- info: 'LeanVM.Protocol.Hotwire.shiftForm_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.shiftForm_fold

/-- info: 'LeanVM.Protocol.Hotwire.chunksEval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.chunksEval_eq

/-- info: 'LeanVM.Protocol.Hotwire.window_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.window_read

/-- info: 'LeanVM.Protocol.Hotwire.sum_window_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.sum_window_read

/-- info: 'LeanVM.Protocol.Hotwire.eqAt_eq_foldl_zipIdx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.eqAt_eq_foldl_zipIdx

/-- info: 'LeanVM.Protocol.Hotwire.eqAt_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.eqAt_ofFn

/-- info: 'LeanVM.Protocol.Hotwire.shiftEq_of_charTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.shiftEq_of_charTwo
