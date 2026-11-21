import Soundness.RBR
import Soundness.State
import Soundness.ProtocolD
import Soundness.Sound
import Soundness.Extract
import Soundness.Hypothesis
import Soundness.Axioms

/-! # Soundness

The composition of the per-message transitions into one statement: Protocol 4.2 of the paper,
with one batch of points per level, as a public-coin transition system over a ladder of levels,
its round-by-round state function (the invariant of `Rounds` together with the potential of
`Protocol`), and the theorem that it is round-by-round sound with the errors of Theorem 5.2. The
files are described in `Soundness/README.md`.
-/
