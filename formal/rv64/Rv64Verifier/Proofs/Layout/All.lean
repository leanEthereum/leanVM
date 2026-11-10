import Rv64Verifier.Proofs.Layout.Term
import Rv64Verifier.Proofs.Layout.Prod
import Rv64Verifier.Proofs.Layout.Pair
import Rv64Verifier.Proofs.Layout.Evaluate
import Rv64Verifier.Proofs.Layout.AddScaled
import Rv64Verifier.Proofs.Layout.SpecExtend
import Rv64Verifier.Proofs.Layout.Concat
import Rv64Verifier.Proofs.Layout.Clone
import Rv64Verifier.Proofs.Runtime.All
import Rv64Verifier.Proofs.Field.All

/-!
# The layout functions' contracts, closed where their callees' are

`Form::term`, `col`, `prod` and `Form::evaluate` need only `alloc`, `E::pow` and `mul`, all proved.
`Flushes::pair` and `Form::add_scaled` need `grow_one` with a fresh buffer (`Grow.lean`), and
`Vec<Form>::spec_extend` `reserve` with one (`ReserveFreshSpec`), which the runtime's contracts do
not yet state; `clone` and `spec_extend` need `memcpy`.
-/

namespace Rv64Verifier.Layout
open Rv64Verifier.Proofs

theorem term_proved : TermSpec := Term.term_spec Runtime.alloc_spec

theorem col_proved : ColSpec := Col.col_spec Field.ePow term_proved

theorem prod_proved : ProdSpec := Prod.prod_spec Field.ePow term_proved

theorem evaluate_proved : EvaluateSpec := Evaluate.evaluate_spec Field.mul

theorem concat_of (hR : SpecExtend.ReserveFreshSpec) : ConcatSpec :=
  Concat.concat_spec Runtime.tryAllocZeroed
    (SpecExtend.spec_extend_spec hR Runtime.tryAllocZeroed Runtime.memcpy)

theorem clone_proved : CloneSpec := Clone.clone_spec Runtime.tryAllocZeroed Runtime.memcpy

/-- info: 'Rv64Verifier.Layout.evaluate_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evaluate_proved

/-- info: 'Rv64Verifier.Layout.AddScaled.add_scaled_spec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AddScaled.add_scaled_spec'

/-- info: 'Rv64Verifier.Layout.concat_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concat_of

/-- info: 'Rv64Verifier.Layout.clone_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clone_proved

/-- info: 'Rv64Verifier.Layout.col_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms col_proved

/-- info: 'Rv64Verifier.Layout.prod_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prod_proved

/-- info: 'Rv64Verifier.Layout.Pair.pair_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Pair.pair_spec

end Rv64Verifier.Layout
