import Rv64Verifier.Proofs.Layout.Term
import Rv64Verifier.Proofs.Layout.Prod
import Rv64Verifier.Proofs.Layout.Pair
import Rv64Verifier.Proofs.Layout.Evaluate
import Rv64Verifier.Proofs.Layout.AddScaled
import Rv64Verifier.Proofs.Layout.SpecExtend
import Rv64Verifier.Proofs.Layout.Concat
import Rv64Verifier.Proofs.Layout.Clone
import Rv64Verifier.Proofs.Layout.StateStep
import Rv64Verifier.Proofs.Layout.StateDerived
import Rv64Verifier.Proofs.Layout.Memory
import Rv64Verifier.Proofs.Layout.Counted
import Rv64Verifier.Proofs.Layout.BusBridge
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

theorem state_derived_of (hG : GrowOneFreshSpec 0x80011c78 24 8) : StateDerivedSpec :=
  StateDerived.state_derived_spec Runtime.alloc_spec term_proved col_proved (Pair.pair_spec hG)

theorem state_step_of (hG : GrowOneFreshSpec 0x80011c78 24 8) : StateStepSpec :=
  StateStep.state_step_spec col_proved (state_derived_of hG)

theorem counted_of (hR : SpecExtend.ReserveFreshSpec) (hG : GrowOneFreshSpec 0x80011c78 24 8) :
    CountedSpec :=
  Counted.counted_spec (concat_of hR) col_proved (Pair.pair_spec hG)

theorem memory_of (hR : SpecExtend.ReserveFreshSpec) (hG : GrowOneFreshSpec 0x80011c78 24 8) :
    MemorySpec :=
  Memory.memory_spec term_proved col_proved (counted_of hR hG)

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

/-- info: 'Rv64Verifier.Layout.state_step_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms state_step_of

/-- info: 'Rv64Verifier.Layout.memory_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memory_of

end Rv64Verifier.Layout
