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
import Rv64Verifier.Proofs.Layout.MemoryCols
import Rv64Verifier.Proofs.Layout.Bytecode
import Rv64Verifier.Proofs.Layout.BusBridge
import Rv64Verifier.Proofs.Layout.BusEvaluate
import Rv64Verifier.Proofs.Layout.CellLanes
import Rv64Verifier.Proofs.Layout.Limb
import Rv64Verifier.Proofs.Layout.BusLayout
import Rv64Verifier.Proofs.Layout.ExtendTrusted
import Rv64Verifier.Proofs.Runtime.All
import Rv64Verifier.Proofs.Field.All

/-!
# The layout functions' contracts, closed

The runtime's `grow_one` and `reserve` say their new buffer is fresh (`NewBuf`); the layout proofs
take that as `GrowOneFreshSpec` and `SpecExtend.ReserveFreshSpec`.
-/

namespace Rv64Verifier.Layout
open Rv64Verifier.Proofs

/-- The runtime's `grow_one` gives the layout's: the new buffer is not empty. -/
theorem growOneFresh_of {entry : BitVec 64} {size align : Nat}
    (h : Runtime.GrowOneFreshSpec entry size align) (hs : 0 < size) :
    Layout.GrowOneFreshSpec entry size align :=
  h.weaken fun _ _ ⟨hp, hb⟩ ↦ ⟨hp, by
    have := hp.cap
    rcases hb.2 with h0 | h1
    · rcases Nat.mul_eq_zero.mp h0 with h0 | h0 <;> omega
    · exact h1.1⟩

theorem growOneFlushes : Layout.GrowOneFreshSpec 0x80011c78 24 8 :=
  growOneFresh_of Runtime.growOneFresh_80011c78 (by decide)

theorem growOnePairs : Layout.GrowOneFreshSpec 0x80010a94 48 8 :=
  growOneFresh_of Runtime.growOneFresh_80010a94 (by decide)

theorem reserveForms : SpecExtend.ReserveFreshSpec := Runtime.reserveFresh_80004aec

theorem term_proved : TermSpec := Term.term_spec Runtime.alloc_spec

theorem col_proved : ColSpec := Col.col_spec Field.ePow term_proved

theorem prod_proved : ProdSpec := Prod.prod_spec Field.ePow term_proved

theorem evaluate_proved : EvaluateSpec := Evaluate.evaluate_spec Field.mul

theorem add_scaled_proved : AddScaledSpec := AddScaled.add_scaled_spec' Field.mul growOnePairs

theorem pair_proved : PairSpec := Pair.pair_spec growOneFlushes

theorem spec_extend_proved : SpecExtendSpec :=
  SpecExtend.spec_extend_spec reserveForms Runtime.tryAllocZeroed Runtime.memcpy

theorem concat_proved : ConcatSpec := Concat.concat_spec Runtime.tryAllocZeroed spec_extend_proved

theorem clone_proved : CloneSpec := Clone.clone_spec Runtime.tryAllocZeroed Runtime.memcpy

theorem state_derived_proved : StateDerivedSpec :=
  StateDerived.state_derived_spec Runtime.alloc_spec term_proved col_proved pair_proved

theorem state_step_proved : StateStepSpec := StateStep.state_step_spec col_proved state_derived_proved

theorem counted_proved : CountedSpec := Counted.counted_spec concat_proved col_proved pair_proved

theorem memory_proved : MemorySpec := Memory.memory_spec term_proved col_proved counted_proved

theorem memory_cols_proved : MemoryColsSpec :=
  MemoryCols.memory_cols_spec term_proved col_proved Runtime.memcpy memory_proved

theorem bytecode_proved : BytecodeSpec :=
  Bytecode.bytecode_spec Runtime.alloc_spec Field.ePow term_proved Runtime.tryAllocZeroed
    spec_extend_proved col_proved counted_proved

/-- `Form::evaluate` as `table_sumcheck` calls it, either slice possibly empty. -/
theorem form_evaluate_e_proved : Proofs.Bus.TableSumcheck.FormEvaluateSpecE :=
  formEvaluateE_spec evaluate_proved

theorem cell_lanes_proved : CellLanesSpec := CellLanes.cell_lanes_spec Runtime.memcpy

theorem limb_proved : LimbSpec :=
  Limb.limb_spec term_proved col_proved prod_proved add_scaled_proved

theorem bus_layout_proved : Bus.BusLayoutSpec :=
  BusLayout.bus_layout_spec Runtime.tryAllocZeroed Runtime.reserveFast_8000d628 Runtime.memcpy
    (Proofs.Multilinear.StackOffsets.stack_offsets_spec Runtime.tryAllocZeroed)

theorem extend_trusted_proved : ExtendSpec :=
  Extend.extend_spec Runtime.reserveFresh_800060bc clone_proved

/-- info: 'Rv64Verifier.Layout.evaluate_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evaluate_proved

/-- info: 'Rv64Verifier.Layout.add_scaled_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms add_scaled_proved

/-- info: 'Rv64Verifier.Layout.concat_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concat_proved

/-- info: 'Rv64Verifier.Layout.clone_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clone_proved

/-- info: 'Rv64Verifier.Layout.col_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms col_proved

/-- info: 'Rv64Verifier.Layout.prod_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prod_proved

/-- info: 'Rv64Verifier.Layout.pair_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pair_proved

/-- info: 'Rv64Verifier.Layout.state_step_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms state_step_proved

/-- info: 'Rv64Verifier.Layout.memory_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memory_proved

/-- info: 'Rv64Verifier.Layout.state_derived_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms state_derived_proved

/-- info: 'Rv64Verifier.Layout.counted_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms counted_proved

/-- info: 'Rv64Verifier.Layout.memory_cols_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memory_cols_proved

/-- info: 'Rv64Verifier.Layout.bytecode_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bytecode_proved

/-- info: 'Rv64Verifier.Layout.form_evaluate_e_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms form_evaluate_e_proved

/-- info: 'Rv64Verifier.Layout.cell_lanes_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cell_lanes_proved

/-- info: 'Rv64Verifier.Layout.limb_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms limb_proved

/-- info: 'Rv64Verifier.Layout.bus_layout_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bus_layout_proved

/-- info: 'Rv64Verifier.Layout.extend_trusted_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms extend_trusted_proved

end Rv64Verifier.Layout
