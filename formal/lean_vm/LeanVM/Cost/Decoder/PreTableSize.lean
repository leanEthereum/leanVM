module

public import LeanVM.Cost.Decoder.PreTable

/-!
# The precondition's test: its size in the decoder's program, by evaluation

As `Cost/ExtractorSize.lean` measures the extractor's program (`MachineValue.size`,
`Term.size`, `Statement/CostMachine.lean`), a module of its own that imports only the compiled
functions:

* **`preTable_size`**: the literal table of the functions' preconditions
  (`Guest.Fast.preTable`, `1536` entries) is a value of size `6666`;
* `preTableC_body_size`: the body that builds it (`preTableC`, its constructors, each natural
  literal a term `Term.literal`) has size `9360`, what it adds to the decoder's program (and `2` for
  its index);
* `preTestBodies_size`: the bodies the compiled test adds past the decoder's witness (`preTestAtC`'s
  dependencies from `powBelowAtC` on, `18` of them, the lanes' scan `twoPowScanC` and the table's
  reads `gpowAtC`, `symValAtC` among them) have size `303`;
* `genPowsBodies_size`: the powers table's bodies (`genPowsC`, `squaresFromC`, `powsFromC`, the
  append, and the product in `K`, `kMulC`), built once and passed to the test, have size `161`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Guest.Fast

public section

/-- **The table's size**: `6666`. -/
theorem preTable_size : (encodeValue preTable).size = 6666 := by
  -- an array's encoding maps `Array.map`, whose body the kernel does not see here: by its list
  show (MachineValue.array (preTable.map encodeValue)).size = 6666
  rw [MachineValue.size, Array.toList_map]
  decide +kernel

/-- The size of the body that builds the table: `9360`. -/
theorem preTableC_body_size : preTableC.costBody.size = 9360 := by decide +kernel

/-- The sizes of the test's bodies: `303`, `18` bodies. -/
theorem preTestBodies_size :
    ((preTestAtC.costDeps.filter fun p ↦ decide (powBelowAtC.costIdx ≤ p.1)).map
      fun p ↦ p.2.size).sum = 303 ∧
    (preTestAtC.costDeps.filter fun p ↦ decide (powBelowAtC.costIdx ≤ p.1)).length = 18 := by
  decide +kernel

/-- The sizes of the powers table's bodies: `161`, `5` bodies. -/
theorem genPowsBodies_size :
    (genPowsC.costDeps.map fun p ↦ p.2.size).sum = 161 ∧ genPowsC.costDeps.length = 5 := by
  decide +kernel

end

end LeanVM.Cost.Decoder
