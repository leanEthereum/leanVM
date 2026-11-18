module

public import LeanVM.Cost.AS.Program

/-!
# The agreement-set extractor's program: its indices and its size, by evaluation

A firewall, as `Cost/DecoderSize.lean`: the kernel evaluations over the program, in a module of
their own.

* `asProgram_indices_increasing`: the bodies' indices are distinct;
* **`asProgram_size_le`**: the program's size is at most `25260` (the bodies' sizes, `25200` for
  `515` bodies, the entry's included, and `30` indices without a body, of size `2` each).
-/

namespace LeanVM.Cost.AS

open LeanVM.Cost

public section

theorem asProgram_indices_increasing :
    increasingFrom 0 (extractLC.costDeps.map (·.1)) = true := by
  decide +kernel

/-- **The program's size**, from its bodies, each count evaluated. -/
theorem asProgram_size_le : compiledASExtractor.size ≤ 25260 := by
  have h := size_ofList_add_length asProgramBodies (by
    rw [asProgramBodies, List.map_cons]
    exact nodup_of_increasing asProgram_indices_increasing)
  have h1 : (asProgramBodies.map fun p ↦ p.2.size).sum = 25200 := by decide +kernel
  have h2 : (asProgramBodies.map (·.1)).foldr max 0 = 544 := by decide +kernel
  have h3 : asProgramBodies.length = 515 := by decide +kernel
  unfold compiledASExtractor
  omega

end

end LeanVM.Cost.AS
