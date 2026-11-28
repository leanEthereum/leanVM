module

public import LeanVM.Cost.AS.Program

/-!
# The agreement-set extractor's program: its indices and its size, by evaluation

A firewall: the kernel evaluations over the program, in a module of their own.

* `asProgram_indices_increasing`: the bodies' indices are distinct;
* **`asProgram_size_le`**: the program's size is at most `23855` (the bodies' sizes, `23825` for
  `477` bodies, the entry's included, at indices up to `491`, and `15` indices without a body, of
  size `2` each).
-/

namespace LeanVM.Cost.AS

open LeanVM.Cost

public section

theorem asProgram_indices_increasing :
    increasingFrom 0 (extractLC.costDeps.map (·.1)) = true := by
  decide +kernel

/-- **The program's size**, from its bodies, each count evaluated. -/
theorem asProgram_size_le : compiledASExtractor.size ≤ 23855 := by
  have h := size_ofList_add_length asProgramBodies (by
    rw [asProgramBodies, List.map_cons]
    exact nodup_of_increasing asProgram_indices_increasing)
  have h1 : (asProgramBodies.map fun p ↦ p.2.size).sum = 23825 := by decide +kernel
  have h2 : (asProgramBodies.map (·.1)).foldr max 0 = 491 := by decide +kernel
  have h3 : asProgramBodies.length = 477 := by decide +kernel
  unfold compiledASExtractor
  omega

end

end LeanVM.Cost.AS
