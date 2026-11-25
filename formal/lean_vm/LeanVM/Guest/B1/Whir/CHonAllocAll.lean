/-
  LeanVM.Guest.B1.Whir.CHonAllocAll

  Every arm's body allocations at every rate.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc0
public import LeanVM.Guest.B1.Whir.CHonAlloc1
public import LeanVM.Guest.B1.Whir.CHonAllocRate

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every arm at every rate**: its statements at the first rate (`CHonAlloc0`, the same at every
rate, `bodyAllocs_rate`), its sizes at each (`CHonAlloc1`). -/
theorem bodyStatic_all (m ri : ℕ) (hm : m < 11) (hr : ri < 4) : BodyStatic (osCfgR m ri) := by
  refine bodyStatic_of ((bodyAllocs_rate m ri).mpr ?_) (bodySizes_all m hm ri hr)
  interval_cases m
  · exact bodyAllocs_0
  · exact bodyAllocs_1
  · exact bodyAllocs_2
  · exact bodyAllocs_3
  · exact bodyAllocs_4
  · exact bodyAllocs_5
  · exact bodyAllocs_6
  · exact bodyAllocs_7
  · exact bodyAllocs_8
  · exact bodyAllocs_9
  · exact bodyAllocs_10

end
end LeanVM.Guest.B1.Whir
