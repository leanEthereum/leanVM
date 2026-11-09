/-
  LeanVM.Guest.WalkOqOk3

  The certificates of a quarter of `opening_queries`' specializations and loops (those whose
  templates `B1/Opening/QueriesBody3.lean` checks) hand on the walk's obligations in the forms
  `WalkKnownDefs` checks, by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

theorem walkOk_458 : mainOkS 458 0 ⟨0, 16, 11, 6⟩ = true := by decide +kernel

theorem walkOk_461 : mainOkS 461 0 ⟨0, 16, 11, 5⟩ = true := by decide +kernel

theorem walkOk_490 : mainOkS 490 0 ⟨1, 64, 12, 8⟩ = true := by decide +kernel

theorem walkOk_523 : mainOkS 523 1 ⟨1, 64, 14, 8⟩ = true := by decide +kernel

theorem walkOk_525 : mainOkS 525 0 ⟨0, 16, 15, 6⟩ = true := by decide +kernel

theorem walkOk_527 : mainOkS 527 0 ⟨0, 16, 15, 5⟩ = true := by decide +kernel

theorem walkOk_564 : mainOkS 564 0 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

theorem walkOk_613 : mainOkS 613 0 ⟨0, 16, 15, 4⟩ = true := by decide +kernel

theorem walkOk_636 : mainOkS 636 1 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

theorem walkOk_698 : mainOkS 698 1 ⟨1, 64, 18, 7⟩ = true := by decide +kernel

theorem walkOk_702 : mainOkS 702 0 ⟨0, 16, 18, 5⟩ = true := by decide +kernel

theorem walkOk_732 : mainOkS 732 0 ⟨1, 64, 16, 6⟩ = true := by decide +kernel

theorem walkOk_754 : mainOkS 754 0 ⟨1, 64, 18, 6⟩ = true := by decide +kernel

theorem walkOk_779 : mainOkS 779 0 ⟨0, 16, 20, 5⟩ = true := by decide +kernel

theorem walkOk_857 : loop0Ok 857 ⟨0, 16, 11, 6⟩ = true := by decide +kernel

theorem walkOk_859 : loop0Ok 859 ⟨0, 16, 11, 5⟩ = true := by decide +kernel

theorem walkOk_867 : loop1Ok 867 0 ⟨1, 64, 12, 8⟩ = true := by decide +kernel

theorem walkOk_880 : loop1Ok 880 1 ⟨1, 64, 14, 8⟩ = true := by decide +kernel

theorem walkOk_882 : loop0Ok 882 ⟨0, 16, 15, 6⟩ = true := by decide +kernel

theorem walkOk_884 : loop0Ok 884 ⟨0, 16, 15, 5⟩ = true := by decide +kernel

theorem walkOk_897 : loop1Ok 897 0 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

theorem walkOk_911 : loop0Ok 911 ⟨0, 16, 15, 4⟩ = true := by decide +kernel

theorem walkOk_921 : loop1Ok 921 1 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

theorem walkOk_934 : loop1Ok 934 1 ⟨1, 64, 18, 7⟩ = true := by decide +kernel

theorem walkOk_938 : loop0Ok 938 ⟨0, 16, 18, 5⟩ = true := by decide +kernel

theorem walkOk_943 : loop1Ok 943 0 ⟨1, 64, 16, 6⟩ = true := by decide +kernel

theorem walkOk_945 : loop1Ok 945 0 ⟨1, 64, 18, 6⟩ = true := by decide +kernel

theorem walkOk_953 : loop0Ok 953 ⟨0, 16, 20, 5⟩ = true := by decide +kernel

end
end LeanVM.Guest.End
