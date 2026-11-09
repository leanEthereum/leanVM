/-
  LeanVM.Guest.WalkOqOk1

  The certificates of a quarter of `opening_queries`' specializations and loops (those whose
  templates `B1/Opening/QueriesBody1.lean` checks) hand on the walk's obligations in the forms
  `WalkKnownDefs` checks, by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

theorem walkOk_444 : mainOkS 444 0 ⟨0, 16, 10, 5⟩ = true := by decide +kernel

theorem walkOk_493 : mainOkS 493 0 ⟨0, 16, 13, 6⟩ = true := by decide +kernel

theorem walkOk_496 : mainOkS 496 0 ⟨0, 16, 13, 5⟩ = true := by decide +kernel

theorem walkOk_537 : mainOkS 537 1 ⟨1, 64, 15, 8⟩ = true := by decide +kernel

theorem walkOk_555 : mainOkS 555 0 ⟨1, 64, 11, 7⟩ = true := by decide +kernel

theorem walkOk_585 : mainOkS 585 0 ⟨1, 64, 14, 7⟩ = true := by decide +kernel

theorem walkOk_590 : mainOkS 590 0 ⟨0, 16, 13, 4⟩ = true := by decide +kernel

theorem walkOk_624 : mainOkS 624 0 ⟨0, 16, 17, 5⟩ = true := by decide +kernel

theorem walkOk_654 : mainOkS 654 1 ⟨1, 64, 14, 7⟩ = true := by decide +kernel

theorem walkOk_705 : mainOkS 705 0 ⟨0, 16, 17, 4⟩ = true := by decide +kernel

theorem walkOk_714 : mainOkS 714 0 ⟨1, 64, 14, 6⟩ = true := by decide +kernel

theorem walkOk_743 : mainOkS 743 0 ⟨1, 64, 17, 6⟩ = true := by decide +kernel

theorem walkOk_765 : mainOkS 765 0 ⟨1, 64, 19, 6⟩ = true := by decide +kernel

theorem walkOk_767 : mainOkS 767 0 ⟨0, 16, 19, 5⟩ = true := by decide +kernel

theorem walkOk_851 : loop0Ok 851 ⟨0, 16, 10, 5⟩ = true := by decide +kernel

theorem walkOk_869 : loop0Ok 869 ⟨0, 16, 13, 6⟩ = true := by decide +kernel

theorem walkOk_871 : loop0Ok 871 ⟨0, 16, 13, 5⟩ = true := by decide +kernel

theorem walkOk_887 : loop1Ok 887 1 ⟨1, 64, 15, 8⟩ = true := by decide +kernel

theorem walkOk_895 : loop1Ok 895 0 ⟨1, 64, 11, 7⟩ = true := by decide +kernel

theorem walkOk_903 : loop1Ok 903 0 ⟨1, 64, 14, 7⟩ = true := by decide +kernel

theorem walkOk_905 : loop0Ok 905 ⟨0, 16, 13, 4⟩ = true := by decide +kernel

theorem walkOk_917 : loop0Ok 917 ⟨0, 16, 17, 5⟩ = true := by decide +kernel

theorem walkOk_925 : loop1Ok 925 1 ⟨1, 64, 14, 7⟩ = true := by decide +kernel

theorem walkOk_940 : loop0Ok 940 ⟨0, 16, 17, 4⟩ = true := by decide +kernel

theorem walkOk_941 : loop1Ok 941 0 ⟨1, 64, 14, 6⟩ = true := by decide +kernel

theorem walkOk_944 : loop1Ok 944 0 ⟨1, 64, 17, 6⟩ = true := by decide +kernel

theorem walkOk_947 : loop1Ok 947 0 ⟨1, 64, 19, 6⟩ = true := by decide +kernel

theorem walkOk_949 : loop0Ok 949 ⟨0, 16, 19, 5⟩ = true := by decide +kernel

end
end LeanVM.Guest.End
