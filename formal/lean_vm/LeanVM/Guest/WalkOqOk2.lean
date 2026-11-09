/-
  LeanVM.Guest.WalkOqOk2

  The certificates of a quarter of `opening_queries`' specializations and loops (those whose
  templates `B1/Opening/QueriesBody2.lean` checks) hand on the walk's obligations in the forms
  `WalkKnownDefs` checks, by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

theorem walkOk_455 : mainOkS 455 0 ⟨1, 64, 10, 8⟩ = true := by decide +kernel

theorem walkOk_474 : mainOkS 474 0 ⟨0, 16, 12, 6⟩ = true := by decide +kernel

theorem walkOk_477 : mainOkS 477 0 ⟨0, 16, 12, 5⟩ = true := by decide +kernel

theorem walkOk_509 : mainOkS 509 0 ⟨1, 64, 13, 8⟩ = true := by decide +kernel

theorem walkOk_539 : mainOkS 539 0 ⟨0, 16, 16, 6⟩ = true := by decide +kernel

theorem walkOk_541 : mainOkS 541 0 ⟨0, 16, 16, 5⟩ = true := by decide +kernel

theorem walkOk_573 : mainOkS 573 0 ⟨1, 64, 13, 7⟩ = true := by decide +kernel

theorem walkOk_578 : mainOkS 578 0 ⟨0, 16, 12, 4⟩ = true := by decide +kernel

theorem walkOk_608 : mainOkS 608 0 ⟨1, 64, 16, 7⟩ = true := by decide +kernel

theorem walkOk_627 : mainOkS 627 0 ⟨0, 16, 16, 4⟩ = true := by decide +kernel

theorem walkOk_665 : mainOkS 665 1 ⟨1, 64, 15, 7⟩ = true := by decide +kernel

theorem walkOk_687 : mainOkS 687 1 ⟨1, 64, 17, 7⟩ = true := by decide +kernel

theorem walkOk_700 : mainOkS 700 0 ⟨0, 16, 18, 6⟩ = true := by decide +kernel

theorem walkOk_777 : mainOkS 777 0 ⟨1, 64, 20, 6⟩ = true := by decide +kernel

theorem walkOk_855 : loop1Ok 855 0 ⟨1, 64, 10, 8⟩ = true := by decide +kernel

theorem walkOk_863 : loop0Ok 863 ⟨0, 16, 12, 6⟩ = true := by decide +kernel

theorem walkOk_865 : loop0Ok 865 ⟨0, 16, 12, 5⟩ = true := by decide +kernel

theorem walkOk_873 : loop1Ok 873 0 ⟨1, 64, 13, 8⟩ = true := by decide +kernel

theorem walkOk_889 : loop0Ok 889 ⟨0, 16, 16, 6⟩ = true := by decide +kernel

theorem walkOk_891 : loop0Ok 891 ⟨0, 16, 16, 5⟩ = true := by decide +kernel

theorem walkOk_899 : loop1Ok 899 0 ⟨1, 64, 13, 7⟩ = true := by decide +kernel

theorem walkOk_901 : loop0Ok 901 ⟨0, 16, 12, 4⟩ = true := by decide +kernel

theorem walkOk_909 : loop1Ok 909 0 ⟨1, 64, 16, 7⟩ = true := by decide +kernel

theorem walkOk_919 : loop0Ok 919 ⟨0, 16, 16, 4⟩ = true := by decide +kernel

theorem walkOk_927 : loop1Ok 927 1 ⟨1, 64, 15, 7⟩ = true := by decide +kernel

theorem walkOk_931 : loop1Ok 931 1 ⟨1, 64, 17, 7⟩ = true := by decide +kernel

theorem walkOk_936 : loop0Ok 936 ⟨0, 16, 18, 6⟩ = true := by decide +kernel

theorem walkOk_951 : loop1Ok 951 0 ⟨1, 64, 20, 6⟩ = true := by decide +kernel

end
end LeanVM.Guest.End
