/-
  LeanVM.Guest.Memory.GuestMainFree.All

  No function of the guest's core IR calls `main`.
-/

module

public import LeanVM.Guest.Memory.GuestMainFree.Part00
public import LeanVM.Guest.Memory.GuestMainFree.Part01
public import LeanVM.Guest.Memory.GuestMainFree.Part02
public import LeanVM.Guest.Memory.GuestMainFree.Part03
public import LeanVM.Guest.Memory.GuestMainFree.Part04
public import LeanVM.Guest.Memory.GuestMainFree.Part05
public import LeanVM.Guest.Memory.GuestMainFree.Part06
public import LeanVM.Guest.Memory.GuestMainFree.Part07
public import LeanVM.Guest.Memory.GuestMainFree.Part08
public import LeanVM.Guest.Memory.GuestMainFree.Part09
public import LeanVM.Guest.Memory.GuestMainFree.Part10
public import LeanVM.Guest.Memory.GuestMainFree.Part11
public import LeanVM.Guest.Memory.GuestMainFree.Part12
public import LeanVM.Guest.Memory.GuestMainFree.Part13
public import LeanVM.Guest.Memory.GuestMainFree.Part14
public import LeanVM.Guest.Memory.GuestMainFree.Part15
public import LeanVM.Guest.Memory.GuestMainFree.Part16
public import LeanVM.Guest.Memory.GuestMainFree.Part17
public import LeanVM.Guest.Memory.GuestMainFree.Part18

namespace LeanVM.Guest

@[expose] public section

theorem mainFree_all : ∀ j < 1043, mainFreeJ j = true := by
  intro j hj
  by_cases h0 : j < 16
  · exact mainFreeRange_0.get (by omega) (by omega)
  by_cases h1 : j < 17
  · exact mainFreeRange_16.get (by omega) (by omega)
  by_cases h2 : j < 37
  · exact mainFreeRange_17.get (by omega) (by omega)
  by_cases h3 : j < 105
  · exact mainFreeRange_37.get (by omega) (by omega)
  by_cases h4 : j < 174
  · exact mainFreeRange_105.get (by omega) (by omega)
  by_cases h5 : j < 198
  · exact mainFreeRange_174.get (by omega) (by omega)
  by_cases h6 : j < 255
  · exact mainFreeRange_198.get (by omega) (by omega)
  by_cases h7 : j < 326
  · exact mainFreeRange_255.get (by omega) (by omega)
  by_cases h8 : j < 397
  · exact mainFreeRange_326.get (by omega) (by omega)
  by_cases h9 : j < 468
  · exact mainFreeRange_397.get (by omega) (by omega)
  by_cases h10 : j < 529
  · exact mainFreeRange_468.get (by omega) (by omega)
  by_cases h11 : j < 586
  · exact mainFreeRange_529.get (by omega) (by omega)
  by_cases h12 : j < 656
  · exact mainFreeRange_586.get (by omega) (by omega)
  by_cases h13 : j < 726
  · exact mainFreeRange_656.get (by omega) (by omega)
  by_cases h14 : j < 796
  · exact mainFreeRange_726.get (by omega) (by omega)
  by_cases h15 : j < 866
  · exact mainFreeRange_796.get (by omega) (by omega)
  by_cases h16 : j < 937
  · exact mainFreeRange_866.get (by omega) (by omega)
  by_cases h17 : j < 997
  · exact mainFreeRange_937.get (by omega) (by omega)
  exact mainFreeRange_997.get (by omega) (by omega)

end
end LeanVM.Guest
