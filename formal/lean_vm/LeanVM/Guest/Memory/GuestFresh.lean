/-
  LeanVM.Guest.Memory.GuestFresh

  The guest's core IR has fresh range-check temporaries (`Program.Fresh`): each named by its
  range check only, none a parameter.
-/

module

public import LeanVM.Guest.Memory.GuestFresh.Part00
public import LeanVM.Guest.Memory.GuestFresh.Part01
public import LeanVM.Guest.Memory.GuestFresh.Part02
public import LeanVM.Guest.Memory.GuestFresh.Part03
public import LeanVM.Guest.Memory.GuestFresh.Part04
public import LeanVM.Guest.Memory.GuestFresh.Part05
public import LeanVM.Guest.Memory.GuestFresh.Fresh16
public import LeanVM.Guest.Memory.GuestFresh.Fresh17

/-!
# The guest's temporaries are fresh

`Fn.freshB` is evaluated by the kernel on ranges of `coreProgram`'s functions (`FreshRange`, one
declaration each), cut by the number of values the functions name and spread over modules
(`GuestFresh/Part*.lean`). Functions 16 and 17 (`verify_lean_xmss`, `verify_sig_lean_sphincs`)
are too large for one check: their bodies are certified by ranges of statements
(`GuestFresh/Fresh16.lean`, `Fresh17.lean`, `RangeFresh`).
-/

namespace LeanVM.Guest

open Core Memory

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The guest's range-check temporaries are fresh.** -/
theorem coreProgram_fresh : coreProgram.Fresh := by
  have a0 : FreshRange 0 12 := freshRange_0
  have a1 : FreshRange 0 15 := a0.append' freshRange_12 rfl rfl
  have a2 : FreshRange 0 16 := a1.append' freshRange_15 rfl rfl
  have b0 : FreshRange 18 52 := freshRange_18
  have b1 : FreshRange 18 160 := b0.append' freshRange_70 rfl rfl
  have b2 : FreshRange 18 164 := b1.append' freshRange_178 rfl rfl
  have b3 : FreshRange 18 168 := b2.append' freshRange_182 rfl rfl
  have b4 : FreshRange 18 172 := b3.append' freshRange_186 rfl rfl
  have b5 : FreshRange 18 176 := b4.append' freshRange_190 rfl rfl
  have b6 : FreshRange 18 180 := b5.append' freshRange_194 rfl rfl
  have b7 : FreshRange 18 185 := b6.append' freshRange_198 rfl rfl
  have b8 : FreshRange 18 292 := b7.append' freshRange_203 rfl rfl
  have b9 : FreshRange 18 442 := b8.append' freshRange_310 rfl rfl
  have b10 : FreshRange 18 501 := b9.append' freshRange_460 rfl rfl
  have b11 : FreshRange 18 530 := b10.append' freshRange_519 rfl rfl
  have b12 : FreshRange 18 554 := b11.append' freshRange_548 rfl rfl
  have b13 : FreshRange 18 670 := b12.append' freshRange_572 rfl rfl
  have b14 : FreshRange 18 820 := b13.append' freshRange_688 rfl rfl
  have b15 : FreshRange 18 959 := b14.append' freshRange_838 rfl rfl
  have b16 : FreshRange 18 974 := b15.append' freshRange_977 rfl rfl
  have b17 : FreshRange 18 991 := b16.append' freshRange_992 rfl rfl
  have b18 : FreshRange 18 1006 := b17.append' freshRange_1009 rfl rfl
  have b19 : FreshRange 18 1020 := b18.append' freshRange_1024 rfl rfl
  have b20 : FreshRange 18 1025 := b19.append' freshRange_1038 rfl rfl
  have hsplit : coreProgram = (coreProgram.drop 0).take 16 ++ Data.core16 :: Data.core17 ::
      (coreProgram.drop 18).take 1025 := by
    rw [List.drop_zero, List.take_of_length_le (l := coreProgram.drop 18) (by simp [coreProgram_length])]
    rfl
  intro fn hfn
  rw [hsplit] at hfn
  simp only [List.mem_append, List.mem_cons] at hfn
  rcases hfn with h | rfl | rfl | h
  · exact a2.fresh h
  · exact core16_fresh
  · exact core17_fresh
  · exact b20.fresh h

end
end LeanVM.Guest
