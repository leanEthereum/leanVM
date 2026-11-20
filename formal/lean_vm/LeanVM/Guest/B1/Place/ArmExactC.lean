/-
  LeanVM.Guest.B1.Place.ArmExactC

  `armExactOk` of `open_stacked`'s arms 9 to 10, by the kernel: each arm's callees twenty at a time.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

/-- Arm 9's callees. -/
noncomputable def callees9 : List String := Stmt.blockCallees (fn% «open_stacked__L9»).body

/-- Arm 9's callees' check. -/
noncomputable def calleeOk9 (g : String) : Bool := armExactS g || exactCallee idx% «open_stacked__L9» g

private theorem callees9_0 : ((callees9.drop (20 * 0)).take 20).all calleeOk9 = true := by
  decide +kernel

private theorem callees9_1 : ((callees9.drop (20 * 1)).take 20).all calleeOk9 = true := by
  decide +kernel

private theorem callees9_2 : ((callees9.drop (20 * 2)).take 20).all calleeOk9 = true := by
  decide +kernel

private theorem callees9_3 : ((callees9.drop (20 * 3)).take 20).all calleeOk9 = true := by
  decide +kernel

private theorem callees9_4 : ((callees9.drop (20 * 4)).take 20).all calleeOk9 = true := by
  decide +kernel

private theorem callees9_5 : ((callees9.drop (20 * 5)).take 20).all calleeOk9 = true := by
  decide +kernel

private theorem callees9_6 : (callees9.drop (20 * 6)).all calleeOk9 = true := by
  decide +kernel

/-- Arm 9's callees by chunks, stated over `callees9` (elaborating the chain against the body's callees unfolds them). -/
private theorem callees9_all : (callees9.drop (20 * 0)).all calleeOk9 = true :=
  all_drop_chunk callees9_0 <| all_drop_chunk callees9_1 <| all_drop_chunk callees9_2 <| all_drop_chunk callees9_3 <| all_drop_chunk callees9_4 <| all_drop_chunk callees9_5 <|
    callees9_6

theorem armExact9 : armExactOk ("open_stacked__L" ++ natStr 9) idx% «open_stacked__L9» = true :=
  armExactOk_of (fn := fn% «open_stacked__L9») rfl (by decide +kernel) (by decide +kernel) callees9_all

/-- Arm 10's callees. -/
noncomputable def callees10 : List String := Stmt.blockCallees (fn% «open_stacked__L10»).body

/-- Arm 10's callees' check. -/
noncomputable def calleeOk10 (g : String) : Bool := armExactS g || exactCallee idx% «open_stacked__L10» g

private theorem callees10_0 : ((callees10.drop (20 * 0)).take 20).all calleeOk10 = true := by
  decide +kernel

private theorem callees10_1 : ((callees10.drop (20 * 1)).take 20).all calleeOk10 = true := by
  decide +kernel

private theorem callees10_2 : ((callees10.drop (20 * 2)).take 20).all calleeOk10 = true := by
  decide +kernel

private theorem callees10_3 : ((callees10.drop (20 * 3)).take 20).all calleeOk10 = true := by
  decide +kernel

private theorem callees10_4 : ((callees10.drop (20 * 4)).take 20).all calleeOk10 = true := by
  decide +kernel

private theorem callees10_5 : ((callees10.drop (20 * 5)).take 20).all calleeOk10 = true := by
  decide +kernel

private theorem callees10_6 : (callees10.drop (20 * 6)).all calleeOk10 = true := by
  decide +kernel

/-- Arm 10's callees by chunks, stated over `callees10` (elaborating the chain against the body's callees unfolds them). -/
private theorem callees10_all : (callees10.drop (20 * 0)).all calleeOk10 = true :=
  all_drop_chunk callees10_0 <| all_drop_chunk callees10_1 <| all_drop_chunk callees10_2 <| all_drop_chunk callees10_3 <| all_drop_chunk callees10_4 <| all_drop_chunk callees10_5 <|
    callees10_6

theorem armExact10 : armExactOk ("open_stacked__L" ++ natStr 10) idx% «open_stacked__L10» = true :=
  armExactOk_of (fn := fn% «open_stacked__L10») rfl (by decide +kernel) (by decide +kernel) callees10_all

end
end LeanVM.Guest.B1.Arm
