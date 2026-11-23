/-
  LeanVM.Guest.B1.Place.ArmExactB

  `armExactOk` of `open_stacked`'s arms 6 to 8, by the kernel: each arm's callees twenty at a time.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

/-- Arm 6's callees. -/
noncomputable def callees6 : List String := Stmt.blockCallees (fn% «open_stacked__L6»).body

/-- Arm 6's callees' check. -/
noncomputable def calleeOk6 (g : String) : Bool := armExactS g || exactCallee idx% «open_stacked__L6» g

private theorem callees6_0 : ((callees6.drop (20 * 0)).take 20).all calleeOk6 = true := by
  decide +kernel

private theorem callees6_1 : ((callees6.drop (20 * 1)).take 20).all calleeOk6 = true := by
  decide +kernel

private theorem callees6_2 : ((callees6.drop (20 * 2)).take 20).all calleeOk6 = true := by
  decide +kernel

private theorem callees6_3 : ((callees6.drop (20 * 3)).take 20).all calleeOk6 = true := by
  decide +kernel

private theorem callees6_4 : ((callees6.drop (20 * 4)).take 20).all calleeOk6 = true := by
  decide +kernel

private theorem callees6_5 : ((callees6.drop (20 * 5)).take 20).all calleeOk6 = true := by
  decide +kernel

private theorem callees6_6 : (callees6.drop (20 * 6)).all calleeOk6 = true := by
  decide +kernel

/-- Arm 6's callees by chunks, stated over `callees6` (elaborating the chain against the body's callees unfolds them). -/
private theorem callees6_all : (callees6.drop (20 * 0)).all calleeOk6 = true :=
  all_drop_chunk callees6_0 <| all_drop_chunk callees6_1 <| all_drop_chunk callees6_2 <| all_drop_chunk callees6_3 <| all_drop_chunk callees6_4 <| all_drop_chunk callees6_5 <|
    callees6_6

theorem armExact6 : armExactOk ("open_stacked__L" ++ natStr 6) idx% «open_stacked__L6» = true :=
  armExactOk_of (fn := fn% «open_stacked__L6») rfl (by decide +kernel) (by decide +kernel) callees6_all

/-- Arm 7's callees. -/
noncomputable def callees7 : List String := Stmt.blockCallees (fn% «open_stacked__L7»).body

/-- Arm 7's callees' check. -/
noncomputable def calleeOk7 (g : String) : Bool := armExactS g || exactCallee idx% «open_stacked__L7» g

private theorem callees7_0 : ((callees7.drop (20 * 0)).take 20).all calleeOk7 = true := by
  decide +kernel

private theorem callees7_1 : ((callees7.drop (20 * 1)).take 20).all calleeOk7 = true := by
  decide +kernel

private theorem callees7_2 : ((callees7.drop (20 * 2)).take 20).all calleeOk7 = true := by
  decide +kernel

private theorem callees7_3 : ((callees7.drop (20 * 3)).take 20).all calleeOk7 = true := by
  decide +kernel

private theorem callees7_4 : ((callees7.drop (20 * 4)).take 20).all calleeOk7 = true := by
  decide +kernel

private theorem callees7_5 : ((callees7.drop (20 * 5)).take 20).all calleeOk7 = true := by
  decide +kernel

private theorem callees7_6 : (callees7.drop (20 * 6)).all calleeOk7 = true := by
  decide +kernel

/-- Arm 7's callees by chunks, stated over `callees7` (elaborating the chain against the body's callees unfolds them). -/
private theorem callees7_all : (callees7.drop (20 * 0)).all calleeOk7 = true :=
  all_drop_chunk callees7_0 <| all_drop_chunk callees7_1 <| all_drop_chunk callees7_2 <| all_drop_chunk callees7_3 <| all_drop_chunk callees7_4 <| all_drop_chunk callees7_5 <|
    callees7_6

theorem armExact7 : armExactOk ("open_stacked__L" ++ natStr 7) idx% «open_stacked__L7» = true :=
  armExactOk_of (fn := fn% «open_stacked__L7») rfl (by decide +kernel) (by decide +kernel) callees7_all

/-- Arm 8's callees. -/
noncomputable def callees8 : List String := Stmt.blockCallees (fn% «open_stacked__L8»).body

/-- Arm 8's callees' check. -/
noncomputable def calleeOk8 (g : String) : Bool := armExactS g || exactCallee idx% «open_stacked__L8» g

private theorem callees8_0 : ((callees8.drop (20 * 0)).take 20).all calleeOk8 = true := by
  decide +kernel

private theorem callees8_1 : ((callees8.drop (20 * 1)).take 20).all calleeOk8 = true := by
  decide +kernel

private theorem callees8_2 : ((callees8.drop (20 * 2)).take 20).all calleeOk8 = true := by
  decide +kernel

private theorem callees8_3 : ((callees8.drop (20 * 3)).take 20).all calleeOk8 = true := by
  decide +kernel

private theorem callees8_4 : ((callees8.drop (20 * 4)).take 20).all calleeOk8 = true := by
  decide +kernel

private theorem callees8_5 : ((callees8.drop (20 * 5)).take 20).all calleeOk8 = true := by
  decide +kernel

private theorem callees8_6 : (callees8.drop (20 * 6)).all calleeOk8 = true := by
  decide +kernel

/-- Arm 8's callees by chunks, stated over `callees8` (elaborating the chain against the body's callees unfolds them). -/
private theorem callees8_all : (callees8.drop (20 * 0)).all calleeOk8 = true :=
  all_drop_chunk callees8_0 <| all_drop_chunk callees8_1 <| all_drop_chunk callees8_2 <| all_drop_chunk callees8_3 <| all_drop_chunk callees8_4 <| all_drop_chunk callees8_5 <|
    callees8_6

theorem armExact8 : armExactOk ("open_stacked__L" ++ natStr 8) idx% «open_stacked__L8» = true :=
  armExactOk_of (fn := fn% «open_stacked__L8») rfl (by decide +kernel) (by decide +kernel) callees8_all

end
end LeanVM.Guest.B1.Arm
