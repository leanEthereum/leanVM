/-
  LeanVM.Guest.Fast.WhirTablesCheck

  `open_stacked`'s literal tables are its template's at every size and rate (`callsOK`).
-/

module

public import LeanVM.Guest.Fast.WhirCalls.R0
public import LeanVM.Guest.Fast.WhirCalls.R1
public import LeanVM.Guest.Fast.WhirCalls.R2
public import LeanVM.Guest.Fast.WhirCalls.R3

namespace LeanVM.Guest.Fast

@[expose] public section

/-- **Every configuration's dispatches are the table's.** -/
theorem callsOK : ∀ j < 44, CallsOK j
  | 0, _ => callsOK_0
  | 1, _ => callsOK_1
  | 2, _ => callsOK_2
  | 3, _ => callsOK_3
  | 4, _ => callsOK_4
  | 5, _ => callsOK_5
  | 6, _ => callsOK_6
  | 7, _ => callsOK_7
  | 8, _ => callsOK_8
  | 9, _ => callsOK_9
  | 10, _ => callsOK_10
  | 11, _ => callsOK_11
  | 12, _ => callsOK_12
  | 13, _ => callsOK_13
  | 14, _ => callsOK_14
  | 15, _ => callsOK_15
  | 16, _ => callsOK_16
  | 17, _ => callsOK_17
  | 18, _ => callsOK_18
  | 19, _ => callsOK_19
  | 20, _ => callsOK_20
  | 21, _ => callsOK_21
  | 22, _ => callsOK_22
  | 23, _ => callsOK_23
  | 24, _ => callsOK_24
  | 25, _ => callsOK_25
  | 26, _ => callsOK_26
  | 27, _ => callsOK_27
  | 28, _ => callsOK_28
  | 29, _ => callsOK_29
  | 30, _ => callsOK_30
  | 31, _ => callsOK_31
  | 32, _ => callsOK_32
  | 33, _ => callsOK_33
  | 34, _ => callsOK_34
  | 35, _ => callsOK_35
  | 36, _ => callsOK_36
  | 37, _ => callsOK_37
  | 38, _ => callsOK_38
  | 39, _ => callsOK_39
  | 40, _ => callsOK_40
  | 41, _ => callsOK_41
  | 42, _ => callsOK_42
  | 43, _ => callsOK_43
  | _ + 44, h => absurd h (by omega)

end
end LeanVM.Guest.Fast
