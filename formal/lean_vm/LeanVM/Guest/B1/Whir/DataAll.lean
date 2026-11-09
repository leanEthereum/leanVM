/-
  LeanVM.Guest.B1.Whir.DataAll

  Every candidate's core IR is its template.
-/

module

public import LeanVM.Guest.B1.Whir.Data0
public import LeanVM.Guest.B1.Whir.Data1
public import LeanVM.Guest.B1.Whir.Data2
public import LeanVM.Guest.B1.Whir.Data3
public import LeanVM.Guest.B1.Whir.Data4
public import LeanVM.Guest.B1.Whir.Data5
public import LeanVM.Guest.B1.Whir.Data6
public import LeanVM.Guest.B1.Whir.Data7
public import LeanVM.Guest.B1.Whir.Data8
public import LeanVM.Guest.B1.Whir.Data9
public import LeanVM.Guest.B1.Whir.Data10
public import LeanVM.Guest.B1.Whir.Data11
public import LeanVM.Guest.B1.Whir.Data12
public import LeanVM.Guest.B1.Whir.Data13
public import LeanVM.Guest.B1.Whir.Data14
public import LeanVM.Guest.B1.Whir.Data15
public import LeanVM.Guest.B1.Whir.Data16
public import LeanVM.Guest.B1.Whir.Data17
public import LeanVM.Guest.B1.Whir.Data18
public import LeanVM.Guest.B1.Whir.Data19
public import LeanVM.Guest.B1.Whir.Data20
public import LeanVM.Guest.B1.Whir.Data21
public import LeanVM.Guest.B1.Whir.Data22
public import LeanVM.Guest.B1.Whir.Data23
public import LeanVM.Guest.B1.Whir.Data24
public import LeanVM.Guest.B1.Whir.Data25
public import LeanVM.Guest.B1.Whir.Data26
public import LeanVM.Guest.B1.Whir.Data27

/-!
# All 28 candidates

`osData_all`: `OsData m` for every candidate `m < 28` (`Whir/Data0.lean` to `Whir/Data27.lean`).
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every candidate's core IR is its template.** -/
theorem osData_all (m : Nat) (h : m < 28) : OsData m := by
  interval_cases m
  · exact osData_0
  · exact osData_1
  · exact osData_2
  · exact osData_3
  · exact osData_4
  · exact osData_5
  · exact osData_6
  · exact osData_7
  · exact osData_8
  · exact osData_9
  · exact osData_10
  · exact osData_11
  · exact osData_12
  · exact osData_13
  · exact osData_14
  · exact osData_15
  · exact osData_16
  · exact osData_17
  · exact osData_18
  · exact osData_19
  · exact osData_20
  · exact osData_21
  · exact osData_22
  · exact osData_23
  · exact osData_24
  · exact osData_25
  · exact osData_26
  · exact osData_27

end
end LeanVM.Guest.B1.Whir
