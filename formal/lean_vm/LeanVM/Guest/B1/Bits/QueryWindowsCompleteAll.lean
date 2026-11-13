/-
  LeanVM.Guest.B1.Bits.QueryWindowsCompleteAll

  `decode_query_windows` is complete at each of its 43 specializations.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsComplete
public import LeanVM.Guest.B1.Bits.QueryWindowsData

/-!
# `decode_query_windows`, complete, every specialization

`decode_query_windows_complete_all_holds`: each deployed `(name, depth, cap depth)` is its template
(`queryWindows_data`, kernel evaluation) at a shape the generic proof covers (`qwShape_all`), so
`qw_complete` applies.
-/

namespace LeanVM.Guest.B1

@[expose] public section

/-- `decode_query_windows__L{d}_L{cd}` is complete in the core IR. -/
def decode_query_windows_complete_Spec (name : String) (d cd : ℕ) : Prop :=
  decode_query_windows_complete_SpecP coreProgram name d cd

/-- Every deployed specialization. -/
def decode_query_windows_complete_all_Spec : Prop := decode_query_windows_complete_all_SpecP coreProgram

theorem decode_query_windows_complete_all_holds : decode_query_windows_complete_all_Spec :=
  fun p hp ↦ qw_complete (qwShape_all p hp) (queryWindows_data p hp)

end
end LeanVM.Guest.B1
