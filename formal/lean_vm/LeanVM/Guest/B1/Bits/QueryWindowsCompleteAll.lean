/-
  LeanVM.Guest.B1.Bits.QueryWindowsCompleteAll

  `decode_query_windows` is complete at each of its 18 specializations.
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

theorem decode_query_windows_complete_all_holds : decode_query_windows_complete_all_Spec :=
  fun p hp ↦ qw_complete (qwShape_all p hp) (queryWindows_data p hp)

end
end LeanVM.Guest.B1
