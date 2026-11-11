/-
  LeanVM.Guest.B1.Bits.QueryWindowsAll

  `decode_query_windows` is sound at each of its 21 specializations.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindows
public import LeanVM.Guest.B1.Bits.QueryWindowsData

/-!
# `decode_query_windows`, every specialization

`decode_query_windows_all_holds`: each deployed `(name, depth, cap depth)` is its template
(`queryWindows_data`, kernel evaluation) at a shape the generic proof covers (`qwShape_all`), so
`qw_sound` applies.
-/

namespace LeanVM.Guest.B1

@[expose] public section

theorem decode_query_windows_all_holds : decode_query_windows_all_Spec :=
  fun p hp ↦ qw_sound (qwShape_all p hp) (queryWindows_data p hp)

end
end LeanVM.Guest.B1
