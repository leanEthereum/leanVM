/-
  LeanVM.Guest.B1.Opening.QueriesAllW

  Every deployed specialization of `opening_queries` is sound with its queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesW0
public import LeanVM.Guest.B1.Opening.QueriesW1
public import LeanVM.Guest.B1.Opening.QueriesW2
public import LeanVM.Guest.B1.Opening.QueriesW3

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **Every deployed `opening_queries` is sound with its queries named.** -/
theorem opening_queries_all_sound_w : opening_queries_all_sound_w_Spec := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqSpecW_1084
  · exact oqSpecW_1086
  · exact oqSpecW_1088
  · exact oqSpecW_1090
  · exact oqSpecW_1096
  · exact oqSpecW_1097
  · exact oqSpecW_1098
  · exact oqSpecW_1099
  · exact oqSpecW_1105
  · exact oqSpecW_1110
  · exact oqSpecW_1142
  · exact oqSpecW_1143
  · exact oqSpecW_1144
  · exact oqSpecW_1145
  · exact oqSpecW_1149
  · exact oqSpecW_1182
  · exact oqSpecW_1183
  · exact oqSpecW_1187
  · exact oqSpecW_1220
  · exact oqSpecW_1221
  · exact oqSpecW_1225
  · exact oqSpecW_1258
  · exact oqSpecW_1259
  · exact oqSpecW_1263
  · exact oqSpecW_1298
  · exact oqSpecW_1299
  · exact oqSpecW_1300
  · exact oqSpecW_1303
  · exact oqSpecW_1337
  · exact oqSpecW_1338
  · exact oqSpecW_1341
  · exact oqSpecW_1375
  · exact oqSpecW_1376
  · exact oqSpecW_1380
  · exact oqSpecW_1412
  · exact oqSpecW_1413
  · exact oqSpecW_1417
  · exact oqSpecW_1454
  · exact oqSpecW_1455
  · exact oqSpecW_1459
  · exact oqSpecW_1498
  · exact oqSpecW_1502
  · exact oqSpecW_1545
  · exact oqSpecW_1546
  · exact oqSpecW_1550
  · exact oqSpecW_1592
  · exact oqSpecW_1596

end
end LeanVM.Guest.B1
