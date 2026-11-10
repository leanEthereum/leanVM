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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqSpecW_1109
  · exact oqSpecW_1111
  · exact oqSpecW_1113
  · exact oqSpecW_1115
  · exact oqSpecW_1121
  · exact oqSpecW_1123
  · exact oqSpecW_1124
  · exact oqSpecW_1125
  · exact oqSpecW_1131
  · exact oqSpecW_1155
  · exact oqSpecW_1156
  · exact oqSpecW_1157
  · exact oqSpecW_1158
  · exact oqSpecW_1162
  · exact oqSpecW_1198
  · exact oqSpecW_1199
  · exact oqSpecW_1203
  · exact oqSpecW_1235
  · exact oqSpecW_1236
  · exact oqSpecW_1240
  · exact oqSpecW_1273
  · exact oqSpecW_1274
  · exact oqSpecW_1277
  · exact oqSpecW_1306
  · exact oqSpecW_1307
  · exact oqSpecW_1311
  · exact oqSpecW_1345
  · exact oqSpecW_1346
  · exact oqSpecW_1347
  · exact oqSpecW_1350
  · exact oqSpecW_1384
  · exact oqSpecW_1385
  · exact oqSpecW_1388
  · exact oqSpecW_1422
  · exact oqSpecW_1423
  · exact oqSpecW_1427
  · exact oqSpecW_1459
  · exact oqSpecW_1460
  · exact oqSpecW_1464
  · exact oqSpecW_1501
  · exact oqSpecW_1502
  · exact oqSpecW_1506
  · exact oqSpecW_1545
  · exact oqSpecW_1549
  · exact oqSpecW_1592
  · exact oqSpecW_1593
  · exact oqSpecW_1597
  · exact oqSpecW_1639
  · exact oqSpecW_1643

end
end LeanVM.Guest.B1
