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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact oqSpecW_1009
  · exact oqSpecW_1011
  · exact oqSpecW_1013
  · exact oqSpecW_1015
  · exact oqSpecW_1022
  · exact oqSpecW_1023
  · exact oqSpecW_1024
  · exact oqSpecW_1025
  · exact oqSpecW_1032
  · exact oqSpecW_1038
  · exact oqSpecW_1039
  · exact oqSpecW_1040
  · exact oqSpecW_1041
  · exact oqSpecW_1070
  · exact oqSpecW_1071
  · exact oqSpecW_1076
  · exact oqSpecW_1079
  · exact oqSpecW_1080
  · exact oqSpecW_1081
  · exact oqSpecW_1082
  · exact oqSpecW_1110
  · exact oqSpecW_1111
  · exact oqSpecW_1116
  · exact oqSpecW_1119
  · exact oqSpecW_1120
  · exact oqSpecW_1121
  · exact oqSpecW_1122
  · exact oqSpecW_1150
  · exact oqSpecW_1151
  · exact oqSpecW_1156
  · exact oqSpecW_1159
  · exact oqSpecW_1160
  · exact oqSpecW_1161
  · exact oqSpecW_1162
  · exact oqSpecW_1190
  · exact oqSpecW_1191
  · exact oqSpecW_1195
  · exact oqSpecW_1199
  · exact oqSpecW_1200
  · exact oqSpecW_1201
  · exact oqSpecW_1236
  · exact oqSpecW_1237
  · exact oqSpecW_1241
  · exact oqSpecW_1245
  · exact oqSpecW_1246
  · exact oqSpecW_1247
  · exact oqSpecW_1280
  · exact oqSpecW_1281
  · exact oqSpecW_1285
  · exact oqSpecW_1289
  · exact oqSpecW_1290
  · exact oqSpecW_1291
  · exact oqSpecW_1324
  · exact oqSpecW_1325
  · exact oqSpecW_1329
  · exact oqSpecW_1332
  · exact oqSpecW_1333
  · exact oqSpecW_1334
  · exact oqSpecW_1367
  · exact oqSpecW_1368
  · exact oqSpecW_1372
  · exact oqSpecW_1377
  · exact oqSpecW_1378
  · exact oqSpecW_1379
  · exact oqSpecW_1417
  · exact oqSpecW_1418
  · exact oqSpecW_1422
  · exact oqSpecW_1426
  · exact oqSpecW_1427
  · exact oqSpecW_1428
  · exact oqSpecW_1464
  · exact oqSpecW_1465
  · exact oqSpecW_1469
  · exact oqSpecW_1474
  · exact oqSpecW_1475
  · exact oqSpecW_1476

end
end LeanVM.Guest.B1
