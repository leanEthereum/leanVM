/-
  LeanVM.Guest.B1.Opening.QueriesPlacedAll

  Every deployed specialization of `opening_queries` is `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedS0
public import LeanVM.Guest.B1.Opening.QueriesPlacedS1
public import LeanVM.Guest.B1.Opening.QueriesPlacedS2
public import LeanVM.Guest.B1.Opening.QueriesPlacedS3

/-!
# `opening_queries`, `CompleteAtB`, every specialization

`opening_queries_completeAtB`: each of the 76 deployed specializations (`openingQueriesLoops`:
name, loop helper, shape) is `CompleteAtB` (`OqCompleteDB` at the shape's `Oq` and `odd`, by a tree
of at most `oqBound fs name loop N` words) at every frame size `fs` and frame certificate `cert`
(`OqFits` trivial: no frame runs).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **Every deployed `opening_queries` is `CompleteAtB`.** -/
theorem opening_queries_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) :
    ∀ p ∈ openingQueriesLoops, OqCompleteDB fs cert p.1 p.2.1 p.2.2.oq p.2.2.odd := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqD_1009 fs cert
  · exact oqD_1011 fs cert
  · exact oqD_1013 fs cert
  · exact oqD_1015 fs cert
  · exact oqD_1022 fs cert
  · exact oqD_1023 fs cert
  · exact oqD_1024 fs cert
  · exact oqD_1025 fs cert
  · exact oqD_1032 fs cert
  · exact oqD_1038 fs cert
  · exact oqD_1039 fs cert
  · exact oqD_1040 fs cert
  · exact oqD_1041 fs cert
  · exact oqD_1070 fs cert
  · exact oqD_1071 fs cert
  · exact oqD_1076 fs cert
  · exact oqD_1079 fs cert
  · exact oqD_1080 fs cert
  · exact oqD_1081 fs cert
  · exact oqD_1082 fs cert
  · exact oqD_1110 fs cert
  · exact oqD_1111 fs cert
  · exact oqD_1116 fs cert
  · exact oqD_1119 fs cert
  · exact oqD_1120 fs cert
  · exact oqD_1121 fs cert
  · exact oqD_1122 fs cert
  · exact oqD_1150 fs cert
  · exact oqD_1151 fs cert
  · exact oqD_1156 fs cert
  · exact oqD_1159 fs cert
  · exact oqD_1160 fs cert
  · exact oqD_1161 fs cert
  · exact oqD_1162 fs cert
  · exact oqD_1190 fs cert
  · exact oqD_1191 fs cert
  · exact oqD_1195 fs cert
  · exact oqD_1199 fs cert
  · exact oqD_1200 fs cert
  · exact oqD_1201 fs cert
  · exact oqD_1236 fs cert
  · exact oqD_1237 fs cert
  · exact oqD_1241 fs cert
  · exact oqD_1245 fs cert
  · exact oqD_1246 fs cert
  · exact oqD_1247 fs cert
  · exact oqD_1280 fs cert
  · exact oqD_1281 fs cert
  · exact oqD_1285 fs cert
  · exact oqD_1289 fs cert
  · exact oqD_1290 fs cert
  · exact oqD_1291 fs cert
  · exact oqD_1324 fs cert
  · exact oqD_1325 fs cert
  · exact oqD_1329 fs cert
  · exact oqD_1332 fs cert
  · exact oqD_1333 fs cert
  · exact oqD_1334 fs cert
  · exact oqD_1367 fs cert
  · exact oqD_1368 fs cert
  · exact oqD_1372 fs cert
  · exact oqD_1377 fs cert
  · exact oqD_1378 fs cert
  · exact oqD_1379 fs cert
  · exact oqD_1417 fs cert
  · exact oqD_1418 fs cert
  · exact oqD_1422 fs cert
  · exact oqD_1426 fs cert
  · exact oqD_1427 fs cert
  · exact oqD_1428 fs cert
  · exact oqD_1464 fs cert
  · exact oqD_1465 fs cert
  · exact oqD_1469 fs cert
  · exact oqD_1474 fs cert
  · exact oqD_1475 fs cert
  · exact oqD_1476 fs cert

end
end LeanVM.Guest.B1
