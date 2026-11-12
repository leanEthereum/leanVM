/-
  LeanVM.Guest.B1.Opening.QueriesPlacedEAll

  Every deployed specialization of `opening_queries` is `CompleteAtE`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedES0
public import LeanVM.Guest.B1.Opening.QueriesPlacedES1
public import LeanVM.Guest.B1.Opening.QueriesPlacedES2
public import LeanVM.Guest.B1.Opening.QueriesPlacedES3

/-!
# `opening_queries`, `CompleteAtE`, every specialization

`opening_queries_completeAtE`: each of the 76 deployed specializations (`openingQueriesLoops`:
name, loop helper, shape) is `CompleteAtE` (`OqCompleteDE` at the shape's `Oq` and `odd`, by a tree
of exactly `oqBound fs name loop N` words) at every frame size `fs` and frame certificate `cert`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **Every deployed `opening_queries` is `CompleteAtE`.** -/
theorem opening_queries_completeAtE (fs : String → ℕ) (cert : String → V → ℕ) :
    ∀ p ∈ openingQueriesLoops, OqCompleteDE fs cert p.1 p.2.1 p.2.2.oq p.2.2.odd := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqDE_1009 fs cert
  · exact oqDE_1011 fs cert
  · exact oqDE_1013 fs cert
  · exact oqDE_1015 fs cert
  · exact oqDE_1022 fs cert
  · exact oqDE_1023 fs cert
  · exact oqDE_1024 fs cert
  · exact oqDE_1025 fs cert
  · exact oqDE_1032 fs cert
  · exact oqDE_1038 fs cert
  · exact oqDE_1039 fs cert
  · exact oqDE_1040 fs cert
  · exact oqDE_1041 fs cert
  · exact oqDE_1070 fs cert
  · exact oqDE_1071 fs cert
  · exact oqDE_1076 fs cert
  · exact oqDE_1079 fs cert
  · exact oqDE_1080 fs cert
  · exact oqDE_1081 fs cert
  · exact oqDE_1082 fs cert
  · exact oqDE_1110 fs cert
  · exact oqDE_1111 fs cert
  · exact oqDE_1116 fs cert
  · exact oqDE_1119 fs cert
  · exact oqDE_1120 fs cert
  · exact oqDE_1121 fs cert
  · exact oqDE_1122 fs cert
  · exact oqDE_1150 fs cert
  · exact oqDE_1151 fs cert
  · exact oqDE_1156 fs cert
  · exact oqDE_1159 fs cert
  · exact oqDE_1160 fs cert
  · exact oqDE_1161 fs cert
  · exact oqDE_1162 fs cert
  · exact oqDE_1190 fs cert
  · exact oqDE_1191 fs cert
  · exact oqDE_1195 fs cert
  · exact oqDE_1199 fs cert
  · exact oqDE_1200 fs cert
  · exact oqDE_1201 fs cert
  · exact oqDE_1236 fs cert
  · exact oqDE_1237 fs cert
  · exact oqDE_1241 fs cert
  · exact oqDE_1245 fs cert
  · exact oqDE_1246 fs cert
  · exact oqDE_1247 fs cert
  · exact oqDE_1280 fs cert
  · exact oqDE_1281 fs cert
  · exact oqDE_1285 fs cert
  · exact oqDE_1289 fs cert
  · exact oqDE_1290 fs cert
  · exact oqDE_1291 fs cert
  · exact oqDE_1324 fs cert
  · exact oqDE_1325 fs cert
  · exact oqDE_1329 fs cert
  · exact oqDE_1332 fs cert
  · exact oqDE_1333 fs cert
  · exact oqDE_1334 fs cert
  · exact oqDE_1367 fs cert
  · exact oqDE_1368 fs cert
  · exact oqDE_1372 fs cert
  · exact oqDE_1377 fs cert
  · exact oqDE_1378 fs cert
  · exact oqDE_1379 fs cert
  · exact oqDE_1417 fs cert
  · exact oqDE_1418 fs cert
  · exact oqDE_1422 fs cert
  · exact oqDE_1426 fs cert
  · exact oqDE_1427 fs cert
  · exact oqDE_1428 fs cert
  · exact oqDE_1464 fs cert
  · exact oqDE_1465 fs cert
  · exact oqDE_1469 fs cert
  · exact oqDE_1474 fs cert
  · exact oqDE_1475 fs cert
  · exact oqDE_1476 fs cert

end
end LeanVM.Guest.B1
