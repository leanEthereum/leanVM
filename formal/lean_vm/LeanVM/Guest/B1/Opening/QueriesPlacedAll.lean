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

`opening_queries_completeAtB`: each of the 49 deployed specializations (`openingQueriesLoops`:
name, loop helper, shape, `odd`) is `CompleteAtB` (`OqCompleteDB`, by a tree of at most
`oqBound fs name loop N` words) at every frame size `fs` and frame certificate `cert` (`OqFits`
trivial: no frame runs); `opening_queries_completeAtD`, its `CompleteAtD`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **Every deployed `opening_queries` is `CompleteAtB`.** -/
theorem opening_queries_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) :
    ∀ p ∈ openingQueriesLoops, OqCompleteDB fs cert p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqD_1109 fs cert
  · exact oqD_1111 fs cert
  · exact oqD_1113 fs cert
  · exact oqD_1115 fs cert
  · exact oqD_1121 fs cert
  · exact oqD_1123 fs cert
  · exact oqD_1124 fs cert
  · exact oqD_1125 fs cert
  · exact oqD_1131 fs cert
  · exact oqD_1155 fs cert
  · exact oqD_1156 fs cert
  · exact oqD_1157 fs cert
  · exact oqD_1158 fs cert
  · exact oqD_1162 fs cert
  · exact oqD_1198 fs cert
  · exact oqD_1199 fs cert
  · exact oqD_1203 fs cert
  · exact oqD_1235 fs cert
  · exact oqD_1236 fs cert
  · exact oqD_1240 fs cert
  · exact oqD_1273 fs cert
  · exact oqD_1274 fs cert
  · exact oqD_1277 fs cert
  · exact oqD_1306 fs cert
  · exact oqD_1307 fs cert
  · exact oqD_1311 fs cert
  · exact oqD_1345 fs cert
  · exact oqD_1346 fs cert
  · exact oqD_1347 fs cert
  · exact oqD_1350 fs cert
  · exact oqD_1384 fs cert
  · exact oqD_1385 fs cert
  · exact oqD_1388 fs cert
  · exact oqD_1422 fs cert
  · exact oqD_1423 fs cert
  · exact oqD_1427 fs cert
  · exact oqD_1459 fs cert
  · exact oqD_1460 fs cert
  · exact oqD_1464 fs cert
  · exact oqD_1501 fs cert
  · exact oqD_1502 fs cert
  · exact oqD_1506 fs cert
  · exact oqD_1545 fs cert
  · exact oqD_1549 fs cert
  · exact oqD_1592 fs cert
  · exact oqD_1593 fs cert
  · exact oqD_1597 fs cert
  · exact oqD_1639 fs cert
  · exact oqD_1643 fs cert

end
end LeanVM.Guest.B1
