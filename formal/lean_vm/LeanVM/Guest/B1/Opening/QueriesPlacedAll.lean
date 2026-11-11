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

`opening_queries_completeAtB`: each of the 47 deployed specializations (`openingQueriesLoops`:
name, loop helper, shape, `odd`) is `CompleteAtB` (`OqCompleteDB`, by a tree of exactly
`oqBound fs name loop N` words, `CompleteAtE`) at every frame size `fs` and frame certificate `cert` (`OqFits`
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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqD_1084 fs cert
  · exact oqD_1086 fs cert
  · exact oqD_1088 fs cert
  · exact oqD_1090 fs cert
  · exact oqD_1096 fs cert
  · exact oqD_1097 fs cert
  · exact oqD_1098 fs cert
  · exact oqD_1099 fs cert
  · exact oqD_1105 fs cert
  · exact oqD_1110 fs cert
  · exact oqD_1142 fs cert
  · exact oqD_1143 fs cert
  · exact oqD_1144 fs cert
  · exact oqD_1145 fs cert
  · exact oqD_1149 fs cert
  · exact oqD_1182 fs cert
  · exact oqD_1183 fs cert
  · exact oqD_1187 fs cert
  · exact oqD_1220 fs cert
  · exact oqD_1221 fs cert
  · exact oqD_1225 fs cert
  · exact oqD_1258 fs cert
  · exact oqD_1259 fs cert
  · exact oqD_1263 fs cert
  · exact oqD_1298 fs cert
  · exact oqD_1299 fs cert
  · exact oqD_1300 fs cert
  · exact oqD_1303 fs cert
  · exact oqD_1337 fs cert
  · exact oqD_1338 fs cert
  · exact oqD_1341 fs cert
  · exact oqD_1375 fs cert
  · exact oqD_1376 fs cert
  · exact oqD_1380 fs cert
  · exact oqD_1412 fs cert
  · exact oqD_1413 fs cert
  · exact oqD_1417 fs cert
  · exact oqD_1454 fs cert
  · exact oqD_1455 fs cert
  · exact oqD_1459 fs cert
  · exact oqD_1498 fs cert
  · exact oqD_1502 fs cert
  · exact oqD_1545 fs cert
  · exact oqD_1546 fs cert
  · exact oqD_1550 fs cert
  · exact oqD_1592 fs cert
  · exact oqD_1596 fs cert

end
end LeanVM.Guest.B1
