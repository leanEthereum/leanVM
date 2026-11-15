/-
  LeanVM.Guest.B1.Tables.VtC.AGlue

  What the honest valuation's equations give between `verify_tables`' ranges: the pull side's
  selectors, `ξ`'s powers, the GKR leaf values read, the sponge after the evaluations.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup
public import LeanVM.Guest.B1.Tables.VtC.FFinal
public import LeanVM.Guest.B1.Tables.VtC.FData

/-!
# Between the ranges

`vt_pull_good`: the pull side's selectors are the push side's. `vt_xi_good`: `ξ`'s powers.
`vt_leaves_good`: the three GKR leaf values are `gkr_leaves`' words. `vt_evalFs_good`: the
sponge after the `153` evaluations is the last permutation's capacity with the last evaluation
waiting, its rate cells `σ4688`, `σ4689`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 10000 in
/-- **The pull side's selectors are the push side's**, honestly. -/
theorem vt_pull_good (hl : args.length = 21) : VtPullSelsH (vtσ rd w args) := by
  have g1334 := (vt_goodL (rd := rd) (w := w) hl 1376 [.atom (.copy (.n 1335) (.n 858))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1336 := (vt_goodL (rd := rd) (w := w) hl 1378 [.atom (.copy (.n 1337) (.n 863))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1338 := (vt_goodL (rd := rd) (w := w) hl 1380 [.atom (.copy (.n 1339) (.n 868))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1340 := (vt_goodL (rd := rd) (w := w) hl 1382 [.atom (.copy (.n 1341) (.n 873))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1342 := (vt_goodL (rd := rd) (w := w) hl 1384 [.atom (.copy (.n 1343) (.n 878))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1344 := (vt_goodL (rd := rd) (w := w) hl 1386 [.atom (.copy (.n 1345) (.n 887))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1346 := (vt_goodL (rd := rd) (w := w) hl 1388 [.atom (.copy (.n 1347) (.n 896))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1348 := (vt_goodL (rd := rd) (w := w) hl 1390 [.atom (.copy (.n 1349) (.n 905))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1350 := (vt_goodL (rd := rd) (w := w) hl 1392 [.atom (.copy (.n 1351) (.n 914))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1352 := (vt_goodL (rd := rd) (w := w) hl 1394 [.atom (.copy (.n 1353) (.n 923))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1354 := (vt_goodL (rd := rd) (w := w) hl 1396 [.atom (.copy (.n 1355) (.n 932))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1356 := (vt_goodL (rd := rd) (w := w) hl 1398 [.atom (.copy (.n 1357) (.n 941))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1358 := (vt_goodL (rd := rd) (w := w) hl 1400 [.atom (.copy (.n 1359) (.n 950))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1360 := (vt_goodL (rd := rd) (w := w) hl 1402 [.atom (.copy (.n 1361) (.n 959))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1362 := (vt_goodL (rd := rd) (w := w) hl 1404 [.atom (.copy (.n 1363) (.n 968))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1364 := (vt_goodL (rd := rd) (w := w) hl 1406 [.atom (.copy (.n 1365) (.n 977))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1366 := (vt_goodL (rd := rd) (w := w) hl 1408 [.atom (.copy (.n 1367) (.n 986))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1368 := (vt_goodL (rd := rd) (w := w) hl 1410 [.atom (.copy (.n 1369) (.n 995))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1370 := (vt_goodL (rd := rd) (w := w) hl 1412 [.atom (.copy (.n 1371) (.n 1004))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1372 := (vt_goodL (rd := rd) (w := w) hl 1414 [.atom (.copy (.n 1373) (.n 1013))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1374 := (vt_goodL (rd := rd) (w := w) hl 1416 [.atom (.copy (.n 1375) (.n 1022))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1376 := (vt_goodL (rd := rd) (w := w) hl 1418 [.atom (.copy (.n 1377) (.n 1031))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1378 := (vt_goodL (rd := rd) (w := w) hl 1420 [.atom (.copy (.n 1379) (.n 1040))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1380 := (vt_goodL (rd := rd) (w := w) hl 1422 [.atom (.copy (.n 1381) (.n 1049))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1382 := (vt_goodL (rd := rd) (w := w) hl 1424 [.atom (.copy (.n 1383) (.n 1058))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1384 := (vt_goodL (rd := rd) (w := w) hl 1426 [.atom (.copy (.n 1385) (.n 1067))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1386 := (vt_goodL (rd := rd) (w := w) hl 1428 [.atom (.copy (.n 1387) (.n 1076))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1388 := (vt_goodL (rd := rd) (w := w) hl 1430 [.atom (.copy (.n 1389) (.n 1085))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1390 := (vt_goodL (rd := rd) (w := w) hl 1432 [.atom (.copy (.n 1391) (.n 1094))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1392 := (vt_goodL (rd := rd) (w := w) hl 1434 [.atom (.copy (.n 1393) (.n 1103))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1394 := (vt_goodL (rd := rd) (w := w) hl 1436 [.atom (.copy (.n 1395) (.n 1112))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1396 := (vt_goodL (rd := rd) (w := w) hl 1438 [.atom (.copy (.n 1397) (.n 1121))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1398 := (vt_goodL (rd := rd) (w := w) hl 1440 [.atom (.copy (.n 1399) (.n 1130))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1400 := (vt_goodL (rd := rd) (w := w) hl 1442 [.atom (.copy (.n 1401) (.n 1139))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1402 := (vt_goodL (rd := rd) (w := w) hl 1444 [.atom (.copy (.n 1403) (.n 1148))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1404 := (vt_goodL (rd := rd) (w := w) hl 1446 [.atom (.copy (.n 1405) (.n 1157))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1406 := (vt_goodL (rd := rd) (w := w) hl 1448 [.atom (.copy (.n 1407) (.n 1166))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1408 := (vt_goodL (rd := rd) (w := w) hl 1450 [.atom (.copy (.n 1409) (.n 1175))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1410 := (vt_goodL (rd := rd) (w := w) hl 1452 [.atom (.copy (.n 1411) (.n 1184))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1412 := (vt_goodL (rd := rd) (w := w) hl 1454 [.atom (.copy (.n 1413) (.n 1193))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1414 := (vt_goodL (rd := rd) (w := w) hl 1456 [.atom (.copy (.n 1415) (.n 1202))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1416 := (vt_goodL (rd := rd) (w := w) hl 1458 [.atom (.copy (.n 1417) (.n 1211))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1418 := (vt_goodL (rd := rd) (w := w) hl 1460 [.atom (.copy (.n 1419) (.n 1220))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1420 := (vt_goodL (rd := rd) (w := w) hl 1462 [.atom (.copy (.n 1421) (.n 1229))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1422 := (vt_goodL (rd := rd) (w := w) hl 1464 [.atom (.copy (.n 1423) (.n 1238))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1424 := (vt_goodL (rd := rd) (w := w) hl 1466 [.atom (.copy (.n 1425) (.n 1247))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1426 := (vt_goodL (rd := rd) (w := w) hl 1468 [.atom (.copy (.n 1427) (.n 1256))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1428 := (vt_goodL (rd := rd) (w := w) hl 1470 [.atom (.copy (.n 1429) (.n 1265))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1430 := (vt_goodL (rd := rd) (w := w) hl 1472 [.atom (.copy (.n 1431) (.n 1274))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1432 := (vt_goodL (rd := rd) (w := w) hl 1474 [.atom (.copy (.n 1433) (.n 1283))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1434 := (vt_goodL (rd := rd) (w := w) hl 1476 [.atom (.copy (.n 1435) (.n 1292))] (by rw [vtPre_drop]; decide +kernel)).1
  generalize vtσ rd w args = σ at g1334 g1336 g1338 g1340 g1342 g1344 g1346 g1348 g1350 g1352 g1354 g1356 g1358 g1360 g1362 g1364 g1366 g1368 g1370 g1372 g1374 g1376 g1378 g1380 g1382 g1384 g1386 g1388 g1390 g1392 g1394 g1396 g1398 g1400 g1402 g1404 g1406 g1408 g1410 g1412 g1414 g1416 g1418 g1420 g1422 g1424 g1426 g1428 g1430 g1432 g1434 ⊢
  simp only [GoodS, fixNe, Good] at g1334 g1336 g1338 g1340 g1342 g1344 g1346 g1348 g1350 g1352 g1354 g1356 g1358 g1360 g1362 g1364 g1366 g1368 g1370 g1372 g1374 g1376 g1378 g1380 g1382 g1384 g1386 g1388 g1390 g1392 g1394 g1396 g1398 g1400 g1402 g1404 g1406 g1408 g1410 g1412 g1414 g1416 g1418 g1420 g1422 g1424 g1426 g1428 g1430 g1432 g1434
  simp only [VtPullSelsH, g1334, g1336, g1338, g1340, g1342, g1344, g1346, g1348, g1350, g1352, g1354, g1356, g1358, g1360, g1362, g1364, g1366, g1368, g1370, g1372, g1374, g1376, g1378, g1380, g1382, g1384, g1386, g1388, g1390, g1392, g1394, g1396, g1398, g1400, g1402, g1404, g1406, g1408, g1410, g1412, g1414, g1416, g1418, g1420, g1422, g1424, g1426, g1428, g1430, g1432, g1434, and_self]

/-- **`ξ`'s powers**, honestly. -/
theorem vt_xi_good (hl : args.length = 21) :
    vtσ rd w args (.n 2612) = 1 ∧ vtσ rd w args (.n 2613) = vtσ rd w args (.n 2611) ∧
      vtσ rd w args (.n 2614) = vtσ rd w args (.n 2611) ^ 2 ∧
      vtσ rd w args (.n 2615) = vtσ rd w args (.n 2611) ^ 3 ∧
      vtσ rd w args (.n 2616) = vtσ rd w args (.n 2611) ^ 4 := by
  have g := vt_goodL (rd := rd) (w := w) hl 2633 [.atom (.const (.n 2612) (word 1 0)),
    .atom (.mul (.n 2613) (.n 2612) (.n 2611)), .atom (.mul (.n 2614) (.n 2613) (.n 2611)),
    .atom (.mul (.n 2615) (.n 2614) (.n 2611)), .atom (.mul (.n 2616) (.n 2615) (.n 2611))]
    (by rw [vtPre_drop]; decide +kernel)
  generalize vtσ rd w args = σ at g ⊢
  simp only [GoodL, GoodS, fixNe, Good, Nat.reduceLT, and_self, ↓reduceIte, and_true] at g
  obtain ⟨g0, g1, g2, g3, g4⟩ := g
  rw [tb_word_one] at g0
  refine ⟨g0, ?_, ?_, ?_, ?_⟩
  · rw [g1, g0, one_mul]
  · rw [g2, g1, g0, one_mul, sq]
  · rw [g3, g2, g1, g0, one_mul]; ring
  · rw [g4, g3, g2, g1, g0, one_mul]; ring

/-- **The GKR leaf values** are read from `gkr_leaves` (`args 17`). -/
theorem vt_leaves_good (hl : args.length = 21) {leaves : List E} (hll : leaves.length = 3)
    (h : TbReadsAt rd (args.getD 17 0) leaves) :
    vtσ rd w args (.n 2442) = leaves.getD 0 0 ∧ vtσ rd w args (.n 2488) = leaves.getD 1 0 ∧
      vtσ rd w args (.n 2543) = leaves.getD 2 0 := by
  have hp : vtσ rd w args (.n 17) = args.getD 17 0 := vt_param hl (by norm_num)
  have rd0 := vt_read (rd := rd) (w := w) hl 2488 (d := .n 2442) (p := .n 17) (off := 0)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  have rd1 := vt_read (rd := rd) (w := w) hl 2534 (d := .n 2488) (p := .n 17) (off := 1)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  have rd2 := vt_read (rd := rd) (w := w) hl 2589 (d := .n 2543) (p := .n 17) (off := 2)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  rw [hp] at rd0 rd1 rd2
  have l0 := h 0 (by omega)
  have l1 := h 1 (by omega)
  have l2 := h 2 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [rd0, rdAt, l0.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]
  · rw [rd1, rdAt, l1.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]
  · rw [rd2, rdAt, l2.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]

theorem vtPermCap_38 : vtPermCap 38 = [.n 4687, .n 4688, .n 4689, .n 4690, .n 4691] := by
  decide +kernel

theorem vtEvB_152 : vtEvB 152 = 4692 := by decide +kernel

/-- **The sponge after the evaluations**, from the evaluations' sponge facts: the last
permutation's capacity and the last evaluation waiting, its rate cells `σ4688`, `σ4689`. -/
theorem vt_evalFs_good (hl : args.length = 21)
    (hF : ∀ j < 38, (⟨vtCapV (vtσ rd w args) 0, []⟩ : Fs).absorbAll
        ((vtEvs (vtσ rd w args)).take (4 * (j + 1))) dsObserve =
      ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
      vtCapV (vtσ rd w args) (j + 1) = capOf (Fs.perm ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩)) :
    rateOf (vtEvalFs (vtσ rd w args)).pend =
        [vtσ rd w args (.n 4693), vtσ rd w args (.n 4694), 0, 0, 0, 0, 0, 0] ∧
      (vtEvalFs (vtσ rd w args)).cap = [vtσ rd w args (.n 4687), vtσ rd w args (.n 4688),
        vtσ rd w args (.n 4689), vtσ rd w args (.n 4690), vtσ rd w args (.n 4691)] := by
  have g := vt_goodL (rd := rd) (w := w) hl 4269 [.atom (.copy (.n 4693) (.n 4692)),
    .atom (.const (.n 4694) (word 0 1))] (by rw [vtPre_drop]; decide +kernel)
  generalize vtσ rd w args = σ at g hF ⊢
  simp only [GoodL, GoodS, fixNe, Good, and_true] at g
  obtain ⟨g0, g1⟩ := g
  obtain ⟨h37, hp37⟩ := hF 37 (by norm_num)
  have hr : vtEvs σ = (List.range 152).map (fun k ↦ σ (.n (vtEvB k))) ++
      [σ (.n (vtEvB 152))] := by
    show (List.range (152 + 1)).map _ = _
    rw [List.range_succ, List.map_append, List.map_singleton]
  have ht : (vtEvs σ).take (4 * (37 + 1)) = (List.range 152).map fun k ↦ σ (.n (vtEvB k)) := by
    rw [hr, List.take_left' (by simp)]
  rw [ht] at h37
  have hE : vtEvalFs σ = ⟨vtCapV σ 38, [(σ (.n (vtEvB 152)), dsObserve)]⟩ := by
    rw [vtEvalFs, hr, fs_absorbAll_append, h37, tb_absorbAll_full' _ (by simp [vtEvs]) _
      (by simp) (by simp), ← hp37]
    rfl
  rw [hE, rateOf_eq_cells _ (by simp), vtEvB_152]
  refine ⟨?_, ?_⟩
  · simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons,
      List.length_nil, Keccak.scalarCells, g0, g1]
    rfl
  · simp [vtCapV, vtPermCap_38]

end

end
end LeanVM.Guest.B1.Tables
