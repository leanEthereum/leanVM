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
theorem vt_pull_good (hl : args.length = 20) : VtPullSelsH (vtσ rd w args) := by
  have g1334 := (vt_goodL (rd := rd) (w := w) hl 1376 [.atom (.copy (.n 1334) (.n 857))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1336 := (vt_goodL (rd := rd) (w := w) hl 1378 [.atom (.copy (.n 1336) (.n 862))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1338 := (vt_goodL (rd := rd) (w := w) hl 1380 [.atom (.copy (.n 1338) (.n 867))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1340 := (vt_goodL (rd := rd) (w := w) hl 1382 [.atom (.copy (.n 1340) (.n 872))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1342 := (vt_goodL (rd := rd) (w := w) hl 1384 [.atom (.copy (.n 1342) (.n 877))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1344 := (vt_goodL (rd := rd) (w := w) hl 1386 [.atom (.copy (.n 1344) (.n 886))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1346 := (vt_goodL (rd := rd) (w := w) hl 1388 [.atom (.copy (.n 1346) (.n 895))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1348 := (vt_goodL (rd := rd) (w := w) hl 1390 [.atom (.copy (.n 1348) (.n 904))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1350 := (vt_goodL (rd := rd) (w := w) hl 1392 [.atom (.copy (.n 1350) (.n 913))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1352 := (vt_goodL (rd := rd) (w := w) hl 1394 [.atom (.copy (.n 1352) (.n 922))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1354 := (vt_goodL (rd := rd) (w := w) hl 1396 [.atom (.copy (.n 1354) (.n 931))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1356 := (vt_goodL (rd := rd) (w := w) hl 1398 [.atom (.copy (.n 1356) (.n 940))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1358 := (vt_goodL (rd := rd) (w := w) hl 1400 [.atom (.copy (.n 1358) (.n 949))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1360 := (vt_goodL (rd := rd) (w := w) hl 1402 [.atom (.copy (.n 1360) (.n 958))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1362 := (vt_goodL (rd := rd) (w := w) hl 1404 [.atom (.copy (.n 1362) (.n 967))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1364 := (vt_goodL (rd := rd) (w := w) hl 1406 [.atom (.copy (.n 1364) (.n 976))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1366 := (vt_goodL (rd := rd) (w := w) hl 1408 [.atom (.copy (.n 1366) (.n 985))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1368 := (vt_goodL (rd := rd) (w := w) hl 1410 [.atom (.copy (.n 1368) (.n 994))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1370 := (vt_goodL (rd := rd) (w := w) hl 1412 [.atom (.copy (.n 1370) (.n 1003))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1372 := (vt_goodL (rd := rd) (w := w) hl 1414 [.atom (.copy (.n 1372) (.n 1012))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1374 := (vt_goodL (rd := rd) (w := w) hl 1416 [.atom (.copy (.n 1374) (.n 1021))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1376 := (vt_goodL (rd := rd) (w := w) hl 1418 [.atom (.copy (.n 1376) (.n 1030))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1378 := (vt_goodL (rd := rd) (w := w) hl 1420 [.atom (.copy (.n 1378) (.n 1039))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1380 := (vt_goodL (rd := rd) (w := w) hl 1422 [.atom (.copy (.n 1380) (.n 1048))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1382 := (vt_goodL (rd := rd) (w := w) hl 1424 [.atom (.copy (.n 1382) (.n 1057))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1384 := (vt_goodL (rd := rd) (w := w) hl 1426 [.atom (.copy (.n 1384) (.n 1066))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1386 := (vt_goodL (rd := rd) (w := w) hl 1428 [.atom (.copy (.n 1386) (.n 1075))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1388 := (vt_goodL (rd := rd) (w := w) hl 1430 [.atom (.copy (.n 1388) (.n 1084))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1390 := (vt_goodL (rd := rd) (w := w) hl 1432 [.atom (.copy (.n 1390) (.n 1093))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1392 := (vt_goodL (rd := rd) (w := w) hl 1434 [.atom (.copy (.n 1392) (.n 1102))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1394 := (vt_goodL (rd := rd) (w := w) hl 1436 [.atom (.copy (.n 1394) (.n 1111))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1396 := (vt_goodL (rd := rd) (w := w) hl 1438 [.atom (.copy (.n 1396) (.n 1120))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1398 := (vt_goodL (rd := rd) (w := w) hl 1440 [.atom (.copy (.n 1398) (.n 1129))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1400 := (vt_goodL (rd := rd) (w := w) hl 1442 [.atom (.copy (.n 1400) (.n 1138))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1402 := (vt_goodL (rd := rd) (w := w) hl 1444 [.atom (.copy (.n 1402) (.n 1147))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1404 := (vt_goodL (rd := rd) (w := w) hl 1446 [.atom (.copy (.n 1404) (.n 1156))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1406 := (vt_goodL (rd := rd) (w := w) hl 1448 [.atom (.copy (.n 1406) (.n 1165))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1408 := (vt_goodL (rd := rd) (w := w) hl 1450 [.atom (.copy (.n 1408) (.n 1174))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1410 := (vt_goodL (rd := rd) (w := w) hl 1452 [.atom (.copy (.n 1410) (.n 1183))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1412 := (vt_goodL (rd := rd) (w := w) hl 1454 [.atom (.copy (.n 1412) (.n 1192))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1414 := (vt_goodL (rd := rd) (w := w) hl 1456 [.atom (.copy (.n 1414) (.n 1201))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1416 := (vt_goodL (rd := rd) (w := w) hl 1458 [.atom (.copy (.n 1416) (.n 1210))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1418 := (vt_goodL (rd := rd) (w := w) hl 1460 [.atom (.copy (.n 1418) (.n 1219))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1420 := (vt_goodL (rd := rd) (w := w) hl 1462 [.atom (.copy (.n 1420) (.n 1228))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1422 := (vt_goodL (rd := rd) (w := w) hl 1464 [.atom (.copy (.n 1422) (.n 1237))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1424 := (vt_goodL (rd := rd) (w := w) hl 1466 [.atom (.copy (.n 1424) (.n 1246))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1426 := (vt_goodL (rd := rd) (w := w) hl 1468 [.atom (.copy (.n 1426) (.n 1255))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1428 := (vt_goodL (rd := rd) (w := w) hl 1470 [.atom (.copy (.n 1428) (.n 1264))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1430 := (vt_goodL (rd := rd) (w := w) hl 1472 [.atom (.copy (.n 1430) (.n 1273))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1432 := (vt_goodL (rd := rd) (w := w) hl 1474 [.atom (.copy (.n 1432) (.n 1282))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1434 := (vt_goodL (rd := rd) (w := w) hl 1476 [.atom (.copy (.n 1434) (.n 1291))] (by rw [vtPre_drop]; decide +kernel)).1
  generalize vtσ rd w args = σ at g1334 g1336 g1338 g1340 g1342 g1344 g1346 g1348 g1350 g1352 g1354 g1356 g1358 g1360 g1362 g1364 g1366 g1368 g1370 g1372 g1374 g1376 g1378 g1380 g1382 g1384 g1386 g1388 g1390 g1392 g1394 g1396 g1398 g1400 g1402 g1404 g1406 g1408 g1410 g1412 g1414 g1416 g1418 g1420 g1422 g1424 g1426 g1428 g1430 g1432 g1434 ⊢
  simp only [GoodS, fixNe, Good] at g1334 g1336 g1338 g1340 g1342 g1344 g1346 g1348 g1350 g1352 g1354 g1356 g1358 g1360 g1362 g1364 g1366 g1368 g1370 g1372 g1374 g1376 g1378 g1380 g1382 g1384 g1386 g1388 g1390 g1392 g1394 g1396 g1398 g1400 g1402 g1404 g1406 g1408 g1410 g1412 g1414 g1416 g1418 g1420 g1422 g1424 g1426 g1428 g1430 g1432 g1434
  simp only [VtPullSelsH, g1334, g1336, g1338, g1340, g1342, g1344, g1346, g1348, g1350, g1352, g1354, g1356, g1358, g1360, g1362, g1364, g1366, g1368, g1370, g1372, g1374, g1376, g1378, g1380, g1382, g1384, g1386, g1388, g1390, g1392, g1394, g1396, g1398, g1400, g1402, g1404, g1406, g1408, g1410, g1412, g1414, g1416, g1418, g1420, g1422, g1424, g1426, g1428, g1430, g1432, g1434, and_self]

/-- **`ξ`'s powers**, honestly. -/
theorem vt_xi_good (hl : args.length = 20) :
    vtσ rd w args (.n 2611) = 1 ∧ vtσ rd w args (.n 2612) = vtσ rd w args (.n 2610) ∧
      vtσ rd w args (.n 2613) = vtσ rd w args (.n 2610) ^ 2 ∧
      vtσ rd w args (.n 2614) = vtσ rd w args (.n 2610) ^ 3 ∧
      vtσ rd w args (.n 2615) = vtσ rd w args (.n 2610) ^ 4 := by
  have g := vt_goodL (rd := rd) (w := w) hl 2633 [.atom (.const (.n 2611) (word 1 0)),
    .atom (.mul (.n 2612) (.n 2611) (.n 2610)), .atom (.mul (.n 2613) (.n 2612) (.n 2610)),
    .atom (.mul (.n 2614) (.n 2613) (.n 2610)), .atom (.mul (.n 2615) (.n 2614) (.n 2610))]
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
theorem vt_leaves_good (hl : args.length = 20) {leaves : List E} (hll : leaves.length = 3)
    (h : TbReadsAt rd (args.getD 17 0) leaves) :
    vtσ rd w args (.n 2441) = leaves.getD 0 0 ∧ vtσ rd w args (.n 2487) = leaves.getD 1 0 ∧
      vtσ rd w args (.n 2542) = leaves.getD 2 0 := by
  have hp : vtσ rd w args (.n 17) = args.getD 17 0 := vt_param hl (by norm_num)
  have rd0 := vt_read (rd := rd) (w := w) hl 2488 (d := .n 2441) (p := .n 17) (off := 0)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  have rd1 := vt_read (rd := rd) (w := w) hl 2534 (d := .n 2487) (p := .n 17) (off := 1)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  have rd2 := vt_read (rd := rd) (w := w) hl 2589 (d := .n 2542) (p := .n 17) (off := 2)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  rw [hp] at rd0 rd1 rd2
  have l0 := h 0 (by omega)
  have l1 := h 1 (by omega)
  have l2 := h 2 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [rd0, rdAt, l0.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]
  · rw [rd1, rdAt, l1.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]
  · rw [rd2, rdAt, l2.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]

theorem vtPermCap_38 : vtPermCap 38 = [.n 4682, .n 4683, .n 4684, .n 4685, .n 4686] := by
  decide +kernel

theorem vtEvB_152 : vtEvB 152 = 4687 := by decide +kernel

/-- **The sponge after the evaluations**, from the evaluations' sponge facts: the last
permutation's capacity and the last evaluation waiting, its rate cells `σ4688`, `σ4689`. -/
theorem vt_evalFs_good (hl : args.length = 20)
    (hF : ∀ j < 38, (⟨vtCapV (vtσ rd w args) 0, []⟩ : Fs).absorbAll
        ((vtEvs (vtσ rd w args)).take (4 * (j + 1))) dsObserve =
      ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
      vtCapV (vtσ rd w args) (j + 1) = capOf (Fs.perm ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩)) :
    rateOf (vtEvalFs (vtσ rd w args)).pend =
        [vtσ rd w args (.n 4688), vtσ rd w args (.n 4689), 0, 0, 0, 0, 0, 0] ∧
      (vtEvalFs (vtσ rd w args)).cap = [vtσ rd w args (.n 4682), vtσ rd w args (.n 4683),
        vtσ rd w args (.n 4684), vtσ rd w args (.n 4685), vtσ rd w args (.n 4686)] := by
  have g := vt_goodL (rd := rd) (w := w) hl 4264 [.atom (.copy (.n 4688) (.n 4687)),
    .atom (.const (.n 4689) (word 0 1))] (by rw [vtPre_drop]; decide +kernel)
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
