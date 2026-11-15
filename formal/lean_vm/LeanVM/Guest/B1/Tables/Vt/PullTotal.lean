/-
  LeanVM.Guest.B1.Tables.Vt.PullTotal

  `verify_tables`' pull side total: its framework blocks' fingerprints (with the final memory and
  bytecode counts), the push side's padding sum, the selector sum and the GKR pull value.

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PushFw

/-!
# The pull side's total (G:2471-2530)

The pull side's blocks mirror the push side's: their eq weights are the push blocks' copies, and
their padding sum is the push side's. `vt_pull_total`: `bus_table_total[PULL]`. The framework blocks' coordinate values are the first loop's (`coord_vals`): constants, the index
extensions and the stream words.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `g^(2^19 - 1)`, the final `pc`, as the data writes it. -/
abbrev vtWFinalPc : E := word 12261764870545049476 0

set_option maxRecDepth 100000 in
/-- **The pull side's framework accumulator.** -/
theorem vt_pull_fw {rd : Reader} {σ : Val} (h : VtH rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2483) = σ (.n 1295) * (σ (.n 14) + (W 0 + W 1 * vtWFinalPc + W 2)) +
      σ (.n 1300) * (σ (.n 14) + (W 0 * gen + W 1 * σ (.n 1302) + W 2 * σ (.n 1306) +
        W 3 * σ (.n 1308) + W 4 * σ (.n 1310))) +
      σ (.n 1314) * (σ (.n 14) + (W 0 * gen ^ 2 + W 1 * σ (.n 1316) + W 2 * σ (.n 1320))) +
      σ (.n 1437) * σ (.n 1844) := by
  have a1335 := h.atomAt 1335 (.const (.n 1296) (word 1 0)) (by decide +kernel)
  have a1336 := h.atomAt 1336 (.const (.n 1297) (word 12261764870545049476 0)) (by decide +kernel)
  have a1337 := h.atomAt 1337 (.const (.n 1298) (word 1 0)) (by decide +kernel)
  have a1340 := h.atomAt 1340 (.const (.n 1301) (word 2 0)) (by decide +kernel)
  have a1355 := h.atomAt 1355 (.const (.n 1315) (word 4 0)) (by decide +kernel)
  have a2490 := h.atomAt 2490 (.load (.n 2444) (.n 13) 0) (by decide +kernel)
  have e2490 := tb_loadHolds_unique a2490 (hw 0 (by norm_num))
  have a2491 := h.atomAt 2491 (.mul (.n 2445) (.n 2444) (.n 1296)) (by decide +kernel)
  have a2492 := h.atomAt 2492 (.load (.n 2446) (.n 13) 1) (by decide +kernel)
  have e2492 := tb_loadHolds_unique a2492 (hw 1 (by norm_num))
  have a2493 := h.atomAt 2493 (.mul (.n 2447) (.n 2446) (.n 1297)) (by decide +kernel)
  have a2494 := h.atomAt 2494 (.add (.n 2448) (.n 2445) (.n 2447)) (by decide +kernel)
  have a2495 := h.atomAt 2495 (.load (.n 2449) (.n 13) 2) (by decide +kernel)
  have e2495 := tb_loadHolds_unique a2495 (hw 2 (by norm_num))
  have a2496 := h.atomAt 2496 (.mul (.n 2450) (.n 2449) (.n 1298)) (by decide +kernel)
  have a2497 := h.atomAt 2497 (.add (.n 2451) (.n 2448) (.n 2450)) (by decide +kernel)
  have a2498 := h.atomAt 2498 (.add (.n 2452) (.n 14) (.n 2451)) (by decide +kernel)
  have a2499 := h.atomAt 2499 (.mul (.n 2453) (.n 1295) (.n 2452)) (by decide +kernel)
  have a2500 := h.atomAt 2500 (.load (.n 2454) (.n 13) 0) (by decide +kernel)
  have e2500 := tb_loadHolds_unique a2500 (hw 0 (by norm_num))
  have a2501 := h.atomAt 2501 (.mul (.n 2455) (.n 2454) (.n 1301)) (by decide +kernel)
  have a2502 := h.atomAt 2502 (.load (.n 2456) (.n 13) 1) (by decide +kernel)
  have e2502 := tb_loadHolds_unique a2502 (hw 1 (by norm_num))
  have a2503 := h.atomAt 2503 (.mul (.n 2457) (.n 2456) (.n 1302)) (by decide +kernel)
  have a2504 := h.atomAt 2504 (.add (.n 2458) (.n 2455) (.n 2457)) (by decide +kernel)
  have a2505 := h.atomAt 2505 (.load (.n 2459) (.n 13) 2) (by decide +kernel)
  have e2505 := tb_loadHolds_unique a2505 (hw 2 (by norm_num))
  have a2506 := h.atomAt 2506 (.mul (.n 2460) (.n 2459) (.n 1306)) (by decide +kernel)
  have a2507 := h.atomAt 2507 (.add (.n 2461) (.n 2458) (.n 2460)) (by decide +kernel)
  have a2508 := h.atomAt 2508 (.load (.n 2462) (.n 13) 3) (by decide +kernel)
  have e2508 := tb_loadHolds_unique a2508 (hw 3 (by norm_num))
  have a2509 := h.atomAt 2509 (.mul (.n 2463) (.n 2462) (.n 1308)) (by decide +kernel)
  have a2510 := h.atomAt 2510 (.add (.n 2464) (.n 2461) (.n 2463)) (by decide +kernel)
  have a2511 := h.atomAt 2511 (.load (.n 2465) (.n 13) 4) (by decide +kernel)
  have e2511 := tb_loadHolds_unique a2511 (hw 4 (by norm_num))
  have a2512 := h.atomAt 2512 (.mul (.n 2466) (.n 2465) (.n 1310)) (by decide +kernel)
  have a2513 := h.atomAt 2513 (.add (.n 2467) (.n 2464) (.n 2466)) (by decide +kernel)
  have a2514 := h.atomAt 2514 (.add (.n 2468) (.n 14) (.n 2467)) (by decide +kernel)
  have a2515 := h.atomAt 2515 (.mul (.n 2469) (.n 1300) (.n 2468)) (by decide +kernel)
  have a2516 := h.atomAt 2516 (.add (.n 2470) (.n 2453) (.n 2469)) (by decide +kernel)
  have a2517 := h.atomAt 2517 (.load (.n 2471) (.n 13) 0) (by decide +kernel)
  have e2517 := tb_loadHolds_unique a2517 (hw 0 (by norm_num))
  have a2518 := h.atomAt 2518 (.mul (.n 2472) (.n 2471) (.n 1315)) (by decide +kernel)
  have a2519 := h.atomAt 2519 (.load (.n 2473) (.n 13) 1) (by decide +kernel)
  have e2519 := tb_loadHolds_unique a2519 (hw 1 (by norm_num))
  have a2520 := h.atomAt 2520 (.mul (.n 2474) (.n 2473) (.n 1316)) (by decide +kernel)
  have a2521 := h.atomAt 2521 (.add (.n 2475) (.n 2472) (.n 2474)) (by decide +kernel)
  have a2522 := h.atomAt 2522 (.load (.n 2476) (.n 13) 2) (by decide +kernel)
  have e2522 := tb_loadHolds_unique a2522 (hw 2 (by norm_num))
  have a2523 := h.atomAt 2523 (.mul (.n 2477) (.n 2476) (.n 1320)) (by decide +kernel)
  have a2524 := h.atomAt 2524 (.add (.n 2478) (.n 2475) (.n 2477)) (by decide +kernel)
  have a2525 := h.atomAt 2525 (.add (.n 2479) (.n 14) (.n 2478)) (by decide +kernel)
  have a2526 := h.atomAt 2526 (.mul (.n 2480) (.n 1314) (.n 2479)) (by decide +kernel)
  have a2527 := h.atomAt 2527 (.add (.n 2481) (.n 2470) (.n 2480)) (by decide +kernel)
  have a2528 := h.atomAt 2528 (.mul (.n 2482) (.n 1437) (.n 1844)) (by decide +kernel)
  have a2529 := h.atomAt 2529 (.add (.n 2483) (.n 2481) (.n 2482)) (by decide +kernel)
  simp only [Atom.Holds] at a1335 a1336 a1337 a1340 a1355 a2491 a2493 a2494 a2496 a2497
  simp only [Atom.Holds] at a2498 a2499 a2501 a2503 a2504 a2506 a2507 a2509 a2510 a2512
  simp only [Atom.Holds] at a2513 a2514 a2515 a2516 a2518 a2520 a2521 a2523 a2524 a2525
  simp only [Atom.Holds] at a2526 a2527 a2528 a2529
  simp only [a1335, a1336, a1337, a1340, a1355, e2490, a2491, e2492, a2493, a2494, e2495, a2496,
    a2497, a2498, a2499, e2500, a2501, e2502, a2503, a2504, e2505, a2506, a2507, e2508, a2509,
    a2510, e2511, a2512, a2513, a2514, a2515, a2516, e2517, a2518, e2519, a2520, a2521, e2522,
    a2523, a2524, a2525, a2526, a2527, a2528, a2529]
  simp only [tb_word_one, tb_word_gen, vt_word4]
  ring

set_option maxRecDepth 100000 in
/-- **The pull side's selector sum: the push blocks' copies.** -/
theorem vt_pull_sel {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 1436) = σ (.n 791) + σ (.n 808) + σ (.n 836) +
      (vtPushPadData.map fun x ↦ σ (.n x.2.2.1)).sum := by
  have a1338 := h.atomAt 1338 (.add (.n 1299) (.n 791) (.n 808)) (by decide +kernel)
  have a1353 := h.atomAt 1353 (.add (.n 1313) (.n 1299) (.n 836)) (by decide +kernel)
  have a1375 := h.atomAt 1375 (.add (.n 1334) (.n 1313) (.n 858)) (by decide +kernel)
  have a1377 := h.atomAt 1377 (.add (.n 1336) (.n 1334) (.n 863)) (by decide +kernel)
  have a1379 := h.atomAt 1379 (.add (.n 1338) (.n 1336) (.n 868)) (by decide +kernel)
  have a1381 := h.atomAt 1381 (.add (.n 1340) (.n 1338) (.n 873)) (by decide +kernel)
  have a1383 := h.atomAt 1383 (.add (.n 1342) (.n 1340) (.n 878)) (by decide +kernel)
  have a1385 := h.atomAt 1385 (.add (.n 1344) (.n 1342) (.n 887)) (by decide +kernel)
  have a1387 := h.atomAt 1387 (.add (.n 1346) (.n 1344) (.n 896)) (by decide +kernel)
  have a1389 := h.atomAt 1389 (.add (.n 1348) (.n 1346) (.n 905)) (by decide +kernel)
  have a1391 := h.atomAt 1391 (.add (.n 1350) (.n 1348) (.n 914)) (by decide +kernel)
  have a1393 := h.atomAt 1393 (.add (.n 1352) (.n 1350) (.n 923)) (by decide +kernel)
  have a1395 := h.atomAt 1395 (.add (.n 1354) (.n 1352) (.n 932)) (by decide +kernel)
  have a1397 := h.atomAt 1397 (.add (.n 1356) (.n 1354) (.n 941)) (by decide +kernel)
  have a1399 := h.atomAt 1399 (.add (.n 1358) (.n 1356) (.n 950)) (by decide +kernel)
  have a1401 := h.atomAt 1401 (.add (.n 1360) (.n 1358) (.n 959)) (by decide +kernel)
  have a1403 := h.atomAt 1403 (.add (.n 1362) (.n 1360) (.n 968)) (by decide +kernel)
  have a1405 := h.atomAt 1405 (.add (.n 1364) (.n 1362) (.n 977)) (by decide +kernel)
  have a1407 := h.atomAt 1407 (.add (.n 1366) (.n 1364) (.n 986)) (by decide +kernel)
  have a1409 := h.atomAt 1409 (.add (.n 1368) (.n 1366) (.n 995)) (by decide +kernel)
  have a1411 := h.atomAt 1411 (.add (.n 1370) (.n 1368) (.n 1004)) (by decide +kernel)
  have a1413 := h.atomAt 1413 (.add (.n 1372) (.n 1370) (.n 1013)) (by decide +kernel)
  have a1415 := h.atomAt 1415 (.add (.n 1374) (.n 1372) (.n 1022)) (by decide +kernel)
  have a1417 := h.atomAt 1417 (.add (.n 1376) (.n 1374) (.n 1031)) (by decide +kernel)
  have a1419 := h.atomAt 1419 (.add (.n 1378) (.n 1376) (.n 1040)) (by decide +kernel)
  have a1421 := h.atomAt 1421 (.add (.n 1380) (.n 1378) (.n 1049)) (by decide +kernel)
  have a1423 := h.atomAt 1423 (.add (.n 1382) (.n 1380) (.n 1058)) (by decide +kernel)
  have a1425 := h.atomAt 1425 (.add (.n 1384) (.n 1382) (.n 1067)) (by decide +kernel)
  have a1427 := h.atomAt 1427 (.add (.n 1386) (.n 1384) (.n 1076)) (by decide +kernel)
  have a1429 := h.atomAt 1429 (.add (.n 1388) (.n 1386) (.n 1085)) (by decide +kernel)
  have a1431 := h.atomAt 1431 (.add (.n 1390) (.n 1388) (.n 1094)) (by decide +kernel)
  have a1433 := h.atomAt 1433 (.add (.n 1392) (.n 1390) (.n 1103)) (by decide +kernel)
  have a1435 := h.atomAt 1435 (.add (.n 1394) (.n 1392) (.n 1112)) (by decide +kernel)
  have a1437 := h.atomAt 1437 (.add (.n 1396) (.n 1394) (.n 1121)) (by decide +kernel)
  have a1439 := h.atomAt 1439 (.add (.n 1398) (.n 1396) (.n 1130)) (by decide +kernel)
  have a1441 := h.atomAt 1441 (.add (.n 1400) (.n 1398) (.n 1139)) (by decide +kernel)
  have a1443 := h.atomAt 1443 (.add (.n 1402) (.n 1400) (.n 1148)) (by decide +kernel)
  have a1445 := h.atomAt 1445 (.add (.n 1404) (.n 1402) (.n 1157)) (by decide +kernel)
  have a1447 := h.atomAt 1447 (.add (.n 1406) (.n 1404) (.n 1166)) (by decide +kernel)
  have a1449 := h.atomAt 1449 (.add (.n 1408) (.n 1406) (.n 1175)) (by decide +kernel)
  have a1451 := h.atomAt 1451 (.add (.n 1410) (.n 1408) (.n 1184)) (by decide +kernel)
  have a1453 := h.atomAt 1453 (.add (.n 1412) (.n 1410) (.n 1193)) (by decide +kernel)
  have a1455 := h.atomAt 1455 (.add (.n 1414) (.n 1412) (.n 1202)) (by decide +kernel)
  have a1457 := h.atomAt 1457 (.add (.n 1416) (.n 1414) (.n 1211)) (by decide +kernel)
  have a1459 := h.atomAt 1459 (.add (.n 1418) (.n 1416) (.n 1220)) (by decide +kernel)
  have a1461 := h.atomAt 1461 (.add (.n 1420) (.n 1418) (.n 1229)) (by decide +kernel)
  have a1463 := h.atomAt 1463 (.add (.n 1422) (.n 1420) (.n 1238)) (by decide +kernel)
  have a1465 := h.atomAt 1465 (.add (.n 1424) (.n 1422) (.n 1247)) (by decide +kernel)
  have a1467 := h.atomAt 1467 (.add (.n 1426) (.n 1424) (.n 1256)) (by decide +kernel)
  have a1469 := h.atomAt 1469 (.add (.n 1428) (.n 1426) (.n 1265)) (by decide +kernel)
  have a1471 := h.atomAt 1471 (.add (.n 1430) (.n 1428) (.n 1274)) (by decide +kernel)
  have a1473 := h.atomAt 1473 (.add (.n 1432) (.n 1430) (.n 1283)) (by decide +kernel)
  have a1475 := h.atomAt 1475 (.add (.n 1434) (.n 1432) (.n 1292)) (by decide +kernel)
  have a1477 := h.atomAt 1477 (.copy (.n 1436) (.n 1434)) (by decide +kernel)
  simp only [Atom.Holds] at a1338 a1353 a1375 a1377 a1379 a1381 a1383 a1385 a1387 a1389
  simp only [Atom.Holds] at a1391 a1393 a1395 a1397 a1399 a1401 a1403 a1405 a1407 a1409
  simp only [Atom.Holds] at a1411 a1413 a1415 a1417 a1419 a1421 a1423 a1425 a1427 a1429
  simp only [Atom.Holds] at a1431 a1433 a1435 a1437 a1439 a1441 a1443 a1445 a1447 a1449
  simp only [Atom.Holds] at a1451 a1453 a1455 a1457 a1459 a1461 a1463 a1465 a1467 a1469
  simp only [Atom.Holds] at a1471 a1473 a1475 a1477
  simp only [a1338, a1353, a1375, a1377, a1379, a1381, a1383, a1385, a1387, a1389, a1391, a1393,
    a1395, a1397, a1399, a1401, a1403, a1405, a1407, a1409, a1411, a1413, a1415, a1417, a1419,
    a1421, a1423, a1425, a1427, a1429, a1431, a1433, a1435, a1437, a1439, a1441, a1443, a1445,
    a1447, a1449, a1451, a1453, a1455, a1457, a1459, a1461, a1463, a1465, a1467, a1469, a1471,
    a1473, a1475, a1477]
  simp only [vtPushPadData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- **The pull side's total.** -/
theorem vt_pull_total {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 2489) = σ (.n 2483) + σ (.n 2437) + (1 + σ (.n 1436)) + σ (.n 2488) := by
  have a2530 := h.atomAt 2530 (.add (.n 2484) (.n 2483) (.n 2437)) (by decide +kernel)
  have a2531 := h.atomAt 2531 (.const (.n 2485) (word 1 0)) (by decide +kernel)
  have a2532 := h.atomAt 2532 (.add (.n 2486) (.n 2485) (.n 1436)) (by decide +kernel)
  have a2533 := h.atomAt 2533 (.add (.n 2487) (.n 2484) (.n 2486)) (by decide +kernel)
  have a2535 := h.atomAt 2535 (.add (.n 2489) (.n 2487) (.n 2488)) (by decide +kernel)
  simp only [Atom.Holds] at a2530 a2531 a2532 a2533 a2535
  rw [a2535, a2533, a2532, a2531, a2530, tb_word_one]

end
end LeanVM.Guest.B1.Tables
