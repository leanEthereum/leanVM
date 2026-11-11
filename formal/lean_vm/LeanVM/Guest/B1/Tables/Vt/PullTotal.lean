/-
  LeanVM.Guest.B1.Tables.Vt.PullTotal

  `verify_tables`' pull side total: its framework blocks' fingerprints (with the final memory and
  bytecode counts), the push side's padding sum, the selector sum and the GKR pull value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PushFw

/-!
# The pull side's total (G:2496-2555)

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
    σ (.n 2482) = σ (.n 1294) * (σ (.n 14) + (W 0 + W 1 * vtWFinalPc + W 2)) +
      σ (.n 1299) * (σ (.n 14) + (W 0 * gen + W 1 * σ (.n 1301) + W 2 * σ (.n 1305) +
        W 3 * σ (.n 1307) + W 4 * σ (.n 1309))) +
      σ (.n 1313) * (σ (.n 14) + (W 0 * gen ^ 2 + W 1 * σ (.n 1315) + W 2 * σ (.n 1319))) +
      σ (.n 1436) * σ (.n 1843) := by
  have a1335 := h.atomAt 1335 (.const (.n 1295) (word 1 0)) (by decide +kernel)
  have a1336 := h.atomAt 1336 (.const (.n 1296) (word 12261764870545049476 0)) (by decide +kernel)
  have a1337 := h.atomAt 1337 (.const (.n 1297) (word 1 0)) (by decide +kernel)
  have a1340 := h.atomAt 1340 (.const (.n 1300) (word 2 0)) (by decide +kernel)
  have a1355 := h.atomAt 1355 (.const (.n 1314) (word 4 0)) (by decide +kernel)
  have a2490 := h.atomAt 2490 (.load (.n 2443) (.n 13) 0) (by decide +kernel)
  have e2490 := tb_loadHolds_unique a2490 (hw 0 (by norm_num))
  have a2491 := h.atomAt 2491 (.mul (.n 2444) (.n 2443) (.n 1295)) (by decide +kernel)
  have a2492 := h.atomAt 2492 (.load (.n 2445) (.n 13) 1) (by decide +kernel)
  have e2492 := tb_loadHolds_unique a2492 (hw 1 (by norm_num))
  have a2493 := h.atomAt 2493 (.mul (.n 2446) (.n 2445) (.n 1296)) (by decide +kernel)
  have a2494 := h.atomAt 2494 (.add (.n 2447) (.n 2444) (.n 2446)) (by decide +kernel)
  have a2495 := h.atomAt 2495 (.load (.n 2448) (.n 13) 2) (by decide +kernel)
  have e2495 := tb_loadHolds_unique a2495 (hw 2 (by norm_num))
  have a2496 := h.atomAt 2496 (.mul (.n 2449) (.n 2448) (.n 1297)) (by decide +kernel)
  have a2497 := h.atomAt 2497 (.add (.n 2450) (.n 2447) (.n 2449)) (by decide +kernel)
  have a2498 := h.atomAt 2498 (.add (.n 2451) (.n 14) (.n 2450)) (by decide +kernel)
  have a2499 := h.atomAt 2499 (.mul (.n 2452) (.n 1294) (.n 2451)) (by decide +kernel)
  have a2500 := h.atomAt 2500 (.load (.n 2453) (.n 13) 0) (by decide +kernel)
  have e2500 := tb_loadHolds_unique a2500 (hw 0 (by norm_num))
  have a2501 := h.atomAt 2501 (.mul (.n 2454) (.n 2453) (.n 1300)) (by decide +kernel)
  have a2502 := h.atomAt 2502 (.load (.n 2455) (.n 13) 1) (by decide +kernel)
  have e2502 := tb_loadHolds_unique a2502 (hw 1 (by norm_num))
  have a2503 := h.atomAt 2503 (.mul (.n 2456) (.n 2455) (.n 1301)) (by decide +kernel)
  have a2504 := h.atomAt 2504 (.add (.n 2457) (.n 2454) (.n 2456)) (by decide +kernel)
  have a2505 := h.atomAt 2505 (.load (.n 2458) (.n 13) 2) (by decide +kernel)
  have e2505 := tb_loadHolds_unique a2505 (hw 2 (by norm_num))
  have a2506 := h.atomAt 2506 (.mul (.n 2459) (.n 2458) (.n 1305)) (by decide +kernel)
  have a2507 := h.atomAt 2507 (.add (.n 2460) (.n 2457) (.n 2459)) (by decide +kernel)
  have a2508 := h.atomAt 2508 (.load (.n 2461) (.n 13) 3) (by decide +kernel)
  have e2508 := tb_loadHolds_unique a2508 (hw 3 (by norm_num))
  have a2509 := h.atomAt 2509 (.mul (.n 2462) (.n 2461) (.n 1307)) (by decide +kernel)
  have a2510 := h.atomAt 2510 (.add (.n 2463) (.n 2460) (.n 2462)) (by decide +kernel)
  have a2511 := h.atomAt 2511 (.load (.n 2464) (.n 13) 4) (by decide +kernel)
  have e2511 := tb_loadHolds_unique a2511 (hw 4 (by norm_num))
  have a2512 := h.atomAt 2512 (.mul (.n 2465) (.n 2464) (.n 1309)) (by decide +kernel)
  have a2513 := h.atomAt 2513 (.add (.n 2466) (.n 2463) (.n 2465)) (by decide +kernel)
  have a2514 := h.atomAt 2514 (.add (.n 2467) (.n 14) (.n 2466)) (by decide +kernel)
  have a2515 := h.atomAt 2515 (.mul (.n 2468) (.n 1299) (.n 2467)) (by decide +kernel)
  have a2516 := h.atomAt 2516 (.add (.n 2469) (.n 2452) (.n 2468)) (by decide +kernel)
  have a2517 := h.atomAt 2517 (.load (.n 2470) (.n 13) 0) (by decide +kernel)
  have e2517 := tb_loadHolds_unique a2517 (hw 0 (by norm_num))
  have a2518 := h.atomAt 2518 (.mul (.n 2471) (.n 2470) (.n 1314)) (by decide +kernel)
  have a2519 := h.atomAt 2519 (.load (.n 2472) (.n 13) 1) (by decide +kernel)
  have e2519 := tb_loadHolds_unique a2519 (hw 1 (by norm_num))
  have a2520 := h.atomAt 2520 (.mul (.n 2473) (.n 2472) (.n 1315)) (by decide +kernel)
  have a2521 := h.atomAt 2521 (.add (.n 2474) (.n 2471) (.n 2473)) (by decide +kernel)
  have a2522 := h.atomAt 2522 (.load (.n 2475) (.n 13) 2) (by decide +kernel)
  have e2522 := tb_loadHolds_unique a2522 (hw 2 (by norm_num))
  have a2523 := h.atomAt 2523 (.mul (.n 2476) (.n 2475) (.n 1319)) (by decide +kernel)
  have a2524 := h.atomAt 2524 (.add (.n 2477) (.n 2474) (.n 2476)) (by decide +kernel)
  have a2525 := h.atomAt 2525 (.add (.n 2478) (.n 14) (.n 2477)) (by decide +kernel)
  have a2526 := h.atomAt 2526 (.mul (.n 2479) (.n 1313) (.n 2478)) (by decide +kernel)
  have a2527 := h.atomAt 2527 (.add (.n 2480) (.n 2469) (.n 2479)) (by decide +kernel)
  have a2528 := h.atomAt 2528 (.mul (.n 2481) (.n 1436) (.n 1843)) (by decide +kernel)
  have a2529 := h.atomAt 2529 (.add (.n 2482) (.n 2480) (.n 2481)) (by decide +kernel)
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
    σ (.n 1435) = σ (.n 790) + σ (.n 807) + σ (.n 835) +
      (vtPushPadData.map fun x ↦ σ (.n x.2.2.1)).sum := by
  have a1338 := h.atomAt 1338 (.add (.n 1298) (.n 790) (.n 807)) (by decide +kernel)
  have a1353 := h.atomAt 1353 (.add (.n 1312) (.n 1298) (.n 835)) (by decide +kernel)
  have a1375 := h.atomAt 1375 (.add (.n 1333) (.n 1312) (.n 857)) (by decide +kernel)
  have a1377 := h.atomAt 1377 (.add (.n 1335) (.n 1333) (.n 862)) (by decide +kernel)
  have a1379 := h.atomAt 1379 (.add (.n 1337) (.n 1335) (.n 867)) (by decide +kernel)
  have a1381 := h.atomAt 1381 (.add (.n 1339) (.n 1337) (.n 872)) (by decide +kernel)
  have a1383 := h.atomAt 1383 (.add (.n 1341) (.n 1339) (.n 877)) (by decide +kernel)
  have a1385 := h.atomAt 1385 (.add (.n 1343) (.n 1341) (.n 886)) (by decide +kernel)
  have a1387 := h.atomAt 1387 (.add (.n 1345) (.n 1343) (.n 895)) (by decide +kernel)
  have a1389 := h.atomAt 1389 (.add (.n 1347) (.n 1345) (.n 904)) (by decide +kernel)
  have a1391 := h.atomAt 1391 (.add (.n 1349) (.n 1347) (.n 913)) (by decide +kernel)
  have a1393 := h.atomAt 1393 (.add (.n 1351) (.n 1349) (.n 922)) (by decide +kernel)
  have a1395 := h.atomAt 1395 (.add (.n 1353) (.n 1351) (.n 931)) (by decide +kernel)
  have a1397 := h.atomAt 1397 (.add (.n 1355) (.n 1353) (.n 940)) (by decide +kernel)
  have a1399 := h.atomAt 1399 (.add (.n 1357) (.n 1355) (.n 949)) (by decide +kernel)
  have a1401 := h.atomAt 1401 (.add (.n 1359) (.n 1357) (.n 958)) (by decide +kernel)
  have a1403 := h.atomAt 1403 (.add (.n 1361) (.n 1359) (.n 967)) (by decide +kernel)
  have a1405 := h.atomAt 1405 (.add (.n 1363) (.n 1361) (.n 976)) (by decide +kernel)
  have a1407 := h.atomAt 1407 (.add (.n 1365) (.n 1363) (.n 985)) (by decide +kernel)
  have a1409 := h.atomAt 1409 (.add (.n 1367) (.n 1365) (.n 994)) (by decide +kernel)
  have a1411 := h.atomAt 1411 (.add (.n 1369) (.n 1367) (.n 1003)) (by decide +kernel)
  have a1413 := h.atomAt 1413 (.add (.n 1371) (.n 1369) (.n 1012)) (by decide +kernel)
  have a1415 := h.atomAt 1415 (.add (.n 1373) (.n 1371) (.n 1021)) (by decide +kernel)
  have a1417 := h.atomAt 1417 (.add (.n 1375) (.n 1373) (.n 1030)) (by decide +kernel)
  have a1419 := h.atomAt 1419 (.add (.n 1377) (.n 1375) (.n 1039)) (by decide +kernel)
  have a1421 := h.atomAt 1421 (.add (.n 1379) (.n 1377) (.n 1048)) (by decide +kernel)
  have a1423 := h.atomAt 1423 (.add (.n 1381) (.n 1379) (.n 1057)) (by decide +kernel)
  have a1425 := h.atomAt 1425 (.add (.n 1383) (.n 1381) (.n 1066)) (by decide +kernel)
  have a1427 := h.atomAt 1427 (.add (.n 1385) (.n 1383) (.n 1075)) (by decide +kernel)
  have a1429 := h.atomAt 1429 (.add (.n 1387) (.n 1385) (.n 1084)) (by decide +kernel)
  have a1431 := h.atomAt 1431 (.add (.n 1389) (.n 1387) (.n 1093)) (by decide +kernel)
  have a1433 := h.atomAt 1433 (.add (.n 1391) (.n 1389) (.n 1102)) (by decide +kernel)
  have a1435 := h.atomAt 1435 (.add (.n 1393) (.n 1391) (.n 1111)) (by decide +kernel)
  have a1437 := h.atomAt 1437 (.add (.n 1395) (.n 1393) (.n 1120)) (by decide +kernel)
  have a1439 := h.atomAt 1439 (.add (.n 1397) (.n 1395) (.n 1129)) (by decide +kernel)
  have a1441 := h.atomAt 1441 (.add (.n 1399) (.n 1397) (.n 1138)) (by decide +kernel)
  have a1443 := h.atomAt 1443 (.add (.n 1401) (.n 1399) (.n 1147)) (by decide +kernel)
  have a1445 := h.atomAt 1445 (.add (.n 1403) (.n 1401) (.n 1156)) (by decide +kernel)
  have a1447 := h.atomAt 1447 (.add (.n 1405) (.n 1403) (.n 1165)) (by decide +kernel)
  have a1449 := h.atomAt 1449 (.add (.n 1407) (.n 1405) (.n 1174)) (by decide +kernel)
  have a1451 := h.atomAt 1451 (.add (.n 1409) (.n 1407) (.n 1183)) (by decide +kernel)
  have a1453 := h.atomAt 1453 (.add (.n 1411) (.n 1409) (.n 1192)) (by decide +kernel)
  have a1455 := h.atomAt 1455 (.add (.n 1413) (.n 1411) (.n 1201)) (by decide +kernel)
  have a1457 := h.atomAt 1457 (.add (.n 1415) (.n 1413) (.n 1210)) (by decide +kernel)
  have a1459 := h.atomAt 1459 (.add (.n 1417) (.n 1415) (.n 1219)) (by decide +kernel)
  have a1461 := h.atomAt 1461 (.add (.n 1419) (.n 1417) (.n 1228)) (by decide +kernel)
  have a1463 := h.atomAt 1463 (.add (.n 1421) (.n 1419) (.n 1237)) (by decide +kernel)
  have a1465 := h.atomAt 1465 (.add (.n 1423) (.n 1421) (.n 1246)) (by decide +kernel)
  have a1467 := h.atomAt 1467 (.add (.n 1425) (.n 1423) (.n 1255)) (by decide +kernel)
  have a1469 := h.atomAt 1469 (.add (.n 1427) (.n 1425) (.n 1264)) (by decide +kernel)
  have a1471 := h.atomAt 1471 (.add (.n 1429) (.n 1427) (.n 1273)) (by decide +kernel)
  have a1473 := h.atomAt 1473 (.add (.n 1431) (.n 1429) (.n 1282)) (by decide +kernel)
  have a1475 := h.atomAt 1475 (.add (.n 1433) (.n 1431) (.n 1291)) (by decide +kernel)
  have a1477 := h.atomAt 1477 (.copy (.n 1435) (.n 1433)) (by decide +kernel)
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
    σ (.n 2488) = σ (.n 2482) + σ (.n 2436) + (1 + σ (.n 1435)) + σ (.n 2487) := by
  have a2530 := h.atomAt 2530 (.add (.n 2483) (.n 2482) (.n 2436)) (by decide +kernel)
  have a2531 := h.atomAt 2531 (.const (.n 2484) (word 1 0)) (by decide +kernel)
  have a2532 := h.atomAt 2532 (.add (.n 2485) (.n 2484) (.n 1435)) (by decide +kernel)
  have a2533 := h.atomAt 2533 (.add (.n 2486) (.n 2483) (.n 2485)) (by decide +kernel)
  have a2535 := h.atomAt 2535 (.add (.n 2488) (.n 2486) (.n 2487)) (by decide +kernel)
  simp only [Atom.Holds] at a2530 a2531 a2532 a2533 a2535
  rw [a2535, a2533, a2532, a2531, a2530, tb_word_one]

end
end LeanVM.Guest.B1.Tables
