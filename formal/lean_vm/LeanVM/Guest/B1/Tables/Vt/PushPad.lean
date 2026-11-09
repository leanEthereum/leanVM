/-
  LeanVM.Guest.B1.Tables.Vt.PushPad

  `verify_tables`' push side total: the framework decomposition's accumulator, the padding sum
  over the tables' blocks, the selector sum and the GKR leaf value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SelFw

/-!
# The push side's padding and total (G:2316-2348)

`vtPushPadData` lists the push side's table blocks with their table, the value of their eq weight's
copy (`block_eq_hi[b]`) and their nonzero `COORD_PADDING` terms (slot, value). `vt_push_total`:
`bus_table_total[PUSH]` is the framework accumulator, plus `Σ_t pad_weight[t]·Σ_b eq_b·(β + 1 +
Σ w_i·pad_i)`, plus `1 + selector_sum`, plus the GKR push leaf value.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- A table's part of a side's padding sum: its blocks' eq weights (by their copies' values)
times `β + 1 + Σ w_i·pad_i` (`β1` the side's `β + 1`). -/
def vtPadTable (eqc W : ℕ → E) (β1 : E) (data : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) (t : ℕ) : E :=
  ((data.filter fun x ↦ x.2.1 = t).map fun x ↦
    eqc x.2.2.1 * (β1 + (x.2.2.2.map fun ic ↦ W ic.1 * word ic.2 0 0).sum)).sum

/-- A side's padding sum: per table, its padding weight times its part. -/
def vtPadSum (eqc pw W : ℕ → E) (β1 : E) (data : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) : E :=
  pw 0 * vtPadTable eqc W β1 data 0 + pw 1 * vtPadTable eqc W β1 data 1 +
    pw 2 * vtPadTable eqc W β1 data 2 + pw 3 * vtPadTable eqc W β1 data 3 +
    pw 4 * vtPadTable eqc W β1 data 4 + pw 5 * vtPadTable eqc W β1 data 5

/-- The push side's table blocks: block, table, copy value, padding terms. -/
def vtPushPadData : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=
  [(3, 0, 960, [(0, 1)]), (4, 0, 965, [(0, 4), (3, 1)]), (5, 0, 970, [(0, 2)]),
    (6, 0, 975, [(0, 2)]), (7, 0, 980, [(0, 2)]), (8, 1, 989, [(0, 1)]),
    (9, 1, 998, [(0, 4), (3, 2)]), (10, 1, 1007, [(0, 2)]), (11, 1, 1016, [(0, 2)]),
    (12, 1, 1025, [(0, 2)]), (13, 2, 1034, [(0, 1)]), (14, 2, 1043, [(0, 4), (3, 4)]),
    (15, 2, 1052, [(0, 2)]), (16, 3, 1061, [(0, 1)]), (17, 3, 1070, [(0, 4), (3, 8)]),
    (18, 3, 1079, [(0, 2)]), (19, 3, 1088, [(0, 2)]), (20, 3, 1097, [(0, 2)]),
    (21, 4, 1106, [(0, 1)]), (22, 4, 1115, [(0, 4), (3, 16)]), (23, 4, 1124, [(0, 2)]),
    (24, 4, 1133, [(0, 2)]), (25, 4, 1142, [(0, 2)]), (26, 5, 1151, [(0, 1)]),
    (27, 5, 1160, [(0, 4), (3, 32)]), (28, 5, 1169, [(0, 2)]), (29, 5, 1178, [(0, 2)]),
    (30, 5, 1187, [(0, 2)]), (31, 5, 1196, [(0, 2)]), (32, 5, 1205, [(0, 2)]),
    (33, 5, 1214, [(0, 2)]), (34, 5, 1223, [(0, 2)]), (35, 5, 1232, [(0, 2)]),
    (36, 5, 1241, [(0, 2)]), (37, 5, 1250, [(0, 2)]), (38, 5, 1259, [(0, 2)]),
    (39, 5, 1268, [(0, 2)]), (40, 5, 1277, [(0, 2)]),
    (41, 5, 1286, [(0, 2), (3, 17376452488221285863), (4, 9571781953733019530)]),
    (42, 5, 1295, [(0, 2), (3, 15391093639620504046), (4, 13624874521033984333)]),
    (43, 5, 1304, [(0, 2), (3, 10027350355371872343), (4, 18417369716475457492)]),
    (44, 5, 1313, [(0, 2), (3, 10448040663659726788), (4, 10113917136857017974)]),
    (45, 5, 1322, [(0, 2), (3, 12479658147685402012), (4, 3500241080921619556)]),
    (46, 5, 1331, [(0, 2), (3, 16959053435453822517), (4, 12224711289652453635)]),
    (47, 5, 1340, [(0, 2), (3, 9342009439668884831), (4, 4879704952849025062)]),
    (48, 5, 1349, [(0, 2), (3, 140226327413610143), (4, 424854978622500449)]),
    (49, 5, 1358, [(0, 2), (3, 7259519967065370866)]),
    (50, 5, 1367, [(0, 2), (3, 7004910057750291985), (4, 13293599522548616907)]),
    (51, 5, 1376, [(0, 2), (3, 10105770293752443592), (4, 10668034807192757780)]),
    (52, 5, 1385, [(0, 2), (3, 1747952066141424100), (4, 1654286879329379778)]),
    (53, 5, 1394, [(0, 2), (3, 8500057116360352059), (4, 16929593379567477321)])]

set_option maxRecDepth 100000 in
/-- **The push side's total.** -/
theorem vt_push_total {rd : Reader} {σ : Val} (h : VtH rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 1820) = σ (.n 955) + vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W
      (σ (.n 783)) vtPushPadData + (1 + σ (.n 1393)) + σ (.n 25) := by
  have a3484 := h.atomAt 1433 (.load (.n 1395) (.n 13) 0) (by decide +kernel)
  have a3485 := h.atomAt 1434 (.add (.n 1396) (.n 783) (.n 1395)) (by decide +kernel)
  have a3486 := h.atomAt 1435 (.mul (.n 1397) (.n 960) (.n 1396)) (by decide +kernel)
  have a3487 := h.atomAt 1436 (.load (.n 1398) (.n 13) 0) (by decide +kernel)
  have a3488 := h.atomAt 1437 (.const (.n 1399) (word 4 0 0)) (by decide +kernel)
  have a3489 := h.atomAt 1438 (.mul (.n 1400) (.n 1398) (.n 1399)) (by decide +kernel)
  have a3490 := h.atomAt 1439 (.add (.n 1401) (.n 783) (.n 1400)) (by decide +kernel)
  have a3491 := h.atomAt 1440 (.load (.n 1402) (.n 13) 3) (by decide +kernel)
  have a3492 := h.atomAt 1441 (.add (.n 1403) (.n 1401) (.n 1402)) (by decide +kernel)
  have a3493 := h.atomAt 1442 (.mul (.n 1404) (.n 965) (.n 1403)) (by decide +kernel)
  have a3494 := h.atomAt 1443 (.add (.n 1405) (.n 1397) (.n 1404)) (by decide +kernel)
  have a3495 := h.atomAt 1444 (.load (.n 1406) (.n 13) 0) (by decide +kernel)
  have a3496 := h.atomAt 1445 (.const (.n 1407) (word 2 0 0)) (by decide +kernel)
  have a3497 := h.atomAt 1446 (.mul (.n 1408) (.n 1406) (.n 1407)) (by decide +kernel)
  have a3498 := h.atomAt 1447 (.add (.n 1409) (.n 783) (.n 1408)) (by decide +kernel)
  have a3499 := h.atomAt 1448 (.mul (.n 1410) (.n 970) (.n 1409)) (by decide +kernel)
  have a3500 := h.atomAt 1449 (.add (.n 1411) (.n 1405) (.n 1410)) (by decide +kernel)
  have a3501 := h.atomAt 1450 (.load (.n 1412) (.n 13) 0) (by decide +kernel)
  have a3502 := h.atomAt 1451 (.const (.n 1413) (word 2 0 0)) (by decide +kernel)
  have a3503 := h.atomAt 1452 (.mul (.n 1414) (.n 1412) (.n 1413)) (by decide +kernel)
  have a3504 := h.atomAt 1453 (.add (.n 1415) (.n 783) (.n 1414)) (by decide +kernel)
  have a3505 := h.atomAt 1454 (.mul (.n 1416) (.n 975) (.n 1415)) (by decide +kernel)
  have a3506 := h.atomAt 1455 (.add (.n 1417) (.n 1411) (.n 1416)) (by decide +kernel)
  have a3507 := h.atomAt 1456 (.load (.n 1418) (.n 13) 0) (by decide +kernel)
  have a3508 := h.atomAt 1457 (.const (.n 1419) (word 2 0 0)) (by decide +kernel)
  have a3509 := h.atomAt 1458 (.mul (.n 1420) (.n 1418) (.n 1419)) (by decide +kernel)
  have a3510 := h.atomAt 1459 (.add (.n 1421) (.n 783) (.n 1420)) (by decide +kernel)
  have a3511 := h.atomAt 1460 (.mul (.n 1422) (.n 980) (.n 1421)) (by decide +kernel)
  have a3512 := h.atomAt 1461 (.add (.n 1423) (.n 1417) (.n 1422)) (by decide +kernel)
  have a3513 := h.atomAt 1462 (.mul (.n 1424) (.n 587) (.n 1423)) (by decide +kernel)
  have a3514 := h.atomAt 1463 (.load (.n 1425) (.n 13) 0) (by decide +kernel)
  have a3515 := h.atomAt 1464 (.add (.n 1426) (.n 783) (.n 1425)) (by decide +kernel)
  have a3516 := h.atomAt 1465 (.mul (.n 1427) (.n 989) (.n 1426)) (by decide +kernel)
  have a3517 := h.atomAt 1466 (.load (.n 1428) (.n 13) 0) (by decide +kernel)
  have a3518 := h.atomAt 1467 (.const (.n 1429) (word 4 0 0)) (by decide +kernel)
  have a3519 := h.atomAt 1468 (.mul (.n 1430) (.n 1428) (.n 1429)) (by decide +kernel)
  have a3520 := h.atomAt 1469 (.add (.n 1431) (.n 783) (.n 1430)) (by decide +kernel)
  have a3521 := h.atomAt 1470 (.load (.n 1432) (.n 13) 3) (by decide +kernel)
  have a3522 := h.atomAt 1471 (.const (.n 1433) (word 2 0 0)) (by decide +kernel)
  have a3523 := h.atomAt 1472 (.mul (.n 1434) (.n 1432) (.n 1433)) (by decide +kernel)
  have a3524 := h.atomAt 1473 (.add (.n 1435) (.n 1431) (.n 1434)) (by decide +kernel)
  have a3525 := h.atomAt 1474 (.mul (.n 1436) (.n 998) (.n 1435)) (by decide +kernel)
  have a3526 := h.atomAt 1475 (.add (.n 1437) (.n 1427) (.n 1436)) (by decide +kernel)
  have a3527 := h.atomAt 1476 (.load (.n 1438) (.n 13) 0) (by decide +kernel)
  have a3528 := h.atomAt 1477 (.const (.n 1439) (word 2 0 0)) (by decide +kernel)
  have a3529 := h.atomAt 1478 (.mul (.n 1440) (.n 1438) (.n 1439)) (by decide +kernel)
  have a3530 := h.atomAt 1479 (.add (.n 1441) (.n 783) (.n 1440)) (by decide +kernel)
  have a3531 := h.atomAt 1480 (.mul (.n 1442) (.n 1007) (.n 1441)) (by decide +kernel)
  have a3532 := h.atomAt 1481 (.add (.n 1443) (.n 1437) (.n 1442)) (by decide +kernel)
  have a3533 := h.atomAt 1482 (.load (.n 1444) (.n 13) 0) (by decide +kernel)
  have a3534 := h.atomAt 1483 (.const (.n 1445) (word 2 0 0)) (by decide +kernel)
  have a3535 := h.atomAt 1484 (.mul (.n 1446) (.n 1444) (.n 1445)) (by decide +kernel)
  have a3536 := h.atomAt 1485 (.add (.n 1447) (.n 783) (.n 1446)) (by decide +kernel)
  have a3537 := h.atomAt 1486 (.mul (.n 1448) (.n 1016) (.n 1447)) (by decide +kernel)
  have a3538 := h.atomAt 1487 (.add (.n 1449) (.n 1443) (.n 1448)) (by decide +kernel)
  have a3539 := h.atomAt 1488 (.load (.n 1450) (.n 13) 0) (by decide +kernel)
  have a3540 := h.atomAt 1489 (.const (.n 1451) (word 2 0 0)) (by decide +kernel)
  have a3541 := h.atomAt 1490 (.mul (.n 1452) (.n 1450) (.n 1451)) (by decide +kernel)
  have a3542 := h.atomAt 1491 (.add (.n 1453) (.n 783) (.n 1452)) (by decide +kernel)
  have a3543 := h.atomAt 1492 (.mul (.n 1454) (.n 1025) (.n 1453)) (by decide +kernel)
  have a3544 := h.atomAt 1493 (.add (.n 1455) (.n 1449) (.n 1454)) (by decide +kernel)
  have a3545 := h.atomAt 1494 (.mul (.n 1456) (.n 600) (.n 1455)) (by decide +kernel)
  have a3546 := h.atomAt 1495 (.add (.n 1457) (.n 1424) (.n 1456)) (by decide +kernel)
  have a3547 := h.atomAt 1496 (.load (.n 1458) (.n 13) 0) (by decide +kernel)
  have a3548 := h.atomAt 1497 (.add (.n 1459) (.n 783) (.n 1458)) (by decide +kernel)
  have a3549 := h.atomAt 1498 (.mul (.n 1460) (.n 1034) (.n 1459)) (by decide +kernel)
  have a3550 := h.atomAt 1499 (.load (.n 1461) (.n 13) 0) (by decide +kernel)
  have a3551 := h.atomAt 1500 (.const (.n 1462) (word 4 0 0)) (by decide +kernel)
  have a3552 := h.atomAt 1501 (.mul (.n 1463) (.n 1461) (.n 1462)) (by decide +kernel)
  have a3553 := h.atomAt 1502 (.add (.n 1464) (.n 783) (.n 1463)) (by decide +kernel)
  have a3554 := h.atomAt 1503 (.load (.n 1465) (.n 13) 3) (by decide +kernel)
  have a3555 := h.atomAt 1504 (.const (.n 1466) (word 4 0 0)) (by decide +kernel)
  have a3556 := h.atomAt 1505 (.mul (.n 1467) (.n 1465) (.n 1466)) (by decide +kernel)
  have a3557 := h.atomAt 1506 (.add (.n 1468) (.n 1464) (.n 1467)) (by decide +kernel)
  have a3558 := h.atomAt 1507 (.mul (.n 1469) (.n 1043) (.n 1468)) (by decide +kernel)
  have a3559 := h.atomAt 1508 (.add (.n 1470) (.n 1460) (.n 1469)) (by decide +kernel)
  have a3560 := h.atomAt 1509 (.load (.n 1471) (.n 13) 0) (by decide +kernel)
  have a3561 := h.atomAt 1510 (.const (.n 1472) (word 2 0 0)) (by decide +kernel)
  have a3562 := h.atomAt 1511 (.mul (.n 1473) (.n 1471) (.n 1472)) (by decide +kernel)
  have a3563 := h.atomAt 1512 (.add (.n 1474) (.n 783) (.n 1473)) (by decide +kernel)
  have a3564 := h.atomAt 1513 (.mul (.n 1475) (.n 1052) (.n 1474)) (by decide +kernel)
  have a3565 := h.atomAt 1514 (.add (.n 1476) (.n 1470) (.n 1475)) (by decide +kernel)
  have a3566 := h.atomAt 1515 (.mul (.n 1477) (.n 613) (.n 1476)) (by decide +kernel)
  have a3567 := h.atomAt 1516 (.add (.n 1478) (.n 1457) (.n 1477)) (by decide +kernel)
  have a3568 := h.atomAt 1517 (.load (.n 1479) (.n 13) 0) (by decide +kernel)
  have a3569 := h.atomAt 1518 (.add (.n 1480) (.n 783) (.n 1479)) (by decide +kernel)
  have a3570 := h.atomAt 1519 (.mul (.n 1481) (.n 1061) (.n 1480)) (by decide +kernel)
  have a3571 := h.atomAt 1520 (.load (.n 1482) (.n 13) 0) (by decide +kernel)
  have a3572 := h.atomAt 1521 (.const (.n 1483) (word 4 0 0)) (by decide +kernel)
  have a3573 := h.atomAt 1522 (.mul (.n 1484) (.n 1482) (.n 1483)) (by decide +kernel)
  have a3574 := h.atomAt 1523 (.add (.n 1485) (.n 783) (.n 1484)) (by decide +kernel)
  have a3575 := h.atomAt 1524 (.load (.n 1486) (.n 13) 3) (by decide +kernel)
  have a3576 := h.atomAt 1525 (.const (.n 1487) (word 8 0 0)) (by decide +kernel)
  have a3577 := h.atomAt 1526 (.mul (.n 1488) (.n 1486) (.n 1487)) (by decide +kernel)
  have a3578 := h.atomAt 1527 (.add (.n 1489) (.n 1485) (.n 1488)) (by decide +kernel)
  have a3579 := h.atomAt 1528 (.mul (.n 1490) (.n 1070) (.n 1489)) (by decide +kernel)
  have a3580 := h.atomAt 1529 (.add (.n 1491) (.n 1481) (.n 1490)) (by decide +kernel)
  have a3581 := h.atomAt 1530 (.load (.n 1492) (.n 13) 0) (by decide +kernel)
  have a3582 := h.atomAt 1531 (.const (.n 1493) (word 2 0 0)) (by decide +kernel)
  have a3583 := h.atomAt 1532 (.mul (.n 1494) (.n 1492) (.n 1493)) (by decide +kernel)
  have a3584 := h.atomAt 1533 (.add (.n 1495) (.n 783) (.n 1494)) (by decide +kernel)
  have a3585 := h.atomAt 1534 (.mul (.n 1496) (.n 1079) (.n 1495)) (by decide +kernel)
  have a3586 := h.atomAt 1535 (.add (.n 1497) (.n 1491) (.n 1496)) (by decide +kernel)
  have a3587 := h.atomAt 1536 (.load (.n 1498) (.n 13) 0) (by decide +kernel)
  have a3588 := h.atomAt 1537 (.const (.n 1499) (word 2 0 0)) (by decide +kernel)
  have a3589 := h.atomAt 1538 (.mul (.n 1500) (.n 1498) (.n 1499)) (by decide +kernel)
  have a3590 := h.atomAt 1539 (.add (.n 1501) (.n 783) (.n 1500)) (by decide +kernel)
  have a3591 := h.atomAt 1540 (.mul (.n 1502) (.n 1088) (.n 1501)) (by decide +kernel)
  have a3592 := h.atomAt 1541 (.add (.n 1503) (.n 1497) (.n 1502)) (by decide +kernel)
  have a3593 := h.atomAt 1542 (.load (.n 1504) (.n 13) 0) (by decide +kernel)
  have a3594 := h.atomAt 1543 (.const (.n 1505) (word 2 0 0)) (by decide +kernel)
  have a3595 := h.atomAt 1544 (.mul (.n 1506) (.n 1504) (.n 1505)) (by decide +kernel)
  have a3596 := h.atomAt 1545 (.add (.n 1507) (.n 783) (.n 1506)) (by decide +kernel)
  have a3597 := h.atomAt 1546 (.mul (.n 1508) (.n 1097) (.n 1507)) (by decide +kernel)
  have a3598 := h.atomAt 1547 (.add (.n 1509) (.n 1503) (.n 1508)) (by decide +kernel)
  have a3599 := h.atomAt 1548 (.mul (.n 1510) (.n 626) (.n 1509)) (by decide +kernel)
  have a3600 := h.atomAt 1549 (.add (.n 1511) (.n 1478) (.n 1510)) (by decide +kernel)
  have a3601 := h.atomAt 1550 (.load (.n 1512) (.n 13) 0) (by decide +kernel)
  have a3602 := h.atomAt 1551 (.add (.n 1513) (.n 783) (.n 1512)) (by decide +kernel)
  have a3603 := h.atomAt 1552 (.mul (.n 1514) (.n 1106) (.n 1513)) (by decide +kernel)
  have a3604 := h.atomAt 1553 (.load (.n 1515) (.n 13) 0) (by decide +kernel)
  have a3605 := h.atomAt 1554 (.const (.n 1516) (word 4 0 0)) (by decide +kernel)
  have a3606 := h.atomAt 1555 (.mul (.n 1517) (.n 1515) (.n 1516)) (by decide +kernel)
  have a3607 := h.atomAt 1556 (.add (.n 1518) (.n 783) (.n 1517)) (by decide +kernel)
  have a3608 := h.atomAt 1557 (.load (.n 1519) (.n 13) 3) (by decide +kernel)
  have a3609 := h.atomAt 1558 (.const (.n 1520) (word 16 0 0)) (by decide +kernel)
  have a3610 := h.atomAt 1559 (.mul (.n 1521) (.n 1519) (.n 1520)) (by decide +kernel)
  have a3611 := h.atomAt 1560 (.add (.n 1522) (.n 1518) (.n 1521)) (by decide +kernel)
  have a3612 := h.atomAt 1561 (.mul (.n 1523) (.n 1115) (.n 1522)) (by decide +kernel)
  have a3613 := h.atomAt 1562 (.add (.n 1524) (.n 1514) (.n 1523)) (by decide +kernel)
  have a3614 := h.atomAt 1563 (.load (.n 1525) (.n 13) 0) (by decide +kernel)
  have a3615 := h.atomAt 1564 (.const (.n 1526) (word 2 0 0)) (by decide +kernel)
  have a3616 := h.atomAt 1565 (.mul (.n 1527) (.n 1525) (.n 1526)) (by decide +kernel)
  have a3617 := h.atomAt 1566 (.add (.n 1528) (.n 783) (.n 1527)) (by decide +kernel)
  have a3618 := h.atomAt 1567 (.mul (.n 1529) (.n 1124) (.n 1528)) (by decide +kernel)
  have a3619 := h.atomAt 1568 (.add (.n 1530) (.n 1524) (.n 1529)) (by decide +kernel)
  have a3620 := h.atomAt 1569 (.load (.n 1531) (.n 13) 0) (by decide +kernel)
  have a3621 := h.atomAt 1570 (.const (.n 1532) (word 2 0 0)) (by decide +kernel)
  have a3622 := h.atomAt 1571 (.mul (.n 1533) (.n 1531) (.n 1532)) (by decide +kernel)
  have a3623 := h.atomAt 1572 (.add (.n 1534) (.n 783) (.n 1533)) (by decide +kernel)
  have a3624 := h.atomAt 1573 (.mul (.n 1535) (.n 1133) (.n 1534)) (by decide +kernel)
  have a3625 := h.atomAt 1574 (.add (.n 1536) (.n 1530) (.n 1535)) (by decide +kernel)
  have a3626 := h.atomAt 1575 (.load (.n 1537) (.n 13) 0) (by decide +kernel)
  have a3627 := h.atomAt 1576 (.const (.n 1538) (word 2 0 0)) (by decide +kernel)
  have a3628 := h.atomAt 1577 (.mul (.n 1539) (.n 1537) (.n 1538)) (by decide +kernel)
  have a3629 := h.atomAt 1578 (.add (.n 1540) (.n 783) (.n 1539)) (by decide +kernel)
  have a3630 := h.atomAt 1579 (.mul (.n 1541) (.n 1142) (.n 1540)) (by decide +kernel)
  have a3631 := h.atomAt 1580 (.add (.n 1542) (.n 1536) (.n 1541)) (by decide +kernel)
  have a3632 := h.atomAt 1581 (.mul (.n 1543) (.n 639) (.n 1542)) (by decide +kernel)
  have a3633 := h.atomAt 1582 (.add (.n 1544) (.n 1511) (.n 1543)) (by decide +kernel)
  have a3634 := h.atomAt 1583 (.load (.n 1545) (.n 13) 0) (by decide +kernel)
  have a3635 := h.atomAt 1584 (.add (.n 1546) (.n 783) (.n 1545)) (by decide +kernel)
  have a3636 := h.atomAt 1585 (.mul (.n 1547) (.n 1151) (.n 1546)) (by decide +kernel)
  have a3637 := h.atomAt 1586 (.load (.n 1548) (.n 13) 0) (by decide +kernel)
  have a3638 := h.atomAt 1587 (.const (.n 1549) (word 4 0 0)) (by decide +kernel)
  have a3639 := h.atomAt 1588 (.mul (.n 1550) (.n 1548) (.n 1549)) (by decide +kernel)
  have a3640 := h.atomAt 1589 (.add (.n 1551) (.n 783) (.n 1550)) (by decide +kernel)
  have a3641 := h.atomAt 1590 (.load (.n 1552) (.n 13) 3) (by decide +kernel)
  have a3642 := h.atomAt 1591 (.const (.n 1553) (word 32 0 0)) (by decide +kernel)
  have a3643 := h.atomAt 1592 (.mul (.n 1554) (.n 1552) (.n 1553)) (by decide +kernel)
  have a3644 := h.atomAt 1593 (.add (.n 1555) (.n 1551) (.n 1554)) (by decide +kernel)
  have a3645 := h.atomAt 1594 (.mul (.n 1556) (.n 1160) (.n 1555)) (by decide +kernel)
  have a3646 := h.atomAt 1595 (.add (.n 1557) (.n 1547) (.n 1556)) (by decide +kernel)
  have a3647 := h.atomAt 1596 (.load (.n 1558) (.n 13) 0) (by decide +kernel)
  have a3648 := h.atomAt 1597 (.const (.n 1559) (word 2 0 0)) (by decide +kernel)
  have a3649 := h.atomAt 1598 (.mul (.n 1560) (.n 1558) (.n 1559)) (by decide +kernel)
  have a3650 := h.atomAt 1599 (.add (.n 1561) (.n 783) (.n 1560)) (by decide +kernel)
  have a3651 := h.atomAt 1600 (.mul (.n 1562) (.n 1169) (.n 1561)) (by decide +kernel)
  have a3652 := h.atomAt 1601 (.add (.n 1563) (.n 1557) (.n 1562)) (by decide +kernel)
  have a3653 := h.atomAt 1602 (.load (.n 1564) (.n 13) 0) (by decide +kernel)
  have a3654 := h.atomAt 1603 (.const (.n 1565) (word 2 0 0)) (by decide +kernel)
  have a3655 := h.atomAt 1604 (.mul (.n 1566) (.n 1564) (.n 1565)) (by decide +kernel)
  have a3656 := h.atomAt 1605 (.add (.n 1567) (.n 783) (.n 1566)) (by decide +kernel)
  have a3657 := h.atomAt 1606 (.mul (.n 1568) (.n 1178) (.n 1567)) (by decide +kernel)
  have a3658 := h.atomAt 1607 (.add (.n 1569) (.n 1563) (.n 1568)) (by decide +kernel)
  have a3659 := h.atomAt 1608 (.load (.n 1570) (.n 13) 0) (by decide +kernel)
  have a3660 := h.atomAt 1609 (.const (.n 1571) (word 2 0 0)) (by decide +kernel)
  have a3661 := h.atomAt 1610 (.mul (.n 1572) (.n 1570) (.n 1571)) (by decide +kernel)
  have a3662 := h.atomAt 1611 (.add (.n 1573) (.n 783) (.n 1572)) (by decide +kernel)
  have a3663 := h.atomAt 1612 (.mul (.n 1574) (.n 1187) (.n 1573)) (by decide +kernel)
  have a3664 := h.atomAt 1613 (.add (.n 1575) (.n 1569) (.n 1574)) (by decide +kernel)
  have a3665 := h.atomAt 1614 (.load (.n 1576) (.n 13) 0) (by decide +kernel)
  have a3666 := h.atomAt 1615 (.const (.n 1577) (word 2 0 0)) (by decide +kernel)
  have a3667 := h.atomAt 1616 (.mul (.n 1578) (.n 1576) (.n 1577)) (by decide +kernel)
  have a3668 := h.atomAt 1617 (.add (.n 1579) (.n 783) (.n 1578)) (by decide +kernel)
  have a3669 := h.atomAt 1618 (.mul (.n 1580) (.n 1196) (.n 1579)) (by decide +kernel)
  have a3670 := h.atomAt 1619 (.add (.n 1581) (.n 1575) (.n 1580)) (by decide +kernel)
  have a3671 := h.atomAt 1620 (.load (.n 1582) (.n 13) 0) (by decide +kernel)
  have a3672 := h.atomAt 1621 (.const (.n 1583) (word 2 0 0)) (by decide +kernel)
  have a3673 := h.atomAt 1622 (.mul (.n 1584) (.n 1582) (.n 1583)) (by decide +kernel)
  have a3674 := h.atomAt 1623 (.add (.n 1585) (.n 783) (.n 1584)) (by decide +kernel)
  have a3675 := h.atomAt 1624 (.mul (.n 1586) (.n 1205) (.n 1585)) (by decide +kernel)
  have a3676 := h.atomAt 1625 (.add (.n 1587) (.n 1581) (.n 1586)) (by decide +kernel)
  have a3677 := h.atomAt 1626 (.load (.n 1588) (.n 13) 0) (by decide +kernel)
  have a3678 := h.atomAt 1627 (.const (.n 1589) (word 2 0 0)) (by decide +kernel)
  have a3679 := h.atomAt 1628 (.mul (.n 1590) (.n 1588) (.n 1589)) (by decide +kernel)
  have a3680 := h.atomAt 1629 (.add (.n 1591) (.n 783) (.n 1590)) (by decide +kernel)
  have a3681 := h.atomAt 1630 (.mul (.n 1592) (.n 1214) (.n 1591)) (by decide +kernel)
  have a3682 := h.atomAt 1631 (.add (.n 1593) (.n 1587) (.n 1592)) (by decide +kernel)
  have a3683 := h.atomAt 1632 (.load (.n 1594) (.n 13) 0) (by decide +kernel)
  have a3684 := h.atomAt 1633 (.const (.n 1595) (word 2 0 0)) (by decide +kernel)
  have a3685 := h.atomAt 1634 (.mul (.n 1596) (.n 1594) (.n 1595)) (by decide +kernel)
  have a3686 := h.atomAt 1635 (.add (.n 1597) (.n 783) (.n 1596)) (by decide +kernel)
  have a3687 := h.atomAt 1636 (.mul (.n 1598) (.n 1223) (.n 1597)) (by decide +kernel)
  have a3688 := h.atomAt 1637 (.add (.n 1599) (.n 1593) (.n 1598)) (by decide +kernel)
  have a3689 := h.atomAt 1638 (.load (.n 1600) (.n 13) 0) (by decide +kernel)
  have a3690 := h.atomAt 1639 (.const (.n 1601) (word 2 0 0)) (by decide +kernel)
  have a3691 := h.atomAt 1640 (.mul (.n 1602) (.n 1600) (.n 1601)) (by decide +kernel)
  have a3692 := h.atomAt 1641 (.add (.n 1603) (.n 783) (.n 1602)) (by decide +kernel)
  have a3693 := h.atomAt 1642 (.mul (.n 1604) (.n 1232) (.n 1603)) (by decide +kernel)
  have a3694 := h.atomAt 1643 (.add (.n 1605) (.n 1599) (.n 1604)) (by decide +kernel)
  have a3695 := h.atomAt 1644 (.load (.n 1606) (.n 13) 0) (by decide +kernel)
  have a3696 := h.atomAt 1645 (.const (.n 1607) (word 2 0 0)) (by decide +kernel)
  have a3697 := h.atomAt 1646 (.mul (.n 1608) (.n 1606) (.n 1607)) (by decide +kernel)
  have a3698 := h.atomAt 1647 (.add (.n 1609) (.n 783) (.n 1608)) (by decide +kernel)
  have a3699 := h.atomAt 1648 (.mul (.n 1610) (.n 1241) (.n 1609)) (by decide +kernel)
  have a3700 := h.atomAt 1649 (.add (.n 1611) (.n 1605) (.n 1610)) (by decide +kernel)
  have a3701 := h.atomAt 1650 (.load (.n 1612) (.n 13) 0) (by decide +kernel)
  have a3702 := h.atomAt 1651 (.const (.n 1613) (word 2 0 0)) (by decide +kernel)
  have a3703 := h.atomAt 1652 (.mul (.n 1614) (.n 1612) (.n 1613)) (by decide +kernel)
  have a3704 := h.atomAt 1653 (.add (.n 1615) (.n 783) (.n 1614)) (by decide +kernel)
  have a3705 := h.atomAt 1654 (.mul (.n 1616) (.n 1250) (.n 1615)) (by decide +kernel)
  have a3706 := h.atomAt 1655 (.add (.n 1617) (.n 1611) (.n 1616)) (by decide +kernel)
  have a3707 := h.atomAt 1656 (.load (.n 1618) (.n 13) 0) (by decide +kernel)
  have a3708 := h.atomAt 1657 (.const (.n 1619) (word 2 0 0)) (by decide +kernel)
  have a3709 := h.atomAt 1658 (.mul (.n 1620) (.n 1618) (.n 1619)) (by decide +kernel)
  have a3710 := h.atomAt 1659 (.add (.n 1621) (.n 783) (.n 1620)) (by decide +kernel)
  have a3711 := h.atomAt 1660 (.mul (.n 1622) (.n 1259) (.n 1621)) (by decide +kernel)
  have a3712 := h.atomAt 1661 (.add (.n 1623) (.n 1617) (.n 1622)) (by decide +kernel)
  have a3713 := h.atomAt 1662 (.load (.n 1624) (.n 13) 0) (by decide +kernel)
  have a3714 := h.atomAt 1663 (.const (.n 1625) (word 2 0 0)) (by decide +kernel)
  have a3715 := h.atomAt 1664 (.mul (.n 1626) (.n 1624) (.n 1625)) (by decide +kernel)
  have a3716 := h.atomAt 1665 (.add (.n 1627) (.n 783) (.n 1626)) (by decide +kernel)
  have a3717 := h.atomAt 1666 (.mul (.n 1628) (.n 1268) (.n 1627)) (by decide +kernel)
  have a3718 := h.atomAt 1667 (.add (.n 1629) (.n 1623) (.n 1628)) (by decide +kernel)
  have a3719 := h.atomAt 1668 (.load (.n 1630) (.n 13) 0) (by decide +kernel)
  have a3720 := h.atomAt 1669 (.const (.n 1631) (word 2 0 0)) (by decide +kernel)
  have a3721 := h.atomAt 1670 (.mul (.n 1632) (.n 1630) (.n 1631)) (by decide +kernel)
  have a3722 := h.atomAt 1671 (.add (.n 1633) (.n 783) (.n 1632)) (by decide +kernel)
  have a3723 := h.atomAt 1672 (.mul (.n 1634) (.n 1277) (.n 1633)) (by decide +kernel)
  have a3724 := h.atomAt 1673 (.add (.n 1635) (.n 1629) (.n 1634)) (by decide +kernel)
  have a3725 := h.atomAt 1674 (.load (.n 1636) (.n 13) 0) (by decide +kernel)
  have a3726 := h.atomAt 1675 (.const (.n 1637) (word 2 0 0)) (by decide +kernel)
  have a3727 := h.atomAt 1676 (.mul (.n 1638) (.n 1636) (.n 1637)) (by decide +kernel)
  have a3728 := h.atomAt 1677 (.add (.n 1639) (.n 783) (.n 1638)) (by decide +kernel)
  have a3729 := h.atomAt 1678 (.load (.n 1640) (.n 13) 3) (by decide +kernel)
  have a3730 := h.atomAt 1679 (.const (.n 1641) (word 17376452488221285863 0 0)) (by decide +kernel)
  have a3731 := h.atomAt 1680 (.mul (.n 1642) (.n 1640) (.n 1641)) (by decide +kernel)
  have a3732 := h.atomAt 1681 (.add (.n 1643) (.n 1639) (.n 1642)) (by decide +kernel)
  have a3733 := h.atomAt 1682 (.load (.n 1644) (.n 13) 4) (by decide +kernel)
  have a3734 := h.atomAt 1683 (.const (.n 1645) (word 9571781953733019530 0 0)) (by decide +kernel)
  have a3735 := h.atomAt 1684 (.mul (.n 1646) (.n 1644) (.n 1645)) (by decide +kernel)
  have a3736 := h.atomAt 1685 (.add (.n 1647) (.n 1643) (.n 1646)) (by decide +kernel)
  have a3737 := h.atomAt 1686 (.mul (.n 1648) (.n 1286) (.n 1647)) (by decide +kernel)
  have a3738 := h.atomAt 1687 (.add (.n 1649) (.n 1635) (.n 1648)) (by decide +kernel)
  have a3739 := h.atomAt 1688 (.load (.n 1650) (.n 13) 0) (by decide +kernel)
  have a3740 := h.atomAt 1689 (.const (.n 1651) (word 2 0 0)) (by decide +kernel)
  have a3741 := h.atomAt 1690 (.mul (.n 1652) (.n 1650) (.n 1651)) (by decide +kernel)
  have a3742 := h.atomAt 1691 (.add (.n 1653) (.n 783) (.n 1652)) (by decide +kernel)
  have a3743 := h.atomAt 1692 (.load (.n 1654) (.n 13) 3) (by decide +kernel)
  have a3744 := h.atomAt 1693 (.const (.n 1655) (word 15391093639620504046 0 0)) (by decide +kernel)
  have a3745 := h.atomAt 1694 (.mul (.n 1656) (.n 1654) (.n 1655)) (by decide +kernel)
  have a3746 := h.atomAt 1695 (.add (.n 1657) (.n 1653) (.n 1656)) (by decide +kernel)
  have a3747 := h.atomAt 1696 (.load (.n 1658) (.n 13) 4) (by decide +kernel)
  have a3748 := h.atomAt 1697 (.const (.n 1659) (word 13624874521033984333 0 0)) (by decide +kernel)
  have a3749 := h.atomAt 1698 (.mul (.n 1660) (.n 1658) (.n 1659)) (by decide +kernel)
  have a3750 := h.atomAt 1699 (.add (.n 1661) (.n 1657) (.n 1660)) (by decide +kernel)
  have a3751 := h.atomAt 1700 (.mul (.n 1662) (.n 1295) (.n 1661)) (by decide +kernel)
  have a3752 := h.atomAt 1701 (.add (.n 1663) (.n 1649) (.n 1662)) (by decide +kernel)
  have a3753 := h.atomAt 1702 (.load (.n 1664) (.n 13) 0) (by decide +kernel)
  have a3754 := h.atomAt 1703 (.const (.n 1665) (word 2 0 0)) (by decide +kernel)
  have a3755 := h.atomAt 1704 (.mul (.n 1666) (.n 1664) (.n 1665)) (by decide +kernel)
  have a3756 := h.atomAt 1705 (.add (.n 1667) (.n 783) (.n 1666)) (by decide +kernel)
  have a3757 := h.atomAt 1706 (.load (.n 1668) (.n 13) 3) (by decide +kernel)
  have a3758 := h.atomAt 1707 (.const (.n 1669) (word 10027350355371872343 0 0)) (by decide +kernel)
  have a3759 := h.atomAt 1708 (.mul (.n 1670) (.n 1668) (.n 1669)) (by decide +kernel)
  have a3760 := h.atomAt 1709 (.add (.n 1671) (.n 1667) (.n 1670)) (by decide +kernel)
  have a3761 := h.atomAt 1710 (.load (.n 1672) (.n 13) 4) (by decide +kernel)
  have a3762 := h.atomAt 1711 (.const (.n 1673) (word 18417369716475457492 0 0)) (by decide +kernel)
  have a3763 := h.atomAt 1712 (.mul (.n 1674) (.n 1672) (.n 1673)) (by decide +kernel)
  have a3764 := h.atomAt 1713 (.add (.n 1675) (.n 1671) (.n 1674)) (by decide +kernel)
  have a3765 := h.atomAt 1714 (.mul (.n 1676) (.n 1304) (.n 1675)) (by decide +kernel)
  have a3766 := h.atomAt 1715 (.add (.n 1677) (.n 1663) (.n 1676)) (by decide +kernel)
  have a3767 := h.atomAt 1716 (.load (.n 1678) (.n 13) 0) (by decide +kernel)
  have a3768 := h.atomAt 1717 (.const (.n 1679) (word 2 0 0)) (by decide +kernel)
  have a3769 := h.atomAt 1718 (.mul (.n 1680) (.n 1678) (.n 1679)) (by decide +kernel)
  have a3770 := h.atomAt 1719 (.add (.n 1681) (.n 783) (.n 1680)) (by decide +kernel)
  have a3771 := h.atomAt 1720 (.load (.n 1682) (.n 13) 3) (by decide +kernel)
  have a3772 := h.atomAt 1721 (.const (.n 1683) (word 10448040663659726788 0 0)) (by decide +kernel)
  have a3773 := h.atomAt 1722 (.mul (.n 1684) (.n 1682) (.n 1683)) (by decide +kernel)
  have a3774 := h.atomAt 1723 (.add (.n 1685) (.n 1681) (.n 1684)) (by decide +kernel)
  have a3775 := h.atomAt 1724 (.load (.n 1686) (.n 13) 4) (by decide +kernel)
  have a3776 := h.atomAt 1725 (.const (.n 1687) (word 10113917136857017974 0 0)) (by decide +kernel)
  have a3777 := h.atomAt 1726 (.mul (.n 1688) (.n 1686) (.n 1687)) (by decide +kernel)
  have a3778 := h.atomAt 1727 (.add (.n 1689) (.n 1685) (.n 1688)) (by decide +kernel)
  have a3779 := h.atomAt 1728 (.mul (.n 1690) (.n 1313) (.n 1689)) (by decide +kernel)
  have a3780 := h.atomAt 1729 (.add (.n 1691) (.n 1677) (.n 1690)) (by decide +kernel)
  have a3781 := h.atomAt 1730 (.load (.n 1692) (.n 13) 0) (by decide +kernel)
  have a3782 := h.atomAt 1731 (.const (.n 1693) (word 2 0 0)) (by decide +kernel)
  have a3783 := h.atomAt 1732 (.mul (.n 1694) (.n 1692) (.n 1693)) (by decide +kernel)
  have a3784 := h.atomAt 1733 (.add (.n 1695) (.n 783) (.n 1694)) (by decide +kernel)
  have a3785 := h.atomAt 1734 (.load (.n 1696) (.n 13) 3) (by decide +kernel)
  have a3786 := h.atomAt 1735 (.const (.n 1697) (word 12479658147685402012 0 0)) (by decide +kernel)
  have a3787 := h.atomAt 1736 (.mul (.n 1698) (.n 1696) (.n 1697)) (by decide +kernel)
  have a3788 := h.atomAt 1737 (.add (.n 1699) (.n 1695) (.n 1698)) (by decide +kernel)
  have a3789 := h.atomAt 1738 (.load (.n 1700) (.n 13) 4) (by decide +kernel)
  have a3790 := h.atomAt 1739 (.const (.n 1701) (word 3500241080921619556 0 0)) (by decide +kernel)
  have a3791 := h.atomAt 1740 (.mul (.n 1702) (.n 1700) (.n 1701)) (by decide +kernel)
  have a3792 := h.atomAt 1741 (.add (.n 1703) (.n 1699) (.n 1702)) (by decide +kernel)
  have a3793 := h.atomAt 1742 (.mul (.n 1704) (.n 1322) (.n 1703)) (by decide +kernel)
  have a3794 := h.atomAt 1743 (.add (.n 1705) (.n 1691) (.n 1704)) (by decide +kernel)
  have a3795 := h.atomAt 1744 (.load (.n 1706) (.n 13) 0) (by decide +kernel)
  have a3796 := h.atomAt 1745 (.const (.n 1707) (word 2 0 0)) (by decide +kernel)
  have a3797 := h.atomAt 1746 (.mul (.n 1708) (.n 1706) (.n 1707)) (by decide +kernel)
  have a3798 := h.atomAt 1747 (.add (.n 1709) (.n 783) (.n 1708)) (by decide +kernel)
  have a3799 := h.atomAt 1748 (.load (.n 1710) (.n 13) 3) (by decide +kernel)
  have a3800 := h.atomAt 1749 (.const (.n 1711) (word 16959053435453822517 0 0)) (by decide +kernel)
  have a3801 := h.atomAt 1750 (.mul (.n 1712) (.n 1710) (.n 1711)) (by decide +kernel)
  have a3802 := h.atomAt 1751 (.add (.n 1713) (.n 1709) (.n 1712)) (by decide +kernel)
  have a3803 := h.atomAt 1752 (.load (.n 1714) (.n 13) 4) (by decide +kernel)
  have a3804 := h.atomAt 1753 (.const (.n 1715) (word 12224711289652453635 0 0)) (by decide +kernel)
  have a3805 := h.atomAt 1754 (.mul (.n 1716) (.n 1714) (.n 1715)) (by decide +kernel)
  have a3806 := h.atomAt 1755 (.add (.n 1717) (.n 1713) (.n 1716)) (by decide +kernel)
  have a3807 := h.atomAt 1756 (.mul (.n 1718) (.n 1331) (.n 1717)) (by decide +kernel)
  have a3808 := h.atomAt 1757 (.add (.n 1719) (.n 1705) (.n 1718)) (by decide +kernel)
  have a3809 := h.atomAt 1758 (.load (.n 1720) (.n 13) 0) (by decide +kernel)
  have a3810 := h.atomAt 1759 (.const (.n 1721) (word 2 0 0)) (by decide +kernel)
  have a3811 := h.atomAt 1760 (.mul (.n 1722) (.n 1720) (.n 1721)) (by decide +kernel)
  have a3812 := h.atomAt 1761 (.add (.n 1723) (.n 783) (.n 1722)) (by decide +kernel)
  have a3813 := h.atomAt 1762 (.load (.n 1724) (.n 13) 3) (by decide +kernel)
  have a3814 := h.atomAt 1763 (.const (.n 1725) (word 9342009439668884831 0 0)) (by decide +kernel)
  have a3815 := h.atomAt 1764 (.mul (.n 1726) (.n 1724) (.n 1725)) (by decide +kernel)
  have a3816 := h.atomAt 1765 (.add (.n 1727) (.n 1723) (.n 1726)) (by decide +kernel)
  have a3817 := h.atomAt 1766 (.load (.n 1728) (.n 13) 4) (by decide +kernel)
  have a3818 := h.atomAt 1767 (.const (.n 1729) (word 4879704952849025062 0 0)) (by decide +kernel)
  have a3819 := h.atomAt 1768 (.mul (.n 1730) (.n 1728) (.n 1729)) (by decide +kernel)
  have a3820 := h.atomAt 1769 (.add (.n 1731) (.n 1727) (.n 1730)) (by decide +kernel)
  have a3821 := h.atomAt 1770 (.mul (.n 1732) (.n 1340) (.n 1731)) (by decide +kernel)
  have a3822 := h.atomAt 1771 (.add (.n 1733) (.n 1719) (.n 1732)) (by decide +kernel)
  have a3823 := h.atomAt 1772 (.load (.n 1734) (.n 13) 0) (by decide +kernel)
  have a3824 := h.atomAt 1773 (.const (.n 1735) (word 2 0 0)) (by decide +kernel)
  have a3825 := h.atomAt 1774 (.mul (.n 1736) (.n 1734) (.n 1735)) (by decide +kernel)
  have a3826 := h.atomAt 1775 (.add (.n 1737) (.n 783) (.n 1736)) (by decide +kernel)
  have a3827 := h.atomAt 1776 (.load (.n 1738) (.n 13) 3) (by decide +kernel)
  have a3828 := h.atomAt 1777 (.const (.n 1739) (word 140226327413610143 0 0)) (by decide +kernel)
  have a3829 := h.atomAt 1778 (.mul (.n 1740) (.n 1738) (.n 1739)) (by decide +kernel)
  have a3830 := h.atomAt 1779 (.add (.n 1741) (.n 1737) (.n 1740)) (by decide +kernel)
  have a3831 := h.atomAt 1780 (.load (.n 1742) (.n 13) 4) (by decide +kernel)
  have a3832 := h.atomAt 1781 (.const (.n 1743) (word 424854978622500449 0 0)) (by decide +kernel)
  have a3833 := h.atomAt 1782 (.mul (.n 1744) (.n 1742) (.n 1743)) (by decide +kernel)
  have a3834 := h.atomAt 1783 (.add (.n 1745) (.n 1741) (.n 1744)) (by decide +kernel)
  have a3835 := h.atomAt 1784 (.mul (.n 1746) (.n 1349) (.n 1745)) (by decide +kernel)
  have a3836 := h.atomAt 1785 (.add (.n 1747) (.n 1733) (.n 1746)) (by decide +kernel)
  have a3837 := h.atomAt 1786 (.load (.n 1748) (.n 13) 0) (by decide +kernel)
  have a3838 := h.atomAt 1787 (.const (.n 1749) (word 2 0 0)) (by decide +kernel)
  have a3839 := h.atomAt 1788 (.mul (.n 1750) (.n 1748) (.n 1749)) (by decide +kernel)
  have a3840 := h.atomAt 1789 (.add (.n 1751) (.n 783) (.n 1750)) (by decide +kernel)
  have a3841 := h.atomAt 1790 (.load (.n 1752) (.n 13) 3) (by decide +kernel)
  have a3842 := h.atomAt 1791 (.const (.n 1753) (word 7259519967065370866 0 0)) (by decide +kernel)
  have a3843 := h.atomAt 1792 (.mul (.n 1754) (.n 1752) (.n 1753)) (by decide +kernel)
  have a3844 := h.atomAt 1793 (.add (.n 1755) (.n 1751) (.n 1754)) (by decide +kernel)
  have a3845 := h.atomAt 1794 (.mul (.n 1756) (.n 1358) (.n 1755)) (by decide +kernel)
  have a3846 := h.atomAt 1795 (.add (.n 1757) (.n 1747) (.n 1756)) (by decide +kernel)
  have a3847 := h.atomAt 1796 (.load (.n 1758) (.n 13) 0) (by decide +kernel)
  have a3848 := h.atomAt 1797 (.const (.n 1759) (word 2 0 0)) (by decide +kernel)
  have a3849 := h.atomAt 1798 (.mul (.n 1760) (.n 1758) (.n 1759)) (by decide +kernel)
  have a3850 := h.atomAt 1799 (.add (.n 1761) (.n 783) (.n 1760)) (by decide +kernel)
  have a3851 := h.atomAt 1800 (.load (.n 1762) (.n 13) 3) (by decide +kernel)
  have a3852 := h.atomAt 1801 (.const (.n 1763) (word 7004910057750291985 0 0)) (by decide +kernel)
  have a3853 := h.atomAt 1802 (.mul (.n 1764) (.n 1762) (.n 1763)) (by decide +kernel)
  have a3854 := h.atomAt 1803 (.add (.n 1765) (.n 1761) (.n 1764)) (by decide +kernel)
  have a3855 := h.atomAt 1804 (.load (.n 1766) (.n 13) 4) (by decide +kernel)
  have a3856 := h.atomAt 1805 (.const (.n 1767) (word 13293599522548616907 0 0)) (by decide +kernel)
  have a3857 := h.atomAt 1806 (.mul (.n 1768) (.n 1766) (.n 1767)) (by decide +kernel)
  have a3858 := h.atomAt 1807 (.add (.n 1769) (.n 1765) (.n 1768)) (by decide +kernel)
  have a3859 := h.atomAt 1808 (.mul (.n 1770) (.n 1367) (.n 1769)) (by decide +kernel)
  have a3860 := h.atomAt 1809 (.add (.n 1771) (.n 1757) (.n 1770)) (by decide +kernel)
  have a3861 := h.atomAt 1810 (.load (.n 1772) (.n 13) 0) (by decide +kernel)
  have a3862 := h.atomAt 1811 (.const (.n 1773) (word 2 0 0)) (by decide +kernel)
  have a3863 := h.atomAt 1812 (.mul (.n 1774) (.n 1772) (.n 1773)) (by decide +kernel)
  have a3864 := h.atomAt 1813 (.add (.n 1775) (.n 783) (.n 1774)) (by decide +kernel)
  have a3865 := h.atomAt 1814 (.load (.n 1776) (.n 13) 3) (by decide +kernel)
  have a3866 := h.atomAt 1815 (.const (.n 1777) (word 10105770293752443592 0 0)) (by decide +kernel)
  have a3867 := h.atomAt 1816 (.mul (.n 1778) (.n 1776) (.n 1777)) (by decide +kernel)
  have a3868 := h.atomAt 1817 (.add (.n 1779) (.n 1775) (.n 1778)) (by decide +kernel)
  have a3869 := h.atomAt 1818 (.load (.n 1780) (.n 13) 4) (by decide +kernel)
  have a3870 := h.atomAt 1819 (.const (.n 1781) (word 10668034807192757780 0 0)) (by decide +kernel)
  have a3871 := h.atomAt 1820 (.mul (.n 1782) (.n 1780) (.n 1781)) (by decide +kernel)
  have a3872 := h.atomAt 1821 (.add (.n 1783) (.n 1779) (.n 1782)) (by decide +kernel)
  have a3873 := h.atomAt 1822 (.mul (.n 1784) (.n 1376) (.n 1783)) (by decide +kernel)
  have a3874 := h.atomAt 1823 (.add (.n 1785) (.n 1771) (.n 1784)) (by decide +kernel)
  have a3875 := h.atomAt 1824 (.load (.n 1786) (.n 13) 0) (by decide +kernel)
  have a3876 := h.atomAt 1825 (.const (.n 1787) (word 2 0 0)) (by decide +kernel)
  have a3877 := h.atomAt 1826 (.mul (.n 1788) (.n 1786) (.n 1787)) (by decide +kernel)
  have a3878 := h.atomAt 1827 (.add (.n 1789) (.n 783) (.n 1788)) (by decide +kernel)
  have a3879 := h.atomAt 1828 (.load (.n 1790) (.n 13) 3) (by decide +kernel)
  have a3880 := h.atomAt 1829 (.const (.n 1791) (word 1747952066141424100 0 0)) (by decide +kernel)
  have a3881 := h.atomAt 1830 (.mul (.n 1792) (.n 1790) (.n 1791)) (by decide +kernel)
  have a3882 := h.atomAt 1831 (.add (.n 1793) (.n 1789) (.n 1792)) (by decide +kernel)
  have a3883 := h.atomAt 1832 (.load (.n 1794) (.n 13) 4) (by decide +kernel)
  have a3884 := h.atomAt 1833 (.const (.n 1795) (word 1654286879329379778 0 0)) (by decide +kernel)
  have a3885 := h.atomAt 1834 (.mul (.n 1796) (.n 1794) (.n 1795)) (by decide +kernel)
  have a3886 := h.atomAt 1835 (.add (.n 1797) (.n 1793) (.n 1796)) (by decide +kernel)
  have a3887 := h.atomAt 1836 (.mul (.n 1798) (.n 1385) (.n 1797)) (by decide +kernel)
  have a3888 := h.atomAt 1837 (.add (.n 1799) (.n 1785) (.n 1798)) (by decide +kernel)
  have a3889 := h.atomAt 1838 (.load (.n 1800) (.n 13) 0) (by decide +kernel)
  have a3890 := h.atomAt 1839 (.const (.n 1801) (word 2 0 0)) (by decide +kernel)
  have a3891 := h.atomAt 1840 (.mul (.n 1802) (.n 1800) (.n 1801)) (by decide +kernel)
  have a3892 := h.atomAt 1841 (.add (.n 1803) (.n 783) (.n 1802)) (by decide +kernel)
  have a3893 := h.atomAt 1842 (.load (.n 1804) (.n 13) 3) (by decide +kernel)
  have a3894 := h.atomAt 1843 (.const (.n 1805) (word 8500057116360352059 0 0)) (by decide +kernel)
  have a3895 := h.atomAt 1844 (.mul (.n 1806) (.n 1804) (.n 1805)) (by decide +kernel)
  have a3896 := h.atomAt 1845 (.add (.n 1807) (.n 1803) (.n 1806)) (by decide +kernel)
  have a3897 := h.atomAt 1846 (.load (.n 1808) (.n 13) 4) (by decide +kernel)
  have a3898 := h.atomAt 1847 (.const (.n 1809) (word 16929593379567477321 0 0)) (by decide +kernel)
  have a3899 := h.atomAt 1848 (.mul (.n 1810) (.n 1808) (.n 1809)) (by decide +kernel)
  have a3900 := h.atomAt 1849 (.add (.n 1811) (.n 1807) (.n 1810)) (by decide +kernel)
  have a3901 := h.atomAt 1850 (.mul (.n 1812) (.n 1394) (.n 1811)) (by decide +kernel)
  have a3902 := h.atomAt 1851 (.add (.n 1813) (.n 1799) (.n 1812)) (by decide +kernel)
  have a3903 := h.atomAt 1852 (.mul (.n 1814) (.n 652) (.n 1813)) (by decide +kernel)
  have a3904 := h.atomAt 1853 (.add (.n 1815) (.n 1544) (.n 1814)) (by decide +kernel)
  have a3905 := h.atomAt 1854 (.add (.n 1816) (.n 955) (.n 1815)) (by decide +kernel)
  have a3906 := h.atomAt 1855 (.const (.n 1817) (word 1 0 0)) (by decide +kernel)
  have a3907 := h.atomAt 1856 (.add (.n 1818) (.n 1817) (.n 1393)) (by decide +kernel)
  have a3908 := h.atomAt 1857 (.add (.n 1819) (.n 1816) (.n 1818)) (by decide +kernel)
  have a3909 := h.atomAt 1858 (.add (.n 1820) (.n 1819) (.n 25)) (by decide +kernel)
  have e3484 := tb_loadHolds_unique a3484 (hw 0 (by norm_num))
  have e3487 := tb_loadHolds_unique a3487 (hw 0 (by norm_num))
  have e3491 := tb_loadHolds_unique a3491 (hw 3 (by norm_num))
  have e3495 := tb_loadHolds_unique a3495 (hw 0 (by norm_num))
  have e3501 := tb_loadHolds_unique a3501 (hw 0 (by norm_num))
  have e3507 := tb_loadHolds_unique a3507 (hw 0 (by norm_num))
  have e3514 := tb_loadHolds_unique a3514 (hw 0 (by norm_num))
  have e3517 := tb_loadHolds_unique a3517 (hw 0 (by norm_num))
  have e3521 := tb_loadHolds_unique a3521 (hw 3 (by norm_num))
  have e3527 := tb_loadHolds_unique a3527 (hw 0 (by norm_num))
  have e3533 := tb_loadHolds_unique a3533 (hw 0 (by norm_num))
  have e3539 := tb_loadHolds_unique a3539 (hw 0 (by norm_num))
  have e3547 := tb_loadHolds_unique a3547 (hw 0 (by norm_num))
  have e3550 := tb_loadHolds_unique a3550 (hw 0 (by norm_num))
  have e3554 := tb_loadHolds_unique a3554 (hw 3 (by norm_num))
  have e3560 := tb_loadHolds_unique a3560 (hw 0 (by norm_num))
  have e3568 := tb_loadHolds_unique a3568 (hw 0 (by norm_num))
  have e3571 := tb_loadHolds_unique a3571 (hw 0 (by norm_num))
  have e3575 := tb_loadHolds_unique a3575 (hw 3 (by norm_num))
  have e3581 := tb_loadHolds_unique a3581 (hw 0 (by norm_num))
  have e3587 := tb_loadHolds_unique a3587 (hw 0 (by norm_num))
  have e3593 := tb_loadHolds_unique a3593 (hw 0 (by norm_num))
  have e3601 := tb_loadHolds_unique a3601 (hw 0 (by norm_num))
  have e3604 := tb_loadHolds_unique a3604 (hw 0 (by norm_num))
  have e3608 := tb_loadHolds_unique a3608 (hw 3 (by norm_num))
  have e3614 := tb_loadHolds_unique a3614 (hw 0 (by norm_num))
  have e3620 := tb_loadHolds_unique a3620 (hw 0 (by norm_num))
  have e3626 := tb_loadHolds_unique a3626 (hw 0 (by norm_num))
  have e3634 := tb_loadHolds_unique a3634 (hw 0 (by norm_num))
  have e3637 := tb_loadHolds_unique a3637 (hw 0 (by norm_num))
  have e3641 := tb_loadHolds_unique a3641 (hw 3 (by norm_num))
  have e3647 := tb_loadHolds_unique a3647 (hw 0 (by norm_num))
  have e3653 := tb_loadHolds_unique a3653 (hw 0 (by norm_num))
  have e3659 := tb_loadHolds_unique a3659 (hw 0 (by norm_num))
  have e3665 := tb_loadHolds_unique a3665 (hw 0 (by norm_num))
  have e3671 := tb_loadHolds_unique a3671 (hw 0 (by norm_num))
  have e3677 := tb_loadHolds_unique a3677 (hw 0 (by norm_num))
  have e3683 := tb_loadHolds_unique a3683 (hw 0 (by norm_num))
  have e3689 := tb_loadHolds_unique a3689 (hw 0 (by norm_num))
  have e3695 := tb_loadHolds_unique a3695 (hw 0 (by norm_num))
  have e3701 := tb_loadHolds_unique a3701 (hw 0 (by norm_num))
  have e3707 := tb_loadHolds_unique a3707 (hw 0 (by norm_num))
  have e3713 := tb_loadHolds_unique a3713 (hw 0 (by norm_num))
  have e3719 := tb_loadHolds_unique a3719 (hw 0 (by norm_num))
  have e3725 := tb_loadHolds_unique a3725 (hw 0 (by norm_num))
  have e3729 := tb_loadHolds_unique a3729 (hw 3 (by norm_num))
  have e3733 := tb_loadHolds_unique a3733 (hw 4 (by norm_num))
  have e3739 := tb_loadHolds_unique a3739 (hw 0 (by norm_num))
  have e3743 := tb_loadHolds_unique a3743 (hw 3 (by norm_num))
  have e3747 := tb_loadHolds_unique a3747 (hw 4 (by norm_num))
  have e3753 := tb_loadHolds_unique a3753 (hw 0 (by norm_num))
  have e3757 := tb_loadHolds_unique a3757 (hw 3 (by norm_num))
  have e3761 := tb_loadHolds_unique a3761 (hw 4 (by norm_num))
  have e3767 := tb_loadHolds_unique a3767 (hw 0 (by norm_num))
  have e3771 := tb_loadHolds_unique a3771 (hw 3 (by norm_num))
  have e3775 := tb_loadHolds_unique a3775 (hw 4 (by norm_num))
  have e3781 := tb_loadHolds_unique a3781 (hw 0 (by norm_num))
  have e3785 := tb_loadHolds_unique a3785 (hw 3 (by norm_num))
  have e3789 := tb_loadHolds_unique a3789 (hw 4 (by norm_num))
  have e3795 := tb_loadHolds_unique a3795 (hw 0 (by norm_num))
  have e3799 := tb_loadHolds_unique a3799 (hw 3 (by norm_num))
  have e3803 := tb_loadHolds_unique a3803 (hw 4 (by norm_num))
  have e3809 := tb_loadHolds_unique a3809 (hw 0 (by norm_num))
  have e3813 := tb_loadHolds_unique a3813 (hw 3 (by norm_num))
  have e3817 := tb_loadHolds_unique a3817 (hw 4 (by norm_num))
  have e3823 := tb_loadHolds_unique a3823 (hw 0 (by norm_num))
  have e3827 := tb_loadHolds_unique a3827 (hw 3 (by norm_num))
  have e3831 := tb_loadHolds_unique a3831 (hw 4 (by norm_num))
  have e3837 := tb_loadHolds_unique a3837 (hw 0 (by norm_num))
  have e3841 := tb_loadHolds_unique a3841 (hw 3 (by norm_num))
  have e3847 := tb_loadHolds_unique a3847 (hw 0 (by norm_num))
  have e3851 := tb_loadHolds_unique a3851 (hw 3 (by norm_num))
  have e3855 := tb_loadHolds_unique a3855 (hw 4 (by norm_num))
  have e3861 := tb_loadHolds_unique a3861 (hw 0 (by norm_num))
  have e3865 := tb_loadHolds_unique a3865 (hw 3 (by norm_num))
  have e3869 := tb_loadHolds_unique a3869 (hw 4 (by norm_num))
  have e3875 := tb_loadHolds_unique a3875 (hw 0 (by norm_num))
  have e3879 := tb_loadHolds_unique a3879 (hw 3 (by norm_num))
  have e3883 := tb_loadHolds_unique a3883 (hw 4 (by norm_num))
  have e3889 := tb_loadHolds_unique a3889 (hw 0 (by norm_num))
  have e3893 := tb_loadHolds_unique a3893 (hw 3 (by norm_num))
  have e3897 := tb_loadHolds_unique a3897 (hw 4 (by norm_num))
  simp only [Atom.Holds] at a3485 a3486 a3488 a3489 a3490 a3492 a3493 a3494 a3496 a3497
  simp only [Atom.Holds] at a3498 a3499 a3500 a3502 a3503 a3504 a3505 a3506 a3508 a3509
  simp only [Atom.Holds] at a3510 a3511 a3512 a3513 a3515 a3516 a3518 a3519 a3520 a3522
  simp only [Atom.Holds] at a3523 a3524 a3525 a3526 a3528 a3529 a3530 a3531 a3532 a3534
  simp only [Atom.Holds] at a3535 a3536 a3537 a3538 a3540 a3541 a3542 a3543 a3544 a3545
  simp only [Atom.Holds] at a3546 a3548 a3549 a3551 a3552 a3553 a3555 a3556 a3557 a3558
  simp only [Atom.Holds] at a3559 a3561 a3562 a3563 a3564 a3565 a3566 a3567 a3569 a3570
  simp only [Atom.Holds] at a3572 a3573 a3574 a3576 a3577 a3578 a3579 a3580 a3582 a3583
  simp only [Atom.Holds] at a3584 a3585 a3586 a3588 a3589 a3590 a3591 a3592 a3594 a3595
  simp only [Atom.Holds] at a3596 a3597 a3598 a3599 a3600 a3602 a3603 a3605 a3606 a3607
  simp only [Atom.Holds] at a3609 a3610 a3611 a3612 a3613 a3615 a3616 a3617 a3618 a3619
  simp only [Atom.Holds] at a3621 a3622 a3623 a3624 a3625 a3627 a3628 a3629 a3630 a3631
  simp only [Atom.Holds] at a3632 a3633 a3635 a3636 a3638 a3639 a3640 a3642 a3643 a3644
  simp only [Atom.Holds] at a3645 a3646 a3648 a3649 a3650 a3651 a3652 a3654 a3655 a3656
  simp only [Atom.Holds] at a3657 a3658 a3660 a3661 a3662 a3663 a3664 a3666 a3667 a3668
  simp only [Atom.Holds] at a3669 a3670 a3672 a3673 a3674 a3675 a3676 a3678 a3679 a3680
  simp only [Atom.Holds] at a3681 a3682 a3684 a3685 a3686 a3687 a3688 a3690 a3691 a3692
  simp only [Atom.Holds] at a3693 a3694 a3696 a3697 a3698 a3699 a3700 a3702 a3703 a3704
  simp only [Atom.Holds] at a3705 a3706 a3708 a3709 a3710 a3711 a3712 a3714 a3715 a3716
  simp only [Atom.Holds] at a3717 a3718 a3720 a3721 a3722 a3723 a3724 a3726 a3727 a3728
  simp only [Atom.Holds] at a3730 a3731 a3732 a3734 a3735 a3736 a3737 a3738 a3740 a3741
  simp only [Atom.Holds] at a3742 a3744 a3745 a3746 a3748 a3749 a3750 a3751 a3752 a3754
  simp only [Atom.Holds] at a3755 a3756 a3758 a3759 a3760 a3762 a3763 a3764 a3765 a3766
  simp only [Atom.Holds] at a3768 a3769 a3770 a3772 a3773 a3774 a3776 a3777 a3778 a3779
  simp only [Atom.Holds] at a3780 a3782 a3783 a3784 a3786 a3787 a3788 a3790 a3791 a3792
  simp only [Atom.Holds] at a3793 a3794 a3796 a3797 a3798 a3800 a3801 a3802 a3804 a3805
  simp only [Atom.Holds] at a3806 a3807 a3808 a3810 a3811 a3812 a3814 a3815 a3816 a3818
  simp only [Atom.Holds] at a3819 a3820 a3821 a3822 a3824 a3825 a3826 a3828 a3829 a3830
  simp only [Atom.Holds] at a3832 a3833 a3834 a3835 a3836 a3838 a3839 a3840 a3842 a3843
  simp only [Atom.Holds] at a3844 a3845 a3846 a3848 a3849 a3850 a3852 a3853 a3854 a3856
  simp only [Atom.Holds] at a3857 a3858 a3859 a3860 a3862 a3863 a3864 a3866 a3867 a3868
  simp only [Atom.Holds] at a3870 a3871 a3872 a3873 a3874 a3876 a3877 a3878 a3880 a3881
  simp only [Atom.Holds] at a3882 a3884 a3885 a3886 a3887 a3888 a3890 a3891 a3892 a3894
  simp only [Atom.Holds] at a3895 a3896 a3898 a3899 a3900 a3901 a3902 a3903 a3904 a3905
  simp only [Atom.Holds] at a3906 a3907 a3908 a3909
  have t0 : σ (.n 1423) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 783)) vtPushPadData 0 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3484, a3485, a3486, e3487, a3488, a3489, a3490, e3491, a3492, a3493, a3494, e3495, a3496,
      a3497, a3498, a3499, a3500, e3501, a3502, a3503, a3504, a3505, a3506, e3507, a3508, a3509,
      a3510, a3511, a3512]
    ring
  have t1 : σ (.n 1455) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 783)) vtPushPadData 1 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3514, a3515, a3516, e3517, a3518, a3519, a3520, e3521, a3522, a3523, a3524, a3525, a3526,
      e3527, a3528, a3529, a3530, a3531, a3532, e3533, a3534, a3535, a3536, a3537, a3538, e3539,
      a3540, a3541, a3542, a3543, a3544]
    ring
  have t2 : σ (.n 1476) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 783)) vtPushPadData 2 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3547, a3548, a3549, e3550, a3551, a3552, a3553, e3554, a3555, a3556, a3557, a3558, a3559,
      e3560, a3561, a3562, a3563, a3564, a3565]
    ring
  have t3 : σ (.n 1509) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 783)) vtPushPadData 3 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3568, a3569, a3570, e3571, a3572, a3573, a3574, e3575, a3576, a3577, a3578, a3579, a3580,
      e3581, a3582, a3583, a3584, a3585, a3586, e3587, a3588, a3589, a3590, a3591, a3592, e3593,
      a3594, a3595, a3596, a3597, a3598]
    ring
  have t4 : σ (.n 1542) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 783)) vtPushPadData 4 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3601, a3602, a3603, e3604, a3605, a3606, a3607, e3608, a3609, a3610, a3611, a3612, a3613,
      e3614, a3615, a3616, a3617, a3618, a3619, e3620, a3621, a3622, a3623, a3624, a3625, e3626,
      a3627, a3628, a3629, a3630, a3631]
    ring
  have t5 : σ (.n 1813) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 783)) vtPushPadData 5 := by
    simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, tb_word_one, mul_one, add_zero]
    simp only [e3634, a3635, a3636, e3637, a3638, a3639, a3640, e3641, a3642, a3643, a3644, a3645, a3646,
      e3647, a3648, a3649, a3650, a3651, a3652, e3653, a3654, a3655, a3656, a3657, a3658, e3659,
      a3660, a3661, a3662, a3663, a3664, e3665, a3666, a3667, a3668, a3669, a3670, e3671, a3672,
      a3673, a3674, a3675, a3676, e3677, a3678, a3679, a3680, a3681, a3682, e3683, a3684, a3685,
      a3686, a3687, a3688, e3689, a3690, a3691, a3692, a3693, a3694, e3695, a3696, a3697, a3698,
      a3699, a3700, e3701, a3702, a3703, a3704, a3705, a3706, e3707, a3708, a3709, a3710, a3711,
      a3712, e3713, a3714, a3715, a3716, a3717, a3718, e3719, a3720, a3721, a3722, a3723, a3724,
      e3725, a3726, a3727, a3728, e3729, a3730, a3731, a3732, e3733, a3734, a3735, a3736, a3737,
      a3738, e3739, a3740, a3741, a3742, e3743, a3744, a3745, a3746, e3747, a3748, a3749, a3750,
      a3751, a3752, e3753, a3754, a3755, a3756, e3757, a3758, a3759, a3760, e3761, a3762, a3763,
      a3764, a3765, a3766, e3767, a3768, a3769, a3770, e3771, a3772, a3773, a3774, e3775, a3776,
      a3777, a3778, a3779, a3780, e3781, a3782, a3783, a3784, e3785, a3786, a3787, a3788, e3789,
      a3790, a3791, a3792, a3793, a3794, e3795, a3796, a3797, a3798, e3799, a3800, a3801, a3802,
      e3803, a3804, a3805, a3806, a3807, a3808, e3809, a3810, a3811, a3812, e3813, a3814, a3815,
      a3816, e3817, a3818, a3819, a3820, a3821, a3822, e3823, a3824, a3825, a3826, e3827, a3828,
      a3829, a3830, e3831, a3832, a3833, a3834, a3835, a3836, e3837, a3838, a3839, a3840, e3841,
      a3842, a3843, a3844, a3845, a3846, e3847, a3848, a3849, a3850, e3851, a3852, a3853, a3854,
      e3855, a3856, a3857, a3858, a3859, a3860, e3861, a3862, a3863, a3864, e3865, a3866, a3867,
      a3868, e3869, a3870, a3871, a3872, a3873, a3874, e3875, a3876, a3877, a3878, e3879, a3880,
      a3881, a3882, e3883, a3884, a3885, a3886, a3887, a3888, e3889, a3890, a3891, a3892, e3893,
      a3894, a3895, a3896, e3897, a3898, a3899, a3900, a3901, a3902]
    ring
  simp only [vtPadSum, vtPadV]
  simp only [a3513, a3545, a3546, a3566, a3567, a3599, a3600, a3632, a3633, a3903, a3904, a3905, a3906,
    a3907, a3908, a3909]
  rw [← t0, ← t1, ← t2, ← t3, ← t4, ← t5, tb_word_one]

end
end LeanVM.Guest.B1.Tables
