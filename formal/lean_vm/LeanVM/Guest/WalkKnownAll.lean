/-
  LeanVM.Guest.WalkKnownAll

  The walks' obligations, proved: every function the certificates hand something on at its cuts,
  but `main` and `verify_sub`.
-/

module

public import LeanVM.Guest.WalkOq0
public import LeanVM.Guest.WalkOq1
public import LeanVM.Guest.WalkOq2
public import LeanVM.Guest.WalkOq3
public import LeanVM.Guest.WalkWp
public import LeanVM.Guest.WalkLq0
public import LeanVM.Guest.WalkLq1
public import LeanVM.Guest.WalkLq2
public import LeanVM.Guest.WalkLq3
public import LeanVM.Guest.WalkOs0
public import LeanVM.Guest.WalkOs1
public import LeanVM.Guest.WalkOs2
public import LeanVM.Guest.WalkOs3
public import LeanVM.Guest.WalkGkr

/-!
# `WalkKnown`, proved

`walkKnown_proved : WalkKnown`: the cut obligations (`CutsKnown`) of every function of
`Checked.oblFns` but `main` (`1`) and `verify_sub` (`19`): `opening_queries`' specializations and
loops (`WalkOq0.lean` to `WalkOq3.lean`, whir's `QueriesWalk` through b2's `WalkKnown.lean`),
`open_stacked`'s arms (`WalkOs0.lean` to `WalkOs3.lean`, from each level's dispatch into
`level_positions`, `WalkOsPre.lean`), `level_queries`' specializations (`WalkLq0.lean` to
`WalkLq3.lean`) and `walk_path`'s (`WalkWp.lean`), from their windows' tags, and
`verify_bus_gkr` (`10`) and its layer loop `__loop6` (`91`), whose obligations (the layers' parities, `GkrPar`) the gkr track proves (`WalkGkr.lean`;
`walkKnown_of_gkr`).
-/

namespace LeanVM.Guest.End

@[expose] public section

set_option maxRecDepth 4000 in
/-- **The walks' obligations**, given `verify_bus_gkr`'s and its layer loop's. -/
theorem walkKnown_of_gkr (h10 : CutsKnown 10) (h91 : CutsKnown 91) : WalkKnown := by
  -- One conjunct per function of `Checked.oblFns`, in order: linear, where `rcases` over the
  -- membership disjunction is quadratic.
  have key : List.Forall (fun j ↦ j ≠ 1 → j ≠ 19 → CutsKnown j) Checked.oblFns :=
    ⟨fun h _ ↦ absurd rfl h, fun _ _ ↦ h10, fun _ h ↦ absurd rfl h, fun _ _ ↦ h91,
      fun _ _ ↦ walk_336, fun _ _ ↦ walk_337, fun _ _ ↦ walk_338, fun _ _ ↦ walk_339,
      fun _ _ ↦ walk_340, fun _ _ ↦ walk_341, fun _ _ ↦ walk_342, fun _ _ ↦ walk_343,
      fun _ _ ↦ walk_344, fun _ _ ↦ walk_345, fun _ _ ↦ walk_346, fun _ _ ↦ walk_468,
      fun _ _ ↦ walk_469, fun _ _ ↦ walk_470, fun _ _ ↦ walk_471, fun _ _ ↦ walk_478,
      fun _ _ ↦ walk_479, fun _ _ ↦ walk_480, fun _ _ ↦ walk_481, fun _ _ ↦ walk_487,
      fun _ _ ↦ walk_488, fun _ _ ↦ walk_489, fun _ _ ↦ walk_490, fun _ _ ↦ walk_495,
      fun _ _ ↦ walk_496, fun _ _ ↦ walk_497, fun _ _ ↦ walk_498, fun _ _ ↦ walk_517,
      fun _ _ ↦ walk_518, fun _ _ ↦ walk_519, fun _ _ ↦ walk_520, fun _ _ ↦ walk_526,
      fun _ _ ↦ walk_527, fun _ _ ↦ walk_528, fun _ _ ↦ walk_529, fun _ _ ↦ walk_533,
      fun _ _ ↦ walk_534, fun _ _ ↦ walk_535, fun _ _ ↦ walk_536, fun _ _ ↦ walk_538,
      fun _ _ ↦ walk_539, fun _ _ ↦ walk_540, fun _ _ ↦ walk_541, fun _ _ ↦ walk_560,
      fun _ _ ↦ walk_561, fun _ _ ↦ walk_562, fun _ _ ↦ walk_563, fun _ _ ↦ walk_569,
      fun _ _ ↦ walk_570, fun _ _ ↦ walk_571, fun _ _ ↦ walk_572, fun _ _ ↦ walk_575,
      fun _ _ ↦ walk_576, fun _ _ ↦ walk_577, fun _ _ ↦ walk_578, fun _ _ ↦ walk_581,
      fun _ _ ↦ walk_582, fun _ _ ↦ walk_583, fun _ _ ↦ walk_584, fun _ _ ↦ walk_603,
      fun _ _ ↦ walk_604, fun _ _ ↦ walk_605, fun _ _ ↦ walk_606, fun _ _ ↦ walk_612,
      fun _ _ ↦ walk_613, fun _ _ ↦ walk_614, fun _ _ ↦ walk_615, fun _ _ ↦ walk_618,
      fun _ _ ↦ walk_619, fun _ _ ↦ walk_620, fun _ _ ↦ walk_621, fun _ _ ↦ walk_624,
      fun _ _ ↦ walk_625, fun _ _ ↦ walk_626, fun _ _ ↦ walk_627, fun _ _ ↦ walk_646,
      fun _ _ ↦ walk_647, fun _ _ ↦ walk_648, fun _ _ ↦ walk_649, fun _ _ ↦ walk_653,
      fun _ _ ↦ walk_654, fun _ _ ↦ walk_655, fun _ _ ↦ walk_656, fun _ _ ↦ walk_659,
      fun _ _ ↦ walk_660, fun _ _ ↦ walk_661, fun _ _ ↦ walk_663, fun _ _ ↦ walk_664,
      fun _ _ ↦ walk_665, fun _ _ ↦ walk_666, fun _ _ ↦ walk_667, fun _ _ ↦ walk_668,
      fun _ _ ↦ walk_688, fun _ _ ↦ walk_689, fun _ _ ↦ walk_690, fun _ _ ↦ walk_691,
      fun _ _ ↦ walk_695, fun _ _ ↦ walk_696, fun _ _ ↦ walk_697, fun _ _ ↦ walk_698,
      fun _ _ ↦ walk_701, fun _ _ ↦ walk_702, fun _ _ ↦ walk_703, fun _ _ ↦ walk_705,
      fun _ _ ↦ walk_706, fun _ _ ↦ walk_707, fun _ _ ↦ walk_708, fun _ _ ↦ walk_709,
      fun _ _ ↦ walk_710, fun _ _ ↦ walk_729, fun _ _ ↦ walk_730, fun _ _ ↦ walk_731,
      fun _ _ ↦ walk_732, fun _ _ ↦ walk_736, fun _ _ ↦ walk_737, fun _ _ ↦ walk_738,
      fun _ _ ↦ walk_739, fun _ _ ↦ walk_742, fun _ _ ↦ walk_743, fun _ _ ↦ walk_744,
      fun _ _ ↦ walk_746, fun _ _ ↦ walk_747, fun _ _ ↦ walk_748, fun _ _ ↦ walk_749,
      fun _ _ ↦ walk_750, fun _ _ ↦ walk_751, fun _ _ ↦ walk_770, fun _ _ ↦ walk_771,
      fun _ _ ↦ walk_772, fun _ _ ↦ walk_773, fun _ _ ↦ walk_777, fun _ _ ↦ walk_778,
      fun _ _ ↦ walk_779, fun _ _ ↦ walk_780, fun _ _ ↦ walk_782, fun _ _ ↦ walk_783,
      fun _ _ ↦ walk_784, fun _ _ ↦ walk_786, fun _ _ ↦ walk_787, fun _ _ ↦ walk_788,
      fun _ _ ↦ walk_789, fun _ _ ↦ walk_790, fun _ _ ↦ walk_791, fun _ _ ↦ walk_810,
      fun _ _ ↦ walk_811, fun _ _ ↦ walk_812, fun _ _ ↦ walk_813, fun _ _ ↦ walk_817,
      fun _ _ ↦ walk_818, fun _ _ ↦ walk_819, fun _ _ ↦ walk_820, fun _ _ ↦ walk_823,
      fun _ _ ↦ walk_824, fun _ _ ↦ walk_825, fun _ _ ↦ walk_827, fun _ _ ↦ walk_828,
      fun _ _ ↦ walk_829, fun _ _ ↦ walk_831, fun _ _ ↦ walk_832, fun _ _ ↦ walk_833,
      fun _ _ ↦ walk_834, fun _ _ ↦ walk_835, fun _ _ ↦ walk_836, fun _ _ ↦ walk_858,
      fun _ _ ↦ walk_859, fun _ _ ↦ walk_860, fun _ _ ↦ walk_861, fun _ _ ↦ walk_865,
      fun _ _ ↦ walk_866, fun _ _ ↦ walk_867, fun _ _ ↦ walk_868, fun _ _ ↦ walk_871,
      fun _ _ ↦ walk_872, fun _ _ ↦ walk_873, fun _ _ ↦ walk_875, fun _ _ ↦ walk_876,
      fun _ _ ↦ walk_877, fun _ _ ↦ walk_878, fun _ _ ↦ walk_879, fun _ _ ↦ walk_880,
      fun _ _ ↦ walk_881, fun _ _ ↦ walk_882, fun _ _ ↦ walk_883, fun _ _ ↦ walk_904,
      fun _ _ ↦ walk_905, fun _ _ ↦ walk_906, fun _ _ ↦ walk_907, fun _ _ ↦ walk_911,
      fun _ _ ↦ walk_912, fun _ _ ↦ walk_913, fun _ _ ↦ walk_914, fun _ _ ↦ walk_917,
      fun _ _ ↦ walk_918, fun _ _ ↦ walk_919, fun _ _ ↦ walk_921, fun _ _ ↦ walk_922,
      fun _ _ ↦ walk_923, fun _ _ ↦ walk_924, fun _ _ ↦ walk_925, fun _ _ ↦ walk_927,
      fun _ _ ↦ walk_928, fun _ _ ↦ walk_929, fun _ _ ↦ walk_1010, fun _ _ ↦ walk_1012,
      fun _ _ ↦ walk_1014, fun _ _ ↦ walk_1016, fun _ _ ↦ walk_1023, fun _ _ ↦ walk_1024,
      fun _ _ ↦ walk_1025, fun _ _ ↦ walk_1026, fun _ _ ↦ walk_1033, fun _ _ ↦ walk_1039,
      fun _ _ ↦ walk_1040, fun _ _ ↦ walk_1041, fun _ _ ↦ walk_1042, fun _ _ ↦ walk_1071,
      fun _ _ ↦ walk_1072, fun _ _ ↦ walk_1077, fun _ _ ↦ walk_1080, fun _ _ ↦ walk_1081,
      fun _ _ ↦ walk_1082, fun _ _ ↦ walk_1083, fun _ _ ↦ walk_1111, fun _ _ ↦ walk_1112,
      fun _ _ ↦ walk_1117, fun _ _ ↦ walk_1120, fun _ _ ↦ walk_1121, fun _ _ ↦ walk_1122,
      fun _ _ ↦ walk_1123, fun _ _ ↦ walk_1151, fun _ _ ↦ walk_1152, fun _ _ ↦ walk_1157,
      fun _ _ ↦ walk_1160, fun _ _ ↦ walk_1161, fun _ _ ↦ walk_1162, fun _ _ ↦ walk_1163,
      fun _ _ ↦ walk_1191, fun _ _ ↦ walk_1192, fun _ _ ↦ walk_1196, fun _ _ ↦ walk_1200,
      fun _ _ ↦ walk_1201, fun _ _ ↦ walk_1202, fun _ _ ↦ walk_1237, fun _ _ ↦ walk_1238,
      fun _ _ ↦ walk_1242, fun _ _ ↦ walk_1246, fun _ _ ↦ walk_1247, fun _ _ ↦ walk_1248,
      fun _ _ ↦ walk_1281, fun _ _ ↦ walk_1282, fun _ _ ↦ walk_1286, fun _ _ ↦ walk_1290,
      fun _ _ ↦ walk_1291, fun _ _ ↦ walk_1292, fun _ _ ↦ walk_1325, fun _ _ ↦ walk_1326,
      fun _ _ ↦ walk_1330, fun _ _ ↦ walk_1333, fun _ _ ↦ walk_1334, fun _ _ ↦ walk_1335,
      fun _ _ ↦ walk_1368, fun _ _ ↦ walk_1369, fun _ _ ↦ walk_1373, fun _ _ ↦ walk_1378,
      fun _ _ ↦ walk_1379, fun _ _ ↦ walk_1380, fun _ _ ↦ walk_1418, fun _ _ ↦ walk_1419,
      fun _ _ ↦ walk_1423, fun _ _ ↦ walk_1427, fun _ _ ↦ walk_1428, fun _ _ ↦ walk_1429,
      fun _ _ ↦ walk_1465, fun _ _ ↦ walk_1466, fun _ _ ↦ walk_1470, fun _ _ ↦ walk_1475,
      fun _ _ ↦ walk_1476, fun _ _ ↦ walk_1477, fun _ _ ↦ walk_1508, fun _ _ ↦ walk_1509,
      fun _ _ ↦ walk_1510, fun _ _ ↦ walk_1511, fun _ _ ↦ walk_1512, fun _ _ ↦ walk_1513,
      fun _ _ ↦ walk_1514, fun _ _ ↦ walk_1515, fun _ _ ↦ walk_1516, fun _ _ ↦ walk_1517,
      fun _ _ ↦ walk_1518, fun _ _ ↦ walk_1519, fun _ _ ↦ walk_1520, fun _ _ ↦ walk_1521,
      fun _ _ ↦ walk_1522, fun _ _ ↦ walk_1523, fun _ _ ↦ walk_1524, fun _ _ ↦ walk_1525,
      fun _ _ ↦ walk_1526, fun _ _ ↦ walk_1527, fun _ _ ↦ walk_1528, fun _ _ ↦ walk_1529,
      fun _ _ ↦ walk_1530, fun _ _ ↦ walk_1531, fun _ _ ↦ walk_1532, fun _ _ ↦ walk_1533,
      fun _ _ ↦ walk_1534, fun _ _ ↦ walk_1535, fun _ _ ↦ walk_1536, fun _ _ ↦ walk_1537,
      fun _ _ ↦ walk_1538, fun _ _ ↦ walk_1539, fun _ _ ↦ walk_1540, fun _ _ ↦ walk_1541,
      fun _ _ ↦ walk_1542, fun _ _ ↦ walk_1543, fun _ _ ↦ walk_1544, fun _ _ ↦ walk_1545,
      fun _ _ ↦ walk_1546, fun _ _ ↦ walk_1547, fun _ _ ↦ walk_1548, fun _ _ ↦ walk_1549,
      fun _ _ ↦ walk_1550, fun _ _ ↦ walk_1551, fun _ _ ↦ walk_1552, fun _ _ ↦ walk_1553,
      fun _ _ ↦ walk_1554, fun _ _ ↦ walk_1555, fun _ _ ↦ walk_1556, fun _ _ ↦ walk_1557,
      fun _ _ ↦ walk_1558, fun _ _ ↦ walk_1559, fun _ _ ↦ walk_1560, fun _ _ ↦ walk_1561,
      fun _ _ ↦ walk_1562, fun _ _ ↦ walk_1563, fun _ _ ↦ walk_1564, fun _ _ ↦ walk_1565,
      fun _ _ ↦ walk_1566, fun _ _ ↦ walk_1567, fun _ _ ↦ walk_1568, fun _ _ ↦ walk_1569,
      fun _ _ ↦ walk_1570, fun _ _ ↦ walk_1571, fun _ _ ↦ walk_1572, fun _ _ ↦ walk_1573,
      fun _ _ ↦ walk_1574, fun _ _ ↦ walk_1575, fun _ _ ↦ walk_1576, fun _ _ ↦ walk_1577,
      fun _ _ ↦ walk_1578, fun _ _ ↦ walk_1579, fun _ _ ↦ walk_1580, fun _ _ ↦ walk_1581,
      fun _ _ ↦ walk_1582, fun _ _ ↦ walk_1583, fun _ _ ↦ walk_1584, fun _ _ ↦ walk_1585,
      fun _ _ ↦ walk_1586, fun _ _ ↦ walk_1587, fun _ _ ↦ walk_1588, fun _ _ ↦ walk_1589,
      fun _ _ ↦ walk_1590, fun _ _ ↦ walk_1591, fun _ _ ↦ walk_1592, fun _ _ ↦ walk_1593,
      fun _ _ ↦ walk_1594, fun _ _ ↦ walk_1595, fun _ _ ↦ walk_1596, fun _ _ ↦ walk_1597,
      fun _ _ ↦ walk_1598, fun _ _ ↦ walk_1599, fun _ _ ↦ walk_1600, fun _ _ ↦ walk_1601⟩
  exact List.forall_iff_forall_mem.mp key

/-- **The walks' obligations, proved.** -/
theorem walkKnown_proved : WalkKnown := walkKnown_of_gkr gkrBus_cutsKnown gkrLoop_cutsKnown

end
end LeanVM.Guest.End
