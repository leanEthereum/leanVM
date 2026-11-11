/-
  LeanVM.Guest.WalkKnownAll

  The walks' obligations, proved: every function the certificates hand something on at its cuts,
  but `main` and `verify_sub`.
-/

module

public import LeanVM.Guest.WalkLq0
public import LeanVM.Guest.WalkLq1
public import LeanVM.Guest.WalkLq2
public import LeanVM.Guest.WalkLq3
public import LeanVM.Guest.WalkOq0
public import LeanVM.Guest.WalkOq1
public import LeanVM.Guest.WalkOq2
public import LeanVM.Guest.WalkOq3
public import LeanVM.Guest.WalkOs0
public import LeanVM.Guest.WalkOs1
public import LeanVM.Guest.WalkOs2
public import LeanVM.Guest.WalkWp
public import LeanVM.Guest.WalkGkr

/-!
# `WalkKnown`, proved

`walkKnown_proved : WalkKnown`: the cut obligations (`CutsKnown`) of every function of
`Checked.oblFns` but `main` (`1`) and `verify_sub` (`19`): `opening_queries`' specializations and
loops (`WalkOq0.lean` to `WalkOq3.lean`, whir's `QueriesWalk` through b2's `WalkKnown.lean`),
`open_stacked`'s sizes (`WalkOs0.lean` to `WalkOs2.lean`, at each rate's arm from that arm's
`level_positions` decodes, `WalkOsPre.lean`), `level_queries`' specializations (`WalkLq0.lean` to
`WalkLq3.lean`, from their windows' tag), `walk_path`'s specializations (`WalkWp.lean`, from their windows' tag),
and `verify_bus_gkr` (`10`) and its layer loop `__loop6` (`90`), whose
obligations (the layers' parities, `GkrPar`) the gkr track proves (`WalkGkr.lean`;
`walkKnown_of_gkr`).
-/

namespace LeanVM.Guest.End

@[expose] public section

set_option maxRecDepth 4000 in
/-- **The walks' obligations**, given `verify_bus_gkr`'s and its layer loop's. -/
theorem walkKnown_of_gkr (hBus : CutsKnown 10) (hLoop : CutsKnown 90) : WalkKnown := by
  -- One conjunct per function of `Checked.oblFns`, in order: linear, where `rcases` over the
  -- membership disjunction is quadratic.
  have key : List.Forall (fun j ↦ j ≠ 1 → j ≠ 19 → CutsKnown j) Checked.oblFns :=
    ⟨fun h _ ↦ absurd rfl h, fun _ _ ↦ hBus, fun _ h ↦ absurd rfl h, fun _ _ ↦ hLoop,
      fun _ _ ↦ walk_307, fun _ _ ↦ walk_308, fun _ _ ↦ walk_309, fun _ _ ↦ walk_310,
      fun _ _ ↦ walk_311, fun _ _ ↦ walk_312, fun _ _ ↦ walk_313, fun _ _ ↦ walk_314,
      fun _ _ ↦ walk_315, fun _ _ ↦ walk_316, fun _ _ ↦ walk_317, fun _ _ ↦ walk_424,
      fun _ _ ↦ walk_425, fun _ _ ↦ walk_426, fun _ _ ↦ walk_427, fun _ _ ↦ walk_434,
      fun _ _ ↦ walk_435, fun _ _ ↦ walk_436, fun _ _ ↦ walk_437, fun _ _ ↦ walk_443,
      fun _ _ ↦ walk_444, fun _ _ ↦ walk_445, fun _ _ ↦ walk_446, fun _ _ ↦ walk_452,
      fun _ _ ↦ walk_453, fun _ _ ↦ walk_454, fun _ _ ↦ walk_455, fun _ _ ↦ walk_478,
      fun _ _ ↦ walk_479, fun _ _ ↦ walk_480, fun _ _ ↦ walk_481, fun _ _ ↦ walk_486,
      fun _ _ ↦ walk_487, fun _ _ ↦ walk_488, fun _ _ ↦ walk_489, fun _ _ ↦ walk_492,
      fun _ _ ↦ walk_493, fun _ _ ↦ walk_494, fun _ _ ↦ walk_495, fun _ _ ↦ walk_497,
      fun _ _ ↦ walk_498, fun _ _ ↦ walk_499, fun _ _ ↦ walk_500, fun _ _ ↦ walk_523,
      fun _ _ ↦ walk_524, fun _ _ ↦ walk_525, fun _ _ ↦ walk_526, fun _ _ ↦ walk_531,
      fun _ _ ↦ walk_532, fun _ _ ↦ walk_533, fun _ _ ↦ walk_534, fun _ _ ↦ walk_537,
      fun _ _ ↦ walk_538, fun _ _ ↦ walk_539, fun _ _ ↦ walk_540, fun _ _ ↦ walk_543,
      fun _ _ ↦ walk_544, fun _ _ ↦ walk_545, fun _ _ ↦ walk_546, fun _ _ ↦ walk_569,
      fun _ _ ↦ walk_570, fun _ _ ↦ walk_571, fun _ _ ↦ walk_572, fun _ _ ↦ walk_577,
      fun _ _ ↦ walk_578, fun _ _ ↦ walk_579, fun _ _ ↦ walk_580, fun _ _ ↦ walk_583,
      fun _ _ ↦ walk_584, fun _ _ ↦ walk_585, fun _ _ ↦ walk_586, fun _ _ ↦ walk_589,
      fun _ _ ↦ walk_590, fun _ _ ↦ walk_591, fun _ _ ↦ walk_592, fun _ _ ↦ walk_615,
      fun _ _ ↦ walk_616, fun _ _ ↦ walk_617, fun _ _ ↦ walk_618, fun _ _ ↦ walk_622,
      fun _ _ ↦ walk_623, fun _ _ ↦ walk_624, fun _ _ ↦ walk_625, fun _ _ ↦ walk_627,
      fun _ _ ↦ walk_628, fun _ _ ↦ walk_629, fun _ _ ↦ walk_631, fun _ _ ↦ walk_632,
      fun _ _ ↦ walk_633, fun _ _ ↦ walk_634, fun _ _ ↦ walk_635, fun _ _ ↦ walk_636,
      fun _ _ ↦ walk_658, fun _ _ ↦ walk_659, fun _ _ ↦ walk_660, fun _ _ ↦ walk_661,
      fun _ _ ↦ walk_664, fun _ _ ↦ walk_665, fun _ _ ↦ walk_666, fun _ _ ↦ walk_667,
      fun _ _ ↦ walk_669, fun _ _ ↦ walk_670, fun _ _ ↦ walk_671, fun _ _ ↦ walk_673,
      fun _ _ ↦ walk_674, fun _ _ ↦ walk_675, fun _ _ ↦ walk_676, fun _ _ ↦ walk_677,
      fun _ _ ↦ walk_678, fun _ _ ↦ walk_700, fun _ _ ↦ walk_701, fun _ _ ↦ walk_702,
      fun _ _ ↦ walk_703, fun _ _ ↦ walk_706, fun _ _ ↦ walk_707, fun _ _ ↦ walk_708,
      fun _ _ ↦ walk_709, fun _ _ ↦ walk_711, fun _ _ ↦ walk_712, fun _ _ ↦ walk_713,
      fun _ _ ↦ walk_715, fun _ _ ↦ walk_716, fun _ _ ↦ walk_717, fun _ _ ↦ walk_718,
      fun _ _ ↦ walk_719, fun _ _ ↦ walk_720, fun _ _ ↦ walk_742, fun _ _ ↦ walk_743,
      fun _ _ ↦ walk_744, fun _ _ ↦ walk_745, fun _ _ ↦ walk_749, fun _ _ ↦ walk_750,
      fun _ _ ↦ walk_751, fun _ _ ↦ walk_752, fun _ _ ↦ walk_754, fun _ _ ↦ walk_755,
      fun _ _ ↦ walk_756, fun _ _ ↦ walk_757, fun _ _ ↦ walk_758, fun _ _ ↦ walk_759,
      fun _ _ ↦ walk_760, fun _ _ ↦ walk_761, fun _ _ ↦ walk_762, fun _ _ ↦ walk_783,
      fun _ _ ↦ walk_784, fun _ _ ↦ walk_785, fun _ _ ↦ walk_786, fun _ _ ↦ walk_790,
      fun _ _ ↦ walk_791, fun _ _ ↦ walk_792, fun _ _ ↦ walk_793, fun _ _ ↦ walk_795,
      fun _ _ ↦ walk_796, fun _ _ ↦ walk_797, fun _ _ ↦ walk_798, fun _ _ ↦ walk_799,
      fun _ _ ↦ walk_800, fun _ _ ↦ walk_802, fun _ _ ↦ walk_803, fun _ _ ↦ walk_804,
      fun _ _ ↦ walk_805, fun _ _ ↦ walk_806, fun _ _ ↦ walk_829, fun _ _ ↦ walk_830,
      fun _ _ ↦ walk_831, fun _ _ ↦ walk_832, fun _ _ ↦ walk_836, fun _ _ ↦ walk_837,
      fun _ _ ↦ walk_838, fun _ _ ↦ walk_839, fun _ _ ↦ walk_841, fun _ _ ↦ walk_842,
      fun _ _ ↦ walk_843, fun _ _ ↦ walk_844, fun _ _ ↦ walk_845, fun _ _ ↦ walk_846,
      fun _ _ ↦ walk_848, fun _ _ ↦ walk_849, fun _ _ ↦ walk_850, fun _ _ ↦ walk_851,
      fun _ _ ↦ walk_874, fun _ _ ↦ walk_875, fun _ _ ↦ walk_876, fun _ _ ↦ walk_877,
      fun _ _ ↦ walk_881, fun _ _ ↦ walk_882, fun _ _ ↦ walk_883, fun _ _ ↦ walk_884,
      fun _ _ ↦ walk_886, fun _ _ ↦ walk_887, fun _ _ ↦ walk_888, fun _ _ ↦ walk_890,
      fun _ _ ↦ walk_891, fun _ _ ↦ walk_892, fun _ _ ↦ walk_894, fun _ _ ↦ walk_895,
      fun _ _ ↦ walk_896, fun _ _ ↦ walk_897, fun _ _ ↦ walk_898, fun _ _ ↦ walk_899,
      fun _ _ ↦ walk_978, fun _ _ ↦ walk_980, fun _ _ ↦ walk_982, fun _ _ ↦ walk_984,
      fun _ _ ↦ walk_990, fun _ _ ↦ walk_991, fun _ _ ↦ walk_992, fun _ _ ↦ walk_993,
      fun _ _ ↦ walk_999, fun _ _ ↦ walk_1004, fun _ _ ↦ walk_1036, fun _ _ ↦ walk_1037,
      fun _ _ ↦ walk_1038, fun _ _ ↦ walk_1039, fun _ _ ↦ walk_1043, fun _ _ ↦ walk_1076,
      fun _ _ ↦ walk_1077, fun _ _ ↦ walk_1081, fun _ _ ↦ walk_1114, fun _ _ ↦ walk_1115,
      fun _ _ ↦ walk_1119, fun _ _ ↦ walk_1152, fun _ _ ↦ walk_1153, fun _ _ ↦ walk_1157,
      fun _ _ ↦ walk_1192, fun _ _ ↦ walk_1193, fun _ _ ↦ walk_1194, fun _ _ ↦ walk_1197,
      fun _ _ ↦ walk_1231, fun _ _ ↦ walk_1232, fun _ _ ↦ walk_1235, fun _ _ ↦ walk_1269,
      fun _ _ ↦ walk_1270, fun _ _ ↦ walk_1274, fun _ _ ↦ walk_1306, fun _ _ ↦ walk_1307,
      fun _ _ ↦ walk_1311, fun _ _ ↦ walk_1348, fun _ _ ↦ walk_1349, fun _ _ ↦ walk_1353,
      fun _ _ ↦ walk_1392, fun _ _ ↦ walk_1396, fun _ _ ↦ walk_1439, fun _ _ ↦ walk_1440,
      fun _ _ ↦ walk_1441, fun _ _ ↦ walk_1442, fun _ _ ↦ walk_1443, fun _ _ ↦ walk_1444,
      fun _ _ ↦ walk_1446, fun _ _ ↦ walk_1447, fun _ _ ↦ walk_1448, fun _ _ ↦ walk_1449,
      fun _ _ ↦ walk_1451, fun _ _ ↦ walk_1453, fun _ _ ↦ walk_1459, fun _ _ ↦ walk_1460,
      fun _ _ ↦ walk_1461, fun _ _ ↦ walk_1462, fun _ _ ↦ walk_1463, fun _ _ ↦ walk_1464,
      fun _ _ ↦ walk_1465, fun _ _ ↦ walk_1471, fun _ _ ↦ walk_1472, fun _ _ ↦ walk_1473,
      fun _ _ ↦ walk_1474, fun _ _ ↦ walk_1480, fun _ _ ↦ walk_1481, fun _ _ ↦ walk_1482,
      fun _ _ ↦ walk_1483, fun _ _ ↦ walk_1489, fun _ _ ↦ walk_1490, fun _ _ ↦ walk_1491,
      fun _ _ ↦ walk_1492, fun _ _ ↦ walk_1496, fun _ _ ↦ walk_1497, fun _ _ ↦ walk_1498,
      fun _ _ ↦ walk_1499, fun _ _ ↦ walk_1500, fun _ _ ↦ walk_1503, fun _ _ ↦ walk_1504,
      fun _ _ ↦ walk_1505, fun _ _ ↦ walk_1506, fun _ _ ↦ walk_1509, fun _ _ ↦ walk_1510,
      fun _ _ ↦ walk_1511, fun _ _ ↦ walk_1512, fun _ _ ↦ walk_1515, fun _ _ ↦ walk_1516,
      fun _ _ ↦ walk_1517, fun _ _ ↦ walk_1518, fun _ _ ↦ walk_1521, fun _ _ ↦ walk_1522,
      fun _ _ ↦ walk_1523, fun _ _ ↦ walk_1524, fun _ _ ↦ walk_1525, fun _ _ ↦ walk_1528,
      fun _ _ ↦ walk_1529, fun _ _ ↦ walk_1530, fun _ _ ↦ walk_1532, fun _ _ ↦ walk_1533,
      fun _ _ ↦ walk_1534, fun _ _ ↦ walk_1535⟩
  exact List.forall_iff_forall_mem.mp key

/-- **The walks' obligations, proved.** -/
theorem walkKnown_proved : WalkKnown := walkKnown_of_gkr gkrBus_cutsKnown gkrLoop_cutsKnown

end
end LeanVM.Guest.End
