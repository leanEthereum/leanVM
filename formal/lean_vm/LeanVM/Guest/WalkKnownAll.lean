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
public import LeanVM.Guest.WalkOs3
public import LeanVM.Guest.WalkWp
public import LeanVM.Guest.WalkGkr

/-!
# `WalkKnown`, proved

`walkKnown_proved : WalkKnown`: the cut obligations (`CutsKnown`) of every function of
`Checked.oblFns` but `main` (`1`) and `verify_sub` (`19`): `opening_queries`' specializations and
loops (`WalkOq0.lean` to `WalkOq3.lean`, whir's `QueriesWalk` through b2's `WalkKnown.lean`),
`open_stacked`'s sizes (`WalkOs0.lean` to `WalkOs3.lean`, at each rate's arm from that arm's
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
      fun _ _ ↦ walk_311, fun _ _ ↦ walk_312, fun _ _ ↦ walk_313, fun _ _ ↦ walk_314,
      fun _ _ ↦ walk_315, fun _ _ ↦ walk_316, fun _ _ ↦ walk_317, fun _ _ ↦ walk_318,
      fun _ _ ↦ walk_319, fun _ _ ↦ walk_320, fun _ _ ↦ walk_321, fun _ _ ↦ walk_322,
      fun _ _ ↦ walk_323, fun _ _ ↦ walk_430, fun _ _ ↦ walk_431, fun _ _ ↦ walk_432,
      fun _ _ ↦ walk_433, fun _ _ ↦ walk_440, fun _ _ ↦ walk_441, fun _ _ ↦ walk_442,
      fun _ _ ↦ walk_443, fun _ _ ↦ walk_449, fun _ _ ↦ walk_450, fun _ _ ↦ walk_451,
      fun _ _ ↦ walk_452, fun _ _ ↦ walk_458, fun _ _ ↦ walk_459, fun _ _ ↦ walk_460,
      fun _ _ ↦ walk_461, fun _ _ ↦ walk_484, fun _ _ ↦ walk_485, fun _ _ ↦ walk_486,
      fun _ _ ↦ walk_487, fun _ _ ↦ walk_492, fun _ _ ↦ walk_493, fun _ _ ↦ walk_494,
      fun _ _ ↦ walk_495, fun _ _ ↦ walk_498, fun _ _ ↦ walk_499, fun _ _ ↦ walk_500,
      fun _ _ ↦ walk_501, fun _ _ ↦ walk_503, fun _ _ ↦ walk_504, fun _ _ ↦ walk_505,
      fun _ _ ↦ walk_506, fun _ _ ↦ walk_529, fun _ _ ↦ walk_530, fun _ _ ↦ walk_531,
      fun _ _ ↦ walk_532, fun _ _ ↦ walk_537, fun _ _ ↦ walk_538, fun _ _ ↦ walk_539,
      fun _ _ ↦ walk_540, fun _ _ ↦ walk_543, fun _ _ ↦ walk_544, fun _ _ ↦ walk_545,
      fun _ _ ↦ walk_546, fun _ _ ↦ walk_549, fun _ _ ↦ walk_550, fun _ _ ↦ walk_551,
      fun _ _ ↦ walk_552, fun _ _ ↦ walk_575, fun _ _ ↦ walk_576, fun _ _ ↦ walk_577,
      fun _ _ ↦ walk_578, fun _ _ ↦ walk_583, fun _ _ ↦ walk_584, fun _ _ ↦ walk_585,
      fun _ _ ↦ walk_586, fun _ _ ↦ walk_589, fun _ _ ↦ walk_590, fun _ _ ↦ walk_591,
      fun _ _ ↦ walk_592, fun _ _ ↦ walk_595, fun _ _ ↦ walk_596, fun _ _ ↦ walk_597,
      fun _ _ ↦ walk_598, fun _ _ ↦ walk_621, fun _ _ ↦ walk_622, fun _ _ ↦ walk_623,
      fun _ _ ↦ walk_624, fun _ _ ↦ walk_628, fun _ _ ↦ walk_629, fun _ _ ↦ walk_630,
      fun _ _ ↦ walk_631, fun _ _ ↦ walk_633, fun _ _ ↦ walk_634, fun _ _ ↦ walk_635,
      fun _ _ ↦ walk_637, fun _ _ ↦ walk_638, fun _ _ ↦ walk_639, fun _ _ ↦ walk_640,
      fun _ _ ↦ walk_641, fun _ _ ↦ walk_642, fun _ _ ↦ walk_664, fun _ _ ↦ walk_665,
      fun _ _ ↦ walk_666, fun _ _ ↦ walk_667, fun _ _ ↦ walk_670, fun _ _ ↦ walk_671,
      fun _ _ ↦ walk_672, fun _ _ ↦ walk_673, fun _ _ ↦ walk_675, fun _ _ ↦ walk_676,
      fun _ _ ↦ walk_677, fun _ _ ↦ walk_679, fun _ _ ↦ walk_680, fun _ _ ↦ walk_681,
      fun _ _ ↦ walk_682, fun _ _ ↦ walk_683, fun _ _ ↦ walk_684, fun _ _ ↦ walk_706,
      fun _ _ ↦ walk_707, fun _ _ ↦ walk_708, fun _ _ ↦ walk_709, fun _ _ ↦ walk_712,
      fun _ _ ↦ walk_713, fun _ _ ↦ walk_714, fun _ _ ↦ walk_715, fun _ _ ↦ walk_717,
      fun _ _ ↦ walk_718, fun _ _ ↦ walk_719, fun _ _ ↦ walk_721, fun _ _ ↦ walk_722,
      fun _ _ ↦ walk_723, fun _ _ ↦ walk_724, fun _ _ ↦ walk_725, fun _ _ ↦ walk_726,
      fun _ _ ↦ walk_748, fun _ _ ↦ walk_749, fun _ _ ↦ walk_750, fun _ _ ↦ walk_751,
      fun _ _ ↦ walk_755, fun _ _ ↦ walk_756, fun _ _ ↦ walk_757, fun _ _ ↦ walk_758,
      fun _ _ ↦ walk_760, fun _ _ ↦ walk_761, fun _ _ ↦ walk_762, fun _ _ ↦ walk_763,
      fun _ _ ↦ walk_764, fun _ _ ↦ walk_765, fun _ _ ↦ walk_766, fun _ _ ↦ walk_767,
      fun _ _ ↦ walk_768, fun _ _ ↦ walk_789, fun _ _ ↦ walk_790, fun _ _ ↦ walk_791,
      fun _ _ ↦ walk_792, fun _ _ ↦ walk_796, fun _ _ ↦ walk_797, fun _ _ ↦ walk_798,
      fun _ _ ↦ walk_799, fun _ _ ↦ walk_801, fun _ _ ↦ walk_802, fun _ _ ↦ walk_803,
      fun _ _ ↦ walk_804, fun _ _ ↦ walk_805, fun _ _ ↦ walk_806, fun _ _ ↦ walk_808,
      fun _ _ ↦ walk_809, fun _ _ ↦ walk_810, fun _ _ ↦ walk_811, fun _ _ ↦ walk_812,
      fun _ _ ↦ walk_835, fun _ _ ↦ walk_836, fun _ _ ↦ walk_837, fun _ _ ↦ walk_838,
      fun _ _ ↦ walk_842, fun _ _ ↦ walk_843, fun _ _ ↦ walk_844, fun _ _ ↦ walk_845,
      fun _ _ ↦ walk_847, fun _ _ ↦ walk_848, fun _ _ ↦ walk_849, fun _ _ ↦ walk_850,
      fun _ _ ↦ walk_851, fun _ _ ↦ walk_852, fun _ _ ↦ walk_854, fun _ _ ↦ walk_855,
      fun _ _ ↦ walk_856, fun _ _ ↦ walk_857, fun _ _ ↦ walk_880, fun _ _ ↦ walk_881,
      fun _ _ ↦ walk_882, fun _ _ ↦ walk_883, fun _ _ ↦ walk_887, fun _ _ ↦ walk_888,
      fun _ _ ↦ walk_889, fun _ _ ↦ walk_890, fun _ _ ↦ walk_892, fun _ _ ↦ walk_893,
      fun _ _ ↦ walk_894, fun _ _ ↦ walk_896, fun _ _ ↦ walk_897, fun _ _ ↦ walk_898,
      fun _ _ ↦ walk_900, fun _ _ ↦ walk_901, fun _ _ ↦ walk_902, fun _ _ ↦ walk_903,
      fun _ _ ↦ walk_904, fun _ _ ↦ walk_905, fun _ _ ↦ walk_929, fun _ _ ↦ walk_930,
      fun _ _ ↦ walk_931, fun _ _ ↦ walk_932, fun _ _ ↦ walk_936, fun _ _ ↦ walk_937,
      fun _ _ ↦ walk_938, fun _ _ ↦ walk_939, fun _ _ ↦ walk_941, fun _ _ ↦ walk_942,
      fun _ _ ↦ walk_943, fun _ _ ↦ walk_945, fun _ _ ↦ walk_946, fun _ _ ↦ walk_947,
      fun _ _ ↦ walk_948, fun _ _ ↦ walk_949, fun _ _ ↦ walk_950, fun _ _ ↦ walk_951,
      fun _ _ ↦ walk_952, fun _ _ ↦ walk_953, fun _ _ ↦ walk_977, fun _ _ ↦ walk_978,
      fun _ _ ↦ walk_979, fun _ _ ↦ walk_980, fun _ _ ↦ walk_984, fun _ _ ↦ walk_985,
      fun _ _ ↦ walk_986, fun _ _ ↦ walk_987, fun _ _ ↦ walk_989, fun _ _ ↦ walk_990,
      fun _ _ ↦ walk_991, fun _ _ ↦ walk_993, fun _ _ ↦ walk_994, fun _ _ ↦ walk_995,
      fun _ _ ↦ walk_996, fun _ _ ↦ walk_997, fun _ _ ↦ walk_998, fun _ _ ↦ walk_1000,
      fun _ _ ↦ walk_1001, fun _ _ ↦ walk_1004, fun _ _ ↦ walk_1005, fun _ _ ↦ walk_1085,
      fun _ _ ↦ walk_1087, fun _ _ ↦ walk_1089, fun _ _ ↦ walk_1091, fun _ _ ↦ walk_1097,
      fun _ _ ↦ walk_1098, fun _ _ ↦ walk_1099, fun _ _ ↦ walk_1100, fun _ _ ↦ walk_1106,
      fun _ _ ↦ walk_1111, fun _ _ ↦ walk_1143, fun _ _ ↦ walk_1144, fun _ _ ↦ walk_1145,
      fun _ _ ↦ walk_1146, fun _ _ ↦ walk_1150, fun _ _ ↦ walk_1183, fun _ _ ↦ walk_1184,
      fun _ _ ↦ walk_1188, fun _ _ ↦ walk_1221, fun _ _ ↦ walk_1222, fun _ _ ↦ walk_1226,
      fun _ _ ↦ walk_1259, fun _ _ ↦ walk_1260, fun _ _ ↦ walk_1264, fun _ _ ↦ walk_1299,
      fun _ _ ↦ walk_1300, fun _ _ ↦ walk_1301, fun _ _ ↦ walk_1304, fun _ _ ↦ walk_1338,
      fun _ _ ↦ walk_1339, fun _ _ ↦ walk_1342, fun _ _ ↦ walk_1376, fun _ _ ↦ walk_1377,
      fun _ _ ↦ walk_1381, fun _ _ ↦ walk_1413, fun _ _ ↦ walk_1414, fun _ _ ↦ walk_1418,
      fun _ _ ↦ walk_1455, fun _ _ ↦ walk_1456, fun _ _ ↦ walk_1460, fun _ _ ↦ walk_1499,
      fun _ _ ↦ walk_1503, fun _ _ ↦ walk_1546, fun _ _ ↦ walk_1547, fun _ _ ↦ walk_1551,
      fun _ _ ↦ walk_1593, fun _ _ ↦ walk_1597, fun _ _ ↦ walk_1643, fun _ _ ↦ walk_1644,
      fun _ _ ↦ walk_1645, fun _ _ ↦ walk_1646, fun _ _ ↦ walk_1647, fun _ _ ↦ walk_1648,
      fun _ _ ↦ walk_1650, fun _ _ ↦ walk_1651, fun _ _ ↦ walk_1652, fun _ _ ↦ walk_1653,
      fun _ _ ↦ walk_1655, fun _ _ ↦ walk_1657, fun _ _ ↦ walk_1663, fun _ _ ↦ walk_1664,
      fun _ _ ↦ walk_1665, fun _ _ ↦ walk_1666, fun _ _ ↦ walk_1667, fun _ _ ↦ walk_1668,
      fun _ _ ↦ walk_1669, fun _ _ ↦ walk_1675, fun _ _ ↦ walk_1676, fun _ _ ↦ walk_1677,
      fun _ _ ↦ walk_1678, fun _ _ ↦ walk_1684, fun _ _ ↦ walk_1685, fun _ _ ↦ walk_1686,
      fun _ _ ↦ walk_1687, fun _ _ ↦ walk_1693, fun _ _ ↦ walk_1694, fun _ _ ↦ walk_1695,
      fun _ _ ↦ walk_1696, fun _ _ ↦ walk_1700, fun _ _ ↦ walk_1701, fun _ _ ↦ walk_1702,
      fun _ _ ↦ walk_1703, fun _ _ ↦ walk_1704, fun _ _ ↦ walk_1707, fun _ _ ↦ walk_1708,
      fun _ _ ↦ walk_1709, fun _ _ ↦ walk_1710, fun _ _ ↦ walk_1713, fun _ _ ↦ walk_1714,
      fun _ _ ↦ walk_1715, fun _ _ ↦ walk_1716, fun _ _ ↦ walk_1719, fun _ _ ↦ walk_1720,
      fun _ _ ↦ walk_1721, fun _ _ ↦ walk_1722, fun _ _ ↦ walk_1725, fun _ _ ↦ walk_1726,
      fun _ _ ↦ walk_1727, fun _ _ ↦ walk_1728, fun _ _ ↦ walk_1729, fun _ _ ↦ walk_1732,
      fun _ _ ↦ walk_1733, fun _ _ ↦ walk_1734, fun _ _ ↦ walk_1738, fun _ _ ↦ walk_1739,
      fun _ _ ↦ walk_1740, fun _ _ ↦ walk_1741, fun _ _ ↦ walk_1744, fun _ _ ↦ walk_1745,
      fun _ _ ↦ walk_1746, fun _ _ ↦ walk_1748, fun _ _ ↦ walk_1749, fun _ _ ↦ walk_1750,
      fun _ _ ↦ walk_1751, fun _ _ ↦ walk_1752⟩
  exact List.forall_iff_forall_mem.mp key

/-- **The walks' obligations, proved.** -/
theorem walkKnown_proved : WalkKnown := walkKnown_of_gkr gkrBus_cutsKnown gkrLoop_cutsKnown

end
end LeanVM.Guest.End
