/-
  LeanVM.Guest.WalkOsTabOk

  Every entry of `lpTab` is its specialization's body and its loop's (`LpOk`), from the helpers'
  kernel checks (`B1/Whir/HelperData*.lean`).
-/

module

public import LeanVM.Guest.WalkOsPre
public import LeanVM.Guest.WalkOsTab
public import LeanVM.Guest.B1.Whir.HelperData0
public import LeanVM.Guest.B1.Whir.HelperData1
public import LeanVM.Guest.B1.Whir.HelperData2
public import LeanVM.Guest.B1.Whir.HelperData3
public import LeanVM.Guest.B1.Whir.HelperData4
public import LeanVM.Guest.B1.Whir.HelperData5
public import LeanVM.Guest.B1.Whir.HelperData6
public import LeanVM.Guest.B1.Whir.HelperData7
public import LeanVM.Guest.B1.Whir.HelperData8
public import LeanVM.Guest.B1.Whir.HelperData9
public import LeanVM.Guest.B1.Whir.HelperData10
public import LeanVM.Guest.B1.Whir.HelperData11
public import LeanVM.Guest.B1.Whir.HelperData12
public import LeanVM.Guest.B1.Whir.HelperData13
public import LeanVM.Guest.B1.Whir.HelperData14
public import LeanVM.Guest.B1.Whir.HelperData15
public import LeanVM.Guest.B1.Whir.HelperData16
public import LeanVM.Guest.B1.Whir.HelperData17
public import LeanVM.Guest.B1.Whir.HelperData18

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **The table's entries are the specializations.** -/
theorem lpTab_ok : ∀ e ∈ lpTab, LpOk e := by
  have key : List.Forall LpOk lpTab :=
    ⟨⟨lp_424, lpl_1079⟩,
      ⟨lp_425, lpl_1080⟩,
      ⟨lp_426, lpl_1081⟩,
      ⟨lp_427, lpl_1082⟩,
      ⟨lp_434, lpl_1091⟩,
      ⟨lp_435, lpl_1092⟩,
      ⟨lp_436, lpl_1093⟩,
      ⟨lp_437, lpl_1094⟩,
      ⟨lp_444, lpl_1100⟩,
      ⟨lp_445, lpl_1101⟩,
      ⟨lp_446, lpl_1102⟩,
      ⟨lp_447, lpl_1103⟩,
      ⟨lp_453, lpl_1106⟩,
      ⟨lp_454, lpl_1107⟩,
      ⟨lp_455, lpl_1108⟩,
      ⟨lp_456, lpl_1109⟩,
      ⟨lp_479, lpl_1138⟩,
      ⟨lp_480, lpl_1139⟩,
      ⟨lp_481, lpl_1140⟩,
      ⟨lp_482, lpl_1141⟩,
      ⟨lp_488, lpl_1146⟩,
      ⟨lp_489, lpl_1147⟩,
      ⟨lp_490, lpl_1148⟩,
      ⟨lp_496, lpl_1150⟩,
      ⟨lp_524, lpl_1178⟩,
      ⟨lp_525, lpl_1179⟩,
      ⟨lp_526, lpl_1180⟩,
      ⟨lp_527, lpl_1181⟩,
      ⟨lp_533, lpl_1184⟩,
      ⟨lp_534, lpl_1185⟩,
      ⟨lp_535, lpl_1186⟩,
      ⟨lp_541, lpl_1188⟩,
      ⟨lp_547, lpl_1189⟩,
      ⟨lp_570, lpl_1216⟩,
      ⟨lp_571, lpl_1217⟩,
      ⟨lp_572, lpl_1218⟩,
      ⟨lp_573, lpl_1219⟩,
      ⟨lp_579, lpl_1222⟩,
      ⟨lp_580, lpl_1223⟩,
      ⟨lp_581, lpl_1224⟩,
      ⟨lp_587, lpl_1226⟩,
      ⟨lp_593, lpl_1227⟩,
      ⟨lp_616, lpl_1254⟩,
      ⟨lp_617, lpl_1255⟩,
      ⟨lp_618, lpl_1256⟩,
      ⟨lp_619, lpl_1257⟩,
      ⟨lp_624, lpl_1260⟩,
      ⟨lp_625, lpl_1261⟩,
      ⟨lp_626, lpl_1262⟩,
      ⟨lp_631, lpl_1264⟩,
      ⟨lp_635, lpl_1265⟩,
      ⟨lp_659, lpl_1293⟩,
      ⟨lp_660, lpl_1294⟩,
      ⟨lp_661, lpl_1295⟩,
      ⟨lp_662, lpl_1296⟩,
      ⟨lp_667, lpl_1301⟩,
      ⟨lp_668, lpl_1302⟩,
      ⟨lp_673, lpl_1304⟩,
      ⟨lp_677, lpl_1305⟩,
      ⟨lp_701, lpl_1333⟩,
      ⟨lp_702, lpl_1334⟩,
      ⟨lp_703, lpl_1335⟩,
      ⟨lp_704, lpl_1336⟩,
      ⟨lp_709, lpl_1339⟩,
      ⟨lp_710, lpl_1340⟩,
      ⟨lp_715, lpl_1342⟩,
      ⟨lp_719, lpl_1343⟩,
      ⟨lp_743, lpl_1371⟩,
      ⟨lp_744, lpl_1372⟩,
      ⟨lp_745, lpl_1373⟩,
      ⟨lp_746, lpl_1374⟩,
      ⟨lp_751, lpl_1377⟩,
      ⟨lp_752, lpl_1378⟩,
      ⟨lp_753, lpl_1379⟩,
      ⟨lp_758, lpl_1381⟩,
      ⟨lp_784, lpl_1408⟩,
      ⟨lp_785, lpl_1409⟩,
      ⟨lp_786, lpl_1410⟩,
      ⟨lp_787, lpl_1411⟩,
      ⟨lp_792, lpl_1414⟩,
      ⟨lp_793, lpl_1415⟩,
      ⟨lp_794, lpl_1416⟩,
      ⟨lp_799, lpl_1418⟩,
      ⟨lp_806, lpl_1419⟩,
      ⟨lp_830, lpl_1450⟩,
      ⟨lp_831, lpl_1451⟩,
      ⟨lp_832, lpl_1452⟩,
      ⟨lp_833, lpl_1453⟩,
      ⟨lp_838, lpl_1456⟩,
      ⟨lp_839, lpl_1457⟩,
      ⟨lp_840, lpl_1458⟩,
      ⟨lp_845, lpl_1460⟩,
      ⟨lp_852, lpl_1461⟩,
      ⟨lp_875, lpl_1494⟩,
      ⟨lp_876, lpl_1495⟩,
      ⟨lp_877, lpl_1496⟩,
      ⟨lp_878, lpl_1497⟩,
      ⟨lp_883, lpl_1499⟩,
      ⟨lp_884, lpl_1500⟩,
      ⟨lp_885, lpl_1501⟩,
      ⟨lp_890, lpl_1503⟩,
      ⟨lp_894, lpl_1504⟩,
      ⟨lp_898, lpl_1505⟩,
      ⟨lp_924, lpl_1541⟩,
      ⟨lp_925, lpl_1542⟩,
      ⟨lp_926, lpl_1543⟩,
      ⟨lp_927, lpl_1544⟩,
      ⟨lp_932, lpl_1547⟩,
      ⟨lp_933, lpl_1548⟩,
      ⟨lp_934, lpl_1549⟩,
      ⟨lp_939, lpl_1551⟩,
      ⟨lp_943, lpl_1552⟩,
      ⟨lp_972, lpl_1588⟩,
      ⟨lp_973, lpl_1589⟩,
      ⟨lp_974, lpl_1590⟩,
      ⟨lp_975, lpl_1591⟩,
      ⟨lp_980, lpl_1593⟩,
      ⟨lp_981, lpl_1594⟩,
      ⟨lp_982, lpl_1595⟩,
      ⟨lp_987, lpl_1597⟩,
      ⟨lp_991, lpl_1598⟩,
      ⟨lp_998, lpl_1599⟩⟩
  exact List.forall_iff_forall_mem.mp key

end
end LeanVM.Guest.End
