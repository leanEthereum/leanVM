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

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **The table's entries are the specializations.** -/
theorem lpTab_ok : ∀ e ∈ lpTab, LpOk e := by
  have key : List.Forall LpOk lpTab :=
    ⟨⟨lp_418, lpl_972⟩,
      ⟨lp_419, lpl_973⟩,
      ⟨lp_420, lpl_974⟩,
      ⟨lp_421, lpl_975⟩,
      ⟨lp_428, lpl_984⟩,
      ⟨lp_429, lpl_985⟩,
      ⟨lp_430, lpl_986⟩,
      ⟨lp_431, lpl_987⟩,
      ⟨lp_438, lpl_993⟩,
      ⟨lp_439, lpl_994⟩,
      ⟨lp_440, lpl_995⟩,
      ⟨lp_441, lpl_996⟩,
      ⟨lp_447, lpl_999⟩,
      ⟨lp_448, lpl_1000⟩,
      ⟨lp_449, lpl_1001⟩,
      ⟨lp_450, lpl_1002⟩,
      ⟨lp_473, lpl_1031⟩,
      ⟨lp_474, lpl_1032⟩,
      ⟨lp_475, lpl_1033⟩,
      ⟨lp_476, lpl_1034⟩,
      ⟨lp_482, lpl_1039⟩,
      ⟨lp_483, lpl_1040⟩,
      ⟨lp_484, lpl_1041⟩,
      ⟨lp_490, lpl_1043⟩,
      ⟨lp_518, lpl_1071⟩,
      ⟨lp_519, lpl_1072⟩,
      ⟨lp_520, lpl_1073⟩,
      ⟨lp_521, lpl_1074⟩,
      ⟨lp_527, lpl_1077⟩,
      ⟨lp_528, lpl_1078⟩,
      ⟨lp_529, lpl_1079⟩,
      ⟨lp_535, lpl_1081⟩,
      ⟨lp_541, lpl_1082⟩,
      ⟨lp_564, lpl_1109⟩,
      ⟨lp_565, lpl_1110⟩,
      ⟨lp_566, lpl_1111⟩,
      ⟨lp_567, lpl_1112⟩,
      ⟨lp_573, lpl_1115⟩,
      ⟨lp_574, lpl_1116⟩,
      ⟨lp_575, lpl_1117⟩,
      ⟨lp_581, lpl_1119⟩,
      ⟨lp_587, lpl_1120⟩,
      ⟨lp_610, lpl_1147⟩,
      ⟨lp_611, lpl_1148⟩,
      ⟨lp_612, lpl_1149⟩,
      ⟨lp_613, lpl_1150⟩,
      ⟨lp_618, lpl_1153⟩,
      ⟨lp_619, lpl_1154⟩,
      ⟨lp_620, lpl_1155⟩,
      ⟨lp_625, lpl_1157⟩,
      ⟨lp_629, lpl_1158⟩,
      ⟨lp_653, lpl_1186⟩,
      ⟨lp_654, lpl_1187⟩,
      ⟨lp_655, lpl_1188⟩,
      ⟨lp_656, lpl_1189⟩,
      ⟨lp_661, lpl_1194⟩,
      ⟨lp_662, lpl_1195⟩,
      ⟨lp_667, lpl_1197⟩,
      ⟨lp_671, lpl_1198⟩,
      ⟨lp_695, lpl_1226⟩,
      ⟨lp_696, lpl_1227⟩,
      ⟨lp_697, lpl_1228⟩,
      ⟨lp_698, lpl_1229⟩,
      ⟨lp_703, lpl_1232⟩,
      ⟨lp_704, lpl_1233⟩,
      ⟨lp_709, lpl_1235⟩,
      ⟨lp_713, lpl_1236⟩,
      ⟨lp_737, lpl_1264⟩,
      ⟨lp_738, lpl_1265⟩,
      ⟨lp_739, lpl_1266⟩,
      ⟨lp_740, lpl_1267⟩,
      ⟨lp_745, lpl_1270⟩,
      ⟨lp_746, lpl_1271⟩,
      ⟨lp_747, lpl_1272⟩,
      ⟨lp_752, lpl_1274⟩,
      ⟨lp_778, lpl_1301⟩,
      ⟨lp_779, lpl_1302⟩,
      ⟨lp_780, lpl_1303⟩,
      ⟨lp_781, lpl_1304⟩,
      ⟨lp_786, lpl_1307⟩,
      ⟨lp_787, lpl_1308⟩,
      ⟨lp_788, lpl_1309⟩,
      ⟨lp_793, lpl_1311⟩,
      ⟨lp_800, lpl_1312⟩,
      ⟨lp_824, lpl_1343⟩,
      ⟨lp_825, lpl_1344⟩,
      ⟨lp_826, lpl_1345⟩,
      ⟨lp_827, lpl_1346⟩,
      ⟨lp_832, lpl_1349⟩,
      ⟨lp_833, lpl_1350⟩,
      ⟨lp_834, lpl_1351⟩,
      ⟨lp_839, lpl_1353⟩,
      ⟨lp_846, lpl_1354⟩,
      ⟨lp_869, lpl_1387⟩,
      ⟨lp_870, lpl_1388⟩,
      ⟨lp_871, lpl_1389⟩,
      ⟨lp_872, lpl_1390⟩,
      ⟨lp_877, lpl_1392⟩,
      ⟨lp_878, lpl_1393⟩,
      ⟨lp_879, lpl_1394⟩,
      ⟨lp_884, lpl_1396⟩,
      ⟨lp_888, lpl_1397⟩,
      ⟨lp_892, lpl_1398⟩⟩
  exact List.forall_iff_forall_mem.mp key

end
end LeanVM.Guest.End
