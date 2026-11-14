/-
  LeanVM.Guest.Backend.Sound.Obl.GuestTab

  The guest's preconditions and postconditions for the analysis: the weakest the selectors need.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.GuestX
public import LeanVM.Guest.Renumber

/-!
# The guest's table

What each guest function asks of its callers and promises them, in the analysis' terms
(`Obl.Sig`, indices into the arguments and, for `post`, into the arguments then the returns).
Every entry is what a selector of the function, or of a function it is passed to, needs and no
more; the existing certificates' `Sig.pre`, `Sig.mem`, `Sig.post` for the same functions are the
same bounds at frame offsets (`2 + i`).

* `verify_tables`: argument `9` below `g^34` (dispatched on), the word at argument `10` below
  `g^34` (`dims_g[0]`, dispatched on);
* `check_opening_terminal`: the eight words at argument `8` (`kappa_base`) below its arms;
* `child_claim_list_any`, `child_claim_list_mono`: argument `6` below `g^17`;
* `open_stacked__L0` to `__L10`: argument `0` below `g^4`, argument `10` (`tabs`) in relation `1`,
  the window table (B1's `WinTabs`), which its `level_positions` read;
* `walk_path__*`: the words at argument `2` (the path's windows) its `match`es read, if read, below
  `g^64`;
* `list_split`: return `2` below `g^17`; `log2_ceil_in_the_exponent__L0_L34`: return `0` below
  `g^34`; `da_row_shape`: its argument `1` below `g^11` (it range-checks it);
* relation `0`, the exponent table and its window section (B1's `ExpTables`, `ExpWinTab`):
  `exponent_tables` returns one, `main_loop4` (compiled `__loop4`) takes it as argument `14` and
  `verify_sub` as argument `4`, where B1's bounds on `dims_g` and `kappa_base`
  (`vsDimsKnown0_holds`, `vsKnown_holds`) and its window table read it;
* `ext`: the functions of `xTab` (`Obl.GuestX`), whose preconditions are relations between their
  arguments and memory, not of the table's form.

`pows`: `g^255`, the bound of `main_loop2`'s (compiled `__loop2`) range checks.
-/

namespace LeanVM.Guest.Backend.Obl

@[expose] public section

/-- **The guest's table.** Every key is a literal: comparing strings is the costly step of
evaluating the analysis in the kernel. -/
def guestTab : Tab where
  sigs := [
    ("verify_tables", { pre := [(9, 34)], mem := [(10, 0, 34)] }),
    ("check_opening_terminal", { mem := [(8, 0, 1), (8, 1, 31), (8, 2, 31), (8, 3, 31),
      (8, 4, 31), (8, 5, 31), (8, 6, 31), (8, 7, 25)] }),
    ("child_claim_list_any", { pre := [(6, 17)] }),
    ("child_claim_list_mono", { pre := [(6, 17)] }),
    ("list_split", { post := [(3, 17)] }),
    ("log2_ceil_in_the_exponent__L0_L34", { post := [(2, 34)] }),
    ("da_row_shape", { post := [(1, 11)] }),
    ("exponent_tables", { xpost := [(0, 0)] }),
    ("__loop4", { xpre := [(14, 0)] }),
    ("verify_sub", { xpre := [(4, 0)] }),
    ("open_stacked__L0", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L1", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L2", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L3", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L4", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L5", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L6", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L7", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L8", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L9", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("open_stacked__L10", { pre := [(0, 4)], xpre := [(10, 1)] }),
    ("walk_path__L6_L6", { mem := [(2, 0, 64)] }),
    ("walk_path__L6_L7", { mem := [(2, 0, 64)] }),
    ("walk_path__L12_L2", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L3", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L4", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L5", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L6", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L7", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L8", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L18_L2", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L3", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L4", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L5", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L6", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L7", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L24_L2", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64), (2, 3, 64)] }),
    ("walk_path__L24_L3", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64), (2, 3, 64)] }),
    ("walk_path__L24_L4", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64), (2, 3, 64)] })] ++
    xTab.map fun p => (p.1, { ext := true })
  pows := [(9223372036854810629, 255)]

/-- The functions (by index in `coreProgram`) the analysis checks with `ext` sites and facts
(`chkFnX`) instead of `chkFn`: `verify_bus_gkr` (9) and `verify_bus_gkr_loop0` (`__loop6`, 90),
`open_stacked__L0` to `__L10`, the `191` `level_queries` specializations, the `76` `opening_queries`
specializations and their `76` loop helpers, the callers of `ext` functions and those whose
selectors their own `ext` precondition bounds. -/
def guestXIdx : List Nat :=
  [9, 90, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 467, 468, 469, 470, 477, 478, 479,
  480, 486, 487, 488, 489, 494, 495, 496, 497, 516, 517, 518, 519, 525, 526, 527, 528, 532, 533,
  534, 535, 537, 538, 539, 540, 559, 560, 561, 562, 568, 569, 570, 571, 574, 575, 576, 577, 580,
  581, 582, 583, 602, 603, 604, 605, 611, 612, 613, 614, 617, 618, 619, 620, 623, 624, 625, 626,
  645, 646, 647, 648, 652, 653, 654, 655, 658, 659, 660, 662, 663, 664, 665, 666, 667, 687, 688,
  689, 690, 694, 695, 696, 697, 700, 701, 702, 704, 705, 706, 707, 708, 709, 728, 729, 730, 731,
  735, 736, 737, 738, 741, 742, 743, 745, 746, 747, 748, 749, 750, 769, 770, 771, 772, 776, 777,
  778, 779, 781, 782, 783, 785, 786, 787, 788, 789, 790, 809, 810, 811, 812, 816, 817, 818, 819,
  822, 823, 824, 826, 827, 828, 830, 831, 832, 833, 834, 835, 857, 858, 859, 860, 864, 865, 866,
  867, 870, 871, 872, 874, 875, 876, 877, 878, 879, 880, 881, 882, 903, 904, 905, 906, 910, 911,
  912, 913, 916, 917, 918, 920, 921, 922, 923, 924, 926, 927, 928, 1009, 1011, 1013, 1015, 1022,
  1023, 1024, 1025, 1032, 1038, 1039, 1040, 1041, 1070, 1071, 1076, 1079, 1080, 1081, 1082, 1110,
  1111, 1116, 1119, 1120, 1121, 1122, 1150, 1151, 1156, 1159, 1160, 1161, 1162, 1190, 1191, 1195,
  1199, 1200, 1201, 1236, 1237, 1241, 1245, 1246, 1247, 1280, 1281, 1285, 1289, 1290, 1291, 1324,
  1325, 1329, 1332, 1333, 1334, 1367, 1368, 1372, 1377, 1378, 1379, 1417, 1418, 1422, 1426, 1427,
  1428, 1464, 1465, 1469, 1474, 1475, 1476, 1508, 1510, 1512, 1514, 1515, 1516, 1517, 1518, 1519,
  1520, 1521, 1522, 1523, 1524, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1534, 1535, 1536, 1537,
  1538, 1539, 1540, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1550, 1551, 1552, 1553, 1554, 1555,
  1557, 1558, 1559, 1560, 1561, 1562, 1564, 1565, 1566, 1567, 1568, 1569, 1571, 1572, 1573, 1574,
  1575, 1576, 1578, 1579, 1580, 1581, 1582, 1583, 1585, 1586, 1587, 1588, 1589, 1590, 1592, 1593,
  1594, 1595, 1596]

/-- `verify_sub`, whose calls of `verify_tables` and `check_opening_terminal` take B1's bounds on
`dims_g` and `kappa_base` as facts (`vsFacts`). -/
def vsIdx : Nat := 18

/-- The functions the analysis without facts does not cover. -/
def guestSkip (j : Nat) : Bool := j == vsIdx || guestXIdx.contains j

/-- `kappa_base`'s bounds (`lean_ethereum.py:3561-3569`): `kb[0] = g^0`, the memory's log and the
six tables' heights below `g^31`, keccak's `τ` below `g^25`. -/
def kbBound (c : Nat) : Nat := [1, 31, 31, 31, 31, 31, 31, 25].getD c 0

/-- **`verify_sub`'s facts from B1**: before its call of `verify_tables` (statement `333`) the word
at `dims_g` (value `71`) is below `g^34` (`vsDimsKnown0_holds`); before its dispatch to
`open_stacked` (statement `1544`) `tabs` (value `1921`) is in relation `1`, the window table
(`vsTabsT_holds`); before its call of `check_opening_terminal` (statement `1545`) the eight words
at `kappa_base` (value `83`) are below `kbBound` (`vsKnown_holds`). -/
def vsFacts : List (Nat × Hyp) :=
  (333, .mem (.n 71) 0 34) :: (1544, .rel (.n 1921) 1) ::
    (List.range 8).map fun c => (1545, .mem (.n 83) c (kbBound c))

end
end LeanVM.Guest.Backend.Obl
