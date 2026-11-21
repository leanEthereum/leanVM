/-
  LeanVM.Guest.Compiled.Obl.GuestTab

  The guest's preconditions and postconditions for the analysis: the weakest the selectors need.
-/

module

public import LeanVM.Guest.Compiled.Obl.GuestX
public import LeanVM.Core.Renumber
public import LeanVM.Guest.Data.NameStrings

/-!
# The guest's table

What each guest function asks of its callers and promises them, in the analysis' terms
(`Obl.Sig`, indices into the arguments and, for `post`, into the arguments then the returns).
Every entry is what a selector of the function, or of a function it is passed to, needs.

* `verify_tables`: argument `9` below `g^34` (dispatched on), the word at argument `10` below
  `g^34` (`dims_g[0]`, dispatched on), read (`memRel`);
* `check_opening_terminal`: the eight words at argument `8` (`kappa_base`) below its arms, read;
* `child_claim_list_any`, `child_claim_list_mono`: argument `6` below `g^17`;
* `open_stacked__L0` to `__L10`: argument `0` below `g^4`, argument `10` (`tabs`) in relation `1`,
  the window table (B1's `WinTabs`), which it hands its `level_positions` as their argument `8`;
* `walk_path__L{pd}_L{cd}`: the words at argument `2` (the path's windows) its `match`es read, if
  read, below `g^64`, and argument `2` the windows of the walk of depth `pd + cd`, cap depth `cd`
  (B1's `WinsAt`, relation `winsTag (pd + cd) cd`);
* `list_split`: return `2` below `g^17`; `log2_ceil_in_the_exponent__L0_L34`: return `0` below
  `g^34`;
* relation `0`, the exponent table and its window section (B1's `ExpTables`, `ExpWinTab`):
  `exponent_tables` returns one, `main_loop4` takes it as argument `14` and `verify_sub` as
  argument `4`, where B1's bounds on `dims_g` and `kappa_base` (`vsDimsKnown0_holds`,
  `vsKnown_holds`) and its window table read it;
* `ext`: the functions of `xTab` (`Obl.GuestX`), whose preconditions are relations between their
  arguments and memory, not of the table's form.

`pows`: `g^255`, the bound of `main_loop2`'s range checks.

`guestXIdx` and `vsIdx` are written by `lake exe guest-oblgen` (`cli/GuestOblGen.lean`), which
checks that every key of `guestTab` names a function of the guest and that `level_positions`,
`walk_path` and `open_stacked` have an entry each.
-/

namespace LeanVM.Guest.Compiled.Obl

open LeanVM.Compiler LeanVM.Compiler.Obl

@[expose] public section

/-- The tag of relation `guestRel (memRel c n)`: the word at the argument times `g^c` is read and
is `g^e` with `e < n`, for `n < 2^16`. -/
def memRel (c n : Nat) : Nat := 2 ^ 32 + c * 2 ^ 16 + n

/-- **The guest's table.** Every key is a literal (`name% s` elaborates to one): comparing strings
is the costly step of evaluating the analysis in the kernel. -/
def guestTab : Tab where
  sigs := [
    ("verify_tables", { pre := [(9, 34)], mem := [(10, 0, 34)], xpre := [(10, memRel 0 34)] }),
    ("check_opening_terminal", { mem := [(8, 0, 1), (8, 1, 31), (8, 2, 31), (8, 3, 31),
      (8, 4, 31), (8, 5, 31), (8, 6, 31), (8, 7, 25)], xpre := [(8, memRel 0 1), (8, memRel 1 31),
      (8, memRel 2 31), (8, memRel 3 31), (8, memRel 4 31), (8, memRel 5 31), (8, memRel 6 31),
      (8, memRel 7 25)] }),
    ("child_claim_list_any", { pre := [(6, 17)] }),
    ("child_claim_list_mono", { pre := [(6, 17)] }),
    ("list_split", { post := [(3, 17)] }),
    ("log2_ceil_in_the_exponent__L0_L34", { post := [(2, 34)] }),
    ("exponent_tables", { xpost := [(0, 0)] }),
    (name% «main_loop4», { xpre := [(14, 0)] }),
    ("verify_sub", { xpre := [(4, 0)] }),
    ("level_positions__L10_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L10_L20_L2", { xpre := [(8, 1)] }),
    ("level_positions__L10_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L10_L26_L2", { xpre := [(8, 1)] }),
    ("level_positions__L11_L17_L5", { xpre := [(8, 1)] }),
    ("level_positions__L11_L18_L6", { xpre := [(8, 1)] }),
    ("level_positions__L11_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L11_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L11_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L11_L25_L7", { xpre := [(8, 1)] }),
    ("level_positions__L13_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L13_L20_L2", { xpre := [(8, 1)] }),
    ("level_positions__L13_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L14_L16_L4", { xpre := [(8, 1)] }),
    ("level_positions__L14_L26_L2", { xpre := [(8, 1)] }),
    ("level_positions__L14_L27_L3", { xpre := [(8, 1)] }),
    ("level_positions__L14_L28_L4", { xpre := [(8, 1)] }),
    ("level_positions__L15_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L15_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L15_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L15_L25_L7", { xpre := [(8, 1)] }),
    ("level_positions__L16_L17_L5", { xpre := [(8, 1)] }),
    ("level_positions__L16_L18_L6", { xpre := [(8, 1)] }),
    ("level_positions__L19_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L19_L20_L2", { xpre := [(8, 1)] }),
    ("level_positions__L19_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L19_L26_L2", { xpre := [(8, 1)] }),
    ("level_positions__L19_L27_L3", { xpre := [(8, 1)] }),
    ("level_positions__L22_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L22_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L22_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L22_L25_L7", { xpre := [(8, 1)] }),
    ("level_positions__L28_L15_L3", { xpre := [(8, 1)] }),
    ("level_positions__L28_L16_L4", { xpre := [(8, 1)] }),
    ("level_positions__L28_L26_L2", { xpre := [(8, 1)] }),
    ("level_positions__L32_L17_L5", { xpre := [(8, 1)] }),
    ("level_positions__L32_L18_L6", { xpre := [(8, 1)] }),
    ("level_positions__L37_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L37_L20_L8", { xpre := [(8, 1)] }),
    ("level_positions__L37_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L3_L12_L6", { xpre := [(8, 1)] }),
    ("level_positions__L3_L13_L7", { xpre := [(8, 1)] }),
    ("level_positions__L3_L14_L2", { xpre := [(8, 1)] }),
    ("level_positions__L3_L15_L3", { xpre := [(8, 1)] }),
    ("level_positions__L3_L16_L4", { xpre := [(8, 1)] }),
    ("level_positions__L3_L17_L5", { xpre := [(8, 1)] }),
    ("level_positions__L3_L18_L6", { xpre := [(8, 1)] }),
    ("level_positions__L3_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L3_L20_L2", { xpre := [(8, 1)] }),
    ("level_positions__L3_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L3_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L3_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L44_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L44_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L44_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L44_L25_L7", { xpre := [(8, 1)] }),
    ("level_positions__L4_L13_L7", { xpre := [(8, 1)] }),
    ("level_positions__L4_L14_L2", { xpre := [(8, 1)] }),
    ("level_positions__L4_L15_L3", { xpre := [(8, 1)] }),
    ("level_positions__L4_L16_L4", { xpre := [(8, 1)] }),
    ("level_positions__L4_L17_L5", { xpre := [(8, 1)] }),
    ("level_positions__L4_L18_L6", { xpre := [(8, 1)] }),
    ("level_positions__L4_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L4_L20_L2", { xpre := [(8, 1)] }),
    ("level_positions__L4_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L4_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L4_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L4_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L4_L25_L7", { xpre := [(8, 1)] }),
    ("level_positions__L5_L16_L4", { xpre := [(8, 1)] }),
    ("level_positions__L5_L17_L5", { xpre := [(8, 1)] }),
    ("level_positions__L5_L18_L6", { xpre := [(8, 1)] }),
    ("level_positions__L5_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L5_L20_L2", { xpre := [(8, 1)] }),
    ("level_positions__L5_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L5_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L5_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L5_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L5_L25_L7", { xpre := [(8, 1)] }),
    ("level_positions__L6_L15_L3", { xpre := [(8, 1)] }),
    ("level_positions__L6_L16_L4", { xpre := [(8, 1)] }),
    ("level_positions__L6_L17_L5", { xpre := [(8, 1)] }),
    ("level_positions__L6_L18_L6", { xpre := [(8, 1)] }),
    ("level_positions__L6_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L6_L20_L2", { xpre := [(8, 1)] }),
    ("level_positions__L6_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L6_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L6_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L6_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L6_L26_L2", { xpre := [(8, 1)] }),
    ("level_positions__L7_L14_L2", { xpre := [(8, 1)] }),
    ("level_positions__L7_L15_L3", { xpre := [(8, 1)] }),
    ("level_positions__L7_L16_L4", { xpre := [(8, 1)] }),
    ("level_positions__L7_L17_L5", { xpre := [(8, 1)] }),
    ("level_positions__L7_L18_L6", { xpre := [(8, 1)] }),
    ("level_positions__L7_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L7_L20_L2", { xpre := [(8, 1)] }),
    ("level_positions__L7_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L7_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L7_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L7_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L7_L25_L7", { xpre := [(8, 1)] }),
    ("level_positions__L8_L17_L5", { xpre := [(8, 1)] }),
    ("level_positions__L8_L18_L6", { xpre := [(8, 1)] }),
    ("level_positions__L8_L19_L7", { xpre := [(8, 1)] }),
    ("level_positions__L8_L20_L2", { xpre := [(8, 1)] }),
    ("level_positions__L8_L21_L3", { xpre := [(8, 1)] }),
    ("level_positions__L8_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L8_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L8_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L8_L25_L7", { xpre := [(8, 1)] }),
    ("level_positions__L8_L26_L2", { xpre := [(8, 1)] }),
    ("level_positions__L8_L27_L3", { xpre := [(8, 1)] }),
    ("level_positions__L9_L22_L4", { xpre := [(8, 1)] }),
    ("level_positions__L9_L23_L5", { xpre := [(8, 1)] }),
    ("level_positions__L9_L24_L6", { xpre := [(8, 1)] }),
    ("level_positions__L9_L25_L7", { xpre := [(8, 1)] }),
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
    ("walk_path__L6_L6", { mem := [(2, 0, 64)], xpre := [(2, winsTag 12 6)] }),
    ("walk_path__L6_L7", { mem := [(2, 0, 64)], xpre := [(2, winsTag 13 7)] }),
    ("walk_path__L12_L2", { mem := [(2, 0, 64), (2, 1, 64)], xpre := [(2, winsTag 14 2)] }),
    ("walk_path__L12_L3", { mem := [(2, 0, 64), (2, 1, 64)], xpre := [(2, winsTag 15 3)] }),
    ("walk_path__L12_L4", { mem := [(2, 0, 64), (2, 1, 64)], xpre := [(2, winsTag 16 4)] }),
    ("walk_path__L12_L5", { mem := [(2, 0, 64), (2, 1, 64)], xpre := [(2, winsTag 17 5)] }),
    ("walk_path__L12_L6", { mem := [(2, 0, 64), (2, 1, 64)], xpre := [(2, winsTag 18 6)] }),
    ("walk_path__L12_L7", { mem := [(2, 0, 64), (2, 1, 64)], xpre := [(2, winsTag 19 7)] }),
    ("walk_path__L12_L8", { mem := [(2, 0, 64), (2, 1, 64)], xpre := [(2, winsTag 20 8)] }),
    ("walk_path__L18_L2", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)], xpre := [(2, winsTag 20 2)] }),
    ("walk_path__L18_L3", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)], xpre := [(2, winsTag 21 3)] }),
    ("walk_path__L18_L4", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)], xpre := [(2, winsTag 22 4)] }),
    ("walk_path__L18_L5", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)], xpre := [(2, winsTag 23 5)] }),
    ("walk_path__L18_L6", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)], xpre := [(2, winsTag 24 6)] }),
    ("walk_path__L18_L7", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)], xpre := [(2, winsTag 25 7)] }),
    ("walk_path__L24_L2", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64), (2, 3, 64)], xpre := [(2, winsTag 26 2)] }),
    ("walk_path__L24_L3", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64), (2, 3, 64)], xpre := [(2, winsTag 27 3)] }),
    ("walk_path__L24_L4", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64), (2, 3, 64)], xpre := [(2, winsTag 28 4)] })] ++
    xTab.map fun p => (p.1, { ext := true })
  pows := [(9223372036854810629, 255)]

/-- The functions (by index in `coreProgram`) the analysis checks with `ext` sites and facts
(`chkFnX`) instead of `chkFn`: `verify_bus_gkr` and `verify_bus_gkr_loop0`, the `open_stacked`,
`level_queries` and `opening_queries` specializations and the latter's loop helpers (`GuestXTab`),
the callers of `ext` functions and those whose selectors their own `ext` precondition bounds. -/
def guestXIdx : List Nat :=
  [9, 91, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 458, 459, 460, 461, 468, 469, 470,
  471, 477, 478, 479, 480, 485, 486, 487, 488, 507, 508, 509, 510, 516, 517, 518, 519, 523, 524,
  525, 526, 528, 529, 530, 531, 550, 551, 552, 553, 559, 560, 561, 562, 565, 566, 567, 568, 571,
  572, 573, 574, 593, 594, 595, 596, 602, 603, 604, 605, 608, 609, 610, 611, 614, 615, 616, 617,
  636, 637, 638, 639, 643, 644, 645, 646, 649, 650, 651, 653, 654, 655, 656, 657, 658, 678, 679,
  680, 681, 685, 686, 687, 688, 691, 692, 693, 695, 696, 697, 698, 699, 700, 719, 720, 721, 722,
  726, 727, 728, 729, 732, 733, 734, 736, 737, 738, 739, 740, 741, 760, 761, 762, 763, 767, 768,
  769, 770, 772, 773, 774, 776, 777, 778, 779, 780, 781, 800, 801, 802, 803, 807, 808, 809, 810,
  813, 814, 815, 817, 818, 819, 821, 822, 823, 824, 825, 826, 848, 849, 850, 851, 855, 856, 857,
  858, 861, 862, 863, 865, 866, 867, 868, 869, 870, 871, 872, 873, 894, 895, 896, 897, 901, 902,
  903, 904, 907, 908, 909, 911, 912, 913, 914, 915, 917, 918, 919, 951, 953, 955, 957, 964, 965,
  966, 967, 974, 980, 981, 982, 983, 1012, 1013, 1018, 1021, 1022, 1023, 1024, 1052, 1053, 1058,
  1061, 1062, 1063, 1064, 1092, 1093, 1098, 1101, 1102, 1103, 1104, 1132, 1133, 1137, 1141, 1142,
  1143, 1178, 1179, 1183, 1187, 1188, 1189, 1222, 1223, 1227, 1231, 1232, 1233, 1266, 1267, 1271,
  1274, 1275, 1276, 1309, 1310, 1314, 1319, 1320, 1321, 1359, 1360, 1364, 1368, 1369, 1370, 1406,
  1407, 1411, 1416, 1417, 1418, 1457, 1459, 1461, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470,
  1471, 1472, 1473, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1483, 1484, 1485, 1486, 1487, 1488,
  1489, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1499, 1500, 1501, 1502, 1503, 1504, 1506, 1507,
  1508, 1509, 1510, 1511, 1513, 1514, 1515, 1516, 1517, 1518, 1520, 1521, 1522, 1523, 1524, 1525,
  1527, 1528, 1529, 1530, 1531, 1532, 1534, 1535, 1536, 1537, 1538, 1539, 1541, 1542, 1543, 1544,
  1545]

/-- `verify_sub`, whose calls of `verify_tables` and `check_opening_terminal` take B1's bounds on
`dims_g` and `kappa_base` as facts (`vsFacts`). -/
def vsIdx : Nat := 19

/-- The functions the analysis without facts does not cover. -/
def guestSkip (j : Nat) : Bool := j == vsIdx || guestXIdx.contains j

/-- `kappa_base`'s bounds (`lean_ethereum.py:3561-3569`): `kb[0] = g^0`, the memory's log and the
six tables' heights below `g^31`, keccak's `τ` below `g^25`. -/
def kbBound (c : Nat) : Nat := [1, 31, 31, 31, 31, 31, 31, 25].getD c 0

/-- **`verify_sub`'s facts from B1**: before its call of `verify_tables` (statement `316`) the word
at `dims_g` (value `71`) is read and below `g^34` (`vsDimsKnown0_holds`, as `mem` and as
`memRel`); before its dispatch to `open_stacked` (statement `1510`) `tabs` (value `1887`) is in
relation `1`, the window table (`vsTabsT_holds`); before its call of `check_opening_terminal`
(statement `1511`) the eight words at `kappa_base` (value `83`) are read and below `kbBound`
(`vsKnown_holds`). -/
def vsFacts : List (Nat × Hyp) :=
  (316, .mem (.n 71) 0 34) :: (316, .rel (.n 71) (memRel 0 34)) :: (1510, .rel (.n 1887) 1) ::
    ((List.range 8).map fun c => (1511, .mem (.n 83) c (kbBound c))) ++
    (List.range 8).map fun c => (1511, .rel (.n 83) (memRel c (kbBound c)))

end
end LeanVM.Guest.Compiled.Obl
