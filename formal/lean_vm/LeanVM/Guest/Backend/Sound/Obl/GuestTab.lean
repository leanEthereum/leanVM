/-
  LeanVM.Guest.Backend.Sound.Obl.GuestTab

  The guest's preconditions and postconditions for the analysis: the weakest the selectors need.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.GuestX
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.Data.NameStrings

/-!
# The guest's table

What each guest function asks of its callers and promises them, in the analysis' terms
(`Obl.Sig`, indices into the arguments and, for `post`, into the arguments then the returns).
Every entry is what a selector of the function, or of a function it is passed to, needs, and what
the existing certificates' signatures ask of the same function (`Sig.pre`, `Sig.mem`, `Sig.sem`,
at frame offsets `2 + i`), so that the guest's precondition `guestU` and the certificates' imply
each other (`Guest/B2/Sig.lean`).

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

namespace LeanVM.Guest.Backend.Obl

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
  [9, 90, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 457, 458, 459, 460, 467, 468, 469,
  470, 476, 477, 478, 479, 484, 485, 486, 487, 506, 507, 508, 509, 515, 516, 517, 518, 522, 523,
  524, 525, 527, 528, 529, 530, 549, 550, 551, 552, 558, 559, 560, 561, 564, 565, 566, 567, 570,
  571, 572, 573, 592, 593, 594, 595, 601, 602, 603, 604, 607, 608, 609, 610, 613, 614, 615, 616,
  635, 636, 637, 638, 642, 643, 644, 645, 648, 649, 650, 652, 653, 654, 655, 656, 657, 677, 678,
  679, 680, 684, 685, 686, 687, 690, 691, 692, 694, 695, 696, 697, 698, 699, 718, 719, 720, 721,
  725, 726, 727, 728, 731, 732, 733, 735, 736, 737, 738, 739, 740, 759, 760, 761, 762, 766, 767,
  768, 769, 771, 772, 773, 775, 776, 777, 778, 779, 780, 799, 800, 801, 802, 806, 807, 808, 809,
  812, 813, 814, 816, 817, 818, 820, 821, 822, 823, 824, 825, 847, 848, 849, 850, 854, 855, 856,
  857, 860, 861, 862, 864, 865, 866, 867, 868, 869, 870, 871, 872, 893, 894, 895, 896, 900, 901,
  902, 903, 906, 907, 908, 910, 911, 912, 913, 914, 916, 917, 918, 950, 952, 954, 956, 963, 964,
  965, 966, 973, 979, 980, 981, 982, 1011, 1012, 1017, 1020, 1021, 1022, 1023, 1051, 1052, 1057,
  1060, 1061, 1062, 1063, 1091, 1092, 1097, 1100, 1101, 1102, 1103, 1131, 1132, 1136, 1140, 1141,
  1142, 1177, 1178, 1182, 1186, 1187, 1188, 1221, 1222, 1226, 1230, 1231, 1232, 1265, 1266, 1270,
  1273, 1274, 1275, 1308, 1309, 1313, 1318, 1319, 1320, 1358, 1359, 1363, 1367, 1368, 1369, 1405,
  1406, 1410, 1415, 1416, 1417, 1456, 1458, 1460, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469,
  1470, 1471, 1472, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1482, 1483, 1484, 1485, 1486, 1487,
  1488, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1498, 1499, 1500, 1501, 1502, 1503, 1505, 1506,
  1507, 1508, 1509, 1510, 1512, 1513, 1514, 1515, 1516, 1517, 1519, 1520, 1521, 1522, 1523, 1524,
  1526, 1527, 1528, 1529, 1530, 1531, 1533, 1534, 1535, 1536, 1537, 1538, 1540, 1541, 1542, 1543,
  1544]

/-- `verify_sub`, whose calls of `verify_tables` and `check_opening_terminal` take B1's bounds on
`dims_g` and `kappa_base` as facts (`vsFacts`). -/
def vsIdx : Nat := 18

/-- The functions the analysis without facts does not cover. -/
def guestSkip (j : Nat) : Bool := j == vsIdx || guestXIdx.contains j

/-- `kappa_base`'s bounds (`lean_ethereum.py:3561-3569`): `kb[0] = g^0`, the memory's log and the
six tables' heights below `g^31`, keccak's `τ` below `g^25`. -/
def kbBound (c : Nat) : Nat := [1, 31, 31, 31, 31, 31, 31, 25].getD c 0

/-- **`verify_sub`'s facts from B1**: before its call of `verify_tables` (statement `333`) the word
at `dims_g` (value `71`) is read and below `g^34` (`vsDimsKnown0_holds`, as `mem` and as
`memRel`); before its dispatch to `open_stacked` (statement `1544`) `tabs` (value `1921`) is in
relation `1`, the window table (`vsTabsT_holds`); before its call of `check_opening_terminal`
(statement `1545`) the eight words at `kappa_base` (value `83`) are read and below `kbBound`
(`vsKnown_holds`). -/
def vsFacts : List (Nat × Hyp) :=
  (333, .mem (.n 71) 0 34) :: (333, .rel (.n 71) (memRel 0 34)) :: (1544, .rel (.n 1921) 1) ::
    ((List.range 8).map fun c => (1545, .mem (.n 83) c (kbBound c))) ++
    (List.range 8).map fun c => (1545, .rel (.n 83) (memRel c (kbBound c)))

end
end LeanVM.Guest.Backend.Obl
