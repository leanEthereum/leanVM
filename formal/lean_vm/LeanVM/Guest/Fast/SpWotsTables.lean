module

/-!
# `sp_wots`' positions, as literal tables

The cells `sp_wots` (`Data.core19`) hints its chains' starts at, precomputed from its template
(`B1/Sig/SpWotsT.lean`, `spGroupsT`, `spLast`) in the guest's numbering (`spRen`) and checked
equal to it by kernel evaluation
(`Fast/SpWotsTablesCheck.lean`): its codeword groups' selector cells (each group's digit hint, its
base), and the chains' starts from a selector (the first group's, the other groups', the last
chain's), as the shared reader of a codeword reads them (`cwCell`, `Fast/Wots.lean`).
-/

namespace LeanVM.Guest.Fast

@[expose] public section

/-- The codeword groups' selector cells: `21` groups of three digits, then the last chain's. -/
def spSel : List Nat := [
    16, 1141, 2229, 3317, 4405, 5493, 6581, 7669, 8757, 9845, 10933, 12021, 13109, 14197, 15285,
    16373, 17461, 18549, 19637, 20725, 21813, 22901]

/-- The first group's chain starts from its selector: row `r`, arm `k`. -/
def spFirst : List (List Nat) := [
  [12, 52, 81, 22, 129, 156, 182, 22, 224, 248, 271, 22, 307, 327, 346, 22, 374, 401, 427, 22, 469,
    493, 516, 22, 552, 573, 593, 22, 623, 640, 656, 22, 678, 702, 725, 22, 761, 782, 802, 22, 832,
    850, 867, 22, 891, 905, 918, 22, 934, 954, 973, 22, 1001, 1018, 1034, 22, 1056, 1070, 1083, 22,
    1099, 1109, 1118, 22],
  [23, 59, 85, 107, 137, 163, 186, 205, 232, 255, 275, 291, 35, 35, 35, 35, 382, 408, 431, 450,
    477, 500, 520, 536, 560, 580, 597, 610, 35, 35, 35, 35, 686, 709, 729, 745, 769, 789, 806, 819,
    840, 857, 871, 881, 35, 35, 35, 35, 942, 961, 977, 989, 1009, 1025, 1038, 1047, 1064, 1077,
    1087, 1093, 35, 35, 35, 35],
  [36, 69, 95, 117, 144, 170, 193, 212, 236, 259, 279, 295, 315, 334, 350, 362, 392, 418, 441, 460,
    484, 507, 527, 543, 564, 584, 601, 614, 631, 647, 660, 669, 696, 719, 739, 755, 776, 796, 813,
    826, 844, 861, 875, 885, 899, 912, 922, 928, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48,
    48, 48, 48, 48]]

/-- The other groups' chain starts from their selectors: row `r`, arm `k`. -/
def spRest : List (List Nat) := [
  [6, 47, 75, 18, 121, 149, 174, 18, 214, 239, 261, 18, 295, 316, 334, 18, 360, 388, 413, 18, 453,
    478, 500, 18, 534, 556, 575, 18, 603, 621, 636, 18, 656, 681, 703, 18, 737, 759, 778, 18, 806,
    825, 841, 18, 863, 878, 890, 18, 904, 925, 943, 18, 969, 987, 1002, 18, 1022, 1037, 1049, 18,
    1063, 1074, 1082, 18],
  [19, 54, 79, 100, 131, 156, 178, 196, 224, 246, 265, 280, 31, 31, 31, 31, 370, 395, 417, 435,
    463, 485, 504, 519, 544, 563, 579, 591, 31, 31, 31, 31, 666, 688, 707, 722, 747, 766, 782, 794,
    816, 832, 845, 854, 31, 31, 31, 31, 914, 932, 947, 958, 979, 994, 1006, 1014, 1032, 1044, 1053,
    1058, 31, 31, 31, 31],
  [32, 64, 89, 110, 138, 163, 185, 203, 228, 250, 269, 284, 305, 323, 338, 349, 380, 405, 427, 445,
    470, 492, 511, 526, 548, 567, 583, 595, 613, 628, 640, 648, 676, 698, 717, 732, 754, 773, 789,
    801, 820, 836, 849, 858, 873, 885, 894, 899, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
    44, 44, 44, 44]]

/-- The last chain's start from its selector: arm `k`. -/
def spLast : List (List Nat) := [
  [6, 21, 29, 18]]

/-- Group `p`'s table of starts from its selector: the first group's, the other groups', the last
chain's. -/
def spTabOf (p : Nat) : List (List Nat) := if p = 0 then spFirst else if p < 21 then spRest else spLast

end
end LeanVM.Guest.Fast
