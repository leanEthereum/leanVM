module

public import LeanVM.Guest.Fast.Numbers

/-!
# `sp_wots`' positions, as literal tables

The cells `sp_wots` hints its chains' starts at, precomputed from its template
(`B1/Sig/SpWotsT.lean`, `spGroupsT`) in the guest's numbering (`spRen`) and checked equal to it by
kernel evaluation (`Fast/SpWotsTablesCheck.lean`): its codeword groups' bases, and the chains'
starts from a group's base (the first group's and the other groups' tables, `64` arms each, and
the last chain's offset, arithmetic), as the codeword reader reads them (`cwCell`, `Fast/Wots.lean`).
-/

namespace LeanVM.Guest.Fast

@[expose] public section

/-- The codeword groups' bases: `21` groups of three digits, then the last chain's. -/
def spBase : List Nat := [
    126, 1113, 2195, 3277, 4359, 5441, 6523, 7605, 8687, 9769, 10851, 11933, 13015, 14097, 15179,
    16261, 17343, 18425, 19507, 20589, 21671, 22753]

/-- The first group's chain starts from its base: row `r`, arm `k`. -/
def spFirst : List (List Nat) := [
  [6, 45, 72, 16, 116, 141, 165, 16, 203, 225, 246, 16, 278, 296, 313, 16, 337, 362, 386, 16, 424,
    446, 467, 16, 499, 518, 536, 16, 562, 577, 591, 16, 609, 631, 652, 16, 684, 703, 721, 16, 747,
    763, 778, 16, 798, 810, 821, 16, 833, 851, 868, 16, 892, 907, 921, 16, 939, 951, 962, 16, 974,
    982, 989, 16],
  [17, 52, 76, 96, 124, 148, 169, 186, 211, 232, 250, 264, 29, 29, 29, 29, 345, 369, 390, 407, 432,
    453, 471, 485, 507, 525, 540, 551, 29, 29, 29, 29, 617, 638, 656, 670, 692, 710, 725, 736, 755,
    770, 782, 790, 29, 29, 29, 29, 841, 858, 872, 882, 900, 914, 925, 932, 947, 958, 966, 970, 29,
    29, 29, 29],
  [30, 62, 86, 106, 131, 155, 176, 193, 215, 236, 254, 268, 286, 303, 317, 327, 355, 379, 400, 417,
    439, 460, 478, 492, 511, 529, 544, 555, 570, 584, 595, 602, 627, 648, 666, 680, 699, 717, 732,
    743, 759, 774, 786, 794, 806, 817, 825, 829, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42,
    42, 42, 42]]

/-- The other groups' chain starts from their bases: row `r`, arm `k`. -/
def spRest : List (List Nat) := [
  [6, 47, 75, 18, 121, 149, 174, 18, 214, 239, 261, 18, 295, 316, 334, 18, 360, 388, 413, 18, 453,
    478, 500, 18, 534, 556, 575, 18, 603, 621, 636, 18, 656, 681, 703, 18, 737, 759, 778, 18, 806,
    825, 841, 18, 863, 878, 890, 18, 904, 925, 943, 18, 969, 987, 1002, 18, 1022, 1037, 1049, 18,
    1063, 1074, 1082, 18],
  [19, 54, 79, 100, 131, 156, 178, 196, 224, 246, 265, 280, 31, 31, 31, 31, 370, 395, 417, 435, 463,
    485, 504, 519, 544, 563, 579, 591, 31, 31, 31, 31, 666, 688, 707, 722, 747, 766, 782, 794, 816,
    832, 845, 854, 31, 31, 31, 31, 914, 932, 947, 958, 979, 994, 1006, 1014, 1032, 1044, 1053, 1058,
    31, 31, 31, 31],
  [32, 64, 89, 110, 138, 163, 185, 203, 228, 250, 269, 284, 305, 323, 338, 349, 380, 405, 427, 445,
    470, 492, 511, 526, 548, 567, 583, 595, 613, 628, 640, 648, 676, 698, 717, 732, 754, 773, 789,
    801, 820, 836, 849, 858, 873, 885, 894, 899, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44,
    44, 44, 44]]

/-- The last chain's start from its group's base in arm `k` (`64` arms): `18`, arm `0`'s slot,
where its digit `k % 4` is `3` (no step); `6` in arm `0`; else past `k / 4` runs of four arms
(`24` cells each), at its digit's offset `11`, `21` or `29`. -/
def spLastOff (k : Nat) : Nat :=
  if k % 4 = 3 then 18 else if k = 0 then 6 else 24 * (k / 4) + 11 + 9 * (k % 4) + k % 2

/-- Group `p`'s start of chain `r` from its base in arm `k`: the first group's table, the other
groups', the last chain's offset. -/
def spOff (p r k : Nat) : Nat :=
  if p = 0 then offAt spFirst r k else if p < 21 then offAt spRest r k else spLastOff k

end
end LeanVM.Guest.Fast
