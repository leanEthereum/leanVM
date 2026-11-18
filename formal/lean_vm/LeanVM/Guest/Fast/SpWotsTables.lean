module

/-!
# `sp_wots`' positions, as literal tables

The cells `sp_wots` hints its chains' starts at, precomputed from its template
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
    16, 1014, 2102, 3190, 4278, 5366, 6454, 7542, 8630, 9718, 10806, 11894, 12982, 14070, 15158,
    16246, 17334, 18422, 19510, 20598, 21686, 22774]

/-- The first group's chain starts from its selector: row `r`, arm `k`. -/
def spFirst : List (List Nat) := [
  [11, 50, 77, 21, 121, 146, 170, 21, 208, 230, 251, 21, 283, 301, 318, 21, 342, 367, 391, 21, 429,
    451, 472, 21, 504, 523, 541, 21, 567, 582, 596, 21, 614, 636, 657, 21, 689, 708, 726, 21, 752,
    768, 783, 21, 803, 815, 826, 21, 838, 856, 873, 21, 897, 912, 926, 21, 944, 956, 967, 21, 979,
    987, 994, 21],
  [22, 57, 81, 101, 129, 153, 174, 191, 216, 237, 255, 269, 34, 34, 34, 34, 350, 374, 395, 412,
    437, 458, 476, 490, 512, 530, 545, 556, 34, 34, 34, 34, 622, 643, 661, 675, 697, 715, 730, 741,
    760, 775, 787, 795, 34, 34, 34, 34, 846, 863, 877, 887, 905, 919, 930, 937, 952, 963, 971, 975,
    34, 34, 34, 34],
  [35, 67, 91, 111, 136, 160, 181, 198, 220, 241, 259, 273, 291, 308, 322, 332, 360, 384, 405, 422,
    444, 465, 483, 497, 516, 534, 549, 560, 575, 589, 600, 607, 632, 653, 671, 685, 704, 722, 737,
    748, 764, 779, 791, 799, 811, 822, 830, 834, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47,
    47, 47, 47]]

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
