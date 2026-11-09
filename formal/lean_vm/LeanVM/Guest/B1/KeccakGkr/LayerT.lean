/-
  LeanVM.Guest.B1.KeccakGkr.LayerT

  `keccak_layer`'s two specializations as one template (`layerT first`), section by section.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Prod
public import LeanVM.Guest.B1.KeccakGkr.LayerRmfe
public import LeanVM.Guest.B1.KeccakGkr.EqFrame

/-!
# `keccak_layer` as a template

The specializations `keccak_layer__L{first}` (G:2694-2875) compile to one statement list up to
the head (`first = 1` copies the waiting word's two cells), the product's table (`prodTab first`),
the waiting cells of the squeeze after it, and the first layer's weight section; from `s` on the
values are the same. Sections:

* `headT`: the carried capacity (and, first, the waiting word's cells) copied, the claim's sixteen
  instance weights read (`KC_MU`), and the readers, a straight line of sums over them
  (`KECCAK_PROJ_A`, `KECCAK_PROJ_B`, G:2710-2714);
* `prodT` (`Prod`): the product's 47 coefficients read and absorbed, and their projection, each
  coefficient times its reader (`KECCAK_PROJ_OUT`);
* `checkT`: the projection plus `ι·κ` against the claim's value;
* `sqT`: the squeeze of `s`; `rmfeBlockT` (`LayerRmfe`): the instance weights at `s`;
* `hornerT`: the product at `s`;
* `packSetupT`: the pack rounds' first record and the two loops;
* `lastT`, `localRoundsT`, `tReadsT`: the last record read, the eleven position rounds, `t`;
* `eqfT` (`EqFrame`): the lane weights of the local point;
* `weightT`: the claim's weights at the local point (first: `lanesEqT`; later: `shiftsT` and
  `formT`, `keccak_shifts_eq` and `keccak_form`);
* `tailT`: the final check, the squeeze of `β`, the next claim's record, and its weights where
  `ι` can flip (`lflipT`, `slice_weight`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Helpers -/

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem holdsList_map_atoms (n : ℕ) (A : ℕ → Atom) : ∀ (next : Prop) (kret : List E → Prop),
    Stmt.HoldsList C rd σ ((List.range n).map fun i ↦ .atom (A i)) next kret ↔
      (∀ i < n, (A i).Holds rd σ) ∧ next := by
  induction n with
  | zero => intro next kret; simp [Stmt.HoldsList]
  | succ n ih =>
    intro next kret
    rw [List.range_succ, List.map_append, holdsList_append, ih]
    simp only [List.map_cons, List.map_nil, Stmt.HoldsList, Stmt.Holds]
    constructor
    · rintro ⟨h, h', hn⟩
      refine ⟨fun i hi ↦ ?_, hn⟩
      rcases Nat.lt_or_ge i n with hin | hin
      · exact h i hin
      · obtain rfl : i = n := by omega
        exact h'
    · rintro ⟨h, hn⟩
      exact ⟨fun i hi ↦ h i (by omega), h n (by omega), hn⟩

theorem eq_of_add_eq_zero' {a b : E} (h : a + b = 0) : a = b := by
  have := congrArg (· + b) h
  simpa [add_assoc, e_add_self] using this

/-! ## The readers -/

/-- `KECCAK_PROJ_A`: reader `16 + t` is reader `projA t` plus reader `projB t`. -/
def projA : List ℕ := [
  1, 3, 2, 10, 8, 6, 1, 7, 14, 7, 4, 1, 3, 9, 20, 6, 8, 11, 18, 19, 8, 9, 10, 14, 17, 20, 10, 11,
  12, 12, 13, 17, 19, 22, 23, 26, 0, 6, 6, 6, 6, 6, 7, 7, 8, 9, 10, 11, 11, 11, 11, 13, 14, 14,
  14, 15, 17, 17, 17, 18, 18, 20, 20, 21, 22, 23, 23, 24, 24, 24, 24, 25, 25, 25, 26, 26, 26,
  28, 28, 29, 29, 30, 30, 30, 30, 31, 31, 32, 32, 33, 33, 35, 39, 41, 43, 44, 44, 46, 47, 48,
  48, 51, 51, 52, 53, 59, 60, 61, 63, 75, 79]

/-- `KECCAK_PROJ_B`. -/
def projB : List ℕ := [
  5, 16, 4, 13, 9, 12, 18, 11, 17, 19, 16, 2, 22, 21, 23, 7, 24, 12, 20, 21, 14, 13, 21, 28, 25,
  22, 27, 27, 19, 23, 24, 34, 23, 25, 38, 31, 18, 10, 26, 41, 46, 47, 13, 20, 10, 14, 17, 19,
  24, 35, 37, 21, 37, 41, 43, 36, 29, 45, 50, 24, 32, 35, 39, 22, 33, 27, 36, 30, 34, 35, 38,
  26, 27, 28, 29, 36, 50, 29, 45, 40, 49, 39, 42, 54, 62, 32, 37, 33, 67, 34, 42, 81, 66, 65,
  77, 69, 84, 105, 58, 76, 91, 68, 71, 95, 78, 86, 80, 106, 90, 102, 82]

/-- `KECCAK_PROJ_OUT`: coefficient `k`'s reader. -/
def projOut : List ℕ := [
  119, 40, 40, 49, 116, 93, 70, 112, 74, 83, 109, 117, 94, 98, 57, 101, 104, 126, 124, 108, 123,
  113, 121, 85, 122, 99, 120, 107, 114, 56, 103, 96, 87, 89, 88, 115, 72, 64, 111, 92, 97, 110,
  125, 73, 100, 55, 118]

/-- The instance weights' base value. -/
def muB (first : ℕ) : ℕ := 19 + 2 * first

/-- The capacity (and the waiting cells) copied, the instance weights read, the readers. -/
def headT (first : ℕ) : List Stmt :=
  (List.range (5 + 2 * first)).map (fun i ↦ .atom (.copy (.n (14 + i)) (.n i))) ++
    (List.range 16).map (fun i ↦ .atom (.load (.n (muB first + i)) (.n 11) (6 + i))) ++
    (List.range 111).map fun t ↦ .atom (.add (.n (muB first + 16 + t))
      (.n (muB first + projA.getD t 0)) (.n (muB first + projB.getD t 0)))

/-- Coefficient `k`'s reader, as `Prod`'s index list. -/
def projR (k : ℕ) : List ℕ := [projOut.getD k 0]

/-! ## The product's tables -/

/-- The product section's table, first = 1. -/
def prodTab1 : List PPos := [
    ⟨148, none, 149, [119], 0, 158, none, 158⟩,
    ⟨159, none, 160, [40], 0, 169, some 158, 170⟩,
    ⟨171, none, 172, [40], 0, 181, some 170, 182⟩,
    ⟨183, some ([19, 20, 155, 157, 166, 168, 178, 180, 14, 15, 16, 17, 18], 184), 197, [49], 0, 206, some 182, 207⟩,
    ⟨208, none, 209, [116], 0, 218, some 207, 219⟩,
    ⟨220, none, 221, [93], 0, 230, some 219, 231⟩,
    ⟨232, none, 233, [70], 0, 242, some 231, 243⟩,
    ⟨244, some ([203, 205, 215, 217, 227, 229, 239, 241, 192, 193, 194, 195, 196], 245), 258, [112], 0, 267, some 243, 268⟩,
    ⟨269, none, 270, [74], 0, 279, some 268, 280⟩,
    ⟨281, none, 282, [83], 0, 291, some 280, 292⟩,
    ⟨293, none, 294, [109], 0, 303, some 292, 304⟩,
    ⟨305, some ([264, 266, 276, 278, 288, 290, 300, 302, 253, 254, 255, 256, 257], 306), 319, [117], 0, 328, some 304, 329⟩,
    ⟨330, none, 331, [94], 0, 340, some 329, 341⟩,
    ⟨342, none, 343, [98], 0, 352, some 341, 353⟩,
    ⟨354, none, 355, [57], 0, 364, some 353, 365⟩,
    ⟨366, some ([325, 327, 337, 339, 349, 351, 361, 363, 314, 315, 316, 317, 318], 367), 380, [101], 0, 389, some 365, 390⟩,
    ⟨391, none, 392, [104], 0, 401, some 390, 402⟩,
    ⟨403, none, 404, [126], 0, 413, some 402, 414⟩,
    ⟨415, none, 416, [124], 0, 425, some 414, 426⟩,
    ⟨427, some ([386, 388, 398, 400, 410, 412, 422, 424, 375, 376, 377, 378, 379], 428), 441, [108], 0, 450, some 426, 451⟩,
    ⟨452, none, 453, [123], 0, 462, some 451, 463⟩,
    ⟨464, none, 465, [113], 0, 474, some 463, 475⟩,
    ⟨476, none, 477, [121], 0, 486, some 475, 487⟩,
    ⟨488, some ([447, 449, 459, 461, 471, 473, 483, 485, 436, 437, 438, 439, 440], 489), 502, [85], 0, 511, some 487, 512⟩,
    ⟨513, none, 514, [122], 0, 523, some 512, 524⟩,
    ⟨525, none, 526, [99], 0, 535, some 524, 536⟩,
    ⟨537, none, 538, [120], 0, 547, some 536, 548⟩,
    ⟨549, some ([508, 510, 520, 522, 532, 534, 544, 546, 497, 498, 499, 500, 501], 550), 563, [107], 0, 572, some 548, 573⟩,
    ⟨574, none, 575, [114], 0, 584, some 573, 585⟩,
    ⟨586, none, 587, [56], 0, 596, some 585, 597⟩,
    ⟨598, none, 599, [103], 0, 608, some 597, 609⟩,
    ⟨610, some ([569, 571, 581, 583, 593, 595, 605, 607, 558, 559, 560, 561, 562], 611), 624, [96], 0, 633, some 609, 634⟩,
    ⟨635, none, 636, [87], 0, 645, some 634, 646⟩,
    ⟨647, none, 648, [89], 0, 657, some 646, 658⟩,
    ⟨659, none, 660, [88], 0, 669, some 658, 670⟩,
    ⟨671, some ([630, 632, 642, 644, 654, 656, 666, 668, 619, 620, 621, 622, 623], 672), 685, [115], 0, 694, some 670, 695⟩,
    ⟨696, none, 697, [72], 0, 706, some 695, 707⟩,
    ⟨708, none, 709, [64], 0, 718, some 707, 719⟩,
    ⟨720, none, 721, [111], 0, 730, some 719, 731⟩,
    ⟨732, some ([691, 693, 703, 705, 715, 717, 727, 729, 680, 681, 682, 683, 684], 733), 746, [92], 0, 755, some 731, 756⟩,
    ⟨757, none, 758, [97], 0, 767, some 756, 768⟩,
    ⟨769, none, 770, [110], 0, 779, some 768, 780⟩,
    ⟨781, none, 782, [125], 0, 791, some 780, 792⟩,
    ⟨793, some ([752, 754, 764, 766, 776, 778, 788, 790, 741, 742, 743, 744, 745], 794), 807, [73], 0, 816, some 792, 817⟩,
    ⟨818, none, 819, [100], 0, 828, some 817, 829⟩,
    ⟨830, none, 831, [55], 0, 840, some 829, 841⟩,
    ⟨842, none, 843, [118], 0, 852, some 841, 853⟩]

/-- The product section's table, first = 0. -/
def prodTab0 : List PPos := [
    ⟨146, none, 147, [119], 0, 156, none, 156⟩,
    ⟨157, none, 158, [40], 0, 167, some 156, 168⟩,
    ⟨169, none, 170, [40], 0, 179, some 168, 180⟩,
    ⟨181, none, 182, [49], 0, 191, some 180, 192⟩,
    ⟨193, some ([153, 155, 164, 166, 176, 178, 188, 190, 14, 15, 16, 17, 18], 194), 207, [116], 0, 216, some 192, 217⟩,
    ⟨218, none, 219, [93], 0, 228, some 217, 229⟩,
    ⟨230, none, 231, [70], 0, 240, some 229, 241⟩,
    ⟨242, none, 243, [112], 0, 252, some 241, 253⟩,
    ⟨254, some ([213, 215, 225, 227, 237, 239, 249, 251, 202, 203, 204, 205, 206], 255), 268, [74], 0, 277, some 253, 278⟩,
    ⟨279, none, 280, [83], 0, 289, some 278, 290⟩,
    ⟨291, none, 292, [109], 0, 301, some 290, 302⟩,
    ⟨303, none, 304, [117], 0, 313, some 302, 314⟩,
    ⟨315, some ([274, 276, 286, 288, 298, 300, 310, 312, 263, 264, 265, 266, 267], 316), 329, [94], 0, 338, some 314, 339⟩,
    ⟨340, none, 341, [98], 0, 350, some 339, 351⟩,
    ⟨352, none, 353, [57], 0, 362, some 351, 363⟩,
    ⟨364, none, 365, [101], 0, 374, some 363, 375⟩,
    ⟨376, some ([335, 337, 347, 349, 359, 361, 371, 373, 324, 325, 326, 327, 328], 377), 390, [104], 0, 399, some 375, 400⟩,
    ⟨401, none, 402, [126], 0, 411, some 400, 412⟩,
    ⟨413, none, 414, [124], 0, 423, some 412, 424⟩,
    ⟨425, none, 426, [108], 0, 435, some 424, 436⟩,
    ⟨437, some ([396, 398, 408, 410, 420, 422, 432, 434, 385, 386, 387, 388, 389], 438), 451, [123], 0, 460, some 436, 461⟩,
    ⟨462, none, 463, [113], 0, 472, some 461, 473⟩,
    ⟨474, none, 475, [121], 0, 484, some 473, 485⟩,
    ⟨486, none, 487, [85], 0, 496, some 485, 497⟩,
    ⟨498, some ([457, 459, 469, 471, 481, 483, 493, 495, 446, 447, 448, 449, 450], 499), 512, [122], 0, 521, some 497, 522⟩,
    ⟨523, none, 524, [99], 0, 533, some 522, 534⟩,
    ⟨535, none, 536, [120], 0, 545, some 534, 546⟩,
    ⟨547, none, 548, [107], 0, 557, some 546, 558⟩,
    ⟨559, some ([518, 520, 530, 532, 542, 544, 554, 556, 507, 508, 509, 510, 511], 560), 573, [114], 0, 582, some 558, 583⟩,
    ⟨584, none, 585, [56], 0, 594, some 583, 595⟩,
    ⟨596, none, 597, [103], 0, 606, some 595, 607⟩,
    ⟨608, none, 609, [96], 0, 618, some 607, 619⟩,
    ⟨620, some ([579, 581, 591, 593, 603, 605, 615, 617, 568, 569, 570, 571, 572], 621), 634, [87], 0, 643, some 619, 644⟩,
    ⟨645, none, 646, [89], 0, 655, some 644, 656⟩,
    ⟨657, none, 658, [88], 0, 667, some 656, 668⟩,
    ⟨669, none, 670, [115], 0, 679, some 668, 680⟩,
    ⟨681, some ([640, 642, 652, 654, 664, 666, 676, 678, 629, 630, 631, 632, 633], 682), 695, [72], 0, 704, some 680, 705⟩,
    ⟨706, none, 707, [64], 0, 716, some 705, 717⟩,
    ⟨718, none, 719, [111], 0, 728, some 717, 729⟩,
    ⟨730, none, 731, [92], 0, 740, some 729, 741⟩,
    ⟨742, some ([701, 703, 713, 715, 725, 727, 737, 739, 690, 691, 692, 693, 694], 743), 756, [97], 0, 765, some 741, 766⟩,
    ⟨767, none, 768, [110], 0, 777, some 766, 778⟩,
    ⟨779, none, 780, [125], 0, 789, some 778, 790⟩,
    ⟨791, none, 792, [73], 0, 801, some 790, 802⟩,
    ⟨803, some ([762, 764, 774, 776, 786, 788, 798, 800, 751, 752, 753, 754, 755], 804), 817, [100], 0, 826, some 802, 827⟩,
    ⟨828, none, 829, [55], 0, 838, some 827, 839⟩,
    ⟨840, none, 841, [118], 0, 850, some 839, 851⟩]

/-- The product section's table. -/
def prodTab (first : ℕ) : List PPos := if first = 1 then prodTab1 else prodTab0

/-- The last running sum. -/
def accL (first : ℕ) : ℕ := if first = 1 then 853 else 851

/-! ## Head, check, squeeze, Horner -/

/-- The projection plus `ι·κ` against the claim's value. -/
def checkT (a : ℕ) : List Stmt :=
  [.atom (.load (.n (a + 1)) (.n 11) 1), .atom (.mul (.n (a + 2)) (.n 13) (.n (a + 1))),
    .atom (.add (.n (a + 3)) (.n a) (.n (a + 2))), .atom (.load (.n (a + 4)) (.n 11) 0),
    .atom (.assertEq (.n (a + 3)) (.n (a + 4)))]

/-- The cells the squeeze of `s` reads. -/
def sqIns : ℕ → List V
  | 1 => [.n 813, .n 815, .n 825, .n 827, .n 837, .n 839, .n 849, .n 851,
      .n 802, .n 803, .n 804, .n 805, .n 806]
  | _ => [.n 823, .n 825, .n 835, .n 837, .n 847, .n 849, .n 856, .n 857,
      .n 812, .n 813, .n 814, .n 815, .n 816]

/-- The squeeze of `s` (`877`). -/
def sqT (first : ℕ) : List Stmt :=
  (if first = 1 then [] else
    [.atom (.const (.n 856) (word 0 0 0)), .atom (.const (.n 857) (word 0 0 0))]) ++
  [keccakA (sqIns first) ((List.range 13).map fun k ↦ .n (858 + k))] ++
  challengeT (.n 858) (.n 859) 871

/-- The product at `s`, Horner from the top coefficient `a 46`, from the value `b`. -/
def hornerT (a : ℕ → ℕ) (s b : ℕ) : List Stmt :=
  ((List.range 46).map fun j ↦
    [.atom (.mul (.n (b + 2 * j)) (.n (if j = 0 then a 46 else b + 2 * j - 1)) (.n s)),
      .atom (.add (.n (b + 2 * j + 1)) (.n (b + 2 * j)) (.n (a (45 - j))))]).flatten

/-! ## The pack rounds and the local rounds -/

/-- The pack rounds' first record (`rounds`, `1053`: the capacity after `s`, the cursor past the
product, the product at `s`, the scale `1`), the eight-round loop on `step_g`, and the remainder
loop on `rem_g` from `rounds·step_g`, `prev_point·step_g⁸`, `point·step_g⁸`. -/
def packSetupT (first : ℕ) : List Stmt :=
  [.atom (.load (.n 1051) (.n 11) 2), .atom (.hint (.allocDyn (.n 1052) (.n 8))),
    .atom (.hint (.alloc (.n 1053) 128)),
    .atom (.load (.n 866) (.n 1053) 0), .atom (.load (.n 867) (.n 1053) 16),
    .atom (.load (.n 868) (.n 1053) 32), .atom (.load (.n 869) (.n 1053) 48),
    .atom (.load (.n 870) (.n 1053) 64),
    .atom (.const (.n 1054) (word 140737488355328 0 0)), .atom (.mul (.n 1055) (.n 7) (.n 1054)),
    .atom (.load (.n 1055) (.n 1053) 80), .atom (.load (.n 1050) (.n 1053) 96),
    .atom (.const (.n 1056) (word 1 0 0)), .atom (.load (.n 1056) (.n 1053) 112),
    .atom (.const (.n 1057) (word 1 0 0)), .atom (.add (.n 1058) (.n 1057) (.n 9)),
    .atom (.const (.n 1059) (word 1 0 0)),
    .callIf (.n 1058) (packLoopName first) [.n 1059, .n 9, .n 1053, .n 1051, .n 1052],
    .atom (.mul (.n 1060) (.n 1053) (.n 9)), .atom (.mul (.n 1061) (.n 9) (.n 9)),
    .atom (.mul (.n 1062) (.n 1061) (.n 1061)), .atom (.mul (.n 1063) (.n 1062) (.n 1062)),
    .atom (.mul (.n 1064) (.n 1051) (.n 1063)), .atom (.mul (.n 1065) (.n 9) (.n 9)),
    .atom (.mul (.n 1066) (.n 1065) (.n 1065)), .atom (.mul (.n 1067) (.n 1066) (.n 1066)),
    .atom (.mul (.n 1068) (.n 1052) (.n 1067)),
    .atom (.const (.n 1069) (word 1 0 0)), .atom (.add (.n 1070) (.n 1069) (.n 10)),
    .atom (.const (.n 1071) (word 1 0 0)),
    .callIf (.n 1070) (remLoopName first) [.n 1071, .n 10, .n 1060, .n 1064, .n 1068]]

/-- The last record (`rounds·step_g·rem_g`) read, the local point allocated. -/
def lastT : List Stmt :=
  [.atom (.mul (.n 1072) (.n 1060) (.n 10))] ++
    (List.range 8).map (fun j ↦ .atom (.load (.n (1073 + j)) (.n 1072) (16 * j))) ++
    [.atom (.hint (.alloc (.n 1081) 11))]

/-- `t`'s three words. -/
def tReadsT : List Stmt :=
  fsNextT (.n 1078) 33 1742 ++ fsNextT (.n 1078) 34 1752 ++ fsNextT (.n 1078) 35 1762

/-- The lane weights of the local point (`f_lanes[LANE_OFF + i]`). -/
def laneW (i : ℕ) : ℕ := eqfVal 1772 5 25 4 i

/-! ## The first claim's weight -/

/-- `Σ_lane f_lanes[lane]·lanes[lane]`, times `Π_t (1 + local_t (1 + g^(2^t)))`, from `B`. -/
def lanesEqT (lp loc : V) (f : ℕ → ℕ) (B : ℕ) : List Stmt :=
  [.atom (.load (.n B) lp 0), .atom (.mul (.n (B + 1)) (.n (f 0)) (.n B))] ++
  ((List.range 24).map fun i ↦
    [.atom (.load (.n (B + 2 + 3 * i)) lp (i + 1)),
      .atom (.mul (.n (B + 3 + 3 * i)) (.n (f (i + 1))) (.n (B + 2 + 3 * i))),
      .atom (.add (.n (B + 4 + 3 * i)) (.n (B + 1 + 3 * i))
        (.n (B + 3 + 3 * i)))]).flatten ++
  ((List.range 6).map fun t ↦
    [.atom (.const (.n (B + 74 + 6 * t)) (word 1 0 0)),
      .atom (.load (.n (B + 75 + 6 * t)) loc t),
      .atom (.const (.n (B + 76 + 6 * t)) (word (2 ^ (2 ^ t) + 1) 0 0)),
      .atom (.mul (.n (B + 77 + 6 * t)) (.n (B + 75 + 6 * t)) (.n (B + 76 + 6 * t))),
      .atom (.add (.n (B + 78 + 6 * t)) (.n (B + 74 + 6 * t)) (.n (B + 77 + 6 * t))),
      .atom (.mul (.n (B + 79 + 6 * t)) (.n (B + 73 + 6 * t)) (.n (B + 78 + 6 * t)))]).flatten

/-! ## A later claim's weight: `keccak_shifts_eq` -/

/-- Bit `t` of the two points from `B`: `a_t`, `b_t`, `1`, `1 + a_t`, `1`, `1 + b_t`,
`(1 + a_t)(1 + b_t)`, `a_t b_t`, then the weights `e_t = (1 + a_t)(1 + b_t) + a_t b_t`, and below
the top bit `u_t = a_t (1 + b_t)`, `v_t = (1 + a_t) b_t`, at the top bit `s_t = a_t + b_t`
(G:2586-2604). -/
def bitT (aP bP : V) (t B : ℕ) : List Stmt :=
  [.atom (.load (.n B) aP t), .atom (.load (.n (B + 1)) bP t),
    .atom (.const (.n (B + 2)) (word 1 0 0)), .atom (.add (.n (B + 3)) (.n (B + 2)) (.n B)),
    .atom (.const (.n (B + 4)) (word 1 0 0)), .atom (.add (.n (B + 5)) (.n (B + 4)) (.n (B + 1))),
    .atom (.mul (.n (B + 6)) (.n (B + 3)) (.n (B + 5))), .atom (.mul (.n (B + 7)) (.n B) (.n (B + 1))),
    .atom (.add (.n (B + 8)) (.n (B + 6)) (.n (B + 7)))] ++
  if t = 5 then [.atom (.add (.n (B + 9)) (.n B) (.n (B + 1)))]
  else [.atom (.mul (.n (B + 9)) (.n B) (.n (B + 5))), .atom (.mul (.n (B + 10)) (.n (B + 3)) (.n (B + 1)))]

/-- `carry_step(c0, c1, n0, n1, e, u, v, t)` from `B`. -/
def carryT (c0 c1 : ℕ → ℕ) (e u v : ℕ) (t B : ℕ) : List Stmt :=
  [.atom (.mul (.n B) (.n (c0 0)) (.n e)), .atom (.mul (.n (B + 1)) (.n (c0 0)) (.n u)),
    .atom (.mul (.n (B + 2)) (.n (c0 0)) (.n v))] ++
  ((List.range (2 ^ t - 1)).map fun i ↦
    [.atom (.mul (.n (B + 3 + 8 * i)) (.n (c0 (i + 1))) (.n e)),
      .atom (.mul (.n (B + 4 + 8 * i)) (.n (c1 (i + 1))) (.n u)),
      .atom (.add (.n (B + 5 + 8 * i)) (.n (B + 3 + 8 * i)) (.n (B + 4 + 8 * i))),
      .atom (.mul (.n (B + 6 + 8 * i)) (.n (c1 (i + 1))) (.n v)),
      .atom (.mul (.n (B + 7 + 8 * i)) (.n (c0 (i + 1))) (.n u)),
      .atom (.mul (.n (B + 8 + 8 * i)) (.n (c0 (i + 1))) (.n v)),
      .atom (.mul (.n (B + 9 + 8 * i)) (.n (c1 (i + 1))) (.n e)),
      .atom (.add (.n (B + 10 + 8 * i)) (.n (B + 8 + 8 * i)) (.n (B + 9 + 8 * i)))]).flatten

/-- Where `carryT` writes `n0[q]`. -/
def carryN0 (t B q : ℕ) : ℕ :=
  if q = 0 then B else if q = 2 ^ t then B + 1 else if q < 2 ^ t then B + 5 + 8 * (q - 1)
  else B + 7 + 8 * (q - 2 ^ t - 1)

/-- Where `carryT` writes `n1[q]` (`q ≠ 0`). -/
def carryN1 (t B q : ℕ) : ℕ :=
  if q = 2 ^ t then B + 2 else if q < 2 ^ t then B + 6 + 8 * (q - 1)
  else B + 10 + 8 * (q - 2 ^ t - 1)

/-- `carry_wrap(c0, c1, out, e, s, t)` from `B`. -/
def carryWrapT (c0 c1 : ℕ → ℕ) (e s : ℕ) (t B : ℕ) : List Stmt :=
  [.atom (.mul (.n B) (.n (c0 0)) (.n e)), .atom (.mul (.n (B + 1)) (.n (c0 0)) (.n s))] ++
  ((List.range (2 ^ t - 1)).map fun i ↦
    [.atom (.mul (.n (B + 2 + 6 * i)) (.n (c0 (i + 1))) (.n e)),
      .atom (.mul (.n (B + 3 + 6 * i)) (.n (c1 (i + 1))) (.n s)),
      .atom (.add (.n (B + 4 + 6 * i)) (.n (B + 2 + 6 * i)) (.n (B + 3 + 6 * i))),
      .atom (.mul (.n (B + 5 + 6 * i)) (.n (c0 (i + 1))) (.n s)),
      .atom (.mul (.n (B + 6 + 6 * i)) (.n (c1 (i + 1))) (.n e)),
      .atom (.add (.n (B + 7 + 6 * i)) (.n (B + 5 + 6 * i)) (.n (B + 6 + 6 * i)))]).flatten

/-- Where `carryWrapT` writes `out[q]`. -/
def wrapOut (t B q : ℕ) : ℕ :=
  if q = 0 then B else if q = 2 ^ t then B + 1 else if q < 2 ^ t then B + 4 + 6 * (q - 1)
  else B + 7 + 6 * (q - 2 ^ t - 1)

/-- The shifts `keccak_form` uses: `ρ` and `ρ + 1`, ascending (`KECCAK_SHIFT_USED`). -/
def shiftUsed : List ℕ :=
  ((List.range 64).filter fun r ↦ keccakRho.contains r || keccakRho.contains ((r + 63) % 64))

/-- `shifts[r]` for the used `r` from `b`: `low0[r % 8]·high[r / 8]`, plus
`low1[r % 8]·high[r / 8 + 1]` unless `r % 8 = 0`. -/
def shOutT (low0 low1 high : ℕ → ℕ) : List ℕ → ℕ → List Stmt
  | [], _ => []
  | r :: rs, b =>
      if r % 8 = 0 then
        .atom (.mul (.n b) (.n (low0 0)) (.n (high (r / 8)))) :: shOutT low0 low1 high rs (b + 1)
      else
        [.atom (.mul (.n b) (.n (low0 (r % 8))) (.n (high (r / 8)))),
          .atom (.mul (.n (b + 1)) (.n (low1 (r % 8))) (.n (high ((r / 8 + 1) % 8)))),
          .atom (.add (.n (b + 2)) (.n b) (.n (b + 1)))] ++ shOutT low0 low1 high rs (b + 3)

/-- Where `shOutT` writes `shifts[r]`. -/
def shOutV : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | r :: rs, b, q =>
      if r % 8 = 0 then (if q = r then b else shOutV rs (b + 1) q)
      else (if q = r then b + 2 else shOutV rs (b + 3) q)

/-- The bit weights' values from `B0`. -/
def bitEv (B0 t : ℕ) : ℕ := B0 + 11 * t + 8
def bitUv (B0 t : ℕ) : ℕ := B0 + 11 * t + 9
def bitVv (B0 t : ℕ) : ℕ := B0 + 11 * t + 10
def bitSv (B0 t : ℕ) : ℕ := B0 + 11 * t + 9

/-- `keccak_shifts_eq(a, b, shifts)` from `B0`: the six bits, the low carries (bits `1`, `2` on
bit `0`), the high ones (bit `4` on bit `3`, bit `5` wrapping), the used shifts. -/
def shiftsT (aP bP : V) (B0 : ℕ) : List Stmt :=
  ((List.range 6).map fun t ↦ bitT aP bP t (B0 + 11 * t)).flatten ++
  carryT (fun p ↦ if p = 0 then bitEv B0 0 else bitUv B0 0) (fun _ ↦ bitVv B0 0)
    (bitEv B0 1) (bitUv B0 1) (bitVv B0 1) 1 (B0 + 65) ++
  carryT (carryN0 1 (B0 + 65)) (carryN1 1 (B0 + 65)) (bitEv B0 2) (bitUv B0 2) (bitVv B0 2) 2
    (B0 + 76) ++
  carryT (fun p ↦ if p = 0 then bitEv B0 3 else bitUv B0 3) (fun _ ↦ bitVv B0 3)
    (bitEv B0 4) (bitUv B0 4) (bitVv B0 4) 1 (B0 + 103) ++
  carryWrapT (carryN0 1 (B0 + 103)) (carryN1 1 (B0 + 103)) (bitEv B0 5) (bitSv B0 5) 2 (B0 + 114) ++
  shOutT (carryN0 2 (B0 + 76)) (carryN1 2 (B0 + 76)) (wrapOut 2 (B0 + 114)) shiftUsed (B0 + 134)

/-- Where `shiftsT` writes `shifts[r]`. -/
def shiftsV (B0 r : ℕ) : ℕ := shOutV shiftUsed (B0 + 134) r

/-- The value after `shiftsT`. -/
def shiftsEnd (B0 : ℕ) : ℕ := B0 + 244

/-! ## A later claim's weight: `keccak_form` -/

/-- An addition onto a running sum (none: the first term, no statement). -/
def addOpt (o : Option ℕ) (v b : ℕ) : List Stmt × ℕ × ℕ :=
  match o with
  | none => ([], b, v)
  | some t => ([.atom (.add (.n b) (.n t) (.n v))], b + 1, b)

/-- The running sums of `keccak_form`: the total, a column's sums and its `f` sum. -/
structure FAcc where
  tot : Option ℕ
  acc : Option ℕ
  accn : Option ℕ
  facc : Option ℕ

/-- Lane `lane` from `b`: its weight read, `moved`, `f·moved` onto the total, `moved` and the
next shift's product onto the column, `f` onto the column's. -/
def formEnt (lp : V) (sh f : ℕ → ℕ) (lane b : ℕ) (st : FAcc) : List Stmt × ℕ × FAcc :=
  let r1 := addOpt st.tot (b + 2) (b + 3)
  let r2 := addOpt st.acc (b + 1) r1.2.1
  let r3 := addOpt st.accn r2.2.1 (r2.2.1 + 1)
  let r4 := addOpt st.facc (f lane) r3.2.1
  ([.atom (.load (.n b) lp (keccakPi lane)),
    .atom (.mul (.n (b + 1)) (.n b) (.n (sh (keccakRho.getD lane 0)))),
    .atom (.mul (.n (b + 2)) (.n (f lane)) (.n (b + 1)))] ++ r1.1 ++ r2.1 ++
    [.atom (.mul (.n r2.2.1) (.n b) (.n (sh ((keccakRho.getD lane 0 + 1) % 64))))] ++ r3.1 ++ r4.1,
    r4.2.1, ⟨some r1.2.2, some r2.2.2, some r3.2.2, some r4.2.2⟩)

/-- The lanes `x + 5y` of a column, `y ∈ ys`. -/
def formEnts (lp : V) (sh f : ℕ → ℕ) (x : ℕ) : List ℕ → ℕ → FAcc → List Stmt × ℕ × FAcc
  | [], b, st => ([], b, st)
  | y :: ys, b, st =>
      let e := formEnt lp sh f (x + 5 * y) b st
      let r := formEnts lp sh f x ys e.2.1 e.2.2
      (e.1 ++ r.1, r.2.1, r.2.2)

/-- The columns `x ∈ xs`: each one's lanes, then its sums copied (`column`, `column_next`,
`f_column`). Returns the statements, the next value, the total and the copies. -/
def formCols (lp : V) (sh f : ℕ → ℕ) : List ℕ → ℕ → Option ℕ →
    List Stmt × ℕ × Option ℕ × List (ℕ × ℕ × ℕ)
  | [], b, tot => ([], b, tot, [])
  | x :: xs, b, tot =>
      let e := formEnts lp sh f x [0, 1, 2, 3, 4] b ⟨tot, none, none, none⟩
      let b1 := e.2.1
      let r := formCols lp sh f xs (b1 + 3) e.2.2.tot
      (e.1 ++ [.atom (.copy (.n b1) (.n (e.2.2.acc.getD 0))),
          .atom (.copy (.n (b1 + 1)) (.n (e.2.2.accn.getD 0))),
          .atom (.copy (.n (b1 + 2)) (.n (e.2.2.facc.getD 0)))] ++ r.1,
        r.2.1, r.2.2.1, (b1, b1 + 1, b1 + 2) :: r.2.2.2)

/-- The final loop: `total += f_column[x]·(column[x + 1] + column_next[x - 1])`. -/
def formFin (cols : List (ℕ × ℕ × ℕ)) : List ℕ → ℕ → ℕ → List Stmt × ℕ × ℕ
  | [], b, tot => ([], b, tot)
  | x :: xs, b, tot =>
      let r := formFin cols xs (b + 3) (b + 2)
      ([.atom (.add (.n b) (.n (cols.getD ((x + 1) % 5) default).1)
          (.n (cols.getD ((x + 4) % 5) default).2.1)),
        .atom (.mul (.n (b + 1)) (.n (cols.getD x default).2.2) (.n b)),
        .atom (.add (.n (b + 2)) (.n tot) (.n (b + 1)))] ++ r.1, r.2.1, r.2.2)

/-- `keccak_form(lanes, shifts, f_lanes, LANE_OFF)` from `B`: the statements, the next value and
the total's value. -/
def formAll (lp : V) (sh f : ℕ → ℕ) (B : ℕ) : List Stmt × ℕ × ℕ :=
  let c := formCols lp sh f [0, 1, 2, 3, 4] B none
  let r := formFin c.2.2.2 [0, 1, 2, 3, 4] c.2.1 (c.2.2.1.getD 0)
  (c.1 ++ r.1, r.2.1, r.2.2)

/-! ## The weight section and the tail -/

/-- The weight section. -/
def weightT (first : ℕ) : List Stmt :=
  if first = 1 then
    .atom (.load (.n 1841) (.n 11) 3) :: lanesEqT (.n 1841) (.n 1081) laneW 1842
  else
    [.atom (.load (.n 1841) (.n 11) 3), .atom (.load (.n 1842) (.n 11) 4)] ++
      shiftsT (.n 1842) (.n 1081) 1843 ++
      (formAll (.n 1841) (shiftsV 1843) laneW (shiftsEnd 1843)).1

/-- The weight's value. -/
def weightVal (first : ℕ) : ℕ :=
  if first = 1 then 1951 else (formAll (.n 1841) (shiftsV 1843) laneW (shiftsEnd 1843)).2.2

/-- The value after the weight section. -/
def weightEnd (first : ℕ) : ℕ :=
  if first = 1 then 1952 else (formAll (.n 1841) (shiftsV 1843) laneW (shiftsEnd 1843)).2.1

/-- The next claim's lanes: `f[x] + β (f[x - 1] + β f[x - 2])` in each row, from `B`. -/
def lanesOutT (beta : ℕ) (f : ℕ → ℕ) (lp B : ℕ) : List Stmt :=
  ((List.range 25).map fun i ↦
    [.atom (.mul (.n (B + 4 * i)) (.n beta) (.n (f ((i % 5 + 3) % 5 + 5 * (i / 5))))),
      .atom (.add (.n (B + 4 * i + 1)) (.n (f ((i % 5 + 4) % 5 + 5 * (i / 5)))) (.n (B + 4 * i))),
      .atom (.mul (.n (B + 4 * i + 2)) (.n beta) (.n (B + 4 * i + 1))),
      .atom (.add (.n (B + 4 * i + 3)) (.n (f i)) (.n (B + 4 * i + 2))),
      .atom (.load (.n (B + 4 * i + 3)) (.n lp) i)]).flatten

/-- The value after `eqfT pt off n count b`. -/
def eqfEnd (n count b : ℕ) : ℕ := eqfBase b (n - 1) + 3 + 2 ^ (n - 1) + eqfK n count (n - 1)

/-- The lane and slice offsets of a later claim's weight at position `2^i - 1` of lane `0`: `θ`'s
transpose through `ρ`, `π`. -/
def flipOffs (i : ℕ) : List (ℕ × ℕ) :=
  (keccakPi 0, (2 ^ i - 1 + keccakRho.getD 0 0) % 64) ::
    (List.range 5).flatMap fun y ↦
      [(keccakPi (1 + 5 * y), (2 ^ i - 1 + keccakRho.getD (1 + 5 * y) 0) % 64),
        (keccakPi (4 + 5 * y), (2 ^ i + keccakRho.getD (4 + 5 * y) 0) % 64)]

/-- `slice_weight`'s factor for slice `z`: the top coordinate's (`top`) when `z ≥ 32`, else
`1 + top` (`top1`). -/
def topOf (top top1 z : ℕ) : ℕ := if z / 32 = 1 then top else top1

/-- Flip `i` from `b` (G:2868-2873): over `flipOffs i`, the lane weight read at `lp`, the slice
weight `slices[z % 32]·top(z)`, their product, summed; the flip at `b + 42`. -/
def lflipT (lp : V) (sl : ℕ → ℕ) (top top1 i b : ℕ) : List Stmt :=
  match flipOffs i with
  | [] => []
  | o :: os =>
      [.atom (.load (.n b) lp o.1), .atom (.mul (.n (b + 1)) (.n (sl (o.2 % 32))) (.n (topOf top top1 o.2))),
        .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1)))] ++
      ((List.range os.length).map fun k ↦
        [.atom (.load (.n (b + 3 + 4 * k)) lp (os.getD k default).1),
          .atom (.mul (.n (b + 4 + 4 * k)) (.n (sl ((os.getD k default).2 % 32)))
            (.n (topOf top top1 (os.getD k default).2))),
          .atom (.mul (.n (b + 5 + 4 * k)) (.n (b + 3 + 4 * k)) (.n (b + 4 + 4 * k))),
          .atom (.add (.n (b + 6 + 4 * k)) (.n (b + 2 + 4 * k))
            (.n (b + 5 + 4 * k)))]).flatten

/-- The slice tree of the local point's first five coordinates, from `E0`. -/
def sliceB (W : ℕ) : ℕ := W + 134

/-- The top coordinate, `top`; `top1 = 1 + top` at `+ 2`; the flips' buffer at `+ 3`. -/
def topV (W : ℕ) : ℕ := eqfEnd 5 32 (sliceB W)

/-- The flips, from `topV W + 4`, each `43` values; then their stores and the flips' pointer. -/
def lflipsT (W : ℕ) : List Stmt :=
  ((List.range 7).map fun i ↦
    lflipT (.n (W + 33)) (eqfVal (sliceB W) 5 32 4) (topV W) (topV W + 2) i (topV W + 4 + 43 * i) ++
      [.atom (.load (.n (topV W + 4 + 43 * i + 42)) (.n (topV W + 3)) i)]).flatten

/-- The final check, the squeeze of `β`, the next claim's record, its flips, the return; `W` the
first value, `wv` the weight's. -/
def tailT (W wv : ℕ) : List Stmt :=
  [.atom (.copy (.n W) (.n wv)), .atom (.mul (.n (W + 1)) (.n 1080) (.n W)),
    .atom (.mul (.n (W + 2)) (.n 958) (.n 1742)),
    .atom (.add (.n (W + 3)) (.n 958) (.n 1752)),
    .atom (.mul (.n (W + 4)) (.n (W + 3)) (.n 1762)),
    .atom (.add (.n (W + 5)) (.n (W + 2)) (.n (W + 4))),
    .atom (.mul (.n (W + 6)) (.n (W + 1)) (.n (W + 5))),
    .atom (.assertEq (.n (W + 6)) (.n 1741)),
    .atom (.const (.n (W + 7)) (word 0 0 0)), .atom (.const (.n (W + 8)) (word 0 0 0)),
    keccakA ([.n 1749, .n 1751, .n 1759, .n 1761, .n 1769, .n 1771, .n (W + 7), .n (W + 8)] ++
      cap5 1722) ((List.range 13).map fun k ↦ .n (W + 9 + k))] ++
  challengeT (.n (W + 9)) (.n (W + 10)) (W + 22) ++
  [.atom (.mul (.n (W + 29)) (.n (W + 28)) (.n 1762)),
    .atom (.add (.n (W + 30)) (.n 1752) (.n (W + 29))),
    .atom (.mul (.n (W + 31)) (.n (W + 28)) (.n (W + 30))),
    .atom (.add (.n (W + 32)) (.n 1742) (.n (W + 31))),
    .atom (.load (.n (W + 32)) (.n 12) 0), .atom (.load (.n 1052) (.n 12) 2),
    .atom (.load (.n 1081) (.n 12) 4), .atom (.hint (.alloc (.n (W + 33)) 25))] ++
  lanesOutT (W + 28) laneW (W + 33) (W + 34) ++
  [.atom (.load (.n (W + 33)) (.n 12) 3)] ++
  eqfT (.n 1081) 0 5 32 (sliceB W) ++
  [.atom (.load (.n (topV W)) (.n 1081) 5), .atom (.const (.n (topV W + 1)) (word 1 0 0)),
    .atom (.add (.n (topV W + 2)) (.n (topV W + 1)) (.n (topV W))),
    .atom (.hint (.alloc (.n (topV W + 3)) 7))] ++
  lflipsT W ++
  [.atom (.load (.n (topV W + 3)) (.n 12) 5)] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (topV W + 305 + j)) (.n (W + 17 + j)))) ++
  [.atom (.const (.n (topV W + 310)) (word 68719476736 0 0)),
    .atom (.mul (.n (topV W + 311)) (.n 1078) (.n (topV W + 310))),
    .atom (.copy (.n (topV W + 312)) (.n (topV W + 311))),
    .ret [.n (topV W + 305), .n (topV W + 306), .n (topV W + 307), .n (topV W + 308),
      .n (topV W + 309), .n (topV W + 312)]]

/-! ## The template -/

/-- **`keccak_layer__L{first}`'s body.** -/
def layerT (first : ℕ) : List Stmt :=
  headT first ++ prodT (.n 7) (muB first) (prodTab first) ++ checkT (accL first) ++
    sqT first ++ rmfeBlockT ++ hornerT (fun k ↦ ((prodTab first).getD k default).a) 877 959 ++
    packSetupT first ++ lastT ++
    localRoundsT (.n 1078) (.n 1081) (.n 1079) (cap5 1073) 1082 11 ++
    tReadsT ++ eqfT (.n 1081) 6 5 25 1772 ++
    weightT first ++ tailT (weightEnd first) (weightVal first)

end
end LeanVM.Guest.B1.VerifySub
