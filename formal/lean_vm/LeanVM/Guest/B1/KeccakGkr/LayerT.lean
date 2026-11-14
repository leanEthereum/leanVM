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

The specializations `keccak_layer__L{first}` (G:2644-2825) compile to one statement list up to
the head (`first = 1` copies the waiting word's two cells), the product's table (`prodTab first`),
the grind before `s` (`sqT first`: at `first = 1` a full queue's permutation, then the nonce's
with the padding run; at `first = 0` the nonce the fourth scalar waiting), and the first layer's
weight section; from the nonce's permutation on, `__L1`'s values are `__L0`'s plus
`layOff first = 20 * first` (the templates' `o`). Sections:

* `headT`: the carried capacity (and, first, the waiting word's cells) copied, the claim's sixteen
  instance weights read (`KC_MU`), and the readers, a straight line of sums over them
  (`KECCAK_PROJ_A`, `KECCAK_PROJ_B`, G:2660-2664);
* `prodT` (`Prod`): the product's 47 coefficients read and absorbed, and their projection, each
  coefficient times its reader (`KECCAK_PROJ_OUT`);
* `checkT`: the projection plus `ι·κ` against the claim's value;
* `sqT`: the grind of `3` bits and the squeeze of `s`; `rmfeBlockT` (`LayerRmfe`): the instance weights at `s`;
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
def muB (first : ℕ) : ℕ := 20 + 2 * first

/-- The capacity (and the waiting cells) copied, the instance weights read, the readers. -/
def headT (first : ℕ) : List Stmt :=
  (List.range (5 + 2 * first)).map (fun i ↦ .atom (.copy (.n (15 + i)) (.n i))) ++
    (List.range 16).map (fun i ↦ .atom (.load (.n (muB first + i)) (.n 11) (6 + i))) ++
    (List.range 111).map fun t ↦ .atom (.add (.n (muB first + 16 + t))
      (.n (muB first + projA.getD t 0)) (.n (muB first + projB.getD t 0)))

/-- Coefficient `k`'s reader, as `Prod`'s index list. -/
def projR (k : ℕ) : List ℕ := [projOut.getD k 0]

/-! ## The product's tables -/

/-- The product section's table, first = 1. -/
def prodTab1 : List PPos := [
    ⟨149, none, 150, [119], 0, 152, none, 152⟩,
    ⟨153, none, 154, [40], 0, 156, some 152, 157⟩,
    ⟨158, none, 159, [40], 0, 161, some 157, 162⟩,
    ⟨163, some ([20, 21, 150, 151, 154, 155, 159, 160, 15, 16, 17, 18, 19], 164), 177, [49], 0, 179, some 162, 180⟩,
    ⟨181, none, 182, [116], 0, 184, some 180, 185⟩,
    ⟨186, none, 187, [93], 0, 189, some 185, 190⟩,
    ⟨191, none, 192, [70], 0, 194, some 190, 195⟩,
    ⟨196, some ([177, 178, 182, 183, 187, 188, 192, 193, 172, 173, 174, 175, 176], 197), 210, [112], 0, 212, some 195, 213⟩,
    ⟨214, none, 215, [74], 0, 217, some 213, 218⟩,
    ⟨219, none, 220, [83], 0, 222, some 218, 223⟩,
    ⟨224, none, 225, [109], 0, 227, some 223, 228⟩,
    ⟨229, some ([210, 211, 215, 216, 220, 221, 225, 226, 205, 206, 207, 208, 209], 230), 243, [117], 0, 245, some 228, 246⟩,
    ⟨247, none, 248, [94], 0, 250, some 246, 251⟩,
    ⟨252, none, 253, [98], 0, 255, some 251, 256⟩,
    ⟨257, none, 258, [57], 0, 260, some 256, 261⟩,
    ⟨262, some ([243, 244, 248, 249, 253, 254, 258, 259, 238, 239, 240, 241, 242], 263), 276, [101], 0, 278, some 261, 279⟩,
    ⟨280, none, 281, [104], 0, 283, some 279, 284⟩,
    ⟨285, none, 286, [126], 0, 288, some 284, 289⟩,
    ⟨290, none, 291, [124], 0, 293, some 289, 294⟩,
    ⟨295, some ([276, 277, 281, 282, 286, 287, 291, 292, 271, 272, 273, 274, 275], 296), 309, [108], 0, 311, some 294, 312⟩,
    ⟨313, none, 314, [123], 0, 316, some 312, 317⟩,
    ⟨318, none, 319, [113], 0, 321, some 317, 322⟩,
    ⟨323, none, 324, [121], 0, 326, some 322, 327⟩,
    ⟨328, some ([309, 310, 314, 315, 319, 320, 324, 325, 304, 305, 306, 307, 308], 329), 342, [85], 0, 344, some 327, 345⟩,
    ⟨346, none, 347, [122], 0, 349, some 345, 350⟩,
    ⟨351, none, 352, [99], 0, 354, some 350, 355⟩,
    ⟨356, none, 357, [120], 0, 359, some 355, 360⟩,
    ⟨361, some ([342, 343, 347, 348, 352, 353, 357, 358, 337, 338, 339, 340, 341], 362), 375, [107], 0, 377, some 360, 378⟩,
    ⟨379, none, 380, [114], 0, 382, some 378, 383⟩,
    ⟨384, none, 385, [56], 0, 387, some 383, 388⟩,
    ⟨389, none, 390, [103], 0, 392, some 388, 393⟩,
    ⟨394, some ([375, 376, 380, 381, 385, 386, 390, 391, 370, 371, 372, 373, 374], 395), 408, [96], 0, 410, some 393, 411⟩,
    ⟨412, none, 413, [87], 0, 415, some 411, 416⟩,
    ⟨417, none, 418, [89], 0, 420, some 416, 421⟩,
    ⟨422, none, 423, [88], 0, 425, some 421, 426⟩,
    ⟨427, some ([408, 409, 413, 414, 418, 419, 423, 424, 403, 404, 405, 406, 407], 428), 441, [115], 0, 443, some 426, 444⟩,
    ⟨445, none, 446, [72], 0, 448, some 444, 449⟩,
    ⟨450, none, 451, [64], 0, 453, some 449, 454⟩,
    ⟨455, none, 456, [111], 0, 458, some 454, 459⟩,
    ⟨460, some ([441, 442, 446, 447, 451, 452, 456, 457, 436, 437, 438, 439, 440], 461), 474, [92], 0, 476, some 459, 477⟩,
    ⟨478, none, 479, [97], 0, 481, some 477, 482⟩,
    ⟨483, none, 484, [110], 0, 486, some 482, 487⟩,
    ⟨488, none, 489, [125], 0, 491, some 487, 492⟩,
    ⟨493, some ([474, 475, 479, 480, 484, 485, 489, 490, 469, 470, 471, 472, 473], 494), 507, [73], 0, 509, some 492, 510⟩,
    ⟨511, none, 512, [100], 0, 514, some 510, 515⟩,
    ⟨516, none, 517, [55], 0, 519, some 515, 520⟩,
    ⟨521, none, 522, [118], 0, 524, some 520, 525⟩]

/-- The product section's table, first = 0. -/
def prodTab0 : List PPos := [
    ⟨147, none, 148, [119], 0, 150, none, 150⟩,
    ⟨151, none, 152, [40], 0, 154, some 150, 155⟩,
    ⟨156, none, 157, [40], 0, 159, some 155, 160⟩,
    ⟨161, none, 162, [49], 0, 164, some 160, 165⟩,
    ⟨166, some ([148, 149, 152, 153, 157, 158, 162, 163, 15, 16, 17, 18, 19], 167), 180, [116], 0, 182, some 165, 183⟩,
    ⟨184, none, 185, [93], 0, 187, some 183, 188⟩,
    ⟨189, none, 190, [70], 0, 192, some 188, 193⟩,
    ⟨194, none, 195, [112], 0, 197, some 193, 198⟩,
    ⟨199, some ([180, 181, 185, 186, 190, 191, 195, 196, 175, 176, 177, 178, 179], 200), 213, [74], 0, 215, some 198, 216⟩,
    ⟨217, none, 218, [83], 0, 220, some 216, 221⟩,
    ⟨222, none, 223, [109], 0, 225, some 221, 226⟩,
    ⟨227, none, 228, [117], 0, 230, some 226, 231⟩,
    ⟨232, some ([213, 214, 218, 219, 223, 224, 228, 229, 208, 209, 210, 211, 212], 233), 246, [94], 0, 248, some 231, 249⟩,
    ⟨250, none, 251, [98], 0, 253, some 249, 254⟩,
    ⟨255, none, 256, [57], 0, 258, some 254, 259⟩,
    ⟨260, none, 261, [101], 0, 263, some 259, 264⟩,
    ⟨265, some ([246, 247, 251, 252, 256, 257, 261, 262, 241, 242, 243, 244, 245], 266), 279, [104], 0, 281, some 264, 282⟩,
    ⟨283, none, 284, [126], 0, 286, some 282, 287⟩,
    ⟨288, none, 289, [124], 0, 291, some 287, 292⟩,
    ⟨293, none, 294, [108], 0, 296, some 292, 297⟩,
    ⟨298, some ([279, 280, 284, 285, 289, 290, 294, 295, 274, 275, 276, 277, 278], 299), 312, [123], 0, 314, some 297, 315⟩,
    ⟨316, none, 317, [113], 0, 319, some 315, 320⟩,
    ⟨321, none, 322, [121], 0, 324, some 320, 325⟩,
    ⟨326, none, 327, [85], 0, 329, some 325, 330⟩,
    ⟨331, some ([312, 313, 317, 318, 322, 323, 327, 328, 307, 308, 309, 310, 311], 332), 345, [122], 0, 347, some 330, 348⟩,
    ⟨349, none, 350, [99], 0, 352, some 348, 353⟩,
    ⟨354, none, 355, [120], 0, 357, some 353, 358⟩,
    ⟨359, none, 360, [107], 0, 362, some 358, 363⟩,
    ⟨364, some ([345, 346, 350, 351, 355, 356, 360, 361, 340, 341, 342, 343, 344], 365), 378, [114], 0, 380, some 363, 381⟩,
    ⟨382, none, 383, [56], 0, 385, some 381, 386⟩,
    ⟨387, none, 388, [103], 0, 390, some 386, 391⟩,
    ⟨392, none, 393, [96], 0, 395, some 391, 396⟩,
    ⟨397, some ([378, 379, 383, 384, 388, 389, 393, 394, 373, 374, 375, 376, 377], 398), 411, [87], 0, 413, some 396, 414⟩,
    ⟨415, none, 416, [89], 0, 418, some 414, 419⟩,
    ⟨420, none, 421, [88], 0, 423, some 419, 424⟩,
    ⟨425, none, 426, [115], 0, 428, some 424, 429⟩,
    ⟨430, some ([411, 412, 416, 417, 421, 422, 426, 427, 406, 407, 408, 409, 410], 431), 444, [72], 0, 446, some 429, 447⟩,
    ⟨448, none, 449, [64], 0, 451, some 447, 452⟩,
    ⟨453, none, 454, [111], 0, 456, some 452, 457⟩,
    ⟨458, none, 459, [92], 0, 461, some 457, 462⟩,
    ⟨463, some ([444, 445, 449, 450, 454, 455, 459, 460, 439, 440, 441, 442, 443], 464), 477, [97], 0, 479, some 462, 480⟩,
    ⟨481, none, 482, [110], 0, 484, some 480, 485⟩,
    ⟨486, none, 487, [125], 0, 489, some 485, 490⟩,
    ⟨491, none, 492, [73], 0, 494, some 490, 495⟩,
    ⟨496, some ([477, 478, 482, 483, 487, 488, 492, 493, 472, 473, 474, 475, 476], 497), 510, [100], 0, 512, some 495, 513⟩,
    ⟨514, none, 515, [55], 0, 517, some 513, 518⟩,
    ⟨519, none, 520, [118], 0, 522, some 518, 523⟩]

/-- The product section's table. -/
def prodTab (first : ℕ) : List PPos := if first = 1 then prodTab1 else prodTab0

/-- The last running sum. -/
def accL (first : ℕ) : ℕ := if first = 1 then 525 else 523

/-- The offset of the values from the nonce's permutation on: `__L1`'s are `__L0`'s plus `20`. -/
def layOff (first : ℕ) : ℕ := 20 * first

/-! ## Head, check, squeeze, Horner -/

/-- The projection plus `ι·κ` against the claim's value. -/
def checkT (a : ℕ) : List Stmt :=
  [.atom (.load (.n (a + 1)) (.n 11) 1), .atom (.mul (.n (a + 2)) (.n 13) (.n (a + 1))),
    .atom (.add (.n (a + 3)) (.n a) (.n (a + 2))), .atom (.load (.n (a + 4)) (.n 11) 0),
    .atom (.assertEq (.n (a + 3)) (.n (a + 4)))]

/-- The cells of the permutation of the waiting scalars and the nonce (`first = 0`), or of the full
queue (`first = 1`). -/
def sqIns : ℕ → List V
  | 1 => [.n 507, .n 508, .n 512, .n 513, .n 517, .n 518, .n 522, .n 523,
      .n 502, .n 503, .n 504, .n 505, .n 506]
  | _ => [.n 510, .n 511, .n 515, .n 516, .n 520, .n 521, .n 529, .n 530,
      .n 505, .n 506, .n 507, .n 508, .n 509]

/-- The grind before `s` and its squeeze: the nonce read at the cursor's word `47`
(`fs_absorb_nonce`), its permutation (outputs from `layOff first + 531`, after the full queue's at
`first = 1`), `grind_check` of `3` bits on its output `1`, and `s` its output `0` copied to
`layOff first + 544`. -/
def sqT (first : ℕ) : List Stmt :=
  if first = 1 then
    [keccakA (sqIns 1) ((List.range 13).map fun k ↦ .n (530 + k))] ++ fsNonceT (.n 7) 47 543 ++
      padRunT 546 ++
      [keccakA (permIns 1 [.n 544, .n 545] 547 (cap5 538)) ((List.range 13).map fun k ↦ .n (551 + k)),
        grindCallT 3 (.n 552) (.n 14)] ++ challengeT (.n 551) 564
  else
    fsNonceT (.n 7) 47 528 ++
      [keccakA (sqIns 0) ((List.range 13).map fun k ↦ .n (531 + k)),
        grindCallT 3 (.n 532) (.n 14)] ++ challengeT (.n 531) 544

/-- The product at `s`, Horner from the top coefficient `a 46`, from the value `b`. -/
def hornerT (a : ℕ → ℕ) (s b : ℕ) : List Stmt :=
  ((List.range 46).map fun j ↦
    [.atom (.mul (.n (b + 2 * j)) (.n (if j = 0 then a 46 else b + 2 * j - 1)) (.n s)),
      .atom (.add (.n (b + 2 * j + 1)) (.n (b + 2 * j)) (.n (a (45 - j))))]).flatten

/-! ## The pack rounds and the local rounds -/

/-- The pack rounds' first record (`rounds`, `o + 720`: the capacity after `s`, the cursor past the
product and the nonce, the product at `s`, the scale `1`), the eight-round loop on `step_g`, and
the remainder loop on `rem_g` from `rounds·step_g`, `prev_point·step_g⁸`, `point·step_g⁸`. -/
def packSetupT (o first : ℕ) : List Stmt :=
  [.atom (.load (.n (o + 718)) (.n 11) 2), .atom (.hint (.allocDyn (.n (o + 719)) (.n 8))),
    .atom (.hint (.alloc (.n (o + 720)) 128)),
    .atom (.load (.n (o + 539)) (.n (o + 720)) 0), .atom (.load (.n (o + 540)) (.n (o + 720)) 16),
    .atom (.load (.n (o + 541)) (.n (o + 720)) 32), .atom (.load (.n (o + 542)) (.n (o + 720)) 48),
    .atom (.load (.n (o + 543)) (.n (o + 720)) 64),
    .atom (.const (.n (o + 721)) (word 281474976710656 0)),
    .atom (.mul (.n (o + 722)) (.n 7) (.n (o + 721))),
    .atom (.load (.n (o + 722)) (.n (o + 720)) 80), .atom (.load (.n (o + 717)) (.n (o + 720)) 96),
    .atom (.const (.n (o + 723)) (word 1 0)), .atom (.load (.n (o + 723)) (.n (o + 720)) 112),
    .atom (.const (.n (o + 724)) (word 1 0)), .atom (.add (.n (o + 725)) (.n (o + 724)) (.n 9)),
    .atom (.const (.n (o + 726)) (word 1 0)),
    .callIf (.n (o + 725)) (packLoopName first)
      [.n (o + 726), .n 9, .n (o + 720), .n (o + 718), .n (o + 719), .n 14],
    .atom (.mul (.n (o + 727)) (.n (o + 720)) (.n 9)), .atom (.mul (.n (o + 728)) (.n 9) (.n 9)),
    .atom (.mul (.n (o + 729)) (.n (o + 728)) (.n (o + 728))),
    .atom (.mul (.n (o + 730)) (.n (o + 729)) (.n (o + 729))),
    .atom (.mul (.n (o + 731)) (.n (o + 718)) (.n (o + 730))),
    .atom (.mul (.n (o + 732)) (.n 9) (.n 9)),
    .atom (.mul (.n (o + 733)) (.n (o + 732)) (.n (o + 732))),
    .atom (.mul (.n (o + 734)) (.n (o + 733)) (.n (o + 733))),
    .atom (.mul (.n (o + 735)) (.n (o + 719)) (.n (o + 734))),
    .atom (.const (.n (o + 736)) (word 1 0)), .atom (.add (.n (o + 737)) (.n (o + 736)) (.n 10)),
    .atom (.const (.n (o + 738)) (word 1 0)),
    .callIf (.n (o + 737)) (remLoopName first)
      [.n (o + 738), .n 10, .n (o + 727), .n (o + 731), .n 14, .n (o + 735)]]

/-- The last record (`rounds·step_g·rem_g`) read, the local point allocated. -/
def lastT (o : ℕ) : List Stmt :=
  [.atom (.mul (.n (o + 739)) (.n (o + 727)) (.n 10))] ++
    (List.range 8).map (fun j ↦ .atom (.load (.n (o + 740 + j)) (.n (o + 739)) (16 * j))) ++
    [.atom (.hint (.alloc (.n (o + 748)) 11))]

/-- `t`'s three words. -/
def tReadsT (o : ℕ) : List Stmt :=
  fsNextT (.n (o + 745)) 33 (o + 1112) ++ fsNextT (.n (o + 745)) 34 (o + 1115) ++
    fsNextT (.n (o + 745)) 35 (o + 1118)

/-- The lane weights of the local point (`f_lanes[LANE_OFF + i]`). -/
def laneW (o i : ℕ) : ℕ := eqfVal (o + 1121) 5 25 4 i

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
    [.atom (.const (.n (B + 74 + 6 * t)) (word 1 0)),
      .atom (.load (.n (B + 75 + 6 * t)) loc t),
      .atom (.const (.n (B + 76 + 6 * t)) (word (2 ^ (2 ^ t) + 1) 0)),
      .atom (.mul (.n (B + 77 + 6 * t)) (.n (B + 75 + 6 * t)) (.n (B + 76 + 6 * t))),
      .atom (.add (.n (B + 78 + 6 * t)) (.n (B + 74 + 6 * t)) (.n (B + 77 + 6 * t))),
      .atom (.mul (.n (B + 79 + 6 * t)) (.n (B + 73 + 6 * t)) (.n (B + 78 + 6 * t)))]).flatten

/-! ## A later claim's weight: `keccak_shifts_eq` -/

/-- Bit `t` of the two points from `B`: `a_t`, `b_t`, `1`, `1 + a_t`, `1`, `1 + b_t`,
`(1 + a_t)(1 + b_t)`, `a_t b_t`, then the weights `e_t = (1 + a_t)(1 + b_t) + a_t b_t`, and below
the top bit `u_t = a_t (1 + b_t)`, `v_t = (1 + a_t) b_t`, at the top bit `s_t = a_t + b_t`
(G:2536-2554). -/
def bitT (aP bP : V) (t B : ℕ) : List Stmt :=
  [.atom (.load (.n B) aP t), .atom (.load (.n (B + 1)) bP t),
    .atom (.const (.n (B + 2)) (word 1 0)), .atom (.add (.n (B + 3)) (.n (B + 2)) (.n B)),
    .atom (.const (.n (B + 4)) (word 1 0)), .atom (.add (.n (B + 5)) (.n (B + 4)) (.n (B + 1))),
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
def weightT (first o : ℕ) : List Stmt :=
  if first = 1 then
    .atom (.load (.n (o + 1190)) (.n 11) 3) :: lanesEqT (.n (o + 1190)) (.n (o + 748)) (laneW o)
      (o + 1191)
  else
    [.atom (.load (.n (o + 1190)) (.n 11) 3), .atom (.load (.n (o + 1191)) (.n 11) 4)] ++
      shiftsT (.n (o + 1191)) (.n (o + 748)) (o + 1192) ++
      (formAll (.n (o + 1190)) (shiftsV (o + 1192)) (laneW o) (shiftsEnd (o + 1192))).1

/-- The weight's value. -/
def weightVal (first o : ℕ) : ℕ :=
  if first = 1 then o + 1300
  else (formAll (.n (o + 1190)) (shiftsV (o + 1192)) (laneW o) (shiftsEnd (o + 1192))).2.2

/-- The value after the weight section. -/
def weightEnd (first o : ℕ) : ℕ :=
  if first = 1 then o + 1301
  else (formAll (.n (o + 1190)) (shiftsV (o + 1192)) (laneW o) (shiftsEnd (o + 1192))).2.1

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

/-- Flip `i` from `b` (G:2818-2823): over `flipOffs i`, the lane weight read at `lp`, the slice
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
def sliceB (W : ℕ) : ℕ := W + 128

/-- The top coordinate, `top`; `top1 = 1 + top` at `+ 2`; the flips' buffer at `+ 3`. -/
def topV (W : ℕ) : ℕ := eqfEnd 5 32 (sliceB W)

/-- The flips, from `topV W + 4`, each `43` values; then their stores and the flips' pointer. -/
def lflipsT (W : ℕ) : List Stmt :=
  ((List.range 7).map fun i ↦
    lflipT (.n (W + 27)) (eqfVal (sliceB W) 5 32 4) (topV W) (topV W + 2) i (topV W + 4 + 43 * i) ++
      [.atom (.load (.n (topV W + 4 + 43 * i + 42)) (.n (topV W + 3)) i)]).flatten

/-- The final check, the squeeze of `β`, the next claim's record, its flips, the return; `W` the
first value, `wv` the weight's. -/
def tailT (o W wv : ℕ) : List Stmt :=
  [.atom (.copy (.n W) (.n wv)), .atom (.mul (.n (W + 1)) (.n (o + 747)) (.n W)),
    .atom (.mul (.n (W + 2)) (.n (o + 625)) (.n (o + 1112))),
    .atom (.add (.n (W + 3)) (.n (o + 625)) (.n (o + 1115))),
    .atom (.mul (.n (W + 4)) (.n (W + 3)) (.n (o + 1118))),
    .atom (.add (.n (W + 5)) (.n (W + 2)) (.n (W + 4))),
    .atom (.mul (.n (W + 6)) (.n (W + 1)) (.n (W + 5))),
    .atom (.assertEq (.n (W + 6)) (.n (o + 1111))),
    .atom (.const (.n (W + 7)) (word 0 0)), .atom (.const (.n (W + 8)) (word 0 0)),
    keccakA ([.n (o + 1113), .n (o + 1114), .n (o + 1116), .n (o + 1117), .n (o + 1119),
      .n (o + 1120), .n (W + 7), .n (W + 8)] ++ cap5 (o + 1098))
      ((List.range 13).map fun k ↦ .n (W + 9 + k))] ++
  challengeT (.n (W + 9)) (W + 22) ++
  [.atom (.mul (.n (W + 23)) (.n (W + 22)) (.n (o + 1118))),
    .atom (.add (.n (W + 24)) (.n (o + 1115)) (.n (W + 23))),
    .atom (.mul (.n (W + 25)) (.n (W + 22)) (.n (W + 24))),
    .atom (.add (.n (W + 26)) (.n (o + 1112)) (.n (W + 25))),
    .atom (.load (.n (W + 26)) (.n 12) 0), .atom (.load (.n (o + 719)) (.n 12) 2),
    .atom (.load (.n (o + 748)) (.n 12) 4), .atom (.hint (.alloc (.n (W + 27)) 25))] ++
  lanesOutT (W + 22) (laneW o) (W + 27) (W + 28) ++
  [.atom (.load (.n (W + 27)) (.n 12) 3)] ++
  eqfT (.n (o + 748)) 0 5 32 (sliceB W) ++
  [.atom (.load (.n (topV W)) (.n (o + 748)) 5), .atom (.const (.n (topV W + 1)) (word 1 0)),
    .atom (.add (.n (topV W + 2)) (.n (topV W + 1)) (.n (topV W))),
    .atom (.hint (.alloc (.n (topV W + 3)) 7))] ++
  lflipsT W ++
  [.atom (.load (.n (topV W + 3)) (.n 12) 5)] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (topV W + 305 + j)) (.n (W + 17 + j)))) ++
  [.atom (.const (.n (topV W + 310)) (word 68719476736 0)),
    .atom (.mul (.n (topV W + 311)) (.n (o + 745)) (.n (topV W + 310))),
    .atom (.copy (.n (topV W + 312)) (.n (topV W + 311))),
    .ret [.n (topV W + 305), .n (topV W + 306), .n (topV W + 307), .n (topV W + 308),
      .n (topV W + 309), .n (topV W + 312)]]

/-! ## The template -/

/-- **`keccak_layer__L{first}`'s body.** -/
def layerT (first : ℕ) : List Stmt :=
  headT first ++ prodT (.n 7) (muB first) (prodTab first) ++ checkT (accL first) ++
    sqT first ++ rmfeBlockT (layOff first) ++
    hornerT (fun k ↦ ((prodTab first).getD k default).a) (layOff first + 544) (layOff first + 626) ++
    packSetupT (layOff first) first ++ lastT (layOff first) ++
    localRoundsT (.n (layOff first + 745)) (.n (layOff first + 748)) (.n (layOff first + 746))
      (cap5 (layOff first + 740)) (layOff first + 749) 11 ++
    tReadsT (layOff first) ++ eqfT (.n (layOff first + 748)) 6 5 25 (layOff first + 1121) ++
    weightT first (layOff first) ++
    tailT (layOff first) (weightEnd first (layOff first)) (weightVal first (layOff first))

end
end LeanVM.Guest.B1.VerifySub
