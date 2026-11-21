/-
  LeanVM.Guest.B1.KeccakGkr.LayerT

  `keccak_layer`'s two specializations as one template (`layerT first`), section by section.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Prod
public import LeanVM.Guest.B1.KeccakGkr.LayerRmfe
public import LeanVM.Guest.B1.KeccakGkr.EqFrame
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# `keccak_layer` as a template

The specializations `keccak_layer__L{first}` compile to one statement list up to
the head (`first = 1` copies the waiting word's two cells), the product's table (`prodTab first`),
the grind before `s` (`sqT first`: at `first = 1` a full queue's permutation, then the nonce's
with the padding run; at `first = 0` the nonce the fourth scalar waiting), and the first layer's
weight section; from the nonce's permutation on, `__L1`'s values are `__L0`'s plus
`layOff first = 20 * first` (the templates' `o`). Sections:

* `headT`: the carried capacity (and, first, the waiting word's cells) copied, the claim's sixteen
  instance weights read (`KC_MU`), and the readers, a straight line of sums over them
  (`KECCAK_PROJ_A`, `KECCAK_PROJ_B`);
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
def muB (first : ℕ) : ℕ := 21 + 2 * first

/-- The capacity (and the waiting cells) copied, the instance weights read, the readers. -/
def headT (first : ℕ) : List Stmt :=
  (List.range (5 + 2 * first)).map (fun i ↦ .atom (.copy (.n (16 + i)) (.n i))) ++
    (List.range 16).map (fun i ↦ .atom (.load (.n (muB first + i)) (.n (valf% «keccak_layer» "claim")) (6 + i))) ++
    (List.range 111).map fun t ↦ .atom (.add (.n (muB first + 16 + t))
      (.n (muB first + projA.getD t 0)) (.n (muB first + projB.getD t 0)))

/-- Coefficient `k`'s reader, as `Prod`'s index list. -/
def projR (k : ℕ) : List ℕ := [projOut.getD k 0]

/-! ## The product's tables -/

/-- The product section's table, first = 1. -/
def prodTab1 : List PPos := [
    ⟨150, none, 151, [119], 0, 153, none, 153⟩,
    ⟨154, none, 155, [40], 0, 157, some 153, 158⟩,
    ⟨159, none, 160, [40], 0, 162, some 158, 163⟩,
    ⟨164, some ([21, 22, 151, 152, 155, 156, 160, 161, 16, 17, 18, 19, 20], 165), 178, [49], 0, 180, some 163, 181⟩,
    ⟨182, none, 183, [116], 0, 185, some 181, 186⟩,
    ⟨187, none, 188, [93], 0, 190, some 186, 191⟩,
    ⟨192, none, 193, [70], 0, 195, some 191, 196⟩,
    ⟨197, some ([178, 179, 183, 184, 188, 189, 193, 194, 173, 174, 175, 176, 177], 198), 211, [112], 0, 213, some 196, 214⟩,
    ⟨215, none, 216, [74], 0, 218, some 214, 219⟩,
    ⟨220, none, 221, [83], 0, 223, some 219, 224⟩,
    ⟨225, none, 226, [109], 0, 228, some 224, 229⟩,
    ⟨230, some ([211, 212, 216, 217, 221, 222, 226, 227, 206, 207, 208, 209, 210], 231), 244, [117], 0, 246, some 229, 247⟩,
    ⟨248, none, 249, [94], 0, 251, some 247, 252⟩,
    ⟨253, none, 254, [98], 0, 256, some 252, 257⟩,
    ⟨258, none, 259, [57], 0, 261, some 257, 262⟩,
    ⟨263, some ([244, 245, 249, 250, 254, 255, 259, 260, 239, 240, 241, 242, 243], 264), 277, [101], 0, 279, some 262, 280⟩,
    ⟨281, none, 282, [104], 0, 284, some 280, 285⟩,
    ⟨286, none, 287, [126], 0, 289, some 285, 290⟩,
    ⟨291, none, 292, [124], 0, 294, some 290, 295⟩,
    ⟨296, some ([277, 278, 282, 283, 287, 288, 292, 293, 272, 273, 274, 275, 276], 297), 310, [108], 0, 312, some 295, 313⟩,
    ⟨314, none, 315, [123], 0, 317, some 313, 318⟩,
    ⟨319, none, 320, [113], 0, 322, some 318, 323⟩,
    ⟨324, none, 325, [121], 0, 327, some 323, 328⟩,
    ⟨329, some ([310, 311, 315, 316, 320, 321, 325, 326, 305, 306, 307, 308, 309], 330), 343, [85], 0, 345, some 328, 346⟩,
    ⟨347, none, 348, [122], 0, 350, some 346, 351⟩,
    ⟨352, none, 353, [99], 0, 355, some 351, 356⟩,
    ⟨357, none, 358, [120], 0, 360, some 356, 361⟩,
    ⟨362, some ([343, 344, 348, 349, 353, 354, 358, 359, 338, 339, 340, 341, 342], 363), 376, [107], 0, 378, some 361, 379⟩,
    ⟨380, none, 381, [114], 0, 383, some 379, 384⟩,
    ⟨385, none, 386, [56], 0, 388, some 384, 389⟩,
    ⟨390, none, 391, [103], 0, 393, some 389, 394⟩,
    ⟨395, some ([376, 377, 381, 382, 386, 387, 391, 392, 371, 372, 373, 374, 375], 396), 409, [96], 0, 411, some 394, 412⟩,
    ⟨413, none, 414, [87], 0, 416, some 412, 417⟩,
    ⟨418, none, 419, [89], 0, 421, some 417, 422⟩,
    ⟨423, none, 424, [88], 0, 426, some 422, 427⟩,
    ⟨428, some ([409, 410, 414, 415, 419, 420, 424, 425, 404, 405, 406, 407, 408], 429), 442, [115], 0, 444, some 427, 445⟩,
    ⟨446, none, 447, [72], 0, 449, some 445, 450⟩,
    ⟨451, none, 452, [64], 0, 454, some 450, 455⟩,
    ⟨456, none, 457, [111], 0, 459, some 455, 460⟩,
    ⟨461, some ([442, 443, 447, 448, 452, 453, 457, 458, 437, 438, 439, 440, 441], 462), 475, [92], 0, 477, some 460, 478⟩,
    ⟨479, none, 480, [97], 0, 482, some 478, 483⟩,
    ⟨484, none, 485, [110], 0, 487, some 483, 488⟩,
    ⟨489, none, 490, [125], 0, 492, some 488, 493⟩,
    ⟨494, some ([475, 476, 480, 481, 485, 486, 490, 491, 470, 471, 472, 473, 474], 495), 508, [73], 0, 510, some 493, 511⟩,
    ⟨512, none, 513, [100], 0, 515, some 511, 516⟩,
    ⟨517, none, 518, [55], 0, 520, some 516, 521⟩,
    ⟨522, none, 523, [118], 0, 525, some 521, 526⟩]

/-- The product section's table, first = 0. -/
def prodTab0 : List PPos := [
    ⟨148, none, 149, [119], 0, 151, none, 151⟩,
    ⟨152, none, 153, [40], 0, 155, some 151, 156⟩,
    ⟨157, none, 158, [40], 0, 160, some 156, 161⟩,
    ⟨162, none, 163, [49], 0, 165, some 161, 166⟩,
    ⟨167, some ([149, 150, 153, 154, 158, 159, 163, 164, 16, 17, 18, 19, 20], 168), 181, [116], 0, 183, some 166, 184⟩,
    ⟨185, none, 186, [93], 0, 188, some 184, 189⟩,
    ⟨190, none, 191, [70], 0, 193, some 189, 194⟩,
    ⟨195, none, 196, [112], 0, 198, some 194, 199⟩,
    ⟨200, some ([181, 182, 186, 187, 191, 192, 196, 197, 176, 177, 178, 179, 180], 201), 214, [74], 0, 216, some 199, 217⟩,
    ⟨218, none, 219, [83], 0, 221, some 217, 222⟩,
    ⟨223, none, 224, [109], 0, 226, some 222, 227⟩,
    ⟨228, none, 229, [117], 0, 231, some 227, 232⟩,
    ⟨233, some ([214, 215, 219, 220, 224, 225, 229, 230, 209, 210, 211, 212, 213], 234), 247, [94], 0, 249, some 232, 250⟩,
    ⟨251, none, 252, [98], 0, 254, some 250, 255⟩,
    ⟨256, none, 257, [57], 0, 259, some 255, 260⟩,
    ⟨261, none, 262, [101], 0, 264, some 260, 265⟩,
    ⟨266, some ([247, 248, 252, 253, 257, 258, 262, 263, 242, 243, 244, 245, 246], 267), 280, [104], 0, 282, some 265, 283⟩,
    ⟨284, none, 285, [126], 0, 287, some 283, 288⟩,
    ⟨289, none, 290, [124], 0, 292, some 288, 293⟩,
    ⟨294, none, 295, [108], 0, 297, some 293, 298⟩,
    ⟨299, some ([280, 281, 285, 286, 290, 291, 295, 296, 275, 276, 277, 278, 279], 300), 313, [123], 0, 315, some 298, 316⟩,
    ⟨317, none, 318, [113], 0, 320, some 316, 321⟩,
    ⟨322, none, 323, [121], 0, 325, some 321, 326⟩,
    ⟨327, none, 328, [85], 0, 330, some 326, 331⟩,
    ⟨332, some ([313, 314, 318, 319, 323, 324, 328, 329, 308, 309, 310, 311, 312], 333), 346, [122], 0, 348, some 331, 349⟩,
    ⟨350, none, 351, [99], 0, 353, some 349, 354⟩,
    ⟨355, none, 356, [120], 0, 358, some 354, 359⟩,
    ⟨360, none, 361, [107], 0, 363, some 359, 364⟩,
    ⟨365, some ([346, 347, 351, 352, 356, 357, 361, 362, 341, 342, 343, 344, 345], 366), 379, [114], 0, 381, some 364, 382⟩,
    ⟨383, none, 384, [56], 0, 386, some 382, 387⟩,
    ⟨388, none, 389, [103], 0, 391, some 387, 392⟩,
    ⟨393, none, 394, [96], 0, 396, some 392, 397⟩,
    ⟨398, some ([379, 380, 384, 385, 389, 390, 394, 395, 374, 375, 376, 377, 378], 399), 412, [87], 0, 414, some 397, 415⟩,
    ⟨416, none, 417, [89], 0, 419, some 415, 420⟩,
    ⟨421, none, 422, [88], 0, 424, some 420, 425⟩,
    ⟨426, none, 427, [115], 0, 429, some 425, 430⟩,
    ⟨431, some ([412, 413, 417, 418, 422, 423, 427, 428, 407, 408, 409, 410, 411], 432), 445, [72], 0, 447, some 430, 448⟩,
    ⟨449, none, 450, [64], 0, 452, some 448, 453⟩,
    ⟨454, none, 455, [111], 0, 457, some 453, 458⟩,
    ⟨459, none, 460, [92], 0, 462, some 458, 463⟩,
    ⟨464, some ([445, 446, 450, 451, 455, 456, 460, 461, 440, 441, 442, 443, 444], 465), 478, [97], 0, 480, some 463, 481⟩,
    ⟨482, none, 483, [110], 0, 485, some 481, 486⟩,
    ⟨487, none, 488, [125], 0, 490, some 486, 491⟩,
    ⟨492, none, 493, [73], 0, 495, some 491, 496⟩,
    ⟨497, some ([478, 479, 483, 484, 488, 489, 493, 494, 473, 474, 475, 476, 477], 498), 511, [100], 0, 513, some 496, 514⟩,
    ⟨515, none, 516, [55], 0, 518, some 514, 519⟩,
    ⟨520, none, 521, [118], 0, 523, some 519, 524⟩]

/-- The product section's table. -/
def prodTab (first : ℕ) : List PPos := if first = 1 then prodTab1 else prodTab0

/-- The last running sum. -/
def accL (first : ℕ) : ℕ := if first = 1 then 526 else 524

/-- The offset of the values from the nonce's permutation on: `__L1`'s are `__L0`'s plus `20`, both past the stream (value `15`). -/
def layOff (first : ℕ) : ℕ := 20 * first + 1

/-! ## Head, check, squeeze, Horner -/

/-- The projection plus `ι·κ` against the claim's value. -/
def checkT (a : ℕ) : List Stmt :=
  [.atom (.load (.n (a + 1)) (.n (valf% «keccak_layer» "claim")) 1), .atom (.mul (.n (a + 2)) (.n (valf% «keccak_layer» "iota")) (.n (a + 1))),
    .atom (.add (.n (a + 3)) (.n a) (.n (a + 2))), .atom (.load (.n (a + 4)) (.n (valf% «keccak_layer» "claim")) 0),
    .atom (.assertEq (.n (a + 3)) (.n (a + 4)))]

/-- The cells of the permutation of the waiting scalars and the nonce (`first = 0`), or of the full
queue (`first = 1`). -/
def sqIns : ℕ → List V
  | 1 => [.n 508, .n 509, .n 513, .n 514, .n 518, .n 519, .n 523, .n 524,
      .n 503, .n 504, .n 505, .n 506, .n 507]
  | _ => [.n 511, .n 512, .n 516, .n 517, .n 521, .n 522, .n 530, .n 531,
      .n 506, .n 507, .n 508, .n 509, .n 510]

/-- The grind before `s` and its squeeze: the nonce read at the cursor's word `47`
(`fs_absorb_nonce`), its permutation (outputs from `layOff first + 531`, after the full queue's at
`first = 1`), `grind_check` of `3` bits on its output `1`, and `s` its output `0`,
`layOff first + 531`. -/
def sqT (first : ℕ) : List Stmt :=
  if first = 1 then
    [keccakA (sqIns 1) ((List.range 13).map fun k ↦ .n (531 + k))] ++ fsNonceT (.n (valf% «keccak_layer» "cursor@1")) 47 544 ++
      padRunT 547 ++
      [keccakA (permIns 1 [.n 545, .n 546] 548 (cap5 539)) ((List.range 13).map fun k ↦ .n (552 + k)),
        grindCallT 3 (.n 553) (.n (valf% «keccak_layer» "tabs"))]
  else
    fsNonceT (.n (valf% «keccak_layer» "cursor@1")) 47 529 ++
      [keccakA (sqIns 0) ((List.range 13).map fun k ↦ .n (532 + k)),
        grindCallT 3 (.n 533) (.n (valf% «keccak_layer» "tabs"))]

/-- The product at `s`, Horner from the top coefficient `a 46`, from the value `b`. -/
def hornerT (a : ℕ → ℕ) (s b : ℕ) : List Stmt :=
  ((List.range 46).map fun j ↦
    [.atom (.mul (.n (b + 2 * j)) (.n (if j = 0 then a 46 else b + 2 * j - 1)) (.n s)),
      .atom (.add (.n (b + 2 * j + 1)) (.n (b + 2 * j)) (.n (a (45 - j))))]).flatten

/-! ## The pack rounds and the local rounds -/

/-- The pack rounds' first record (`rounds`, `o + 719`: the capacity after `s`, the cursor past the
product and the nonce, the product at `s`), the eight-round loop on `step_g`, and
the remainder loop on `rem_g` from `rounds·step_g`, `prev_point·step_g⁸`, `point·step_g⁸`. -/
def packSetupT (o first : ℕ) : List Stmt :=
  [.atom (.load (.n (o + 717)) (.n (valf% «keccak_layer» "claim")) 2), .atom (.hint (.allocDyn (.n (o + 718)) (.n (valf% «keccak_layer» "y_g")))),
    .atom (.hint (.alloc (.n (o + 719)) 112)),
    .atom (.load (.n (o + 539)) (.n (o + 719)) 0), .atom (.load (.n (o + 540)) (.n (o + 719)) 16),
    .atom (.load (.n (o + 541)) (.n (o + 719)) 32), .atom (.load (.n (o + 542)) (.n (o + 719)) 48),
    .atom (.load (.n (o + 543)) (.n (o + 719)) 64),
    .atom (.const (.n (o + 720)) (word 281474976710656 0)),
    .atom (.mul (.n (o + 721)) (.n (valf% «keccak_layer» "cursor@1")) (.n (o + 720))),
    .atom (.load (.n (o + 721)) (.n (o + 719)) 80), .atom (.load (.n (o + 716)) (.n (o + 719)) 96),
    .atom (.const (.n (o + 722)) (word 1 0)), .atom (.add (.n (o + 723)) (.n (o + 722)) (.n (valf% «keccak_layer» "step_g"))),
    .atom (.const (.n (o + 724)) (word 1 0)),
    .callIf (.n (o + 723)) (packLoopName first)
      [.n (o + 724), .n (valf% «keccak_layer» "step_g"), .n (o + 719), .n (o + 717), .n (o + 718), .n (valf% «keccak_layer» "tabs")],
    .atom (.mul (.n (o + 725)) (.n (o + 719)) (.n (valf% «keccak_layer» "step_g"))), .atom (.mul (.n (o + 726)) (.n (valf% «keccak_layer» "step_g")) (.n (valf% «keccak_layer» "step_g"))),
    .atom (.mul (.n (o + 727)) (.n (o + 726)) (.n (o + 726))),
    .atom (.mul (.n (o + 728)) (.n (o + 727)) (.n (o + 727))),
    .atom (.mul (.n (o + 729)) (.n (o + 717)) (.n (o + 728))),
    .atom (.mul (.n (o + 730)) (.n (valf% «keccak_layer» "step_g")) (.n (valf% «keccak_layer» "step_g"))),
    .atom (.mul (.n (o + 731)) (.n (o + 730)) (.n (o + 730))),
    .atom (.mul (.n (o + 732)) (.n (o + 731)) (.n (o + 731))),
    .atom (.mul (.n (o + 733)) (.n (o + 718)) (.n (o + 732))),
    .atom (.const (.n (o + 734)) (word 1 0)), .atom (.add (.n (o + 735)) (.n (o + 734)) (.n (valf% «keccak_layer» "rem_g"))),
    .atom (.const (.n (o + 736)) (word 1 0)),
    .callIf (.n (o + 735)) (remLoopName first)
      [.n (o + 736), .n (valf% «keccak_layer» "rem_g"), .n (o + 725), .n (o + 729), .n (valf% «keccak_layer» "tabs"), .n (o + 733)]]

/-- The last record (`rounds·step_g·rem_g`) read, the local point allocated. -/
def lastT (o : ℕ) : List Stmt :=
  [.atom (.mul (.n (o + 737)) (.n (o + 725)) (.n (valf% «keccak_layer» "rem_g")))] ++
    (List.range 7).map (fun j ↦ .atom (.load (.n (o + 738 + j)) (.n (o + 737)) (16 * j))) ++
    [.atom (.hint (.alloc (.n (o + 745)) 11))]

/-- `t`'s three words. -/
def tReadsT (o : ℕ) : List Stmt :=
  fsNextT (.n (o + 743)) 33 (o + 1098) ++ fsNextT (.n (o + 743)) 34 (o + 1101) ++
    fsNextT (.n (o + 743)) 35 (o + 1104)

/-- The lane weights of the local point (`f_lanes[LANE_OFF + i]`). -/
def laneW (o i : ℕ) : ℕ := eqfVal (o + 1107) 5 25 4 i

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
. -/
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
    .atom (.load (.n (o + 1176)) (.n (valf% «keccak_layer» "claim")) 3) :: lanesEqT (.n (o + 1176)) (.n (o + 745)) (laneW o)
      (o + 1177)
  else
    [.atom (.load (.n (o + 1176)) (.n (valf% «keccak_layer» "claim")) 3), .atom (.load (.n (o + 1177)) (.n (valf% «keccak_layer» "claim")) 4)] ++
      shiftsT (.n (o + 1177)) (.n (o + 745)) (o + 1178) ++
      (formAll (.n (o + 1176)) (shiftsV (o + 1178)) (laneW o) (shiftsEnd (o + 1178))).1

/-- The weight's value. -/
def weightVal (first o : ℕ) : ℕ :=
  if first = 1 then o + 1286
  else (formAll (.n (o + 1176)) (shiftsV (o + 1178)) (laneW o) (shiftsEnd (o + 1178))).2.2

/-- The value after the weight section. -/
def weightEnd (first o : ℕ) : ℕ :=
  if first = 1 then o + 1287
  else (formAll (.n (o + 1176)) (shiftsV (o + 1178)) (laneW o) (shiftsEnd (o + 1178))).2.1

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

/-- Flip `i` from `b`: over `flipOffs i`, the lane weight read at `lp`, the slice
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
def sliceB (W : ℕ) : ℕ := W + 126

/-- The top coordinate, `top`; `top1 = 1 + top` at `+ 2`; the flips' buffer at `+ 3`. -/
def topV (W : ℕ) : ℕ := eqfEnd 5 32 (sliceB W)

/-- The flips, from `topV W + 4`, each `43` values; then their stores and the flips' pointer. -/
def lflipsT (W : ℕ) : List Stmt :=
  ((List.range 7).map fun i ↦
    lflipT (.n (W + 25)) (eqfVal (sliceB W) 5 32 4) (topV W) (topV W + 2) i (topV W + 4 + 43 * i) ++
      [.atom (.load (.n (topV W + 4 + 43 * i + 42)) (.n (topV W + 3)) i)]).flatten

/-- The final check, the squeeze of `β`, the next claim's record, its flips, the return; `W` the
first value, `wv` the weight's. -/
def tailT (o W wv : ℕ) : List Stmt :=
  [.atom (.copy (.n W) (.n wv)),
    .atom (.mul (.n (W + 1)) (.n (o + 624)) (.n (o + 1098))),
    .atom (.add (.n (W + 2)) (.n (o + 624)) (.n (o + 1101))),
    .atom (.mul (.n (W + 3)) (.n (W + 2)) (.n (o + 1104))),
    .atom (.add (.n (W + 4)) (.n (W + 1)) (.n (W + 3))),
    .atom (.mul (.n (W + 5)) (.n W) (.n (W + 4))),
    .atom (.assertEq (.n (W + 5)) (.n (o + 1097))),
    .atom (.const (.n (W + 6)) (word 0 0)), .atom (.const (.n (W + 7)) (word 0 0)),
    keccakA ([.n (o + 1099), .n (o + 1100), .n (o + 1102), .n (o + 1103), .n (o + 1105),
      .n (o + 1106), .n (W + 6), .n (W + 7)] ++ cap5 (o + 1085))
      ((List.range 13).map fun k ↦ .n (W + 8 + k))] ++
  [.atom (.mul (.n (W + 21)) (.n (W + 8)) (.n (o + 1104))),
    .atom (.add (.n (W + 22)) (.n (o + 1101)) (.n (W + 21))),
    .atom (.mul (.n (W + 23)) (.n (W + 8)) (.n (W + 22))),
    .atom (.add (.n (W + 24)) (.n (o + 1098)) (.n (W + 23))),
    .atom (.load (.n (W + 24)) (.n (valf% «keccak_layer» "out")) 0), .atom (.load (.n (o + 718)) (.n (valf% «keccak_layer» "out")) 2),
    .atom (.load (.n (o + 745)) (.n (valf% «keccak_layer» "out")) 4), .atom (.hint (.alloc (.n (W + 25)) 25))] ++
  lanesOutT (W + 8) (laneW o) (W + 25) (W + 26) ++
  [.atom (.load (.n (W + 25)) (.n (valf% «keccak_layer» "out")) 3)] ++
  eqfT (.n (o + 745)) 0 5 32 (sliceB W) ++
  [.atom (.load (.n (topV W)) (.n (o + 745)) 5), .atom (.const (.n (topV W + 1)) (word 1 0)),
    .atom (.add (.n (topV W + 2)) (.n (topV W + 1)) (.n (topV W))),
    .atom (.hint (.alloc (.n (topV W + 3)) 7))] ++
  lflipsT W ++
  [.atom (.load (.n (topV W + 3)) (.n (valf% «keccak_layer» "out")) 5)] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (topV W + 305 + j)) (.n (W + 16 + j)))) ++
  [.atom (.const (.n (topV W + 310)) (word 68719476736 0)),
    .atom (.mul (.n (topV W + 311)) (.n (o + 743)) (.n (topV W + 310))),
    .atom (.copy (.n (topV W + 312)) (.n (topV W + 311))),
    .ret [.n (topV W + 305), .n (topV W + 306), .n (topV W + 307), .n (topV W + 308),
      .n (topV W + 309), .n (topV W + 312)]]

/-! ## The template -/

/-- **`keccak_layer__L{first}`'s body.** -/
def layerT (first : ℕ) : List Stmt :=
  headT first ++ prodT (.n (valf% «keccak_layer» "cursor@1")) (muB first) (prodTab first) ++ checkT (accL first) ++
    sqT first ++ rmfeBlockT (layOff first) ++
    hornerT (fun k ↦ ((prodTab first).getD k default).a) (layOff first + 531) (layOff first + 625) ++
    packSetupT (layOff first) first ++ lastT (layOff first) ++
    localRoundsT (.n (layOff first + 743)) (.n (layOff first + 745)) (.n (layOff first + 744))
      (cap5 (layOff first + 738)) (layOff first + 746) 11 ++
    tReadsT (layOff first) ++ eqfT (.n (layOff first + 745)) 6 5 25 (layOff first + 1107) ++
    weightT first (layOff first) ++
    tailT (layOff first) (weightEnd first (layOff first)) (weightVal first (layOff first))

end
end LeanVM.Guest.B1.VerifySub
