/-
  LeanVM.Guest.B1.KeccakGkr.VkT

  `verify_keccak`'s body as a template, section by section.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
public import LeanVM.Guest.B1.Eq.EqTree
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_keccak` as a template

The sections, in order:

* `vkHeadT`: the capacity copied, `pack_g`, `y_g`, the bits of `y` (pinned boolean), `step_g`
  and `rem_g` (`assert step_g⁸·rem_g = y_g`); the instance coordinates copied to `z_vals`;
  the point's pack coordinates copied (`verify_keccak_loop0`); the segment and the lane coordinates
  squeezed (`sqZeroT`); the committed outputs' value read;
* the first claim's record: `KC_KAPPA`, `KC_POINT`, the instance weights (`eqtreeT`, `muCopyT`),
  the lanes (`eqtreeT`), the segment weights (`eqtreeT`), the value (`dotLoadsT`);
* twelve steps (`stepT`): the claim's segment weights (`eqfLevel0T`), its `ι` term (`flipsT`,
  `iotaSegT`), and `keccak_layer` (`stepTailT`);
* the committed outputs: `keccak_plain_rounds` over the slot, the word, the slot's lane weights
  (`slotLanesT`), their check; the pack coordinates copied (`verify_keccak_loop1`);
* the inputs: `keccak_plain_rounds` over the pack, `μ(low)`, over the slot, the 64 slices
  (`slicesT`, the full queue permuted), the slot's lane weights, the shifts of the slices
  (`foldT`), `keccak_form` (`formAll`), the check; the pack coordinates copied
  (`verify_keccak_loop2`); the return.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Squeezes with nothing waiting -/

/-- A squeeze with nothing waiting, on the capacity from `capb` (the zero cells `69 .. 72`),
outputs from `o`, the challenge at `o + 13`. -/
def sqZeroT (capb o : ℕ) : List Stmt :=
  [keccakA ([.n 69, .n 69, .n 69, .n 69, .n 69, .n 70, .n 71, .n 72] ++ cap5 capb)
    ((List.range 13).map fun k ↦ .n (o + k))] ++ challengeT (.n o) (o + 13)

/-! ## Copies and dot products -/

/-- `dst[dOff + i] = src[sOff + i]` through the values `b + i`, `i < n`. -/
def copyWordsT (src dst : V) (sOff dOff b n : ℕ) : List Stmt :=
  ((List.range n).map fun i ↦ [.atom (.load (.n (b + i)) src (sOff + i)),
    .atom (.load (.n (b + i)) dst (dOff + i))]).flatten

/-- `Σ_k x_k·p[off + k]` from `b`: per `k` a load, a product, an addition after the first. -/
def dotLoadsT (xs : List ℕ) (p : V) (off b : ℕ) : List Stmt :=
  ((List.range xs.length).map fun k ↦
    if k = 0 then [.atom (.load (.n b) p off), .atom (.mul (.n (b + 1)) (.n (xs.getD 0 0)) (.n b))]
    else [.atom (.load (.n (b + 3 * k - 1)) p (off + k)),
      .atom (.mul (.n (b + 3 * k)) (.n (xs.getD k 0)) (.n (b + 3 * k - 1))),
      .atom (.add (.n (b + 3 * k + 1)) (.n (if k = 1 then b + 1 else b + 3 * k - 2))
        (.n (b + 3 * k)))]).flatten

/-- The value of `dotLoadsT` over `n ≥ 1` terms. -/
def dotLoadsV (b n : ℕ) : ℕ := if n = 1 then b + 1 else b + 3 * (n - 1) + 1

/-- `Σ_k p[o_k.1]·q[o_k.2]`, both loaded, from `b`. -/
def pairsDotT (p q : V) (offs : List (ℕ × ℕ)) (b : ℕ) : List Stmt :=
  ((List.range offs.length).map fun k ↦
    if k = 0 then [.atom (.load (.n b) p (offs.getD 0 (0, 0)).1),
      .atom (.load (.n (b + 1)) q (offs.getD 0 (0, 0)).2),
      .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1)))]
    else [.atom (.load (.n (b + 4 * k - 1)) p (offs.getD k (0, 0)).1),
      .atom (.load (.n (b + 4 * k)) q (offs.getD k (0, 0)).2),
      .atom (.mul (.n (b + 4 * k + 1)) (.n (b + 4 * k - 1)) (.n (b + 4 * k))),
      .atom (.add (.n (b + 4 * k + 2)) (.n (if k = 1 then b + 2 else b + 4 * k - 2))
        (.n (b + 4 * k + 1)))]).flatten

/-- The value of `pairsDotT` over `n ≥ 2` terms. -/
def pairsDotV (b n : ℕ) : ℕ := b + 4 * (n - 1) + 2

/-- Consecutive offsets. -/
def consecOffs (pOff qOff n : ℕ) : List (ℕ × ℕ) := (List.range n).map fun k ↦ (pOff + k, qOff + k)

/-- A chain of additions over the values `vs` from `b` (none for one value). -/
def addChainT (vs : List ℕ) (b : ℕ) : List Stmt :=
  ((List.range (vs.length - 1)).map fun k ↦
    .atom (.add (.n (b + k)) (.n (if k = 0 then vs.getD 0 0 else b + k - 1)) (.n (vs.getD (k + 1) 0))))

/-- The value of `addChainT`. -/
def addChainV (vs : List ℕ) (b : ℕ) : ℕ := if vs.length ≤ 1 then vs.getD 0 0 else b + vs.length - 2

/-! ## A step's `ι` term -/

/-- The bits `i` whose positions `2^i - 1` of the round constant segment `m` of step `s` uses. -/
def iotaIdx (s m : ℕ) : List ℕ :=
  (List.range 7).filter fun i ↦ (keccakRC.getD (12 * (m + 1) - s - 1) 0).toNat.testBit (2 ^ i - 1)

/-- The bits either segment uses. -/
def iotaUsed (s : ℕ) : List ℕ :=
  (List.range 7).filter fun i ↦ i ∈ iotaIdx s 0 || i ∈ iotaIdx s 1

/-- The size of a flip's block. -/
def flipSz (s : ℕ) : ℕ := if s = 0 then 3 else 2

/-- Flip `i` of step `s` from `b`: the first claim's word bit (`x^(2^i - 1)` on lane `0`), a later
claim's from its record (`KC_FLIPS`). -/
def flipT (s i b : ℕ) : List Stmt :=
  if s = 0 then
    [.atom (.load (.n b) (.n 234) 30), .atom (.const (.n (b + 1)) (word (2 ^ (2 ^ i - 1)) 0)),
      .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1)))]
  else
    [.atom (.load (.n b) (.n 161) (22 * s + 5)), .atom (.load (.n (b + 1)) (.n b) i)]

/-- The value of flip `j` (in the used order) from `b`. -/
def flipV (s b j : ℕ) : ℕ := b + flipSz s * j + flipSz s - 1

/-- The flips of step `s` from `b`. -/
def flipsT (s b : ℕ) : List Stmt :=
  ((List.range (iotaUsed s).length).map fun j ↦ flipT s ((iotaUsed s).getD j 0) (b + flipSz s * j)).flatten

/-- The value of flip `i`. -/
def flipOf (s b i : ℕ) : ℕ := flipV s b ((iotaUsed s).idxOf i)

/-- The `ι` term from `c`, the segment weights `w0`, `w1`: per segment the flips summed, times
its weight, the two added. -/
def iotaSegT (s b c w0 w1 : ℕ) : List Stmt :=
  let v0 := (iotaIdx s 0).map (flipOf s b)
  let v1 := (iotaIdx s 1).map (flipOf s b)
  let c1 := c + v0.length
  addChainT v0 c ++
    [.atom (.mul (.n (c + v0.length - 1)) (.n w0) (.n (addChainV v0 c)))] ++
    addChainT v1 c1 ++
    [.atom (.mul (.n (c1 + v1.length - 1)) (.n w1) (.n (addChainV v1 c1))),
      .atom (.add (.n (c1 + v1.length)) (.n (c + v0.length - 1)) (.n (c1 + v1.length - 1)))]

/-- The value after `iotaSegT`; the `ι` term's is the one before. -/
def iotaSegEnd (s c : ℕ) : ℕ := c + (iotaIdx s 0).length + (iotaIdx s 1).length + 1

/-- The call of step `s` from `b`: `keccak_layer` on the capacity `cap`, the waiting cells (step
`0`), the cursor `cur`, the `ι` term `io` and the window table `tabs`; the claim `claims·g^(22 s)`
(step `0`: `claims`, value `161`; else `cb·g^22`) and the next one `pn·g^22` (step `0`:
`claims·g^22`). -/
def stepTailT (s b : ℕ) (cap : List ℕ) (cur cb pn io : ℕ) : List Stmt :=
  if s = 0 then
    [.atom (.const (.n b) (word 2 0)), .atom (.mul (.n (b + 1)) (.n 5) (.n b)),
      .atom (.const (.n (b + 2)) (word 2 0)), .atom (.mul (.n (b + 3)) (.n 18) (.n (b + 2))),
      .atom (.const (.n (b + 4)) (word 4194304 0)), .atom (.mul (.n (b + 5)) (.n 161) (.n (b + 4))),
      .call "keccak_layer__L1"
        (cap.map .n ++ [.n 159, .n 160, .n (b + 1), .n (b + 3), .n 34, .n 48, .n 161, .n (b + 5),
          .n io, .n 11]) ((List.range 6).map fun j ↦ .n (b + 6 + j))]
  else
    [.atom (.const (.n b) (word 0 0)), .atom (.const (.n (b + 1)) (word 0 0)),
      .atom (.const (.n (b + 2)) (word 2 0)), .atom (.mul (.n (b + 3)) (.n 18) (.n (b + 2))),
      .atom (.const (.n (b + 4)) (word 4194304 0)), .atom (.mul (.n (b + 5)) (.n cb) (.n (b + 4))),
      .atom (.const (.n (b + 6)) (word 4194304 0)), .atom (.mul (.n (b + 7)) (.n pn) (.n (b + 6))),
      .call "keccak_layer__L0"
        (cap.map .n ++ [.n b, .n (b + 1), .n cur, .n (b + 3), .n 34, .n 48, .n (b + 5), .n (b + 7),
          .n io, .n 11]) ((List.range 6).map fun j ↦ .n (b + 8 + j))]

/-- The size of `stepTailT`'s values. -/
def stepTailSz (s : ℕ) : ℕ := if s = 0 then 12 else 14

/-- **Step `s`** from `b`: the claim's point, its segment weights (`eqtree_frame` of
one coordinate, `1 + r` at `b + 4`, `r` at `b + 5`), the flips, the `ι` term, the call. -/
def stepT (s b : ℕ) (cap : List ℕ) (cur cb pn : ℕ) : List Stmt :=
  let f0 := b + 6
  let c := f0 + flipSz s * (iotaUsed s).length
  [.atom (.load (.n b) (.n 161) (22 * s + 2)), .atom (.mul (.n (b + 1)) (.n b) (.n 18))] ++
  eqfLevel0T (.n (b + 1)) 0 (b + 2) ++ flipsT s f0 ++ iotaSegT s f0 c (b + 4) (b + 5) ++
  stepTailT s (iotaSegEnd s c) cap cur cb pn (iotaSegEnd s c - 1)

/-- The value after step `s`. -/
def stepEnd (s b : ℕ) : ℕ :=
  iotaSegEnd s (b + 6 + flipSz s * (iotaUsed s).length) + stepTailSz s

/-! ## The head -/

/-- `pack_g`, `y_g`, the bits of `y` (pinned boolean), `step_g = g^⌊y/8⌋`, `rem_g = g^(y % 8)`
and their check `step_g⁸·rem_g = y_g`. -/
def vkBitsT : List Stmt :=
  [.atom (.const (.n 17) (word 8070450532247928836 0)),
    .atom (.mul (.n 18) (.n 6) (.n 17)),
    .atom (.const (.n 19) (word 2 0)),
    .atom (.mul (.n 20) (.n 18) (.n 19)),
    .atom (.hint (.bitsExp (.n 20) 5 (.stack [.n 21, .n 22, .n 23, .n 24, .n 25]))),
    .atom (.mul (.n 21) (.n 21) (.n 21)),
    .atom (.mul (.n 22) (.n 22) (.n 22)),
    .atom (.mul (.n 23) (.n 23) (.n 23)),
    .atom (.mul (.n 24) (.n 24) (.n 24)),
    .atom (.mul (.n 25) (.n 25) (.n 25)),
    .atom (.const (.n 26) (word 1 0)),
    .atom (.const (.n 27) (word 3 0)),
    .atom (.mul (.n 28) (.n 24) (.n 27)),
    .atom (.add (.n 29) (.n 26) (.n 28)),
    .atom (.const (.n 30) (word 1 0)),
    .atom (.const (.n 31) (word 5 0)),
    .atom (.mul (.n 32) (.n 25) (.n 31)),
    .atom (.add (.n 33) (.n 30) (.n 32)),
    .atom (.mul (.n 34) (.n 29) (.n 33)),
    .atom (.const (.n 35) (word 1 0)),
    .atom (.const (.n 36) (word 3 0)),
    .atom (.mul (.n 37) (.n 21) (.n 36)),
    .atom (.add (.n 38) (.n 35) (.n 37)),
    .atom (.const (.n 39) (word 1 0)),
    .atom (.const (.n 40) (word 5 0)),
    .atom (.mul (.n 41) (.n 22) (.n 40)),
    .atom (.add (.n 42) (.n 39) (.n 41)),
    .atom (.mul (.n 43) (.n 38) (.n 42)),
    .atom (.const (.n 44) (word 1 0)),
    .atom (.const (.n 45) (word 17 0)),
    .atom (.mul (.n 46) (.n 23) (.n 45)),
    .atom (.add (.n 47) (.n 44) (.n 46)),
    .atom (.mul (.n 48) (.n 43) (.n 47)),
    .atom (.mul (.n 49) (.n 34) (.n 34)),
    .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 50)),
    .atom (.mul (.n 52) (.n 51) (.n 48)),
    .atom (.const (.n 53) (word 2 0)),
    .atom (.mul (.n 54) (.n 18) (.n 53)),
    .atom (.assertEq (.n 52) (.n 54))]

/-- The point's allocation and the copy of its pack coordinates (`verify_keccak_loop0`). -/
def vkPointT : List Stmt :=
  [.atom (.const (.n 59) (word 2 0)), .atom (.mul (.n 60) (.n 18) (.n 59)),
    .atom (.hint (.allocDyn (.n 61) (.n 60))), .atom (.const (.n 62) (word 1 0)),
    .atom (.add (.n 63) (.n 62) (.n 18)), .atom (.const (.n 64) (word 1 0)),
    .atom (.const (.n 65) (word 16 0)), .atom (.mul (.n 66) (.n 7) (.n 65)),
    .callIf (.n 63) name% «verify_keccak_loop0» [.n 64, .n 18, .n 61, .n 66],
    .atom (.mul (.n 67) (.n 61) (.n 18)), .atom (.const (.n 68) (word 1 0)),
    .atom (.const (.n 69) (word 0 0)), .atom (.const (.n 70) (word 0 0)),
    .atom (.const (.n 71) (word 0 0)), .atom (.const (.n 72) (word 0 0))]

/-- The segment and the five lane coordinates squeezed. -/
def vkSqueezesT : List Stmt :=
  sqZeroT 12 73 ++ [.atom (.load (.n 86) (.n 67) 0), .atom (.hint (.alloc (.n 87) 5))] ++
    ((List.range 5).map fun i ↦
      sqZeroT (if i = 0 then 81 else 82 + 14 * i) (88 + 14 * i) ++
        [.atom (.load (.n (101 + 14 * i)) (.n 87) i)]).flatten

/-- **The head.** -/
def vkHeadT : List Stmt :=
  (List.range 5).map (fun i ↦ .atom (.copy (.n (12 + i)) (.n i))) ++ vkBitsT ++
    copyWordsT (.n 7) (.n 9) 0 0 55 4 ++ vkPointT ++ vkSqueezesT ++ fsNextT (.n 5) 0 158

/-- **The first claim's record.** -/
def vkFirstT : List Stmt :=
  [.atom (.hint (.alloc (.n 161) 286)), .atom (.const (.n 162) (word 1 0)),
    .atom (.load (.n 162) (.n 161) 1), .atom (.load (.n 61) (.n 161) 2),
    .atom (.hint (.alloc (.n 163) 30))] ++
  eqtreeT (.n 9) (.n 163) 0 164 4 ++ copyWordsT (.n 163) (.n 161) 14 6 218 16 ++
  [.atom (.hint (.alloc (.n 234) 62))] ++ eqtreeT (.n 87) (.n 234) 0 235 5 ++
  [.atom (.const (.n 340) (word 1073741824 0)), .atom (.mul (.n 341) (.n 234) (.n 340)),
    .atom (.load (.n 341) (.n 161) 3), .atom (.hint (.alloc (.n 342) 2))] ++
  eqtreeT (.n 67) (.n 342) 0 343 1 ++ pairsDotT (.n 234) (.n 8) (consecOffs 30 0 25) 346 ++
  [.atom (.load (.n 445) (.n 342) 1), .atom (.mul (.n 446) (.n 445) (.n 444)),
    .atom (.add (.n 447) (.n 158) (.n 446)), .atom (.load (.n 447) (.n 161) 0)]

/-! ## The openings -/

/-- An opening's lane weights at the slot point `slot` and segment point `segp` from `b`: the
slot's equality weights (`eqfT`, the first 50), the segment's, and per lane the segments'
`first .. first + count` weighted (`keccak_slot_lanes`). -/
def slotLanesT (slot segp b first count : ℕ) : List Stmt :=
  eqfT (.n slot) 0 6 50 b ++ eqfLevel0T (.n segp) 0 (b + 129) ++
  ((List.range 25).map fun lane ↦
    if count = 1 then
      [.atom (.mul (.n (b + 133 + 2 * lane)) (.n (b + 131))
          (.n (eqfVal b 6 50 5 (25 * first + lane)))),
        .atom (.copy (.n (b + 134 + 2 * lane)) (.n (b + 133 + 2 * lane)))]
    else
      [.atom (.mul (.n (b + 133 + 4 * lane)) (.n (b + 131)) (.n (eqfVal b 6 50 5 (25 * first + lane)))),
        .atom (.mul (.n (b + 134 + 4 * lane)) (.n (b + 132))
          (.n (eqfVal b 6 50 5 (25 * (first + 1) + lane)))),
        .atom (.add (.n (b + 135 + 4 * lane)) (.n (b + 133 + 4 * lane)) (.n (b + 134 + 4 * lane))),
        .atom (.copy (.n (b + 136 + 4 * lane)) (.n (b + 135 + 4 * lane)))]).flatten

/-- Lane `lane`'s weight in `slotLanesT`. -/
def slotLaneV (b count lane : ℕ) : ℕ :=
  if count = 1 then b + 134 + 2 * lane else b + 136 + 4 * lane

/-- The value after `slotLanesT`. -/
def slotLanesEnd (b count : ℕ) : ℕ := if count = 1 then b + 183 else b + 233

/-- Read `z` of the slices from `b`. -/
def slB (b z : ℕ) : ℕ := b + 3 * z + 13 * (z / 4)

/-- The permutation before group `g` of four slices. -/
def slP (b g : ℕ) : ℕ := b + 12 * g + 13 * (g - 1)

/-- The capacity before group `g`. -/
def slCap (capb b g : ℕ) : ℕ := if g = 0 then capb else slP b g + 8

/-- The cells of group `g`'s four reads. -/
def slCells (b g : ℕ) : List V :=
  ((List.range 4).map fun j ↦ [V.n (slB b (4 * g + j) + 1), .n (slB b (4 * g + j) + 2)]).flatten

/-- **The 64 slices**: read at the cursor and stored, four to a permutation, the
last four's permutation (the full queue) at `slP b 16`. -/
def slicesT (cur : V) (capb b : ℕ) : List Stmt :=
  ((List.range 16).map fun g ↦
    (if g = 0 then [] else
      [keccakA (slCells b (g - 1) ++ cap5 (slCap capb b (g - 1)))
        ((List.range 13).map fun k ↦ .n (slP b g + k))]) ++
    ((List.range 4).map fun j ↦
      fsNextT cur (4 * g + j) (slB b (4 * g + j)) ++
        [.atom (.load (.n (slB b (4 * g + j))) (.n 10) (4 * g + j))]).flatten).flatten ++
  [keccakA (slCells b 15 ++ cap5 (slCap capb b 15)) ((List.range 13).map fun k ↦ .n (slP b 16 + k))]

/-! ## The shifts of the slices -/

/-- The values of level `t` (`level t j`), from the slices `src` at level `0`. -/
def foldVal (src : ℕ → ℕ) (b : ℕ) : ℕ → ℕ → ℕ
  | 0, j => src j
  | t + 1, j =>
    let n := 2 ^ (6 - t)
    b + 195 * t + 3 + 3 * (foldPos' t (j / (n / 2)) * (n / 2) + j % (n / 2)) + 2
where
  /-- A node's position in the order the guest folds them: `(p, b)` with `q = p + 2^t·b`. -/
  foldPos' (t q : ℕ) : ℕ := ((List.range (2 ^ (t + 1))).filter fun q' ↦
    t + 1 < 6 || shiftUsed.contains (q' / 2 + 2 ^ t * (q' % 2))).idxOf (q % 2 ^ t * 2 + q / 2 ^ t)

/-- **`fold_shifts`, level `t`** (`fold_node`) from `B`, the coordinate
`a_t` at `a·g^t`, `1 + a_t` at `B + 2`: each node `(1 + a_t)·x₀ + a_t·x₁`. -/
def foldLevelT (src : ℕ → ℕ) (b : ℕ) (a : V) (t : ℕ) : List Stmt :=
  let n := 2 ^ (6 - t)
  let B := b + 195 * t
  [.atom (.load (.n B) a t), .atom (.const (.n (B + 1)) (word 1 0)),
    .atom (.add (.n (B + 2)) (.n (B + 1)) (.n B))] ++
  ((List.range (2 ^ (t + 1))).filter (fun q' ↦
      t + 1 < 6 || shiftUsed.contains (q' / 2 + 2 ^ t * (q' % 2)))).zipIdx.flatMap fun (q', c) ↦
    let p := q' / 2
    let bb := q' % 2
    (List.range (n / 2)).flatMap fun k ↦
      let x0 := foldVal src b t (p * n + (2 * k + (n - 1) * bb) % n)
      let x1 := foldVal src b t (p * n + (2 * k + 1 + (n - 1) * bb) % n)
      let d := B + 3 + 3 * (c * (n / 2) + k)
      [.atom (.mul (.n d) (.n (B + 2)) (.n x0)), .atom (.mul (.n (d + 1)) (.n B) (.n x1)),
        .atom (.add (.n (d + 2)) (.n d) (.n (d + 1)))]

/-- **`fold_shifts`** over the six levels. -/
def foldT (src : ℕ → ℕ) (b : ℕ) (a : V) : List Stmt :=
  ((List.range 6).map (foldLevelT src b a)).flatten

/-! ## The template -/

/-- The twelve steps. -/
def vkStepsT : List Stmt :=
  stepT 0 448 [152, 153, 154, 155, 156] 0 161 0 ++
  stepT 1 489 [483, 484, 485, 486, 487] 488 161 482 ++
  stepT 2 524 [518, 519, 520, 521, 522] 523 482 517 ++
  stepT 3 558 [552, 553, 554, 555, 556] 557 517 551 ++
  stepT 4 601 [595, 596, 597, 598, 599] 600 551 594 ++
  stepT 5 642 [636, 637, 638, 639, 640] 641 594 635 ++
  stepT 6 685 [679, 680, 681, 682, 683] 684 635 678 ++
  stepT 7 718 [712, 713, 714, 715, 716] 717 678 711 ++
  stepT 8 759 [753, 754, 755, 756, 757] 758 711 752 ++
  stepT 9 797 [791, 792, 793, 794, 795] 796 752 790 ++
  stepT 10 840 [834, 835, 836, 837, 838] 839 790 833 ++
  stepT 11 881 [875, 876, 877, 878, 879] 880 833 874

/-- The committed outputs' opening. -/
def vkOutT : List Stmt :=
  [.atom (.mul (.n 921) (.n 9) (.n 6)), .atom (.const (.n 922) (word 0 0)),
    .atom (.const (.n 923) (word 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n 915, .n 916, .n 917, .n 918, .n 919, .n 922,
      .n 923, .n 920, .n 158, .n 921, .n 11] ((List.range 7).map fun j ↦ .n (924 + j))] ++
  fsNextT (.n 929) 0 931 ++ [.atom (.mul (.n 934) (.n 61) (.n 18))] ++
  slotLanesT 921 934 935 1 1 ++ dotLoadsT ((List.range 25).map (slotLaneV 935 1)) (.n 234) 30 1118 ++
  [.atom (.mul (.n 1192) (.n 1191) (.n 931)), .atom (.assertEq (.n 1192) (.n 930)),
    .atom (.const (.n 1193) (word 1 0)), .atom (.add (.n 1194) (.n 1193) (.n 18)),
    .atom (.const (.n 1195) (word 1 0)), .atom (.const (.n 1196) (word 16 0)),
    .atom (.mul (.n 1197) (.n 9) (.n 1196)),
    .callIf (.n 1194) name% «verify_keccak_loop1» [.n 1195, .n 18, .n 1197, .n 61]]

/-- The inputs' opening up to the slices. -/
def vkInT : List Stmt :=
  [.atom (.const (.n 1198) (word 2 0)), .atom (.mul (.n 1199) (.n 929) (.n 1198)),
    .atom (.load (.n 1200) (.n 161) 264), .atom (.const (.n 1201) (word 549755813888 0)),
    .atom (.mul (.n 1202) (.n 9) (.n 1201)),
    .call "keccak_plain_rounds__L4_L1" [.n 924, .n 925, .n 926, .n 927, .n 928, .n 932,
      .n 933, .n 1199, .n 1200, .n 1202, .n 11] ((List.range 7).map fun j ↦ .n (1203 + j)),
    .atom (.hint (.alloc (.n 1210) 30))] ++
  eqtreeT (.n 9) (.n 1210) 39 1211 4 ++ pairsDotT (.n 1210) (.n 161) (consecOffs 14 270 16) 1265 ++
  [.atom (.const (.n 1328) (word 549755813888 0)), .atom (.mul (.n 1329) (.n 9) (.n 1328)),
    .atom (.mul (.n 1330) (.n 1329) (.n 6)), .atom (.const (.n 1331) (word 0 0)),
    .atom (.const (.n 1332) (word 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n 1203, .n 1204, .n 1205, .n 1206, .n 1207, .n 1331,
      .n 1332, .n 1208, .n 1209, .n 1330, .n 11] ((List.range 7).map fun j ↦ .n (1333 + j))] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (1340 + j)) (.n (1333 + j)))) ++
  slicesT (.n 1338) 1340 1345

/-- The shifts of the slices' values. -/
def vkSh (r : ℕ) : ℕ := foldVal (fun j ↦ 1981 + j) 2045 6 r

/-- The inputs' check, the copy of their pack coordinates, the return. -/
def vkFinT : List Stmt :=
  [.atom (.load (.n 1745) (.n 161) 266), .atom (.mul (.n 1746) (.n 1745) (.n 18))] ++
  slotLanesT 1330 1746 1747 0 2 ++ [.atom (.load (.n 1980) (.n 161) 268)] ++
  (List.range 64).map (fun z ↦ .atom (.load (.n (1981 + z)) (.n 10) z)) ++
  foldT (fun j ↦ 1981 + j) 2045 (.n 1980) ++ [.atom (.load (.n 3143) (.n 161) 267)] ++
  (formAll (.n 3143) vkSh (slotLaneV 1747 2) 3144).1 ++
  [.atom (.mul (.n 3358) (.n 1327) (.n (formAll (.n 3143) vkSh (slotLaneV 1747 2) 3144).2.2)),
    .atom (.assertEq (.n 3358) (.n 1339)), .atom (.const (.n 3359) (word 1 0)),
    .atom (.add (.n 3360) (.n 3359) (.n 18)), .atom (.const (.n 3361) (word 1 0)),
    .atom (.const (.n 3362) (word 16 0)), .atom (.mul (.n 3363) (.n 1202) (.n 3362)),
    .callIf (.n 3360) name% «verify_keccak_loop2» [.n 3361, .n 18, .n 3363, .n 1745]] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (3364 + j)) (.n (1740 + j)))) ++
  [.atom (.const (.n 3369) (word 27 0)), .atom (.mul (.n 3370) (.n 1338) (.n 3369)),
    .atom (.copy (.n 3371) (.n 3370)), .atom (.copy (.n 3372) (.n 931)),
    .ret [.n 3364, .n 3365, .n 3366, .n 3367, .n 3368, .n 3371, .n 3372]]

/-- **`verify_keccak`'s body.** -/
def vkT : List Stmt := vkHeadT ++ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinT

end
end LeanVM.Guest.B1.VerifySub
