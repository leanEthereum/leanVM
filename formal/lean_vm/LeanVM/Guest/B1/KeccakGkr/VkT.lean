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
outputs from `o`, the challenge `o` (`challenge_from_state`). -/
def sqZeroT (capb o : ℕ) : List Stmt :=
  [keccakA ([.n 69, .n 69, .n 69, .n 69, .n 69, .n 70, .n 71, .n 72] ++ cap5 capb)
    ((List.range 13).map fun k ↦ .n (o + k))]

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
    [.atom (.load (.n b) (.n 228) 30), .atom (.const (.n (b + 1)) (word (2 ^ (2 ^ i - 1)) 0)),
      .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1)))]
  else
    [.atom (.load (.n b) (.n 155) (22 * s + 5)), .atom (.load (.n (b + 1)) (.n b) i)]

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
(step `0`: `claims`, value `155`; else `cb·g^22`) and the next one `pn·g^22` (step `0`:
`claims·g^22`). -/
def stepTailT (s b : ℕ) (cap : List ℕ) (cur cb pn io : ℕ) : List Stmt :=
  if s = 0 then
    [.atom (.const (.n b) (word 2 0)), .atom (.mul (.n (b + 1)) (.n 5) (.n b)),
      .atom (.const (.n (b + 2)) (word 2 0)), .atom (.mul (.n (b + 3)) (.n 18) (.n (b + 2))),
      .atom (.const (.n (b + 4)) (word 4194304 0)), .atom (.mul (.n (b + 5)) (.n 155) (.n (b + 4))),
      .call "keccak_layer__L1"
        (cap.map .n ++ [.n 153, .n 154, .n (b + 1), .n (b + 3), .n 34, .n 48, .n 155, .n (b + 5),
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
  [.atom (.load (.n b) (.n 155) (22 * s + 2)), .atom (.mul (.n (b + 1)) (.n b) (.n 18))] ++
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
  sqZeroT 12 73 ++ [.atom (.load (.n 73) (.n 67) 0), .atom (.hint (.alloc (.n 86) 5))] ++
    ((List.range 5).map fun i ↦
      sqZeroT (if i = 0 then 81 else 82 + 13 * i) (87 + 13 * i) ++
        [.atom (.load (.n (87 + 13 * i)) (.n 86) i)]).flatten

/-- **The head.** -/
def vkHeadT : List Stmt :=
  (List.range 5).map (fun i ↦ .atom (.copy (.n (12 + i)) (.n i))) ++ vkBitsT ++
    copyWordsT (.n 7) (.n 9) 0 0 55 4 ++ vkPointT ++ vkSqueezesT ++ fsNextT (.n 5) 0 152

/-- **The first claim's record.** -/
def vkFirstT : List Stmt :=
  [.atom (.hint (.alloc (.n 155) 286)), .atom (.const (.n 156) (word 1 0)),
    .atom (.load (.n 156) (.n 155) 1), .atom (.load (.n 61) (.n 155) 2),
    .atom (.hint (.alloc (.n 157) 30))] ++
  eqtreeT (.n 9) (.n 157) 0 158 4 ++ copyWordsT (.n 157) (.n 155) 14 6 212 16 ++
  [.atom (.hint (.alloc (.n 228) 62))] ++ eqtreeT (.n 86) (.n 228) 0 229 5 ++
  [.atom (.const (.n 334) (word 1073741824 0)), .atom (.mul (.n 335) (.n 228) (.n 334)),
    .atom (.load (.n 335) (.n 155) 3), .atom (.hint (.alloc (.n 336) 2))] ++
  eqtreeT (.n 67) (.n 336) 0 337 1 ++ pairsDotT (.n 228) (.n 8) (consecOffs 30 0 25) 340 ++
  [.atom (.load (.n 439) (.n 336) 1), .atom (.mul (.n 440) (.n 439) (.n 438)),
    .atom (.add (.n 441) (.n 152) (.n 440)), .atom (.load (.n 441) (.n 155) 0)]

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
  stepT 0 442 [147, 148, 149, 150, 151] 0 155 0 ++
  stepT 1 483 [477, 478, 479, 480, 481] 482 155 476 ++
  stepT 2 518 [512, 513, 514, 515, 516] 517 476 511 ++
  stepT 3 552 [546, 547, 548, 549, 550] 551 511 545 ++
  stepT 4 595 [589, 590, 591, 592, 593] 594 545 588 ++
  stepT 5 636 [630, 631, 632, 633, 634] 635 588 629 ++
  stepT 6 679 [673, 674, 675, 676, 677] 678 629 672 ++
  stepT 7 712 [706, 707, 708, 709, 710] 711 672 705 ++
  stepT 8 753 [747, 748, 749, 750, 751] 752 705 746 ++
  stepT 9 791 [785, 786, 787, 788, 789] 790 746 784 ++
  stepT 10 834 [828, 829, 830, 831, 832] 833 784 827 ++
  stepT 11 875 [869, 870, 871, 872, 873] 874 827 868

/-- The committed outputs' opening. -/
def vkOutT : List Stmt :=
  [.atom (.mul (.n 915) (.n 9) (.n 6)), .atom (.const (.n 916) (word 0 0)),
    .atom (.const (.n 917) (word 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n 909, .n 910, .n 911, .n 912, .n 913, .n 916,
      .n 917, .n 914, .n 152, .n 915, .n 11] ((List.range 7).map fun j ↦ .n (918 + j))] ++
  fsNextT (.n 923) 0 925 ++ [.atom (.mul (.n 928) (.n 61) (.n 18))] ++
  slotLanesT 915 928 929 1 1 ++ dotLoadsT ((List.range 25).map (slotLaneV 929 1)) (.n 228) 30 1112 ++
  [.atom (.mul (.n 1186) (.n 1185) (.n 925)), .atom (.assertEq (.n 1186) (.n 924)),
    .atom (.const (.n 1187) (word 1 0)), .atom (.add (.n 1188) (.n 1187) (.n 18)),
    .atom (.const (.n 1189) (word 1 0)), .atom (.const (.n 1190) (word 16 0)),
    .atom (.mul (.n 1191) (.n 9) (.n 1190)),
    .callIf (.n 1188) name% «verify_keccak_loop1» [.n 1189, .n 18, .n 1191, .n 61]]

/-- The inputs' opening up to the slices. -/
def vkInT : List Stmt :=
  [.atom (.const (.n 1192) (word 2 0)), .atom (.mul (.n 1193) (.n 923) (.n 1192)),
    .atom (.load (.n 1194) (.n 155) 264), .atom (.const (.n 1195) (word 549755813888 0)),
    .atom (.mul (.n 1196) (.n 9) (.n 1195)),
    .call "keccak_plain_rounds__L4_L1" [.n 918, .n 919, .n 920, .n 921, .n 922, .n 926,
      .n 927, .n 1193, .n 1194, .n 1196, .n 11] ((List.range 7).map fun j ↦ .n (1197 + j)),
    .atom (.hint (.alloc (.n 1204) 30))] ++
  eqtreeT (.n 9) (.n 1204) 39 1205 4 ++ pairsDotT (.n 1204) (.n 155) (consecOffs 14 270 16) 1259 ++
  [.atom (.const (.n 1322) (word 549755813888 0)), .atom (.mul (.n 1323) (.n 9) (.n 1322)),
    .atom (.mul (.n 1324) (.n 1323) (.n 6)), .atom (.const (.n 1325) (word 0 0)),
    .atom (.const (.n 1326) (word 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n 1197, .n 1198, .n 1199, .n 1200, .n 1201, .n 1325,
      .n 1326, .n 1202, .n 1203, .n 1324, .n 11] ((List.range 7).map fun j ↦ .n (1327 + j))] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (1334 + j)) (.n (1327 + j)))) ++
  slicesT (.n 1332) 1334 1339

/-- The shifts of the slices' values. -/
def vkSh (r : ℕ) : ℕ := foldVal (fun j ↦ 1975 + j) 2039 6 r

/-- The inputs' check, the copy of their pack coordinates, the return. -/
def vkFinT : List Stmt :=
  [.atom (.load (.n 1739) (.n 155) 266), .atom (.mul (.n 1740) (.n 1739) (.n 18))] ++
  slotLanesT 1324 1740 1741 0 2 ++ [.atom (.load (.n 1974) (.n 155) 268)] ++
  (List.range 64).map (fun z ↦ .atom (.load (.n (1975 + z)) (.n 10) z)) ++
  foldT (fun j ↦ 1975 + j) 2039 (.n 1974) ++ [.atom (.load (.n 3137) (.n 155) 267)] ++
  (formAll (.n 3137) vkSh (slotLaneV 1741 2) 3138).1 ++
  [.atom (.mul (.n 3352) (.n 1321) (.n (formAll (.n 3137) vkSh (slotLaneV 1741 2) 3138).2.2)),
    .atom (.assertEq (.n 3352) (.n 1333)), .atom (.const (.n 3353) (word 1 0)),
    .atom (.add (.n 3354) (.n 3353) (.n 18)), .atom (.const (.n 3355) (word 1 0)),
    .atom (.const (.n 3356) (word 16 0)), .atom (.mul (.n 3357) (.n 1196) (.n 3356)),
    .callIf (.n 3354) name% «verify_keccak_loop2» [.n 3355, .n 18, .n 3357, .n 1739]] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (3358 + j)) (.n (1734 + j)))) ++
  [.atom (.const (.n 3363) (word 27 0)), .atom (.mul (.n 3364) (.n 1332) (.n 3363)),
    .atom (.copy (.n 3365) (.n 3364)), .atom (.copy (.n 3366) (.n 925)),
    .ret [.n 3358, .n 3359, .n 3360, .n 3361, .n 3362, .n 3365, .n 3366]]

/-- **`verify_keccak`'s body.** -/
def vkT : List Stmt := vkHeadT ++ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinT

end
end LeanVM.Guest.B1.VerifySub
