/-
  LeanVM.Guest.B1.KeccakGkr.VkT

  `verify_keccak`'s body as a template (G:2923-3089), section by section.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
public import LeanVM.Guest.B1.Eq.EqTree

/-!
# `verify_keccak` as a template

The sections, in order:

* `vkHeadT`: the capacity copied, `pack_g`, `y_g`, the bits of `y` (pinned boolean), `step_g`
  and `rem_g` (`assert step_g⁸·rem_g = y_g`); the instance coordinates copied to `z_vals`;
  the point's pack coordinates copied (`__loop10`); the segment and the lane coordinates
  squeezed (`sqZeroT`); the committed outputs' value read;
* the first claim's record: `KC_KAPPA`, `KC_POINT`, the instance weights (`eqtreeT`, `muCopyT`),
  the lanes (`eqtreeT`), the segment weights (`eqtreeT`), the value (`dotLoadsT`);
* twelve steps (`stepT`): the claim's segment weights (`eqfLevel0T`), its `ι` term (`flipsT`,
  `iotaSegT`), and `keccak_layer` (`stepTailT`);
* the committed outputs: `keccak_plain_rounds` over the slot, the word, the slot's lane weights
  (`slotLanesT`), their check; the pack coordinates copied (`__loop11`);
* the inputs: `keccak_plain_rounds` over the pack, `μ(low)`, over the slot, the 64 slices
  (`slicesT`), the ring map's first challenge, the slot's lane weights, the shifts of the slices
  (`foldT`), `keccak_form` (`formAll`), the check; the pack coordinates copied (`__loop12`); the
  return.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Squeezes with nothing waiting -/

/-- A squeeze with nothing waiting, on the capacity from `capb` (the zero cells `68 .. 71`),
outputs from `o`, the challenge at `o + 19`. -/
def sqZeroT (capb o : ℕ) : List Stmt :=
  [keccakA ([.n 68, .n 68, .n 68, .n 68, .n 68, .n 69, .n 70, .n 71] ++ cap5 capb)
    ((List.range 13).map fun k ↦ .n (o + k))] ++ challengeT (.n o) (.n (o + 1)) (o + 13)

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
claim's from its record (`KC_FLIPS`, G:3016-3020). -/
def flipT (s i b : ℕ) : List Stmt :=
  if s = 0 then
    [.atom (.load (.n b) (.n 276) 30), .atom (.const (.n (b + 1)) (word (2 ^ (2 ^ i - 1)) 0 0)),
      .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1)))]
  else
    [.atom (.load (.n b) (.n 203) (22 * s + 5)), .atom (.load (.n (b + 1)) (.n b) i)]

/-- The value of flip `j` (in the used order) from `b`. -/
def flipV (s b j : ℕ) : ℕ := b + flipSz s * j + flipSz s - 1

/-- The flips of step `s` from `b`. -/
def flipsT (s b : ℕ) : List Stmt :=
  ((List.range (iotaUsed s).length).map fun j ↦ flipT s ((iotaUsed s).getD j 0) (b + flipSz s * j)).flatten

/-- The value of flip `i`. -/
def flipOf (s b i : ℕ) : ℕ := flipV s b ((iotaUsed s).idxOf i)

/-- The `ι` term from `c`, the segment weights `w0`, `w1`: per segment the flips summed, times
its weight, the two added (G:3022-3027). -/
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
`0`), the cursor `cur` and the `ι` term `io`; the claim `claims·g^(22 s)` (step `0`: `claims`,
value `203`; else `cb·g^22`) and the next one `pn·g^22` (step `0`: `claims·g^22`). -/
def stepTailT (s b : ℕ) (cap : List ℕ) (cur cb pn io : ℕ) : List Stmt :=
  if s = 0 then
    [.atom (.const (.n b) (word 2 0 0)), .atom (.mul (.n (b + 1)) (.n 5) (.n b)),
      .atom (.const (.n (b + 2)) (word 2 0 0)), .atom (.mul (.n (b + 3)) (.n 17) (.n (b + 2))),
      .atom (.const (.n (b + 4)) (word 4194304 0 0)), .atom (.mul (.n (b + 5)) (.n 203) (.n (b + 4))),
      .call "keccak_layer__L1"
        (cap.map .n ++ [.n 200, .n 202, .n (b + 1), .n (b + 3), .n 33, .n 47, .n 203, .n (b + 5),
          .n io]) ((List.range 6).map fun j ↦ .n (b + 6 + j))]
  else
    [.atom (.const (.n b) (word 0 0 0)), .atom (.const (.n (b + 1)) (word 0 0 0)),
      .atom (.const (.n (b + 2)) (word 2 0 0)), .atom (.mul (.n (b + 3)) (.n 17) (.n (b + 2))),
      .atom (.const (.n (b + 4)) (word 4194304 0 0)), .atom (.mul (.n (b + 5)) (.n cb) (.n (b + 4))),
      .atom (.const (.n (b + 6)) (word 4194304 0 0)), .atom (.mul (.n (b + 7)) (.n pn) (.n (b + 6))),
      .call "keccak_layer__L0"
        (cap.map .n ++ [.n b, .n (b + 1), .n cur, .n (b + 3), .n 33, .n 47, .n (b + 5), .n (b + 7),
          .n io]) ((List.range 6).map fun j ↦ .n (b + 8 + j))]

/-- The size of `stepTailT`'s values. -/
def stepTailSz (s : ℕ) : ℕ := if s = 0 then 12 else 14

/-- **Step `s`** from `b` (G:3000-3031): the claim's point, its segment weights (`eqtree_frame` of
one coordinate, `1 + r` at `b + 4`, `r` at `b + 5`), the flips, the `ι` term, the call. -/
def stepT (s b : ℕ) (cap : List ℕ) (cur cb pn : ℕ) : List Stmt :=
  let f0 := b + 6
  let c := f0 + flipSz s * (iotaUsed s).length
  [.atom (.load (.n b) (.n 203) (22 * s + 2)), .atom (.mul (.n (b + 1)) (.n b) (.n 17))] ++
  eqfLevel0T (.n (b + 1)) 0 (b + 2) ++ flipsT s f0 ++ iotaSegT s f0 c (b + 4) (b + 5) ++
  stepTailT s (iotaSegEnd s c) cap cur cb pn (iotaSegEnd s c - 1)

/-- The value after step `s`. -/
def stepEnd (s b : ℕ) : ℕ :=
  iotaSegEnd s (b + 6 + flipSz s * (iotaUsed s).length) + stepTailSz s

/-! ## The head -/

/-- `pack_g`, `y_g`, the bits of `y` (pinned boolean), `step_g = g^⌊y/8⌋`, `rem_g = g^(y % 8)`
and their check `step_g⁸·rem_g = y_g`. -/
def vkBitsT : List Stmt :=
  [.atom (.const (.n 16) (word 8070450532247928836 0 0)),
    .atom (.mul (.n 17) (.n 6) (.n 16)),
    .atom (.const (.n 18) (word 2 0 0)),
    .atom (.mul (.n 19) (.n 17) (.n 18)),
    .atom (.hint (.bitsExp (.n 19) 5 (.stack [.n 20, .n 21, .n 22, .n 23, .n 24]))),
    .atom (.mul (.n 20) (.n 20) (.n 20)),
    .atom (.mul (.n 21) (.n 21) (.n 21)),
    .atom (.mul (.n 22) (.n 22) (.n 22)),
    .atom (.mul (.n 23) (.n 23) (.n 23)),
    .atom (.mul (.n 24) (.n 24) (.n 24)),
    .atom (.const (.n 25) (word 1 0 0)),
    .atom (.const (.n 26) (word 3 0 0)),
    .atom (.mul (.n 27) (.n 23) (.n 26)),
    .atom (.add (.n 28) (.n 25) (.n 27)),
    .atom (.const (.n 29) (word 1 0 0)),
    .atom (.const (.n 30) (word 5 0 0)),
    .atom (.mul (.n 31) (.n 24) (.n 30)),
    .atom (.add (.n 32) (.n 29) (.n 31)),
    .atom (.mul (.n 33) (.n 28) (.n 32)),
    .atom (.const (.n 34) (word 1 0 0)),
    .atom (.const (.n 35) (word 3 0 0)),
    .atom (.mul (.n 36) (.n 20) (.n 35)),
    .atom (.add (.n 37) (.n 34) (.n 36)),
    .atom (.const (.n 38) (word 1 0 0)),
    .atom (.const (.n 39) (word 5 0 0)),
    .atom (.mul (.n 40) (.n 21) (.n 39)),
    .atom (.add (.n 41) (.n 38) (.n 40)),
    .atom (.mul (.n 42) (.n 37) (.n 41)),
    .atom (.const (.n 43) (word 1 0 0)),
    .atom (.const (.n 44) (word 17 0 0)),
    .atom (.mul (.n 45) (.n 22) (.n 44)),
    .atom (.add (.n 46) (.n 43) (.n 45)),
    .atom (.mul (.n 47) (.n 42) (.n 46)),
    .atom (.mul (.n 48) (.n 33) (.n 33)),
    .atom (.mul (.n 49) (.n 48) (.n 48)),
    .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 47)),
    .atom (.const (.n 52) (word 2 0 0)),
    .atom (.mul (.n 53) (.n 17) (.n 52)),
    .atom (.assertEq (.n 51) (.n 53))]

/-- The point's allocation and the copy of its pack coordinates (`__loop10`). -/
def vkPointT : List Stmt :=
  [.atom (.const (.n 58) (word 2 0 0)), .atom (.mul (.n 59) (.n 17) (.n 58)),
    .atom (.hint (.allocDyn (.n 60) (.n 59))), .atom (.const (.n 61) (word 1 0 0)),
    .atom (.add (.n 62) (.n 61) (.n 17)), .atom (.const (.n 63) (word 1 0 0)),
    .atom (.const (.n 64) (word 16 0 0)), .atom (.mul (.n 65) (.n 7) (.n 64)),
    .callIf (.n 62) "__loop10" [.n 63, .n 17, .n 60, .n 65],
    .atom (.mul (.n 66) (.n 60) (.n 17)), .atom (.const (.n 67) (word 1 0 0)),
    .atom (.const (.n 68) (word 0 0 0)), .atom (.const (.n 69) (word 0 0 0)),
    .atom (.const (.n 70) (word 0 0 0)), .atom (.const (.n 71) (word 0 0 0))]

/-- The segment and the five lane coordinates squeezed. -/
def vkSqueezesT : List Stmt :=
  sqZeroT 11 72 ++ [.atom (.load (.n 91) (.n 66) 0), .atom (.hint (.alloc (.n 92) 5))] ++
    ((List.range 5).map fun i ↦
      sqZeroT (if i = 0 then 80 else 81 + 20 * i) (93 + 20 * i) ++ [.atom (.load (.n (112 + 20 * i)) (.n 92) i)]).flatten

/-- **The head.** -/
def vkHeadT : List Stmt :=
  (List.range 5).map (fun i ↦ .atom (.copy (.n (11 + i)) (.n i))) ++ vkBitsT ++
    copyWordsT (.n 7) (.n 9) 0 0 54 4 ++ vkPointT ++ vkSqueezesT ++ fsNextT (.n 5) 0 193

/-- **The first claim's record.** -/
def vkFirstT : List Stmt :=
  [.atom (.hint (.alloc (.n 203) 286)), .atom (.const (.n 204) (word 1 0 0)),
    .atom (.load (.n 204) (.n 203) 1), .atom (.load (.n 60) (.n 203) 2),
    .atom (.hint (.alloc (.n 205) 30))] ++
  eqtreeT (.n 9) (.n 205) 0 206 4 ++ copyWordsT (.n 205) (.n 203) 14 6 260 16 ++
  [.atom (.hint (.alloc (.n 276) 62))] ++ eqtreeT (.n 92) (.n 276) 0 277 5 ++
  [.atom (.const (.n 382) (word 1073741824 0 0)), .atom (.mul (.n 383) (.n 276) (.n 382)),
    .atom (.load (.n 383) (.n 203) 3), .atom (.hint (.alloc (.n 384) 2))] ++
  eqtreeT (.n 66) (.n 384) 0 385 1 ++ pairsDotT (.n 276) (.n 8) (consecOffs 30 0 25) 388 ++
  [.atom (.load (.n 487) (.n 384) 1), .atom (.mul (.n 488) (.n 487) (.n 486)),
    .atom (.add (.n 489) (.n 193) (.n 488)), .atom (.load (.n 489) (.n 203) 0)]

/-! ## The openings -/

/-- An opening's lane weights at the slot point `slot` and segment point `segp` from `b`: the
slot's equality weights (`eqfT`, the first 50), the segment's, and per lane the segments'
`first .. first + count` weighted (`keccak_slot_lanes`, G:2907-2920). -/
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
def slB (b z : ℕ) : ℕ := b + 10 * z + 13 * (z / 4)

/-- The permutation before group `g` of four slices. -/
def slP (b g : ℕ) : ℕ := b + 40 * g + 13 * (g - 1)

/-- The capacity before group `g`. -/
def slCap (capb b g : ℕ) : ℕ := if g = 0 then capb else slP b g + 8

/-- The cells of group `g`'s four reads. -/
def slCells (b g : ℕ) : List V :=
  ((List.range 4).map fun j ↦ [V.n (slB b (4 * g + j) + 7), .n (slB b (4 * g + j) + 9)]).flatten

/-- **The 64 slices** (G:3064-3071): read at the cursor and stored, four to a permutation, then the
ring map's first challenge squeezed (at `b + 854`). -/
def slicesT (cur : V) (capb b : ℕ) : List Stmt :=
  ((List.range 16).map fun g ↦
    (if g = 0 then [] else
      [keccakA (slCells b (g - 1) ++ cap5 (slCap capb b (g - 1)))
        ((List.range 13).map fun k ↦ .n (slP b g + k))]) ++
    ((List.range 4).map fun j ↦
      fsNextT cur (4 * g + j) (slB b (4 * g + j)) ++
        [.atom (.load (.n (slB b (4 * g + j))) (.n 10) (4 * g + j))]).flatten).flatten ++
  [keccakA (slCells b 15 ++ cap5 (slCap capb b 15)) ((List.range 13).map fun k ↦ .n (b + 835 + k))] ++
  challengeT (.n (b + 835)) (.n (b + 836)) (b + 848)

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

/-- **`fold_shifts`, level `t`** (G:2638-2652, `fold_node` G:2627-2635) from `B`, the coordinate
`a_t` at `a·g^t`, `1 + a_t` at `B + 2`: each node `(1 + a_t)·x₀ + a_t·x₁`. -/
def foldLevelT (src : ℕ → ℕ) (b : ℕ) (a : V) (t : ℕ) : List Stmt :=
  let n := 2 ^ (6 - t)
  let B := b + 195 * t
  [.atom (.load (.n B) a t), .atom (.const (.n (B + 1)) (word 1 0 0)),
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
  stepT 0 490 [181, 182, 183, 184, 185] 0 203 0 ++
  stepT 1 531 [525, 526, 527, 528, 529] 530 203 524 ++
  stepT 2 566 [560, 561, 562, 563, 564] 565 524 559 ++
  stepT 3 600 [594, 595, 596, 597, 598] 599 559 593 ++
  stepT 4 643 [637, 638, 639, 640, 641] 642 593 636 ++
  stepT 5 684 [678, 679, 680, 681, 682] 683 636 677 ++
  stepT 6 727 [721, 722, 723, 724, 725] 726 677 720 ++
  stepT 7 760 [754, 755, 756, 757, 758] 759 720 753 ++
  stepT 8 801 [795, 796, 797, 798, 799] 800 753 794 ++
  stepT 9 839 [833, 834, 835, 836, 837] 838 794 832 ++
  stepT 10 882 [876, 877, 878, 879, 880] 881 832 875 ++
  stepT 11 923 [917, 918, 919, 920, 921] 922 875 916

/-- The committed outputs' opening (G:2860-2873). -/
def vkOutT : List Stmt :=
  [.atom (.mul (.n 963) (.n 9) (.n 6)), .atom (.const (.n 964) (word 0 0 0)),
    .atom (.const (.n 965) (word 0 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n 957, .n 958, .n 959, .n 960, .n 961, .n 964,
      .n 965, .n 962, .n 193, .n 963] ((List.range 7).map fun j ↦ .n (966 + j))] ++
  fsNextT (.n 971) 0 973 ++ [.atom (.mul (.n 983) (.n 60) (.n 17))] ++
  slotLanesT 963 983 984 1 1 ++ dotLoadsT ((List.range 25).map (slotLaneV 984 1)) (.n 276) 30 1167 ++
  [.atom (.mul (.n 1241) (.n 1240) (.n 973)), .atom (.assertEq (.n 1241) (.n 972)),
    .atom (.const (.n 1242) (word 1 0 0)), .atom (.add (.n 1243) (.n 1242) (.n 17)),
    .atom (.const (.n 1244) (word 1 0 0)), .atom (.const (.n 1245) (word 16 0 0)),
    .atom (.mul (.n 1246) (.n 9) (.n 1245)),
    .callIf (.n 1243) "__loop11" [.n 1244, .n 17, .n 1246, .n 60]]

/-- The inputs' opening up to the slices and the ring map's first challenge (G:2875-2927). -/
def vkInT : List Stmt :=
  [.atom (.const (.n 1247) (word 2 0 0)), .atom (.mul (.n 1248) (.n 971) (.n 1247)),
    .atom (.load (.n 1249) (.n 203) 264), .atom (.const (.n 1250) (word 549755813888 0 0)),
    .atom (.mul (.n 1251) (.n 9) (.n 1250)),
    .call "keccak_plain_rounds__L4_L1" [.n 966, .n 967, .n 968, .n 969, .n 970, .n 980,
      .n 982, .n 1248, .n 1249, .n 1251] ((List.range 7).map fun j ↦ .n (1252 + j)),
    .atom (.hint (.alloc (.n 1259) 30))] ++
  eqtreeT (.n 9) (.n 1259) 39 1260 4 ++ pairsDotT (.n 1259) (.n 203) (consecOffs 14 270 16) 1314 ++
  [.atom (.const (.n 1377) (word 549755813888 0 0)), .atom (.mul (.n 1378) (.n 9) (.n 1377)),
    .atom (.mul (.n 1379) (.n 1378) (.n 6)), .atom (.const (.n 1380) (word 0 0 0)),
    .atom (.const (.n 1381) (word 0 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n 1252, .n 1253, .n 1254, .n 1255, .n 1256, .n 1380,
      .n 1381, .n 1257, .n 1258, .n 1379] ((List.range 7).map fun j ↦ .n (1382 + j))] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (1389 + j)) (.n (1382 + j)))) ++
  slicesT (.n 1387) 1389 1394

/-- The shifts of the slices' values. -/
def vkSh (r : ℕ) : ℕ := foldVal (fun j ↦ 2485 + j) 2549 6 r

/-- The inputs' check, the copy of their pack coordinates, the return (G:3073-3085). -/
def vkFinT : List Stmt :=
  [.atom (.load (.n 2249) (.n 203) 266), .atom (.mul (.n 2250) (.n 2249) (.n 17))] ++
  slotLanesT 1379 2250 2251 0 2 ++ [.atom (.load (.n 2484) (.n 203) 268)] ++
  (List.range 64).map (fun z ↦ .atom (.load (.n (2485 + z)) (.n 10) z)) ++
  foldT (fun j ↦ 2485 + j) 2549 (.n 2484) ++ [.atom (.load (.n 3647) (.n 203) 267)] ++
  (formAll (.n 3647) vkSh (slotLaneV 2251 2) 3648).1 ++
  [.atom (.mul (.n 3862) (.n 1376) (.n (formAll (.n 3647) vkSh (slotLaneV 2251 2) 3648).2.2)),
    .atom (.assertEq (.n 3862) (.n 1388)), .atom (.const (.n 3863) (word 1 0 0)),
    .atom (.add (.n 3864) (.n 3863) (.n 17)), .atom (.const (.n 3865) (word 1 0 0)),
    .atom (.const (.n 3866) (word 16 0 0)), .atom (.mul (.n 3867) (.n 1251) (.n 3866)),
    .callIf (.n 3864) "__loop12" [.n 3865, .n 17, .n 3867, .n 2249]] ++
  (List.range 5).map (fun j ↦ .atom (.copy (.n (3868 + j)) (.n (2237 + j)))) ++
  [.atom (.const (.n 3873) (word 27 0 0)), .atom (.mul (.n 3874) (.n 1387) (.n 3873)),
    .atom (.copy (.n 3875) (.n 3874)), .atom (.copy (.n 3876) (.n 973)),
    .atom (.copy (.n 3877) (.n 2248)),
    .ret [.n 3868, .n 3869, .n 3870, .n 3871, .n 3872, .n 3875, .n 3876, .n 3877]]

/-- **`verify_keccak`'s body.** -/
def vkT : List Stmt := vkHeadT ++ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinT

end
end LeanVM.Guest.B1.VerifySub
