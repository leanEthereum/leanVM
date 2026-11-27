/-
  LeanVM.Guest.B1.KeccakGkr.VkT

  `verify_keccak`'s body as a template, section by section.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
public import LeanVM.Guest.B1.Eq.EqTree
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»
import LeanVM.Guest.StmtsAppend

/-!
# `verify_keccak` as a template

The sections, in order:

* `vkHeadT`: the capacity copied, `pack_g`, `y_g`, the bits of `y` (pinned boolean), `step_g`
  and `rem_g` (`assert step_g⁸·rem_g = y_g`); the instance coordinates copied to `z_vals`;
  the point's pack coordinates copied (`verify_keccak_loop0`); the segment and the lane coordinates
  squeezed (`sqZeroT`); the committed outputs' value read;
* the first claim's record: `KC_KAPPA`, `KC_POINT`, the instance weights (`eqtreeT`, `copyWordsT`),
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
  [keccakA ([.n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]"), .n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]"), .n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")] ++ cap5 capb)
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
    [.atom (.load (.n b) (.n (val% «verify_keccak» "lane_tree")) 30), .atom (.const (.n (b + 1)) (word (2 ^ (2 ^ i - 1)) 0)),
      .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1)))]
  else
    [.atom (.load (.n b) (.n (val% «verify_keccak» "claims")) (22 * s + 5)), .atom (.load (.n (b + 1)) (.n b) i)]

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
  addChainT v0 c ⧺
    [.atom (.mul (.n (c + v0.length - 1)) (.n w0) (.n (addChainV v0 c)))] ⧺
    addChainT v1 c1 ⧺
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
    [.atom (.const (.n b) (word 2 0)), .atom (.mul (.n (b + 1)) (.n (val% «verify_keccak» "cursor@1")) (.n b)),
      .atom (.const (.n (b + 2)) (word 2 0)), .atom (.mul (.n (b + 3)) (.n (val% «verify_keccak» "pack_g")) (.n (b + 2))),
      .atom (.const (.n (b + 4)) (word 4194304 0)), .atom (.mul (.n (b + 5)) (.n (val% «verify_keccak» "claims")) (.n (b + 4))),
      .call "keccak_layer__L1"
        (cap.map .n ++ [.n (val% «verify_keccak» "value_rate[0]"), .n (val% «verify_keccak» "value_rate[1]"), .n (b + 1), .n (b + 3), .n (val% «verify_keccak» "step_g@2"), .n (val% «verify_keccak» "rem_g@3"), .n (val% «verify_keccak» "claims"), .n (b + 5),
          .n io, .n (val% «verify_keccak» "tabs"), .n (val% «verify_keccak» "stream")]) ((List.range 6).map fun j ↦ .n (b + 6 + j))]
  else
    [.atom (.const (.n b) (word 0 0)), .atom (.const (.n (b + 1)) (word 0 0)),
      .atom (.const (.n (b + 2)) (word 2 0)), .atom (.mul (.n (b + 3)) (.n (val% «verify_keccak» "pack_g")) (.n (b + 2))),
      .atom (.const (.n (b + 4)) (word 4194304 0)), .atom (.mul (.n (b + 5)) (.n cb) (.n (b + 4))),
      .atom (.const (.n (b + 6)) (word 4194304 0)), .atom (.mul (.n (b + 7)) (.n pn) (.n (b + 6))),
      .call "keccak_layer__L0"
        (cap.map .n ++ [.n b, .n (b + 1), .n cur, .n (b + 3), .n (val% «verify_keccak» "step_g@2"), .n (val% «verify_keccak» "rem_g@3"), .n (b + 5), .n (b + 7),
          .n io, .n (val% «verify_keccak» "tabs"), .n (val% «verify_keccak» "stream")]) ((List.range 6).map fun j ↦ .n (b + 8 + j))]

/-- The size of `stepTailT`'s values. -/
def stepTailSz (s : ℕ) : ℕ := if s = 0 then 12 else 14

/-- **Step `s`** from `b`: the claim's point, its segment weights (`eqtree_frame` of
one coordinate, `1 + r` at `b + 4`, `r` at `b + 5`), the flips, the `ι` term, the call. -/
def stepT (s b : ℕ) (cap : List ℕ) (cur cb pn : ℕ) : List Stmt :=
  let f0 := b + 6
  let c := f0 + flipSz s * (iotaUsed s).length
  [.atom (.load (.n b) (.n (val% «verify_keccak» "claims")) (22 * s + 2)), .atom (.mul (.n (b + 1)) (.n b) (.n (val% «verify_keccak» "pack_g")))] ⧺
  eqfLevel0T (.n (b + 1)) 0 (b + 2) ⧺ flipsT s f0 ⧺ iotaSegT s f0 c (b + 4) (b + 5) ⧺
  stepTailT s (iotaSegEnd s c) cap cur cb pn (iotaSegEnd s c - 1)

/-- The value after step `s`. -/
def stepEnd (s b : ℕ) : ℕ :=
  iotaSegEnd s (b + 6 + flipSz s * (iotaUsed s).length) + stepTailSz s

/-! ## The head -/

/-- `pack_g`, `y_g`, the bits of `y` (pinned boolean), `step_g = g^⌊y/8⌋`, `rem_g = g^(y % 8)`
and their check `step_g⁸·rem_g = y_g`. -/
def vkBitsT : List Stmt :=
  [.atom (.const (.n (val% «verify_keccak» "pack_g~0")) (word 8070450532247928836 0)),
    .atom (.mul (.n (val% «verify_keccak» "pack_g")) (.n (val% «verify_keccak» "tau_g")) (.n (val% «verify_keccak» "pack_g~0"))),
    .atom (.const (.n (val% «verify_keccak» "s5#0")) (word 2 0)),
    .atom (.mul (.n (val% «verify_keccak» "s5#1")) (.n (val% «verify_keccak» "pack_g")) (.n (val% «verify_keccak» "s5#0"))),
    .atom (.hint (.bitsExp (.n (val% «verify_keccak» "s5#1")) 5 (.stack [.n (val% «verify_keccak» "y_bits[0]"), .n (val% «verify_keccak» "y_bits[1]"), .n (val% «verify_keccak» "y_bits[2]"), .n (val% «verify_keccak» "y_bits[3]"), .n (val% «verify_keccak» "y_bits[4]")]))),
    .atom (.mul (.n (val% «verify_keccak» "y_bits[0]")) (.n (val% «verify_keccak» "y_bits[0]")) (.n (val% «verify_keccak» "y_bits[0]"))),
    .atom (.mul (.n (val% «verify_keccak» "y_bits[1]")) (.n (val% «verify_keccak» "y_bits[1]")) (.n (val% «verify_keccak» "y_bits[1]"))),
    .atom (.mul (.n (val% «verify_keccak» "y_bits[2]")) (.n (val% «verify_keccak» "y_bits[2]")) (.n (val% «verify_keccak» "y_bits[2]"))),
    .atom (.mul (.n (val% «verify_keccak» "y_bits[3]")) (.n (val% «verify_keccak» "y_bits[3]")) (.n (val% «verify_keccak» "y_bits[3]"))),
    .atom (.mul (.n (val% «verify_keccak» "y_bits[4]")) (.n (val% «verify_keccak» "y_bits[4]")) (.n (val% «verify_keccak» "y_bits[4]"))),
    .atom (.const (.n (val% «verify_keccak» "step_g@1~0")) (word 1 0)),
    .atom (.const (.n (val% «verify_keccak» "step_g@1~1")) (word 3 0)),
    .atom (.mul (.n (val% «verify_keccak» "step_g@1~2")) (.n (val% «verify_keccak» "y_bits[3]")) (.n (val% «verify_keccak» "step_g@1~1"))),
    .atom (.add (.n (val% «verify_keccak» "step_g@1")) (.n (val% «verify_keccak» "step_g@1~0")) (.n (val% «verify_keccak» "step_g@1~2"))),
    .atom (.const (.n (val% «verify_keccak» "step_g@2~0")) (word 1 0)),
    .atom (.const (.n (val% «verify_keccak» "step_g@2~1")) (word 5 0)),
    .atom (.mul (.n (val% «verify_keccak» "step_g@2~2")) (.n (val% «verify_keccak» "y_bits[4]")) (.n (val% «verify_keccak» "step_g@2~1"))),
    .atom (.add (.n (val% «verify_keccak» "step_g@2~3")) (.n (val% «verify_keccak» "step_g@2~0")) (.n (val% «verify_keccak» "step_g@2~2"))),
    .atom (.mul (.n (val% «verify_keccak» "step_g@2")) (.n (val% «verify_keccak» "step_g@1")) (.n (val% «verify_keccak» "step_g@2~3"))),
    .atom (.const (.n (val% «verify_keccak» "rem_g@1~0")) (word 1 0)),
    .atom (.const (.n (val% «verify_keccak» "rem_g@1~1")) (word 3 0)),
    .atom (.mul (.n (val% «verify_keccak» "rem_g@1~2")) (.n (val% «verify_keccak» "y_bits[0]")) (.n (val% «verify_keccak» "rem_g@1~1"))),
    .atom (.add (.n (val% «verify_keccak» "rem_g@1")) (.n (val% «verify_keccak» "rem_g@1~0")) (.n (val% «verify_keccak» "rem_g@1~2"))),
    .atom (.const (.n (val% «verify_keccak» "rem_g@2~0")) (word 1 0)),
    .atom (.const (.n (val% «verify_keccak» "rem_g@2~1")) (word 5 0)),
    .atom (.mul (.n (val% «verify_keccak» "rem_g@2~2")) (.n (val% «verify_keccak» "y_bits[1]")) (.n (val% «verify_keccak» "rem_g@2~1"))),
    .atom (.add (.n (val% «verify_keccak» "rem_g@2~3")) (.n (val% «verify_keccak» "rem_g@2~0")) (.n (val% «verify_keccak» "rem_g@2~2"))),
    .atom (.mul (.n (val% «verify_keccak» "rem_g@2")) (.n (val% «verify_keccak» "rem_g@1")) (.n (val% «verify_keccak» "rem_g@2~3"))),
    .atom (.const (.n (val% «verify_keccak» "rem_g@3~0")) (word 1 0)),
    .atom (.const (.n (val% «verify_keccak» "rem_g@3~1")) (word 17 0)),
    .atom (.mul (.n (val% «verify_keccak» "rem_g@3~2")) (.n (val% «verify_keccak» "y_bits[2]")) (.n (val% «verify_keccak» "rem_g@3~1"))),
    .atom (.add (.n (val% «verify_keccak» "rem_g@3~3")) (.n (val% «verify_keccak» "rem_g@3~0")) (.n (val% «verify_keccak» "rem_g@3~2"))),
    .atom (.mul (.n (val% «verify_keccak» "rem_g@3")) (.n (val% «verify_keccak» "rem_g@2")) (.n (val% «verify_keccak» "rem_g@3~3"))),
    .atom (.mul (.n (val% «verify_keccak» "s11#0")) (.n (val% «verify_keccak» "step_g@2")) (.n (val% «verify_keccak» "step_g@2"))),
    .atom (.mul (.n (val% «verify_keccak» "s11#1")) (.n (val% «verify_keccak» "s11#0")) (.n (val% «verify_keccak» "s11#0"))),
    .atom (.mul (.n (val% «verify_keccak» "s11#2")) (.n (val% «verify_keccak» "s11#1")) (.n (val% «verify_keccak» "s11#1"))),
    .atom (.mul (.n (val% «verify_keccak» "s11#3")) (.n (val% «verify_keccak» "s11#2")) (.n (val% «verify_keccak» "rem_g@3"))),
    .atom (.const (.n (val% «verify_keccak» "s11#4")) (word 2 0)),
    .atom (.mul (.n (val% «verify_keccak» "s11#5")) (.n (val% «verify_keccak» "pack_g")) (.n (val% «verify_keccak» "s11#4"))),
    .atom (.assertEq (.n (val% «verify_keccak» "s11#3")) (.n (val% «verify_keccak» "s11#5")))]

/-- The point's allocation and the copy of its pack coordinates (`verify_keccak_loop0`). -/
def vkPointT : List Stmt :=
  [.atom (.const (.n (val% «verify_keccak» "point~0")) (word 2 0)), .atom (.mul (.n (val% «verify_keccak» "point~1")) (.n (val% «verify_keccak» "pack_g")) (.n (val% «verify_keccak» "point~0"))),
    .atom (.hint (.allocDyn (.n (val% «verify_keccak» "point")) (.n (val% «verify_keccak» "point~1")))), .atom (.const (.n (val% «verify_keccak» "s17#0")) (word 1 0)),
    .atom (.add (.n (val% «verify_keccak» "s17#1")) (.n (val% «verify_keccak» "s17#0")) (.n (val% «verify_keccak» "pack_g"))), .atom (.const (.n (val% «verify_keccak» "s17#2")) (word 1 0)),
    .atom (.const (.n (val% «verify_keccak» "s17#3")) (word 16 0)), .atom (.mul (.n (val% «verify_keccak» "s17#4")) (.n (val% «verify_keccak» "chi")) (.n (val% «verify_keccak» "s17#3"))),
    .callIf (.n (val% «verify_keccak» "s17#1")) name% «verify_keccak_loop0» [.n (val% «verify_keccak» "s17#2"), .n (val% «verify_keccak» "pack_g"), .n (val% «verify_keccak» "point"), .n (val% «verify_keccak» "s17#4")],
    .atom (.mul (.n (val% «verify_keccak» "segment")) (.n (val% «verify_keccak» "point")) (.n (val% «verify_keccak» "pack_g"))), .atom (.const (.n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0")) (word 1 0)),
    .atom (.const (.n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) (word 0 0)), .atom (.const (.n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) (word 0 0)),
    .atom (.const (.n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) (word 0 0)), .atom (.const (.n (val% «verify_keccak» "s19.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) (word 0 0))]

/-- The segment and the five lane coordinates squeezed. -/
def vkSqueezesT : List Stmt :=
  sqZeroT 13 74 ⧺ [.atom (.load (.n (val% «verify_keccak» "nxt[0]@1")) (.n (val% «verify_keccak» "segment")) 0), .atom (.hint (.alloc (.n (val% «verify_keccak» "r_lane")) 5))] ⧺
    ((List.range 5).map fun i ↦
      sqZeroT (if i = 0 then 82 else 83 + 13 * i) (88 + 13 * i) ⧺
        [.atom (.load (.n (88 + 13 * i)) (.n (val% «verify_keccak» "r_lane")) i)]).flatten

/-- **The head.** -/
def vkHeadT : List Stmt :=
  (List.range 5).map (fun i ↦ .atom (.copy (.n ((val% «verify_keccak» "sp[0]@1") + i)) (.n i))) ⧺ vkBitsT ⧺
    copyWordsT (.n (val% «verify_keccak» "chi")) (.n (val% «verify_keccak» "z_vals")) 0 0 56 4 ⧺ vkPointT ⧺ vkSqueezesT ⧺ fsNextT (.n (val% «verify_keccak» "cursor@1")) 0 (val% «verify_keccak» "x@1")

/-- **The first claim's record.** -/
def vkFirstT : List Stmt :=
  [.atom (.hint (.alloc (.n (val% «verify_keccak» "claims")) 286)), .atom (.const (.n (val% «verify_keccak» "s32#0")) (word 1 0)),
    .atom (.load (.n (val% «verify_keccak» "s32#0")) (.n (val% «verify_keccak» "claims")) 1), .atom (.load (.n (val% «verify_keccak» "point")) (.n (val% «verify_keccak» "claims")) 2),
    .atom (.hint (.alloc (.n (val% «verify_keccak» "mu_tree")) 30))] ⧺
  eqtreeT (.n (val% «verify_keccak» "z_vals")) (.n (val% «verify_keccak» "mu_tree")) 0 159 4 ⧺ copyWordsT (.n (val% «verify_keccak» "mu_tree")) (.n (val% «verify_keccak» "claims")) 14 6 213 16 ⧺
  [.atom (.hint (.alloc (.n (val% «verify_keccak» "lane_tree")) 62))] ⧺ eqtreeT (.n (val% «verify_keccak» "r_lane")) (.n (val% «verify_keccak» "lane_tree")) 0 230 5 ⧺
  [.atom (.const (.n (val% «verify_keccak» "s40#0")) (word 1073741824 0)), .atom (.mul (.n (val% «verify_keccak» "s40#1")) (.n (val% «verify_keccak» "lane_tree")) (.n (val% «verify_keccak» "s40#0"))),
    .atom (.load (.n (val% «verify_keccak» "s40#1")) (.n (val% «verify_keccak» "claims")) 3), .atom (.hint (.alloc (.n (val% «verify_keccak» "segment_tree")) 2))] ⧺
  eqtreeT (.n (val% «verify_keccak» "segment")) (.n (val% «verify_keccak» "segment_tree")) 0 338 1 ⧺ pairsDotT (.n (val% «verify_keccak» "lane_tree")) (.n (val% «verify_keccak» "output_lanes")) (consecOffs 30 0 25) 341 ⧺
  [.atom (.load (.n (val% «verify_keccak» "s45#0")) (.n (val% «verify_keccak» "segment_tree")) 1), .atom (.mul (.n (val% «verify_keccak» "s45#1")) (.n (val% «verify_keccak» "s45#0")) (.n (val% «verify_keccak» "output@25"))),
    .atom (.add (.n (val% «verify_keccak» "s45#2")) (.n (val% «verify_keccak» "x@1")) (.n (val% «verify_keccak» "s45#1"))), .atom (.load (.n (val% «verify_keccak» "s45#2")) (.n (val% «verify_keccak» "claims")) 0)]

/-! ## The openings -/

/-- An opening's lane weights at the slot point `slot` and segment point `segp` from `b`: the
slot's equality weights (`eqfT`, the first 50), the segment's, and per lane the segments'
`first .. first + count` weighted (`keccak_slot_lanes`). -/
def slotLanesT (slot segp b first count : ℕ) : List Stmt :=
  eqfT (.n slot) 0 6 50 b ⧺ eqfLevel0T (.n segp) 0 (b + 129) ⧺
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
      fsNextT cur (4 * g + j) (slB b (4 * g + j)) ⧺
        [.atom (.load (.n (slB b (4 * g + j))) (.n (val% «verify_keccak» "slices")) (4 * g + j))]).flatten).flatten ⧺
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
    .atom (.add (.n (B + 2)) (.n (B + 1)) (.n B))] ⧺
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
  stepT 0 443 [148, 149, 150, 151, 152] 0 156 0 ⧺
  stepT 1 484 [478, 479, 480, 481, 482] 483 156 477 ⧺
  stepT 2 519 [513, 514, 515, 516, 517] 518 477 512 ⧺
  stepT 3 553 [547, 548, 549, 550, 551] 552 512 546 ⧺
  stepT 4 596 [590, 591, 592, 593, 594] 595 546 589 ⧺
  stepT 5 637 [631, 632, 633, 634, 635] 636 589 630 ⧺
  stepT 6 680 [674, 675, 676, 677, 678] 679 630 673 ⧺
  stepT 7 713 [707, 708, 709, 710, 711] 712 673 706 ⧺
  stepT 8 754 [748, 749, 750, 751, 752] 753 706 747 ⧺
  stepT 9 792 [786, 787, 788, 789, 790] 791 747 785 ⧺
  stepT 10 835 [829, 830, 831, 832, 833] 834 785 828 ⧺
  stepT 11 876 [870, 871, 872, 873, 874] 875 828 869

/-- The committed outputs' opening. -/
def vkOutT : List Stmt :=
  [.atom (.mul (.n (val% «verify_keccak» "out_slot")) (.n (val% «verify_keccak» "z_vals")) (.n (val% «verify_keccak» "tau_g"))), .atom (.const (.n (val% «verify_keccak» "fs0@14~7")) (word 0 0)),
    .atom (.const (.n (val% «verify_keccak» "fs0@14~8")) (word 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n (val% «verify_keccak» "fs0@13"), .n (val% «verify_keccak» "fs1@13"), .n (val% «verify_keccak» "fs2@13"), .n (val% «verify_keccak» "fs3@13"), .n (val% «verify_keccak» "fs4@13"), .n (val% «verify_keccak» "fs0@14~7"),
      .n (val% «verify_keccak» "fs0@14~8"), .n (val% «verify_keccak» "cursor@13"), .n (val% «verify_keccak» "x@1"), .n (val% «verify_keccak» "out_slot"), .n (val% «verify_keccak» "tabs")] ((List.range 7).map fun j ↦ .n ((val% «verify_keccak» "fs0@14") + j))] ⧺
  fsNextT (.n (val% «verify_keccak» "cursor@14")) 0 (val% «verify_keccak» "x@2") ⧺ [.atom (.mul (.n (val% «verify_keccak» "s52#0")) (.n (val% «verify_keccak» "point")) (.n (val% «verify_keccak» "pack_g")))] ⧺
  slotLanesT 916 929 930 1 1 ⧺ dotLoadsT ((List.range 25).map (slotLaneV 930 1)) (.n (val% «verify_keccak» "lane_tree")) 30 1113 ⧺
  [.atom (.mul (.n (val% «verify_keccak» "s55#0")) (.n (val% «verify_keccak» "lanes_sum@25")) (.n (val% «verify_keccak» "x@2"))), .atom (.assertEq (.n (val% «verify_keccak» "s55#0")) (.n (val% «verify_keccak» "out_value"))),
    .atom (.const (.n (val% «verify_keccak» "s57#0")) (word 1 0)), .atom (.add (.n (val% «verify_keccak» "s57#1")) (.n (val% «verify_keccak» "s57#0")) (.n (val% «verify_keccak» "pack_g"))),
    .atom (.const (.n (val% «verify_keccak» "s57#2")) (word 1 0)), .atom (.const (.n (val% «verify_keccak» "s57#3")) (word 16 0)),
    .atom (.mul (.n (val% «verify_keccak» "s57#4")) (.n (val% «verify_keccak» "z_vals")) (.n (val% «verify_keccak» "s57#3"))),
    .callIf (.n (val% «verify_keccak» "s57#1")) name% «verify_keccak_loop1» [.n (val% «verify_keccak» "s57#2"), .n (val% «verify_keccak» "pack_g"), .n (val% «verify_keccak» "s57#4"), .n (val% «verify_keccak» "point")]]

/-- The inputs' opening up to the slices. -/
def vkInT : List Stmt :=
  [.atom (.const (.n (val% «verify_keccak» "fs0@15~7")) (word 2 0)), .atom (.mul (.n (val% «verify_keccak» "fs0@15~8")) (.n (val% «verify_keccak» "cursor@14")) (.n (val% «verify_keccak» "fs0@15~7"))),
    .atom (.load (.n (val% «verify_keccak» "fs0@15~9")) (.n (val% «verify_keccak» "claims")) 264), .atom (.const (.n (val% «verify_keccak» "fs0@15~10")) (word 549755813888 0)),
    .atom (.mul (.n (val% «verify_keccak» "fs0@15~11")) (.n (val% «verify_keccak» "z_vals")) (.n (val% «verify_keccak» "fs0@15~10"))),
    .call "keccak_plain_rounds__L4_L1" [.n (val% «verify_keccak» "fs0@14"), .n (val% «verify_keccak» "fs1@14"), .n (val% «verify_keccak» "fs2@14"), .n (val% «verify_keccak» "fs3@14"), .n (val% «verify_keccak» "fs4@14"), .n (val% «verify_keccak» "word_rate[0]"),
      .n (val% «verify_keccak» "word_rate[1]"), .n (val% «verify_keccak» "fs0@15~8"), .n (val% «verify_keccak» "fs0@15~9"), .n (val% «verify_keccak» "fs0@15~11"), .n (val% «verify_keccak» "tabs")] ((List.range 7).map fun j ↦ .n ((val% «verify_keccak» "fs0@15") + j)),
    .atom (.hint (.alloc (.n (val% «verify_keccak» "low_tree")) 30))] ⧺
  eqtreeT (.n (val% «verify_keccak» "z_vals")) (.n (val% «verify_keccak» "low_tree")) 39 1206 4 ⧺ pairsDotT (.n (val% «verify_keccak» "low_tree")) (.n (val% «verify_keccak» "claims")) (consecOffs 14 270 16) 1260 ⧺
  [.atom (.const (.n (val% «verify_keccak» "in_slot~0")) (word 549755813888 0)), .atom (.mul (.n (val% «verify_keccak» "in_slot~1")) (.n (val% «verify_keccak» "z_vals")) (.n (val% «verify_keccak» "in_slot~0"))),
    .atom (.mul (.n (val% «verify_keccak» "in_slot")) (.n (val% «verify_keccak» "in_slot~1")) (.n (val% «verify_keccak» "tau_g"))), .atom (.const (.n (val% «verify_keccak» "fs0@16~7")) (word 0 0)),
    .atom (.const (.n (val% «verify_keccak» "fs0@16~8")) (word 0 0)),
    .call "keccak_plain_rounds__L6_L0" [.n (val% «verify_keccak» "fs0@15"), .n (val% «verify_keccak» "fs1@15"), .n (val% «verify_keccak» "fs2@15"), .n (val% «verify_keccak» "fs3@15"), .n (val% «verify_keccak» "fs4@15"), .n (val% «verify_keccak» "fs0@16~7"),
      .n (val% «verify_keccak» "fs0@16~8"), .n (val% «verify_keccak» "cursor@15"), .n (val% «verify_keccak» "low_value"), .n (val% «verify_keccak» "in_slot"), .n (val% «verify_keccak» "tabs")] ((List.range 7).map fun j ↦ .n ((val% «verify_keccak» "fs0@16") + j))] ⧺
  (List.range 5).map (fun j ↦ .atom (.copy (.n ((val% «verify_keccak» "sp[0]@2") + j)) (.n ((val% «verify_keccak» "fs0@16") + j)))) ⧺
  slicesT (.n (val% «verify_keccak» "cursor@16")) 1335 1340

/-- The shifts of the slices' values. -/
def vkSh (r : ℕ) : ℕ := foldVal (fun j ↦ 1976 + j) 2040 6 r

/-- The inputs' check, the copy of their pack coordinates, the return. -/
def vkFinT : List Stmt :=
  [.atom (.load (.n (val% «verify_keccak» "last_point")) (.n (val% «verify_keccak» "claims")) 266), .atom (.mul (.n (val% «verify_keccak» "s72#0")) (.n (val% «verify_keccak» "last_point")) (.n (val% «verify_keccak» "pack_g")))] ⧺
  slotLanesT 1325 1741 1742 0 2 ⧺ [.atom (.load (.n (val% «verify_keccak» "last_local")) (.n (val% «verify_keccak» "claims")) 268)] ⧺
  (List.range 64).map (fun z ↦ .atom (.load (.n ((val% «verify_keccak» "level[0]") + z)) (.n (val% «verify_keccak» "slices")) z)) ⧺
  foldT (fun j ↦ 1976 + j) 2040 (.n (val% «verify_keccak» "last_local")) ⧺ [.atom (.load (.n (val% «verify_keccak» "last_lanes")) (.n (val% «verify_keccak» "claims")) 267)] ⧺
  (formAll (.n (val% «verify_keccak» "last_lanes")) vkSh (slotLaneV 1742 2) 3139).1 ⧺
  [.atom (.mul (.n (val% «verify_keccak» "s79#1")) (.n (val% «verify_keccak» "mu_at_low@16")) (.n (formAll (.n (val% «verify_keccak» "last_lanes")) vkSh (slotLaneV 1742 2) 3139).2.2)),
    .atom (.assertEq (.n (val% «verify_keccak» "s79#1")) (.n (val% «verify_keccak» "in_value"))), .atom (.const (.n (val% «verify_keccak» "s81#0")) (word 1 0)),
    .atom (.add (.n (val% «verify_keccak» "s81#1")) (.n (val% «verify_keccak» "s81#0")) (.n (val% «verify_keccak» "pack_g"))), .atom (.const (.n (val% «verify_keccak» "s81#2")) (word 1 0)),
    .atom (.const (.n (val% «verify_keccak» "s81#3")) (word 16 0)), .atom (.mul (.n (val% «verify_keccak» "s81#4")) (.n (val% «verify_keccak» "fs0@15~11")) (.n (val% «verify_keccak» "s81#3"))),
    .callIf (.n (val% «verify_keccak» "s81#1")) name% «verify_keccak_loop2» [.n (val% «verify_keccak» "s81#2"), .n (val% «verify_keccak» "pack_g"), .n (val% «verify_keccak» "s81#4"), .n (val% «verify_keccak» "last_point")]] ⧺
  (List.range 5).map (fun j ↦ .atom (.copy (.n ((val% «verify_keccak» "s82#0") + j)) (.n ((val% «verify_keccak» "nxt[8]@22") + j)))) ⧺
  [.atom (.const (.n (val% «verify_keccak» "s82#1")) (word 27 0)), .atom (.mul (.n (val% «verify_keccak» "s82#2")) (.n (val% «verify_keccak» "cursor@16")) (.n (val% «verify_keccak» "s82#1"))),
    .atom (.copy (.n (val% «verify_keccak» "s82#0[5]")) (.n (val% «verify_keccak» "s82#2"))), .atom (.copy (.n (val% «verify_keccak» "s82#0[6]")) (.n (val% «verify_keccak» "x@2"))),
    .ret [.n (val% «verify_keccak» "s82#0"), .n (val% «verify_keccak» "s82#0[1]"), .n (val% «verify_keccak» "s82#0[2]"), .n (val% «verify_keccak» "s82#0[3]"), .n (val% «verify_keccak» "s82#0[4]"), .n (val% «verify_keccak» "s82#0[5]"), .n (val% «verify_keccak» "s82#0[6]")]]

/-- **`verify_keccak`'s body.** -/
def vkT : List Stmt := vkHeadT ⧺ vkFirstT ⧺ vkStepsT ⧺ vkOutT ⧺ vkInT ⧺ vkFinT

end
end LeanVM.Guest.B1.VerifySub
