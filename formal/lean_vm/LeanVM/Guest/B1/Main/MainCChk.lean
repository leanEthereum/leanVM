/-
  LeanVM.Guest.B1.Main.MainCChk

  `main`'s body as one evaluated block (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.B1.Fwd.Canon
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main»

/-!
# `main`'s body, evaluated

`mFlat` is `main`'s body with both branches of the direct DA check and the leaf's branch inlined
(`mPre`, `mDa`, `mDaZ`, `mMid`, `mLeaf`, `mPost`), every value defined at its first occurrence
(`chk`). The atoms needing a side condition are the range
checks, the loads through `main`'s buffers and the header, the touches through the counts
(`assert_gpow`), and the four equality checks
(`mSideOk`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `main`'s body, both branches of each conditional block inlined. -/
noncomputable def mFlat : List Stmt := mPre ++ mDa ++ mDaZ ++ mMid ++ mLeaf ++ mAgg ++ mPost

/-- The evaluated block: `mFlat` itself (`main` hints no inverse). -/
noncomputable def mFlatE : List Stmt := mFlat

/-- `main`'s stores: the byte table, the own DA digest (both branches), the first running count,
the leaf's deferred claim. -/
def mStoresL : List Atom :=
  (List.range 256).map (fun v => .load (.n (48 + v)) (.n (val% «main» "byte_bits")) v) ++
    [.load (.n (val% «main» "s43.t.s1#0")) (.n (val% «main» "own_da")) 0, .load (.n (val% «main» "s43.t.s1#0[1]")) (.n (val% «main» "own_da")) 1, .load (.n (val% «main» "s43.e.s0#0")) (.n (val% «main» "own_da")) 0,
      .load (.n (val% «main» "s43.e.s1#0")) (.n (val% «main» "own_da")) 1, .load (.n (val% «main» "s48#0")) (.n (val% «main» "written")) 0] ++
    (List.range 23).map (fun k => .load (.n (420 + k)) (.n (val% «main» "defer_stmt")) k) ++ [.load (.n (val% «main» "leaf_value")) (.n (val% «main» "defer_stmt")) 23]

/-- `main`'s loads, by their words' numbers: the five reads, then the stores. -/
def mLoadOk (d p o : ℕ) : Bool :=
  decide ((d, p, o) ∈ [(404, 403, 0), (445, 415, 0), (446, 415, 1), (450, 449, 0),
    (454, 453, 0)]) ||
  (decide (p = 47) && decide (d = 48 + o) && decide (o < 256)) ||
  decide ((d, p, o) ∈ [(378, 366, 0), (379, 366, 1), (380, 366, 0), (381, 366, 1),
    (399, 398, 0)]) ||
  (decide (p = 416) && (decide (o < 23 ∧ d = 420 + o) || decide (o = 23 ∧ d = 419)))

/-- The range checks: the checked value and the bound's constant. -/
def rcPairs : List (ℕ × ℕ) :=
  [(6, 14), (7, 18), (405, 6)]

/-- The atoms of `main` whose side conditions its completeness discharges. -/
def mSideOk : Atom → Bool
  | .rangeCheck x y _ _ k => decide ((x.idx, k.idx) ∈ rcPairs) && decide (x = .n x.idx) &&
      decide (k = .n k.idx) && decide (k.idx < y.idx)
  | .load d p o => decide (d = .n d.idx) && decide (p = .n p.idx) && mLoadOk d.idx p.idx o
  | .touch t p => decide (t = .n t.idx) && decide (p = .n p.idx) &&
      decide ((t.idx, p.idx) ∈ [(8, 0), (9, 1), (10, 2), (11, 3), (12, 4), (13, 5), (25, 24)])
  | .assertEq x y => decide ((x, y) ∈ [(V.n (val% «main» "s50#1"), V.n (val% «main» "n_total_g")), (.n (val% «main» "s53#3"), .n (val% «main» "s53#4")), (.n (val% «main» "s59#1"), .n (val% «main» "own_0")),
      (.n (val% «main» "s60#3"), .n (val% «main» "own_1"))])
  | _ => false

/-- The stores of `main`'s body. -/
noncomputable def mStores : List Atom := storesOf 0 mFlatE

/-- A block's atoms but the stores. -/
noncomputable def noStores (P : List Stmt) : List Atom :=
  (atomsIn P).filter fun a => decide (a ∉ mStores)

/-- **`main`'s body, evaluated.** -/
noncomputable def mainCOk : Bool :=
  (chk 0 mFlatE).isSome &&
  (atomsIn mFlat).all (fun a => !needsSide a || mSideOk a)

set_option maxRecDepth 100000 in
theorem mainc_ok : mainCOk = true := by decide +kernel

/-- The statements defining `main`'s oracle values: hints, `HeapBuf`s, calls' returns. -/
def mOrcStmts : List Stmt :=
  [.atom (.hint (.witness "meta" (.stack [.n (val% «main» "meta[0]"), .n (val% «main» "meta[1]"), .n (val% «main» "meta[2]"), .n (val% «main» "meta[3]"), .n (val% «main» "meta[4]"), .n (val% «main» "meta[5]"), .n (val% «main» "meta[6]"), .n (val% «main» "meta[7]")]))),
    .atom (.hint (.witness "fs_seed" (.stack [.n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]")]))),
    .call "exponent_tables" [] [.n (val% «main» "g_squares")], .atom (.hint (.allocDyn (.n (val% «main» "lx_table")) (.n (val% «main» "lx_table~1")))),
    .atom (.hint (.allocDyn (.n (val% «main» "lean_sphincs_table")) (.n (val% «main» "lean_sphincs_table~1")))),
    .call "claim_list_digest" [.n (val% «main» "lx_table"), .n (val% «main» "meta[0]")] [.n (val% «main» "xd_0"), .n (val% «main» "xd_1")],
    .call "claim_list_digest" [.n (val% «main» "lean_sphincs_table"), .n (val% «main» "meta[3]")] [.n (val% «main» "sd_0"), .n (val% «main» "sd_1")],
    .atom (.hint (.allocDyn (.n (val% «main» "cover")) (.n (val% «main» "n_total_g")))), .atom (.hint (.alloc (.n (val% «main» "byte_bits")) 256)),
    .atom (.hint (.allocDyn (.n (val% «main» "da_digests")) (.n (val% «main» "da_digests~2")))),
    .call "da_verify" [.n (val% «main» "byte_bits")] [.n (val% «main» "root_0"), .n (val% «main» "root_1"), .n (val% «main» "z")],
    .atom (.hint (.allocDyn (.n (val% «main» "child_pi")) (.n (val% «main» "child_pi~0")))), .atom (.hint (.allocDyn (.n (val% «main» "child_fresh")) (.n (val% «main» "child_fresh~4")))),
    .atom (.hint (.allocDyn (.n (val% «main» "child_carried")) (.n (val% «main» "child_carried~4")))), .atom (.hint (.allocDyn (.n (val% «main» "written")) (.n (val% «main» "written~1")))),
    .atom (.hint (.witness "da_pick" (.stack [.n (val% «main» "da_pick")]))),
    .atom (.hint (.alloc (.n (val% «main» "defer_stmt")) 24)), .atom (.hint (.witness "leaf_defer" (.stack [.n (val% «main» "leaf_value")]))),
    .call "statement_digest" [.n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "xd_0"), .n (val% «main» "xd_1"), .n (val% «main» "sd_0"), .n (val% «main» "sd_1"), .n (val% «main» "own_0~2"), .n (val% «main» "own_0~3"), .n (val% «main» "defer_stmt")]
      [.n (val% «main» "own_0"), .n (val% «main» "own_1")]]

/-- The atoms defining `main`'s words the proof reads. -/
def mDefAtoms : List Atom :=
  [.mul (.n (val% «main» "lx_slots_g")) (.n (val% «main» "meta[0]")) (.n (val% «main» "meta[1]")), .mul (.n (val% «main» "lean_sphincs_slots_g")) (.n (val% «main» "meta[3]")) (.n (val% «main» "meta[4]")), .mul (.n (val% «main» "n_total_g")) (.n (val% «main» "lx_slots_g")) (.n (val% «main» "lean_sphincs_slots_g")),
    .mul (.n (val% «main» "lx_table~0")) (.n (val% «main» "lx_slots_g")) (.n (val% «main» "lx_slots_g")), .mul (.n (val% «main» "lx_table~1")) (.n (val% «main» "lx_table~0")) (.n (val% «main» "lx_table~0")),
    .mul (.n (val% «main» "lean_sphincs_table~0")) (.n (val% «main» "lean_sphincs_slots_g")) (.n (val% «main» "lean_sphincs_slots_g")), .mul (.n (val% «main» "lean_sphincs_table~1")) (.n (val% «main» "lean_sphincs_table~0")) (.n (val% «main» "lean_sphincs_table~0")), .mul (.n (val% «main» "sp_cover")) (.n (val% «main» "cover")) (.n (val% «main» "lx_slots_g")),
    .const (.n (val% «main» "s31#0")) (word 1 0), .add (.n (val% «main» "s31#1")) (.n (val% «main» "s31#0")) (.n (val% «main» "meta[1]")), .const (.n (val% «main» "s31#2")) (word 1 0),
    .const (.n (val% «main» "s32#0")) (word 1 0), .add (.n (val% «main» "s32#1")) (.n (val% «main» "s32#0")) (.n (val% «main» "meta[4]")), .const (.n (val% «main» "s32#2")) (word 1 0),
    .const (.n (val% «main» "s39#0")) (word 1 0), .add (.n (val% «main» "s39#1")) (.n (val% «main» "s39#0")) (.n (val% «main» "meta[2]")), .const (.n (val% «main» "s39#2")) (word 1 0),
    .const (.n (val% «main» "s40#0")) (word 1 0), .add (.n (val% «main» "s40#1")) (.n (val% «main» "s40#0")) (.n (val% «main» "meta[5]")), .const (.n (val% «main» "s40#2")) (word 1 0),
    .const (.n (val% «main» "da_digests~0")) (word 2 0), .mul (.n (val% «main» "da_digests~1")) (.n (val% «main» "meta[6]")) (.n (val% «main» "da_digests~0")), .mul (.n (val% «main» "da_digests~2")) (.n (val% «main» "da_digests~1")) (.n (val% «main» "da_digests~1")),
    .mul (.n (val% «main» "own_da~0")) (.n (val% «main» "meta[6]")) (.n (val% «main» "meta[6]")), .mul (.n (val% «main» "own_da")) (.n (val% «main» "da_digests")) (.n (val% «main» "own_da~0")),
    .const (.n (val% «main» "s43#0")) (word 2 0), .add (.n (val% «main» "s43#1")) (.n (val% «main» "meta[7]")) (.n (val% «main» "s43#0")), .const (.n (val% «main» "s43.t.s1#1[1]")) (word 0 0),
    .mul (.n (val% «main» "child_pi~0")) (.n (val% «main» "meta[6]")) (.n (val% «main» "meta[6]")), .mul (.n (val% «main» "child_fresh~0")) (.n (val% «main» "meta[6]")) (.n (val% «main» "meta[6]")), .mul (.n (val% «main» "child_fresh~1")) (.n (val% «main» "child_fresh~0")) (.n (val% «main» "meta[6]")),
    .mul (.n (val% «main» "child_fresh~2")) (.n (val% «main» "child_fresh~1")) (.n (val% «main» "child_fresh~1")), .mul (.n (val% «main» "child_fresh~3")) (.n (val% «main» "child_fresh~2")) (.n (val% «main» "child_fresh~2")),
    .mul (.n (val% «main» "child_fresh~4")) (.n (val% «main» "child_fresh~3")) (.n (val% «main» "child_fresh~3")), .mul (.n (val% «main» "child_carried~0")) (.n (val% «main» "meta[6]")) (.n (val% «main» "meta[6]")), .mul (.n (val% «main» "child_carried~1")) (.n (val% «main» "child_carried~0")) (.n (val% «main» "meta[6]")),
    .mul (.n (val% «main» "child_carried~2")) (.n (val% «main» "child_carried~1")) (.n (val% «main» "child_carried~1")), .mul (.n (val% «main» "child_carried~3")) (.n (val% «main» "child_carried~2")) (.n (val% «main» "child_carried~2")),
    .mul (.n (val% «main» "child_carried~4")) (.n (val% «main» "child_carried~3")) (.n (val% «main» "child_carried~3")), .const (.n (val% «main» "written~0")) (word 2 0), .mul (.n (val% «main» "written~1")) (.n (val% «main» "meta[6]")) (.n (val% «main» "written~0")),
    .mul (.n (val% «main» "s48#0")) (.n (val% «main» "meta[2]")) (.n (val% «main» "meta[5]")), .const (.n (val% «main» "s49#0")) (word 1 0), .add (.n (val% «main» "s49#1")) (.n (val% «main» "s49#0")) (.n (val% «main» "meta[6]")),
    .const (.n (val% «main» "s49#2")) (word 1 0), .mul (.n (val% «main» "s50#0")) (.n (val% «main» "written")) (.n (val% «main» "meta[6]")),
    .add (.n (val% «main» "s53#0")) (.n (val% «main» "da_pick")) (.n (val% «main» "meta[6]")), .const (.n (val% «main» "s53#1")) (word 1 0), .add (.n (val% «main» "s53#2")) (.n (val% «main» "meta[7]")) (.n (val% «main» "s53#1")),
    .mul (.n (val% «main» "s53#3")) (.n (val% «main» "s53#0")) (.n (val% «main» "s53#2")), .const (.n (val% «main» "s53#4")) (word 0 0),
    .mul (.n (val% «main» "da~0")) (.n (val% «main» "da_pick")) (.n (val% «main» "da_pick")), .mul (.n (val% «main» "da")) (.n (val% «main» "da_digests")) (.n (val% «main» "da~0")),
    .const (.n (val% «main» "s56#0")) (word 1 0), .add (.n (val% «main» "s56#1")) (.n (val% «main» "meta[6]")) (.n (val% «main» "s56#0")),
    .const (.n (val% «main» "s56.e.s0#0")) (word 133823759239872512 0), .mul (.n (val% «main» "s56.e.s0#1")) (.n (val% «main» "g_squares")) (.n (val% «main» "s56.e.s0#0")),
    .const (.n (val% «main» "s59#0")) (word 1 0), .const (.n (val% «main» "s60#0")) (word 1 0), .const (.n (val% «main» "s60#1")) (word 2 0),
    .mul (.n (val% «main» "s60#2")) (.n (val% «main» "s60#0")) (.n (val% «main» "s60#1")),
    .const (.n (val% «main» "s16#0")) (word 65536 0), .const (.n (val% «main» "s17#0")) (word 2 0),
    .load (.n (val% «main» "s50#1")) (.n (val% «main» "s50#0")) 0, .load (.n (val% «main» "own_0~2")) (.n (val% «main» "da")) 0, .load (.n (val% «main» "own_0~3")) (.n (val% «main» "da")) 1,
    .load (.n (val% «main» "s59#1")) (.n (val% «main» "s59#0")) 0, .load (.n (val% «main» "s60#3")) (.n (val% «main» "s60#2")) 0] ++
  (List.range 51).map fun j => .const (.n (304 + j)) (word (lxTagVals.getD j 0) 0)

end
end LeanVM.Guest.B1.Main
