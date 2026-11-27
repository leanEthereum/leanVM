/-
  LeanVM.Guest.B1.Main.MainCChk

  `main`'s body as one evaluated block (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.B1.Fwd.Canon
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main»
import LeanVM.Guest.StmtsAppend

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
noncomputable def mFlat : List Stmt := mPre ⧺ mDa ⧺ mDaZ ⧺ mMid ⧺ mLeaf ⧺ mAgg ⧺ mPost

/-- The evaluated block: `mFlat` itself (`main` hints no inverse). -/
noncomputable def mFlatE : List Stmt := mFlat

/-- `main`'s stores: the byte table, the own DA digest (both branches), the first running count,
the leaf's deferred claim. -/
def mStoresL : List Atom :=
  (List.range 256).map (fun v => .load (.n ((val% «main» "s43.u0.s0#0") + v)) (.n (val% «main» "byte_bits")) v) ++
    [.load (.n (val% «main» "s50.t.s1#0")) (.n (val% «main» "own_da")) 0, .load (.n (val% «main» "s50.t.s1#0[1]")) (.n (val% «main» "own_da")) 1, .load (.n (val% «main» "s50.e.s0#0")) (.n (val% «main» "own_da")) 0,
      .load (.n (val% «main» "s50.e.s1#0")) (.n (val% «main» "own_da")) 1, .load (.n (val% «main» "s55#0")) (.n (val% «main» "written")) 0] ++
    (List.range 23).map (fun k => .load (.n ((val% «main» "s63.t.s1.u0.s0#0") + k)) (.n (val% «main» "defer_stmt")) k) ++ [.load (.n (val% «main» "leaf_value")) (.n (val% «main» "defer_stmt")) 23]

/-- `main`'s loads, by their words' numbers: the five reads, then the stores. -/
def mLoadOk (d p o : ℕ) : Bool :=
  decide ((d, p, o) ∈ [(val% «main» "s57#1", val% «main» "s57#0", 0), (val% «main» "own_0~2", val% «main» "da", 0),
    (val% «main» "own_0~3", val% «main» "da", 1), (val% «main» "s66#1", val% «main» "s66#0", 0),
    (val% «main» "s67#1", val% «main» "s67#0", 0)]) ||
  (decide (p = val% «main» "byte_bits") && decide (d = (val% «main» "s43.u0.s0#0") + o) && decide (o < 256)) ||
  decide ((d, p, o) ∈ [(val% «main» "s50.t.s1#0", val% «main» "own_da", 0), (val% «main» "s50.t.s1#0[1]", val% «main» "own_da", 1),
    (val% «main» "s50.e.s0#0", val% «main» "own_da", 0), (val% «main» "s50.e.s1#0", val% «main» "own_da", 1),
    (val% «main» "s55#0", val% «main» "written", 0)]) ||
  (decide (p = val% «main» "defer_stmt") && (decide (o < 23 ∧ d = (val% «main» "s63.t.s1.u0.s0#0") + o) ||
    decide (o = 23 ∧ d = val% «main» "leaf_value")))

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
  | .assertEq x y => decide ((x, y) ∈ [(V.n (val% «main» "s57#1"), V.n (val% «main» "n_total_g")), (.n (val% «main» "s60#3"), .n (val% «main» "s60#4")), (.n (val% «main» "s66#1"), .n (val% «main» "own_0")),
      (.n (val% «main» "s67#1"), .n (val% «main» "own_1"))])
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
    .call "exponent_tables" [] [.n (val% «main» "g_squares")], .atom (.hint (.allocDyn (.n (val% «main» "lx_table")) (.n (val% «main» "lx_table_size")))),
    .atom (.hint (.allocDyn (.n (val% «main» "lean_sphincs_table")) (.n (val% «main» "lean_sphincs_table_size")))),
    .call "claim_list_digest" [.n (val% «main» "lx_table"), .n (val% «main» "meta[0]")] [.n (val% «main» "xd_0"), .n (val% «main» "xd_1")],
    .call "claim_list_digest" [.n (val% «main» "lean_sphincs_table"), .n (val% «main» "meta[3]")] [.n (val% «main» "sd_0"), .n (val% «main» "sd_1")],
    .atom (.hint (.allocDyn (.n (val% «main» "cover")) (.n (val% «main» "n_total_g")))), .atom (.hint (.alloc (.n (val% «main» "byte_bits")) 256)),
    .atom (.hint (.allocDyn (.n (val% «main» "da_digests")) (.n (val% «main» "da_digests_size")))),
    .call "da_verify" [.n (val% «main» "byte_bits")] [.n (val% «main» "root_0"), .n (val% «main» "root_1"), .n (val% «main» "z")],
    .atom (.hint (.allocDyn (.n (val% «main» "child_pi")) (.n (val% «main» "child_pi_size")))), .atom (.hint (.allocDyn (.n (val% «main» "child_fresh")) (.n (val% «main» "child_fresh_size")))),
    .atom (.hint (.allocDyn (.n (val% «main» "child_carried")) (.n (val% «main» "child_carried_size")))), .atom (.hint (.allocDyn (.n (val% «main» "written")) (.n (val% «main» "written~1")))),
    .atom (.hint (.witness "da_pick" (.stack [.n (val% «main» "da_pick")]))),
    .atom (.hint (.alloc (.n (val% «main» "defer_stmt")) 24)), .atom (.hint (.witness "leaf_defer" (.stack [.n (val% «main» "leaf_value")]))),
    .call "statement_digest" [.n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "xd_0"), .n (val% «main» "xd_1"), .n (val% «main» "sd_0"), .n (val% «main» "sd_1"), .n (val% «main» "own_0~2"), .n (val% «main» "own_0~3"), .n (val% «main» "defer_stmt")]
      [.n (val% «main» "own_0"), .n (val% «main» "own_1")]]

/-- The atoms defining `main`'s words the proof reads. -/
def mDefAtoms : List Atom :=
  [.mul (.n (val% «main» "lx_slots_g")) (.n (val% «main» "meta[0]")) (.n (val% «main» "meta[1]")), .mul (.n (val% «main» "lean_sphincs_slots_g")) (.n (val% «main» "meta[3]")) (.n (val% «main» "meta[4]")), .mul (.n (val% «main» "n_total_g")) (.n (val% «main» "lx_slots_g")) (.n (val% «main» "lean_sphincs_slots_g")),
    .mul (.n (val% «main» "lx_table_size~0")) (.n (val% «main» "lx_slots_g")) (.n (val% «main» "lx_slots_g")), .mul (.n (val% «main» "lx_table_size")) (.n (val% «main» "lx_table_size~0")) (.n (val% «main» "lx_table_size~0")),
    .mul (.n (val% «main» "lean_sphincs_table_size~0")) (.n (val% «main» "lean_sphincs_slots_g")) (.n (val% «main» "lean_sphincs_slots_g")), .mul (.n (val% «main» "lean_sphincs_table_size")) (.n (val% «main» "lean_sphincs_table_size~0")) (.n (val% «main» "lean_sphincs_table_size~0")), .mul (.n (val% «main» "sp_cover")) (.n (val% «main» "cover")) (.n (val% «main» "lx_slots_g")),
    .const (.n (val% «main» "s38#0")) (word 1 0), .add (.n (val% «main» "s38#1")) (.n (val% «main» "s38#0")) (.n (val% «main» "meta[1]")), .const (.n (val% «main» "s38#2")) (word 1 0),
    .const (.n (val% «main» "s39#0")) (word 1 0), .add (.n (val% «main» "s39#1")) (.n (val% «main» "s39#0")) (.n (val% «main» "meta[4]")), .const (.n (val% «main» "s39#2")) (word 1 0),
    .const (.n (val% «main» "s46#0")) (word 1 0), .add (.n (val% «main» "s46#1")) (.n (val% «main» "s46#0")) (.n (val% «main» "meta[2]")), .const (.n (val% «main» "s46#2")) (word 1 0),
    .const (.n (val% «main» "s47#0")) (word 1 0), .add (.n (val% «main» "s47#1")) (.n (val% «main» "s47#0")) (.n (val% «main» "meta[5]")), .const (.n (val% «main» "s47#2")) (word 1 0),
    .const (.n (val% «main» "da_digests_size~0")) (word 2 0), .mul (.n (val% «main» "da_digests_size~1")) (.n (val% «main» "meta[6]")) (.n (val% «main» "da_digests_size~0")), .mul (.n (val% «main» "da_digests_size")) (.n (val% «main» "da_digests_size~1")) (.n (val% «main» "da_digests_size~1")),
    .mul (.n (val% «main» "own_da~0")) (.n (val% «main» "meta[6]")) (.n (val% «main» "meta[6]")), .mul (.n (val% «main» "own_da")) (.n (val% «main» "da_digests")) (.n (val% «main» "own_da~0")),
    .const (.n (val% «main» "s50#0")) (word 2 0), .add (.n (val% «main» "s50#1")) (.n (val% «main» "meta[7]")) (.n (val% «main» "s50#0")), .const (.n (val% «main» "s50.t.s1#1[1]")) (word 0 0),
    .mul (.n (val% «main» "child_pi_size")) (.n (val% «main» "meta[6]")) (.n (val% «main» "meta[6]")), .mul (.n (val% «main» "child_fresh_size~0")) (.n (val% «main» "meta[6]")) (.n (val% «main» "meta[6]")), .mul (.n (val% «main» "child_fresh_size~1")) (.n (val% «main» "child_fresh_size~0")) (.n (val% «main» "meta[6]")),
    .mul (.n (val% «main» "child_fresh_size~2")) (.n (val% «main» "child_fresh_size~1")) (.n (val% «main» "child_fresh_size~1")), .mul (.n (val% «main» "child_fresh_size~3")) (.n (val% «main» "child_fresh_size~2")) (.n (val% «main» "child_fresh_size~2")),
    .mul (.n (val% «main» "child_fresh_size")) (.n (val% «main» "child_fresh_size~3")) (.n (val% «main» "child_fresh_size~3")), .mul (.n (val% «main» "child_carried_size~0")) (.n (val% «main» "meta[6]")) (.n (val% «main» "meta[6]")), .mul (.n (val% «main» "child_carried_size~1")) (.n (val% «main» "child_carried_size~0")) (.n (val% «main» "meta[6]")),
    .mul (.n (val% «main» "child_carried_size~2")) (.n (val% «main» "child_carried_size~1")) (.n (val% «main» "child_carried_size~1")), .mul (.n (val% «main» "child_carried_size~3")) (.n (val% «main» "child_carried_size~2")) (.n (val% «main» "child_carried_size~2")),
    .mul (.n (val% «main» "child_carried_size")) (.n (val% «main» "child_carried_size~3")) (.n (val% «main» "child_carried_size~3")), .const (.n (val% «main» "written~0")) (word 2 0), .mul (.n (val% «main» "written~1")) (.n (val% «main» "meta[6]")) (.n (val% «main» "written~0")),
    .mul (.n (val% «main» "s55#0")) (.n (val% «main» "meta[2]")) (.n (val% «main» "meta[5]")), .const (.n (val% «main» "s56#0")) (word 1 0), .add (.n (val% «main» "s56#1")) (.n (val% «main» "s56#0")) (.n (val% «main» "meta[6]")),
    .const (.n (val% «main» "s56#2")) (word 1 0), .mul (.n (val% «main» "s57#0")) (.n (val% «main» "written")) (.n (val% «main» "meta[6]")),
    .add (.n (val% «main» "s60#0")) (.n (val% «main» "da_pick")) (.n (val% «main» "meta[6]")), .const (.n (val% «main» "s60#1")) (word 1 0), .add (.n (val% «main» "s60#2")) (.n (val% «main» "meta[7]")) (.n (val% «main» "s60#1")),
    .mul (.n (val% «main» "s60#3")) (.n (val% «main» "s60#0")) (.n (val% «main» "s60#2")), .const (.n (val% «main» "s60#4")) (word 0 0),
    .mul (.n (val% «main» "da~0")) (.n (val% «main» "da_pick")) (.n (val% «main» "da_pick")), .mul (.n (val% «main» "da")) (.n (val% «main» "da_digests")) (.n (val% «main» "da~0")),
    .const (.n (val% «main» "s63#0")) (word 1 0), .add (.n (val% «main» "s63#1")) (.n (val% «main» "meta[6]")) (.n (val% «main» "s63#0")),
    .const (.n (val% «main» "s63.e.s0#0")) (word 133823759239872512 0), .mul (.n (val% «main» "s63.e.s0#1")) (.n (val% «main» "g_squares")) (.n (val% «main» "s63.e.s0#0")),
    .const (.n (val% «main» "s66#0")) (word 1 0), .const (.n (val% «main» "s67#0")) (word 2 0),
    .const (.n (val% «main» "s16#0")) (word 65536 0), .const (.n (val% «main» "s17#0")) (word 2 0),
    .load (.n (val% «main» "s57#1")) (.n (val% «main» "s57#0")) 0, .load (.n (val% «main» "own_0~2")) (.n (val% «main» "da")) 0, .load (.n (val% «main» "own_0~3")) (.n (val% «main» "da")) 1,
    .load (.n (val% «main» "s66#1")) (.n (val% «main» "s66#0")) 0, .load (.n (val% «main» "s67#1")) (.n (val% «main» "s67#0")) 0] ++
  (List.range 51).map fun j => .const (.n ((val% «main» "lx_tags[0]") + j)) (word (lxTagVals.getD j 0) 0)

end
end LeanVM.Guest.B1.Main
