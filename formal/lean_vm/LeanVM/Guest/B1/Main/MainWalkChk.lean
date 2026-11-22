/-
  LeanVM.Guest.B1.Main.MainWalkChk

  `main`'s path, read off its blocks by kernel evaluation: its `HeapBuf`s, frames, loads.
-/

module

public import LeanVM.Guest.B1.Main.MainCChk
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main»

/-!
# `main`'s path, checked

Every block of `main`'s body is straight (atoms, calls, conditional calls); the conditional calls
are the guarded loops; the blocks' `HeapBuf` hints, frames and loads are the listed ones.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Digest

@[expose] public section

/-- A statement of `main`'s blocks: an atom, a call, or a guarded loop on one of `cs`. -/
def mKind (cs : List ℕ) : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf c _ _ => decide (c = .n c.idx) && decide (c.idx ∈ cs)
  | _ => false

set_option maxRecDepth 100000 in
theorem mBlocks_straight : mPre.all Main.Stmt.straight = true ∧ mDa.all Main.Stmt.straight = true ∧
    mDaZ.all Main.Stmt.straight = true ∧ mMid.all Main.Stmt.straight = true ∧
    mLeaf.all Main.Stmt.straight = true ∧ mAgg.all Main.Stmt.straight = true ∧
    mPost.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_kind : mPre.all (mKind [54, 57, 370, 373]) = true ∧ mDa.all (mKind []) = true ∧
    mDaZ.all (mKind []) = true ∧ mMid.all (mKind [401]) = true ∧ mLeaf.all (mKind []) = true ∧
    mAgg.all (mKind []) = true ∧ mPost.all (mKind []) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_allocs : mPre.filterMap Main.Stmt.allocSz = [(.n (val% «main» "lx_table"), .inr (.n (val% «main» "lx_table_size"))),
      (.n (val% «main» "lean_sphincs_table"), .inr (.n (val% «main» "lean_sphincs_table_size"))), (.n (val% «main» "cover"), .inr (.n (val% «main» "n_total_g"))), (.n (val% «main» "byte_bits"), .inl 256),
      (.n (val% «main» "da_digests"), .inr (.n (val% «main» "da_digests_size")))] ∧ mDa.filterMap Main.Stmt.allocSz = [] ∧
    mDaZ.filterMap Main.Stmt.allocSz = [] ∧
    mMid.filterMap Main.Stmt.allocSz = [(.n (val% «main» "child_pi"), .inr (.n (val% «main» "child_pi_size"))), (.n (val% «main» "child_fresh"), .inr (.n (val% «main» "child_fresh_size"))),
      (.n (val% «main» "child_carried"), .inr (.n (val% «main» "child_carried_size"))), (.n (val% «main» "written"), .inr (.n (val% «main» "written~1"))), (.n (val% «main» "defer_stmt"), .inl 24)] ∧
    mLeaf.filterMap Main.Stmt.allocSz = [] ∧ mAgg.filterMap Main.Stmt.allocSz = [] ∧
    mPost.filterMap Main.Stmt.allocSz = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_addrs : mPre.filterMap Main.Stmt.addrS = [] ∧ mDa.filterMap Main.Stmt.addrS = [] ∧
    mDaZ.filterMap Main.Stmt.addrS = [] ∧ mMid.filterMap Main.Stmt.addrS = [] ∧
    mLeaf.filterMap Main.Stmt.addrS = [] ∧ mAgg.filterMap Main.Stmt.addrS = [] ∧
    mPost.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPre_calls : mPre.filterMap Main.Stmt.callS =
    [(none, "exponent_tables", [], [.n (val% «main» "g_squares")]),
      (none, "claim_list_digest", [.n (val% «main» "lx_table"), .n (val% «main» "meta[0]")], [.n (val% «main» "xd_0"), .n (val% «main» "xd_1")]),
      (none, "claim_list_digest", [.n (val% «main» "lean_sphincs_table"), .n (val% «main» "meta[3]")], [.n (val% «main» "sd_0"), .n (val% «main» "sd_1")]),
      (some (.n (val% «main» "s38#1")), name% «main_loop0», [.n (val% «main» "s38#2"), .n (val% «main» "meta[1]"), .n (val% «main» "lx_table"), .n (val% «main» "meta[0]")], []),
      (some (.n (val% «main» "s39#1")), name% «main_loop1», [.n (val% «main» "s39#2"), .n (val% «main» "meta[4]"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "meta[3]")], []),
      (some (.n (val% «main» "s46#1")), name% «main_loop2», [.n (val% «main» "s46#2"), .n (val% «main» "meta[2]"), .n (val% «main» "lx_slots_g"), .n (val% «main» "cover"), .n (val% «main» "lx_table")] ++ lxTagsV, []),
      (some (.n (val% «main» "s47#1")), name% «main_loop3», [.n (val% «main» "s47#2"), .n (val% «main» "meta[5]"), .n (val% «main» "lean_sphincs_slots_g"), .n (val% «main» "sp_cover"), .n (val% «main» "meta[2]"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "byte_bits")],
          [])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mDa_calls : mDa.filterMap Main.Stmt.callS =
    [(none, "da_verify", [.n (val% «main» "byte_bits")], [.n (val% «main» "root_0"), .n (val% «main» "root_1"), .n (val% «main» "z")])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mDaZ_calls : mDaZ.filterMap Main.Stmt.callS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mMid_calls : mMid.filterMap Main.Stmt.callS =
    [(some (.n (val% «main» "s56#1")), name% «main_loop4», [.n (val% «main» "s56#2"), .n (val% «main» "meta[6]"), .n (val% «main» "written"), .n (val% «main» "lx_table"), .n (val% «main» "cover"), .n (val% «main» "lx_slots_g"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "sp_cover"),
        .n (val% «main» "lean_sphincs_slots_g"),
      .n (val% «main» "child_carried"), .n (val% «main» "da_digests"), .n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "child_pi"), .n (val% «main» "g_squares"), .n (val% «main» "child_fresh")], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mLeaf_calls : mLeaf.filterMap Main.Stmt.callS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mAgg_calls : mAgg.filterMap Main.Stmt.callS =
    [(none, "aggregate_claims", [.n (val% «main» "meta[6]"), .n (val% «main» "child_pi"), .n (val% «main» "child_fresh"), .n (val% «main» "child_carried"), .n (val% «main» "defer_stmt"), .n (val% «main» "s63.e.s0#1")], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPost_calls : mPost.filterMap Main.Stmt.callS =
    [(none, "statement_digest", [.n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "xd_0"), .n (val% «main» "xd_1"), .n (val% «main» "sd_0"), .n (val% «main» "sd_1"), .n (val% «main» "own_0~2"), .n (val% «main» "own_0~3"), .n (val% «main» "defer_stmt")],
      [.n (val% «main» "own_0"), .n (val% «main» "own_1")])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_loads : mPre.filterMap B1.Stmt.loadS = (List.range 256).map (fun v => (.n (val% «main» "byte_bits"), v)) ∧
    mDa.filterMap B1.Stmt.loadS = [(.n (val% «main» "own_da"), 0), (.n (val% «main» "own_da"), 1)] ∧
    mDaZ.filterMap B1.Stmt.loadS = [(.n (val% «main» "own_da"), 0), (.n (val% «main» "own_da"), 1)] ∧
    mMid.filterMap B1.Stmt.loadS = [(.n (val% «main» "written"), 0), (.n (val% «main» "s57#0"), 0)] ∧
    mLeaf.filterMap B1.Stmt.loadS = (List.range 24).map (fun k => (.n (val% «main» "defer_stmt"), k)) ∧
    mAgg.filterMap B1.Stmt.loadS = [] ∧
    mPost.filterMap B1.Stmt.loadS = [(.n (val% «main» "da"), 0), (.n (val% «main» "da"), 1), (.n (val% «main» "s66#0"), 0), (.n (val% «main» "s67#2"), 0)] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem main_loop : coreProgram.loop "main" = false := by
  rw [Program.loop_of_find? find_main]; decide +kernel

end
end LeanVM.Guest.B1.Main
