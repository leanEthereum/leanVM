/-
  LeanVM.Guest.B1.Main.MainWalkChk

  `main`'s path, read off its blocks by kernel evaluation: its `HeapBuf`s, frames, loads.
-/

module

public import LeanVM.Guest.B1.Main.MainCChk
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Data.NameStrings

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
theorem mBlocks_kind : mPre.all (mKind [40, 43, 356, 359]) = true ∧ mDa.all (mKind []) = true ∧
    mDaZ.all (mKind []) = true ∧ mMid.all (mKind [401]) = true ∧ mLeaf.all (mKind []) = true ∧
    mAgg.all (mKind []) = true ∧ mPost.all (mKind []) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_allocs : mPre.filterMap Main.Stmt.allocSz = [(.n 31, .inr (.n 30)),
      (.n 34, .inr (.n 33)), (.n 45, .inr (.n 24)), (.n 47, .inl 256),
      (.n 364, .inr (.n 363))] ∧ mDa.filterMap Main.Stmt.allocSz = [] ∧
    mDaZ.filterMap Main.Stmt.allocSz = [] ∧
    mMid.filterMap Main.Stmt.allocSz = [(.n 383, .inr (.n 382)), (.n 389, .inr (.n 388)),
      (.n 395, .inr (.n 394)), (.n 398, .inr (.n 397)), (.n 416, .inl 24)] ∧
    mLeaf.filterMap Main.Stmt.allocSz = [] ∧ mAgg.filterMap Main.Stmt.allocSz = [] ∧
    mPost.filterMap Main.Stmt.allocSz = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_addrs : mPre.filterMap Main.Stmt.addrS = [] ∧ mDa.filterMap Main.Stmt.addrS = [] ∧
    mDaZ.filterMap Main.Stmt.addrS = [] ∧ mMid.filterMap Main.Stmt.addrS = [] ∧
    mLeaf.filterMap Main.Stmt.addrS = [] ∧ mAgg.filterMap Main.Stmt.addrS = [] ∧
    mPost.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPre_calls : mPre.filterMap Main.Stmt.callS =
    [(none, "exponent_tables", [], [.n 28]),
      (none, "claim_list_digest", [.n 31, .n 0], [.n 35, .n 36]),
      (none, "claim_list_digest", [.n 34, .n 3], [.n 37, .n 38]),
      (some (.n 40), name% «main_loop0», [.n 41, .n 1, .n 31, .n 0], []),
      (some (.n 43), name% «main_loop1», [.n 44, .n 4, .n 34, .n 3], []),
      (some (.n 356), name% «main_loop2», [.n 357, .n 2, .n 22, .n 45, .n 31] ++ lxTagsV, []),
      (some (.n 359), name% «main_loop3», [.n 360, .n 5, .n 23, .n 46, .n 2, .n 34, .n 47],
          [])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mDa_calls : mDa.filterMap Main.Stmt.callS =
    [(none, "da_verify", [.n 28], [.n 369, .n 370, .n 371])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mDaZ_calls : mDaZ.filterMap Main.Stmt.callS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mMid_calls : mMid.filterMap Main.Stmt.callS =
    [(some (.n 401), name% «main_loop4», [.n 402, .n 6, .n 398, .n 31, .n 45, .n 22, .n 34, .n 46,
        .n 23,
      .n 395, .n 364, .n 26, .n 27, .n 383, .n 28, .n 389], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mLeaf_calls : mLeaf.filterMap Main.Stmt.callS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mAgg_calls : mAgg.filterMap Main.Stmt.callS =
    [(none, "aggregate_claims", [.n 6, .n 383, .n 389, .n 395, .n 416, .n 444], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPost_calls : mPost.filterMap Main.Stmt.callS =
    [(none, "statement_digest", [.n 26, .n 27, .n 35, .n 36, .n 37, .n 38, .n 445, .n 446, .n 416],
      [.n 447, .n 448])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_loads : mPre.filterMap B1.Stmt.loadS = (List.range 256).map (fun v => (.n 47, v)) ∧
    mDa.filterMap B1.Stmt.loadS = [(.n 366, 0), (.n 366, 1)] ∧
    mDaZ.filterMap B1.Stmt.loadS = [(.n 366, 0), (.n 366, 1)] ∧
    mMid.filterMap B1.Stmt.loadS = [(.n 398, 0), (.n 403, 0)] ∧
    mLeaf.filterMap B1.Stmt.loadS = (List.range 24).map (fun k => (.n 416, k)) ∧
    mAgg.filterMap B1.Stmt.loadS = [] ∧
    mPost.filterMap B1.Stmt.loadS = [(.n 415, 0), (.n 415, 1), (.n 449, 0), (.n 453, 0)] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mAgg_atoms : atomsIn mAgg =
    [.const (.n 443) (word 133823759239872512 0), .mul (.n 444) (.n 28) (.n 443)] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem main_loop : coreProgram.loop "main" = false := by
  rw [Program.loop_of_find? find_main]; decide +kernel

end
end LeanVM.Guest.B1.Main
