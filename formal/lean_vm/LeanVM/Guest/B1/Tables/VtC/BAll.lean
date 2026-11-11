/-
  LeanVM.Guest.B1.Tables.VtC.BAll

  `verify_tables`' statements `765 ..< 2593` (the bus sides and the bytecode share, G:2413-2571)
  hold on the honest valuation.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BSels
public import LeanVM.Guest.B1.Tables.VtC.BGlueGen
public import LeanVM.Guest.B1.Tables.VtC.BTwin
public import LeanVM.Guest.B1.Tables.VtC.BBc
public import LeanVM.Guest.B1.Tables.VtC.InBuf
public import LeanVM.Guest.B1.Tables.Vt.Fw
public import LeanVM.Guest.B1.Selectors.IndexMleComplete

/-!
# The bus sides (G:2413-2571)

`VtBIn`: the honest data: the bus point, the memory's log-size, the tables' row counts (heights
`vtHt rows`), the sixteen slot weights at `fp_w`, the four framework words and the bytecode share's
ten at the cursor, the three GKR leaf values. `VtBHyp`: what the range needs of the memory, the
oracle and the earlier statements (`vtS_complete` gives the latter), the slot sumcheck's honest
point at `bc_point` and its last claim accepted.

`vtB_complete`: every statement of `765 ..< 2593` holds; the block selectors, the framework
words, the share's words and the three bus totals are the honest ones (`vtAcc0/1/2`, as
`vt_asm_totals`); every load reads inside the buffers `vtBufsB`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel)

@[expose] public section

/-- `block_index_mle`'s honest words: the index MLE of the memory's and the bytecode's prefixes
at the push side's memory and bytecode blocks. -/
def vtIdxBufW (point : List E) (lm : ℕ) : List E := (List.range 153).map fun b ↦
  if b = 1 then indexMle (point.take lm) else if b = 2 then indexMle (point.take 19) else 0

/-- The honest data of the bus sides. -/
structure VtBIn where
  /-- The bus point at `zeta`. -/
  point : List E
  /-- The memory's log-size. -/
  lm : ℕ
  /-- The tables' row counts. -/
  rows : List ℕ
  /-- The sixteen slot weights at `fp_w`. -/
  weights : List E
  /-- The four framework words at the cursor: the memory's two values, the final memory and
  bytecode counts. -/
  xs : List E
  /-- The bytecode share's ten words after them: the share, the slot sumcheck's six words, the
  value. -/
  w : List E
  /-- The three GKR leaf values at `gkr_leaves`. -/
  leaves : List E
  /-- The guest's bytecode. -/
  bc : List K

/-- The buffers the bus sides read and write: the cursor (the framework's and the share's
fourteen words), `fp_w`, `claim_pool`, `block_index_mle`, `gkr_leaves`, `bc_point`. -/
def vtBufsBIdx : List (ℕ × ℕ) := [(5, 14), (13, 16), (15, 4), (777, 153), (17, 3), (19, 4)]

/-- The buffers, as pointers and lengths. -/
def vtBufsB (σ : Val) : List (E × ℕ) := vtBufsBIdx.map fun q ↦ (σ (.n q.1), q.2)

/-- **What the bus sides need.** -/
structure VtBHyp (rd : Reader) (wo : ℕ → E) (args : List E) (D : VtBIn) : Prop where
  hl : args.length = 20
  hlow : LowDefB 14 rd
  hml : D.point.length < 33
  hlmμ : D.lm ≤ D.point.length
  h19 : 19 ≤ D.point.length
  hr : D.rows.length = 6
  hτμ : ∀ t < 6, vtHt D.rows t ≤ D.point.length
  hmu : args.getD 9 0 = gen ^ D.point.length
  hz : TbReadsAt rd (args.getD 8 0) D.point
  hwl : D.weights.length = 16
  hW : TbReadsAt rd (args.getD 13 0) D.weights
  hxl : D.xs.length = 4
  hbl : D.w.length = 10
  hcur : TbReadsAt rd (args.getD 5 0) (D.xs ++ D.w)
  hpool : ∀ i < 4, LoadHolds rd (args.getD 15 0) i (D.xs.getD i 0)
  hll : D.leaves.length = 3
  hleaves : TbReadsAt rd (args.getD 17 0) D.leaves
  /-- `bc_point` holds the slot sumcheck's honest point. -/
  hpt : TbReadsAt rd (args.getD 19 0) (vtBcPoint (vtF0 args D.xs) D.w)
  /-- The earlier statements' values (`vtS_complete`). -/
  ekb : ∀ i < 8, vtσ rd wo args (.n (25 + i)) = gen ^ ([0, D.lm] ++ vtTauList (vtHt D.rows)).getD i 0
  eoP : ∀ x < 54, vtσ rd wo args (.n (vtBoffV x)) =
    gen ^ (stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD x 0
  eoC : ∀ x < 45, vtσ rd wo args (.n (vtBoffV (108 + x))) =
    gen ^ (stackOffsets (vtSizesC (vtHt D.rows))).1.getD x 0
  eSh : ∀ t < 6, vtσ rd wo args (.n (vtShLen t)) = gen ^ (D.point.length - vtHt D.rows t)
  e664 : vtσ rd wo args (.n 664) = wo 664
  e699 : vtσ rd wo args (.n 699) = wo 699
  e701 : vtσ rd wo args (.n 701) = wo 701
  e702 : vtσ rd wo args (.n 702) = wo 702
  hpw : ∀ t < 6, vtσ rd wo args (.n (vtPadV t)) =
    paddingWeight (D.point.take (vtHt D.rows t)) (vtRw D.rows t)
  /-- The own buffers' words. -/
  hidxc : TbReadsAt rd (wo 664) vtIdxcW
  hz1 : TbReadsAt rd (wo 699) (D.point.map (1 + ·))
  hrun : ∀ t < 6, RunTables rd (wo 701 * gen ^ (288 * t)) (wo 702 * gen ^ (144 * t))
    (D.point.length - vtHt D.rows t) (D.point.drop (vtHt D.rows t))
    ((D.point.map (1 + ·)).drop (vtHt D.rows t))
    ((gSquaresList.drop (vtHt D.rows t)).take (D.point.length - vtHt D.rows t))
  hidxB : TbReadsAt rd (wo 777) (vtIdxBufW D.point D.lm)
  /-- Each side's blocks fit in the bus cube. -/
  hfitP : ((vtSizesP D.lm (vtHt D.rows)).map (2 ^ ·)).sum ≤ 2 ^ D.point.length
  hfitC : ((vtSizesC (vtHt D.rows)).map (2 ^ ·)).sum ≤ 2 ^ D.point.length
  /-- The offsets' bits and digits at the hinted buffers. -/
  hbitsF : ∀ b < 3, TbReadsAt rd (wo (vtFwW b + 6))
    (offBits ((stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD b 0))
  hdigP : ∀ i < 51, TbReadsAt rd (wo (vtPushSel.getD i default).2.2.1)
    (offDigits ((stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD (3 + i) 0)
      (vtHt D.rows (vtPushSel.getD i default).2.2.2.1))
  hdigC : ∀ i < 45, TbReadsAt rd (wo (vtCountSel.getD i default).2.2.1)
    (offDigits ((stackOffsets (vtSizesC (vtHt D.rows))).1.getD i 0)
      (vtHt D.rows (vtCountSel.getD i default).2.2.2.1))
  /-- The callees' returns. -/
  hwF : ∀ b < 3, wo (vtFwW b + 10) =
      blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length b D.point ∧
    wo (vtFwW b + 11) = gen ^ (stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD b 0
  hwP : ∀ i < 51, wo (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1) =
      blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length (3 + i) D.point ∧
    wo (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1 + 1) =
      gen ^ (stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD (3 + i) 0
  hwC : ∀ i < 45, wo (vtSelE (vtCountSel.getD i default).2.2.1
      (vtCountSel.getD i default).2.2.2.1) =
      blockSel (vtSizesC (vtHt D.rows)) D.point.length i D.point ∧
    wo (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1 + 1) =
      gen ^ (stackOffsets (vtSizesC (vtHt D.rows))).1.getD i 0
  hwI : wo 809 = indexMle (D.point.take D.lm) ∧ wo 837 = indexMle (D.point.take 19)
  /-- The tail rounds' returns: each round's capacity, cursor, claim and challenge. -/
  hw1 : (List.range 8).map (fun i ↦ wo (1876 + i)) = (vtBcR1 (vtF0 args D.xs) D.w).1 ++
    [args.getD 5 0 * gen ^ 7 * gen ^ 2, (vtBcR1 (vtF0 args D.xs) D.w).2.1,
      (vtBcR1 (vtF0 args D.xs) D.w).2.2]
  hw2 : (List.range 8).map (fun i ↦ wo (1884 + i)) = (vtBcR2 (vtF0 args D.xs) D.w).1 ++
    [args.getD 5 0 * gen ^ 7 * gen ^ 2 * gen ^ 2, (vtBcR2 (vtF0 args D.xs) D.w).2.1,
      (vtBcR2 (vtF0 args D.xs) D.w).2.2]
  hw3 : (List.range 8).map (fun i ↦ wo (1892 + i)) = (vtBcR3 (vtF0 args D.xs) D.w).1 ++
    [args.getD 5 0 * gen ^ 7 * gen ^ 2 * gen ^ 2 * gen ^ 2, (vtBcR3 (vtF0 args D.xs) D.w).2.1,
      (vtBcR3 (vtF0 args D.xs) D.w).2.2]
  /-- The slot sumcheck's last claim is accepted (`bytecodeShare`'s check). -/
  hacc : (vtBcR3 (vtF0 args D.xs) D.w).2.1 =
    dot (eqKernel (vtBcPoint (vtF0 args D.xs) D.w)) D.weights * D.w.getD 9 0
  /-- The bytecode's size. -/
  hbc : D.bc.length = 2 ^ 23

theorem vtB_loads_check : ((vtPre.drop 765).take 1828).all (fun s ↦ match s with
    | .atom (.load _ p off) => decide (p = .n 1897) ||
        vtBufsBIdx.any fun q ↦ decide (p = .n q.1) && decide (off < q.2)
    | _ => true) = true := by simp only [vtPre_drop]; decide +kernel

theorem vtB_load1897 : ∀ d off, Stmt.atom (.load d (.n 1897) off) ∈ (vtPre.drop 765).take 1828 →
    off = 0 := by
  have h : ((vtPre.drop 765).take 1828).all (fun s ↦ match s with
      | .atom (.load _ p off) => !decide (p = .n 1897) || decide (off = 0)
      | _ => true) = true := by simp only [vtPre_drop]; decide +kernel
  intro d off hm
  have := List.all_eq_true.mp h _ hm
  simpa using this

/-- **Every load of the bus sides reads inside `vtBufsB`**, the value's read through the cursor
after the tail rounds (`g^13` words on) included. -/
theorem vtB_loadsInBuf (σ : Val) (h1897 : σ (.n 1897) = σ (.n 5) * gen ^ 13) :
    LoadsInBuf σ (vtBufsB σ) ((vtPre.drop 765).take 1828) := by
  intro d p off hm
  have := List.all_eq_true.mp vtB_loads_check _ hm
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at this
  rcases this with rfl | ⟨q, hq, rfl, hoff⟩
  · have h0 := vtB_load1897 d off hm
    subst h0
    exact ⟨(σ (.n 5), 14), by simp [vtBufsB, vtBufsBIdx], 13, h1897, by norm_num⟩
  · exact vt_inBuf_direct (List.mem_map.mpr ⟨q, hq, rfl⟩) hoff

end
end LeanVM.Guest.B1.Tables
