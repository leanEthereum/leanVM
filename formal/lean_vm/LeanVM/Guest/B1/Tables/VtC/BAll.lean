/-
  LeanVM.Guest.B1.Tables.VtC.BAll

  `verify_tables`' statements `769 ..< 2589` (the bus sides, G:2257-2422) hold on the honest
  valuation.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BSels
public import LeanVM.Guest.B1.Tables.VtC.BGlueGen
public import LeanVM.Guest.B1.Tables.VtC.BTwin
public import LeanVM.Guest.B1.Tables.VtC.InBuf
public import LeanVM.Guest.B1.Tables.Vt.Fw
public import LeanVM.Guest.B1.Selectors.IndexMleComplete

/-!
# The bus sides (G:2229-2394)

`VtBIn`: the honest data: the bus point, the memory's log-size, the tables' row counts (heights
`vtHt rows`), the bus challenges `alphas` (weights `eqKernel alphas` at `fp_w`), the five framework
words at the cursor. `VtBHyp`: what the range needs of the memory, the oracle and the earlier
statements (`vtS_complete` gives the latter).

`vtB_complete`: every statement of `769 ..< 2589` holds; the block selectors, the framework
words and the three bus totals are the honest ones (`vtAcc0/1/2`, as `vt_asm_totals`); every
load reads inside the buffers `vtBufsB`.
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
  /-- The bus challenges. -/
  alphas : List E
  /-- The five framework words at the cursor. -/
  xs : List E
  /-- The guest's bytecode. -/
  bc : List K

/-- The buffers the bus sides read and write: the cursor, `fp_w`, `claim_pool`,
`block_index_mle`. -/
def vtBufsBIdx : List (ℕ × ℕ) := [(5, 5), (13, 16), (15, 5), (781, 153)]

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
  hal : D.alphas.length = 4
  hW : TbReadsAt rd (args.getD 13 0) (eqKernel D.alphas)
  hxl : D.xs.length = 5
  hcur : TbReadsAt rd (args.getD 5 0) D.xs
  hpool : ∀ i < 5, LoadHolds rd (args.getD 15 0) i (D.xs.getD i 0)
  hcan : ∀ i < 5, IsCanonical128 (args.getD i 0)
  /-- The earlier statements' values (`vtS_complete`). -/
  e20 : ∀ i < 5, vtσ rd wo args (.n (20 + i)) = vtσ rd wo args (.n i)
  ekb : ∀ i < 8, vtσ rd wo args (.n (28 + i)) = gen ^ ([0, D.lm] ++ vtTauList (vtHt D.rows)).getD i 0
  eoP : ∀ x < 54, vtσ rd wo args (.n (vtBoffV x)) =
    gen ^ (stackOffsets (vtSizesP D.lm (vtHt D.rows))).1.getD x 0
  eoC : ∀ x < 45, vtσ rd wo args (.n (vtBoffV (108 + x))) =
    gen ^ (stackOffsets (vtSizesC (vtHt D.rows))).1.getD x 0
  eSh : ∀ t < 6, vtσ rd wo args (.n (vtShLen t)) = gen ^ (D.point.length - vtHt D.rows t)
  e668 : vtσ rd wo args (.n 668) = wo 668
  e703 : vtσ rd wo args (.n 703) = wo 703
  e705 : vtσ rd wo args (.n 705) = wo 705
  e706 : vtσ rd wo args (.n 706) = wo 706
  hpw : ∀ t < 6, vtσ rd wo args (.n (vtPadV t)) =
    paddingWeight (D.point.take (vtHt D.rows t)) (vtRw D.rows t)
  /-- The own buffers' words. -/
  hidxc : TbReadsAt rd (wo 668) vtIdxcW
  hz1 : TbReadsAt rd (wo 703) (D.point.map (1 + ·))
  hrun : ∀ t < 6, RunTables rd (wo 705 * gen ^ (288 * t)) (wo 706 * gen ^ (144 * t))
    (D.point.length - vtHt D.rows t) (D.point.drop (vtHt D.rows t))
    ((D.point.map (1 + ·)).drop (vtHt D.rows t))
    ((gSquaresList.drop (vtHt D.rows t)).take (D.point.length - vtHt D.rows t))
  hidxB : TbReadsAt rd (wo 781) (vtIdxBufW D.point D.lm)
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
  hwI : wo 824 = indexMle (D.point.take D.lm) ∧ wo 894 = indexMle (D.point.take 19)
  /-- The bytecode's size. -/
  hbc : D.bc.length = 2 ^ 23

theorem vtB_loads_check : ((vtPre.drop 769).take 1820).all (fun s ↦ match s with
    | .atom (.load _ p off) => vtBufsBIdx.any fun q ↦ decide (p = .n q.1) && decide (off < q.2)
    | _ => true) = true := by simp only [vtPre_drop]; decide +kernel

/-- **Every load of the bus sides reads inside `vtBufsB`.** -/
theorem vtB_loadsInBuf (σ : Val) : LoadsInBuf σ (vtBufsB σ) ((vtPre.drop 769).take 1820) := by
  intro d p off hm
  have := List.all_eq_true.mp vtB_loads_check _ hm
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨q, hq, rfl, hoff⟩ := this
  exact vt_inBuf_direct (List.mem_map.mpr ⟨q, hq, rfl⟩) hoff

end
end LeanVM.Guest.B1.Tables
