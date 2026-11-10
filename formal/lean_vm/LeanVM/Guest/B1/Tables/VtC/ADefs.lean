/-
  LeanVM.Guest.B1.Tables.VtC.ADefs

  `verify_tables`' honest memory and oracle: the caller's buffers, its own buffers in allocation
  order at the bump allocator's positions, and the oracle's words.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AHon
public import LeanVM.Guest.B1.Tables.VtC.ABuf
public import LeanVM.Guest.B1.Tables.VtC.BMain
public import LeanVM.Guest.B1.Selectors.LayoutBasic
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.B1.Tables.VtC.FData
public import LeanVM.Guest.B1.Bits.Tables

/-!
# The honest memory

`VtBases`: the caller's buffers' addresses (the cursor, `zeta`, `dims_g`, `table_rows`,
`g_squares` (the exponent table), `fp_w`, `claim_pool`, `chi`, `gkr_leaves`, `bc_point`; `tabs` is `g_squares`' window section)
and the first word of `verify_tables`' own buffers. `VtHonest.args`: the 20 arguments. `VtHonest.linL`: the caller's
buffers' honest words. `vtAllocVars`: the 111 allocations' values, in order (`vt_allocs`, by the
kernel); `VtHonest.sizes`, `VtHonest.ownW`: their sizes and honest words; `VtHonest.ownL`: them
at the bump allocator's positions. `VtWOk`: what the oracle answers (the allocations' pointers,
the witnesses, the callees' returns).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure blockSel)

@[expose] public section

/-- The exponent table's words and its bit windows (`exponent_tables`). -/
def expTableWordsW : List E := expTableWords ++ (List.range (2 ^ winTabBits)).map eOfNat

theorem length_expTableWordsW : expTableWordsW.length = 236 + 2 ^ winTabBits := by
  simp [expTableWordsW, expTableWords, length_etWordsN]

/-- **The exponent table holds what `verify_tables` reads of it.** -/
theorem vt_expTablesAt {rd : Reader} {sq : E} (h : TbReadsAt rd sq expTableWordsW) :
    ExpTablesAt rd sq := by
  have hl : expTableWords.length = 236 := by simp [expTableWords, length_etWordsN]
  have hE : ExpTables rd sq := (expTables_iff_words _ _).2 fun o ho ↦ by
    have := h o (by rw [length_expTableWordsW]; exact Nat.lt_add_right _ ho)
    rw [← List.getD_eq_getElem _ 0, expTableWordsW, List.getD_append _ _ _ _ (by omega)] at this
    exact this
  refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_, fun gi hgi ↦ ?_, fun n hn ↦ ?_⟩
  · simp only [gSquaresList, List.length_map, List.length_range] at hk
    simpa [gSquaresList] using hE.1 k hk
  · simp only [rankKeysList, List.length_map, List.length_range] at hk
    rw [loadHolds_mul_gen_pow]
    simpa [rankKeysList] using hE.2.2.1 k hk
  · simp only [sideTabList, List.length_map, List.length_range] at hgi
    rw [loadHolds_mul_gen_pow]
    simp only [sideTabList, List.getElem_map, List.getElem_range]
    have h0 := fun gi (h1 : gi < 9) ↦ hE.2.2.2 0 (by decide) gi (by simp [B1.sideGroupStart]) (by
      simpa [B1.sideGroupStart] using h1)
    have h1 := fun gi (h1 : 9 ≤ gi) (h2 : gi < 18) ↦ hE.2.2.2 1 (by decide) gi (by
      simpa [B1.sideGroupStart] using h1) (by simpa [B1.sideGroupStart] using h2)
    have h2 := fun gi (h1 : 18 ≤ gi) (h2 : gi < 24) ↦ hE.2.2.2 2 (by decide) gi (by
      simpa [B1.sideGroupStart] using h1) (by simpa [B1.sideGroupStart] using h2)
    interval_cases gi
    all_goals first
      | exact h0 _ (by decide)
      | exact h1 _ (by decide) (by decide)
      | exact h2 _ (by decide) (by decide)
  · rw [loadHolds_mul_gen_pow]
    have := h (236 + n) (by rw [length_expTableWordsW]; exact Nat.add_lt_add_left hn 236)
    rw [← List.getD_eq_getElem _ 0, expTableWordsW, List.getD_append_right _ _ _ _ (by omega),
      show 236 + n - expTableWords.length = n by omega, List.getD_eq_getElem _ _ (by simpa using hn),
      List.getElem_map, List.getElem_range] at this
    exact this

/-- The caller's buffers' addresses and the first word of the function's own. -/
structure VtBases where
  cur : ℕ
  zeta : ℕ
  dims : ℕ
  rows : ℕ
  sq : ℕ
  fpw : ℕ
  pool : ℕ
  chi : ℕ
  leaves : ℕ
  bcp : ℕ
  own : ℕ

/-- The allocations' values, in order. -/
def vtAllocVars : List ℕ :=
  [33, 34, 35, 36, 664, 699, 701, 702, 777] ++ (List.range 3).map (fun b ↦ vtFwW b + 6) ++
    (List.range 51).map (fun i ↦ (vtPushSel.getD i default).2.2.1) ++
    (List.range 45).map (fun i ↦ (vtCountSel.getD i default).2.2.1) ++ [2627, 2630, 2651]

theorem vtAllocVars_length : vtAllocVars.length = 111 := by decide

/-- **The allocations, by the kernel.** -/
theorem vt_allocs : (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.1) =
    vtAllocVars.map V.n := by decide +kernel

namespace VtHonest

variable (H : VtHonest) (B : VtBases)

/-- `|point|`. -/
def μ : ℕ := H.point.length

/-- Table `t`'s height. -/
def τ (t : ℕ) : ℕ := vtHt H.rows t

/-- The push side's offsets. -/
def offP : List ℕ := (stackOffsets (vtSizesP H.lm H.τ)).1

/-- The count side's offsets. -/
def offC : List ℕ := (stackOffsets (vtSizesC H.τ)).1

/-- The arguments. -/
noncomputable def args : List E :=
  [H.f.getD 0 0, H.f.getD 1 0, H.f.getD 2 0, H.f.getD 3 0, H.f.getD 4 0, ofK (addressOfIndex B.cur),
    (digestHalves H.pi).1, (digestHalves H.pi).2, ofK (addressOfIndex B.zeta), gen ^ H.μ,
    ofK (addressOfIndex B.dims), ofK (addressOfIndex B.rows), ofK (addressOfIndex B.sq),
    ofK (addressOfIndex B.fpw), H.beta, ofK (addressOfIndex B.pool), ofK (addressOfIndex B.chi),
    ofK (addressOfIndex B.leaves), ofK (addressOfIndex B.sq) * gen ^ winTabAt, ofK (addressOfIndex B.bcp)]

/-- `dims_g`'s words. -/
noncomputable def dimsW : List E := gen ^ H.lm :: (vtTauList H.τ).map (gen ^ ·)

/-- The stream words. -/
def curW : List E := H.xs4 ++ H.bcW ++ H.xsR ++ H.evsT.flatten

/-- The public input's claims' values. -/
noncomputable def pcW : List E :=
  ([0, 1] : List (Fin 2)).map fun limb ↦
    multilinearEval [ofK ((digestHalves H.pi).1.limb limb),
      ofK ((digestHalves H.pi).2.limb limb)] [H.rm]

/-- `claim_pool`'s words: the bus's four, slots `4 ..< 157` unwritten by `verify_tables`, the
public input's two. -/
noncomputable def poolW : List E := H.xs4 ++ List.replicate 153 0 ++ H.pcW

/-- `chi`'s words: the challenges, last first. -/
noncomputable def chiW : List E := zcChis H.cap0 H.target H.xsR H.n

/-- **The caller's buffers.** -/
noncomputable def linL : TLay :=
  [(B.cur, H.curW), (B.zeta, H.point), (B.dims, H.dimsW), (B.rows, H.rows.map eOfNat),
    (B.sq, expTableWordsW), (B.fpw, H.weights), (B.pool, H.poolW), (B.chi, H.chiW),
    (B.leaves, H.values), (B.bcp, H.slots)]

/-- The own buffers' sizes, in allocation order. -/
def sizes : List ℕ :=
  [24, 24, 24, 24, 34, H.μ, 1728, 864, 153, 34, 34, 34] ++ List.replicate 96 9 ++
    [7 * (H.n + 1), H.n + 1, H.n + 1]

/-- **The own buffers' honest words**, in allocation order. -/
noncomputable def ownW : List (List E) :=
  [vtGKeyW H.lm H.τ, vtGSizeW H.lm H.τ, vtGBaseW H.lm H.τ, vtGOrdW H.lm H.τ, vtIdxcW,
    H.point.map (1 + ·), vtShEqW H.point H.τ, vtShGW H.point H.τ, vtIdxBufW H.point H.lm] ++
    (List.range 3).map (fun b ↦ offBits (H.offP.getD b 0)) ++
    (List.range 51).map (fun i ↦ offDigits (H.offP.getD (3 + i) 0)
      (H.τ (vtPushSel.getD i default).2.2.2.1)) ++
    (List.range 45).map (fun i ↦ offDigits (H.offC.getD i 0)
      (H.τ (vtCountSel.getD i default).2.2.2.1)) ++
    [zcRoundsW H.cap0 H.target (ofK (addressOfIndex B.cur) * gen ^ 13 * gen) H.xsR H.n,
      zcCprodW H.cap0 H.target H.xsR H.n,
      (List.range (H.n + 1)).map (prefixProd 1 H.chiW ((H.point.map (1 + ·)).take H.n))]

/-- The own buffers' bases. -/
def ownB : List ℕ := LeanVM.Guest.Memory.bases B.own H.sizes

/-- **The own buffers at the bump allocator's positions.** -/
noncomputable def ownL : TLay := (H.ownB B).zip (H.ownW B)

end VtHonest

/-- **What the oracle answers**: the allocations' pointers, the witnesses, the callees'
returns. -/
structure VtWOk (H : VtHonest) (B : VtBases) (w : ℕ → E) : Prop where
  alloc : ∀ j < 111, w (vtAllocVars.getD j 0) = ofK (addressOfIndex ((H.ownB B).getD j 0))
  pads : ∀ t < 6, w (vtPadV t) = paddingWeight (H.point.take (H.τ t)) (vtRw H.rows t) ∧
    w (vtPadV t + 1) = PadLead (H.τ t) (vtRw H.rows t) ∧
    w (vtPadV t + 2) = PadRest (H.τ t) (vtRw H.rows t)
  w700 : w 700 = 0
  w2544 : w 2544 = gen ^ H.n
  hwI : w 809 = indexMle (H.point.take H.lm) ∧ w 837 = indexMle (H.point.take 19)
  hwF : ∀ b < 3, w (vtFwW b + 10) = blockSel (vtSizesP H.lm H.τ) H.μ b H.point ∧
    w (vtFwW b + 11) = gen ^ H.offP.getD b 0
  hwP : ∀ i < 51, w (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1) =
      blockSel (vtSizesP H.lm H.τ) H.μ (3 + i) H.point ∧
    w (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1 + 1) =
      gen ^ H.offP.getD (3 + i) 0
  hw1 : (List.range 8).map (fun i ↦ w (1876 + i)) = (vtBcR1 (vtF0 (H.args B) H.xs4) H.bcW).1 ++
    [(H.args B).getD 5 0 * gen ^ 7 * gen ^ 2, (vtBcR1 (vtF0 (H.args B) H.xs4) H.bcW).2.1,
      (vtBcR1 (vtF0 (H.args B) H.xs4) H.bcW).2.2]
  hw2 : (List.range 8).map (fun i ↦ w (1884 + i)) = (vtBcR2 (vtF0 (H.args B) H.xs4) H.bcW).1 ++
    [(H.args B).getD 5 0 * gen ^ 7 * gen ^ 2 * gen ^ 2, (vtBcR2 (vtF0 (H.args B) H.xs4) H.bcW).2.1,
      (vtBcR2 (vtF0 (H.args B) H.xs4) H.bcW).2.2]
  hw3 : (List.range 8).map (fun i ↦ w (1892 + i)) = (vtBcR3 (vtF0 (H.args B) H.xs4) H.bcW).1 ++
    [(H.args B).getD 5 0 * gen ^ 7 * gen ^ 2 * gen ^ 2 * gen ^ 2,
      (vtBcR3 (vtF0 (H.args B) H.xs4) H.bcW).2.1, (vtBcR3 (vtF0 (H.args B) H.xs4) H.bcW).2.2]
  hwC : ∀ i < 45, w (vtSelE (vtCountSel.getD i default).2.2.1
      (vtCountSel.getD i default).2.2.2.1) = blockSel (vtSizesC H.τ) H.μ i H.point ∧
    w (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1 + 1) =
      gen ^ H.offC.getD i 0

end
end LeanVM.Guest.B1.Tables
