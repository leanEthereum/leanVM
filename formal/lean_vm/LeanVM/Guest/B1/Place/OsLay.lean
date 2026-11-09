/-
  LeanVM.Guest.B1.Place.OsLay

  open_stacked's own buffers, in the order its body allocates them: sizes, honest words, pointers.
-/

module

public import LeanVM.Guest.B1.Place.OsKids
public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.B1.Whir.BrBody

/-!
# `open_stacked`'s buffers

In allocation order (G:1516-1545 at 40f877dc): the head's twelve fixed buffers (`merkle_caps`,
`merkle_cap_active`, the final message, the roots, the fold challenges, `level_betas`,
`level_mus`, `query_positions`, `query_win_ptrs`, `win_tabs`, `ood_z`, `ood`), each level's
squeeze run and row weights, the tail's challenges, the point and `point1`, `basis_d`, the
scales, the inner sums, each level's residual chain (`queries / 8 + 1` words).

* `osSizesL c`: their sizes; `osOwnL c tr bp`: their honest words, the query window pointers
  `bp` (the decoders' frames, placement-dependent) a parameter; `osAtOf c b`: their pointers
  from `b`.
* Indices: `osIxSqz i = 12 + 2i`, `osIxWp i = 13 + 2i`, `osIxT = 12 + 2n`, `osIxPT = 13 + 2n`,
  `osIxPT1 = 14 + 2n`, `osIxBD`, `osIxLS`, `osIxICH`, `osIxRC i = 18 + 2n + i`; `qbp` is index
  `8`.
* `osBp`: the window pointers when level `l`'s squeeze loop is placed at `ps l`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The buffers' sizes, in allocation order. -/
def osSizesL (c : OsCfg) : List ℕ :=
  [4 * c.capLen, c.capLen, c.yrLen, 2 * c.levels.length, c.nFolds, c.levels.length,
    c.levels.length, c.posLen, c.posLen, 128, c.levels.length * ligColsCap,
    c.levels.length * oodSlots] ++
  (List.range c.levels.length).flatMap (fun _ ↦ [(c.maxSq + 1) * 5, c.maxIl]) ++
  [yrLogCap, pointCap, pointCap, c.levels.length * ligColsCap, c.levels.length,
    c.levels.length + 1] ++
  (List.range c.levels.length).map fun i ↦ (lvAt c i).queries / resBatch + 1

/-- The buffers' honest words, in allocation order, the query bit pointers `bp`. -/
noncomputable def osOwnL (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) : List (List E) :=
  [capsC c tr, flagsC c tr, fmsgC c tr, rootsC c tr, fchC c tr, betasC c tr, musC c tr, qposC c tr,
    qbpC c bp, winC, oodzC c tr, oodC c tr] ++
  (List.range c.levels.length).flatMap (fun i ↦ [sqzC c tr i, wpC c tr i]) ++
  [tailC tr.Lf tr.xsR, ptC tr (c.levels.headD default).folds,
    pt1C tr (c.levels.headD default).folds, bdC c tr, lsC c tr, ichC c tr] ++
  (List.range c.levels.length).map (rcC c tr)

/-- Indices of the per-level and finish buffers. -/
def osIxSqz (i : ℕ) : ℕ := 12 + 2 * i
def osIxWp (i : ℕ) : ℕ := 13 + 2 * i
def osIxT (c : OsCfg) : ℕ := 12 + 2 * c.levels.length
def osIxPT (c : OsCfg) : ℕ := 13 + 2 * c.levels.length
def osIxPT1 (c : OsCfg) : ℕ := 14 + 2 * c.levels.length
def osIxBD (c : OsCfg) : ℕ := 15 + 2 * c.levels.length
def osIxLS (c : OsCfg) : ℕ := 16 + 2 * c.levels.length
def osIxICH (c : OsCfg) : ℕ := 17 + 2 * c.levels.length
def osIxRC (c : OsCfg) (i : ℕ) : ℕ := 18 + 2 * c.levels.length + i

/-- The exponent of buffer `j` from `b`. -/
def osBase (c : OsCfg) (b j : ℕ) : ℕ := (bases b (osSizesL c)).getD j 0

/-- The pointer of buffer `j` from `b`. -/
def osPtrAt (c : OsCfg) (b j : ℕ) : E := ofK (addressOfIndex (osBase c b j))

/-- The buffers' pointers from `b`. -/
def osAtOf (c : OsCfg) (b : ℕ) : OsAt :=
  ⟨⟨osPtrAt c b 0, osPtrAt c b 1, osPtrAt c b 2, osPtrAt c b 3, osPtrAt c b 4, osPtrAt c b 5,
      osPtrAt c b 6, osPtrAt c b 7, osPtrAt c b 8, osPtrAt c b 9, osPtrAt c b 10, osPtrAt c b 11⟩,
    osPtrAt c b (osIxT c), osPtrAt c b (osIxPT c), osPtrAt c b (osIxPT1 c), osPtrAt c b (osIxBD c),
    osPtrAt c b (osIxLS c), osPtrAt c b (osIxICH c), fun i ↦ osPtrAt c b (osIxSqz i),
    fun i ↦ osPtrAt c b (osIxWp i), fun i ↦ osPtrAt c b (osIxRC c i)⟩

/-- The squeeze loop's name, trip count and decoders' first cell, of level `l`. -/
def osSqN (c : OsCfg) (l : ℕ) : ℕ := (lvAt c l).squeezes

/-- **The query window pointers** when level `l`'s squeeze loop is placed at `ps l`: decoder
`j`'s `wins` run (dqwc's `qwPtrAt` at position `0`). -/
def osBp (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (ps : ℕ → ℕ) (l j : ℕ) : E :=
  ofK (addressOfIndex (sqDecAt fs (lvAt c l) (c.sqLoop l) (osSqN c l) (ps l) j +
    cert (sqDecName (lvAt c l)) (.n 5)))

/-- The caller's words the callees read, but the query bit pointers: the own buffers without
`qbp`, and the caller's words `Lin`. -/
noncomputable def osLk (c : OsCfg) (tr : OsTr) (b : ℕ) (Lin : Layout) : Layout :=
  ((bufL b (osSizesL c) (osOwnL c tr fun _ _ ↦ 0)).eraseIdx 8) ++ Lin

/-- Level `l`'s query bit pointers, its squeeze loop at `p`. -/
def osW (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (b l p : ℕ) : Layout :=
  [(osBase c b 8 + (lvAt c l).posOff,
    (List.range ((lvAt c l).squeezes * (192 / (lvAt c l).depth))).map fun k ↦
      osBp fs cert c (fun _ ↦ p) l (k / (192 / (lvAt c l).depth)) *
        gen ^ ((k % (192 / (lvAt c l).depth)) * qwN (lvAt c l).depth (lvAt c l).capDepth))]

/-- Level `l`'s decoders' frame runs, its squeeze loop at `p` (the loop's returned buffers). -/
def osS (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (tr : OsTr) (l p : ℕ) : Layout :=
  sqRuns fs cert (lvAt c l) (c.sqLoop l) (osSqN c l) p
    (sqWJ (((tr.L l).F2.squeezeN 0).2.cap)) 0

end
end LeanVM.Guest.B1
