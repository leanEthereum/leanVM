/-
  LeanVM.Guest.B1.Place.OsLay

  open_stacked's own buffers, in the order its body allocates them: sizes, honest words, pointers.
-/

module

public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Place.OsKids
public import LeanVM.Guest.B1.Place.Lp
public import LeanVM.Guest.B1.Whir.BrBody

/-!
# `open_stacked`'s buffers

In allocation order (`osSizesL`): the head's ten fixed buffers (the final message, the roots, the
fold challenges, `level_betas`, `level_mus`, `query_positions`, `query_win_ptrs`, `win_tabs`,
`ood_z`, `ood`), each level's row weights, the tail's challenges, the point and `point1`,
`basis_d`, the scales, the inner sums.

* `osOwnL c tr bp`: their honest words, the window pointers `bp` (into `level_positions`'
  decoders' frames, placement-dependent) a parameter; `osAtOf c b`: their pointers from `b`.
* Indices: `query_win_ptrs` is `6`, `osIxWp i = 10 + i`, `osIxT = 10 + n`, `osIxPT = 11 + n`,
  `osIxPT1 = 12 + n`, `osIxBD`, `osIxLS`, `osIxICH`.
* `osBp cert c D ps l j`: the pointer to decoder `j`'s windows when level `l`'s `level_positions`
  is entered at `ps l`, its decoders' frame pointers `D l (ps l) j`.
* `osLk`: the own buffers but the window pointers, and the caller's words; `osW`: level `l`'s
  window pointers, its `level_positions` at `p`; `osS`: that call's decoders' runs.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The buffers' honest words, in allocation order, the window pointers `bp`. -/
noncomputable def osOwnL (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) : List (List E) :=
  [fmsgC c tr, rootsC c tr, fchC c tr, betasC c tr, musC c tr, qposC c tr, qbpC c bp, winC,
    oodzC c tr, oodC c tr] ++
  (List.range c.levels.length).map (wpC c tr) ++
  [tailC tr.Lf tr.xsR, ptC tr (c.levels.headD default).folds,
    pt1C tr (c.levels.headD default).folds, bdC c tr, lsC c tr, ichC c tr]

/-- Indices of the per-level and finish buffers. -/
def osIxWp (i : ℕ) : ℕ := 10 + i
def osIxT (c : OsCfg) : ℕ := 10 + c.levels.length
def osIxPT (c : OsCfg) : ℕ := 11 + c.levels.length
def osIxPT1 (c : OsCfg) : ℕ := 12 + c.levels.length
def osIxBD (c : OsCfg) : ℕ := 13 + c.levels.length
def osIxLS (c : OsCfg) : ℕ := 14 + c.levels.length
def osIxICH (c : OsCfg) : ℕ := 15 + c.levels.length

/-- The exponent of buffer `j` from `b`. -/
def osBase (c : OsCfg) (b j : ℕ) : ℕ := (bases b (osSizesL c)).getD j 0

/-- The pointer of buffer `j` from `b`. -/
def osPtrAt (c : OsCfg) (b j : ℕ) : E := ofK (addressOfIndex (osBase c b j))

/-- The buffers' pointers from `b`. -/
def osAtOf (c : OsCfg) (b : ℕ) : OsAt :=
  ⟨⟨osPtrAt c b 0, osPtrAt c b 1, osPtrAt c b 2, osPtrAt c b 3, osPtrAt c b 4, osPtrAt c b 5,
      osPtrAt c b 6, osPtrAt c b 7, osPtrAt c b 8, osPtrAt c b 9⟩,
    osPtrAt c b (osIxT c), osPtrAt c b (osIxPT c), osPtrAt c b (osIxPT1 c), osPtrAt c b (osIxBD c),
    osPtrAt c b (osIxLS c), osPtrAt c b (osIxICH c), fun i ↦ osPtrAt c b (osIxWp i)⟩

/-- Level `l`'s decoder. -/
def osDecName (c : OsCfg) (l : ℕ) : String := qwDecName (lvAt c l).depth (lvAt c l).capDepth

/-- **The window pointers' runs** when level `l`'s `level_positions` is entered at `ps l`, its
decoders' frame pointers `D l (ps l) j`: decoder `j`'s windows (`qwPtrAt` at position `0`). -/
def osBp (cert : String → V → ℕ) (c : OsCfg) (D : ℕ → ℕ → ℕ → ℕ) (ps : ℕ → ℕ) (l j : ℕ) : E :=
  ofK (addressOfIndex (D l (ps l) j + cert (osDecName c l) (.n 5)))

/-- The caller's words the callees read, but the window pointers: the own buffers without
`query_win_ptrs`, and the caller's words `Lin`. -/
noncomputable def osLk (c : OsCfg) (tr : OsTr) (b : ℕ) (Lin : Layout) : Layout :=
  ((bufL b (osSizesL c) (osOwnL c tr fun _ _ ↦ 0)).eraseIdx 6) ++ Lin

/-- Level `l`'s window pointers, its `level_positions` at `p`. -/
def osW (cert : String → V → ℕ) (c : OsCfg) (D : ℕ → ℕ → ℕ → ℕ) (b l p : ℕ) : Layout :=
  [(osBase c b 6 + (lvAt c l).posOff,
    (List.range ((lvAt c l).squeezes * (192 / (lvAt c l).depth))).map fun k ↦
      osBp cert c D (fun _ ↦ p) l (k / (192 / (lvAt c l).depth)) *
        gen ^ ((k % (192 / (lvAt c l).depth)) * qwN (lvAt c l).depth (lvAt c l).capDepth))]

/-- Level `l`'s decoders' runs, its `level_positions` at `p` (the buffers it hands back). -/
def osS (cert : String → V → ℕ) (c : OsCfg) (tr : OsTr) (D : ℕ → ℕ → ℕ → ℕ) (l p : ℕ) : Layout :=
  lpRuns cert (lvAt c l).depth (lvAt c l).capDepth (lvAt c l).squeezes (D l p) (tr.L l).F2.cap

end
end LeanVM.Guest.B1
