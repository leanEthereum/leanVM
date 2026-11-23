/-
  LeanVM.Guest.B1.Gkr.VbgBuf

  `verify_bus_gkr` as a flat function, and its six buffers' honest words as whole buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgComplete
public import LeanVM.Guest.B1.Gkr.GlCLayers
public import LeanVM.Guest.B1.Gkr.VbgBound
public import LeanVM.Guest.B1.Tables.FlatLift
public import LeanVM.Guest.B1.Fwd.PureIn
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr»

/-!
# `verify_bus_gkr`'s kernel facts and buffers

`vbgFlat`: `verify_bus_gkr` as a flat function (`FlatFn`): its evaluation list `vbgEvL`, its
range check's two reads (`vbgAux`), its callees `vbgKidS`
(`gkr_layers__L{o}`, `verify_bus_gkr_loop0` and theirs, placing nothing).

**The buffers.** `vbgLay` (`VbgComplete`) places the honest words as runs inside the eight
buffers; `vbgOwnW` lays out each buffer whole, the runs at their offsets and zeros between:
`layers` (`10·(depth + 2)` words, a slot of `10` per level, the levels `≡ depth (mod 2)` from `1`
up to `depth`), `gkr_sizes` (`66`), the round records (`7·gkRecCount depth` words, records of `7`,
layer `j`'s `j / 4 + 1` from record `gkPos`), the point rows (`depth / 2 + 2` rows of `40`), the
tables `depth_odd`, `four_bounds`, `four_rem` (`33` each) and the last slot's values (`3`).
`vbg_memLay` (`VbgMem`): a memory holding the whole buffers holds `vbgLay`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## Kernel facts -/

/-- `verify_bus_gkr`'s callees, directly or not. -/
def vbgKidS : List String :=
  [glcLsN 0, glcLsN 1, glcLsLN 0, glcLsLN 1] ++
    ((List.range 4).flatMap fun r ↦ [glcLastN r 0, glcLastN r 1]) ++
    ((List.range 4).flatMap fun p ↦ [glName p 0, glName p 1, glLoopName p 0, glLoopName p 1]) ++
    [name% «verify_bus_gkr_loop0»]

theorem vbg_kids_pure : coreProgram.PureIn vbgKidS := pureIn_of_pureInB (by decide +kernel)

/-- The range check's reads. -/
def vbgAux (i : ℕ) : Bool := i == val% «verify_bus_gkr» "s3#2" || i == val% «verify_bus_gkr» "s3#3"

theorem vbg_aux : ∀ i ∈ auxIdx vbgEvL, vbgAux i = true :=
  List.all_eq_true.mp (show (auxIdx vbgEvL).all vbgAux = true by decide +kernel)

theorem vbg_dead : vbgEvL.all (deadS vbgAux) = true := by decide +kernel

theorem vbg_flat : vbgPre.all Stmt.flat = true := by decide +kernel

theorem vbg_addrs : vbgPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem vbg_not_loop : coreProgram.loop "verify_bus_gkr" = false := by decide +kernel

theorem vbg_iteOk : vbgPre.all iteOk = true := by decide +kernel

theorem vbg_callOk : vbgPre.all (callOk vbgKidS) = true := by decide +kernel

/-- **`verify_bus_gkr` as a flat function.** -/
noncomputable def vbgFlat : FlatFn where
  name := "verify_bus_gkr"
  fn := vbgFound.choose
  k := 10
  pre := vbgPre
  rets := vbgRets
  evL := vbgEvL
  aux := vbgAux
  kids := vbgKidS
  hf := vbgFound.choose_spec.1
  hloop := vbg_not_loop
  hp := vbgFound.choose_spec.2.1
  hb := vbgFound.choose_spec.2.2
  hevL := rfl
  hchk := Option.isSome_iff_exists.mp vb_chk
  hdead := vbg_dead
  haux := vbg_aux
  hflat := vbg_flat
  haddrs := vbg_addrs
  hiteOk := vbg_iteOk
  hcall := vbg_callOk
  hpure := vbg_kids_pure

/-! ## The buffers' words -/

section
variable (depth : ℕ) (cap0 xs : List E) (cur : E)

/-- Layer index `k`'s slot's words. -/
noncomputable def vbgSlotW (k : ℕ) : List E :=
  gkSlotWords (gkSl cap0 xs (depth % 2) k).1 (cur * gen ^ (gkSl cap0 xs (depth % 2) k).2.2)
    (gkSl cap0 xs (depth % 2) k).2.1 (gen ^ (7 * gkPos (depth % 2) k))

/-- Level `l`'s ten words of `layers`. -/
noncomputable def vbgLayBlock (l : ℕ) : List E :=
  if l % 2 = depth % 2 ∧ 1 ≤ l ∧ l ≤ depth then vbgSlotW depth cap0 xs cur ((l - depth % 2) / 2)
  else List.replicate 10 0

/-- `layers`, whole. -/
noncomputable def vbgLayersW : List E :=
  (List.range (depth + 2)).flatMap (vbgLayBlock depth cap0 xs cur)

/-- Row `t` of the point rows, forty words: the point, at an odd depth a zero, then zeros. -/
noncomputable def vbgRowBlock (t : ℕ) : List E :=
  if depth % 2 ≤ t ∧ t - depth % 2 ≤ depth / 2 then
    ((gkSl cap0 xs (depth % 2) (t - depth % 2)).2.1.point ++ List.replicate (depth % 2) 0) ++
      List.replicate (40 - ((gkSl cap0 xs (depth % 2) (t - depth % 2)).2.1.point.length +
        depth % 2)) 0
  else List.replicate 40 0

/-- The point rows, whole. -/
noncomputable def vbgRowsW : List E := (List.range (depth / 2 + 2)).flatMap (vbgRowBlock depth cap0 xs)

/-- Radix-four layer `j`'s (layer index `j + 1 - sh`) records, seven words each. -/
noncomputable def vbgRecRun (j : ℕ) : List E :=
  (List.range (j / 4 + 1)).flatMap fun y ↦
    (List.range 7).map fun f ↦ gkRecW cap0 xs (depth % 2) cur (j + 1 - depth % 2) f y

/-- The layers' records, in layer order. -/
noncomputable def vbgRecs : List E := (List.range ((depth - 1) / 2)).flatMap (vbgRecRun depth cap0 xs cur)

/-- The round records, whole: an unused record, the layers' records, zeros. -/
noncomputable def vbgRoundsW : List E :=
  List.replicate 7 0 ++ vbgRecs depth cap0 xs cur ++
    List.replicate (7 * gkRecCount depth - (7 + (vbgRecs depth cap0 xs cur).length)) 0

end

/-- The tables `depth_odd`, `four_bounds`, `four_rem`. -/
def vbgOddW : List E := (List.range 33).map fun k ↦ gen ^ (k % 2)
def vbgBndW : List E := (List.range 33).map fun k ↦ gen ^ ((k - 1) / 8)
def vbgRemW : List E := (List.range 33).map fun k ↦ gen ^ (((k - 1) / 2) % 4)

/-- The last slot's values. -/
noncomputable def vbgValsW (depth : ℕ) (cap0 xs : List E) : List E :=
  (gkSl cap0 xs (depth % 2) (depth / 2)).2.1.values

/-- The buffers' words. -/
noncomputable def vbgOwnW (depth : ℕ) (cap0 xs : List E) (cur : E) : List (List E) :=
  [vbgLayersW depth cap0 xs cur, vbgSizesW, vbgRoundsW depth cap0 xs cur, vbgRowsW depth cap0 xs,
    vbgOddW, vbgBndW, vbgRemW, vbgValsW depth cap0 xs]

end
end LeanVM.Guest.B1.Tables
