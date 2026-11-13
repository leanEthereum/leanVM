/-
  LeanVM.Guest.B1.Gkr.VbgBuf

  `verify_bus_gkr` as a flat function, and its six buffers' honest words as whole buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgComplete
public import LeanVM.Guest.B1.Gkr.VbgBound
public import LeanVM.Guest.B1.Tables.FlatLift
public import LeanVM.Guest.B1.Fwd.PureIn
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr`'s kernel facts and buffers

`vbgFlat`: `verify_bus_gkr` as a flat function (`FlatFn`): its evaluation list `vbgEvL`, its
range check's two reads (`vbgAux`, values `21`, `22`), its callees `vbgKidS` (`verify_bus_gkr_loop0`, `verify_bus_gkr_loop1`
and theirs, placing nothing).

**The buffers.** `vbgLay` (`VbgComplete`) places the honest words as runs inside the seven
buffers; `vbgOwnW` lays out each buffer whole, the runs at their offsets and zeros between:
`layers` (`13·(depth + 2)` words, a slot of `13` per level, the levels `≡ depth (mod 2)` from `1`
up to `depth`), the round records (`7` fields of `862` words, the loop's from position `1`), the
point rows (`41` rows of `40`), the table `k_mod_next` (`8`), the tables `loop_bounds`,
`depth_odd` (`33` each) and the last slot's values (`3`). `vbg_memLay` (`VbgMem`): a memory
holding the whole buffers holds `vbgLay`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## Kernel facts -/

/-- `verify_bus_gkr`'s callees, directly or not. -/
def vbgKidS : List String :=
  [name% «verify_bus_gkr_loop0_loop0», name% «verify_bus_gkr_loop0», name% «verify_bus_gkr_loop1», "gkr_rounds__L0", "gkr_rounds__L1", "gkr_rounds__L2",
    "gkr_rounds__L4", "gkr_rounds__L6"]

theorem vbg_kids_pure : coreProgram.PureIn vbgKidS := pureIn_of_pureInB (by decide +kernel)

/-- The range check's reads. -/
def vbgAux (i : ℕ) : Bool := i == 21 || i == 22

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
  k := 9
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
variable (depth : ℕ) (cap0 xs : List E) (cur : E) (eP : ℕ)

/-- Layer index `k`'s slot's words. -/
noncomputable def vbgSlotW (k : ℕ) : List E :=
  gkSlotWords (gkSl cap0 xs (depth % 2) k).1 (cur * gen ^ (gkSl cap0 xs (depth % 2) k).2.2)
    (gkSl cap0 xs (depth % 2) k).2.1 (ofK (addressOfIndex eP) * gen ^ (40 * (k + depth % 2)))
    (gen ^ gkPos (depth % 2) k) (gen ^ (k / 4)) (gen ^ (k % 4))

/-- Level `l`'s thirteen words of `layers`. -/
noncomputable def vbgLayBlock (l : ℕ) : List E :=
  if l % 2 = depth % 2 ∧ 1 ≤ l ∧ l ≤ depth then vbgSlotW depth cap0 xs cur eP ((l - depth % 2) / 2)
  else List.replicate 13 0

/-- `layers`, whole. -/
noncomputable def vbgLayersW : List E :=
  (List.range (depth + 2)).flatMap (vbgLayBlock depth cap0 xs cur eP)

/-- Row `t` of the point rows, forty words. -/
noncomputable def vbgRowBlock (t : ℕ) : List E :=
  if depth % 2 ≤ t ∧ t - depth % 2 ≤ depth / 2 then
    (gkSl cap0 xs (depth % 2) (t - depth % 2)).2.1.point ++
      List.replicate (40 - (gkSl cap0 xs (depth % 2) (t - depth % 2)).2.1.point.length) 0
  else List.replicate 40 0

/-- The point rows, whole. -/
noncomputable def vbgRowsW : List E := (List.range 41).flatMap (vbgRowBlock depth cap0 xs)

/-- The loop's step `j`'s (layer index `j + 1 - sh`) records' field `f`. -/
noncomputable def vbgRecRun (f j : ℕ) : List E :=
  (List.range (2 * (j + 1 - depth % 2) + depth % 2 + 1)).map
    (gkRecW cap0 xs (depth % 2) cur (j + 1 - depth % 2) f)

/-- Field `f`'s `862` words of the round records. -/
noncomputable def vbgRecBlock (f : ℕ) : List E :=
  List.replicate 1 0 ++ (List.range ((depth - 1) / 2)).flatMap (vbgRecRun depth cap0 xs cur f) ++
    List.replicate (862 - (1 +
      ((List.range ((depth - 1) / 2)).flatMap (vbgRecRun depth cap0 xs cur f)).length)) 0

/-- The round records, whole. -/
noncomputable def vbgRoundsW : List E := (List.range 7).flatMap (vbgRecBlock depth cap0 xs cur)

end

/-- The tables `loop_bounds`, `depth_odd` (`k_mod_next`'s words are `kmnWords`). -/
def vbgBndW : List E := (List.range 33).map fun k ↦ gen ^ ((k - 1) / 2)
def vbgOddW : List E := (List.range 33).map fun k ↦ gen ^ (k % 2)

/-- The last slot's values. -/
noncomputable def vbgValsW (depth : ℕ) (cap0 xs : List E) : List E :=
  (gkSl cap0 xs (depth % 2) (depth / 2)).2.1.values

/-- The buffers' words. -/
noncomputable def vbgOwnW (depth : ℕ) (cap0 xs : List E) (cur : E) (eP : ℕ) : List (List E) :=
  [vbgLayersW depth cap0 xs cur eP, vbgRoundsW depth cap0 xs cur, vbgRowsW depth cap0 xs,
    kmnWords, vbgBndW, vbgOddW, vbgValsW depth cap0 xs]

end
end LeanVM.Guest.B1.Tables
