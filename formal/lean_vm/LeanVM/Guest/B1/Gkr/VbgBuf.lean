/-
  LeanVM.Guest.B1.Gkr.VbgBuf

  `verify_bus_gkr` as a flat function, and its six buffers' honest words as whole buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgComplete
public import LeanVM.Guest.B1.Tables.FlatLift
public import LeanVM.Guest.B1.Fwd.PureIn

/-!
# `verify_bus_gkr`'s kernel facts and buffers

`vbgFlat`: `verify_bus_gkr` as a flat function (`FlatFn`): its evaluation list `vbgEvL`, its
range check's two reads (`vbgAux`, values `20`, `21`), its callees `vbgKidS` (`__loop6`, `__loop7`
and theirs, placing nothing).

**The buffers.** `vbgLay` (`VbgComplete`) places the honest words as runs inside the six buffers;
`vbgBufs` lays out each buffer whole, the runs at their offsets and zeros between: `layers`
(`17·(depth + 2)` words, a slot of `17` per level, the levels `≡ depth (mod 2)` up to `depth` and
the root), the round records (`7` fields of `862` words), the point rows (`41` rows of `40`), the
table `k_mod_next` (`8`), the tables `pairs`, `depth_shift` (`33` each). `vbg_memLay`: a memory holding the whole buffers holds
`vbgLay`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## Kernel facts -/

/-- `verify_bus_gkr`'s callees, directly or not. -/
def vbgKidS : List String :=
  ["__loop36", "__loop6", "__loop7", "gkr_rounds__L0", "gkr_rounds__L1", "gkr_rounds__L2",
    "gkr_rounds__L4", "gkr_rounds__L6"]

theorem vbg_kids_pure : coreProgram.PureIn vbgKidS := pureIn_of_pureInB (by decide +kernel)

/-- The range check's reads. -/
def vbgAux (i : ℕ) : Bool := i == 20 || i == 21

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
  k := 8
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

/-- Step `j`'s slot's words. -/
noncomputable def vbgSlotW (j : ℕ) : List E :=
  gkSlotWords (gkSl cap0 xs (depth % 2) j).1 (cur * gen ^ (gkSl cap0 xs (depth % 2) j).2.2)
    (gkSl cap0 xs (depth % 2) j).2.1 (ofK (addressOfIndex eP) * gen ^ (40 * (j + depth % 2)))
    (gen ^ gkPos (depth % 2) j) (gen ^ (j / 4)) (gen ^ (j % 4))

/-- The root slot's words. -/
noncomputable def vbgRootW : List E :=
  gkSlotWords (gkRootS cap0 xs) (cur * gen ^ 2) (gkRootSt xs) (ofK (addressOfIndex eP)) 1 1 1

/-- Level `l`'s seventeen words of `layers`. -/
noncomputable def vbgLayBlock (l : ℕ) : List E :=
  if l % 2 = depth % 2 ∧ l ≤ depth then vbgSlotW depth cap0 xs cur eP ((l - depth % 2) / 2)
  else if l = 0 then vbgRootW cap0 xs cur eP else List.replicate 17 0

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

/-- Step `j`'s records' field `f`. -/
noncomputable def vbgRecRun (f j : ℕ) : List E :=
  (List.range (2 * j + depth % 2 + 1)).map (gkRecW cap0 xs (depth % 2) cur j f)

/-- Field `f`'s `862` words of the round records. -/
noncomputable def vbgRecBlock (f : ℕ) : List E :=
  List.replicate (depth % 2) 0 ++ (List.range (depth / 2)).flatMap (vbgRecRun depth cap0 xs cur f) ++
    List.replicate (862 - (depth % 2 +
      ((List.range (depth / 2)).flatMap (vbgRecRun depth cap0 xs cur f)).length)) 0

/-- The round records, whole. -/
noncomputable def vbgRoundsW : List E := (List.range 7).flatMap (vbgRecBlock depth cap0 xs cur)

end

/-- The tables `pairs`, `depth_shift` (`k_mod_next`'s words are `kmnWords`). -/
def vbgPairsW : List E := (List.range 33).map fun k ↦ gen ^ (k / 2)
def vbgDshW : List E := (List.range 33).map fun k ↦ gen ^ (k % 2)

/-- The buffers' sizes. -/
def vbgSizes (depth : ℕ) : List ℕ := [17 * (depth + 2), 6034, 1640, 8, 33, 33]

/-- The buffers' words. -/
noncomputable def vbgOwnW (depth : ℕ) (cap0 xs : List E) (cur : E) (eP : ℕ) : List (List E) :=
  [vbgLayersW depth cap0 xs cur eP, vbgRoundsW depth cap0 xs cur, vbgRowsW depth cap0 xs,
    kmnWords, vbgPairsW, vbgDshW]

end
end LeanVM.Guest.B1.Tables
