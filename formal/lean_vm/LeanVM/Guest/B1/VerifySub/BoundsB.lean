/-
  LeanVM.Guest.B1.VerifySub.BoundsB

  `verify_sub`'s bounds over its sixteen callees, apart from its completeness: the callees' bounds
  in call order (`vsBs`), its bound (`vsBound`), the callees' names and trees (`vsNames`, `vsTs`).
-/

module

public import LeanVM.Guest.B1.VerifySub.WordsB
public import LeanVM.Guest.B1.Gkr.VbgBound
public import LeanVM.Guest.B1.Place.OsSpec
public import LeanVM.Guest.B1.Terminal.KidsDepBP
public import LeanVM.Guest.B1.Placement.CertifyAt
public import LeanVM.Guest.B1.Bits.BusGrind

/-!
# `verify_sub`'s bounds

The definitions `VerifySub/CompleteB` proves `verify_sub`'s completeness within, apart from its
proof's imports, for the budget (`Budget/VsCount`).

`VsWordsOs`: `VsWords` with `open_stacked`'s leaves' and residual loops' facts. `vsBs W Bvk`: the
sixteen callees' bounds, in call order (`Data.core18`): two `g_power_of_word`s,
`log2_ceil_in_the_exponent__L0_L34`, `certify_placement`, `log2_ceil_in_the_exponent__L15_L34`,
`grind_check__L15`, the `squeeze_point_from` dispatch, `opening_message__L1_L1`, the
`bus_grind_check` dispatch, `verify_bus_gkr`, `verify_tables`, `verify_keccak`, `grind_check__L14`,
`ring_switch_target`, the `open_stacked` dispatch and the terminal; the maxima over the honest
children's depths (`vbgMax`, `vtMax`, `osMax`) or a dispatch's arms (`armMax`, `busGrindMax`: an
arm's frame and its `grind_check`'s) where a callee's bound depends on them. `vsBound W Bvk = fs "verify_sub" + 8706 + (vsBs W Bvk).sum`: the frame,
the own buffers (`8677 + μ` words, `μ ≤ 29`) and the callees. `vsNames μ r d`, `vsTs`: the
callees' names (the squeeze's arm at the stack log `μ`, the bus grind's at the depth `d`,
`open_stacked`'s candidate) and trees, within their bounds, `verify_tables`' and the terminal's
within their weights (`vsPs`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-! ## The bounds -/

/-- `verify_bus_gkr`'s bound over the depths below `30`. -/
@[irreducible] noncomputable def vbgMax (fs : String → ℕ) (K29 R K8 : ℕ) : ℕ :=
  lmax ((List.range 30).map (Tables.vbgBound fs K29 R K8))

/-- `verify_tables`' bound at the bus depth `m` and the largest height `n`. -/
noncomputable def vtBnd (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 m n : ℕ) : ℕ :=
  fs "verify_tables" + (3841 + m + 9 * (n + 1)) +
    ((Tables.vtBs Kf Ksh (Tables.vtRunB fs K10 n)).sum + Tables.ifFrames fs Tables.vtPre)

/-- `verify_tables`' bound over the depths below `30` and the heights below `29`. -/
@[irreducible] noncomputable def vtMax (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 : ℕ) : ℕ :=
  lmax ((List.range 30).flatMap fun m ↦ (List.range 29).map (vtBnd fs Kf Ksh K10 m))

/-- `open_stacked`'s bound over the candidates (stack logs below `29`, rates below `5`). -/
@[irreducible] noncomputable def osMax (fs Bnd Kr : String → ℕ) : ℕ :=
  lmax ((List.range 29).flatMap fun μ ↦ (List.range 5).map (osBosAt fs Bnd Kr μ))

/-- The `bus_grind_check` dispatch's bound over its arms: an arm's frame and its `grind_check`'s
(arm `j` grinds `13 + j` bits, `busGrindBits_eq`). -/
def busGrindMax (fs : String → ℕ) : ℕ :=
  lmax ((List.range 18).map fun j ↦ fs (busGrindName j) + fs (grindCheckName (13 + j)))

/-- **`verify_sub`'s callees' words facts with `open_stacked`'s**: its leaves' and residual loops'
(`Bnd`, `Kr`). -/
structure VsWordsOs (fs : String → ℕ) extends VsWords fs where
  Bnd : String → ℕ
  Kr : String → ℕ
  hleaf : OsLeafBounds fs Bnd
  hloop : ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    OsLoopBounds fs Kr (B1.Whir.osCfg (B1.Whir.candidate μ r))

/-- **The callees' bounds**, in call order, `open_stacked`'s `os`. -/
noncomputable def vsBsWith {fs : String → ℕ} (W : VsWordsOs fs) (Bvk os : ℕ) : List ℕ :=
  [W.Bg, W.Bg, fs "log2_ceil_in_the_exponent__L0_L34" + 34 + 2 * fs "assert_small_g_power",
    fs "certify_placement" + Tables.cpSizes.sum,
    fs "log2_ceil_in_the_exponent__L15_L34" + 34 + 2 * fs "assert_small_g_power",
    W.Kst "grind_check__L15", armMax W.Kst squeezeNames, W.Kst "opening_message__L1_L1",
    busGrindMax fs, vbgMax fs W.K29 W.R W.K8, vtMax fs W.Kf W.Ksh W.K10, Bvk,
    W.Kst "grind_check__L14", fs "ring_switch_target" + 72 + W.B14, os,
    termBound fs W.Beqc W.K15 W.Bcs W.Brs]

/-- **The callees' bounds at one candidate**: `open_stacked`'s at the stack log `μ` and the
rate `r`. -/
noncomputable def vsBsAt {fs : String → ℕ} (W : VsWordsOs fs) (Bvk μ r : ℕ) : List ℕ :=
  vsBsWith W Bvk (osBosAt fs W.Bnd W.Kr μ r)

/-- **The callees' bounds**, `open_stacked`'s the largest over the candidates. -/
noncomputable def vsBs {fs : String → ℕ} (W : VsWordsOs fs) (Bvk : ℕ) : List ℕ :=
  vsBsWith W Bvk (osMax fs W.Bnd W.Kr)

/-- **`verify_sub`'s bound**: its frame, its own buffers (`8677 + μ`, `μ ≤ 29`), its callees. -/
noncomputable def vsBound {fs : String → ℕ} (W : VsWordsOs fs) (Bvk : ℕ) : ℕ :=
  fs "verify_sub" + 8706 + (vsBs W Bvk).sum

/-- **`verify_sub`'s bound at one candidate.** -/
noncomputable def vsBoundAt {fs : String → ℕ} (W : VsWordsOs fs) (Bvk μ r : ℕ) : ℕ :=
  fs "verify_sub" + 8706 + (vsBsAt W Bvk μ r).sum

/-! ## The callees' trees -/

/-- **`verify_sub`'s callees' names**, in call order: the squeeze's arm at the stack log `μ`, the
bus grind's at the depth `d`, `open_stacked`'s candidate `openName μ r`. -/
def vsNames (μ r d : ℕ) : List String :=
  ["g_power_of_word", "g_power_of_word", "log2_ceil_in_the_exponent__L0_L34", "certify_placement",
    "log2_ceil_in_the_exponent__L15_L34", "grind_check__L15", squeezeNames.getD (μ - 22) "",
    "opening_message__L1_L1", busGrindNames.getD d "", "verify_bus_gkr", "verify_tables",
    "verify_keccak", "grind_check__L14", "ring_switch_target", B1.Whir.openName μ r,
    "check_opening_terminal"]

/-- **`verify_sub`'s callees' predicates**: `verify_tables`' tree within `vtWB`, the terminal's
within `termWB`, at each opcode's weights. -/
noncomputable def vsPs {fs : String → ℕ} (W : VsWordsOs fs) : List (Tree → Prop) :=
  List.replicate 10 (fun _ ↦ True) ++
    [fun t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t] ++
    List.replicate 4 (fun _ ↦ True) ++
    [fun t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t]

/-- **`verify_sub`'s callees' trees**: callee `j` a call of its name within its bound satisfying
its predicate; `vsTsAny`, a flat node of them at some bus grind arm. -/
noncomputable def vsTs (fs : String → ℕ) (W : VsWordsOs fs) (Bvk μ r d : ℕ) : List (Tree → Prop) :=
  namedP fs (vsNames μ r d) (vsBsAt W Bvk μ r) (vsPs W)

/-- **`verify_sub`'s trees at the stack log `μ` and the rate `r`**: a flat node whose callees are
`vsTs` at some bus grind arm `d < 18` (the child's bus depth less `16`). -/
noncomputable def vsTsAny (fs : String → ℕ) (W : VsWordsOs fs) (Bvk μ r : ℕ) (t : Tree) : Prop :=
  ∃ d < 18, Budget.FlatShape coreProgram "verify_sub" (vsTs fs W Bvk μ r d) t

end
end LeanVM.Guest.B1.VerifySub
