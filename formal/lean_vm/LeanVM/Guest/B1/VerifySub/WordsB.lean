/-
  LeanVM.Guest.B1.VerifySub.WordsB

  `verify_sub`'s callees' words facts (`VsWords`) and `verify_tables`' and the terminal's weight
  bounds (`vtWB`, `termWB`), apart from `verify_sub`'s completeness.
-/

module

public import LeanVM.Guest.B1.Tables.VtWords
public import LeanVM.Guest.B1.Gkr.VbgWords
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.B1.Terminal.TermWeight
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.LitRef

/-!
# `verify_sub`'s callees' words

What the budget's instances (`Count/VsWords`, `Count/VsWB`) and `verify_tables`' bounded
completeness need of `VerifySub/CompleteB`, without its proof's imports.

`VsWords fs`: the words facts of `verify_sub`'s callees' pure callees, at the frame sizes `fs`
(`TotalLe`, `TotalLeOn`), with their constants, and the weights of `verify_tables`' and the
terminal's callees. `vsStaticS`: the statically bounded callees `Kst` bounds, the grind checks,
the opening message and the arms of the `squeeze_point_from` and `bus_grind_check` dispatches
(`armMax`: a dispatch's bound). `VerifySub/CompleteB` adds `open_stacked`'s facts (`VsWordsOs`)
and the bounds over the sixteen callees.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-! ## The statically bounded callees -/

/-- `squeeze_point_from`'s arms, by the stack log `20 .. 30`. -/
def squeezeNames : List String :=
  ["squeeze_point_from__L20", "squeeze_point_from__L21", "squeeze_point_from__L22", "squeeze_point_from__L23", "squeeze_point_from__L24", "squeeze_point_from__L25", "squeeze_point_from__L26", "squeeze_point_from__L27", "squeeze_point_from__L28", "squeeze_point_from__L29", "squeeze_point_from__L30"]

/-- `bus_grind_check`'s arms, by the push depth's excess `0 .. 13`. -/
def busGrindNames : List String :=
  ["bus_grind_check__L0", "bus_grind_check__L1", "bus_grind_check__L2", "bus_grind_check__L3", "bus_grind_check__L4", "bus_grind_check__L5", "bus_grind_check__L6", "bus_grind_check__L7", "bus_grind_check__L8", "bus_grind_check__L9", "bus_grind_check__L10", "bus_grind_check__L11", "bus_grind_check__L12", "bus_grind_check__L13"]

/-- **`verify_sub`'s statically bounded callees** but `g_power_of_word`, `log2_ceil_in_the_exponent`
and `certify_placement`: the opening message and the two dispatches' arms. -/
def vsStaticS : List String :=
  ["opening_message__L1_L1"] ++ squeezeNames ++ busGrindNames

/-- A dispatch's bound: the largest of its arms'. -/
def armMax (K : String → ℕ) (names : List String) : ℕ := lmax (names.map K)

theorem le_armMax (K : String → ℕ) {names : List String} {f : String} (h : f ∈ names) :
    K f ≤ armMax K names :=
  le_lmax (List.mem_map.2 ⟨f, h, rfl⟩)

/-! ## The words facts -/

/-- **`verify_sub`'s callees' words facts**, at the frame sizes `fs`: `g_power_of_word`'s (`Bg`),
the statically bounded callees' (`Kst`), `verify_bus_gkr`'s and `verify_tables`' words interfaces (`vbg`,
`vt`), `ring_switch_target`'s loop (`B14`),
the terminal's pure callees (`Beqc`,
`K15`, `Bcs`, `Brs`) — a loop's words per iteration, its run's one phantom frame charged once by the
`TotalLeOn … LoopPre` fact; and, at the weights `ωv op` (an opcode's instructions per frame), the
weights interface of `verify_tables` (`vtW`) and the weights of the terminal's callees (`Weqc`, `W15`,
`Wst`, `Wcs`, `Wrsw`), which bound those two callees' trees (`vtWB`, `termWB`). -/
structure VsWords (fs : String → ℕ) : Type where
  Bg : ℕ
  hg : TotalLe coreProgram fs "g_power_of_word" fun _ ↦ Bg
  Kst : String → ℕ
  hst : ∀ g ∈ vsStaticS, TotalLe coreProgram fs g fun _ ↦ Kst g
  vbg : Tables.VbgWords fs
  vt : Tables.VtWords fs
  B14 : ℕ
  hl14 : TotalLeOn coreProgram fs name% «ring_switch_target_loop0» (fun a ↦ a.getD 0 0 = 1) fun _ ↦
      B14
  Beqc : ℕ
  K15 : ℕ
  Bcs : ℕ
  Brs : ℕ
  hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ ↦ Beqc
  hL15 : TotalLeOn coreProgram fs name% «check_opening_terminal_loop0» LoopPre
    fun a ↦ logG (a.getD 1 0) * K15 + fs name% «check_opening_terminal_loop0»
  hCsF : ∀ κ' < 31, fs (Tables.lName "column_selector" κ') ≤ Bcs
  hrs : RsBound fs Brs
  ωv : Opcode → String → ℕ
  vtW : Tables.VtWeights ωv
  Weqc : Opcode → ℕ
  W15 : Opcode → ℕ
  Wst : Opcode → ℕ
  Wcs : Opcode → ℕ
  Wrsw : Opcode → ℕ
  hEqcW : ∀ op, WeightLe coreProgram (ωv op) "eq_prefix_chain" fun _ ↦ Weqc op
  hStW : ∀ op, WeightLe coreProgram (ωv op) "selector_tables" fun _ ↦ Wst op
  hCsW : ∀ op, ∀ κ' < 31, WeightLe coreProgram (ωv op) (Tables.lName "column_selector" κ')
    fun _ ↦ Wcs op
  h15W : ∀ op (rd : Reader) (t : Tree) (args rets : List E),
      t.name = name% «check_opening_terminal_loop0» →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
    t.total fs ≤ (32 * K15 + fs name% «check_opening_terminal_loop0») → t.weight (ωv op) ≤ W15 op
  hrswW : ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
    t.total fs ≤ fs "ring_switch_weight" + lit% termRswChain + Brs → t.weight (ωv op) ≤ Wrsw op

/-! ## The bounds -/

/-- **`verify_tables`' weight bound** at `W.ωv op`. -/
noncomputable def vtWB {fs : String → ℕ} (W : VsWords fs) (op : Opcode) : ℕ :=
  Tables.vtWeightB W.vtW op

/-- **The terminal's weight bound** at `W.ωv op`: its frame's and its calls' (`termWs`). -/
noncomputable def termWB {fs : String → ℕ} (W : VsWords fs) (op : Opcode) : ℕ :=
  W.ωv op "check_opening_terminal" + (termWs W.Weqc W.W15 W.Wst W.Wcs W.Wrsw op).sum

end
end LeanVM.Guest.B1.VerifySub
