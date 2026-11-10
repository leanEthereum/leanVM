/-
  LeanVM.Guest.B1.VerifySub.WordsB

  `verify_sub`'s callees' words facts (`VsWords`) and `verify_tables`' and the terminal's weight
  bounds (`vtWB`, `termWB`), apart from `verify_sub`'s completeness.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Calls
public import LeanVM.Guest.B1.Tables.VtC.Kids
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.B1.Terminal.TermWeight

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

/-! ## The maxima -/

/-- The largest of a list. -/
def lmax (l : List ℕ) : ℕ := l.foldl max 0

theorem foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], _ => ⟨le_rfl, fun _ h => by simp at h⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a y)
    refine ⟨le_trans (le_max_left a y) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right a x) h1
    · exact h2 x hx

theorem le_lmax {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ lmax l := (foldl_max_ge l 0).2 x h

theorem le_lmax2 (f : ℕ → ℕ → ℕ) {A B a b : ℕ} (ha : a < A) (hb : b < B) :
    f a b ≤ lmax ((List.range A).flatMap fun a ↦ (List.range B).map (f a)) :=
  le_lmax (List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩)

/-! ## The statically bounded callees -/

/-- `squeeze_point_from`'s arms, by the stack log `22 .. 28`. -/
def squeezeNames : List String :=
  ["squeeze_point_from__L22", "squeeze_point_from__L23", "squeeze_point_from__L24",
    "squeeze_point_from__L25", "squeeze_point_from__L26", "squeeze_point_from__L27",
    "squeeze_point_from__L28"]

/-- `bus_grind_check`'s arms, by the push depth's excess `0 .. 17`. -/
def busGrindNames : List String :=
  ["bus_grind_check__L0", "bus_grind_check__L1", "bus_grind_check__L2", "bus_grind_check__L3",
    "bus_grind_check__L4", "bus_grind_check__L5", "bus_grind_check__L6", "bus_grind_check__L7",
    "bus_grind_check__L8", "bus_grind_check__L9", "bus_grind_check__L10", "bus_grind_check__L11",
    "bus_grind_check__L12", "bus_grind_check__L13", "bus_grind_check__L14", "bus_grind_check__L15",
    "bus_grind_check__L16", "bus_grind_check__L17"]

/-- **`verify_sub`'s statically bounded callees** but `g_power_of_word`, `log2_ceil_in_the_exponent`
and `certify_placement`: the grind checks, the opening message and the two dispatches' arms. -/
def vsStaticS : List String :=
  ["grind_check__L15", "opening_message__L1_L1", "grind_check__L14"] ++ squeezeNames ++ busGrindNames

/-- A dispatch's bound: the largest of its arms'. -/
def armMax (K : String → ℕ) (names : List String) : ℕ := lmax (names.map K)

theorem le_armMax (K : String → ℕ) {names : List String} {f : String} (h : f ∈ names) :
    K f ≤ armMax K names :=
  le_lmax (List.mem_map.2 ⟨f, h, rfl⟩)

/-! ## The words facts -/

/-- **`verify_sub`'s callees' words facts**, at the frame sizes `fs`: `g_power_of_word`'s (`Bg`),
the statically bounded callees' (`Kst`), `verify_bus_gkr`'s loops and rounds (`K29`, `R`, `K8`),
`verify_tables`' callees (`Kf`, `Ksh`, `K10`), `ring_switch_target`'s loop (`B14`),
the terminal's pure callees (`Beqc`,
`K15`, `Bcs`, `Brs`) — a loop's words per iteration, its run's one phantom frame charged once by the
`TotalLeOn … LoopPre` fact; and, at the weights `ωv op` (an opcode's instructions per frame), the
weights of `verify_tables`' callees (`Kvw`, `Wss`, `Kw10`) and of the terminal's (`Weqc`, `W15`,
`Wst`, `Wcs`, `Wrsw`), which bound those two callees' trees (`vtWB`, `termWB`). -/
structure VsWords (fs : String → ℕ) : Type where
  Bg : ℕ
  hg : TotalLe coreProgram fs "g_power_of_word" fun _ ↦ Bg
  Kst : String → ℕ
  hst : ∀ g ∈ vsStaticS, TotalLe coreProgram fs g fun _ ↦ Kst g
  K29 : ℕ
  R : ℕ
  K8 : ℕ
  h29 : TotalLeOn coreProgram fs "__loop36" LoopPre
    (fun a ↦ logG (a.getD 1 0) * K29 + fs "__loop36")
  hR : ∀ n ∈ [0, 1, 2, 4, 6], TotalLe coreProgram fs (Tables.lName "gkr_rounds" n) (fun _ ↦ R)
  h8 : TotalLeOn coreProgram fs "__loop7" LoopPre (fun a ↦ logG (a.getD 1 0) * K8 + fs "__loop7")
  Kf : String → ℕ
  Ksh : ℕ
  K10 : ℕ
  hKf : ∀ g ∈ Tables.vtKidS, g ≠ "__loop9" → g ≠ "__loop8" → g ≠ "shared_selector_tables" →
    TotalLe coreProgram fs g (fun _ ↦ Kf g)
  hsh : TotalLeOn coreProgram fs "shared_selector_tables"
    (fun a ↦ ∃ n < 64, a.getD 5 0 = gen ^ n) (fun _ ↦ Ksh)
  h10 : TotalLeOn coreProgram fs "__loop9" LoopPre (fun a ↦ logG (a.getD 1 0) * K10 + fs "__loop9")
  B14 : ℕ
  hl14 : TotalLeOn coreProgram fs "__loop13" (fun a ↦ a.getD 0 0 = 1) fun _ ↦ B14
  Beqc : ℕ
  K15 : ℕ
  Bcs : ℕ
  Brs : ℕ
  hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ ↦ Beqc
  hL15 : TotalLeOn coreProgram fs "__loop14" LoopPre
    fun a ↦ logG (a.getD 1 0) * K15 + fs "__loop14"
  hCsF : ∀ κ' < 29, fs (Tables.lName "column_selector" κ') ≤ Bcs
  hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 3 0 = gen ^ c)
    fun _ ↦ Brs
  ωv : Opcode → String → ℕ
  Kvw : Opcode → String → ℕ
  Wss : Opcode → ℕ
  Kw10 : Opcode → ℕ
  hKvw : ∀ op, ∀ g ∈ Tables.vtKidS, g ≠ "__loop9" → g ≠ "__loop8" → g ≠ "shared_selector_tables" →
    WeightLe coreProgram (ωv op) g (fun _ ↦ Kvw op g)
  hssw : ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "shared_selector_tables" →
    (∃ n < 64, args.getD 5 0 = gen ^ n) → t.Valid coreProgram rd args rets →
    t.BufsOk coreProgram → t.weight (ωv op) ≤ Wss op
  h10w : ∀ op, Budget.LoopW (ωv op) "__loop9" (Kw10 op)
  Weqc : Opcode → ℕ
  W15 : Opcode → ℕ
  Wst : Opcode → ℕ
  Wcs : Opcode → ℕ
  Wrsw : Opcode → ℕ
  hEqcW : ∀ op, WeightLe coreProgram (ωv op) "eq_prefix_chain" fun _ ↦ Weqc op
  hStW : ∀ op, WeightLe coreProgram (ωv op) "selector_tables" fun _ ↦ Wst op
  hCsW : ∀ op, ∀ κ' < 29, WeightLe coreProgram (ωv op) (Tables.lName "column_selector" κ')
    fun _ ↦ Wcs op
  h15W : ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "__loop14" →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
    t.total fs ≤ (32 * K15 + fs "__loop14") → t.weight (ωv op) ≤ W15 op
  hrswW : ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
    t.total fs ≤ fs "ring_switch_weight" + 2240 + Brs → t.weight (ωv op) ≤ Wrsw op

/-! ## The bounds -/

/-- **`verify_tables`' weight bound** at `W.ωv op`: its frame's and its calls' (`vtBs`). -/
noncomputable def vtWB {fs : String → ℕ} (W : VsWords fs) (op : Opcode) : ℕ :=
  W.ωv op "verify_tables" + (Tables.vtBs (W.Kvw op) (W.Wss op) (28 * W.Kw10 op)).sum

/-- **The terminal's weight bound** at `W.ωv op`: its frame's and its calls' (`termWs`). -/
noncomputable def termWB {fs : String → ℕ} (W : VsWords fs) (op : Opcode) : ℕ :=
  W.ωv op "check_opening_terminal" + (termWs W.Weqc W.W15 W.Wst W.Wcs W.Wrsw op).sum

end
end LeanVM.Guest.B1.VerifySub
