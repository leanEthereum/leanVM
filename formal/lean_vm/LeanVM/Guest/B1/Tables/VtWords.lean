/-
  LeanVM.Guest.B1.Tables.VtWords

  `verify_tables`' words interface: what its bound needs of the frame sizes (`VtWords`) and of the weights
  (`VtWeights`), its bound over the bus depths and heights (`vtMax`) and its weight bound (`vtWeightB`).
-/

module

public import LeanVM.Guest.B1.Lmax
public import LeanVM.Guest.B1.Tables.VtC.Calls
public import LeanVM.Guest.B1.Tables.VtC.Kids
public import LeanVM.Guest.B1.Tables.FlatLiftT
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_tables`' words

Its callers name only this interface: `VtWords fs`, its callees' words facts at the frame sizes `fs` (its callees'
but the shared tables' and its rounds loop's, `Kf`; the shared tables', `Ksh`; the rounds loop's per iteration,
`K10`); `VtWeights ω`, the same at the weights `ω op`; `vtMax fs W`, its bound over the bus depths below `32` and
the heights below `31`; `vtWeightB ω Ww op`, its tree's weight bound. `VtWordsC` proves its completeness within
them.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **`verify_tables`' words facts** at the frame sizes `fs`: a loop's words per iteration, its run's one phantom
frame charged once by the `TotalLeOn … LoopPre` fact. -/
structure VtWords (fs : String → ℕ) : Type where
  Kf : String → ℕ
  Ksh : ℕ
  K10 : ℕ
  hKf : ∀ g ∈ vtKidS, g ≠ name% «verify_tables_loop0» →
      g ≠ name% «shared_selector_tables_loop0» → g ≠ "shared_selector_tables" →
    TotalLe coreProgram fs g (fun _ ↦ Kf g)
  hsh : TotalLeOn coreProgram fs "shared_selector_tables"
    (fun a ↦ ∃ n < 64, a.getD 5 0 = gen ^ n) (fun _ ↦ Ksh)
  h10 : TotalLeOn coreProgram fs name% «verify_tables_loop0» LoopPre (fun a ↦ logG (a.getD 1 0) *
      K10 + fs name% «verify_tables_loop0»)

/-- **`verify_tables`' weights facts** at the weights `ω op` (an opcode's instructions per frame). -/
structure VtWeights (ω : Opcode → String → ℕ) : Type where
  Kvw : Opcode → String → ℕ
  Wss : Opcode → ℕ
  Kw10 : Opcode → ℕ
  hKvw : ∀ op, ∀ g ∈ vtKidS, g ≠ name% «verify_tables_loop0» →
      g ≠ name% «shared_selector_tables_loop0» → g ≠ "shared_selector_tables" →
    WeightLe coreProgram (ω op) g (fun _ ↦ Kvw op g)
  hssw : ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "shared_selector_tables" →
    (∃ n < 64, args.getD 5 0 = gen ^ n) → t.Valid coreProgram rd args rets →
    t.BufsOk coreProgram → t.weight (ω op) ≤ Wss op
  h10w : ∀ op, Budget.LoopW (ω op) name% «verify_tables_loop0» (Kw10 op)

/-- `verify_tables`' bound at the bus depth `m` and the largest height `n`, from its words' numbers: its frame, its
own buffers, its callees and its skipped frames. -/
noncomputable def vtBnd (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 m n : ℕ) : ℕ :=
  fs "verify_tables" + (4190 + m) +
    ((vtBs Kf Ksh (vtRunB fs K10 n)).sum + ifFrames fs vtPre)

/-- `verify_tables`' bound over the bus depths below `32` and the heights below `31`, from its words' numbers. -/
@[irreducible] noncomputable def vtMaxOf (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 : ℕ) : ℕ :=
  lmax ((List.range 32).flatMap fun m ↦ (List.range 31).map (vtBnd fs Kf Ksh K10 m))

/-- **`verify_tables`' bound** over the bus depths below `32` and the heights below `31`. -/
noncomputable def vtMax (fs : String → ℕ) (W : VtWords fs) : ℕ := vtMaxOf fs W.Kf W.Ksh W.K10

theorem vtBnd_le_vtMax {fs : String → ℕ} (W : VtWords fs) {m n : ℕ} (hm : m < 32) (hn : n < 31) :
    vtBnd fs W.Kf W.Ksh W.K10 m n ≤ vtMax fs W := by
  unfold vtMax vtMaxOf
  exact le_lmax2 (vtBnd fs W.Kf W.Ksh W.K10) hm hn

/-- **`verify_tables`' weight bound** at `ω op`: its frame's and its calls' (`vtBs`). -/
noncomputable def vtWeightB {ω : Opcode → String → ℕ} (Ww : VtWeights ω) (op : Opcode) : ℕ :=
  ω op "verify_tables" + (vtBs (Ww.Kvw op) (Ww.Wss op) (32 * Ww.Kw10 op)).sum

end
end LeanVM.Guest.B1.Tables
