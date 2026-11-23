/-
  LeanVM.Guest.Count.Fn.check_opening_terminal

  The terminal's callees' weights at the xmss arm's weights (`termWeqc`, `termW15`, `termWst`, `kCsW`,
  `termWrsw`), from the `W` count certificates (`kuSB`) and the ratios of `check_opening_terminal_loop0` and
  `ring_switch_weight` (`Count/RatioV`), and its weight bound as one closed form (`termWForm`, `termW_form`).
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Count.StaticW
public import LeanVM.Guest.Count.RatioV
public import LeanVM.Guest.B1.Lmax
public import LeanVM.Guest.B1.Terminal.TermWeight
import LeanVM.Guest.LitRef

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- The column selectors' weights, at most. -/
noncomputable def kCsW (op : Opcode) : ℕ :=
  B1.lmax ((List.range 31).map fun κ => kuSB op (B1.Tables.lName "column_selector" κ))

theorem cs_okW (op : Opcode) : (List.range 31).all (fun κ =>
    kuOkB op (idx% column_selector__L0 + κ) (B1.Tables.lName "column_selector" κ)) = true := by
  cases op <;> decide +kernel

theorem cs_weightLe (op : Opcode) : ∀ κ < 31, WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op)
    (B1.Tables.lName "column_selector" κ) (fun _ => kCsW op) := by
  intro κ hκ rd t args rets hn hv hb
  refine (kuSB_weightLe (List.all_eq_true.mp (cs_okW op) κ (List.mem_range.mpr hκ)) rd t args rets hn hv hb).trans ?_
  exact B1.le_lmax (List.mem_map.mpr ⟨κ, List.mem_range.mpr hκ, rfl⟩)

/-- `eq_prefix_chain`'s weight. -/
noncomputable def termWeqc (op : Opcode) : ℕ := kuSB op "eq_prefix_chain"

/-- `selector_tables`' weight. -/
noncomputable def termWst (op : Opcode) : ℕ := kuSB op "selector_tables"

/-- `check_opening_terminal_loop0`'s weight, by its ratio at its words. -/
noncomputable def termW15 (op : Opcode) : ℕ :=
  krVl15A op * max (B2C.fs (name% check_opening_terminal_loop0)) (32 * 38) / 1000

/-- **A cap on `rs_eq_run`'s words under `ring_switch_weight`** (`Brs`), at which `ring_switch_weight`'s ratio
bounds its weight: what its rule file reads. -/
def rswBrsCap : ℕ := 16433

/-- `ring_switch_weight`'s weight, by its ratio at its words. -/
noncomputable def termWrsw (op : Opcode) : ℕ :=
  krVrswA op * (B2C.fs "ring_switch_weight" + lit% B1.VerifySub.termRswChain + lit% rswBrsCap) / 1000

/-- **The terminal's weight bound as one closed form** in an opcode's frame weights `ω`, the `W`
certificates' bounds `KB` (`kuSB` at the opcode), the frame sizes `fs` and the two ratios at the opcode:
what `Count/VsWB` instantiates. -/
noncomputable def termWForm (ω KB fs : String → ℕ) (r15 rrsw : ℕ) : ℕ :=
  ω "check_opening_terminal" + (B1.VerifySub.termWs (fun _ : Unit => KB "eq_prefix_chain")
    (fun _ => r15 * max (fs (name% check_opening_terminal_loop0)) (32 * 38) / 1000)
    (fun _ => KB "selector_tables")
    (fun _ => B1.lmax ((List.range 31).map fun κ => KB (B1.Tables.lName "column_selector" κ)))
    (fun _ => rrsw * (fs "ring_switch_weight" + lit% B1.VerifySub.termRswChain + lit% rswBrsCap) / 1000) ()).sum

theorem termW_form (op : Opcode) : B2C.ωArm B2C.xmssArmC op "check_opening_terminal" +
    (B1.VerifySub.termWs termWeqc termW15 termWst kCsW termWrsw op).sum =
    termWForm (B2C.ωArm B2C.xmssArmC op) (kuSB op) B2C.fs (krVl15A op) (krVrswA op) := rfl

end
end LeanVM.Guest.Count
