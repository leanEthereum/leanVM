module

public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Tables.ColumnClaims.Steps
public import NativeRustcVmArm.Tables.ColumnClaims.Blocks

/-!
# `table_column_claims` meets its contract

rustc unrolled the loop over the six tables: `b0` saves the registers and sets table `0`'s loop
registers (`entry`); each table's loop pushes its values' claims (`loop`, with its blocks `lb0` to
`lb5`), then the next table's setup block (`next`, `sb1` to `sb5`). A failed push (the claims do not
fit) goes to the exit with X0 zero (`failJ`, `fail24`, `fail30`); after the last table, the exit
with X0 one (`exit31`), the claims then `cs ++ tableColumnClaims evals` (`pre_six`).
-/

namespace NativeRustcVmArm.Tables.ColumnClaims

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.TableColumnClaims
open NativeRustcVm.Tables
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap)

public section

/-- All tables' claims after the last table's loop. -/
theorem claims_end {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW} {d : DataMem}
    {a : BitVec 64} (h6 : ev.size = 6)
    (h : ClaimsWAt d a (cs ++ (pre ev 5 (valsOf ev 5).size).toArray)) :
    ClaimsWAt d a (cs ++ tableColumnClaims ev) := by
  have hl : (valsOf ev 5).size = (claimsOf ev 5).length := (length_claimsOf 5).symm
  rwa [hl, pre_next, pre_six h6, Array.toArray_toList] at h

variable [Host] {k : Nat}

/-- **`table_column_claims` meets its contract.** -/
theorem tableColumnClaims_spec (hp : Placed code k)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW} :
    Spec (Labels.label NativeRustcVmArm.Vm.TableColumnClaims.entryLabel) (TableColumnClaimsPre ev cs)
      (TableColumnClaimsPost ev cs) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.TableColumnClaims.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.entryOffset) NativeRustcVmArm.Vm.TableColumnClaims.entry_at]
  show Eventually _ (Goal ev cs m0) _
  have h6 : ev.size = 6 := hpre.2.2.1.1
  have t5 : ∀ m, LoopAt R5 ev cs m0 5 0 m →
      Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b27Offset)⟩ := fun m h ↦
    loop hpush (lb5 hp) hpre (by decide) (fun _ h' ↦ exit31 hp hpre h'.fr (claims_end h6 h'.claims))
      (fun _ hfr h0 hn ↦ fail30 hp hpre hfr h0 hn) _ 0 m rfl h
  have t4 : ∀ m, LoopAt R04 ev cs m0 4 0 m →
      Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b21Offset)⟩ := fun m h ↦
    loop hpush (lb4 hp) hpre (by decide)
      (fun _ h' ↦ next hpre (i := 4) (by decide) (sb5 hp) rfl t5 h')
      (fun _ hfr _ hn ↦ fail24 hp hpre hfr hn) _ 0 m rfl h
  have t3 : ∀ m, LoopAt R04 ev cs m0 3 0 m →
      Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b16Offset)⟩ := fun m h ↦
    loop hpush (lb3 hp) hpre (by decide)
      (fun _ h' ↦ next hpre (i := 3) (by decide) (sb4 hp) rfl t4 h')
      (fun _ hfr _ hn ↦ failJ hp hpre (b19_in_code.trans hp.1 (by simp [b19]))
        (by rw [Bus.after_eq run_b19]; exact run_b19) ok_b19 hfr hn) _ 0 m rfl h
  have t2 : ∀ m, LoopAt R04 ev cs m0 2 0 m →
      Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b11Offset)⟩ := fun m h ↦
    loop hpush (lb2 hp) hpre (by decide)
      (fun _ h' ↦ next hpre (i := 2) (by decide) (sb3 hp) rfl t3 h')
      (fun _ hfr _ hn ↦ failJ hp hpre (b14_in_code.trans hp.1 (by simp [b14]))
        (by rw [Bus.after_eq run_b14]; exact run_b14) ok_b14 hfr hn) _ 0 m rfl h
  have t1 : ∀ m, LoopAt R04 ev cs m0 1 0 m →
      Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b6Offset)⟩ := fun m h ↦
    loop hpush (lb1 hp) hpre (by decide)
      (fun _ h' ↦ next hpre (i := 1) (by decide) (sb2 hp) rfl t2 h')
      (fun _ hfr _ hn ↦ failJ hp hpre (b9_in_code.trans hp.1 (by simp [b9]))
        (by rw [Bus.after_eq run_b9]; exact run_b9) ok_b9 hfr hn) _ 0 m rfl h
  refine entry hp hpre fun m h ↦ ?_
  exact loop hpush (lb0 hp) hpre (by decide)
    (fun _ h' ↦ next hpre (i := 0) (by decide) (sb1 hp) rfl t1 h')
    (fun _ hfr _ hn ↦ failJ hp hpre (b4_in_code.trans hp.1 (by simp [b4]))
      (by rw [Bus.after_eq run_b4]; exact run_b4) ok_b4 hfr hn) _ 0 m rfl h

end

end NativeRustcVmArm.Tables.ColumnClaims
