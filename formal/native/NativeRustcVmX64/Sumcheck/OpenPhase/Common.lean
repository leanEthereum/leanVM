module

public import NativeRustcVmX64.Sumcheck.Ctx
public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# Helpers of `open_phase`'s and `query_openings`' proofs (x86-64)

`KeepAll S`, `KeepBut rs S`: every register but RSP (and `rs`) keeps its atom (`KeepAll.atom`;
`KeepAll.regs`: the machine's registers kept by such a block).
-/

namespace NativeRustcVmX64.Sumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript

@[expose] public section

/-- Every register but RSP is its atom. -/
def KeepAll (S : SState) : Bool := allRegs.all fun r ↦ r == .rsp || S.reg r == some (.reg r)

/-- Every register but RSP and those of `rs` is its atom. -/
def KeepBut (rs : List Reg64) (S : SState) : Bool :=
  allRegs.all fun r ↦ r == .rsp || rs.contains r || S.reg r == some (.reg r)

end

public section

theorem KeepAll.atom {S : SState} (h : KeepAll S = true) {r : Reg64} (hr : r ≠ .rsp) :
    S.reg r = some (.reg r) := by
  unfold KeepAll at h
  rw [List.all_eq_true] at h
  rcases Bool.or_eq_true_iff.mp (h r (mem_allRegs r)) with h1 | h1
  · exact absurd (Reg64.eq_of_beq h1) hr
  · exact beq_iff_eq.mp h1

theorem KeepBut.atom {rs : List Reg64} {S : SState} (h : KeepBut rs S = true) {r : Reg64}
    (hr : r ≠ .rsp) (hrs : rs.contains r = false) : S.reg r = some (.reg r) := by
  unfold KeepBut at h
  rw [List.all_eq_true] at h
  rcases Bool.or_eq_true_iff.mp (h r (mem_allRegs r)) with h1 | h1
  · rcases Bool.or_eq_true_iff.mp h1 with h2 | h2
    · exact absurd (Reg64.eq_of_beq h2) hr
    · rw [hrs] at h2; cases h2
  · exact beq_iff_eq.mp h1

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- A block keeping every register but RSP: the machine's registers kept. -/
theorem KeepAll.regs (h : KeepAll S = true) {m0 : MachineData} {rs : List (BitVec 64 × Nat)}
    {vs : Nat → BitVec 64} {ret : BitVec 64} (hm : Match (Env.ofMachine m0 rs vs ret) S m)
    {r : Reg64} (hr : r ≠ .rsp) : reg m r = reg m0 r :=
  hm.regs r _ (KeepAll.atom h hr)

theorem KeepBut.regs {rs' : List Reg64} (h : KeepBut rs' S = true) {m0 : MachineData}
    {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {ret : BitVec 64}
    (hm : Match (Env.ofMachine m0 rs vs ret) S m) {r : Reg64} (hr : r ≠ .rsp)
    (hrs : rs'.contains r = false) : reg m r = reg m0 r :=
  hm.regs r _ (KeepBut.atom h hr hrs)

end

end NativeRustcVmX64.Sumcheck
