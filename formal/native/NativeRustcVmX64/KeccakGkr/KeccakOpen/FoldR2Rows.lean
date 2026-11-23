module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldRow
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Entry2
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecL
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecS
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecR2
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {cx : Cx} {rows : Array (Array EW)}

theorem row2_0 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b18Offset))
    (hh : Row cx m0 rows 2 0 (varsOf cx.sl 2 0) [] [] st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b23Offset) ∧
      Row cx m0 rows 2 1 (varsOf cx.sl 2 0) k18 w19 st'.data) st := by
  refine (row_run (t := 2) (i := 0) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := []) (ks1 := kCopy k18) (ks2 := k18) (ks := k18)
    (ws0 := []) (ws1 := []) (ws2 := w19) (ws := w19)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 8) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide)
    (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b18_in_code b19_in_code b20_in_code b21_in_code b22_in_code
    (by simp [b18]) (by simp [b19]) (by simp [b20]) (by simp [b21]) (by simp [b22])
    NativeRustcVmX64.Vm.KeccakOpen.b18_next NativeRustcVmX64.Vm.KeccakOpen.b19_next NativeRustcVmX64.Vm.KeccakOpen.b20_next NativeRustcVmX64.Vm.KeccakOpen.b21_next
    (label_of_infix hp b21_in_code rfl) x18 x19 x20 x21 x22
    f18.2 f19.2 f20.2 f21.2 f22.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b22_next), hh'⟩

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
