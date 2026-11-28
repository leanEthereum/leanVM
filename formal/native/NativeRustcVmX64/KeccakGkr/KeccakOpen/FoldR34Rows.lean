module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldRow
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Entry2
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecL
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecS
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecR35
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {cx : Cx} {rows : Array (Array EW)}

theorem row3_0 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b58Offset))
    (hh : Row cx m0 rows 3 0 (varsOf cx.sl 3 0) [(.r13, P)] W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b63Offset) ∧
      Row cx m0 rows 3 1 (varsOf cx.sl 3 0) k58 W6 st'.data) st := by
  refine (row_run (t := 3) (i := 0) (vars := varsOf cx.sl 3 0) (dst := 0)
    (ks0 := [(.r13, P)]) (ks1 := kCopy k58) (ks2 := k58) (ks := k58)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .r12) (cx1 := .rbp) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 8) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b58_in_code b59_in_code b60_in_code b61_in_code b62_in_code
    (by simp [b58]) (by simp [b59]) (by simp [b60]) (by simp [b61]) (by simp [b62])
    NativeRustcVmX64.Vm.KeccakOpen.b58_next NativeRustcVmX64.Vm.KeccakOpen.b59_next NativeRustcVmX64.Vm.KeccakOpen.b60_next NativeRustcVmX64.Vm.KeccakOpen.b61_next
    (label_of_infix hp b61_in_code rfl) x58 x59 x60 x61 x62
    f58.2 f59.2 f60.2 f61.2 f62.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b62_next), hh'⟩

theorem row3_1 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b63Offset))
    (hh : Row cx m0 rows 3 1 (varsOf cx.sl 3 0) k58 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b68Offset) ∧
      Row cx m0 rows 3 2 (varsOf cx.sl 3 0) k58 W6 st'.data) st := by
  refine (row_run (t := 3) (i := 1) (vars := varsOf cx.sl 3 0) (dst := 0)
    (ks0 := k58) (ks1 := kCopy k58) (ks2 := k58) (ks := k58)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .r12) (cx1 := .rbp) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 1032) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b63_in_code b64_in_code b65_in_code b66_in_code b67_in_code
    (by simp [b63]) (by simp [b64]) (by simp [b65]) (by simp [b66]) (by simp [b67])
    NativeRustcVmX64.Vm.KeccakOpen.b63_next NativeRustcVmX64.Vm.KeccakOpen.b64_next NativeRustcVmX64.Vm.KeccakOpen.b65_next NativeRustcVmX64.Vm.KeccakOpen.b66_next
    (label_of_infix hp b66_in_code rfl) x63 x64 x65 x66 x67
    f63.2 f64.2 f65.2 f66.2 f67.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b67_next), hh'⟩

theorem row3_2 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b68Offset))
    (hh : Row cx m0 rows 3 2 (varsOf cx.sl 3 0) k58 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b73Offset) ∧
      Row cx m0 rows 3 3 (varsOf cx.sl 3 0) k58 W6 st'.data) st := by
  refine (row_run (t := 3) (i := 2) (vars := varsOf cx.sl 3 0) (dst := 0)
    (ks0 := k58) (ks1 := kCopy k58) (ks2 := k58) (ks := k58)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .r12) (cx1 := .rbp) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 2048) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b68_in_code b69_in_code b70_in_code b71_in_code b72_in_code
    (by simp [b68]) (by simp [b69]) (by simp [b70]) (by simp [b71]) (by simp [b72])
    NativeRustcVmX64.Vm.KeccakOpen.b68_next NativeRustcVmX64.Vm.KeccakOpen.b69_next NativeRustcVmX64.Vm.KeccakOpen.b70_next NativeRustcVmX64.Vm.KeccakOpen.b71_next
    (label_of_infix hp b71_in_code rfl) x68 x69 x70 x71 x72
    f68.2 f69.2 f70.2 f71.2 f72.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b72_next), hh'⟩

theorem row3_3 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b73Offset))
    (hh : Row cx m0 rows 3 3 (varsOf cx.sl 3 0) k58 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b78Offset) ∧
      Row cx m0 rows 3 4 (varsOf cx.sl 3 0) k58 W6 st'.data) st := by
  refine (row_run (t := 3) (i := 3) (vars := varsOf cx.sl 3 0) (dst := 0)
    (ks0 := k58) (ks1 := kCopy k58) (ks2 := k58) (ks := k58)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .r12) (cx1 := .rbp) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 3072) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b73_in_code b74_in_code b75_in_code b76_in_code b77_in_code
    (by simp [b73]) (by simp [b74]) (by simp [b75]) (by simp [b76]) (by simp [b77])
    NativeRustcVmX64.Vm.KeccakOpen.b73_next NativeRustcVmX64.Vm.KeccakOpen.b74_next NativeRustcVmX64.Vm.KeccakOpen.b75_next NativeRustcVmX64.Vm.KeccakOpen.b76_next
    (label_of_infix hp b76_in_code rfl) x73 x74 x75 x76 x77
    f73.2 f74.2 f75.2 f76.2 f77.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b77_next), hh'⟩

theorem row4_0 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b78Offset))
    (hh : Row cx m0 rows 4 0 (varsOf cx.sl 4 0) [(.r13, P)] W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b83Offset) ∧
      Row cx m0 rows 4 1 (varsOf cx.sl 4 0) k78 W6 st'.data) st := by
  refine (row_run (t := 4) (i := 0) (vars := varsOf cx.sl 4 0) (dst := 0)
    (ks0 := [(.r13, P)]) (ks1 := kCopy k78) (ks2 := k78) (ks := k78)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .r12) (cx1 := .r13) (lo0 := .r14) (lo1 := .r15)
    (dr := .rbp) (s0 := 8) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b78_in_code b79_in_code b80_in_code b81_in_code b82_in_code
    (by simp [b78]) (by simp [b79]) (by simp [b80]) (by simp [b81]) (by simp [b82])
    NativeRustcVmX64.Vm.KeccakOpen.b78_next NativeRustcVmX64.Vm.KeccakOpen.b79_next NativeRustcVmX64.Vm.KeccakOpen.b80_next NativeRustcVmX64.Vm.KeccakOpen.b81_next
    (label_of_infix hp b81_in_code rfl) x78 x79 x80 x81 x82
    f78.2 f79.2 f80.2 f81.2 f82.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .rbp) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b82_next), hh'⟩

theorem row4_1 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b83Offset))
    (hh : Row cx m0 rows 4 1 (varsOf cx.sl 4 0) k78 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b88Offset) ∧
      Row cx m0 rows 4 2 (varsOf cx.sl 4 0) k78 W6 st'.data) st := by
  refine (row_run (t := 4) (i := 1) (vars := varsOf cx.sl 4 0) (dst := 0)
    (ks0 := k78) (ks1 := kCopy k78) (ks2 := k78) (ks := k78)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .r12) (cx1 := .r13) (lo0 := .r14) (lo1 := .r15)
    (dr := .rbp) (s0 := 1032) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b83_in_code b84_in_code b85_in_code b86_in_code b87_in_code
    (by simp [b83]) (by simp [b84]) (by simp [b85]) (by simp [b86]) (by simp [b87])
    NativeRustcVmX64.Vm.KeccakOpen.b83_next NativeRustcVmX64.Vm.KeccakOpen.b84_next NativeRustcVmX64.Vm.KeccakOpen.b85_next NativeRustcVmX64.Vm.KeccakOpen.b86_next
    (label_of_infix hp b86_in_code rfl) x83 x84 x85 x86 x87
    f83.2 f84.2 f85.2 f86.2 f87.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .rbp) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b87_next), hh'⟩

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
