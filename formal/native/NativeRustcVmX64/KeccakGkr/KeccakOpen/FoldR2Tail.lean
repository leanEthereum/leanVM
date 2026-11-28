module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldR2Rows
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {cx : Cx} {rows : Array (Array EW)}

theorem row2_1 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b23Offset))
    (hh : Row cx m0 rows 2 1 (varsOf cx.sl 2 0) k18 w19 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b28Offset) ∧
      Row cx m0 rows 2 2 (varsOf cx.sl 2 0) k18 w24 st'.data) st := by
  refine (row_run (t := 2) (i := 1) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := kCopy k18) (ks2 := k18) (ks := k18)
    (ws0 := w19) (ws1 := w23) (ws2 := w24) (ws := w24)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 1032) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b23_in_code b24_in_code b25_in_code b26_in_code b27_in_code
    (by simp [b23]) (by simp [b24]) (by simp [b25]) (by simp [b26]) (by simp [b27])
    NativeRustcVmX64.Vm.KeccakOpen.b23_next NativeRustcVmX64.Vm.KeccakOpen.b24_next NativeRustcVmX64.Vm.KeccakOpen.b25_next NativeRustcVmX64.Vm.KeccakOpen.b26_next
    (label_of_infix hp b26_in_code rfl) x23 x24 x25 x26 x27
    f23.2 f24.2 f25.2 f26.2 f27.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b27_next), hh'⟩

theorem row2_2 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b28Offset))
    (hh : Row cx m0 rows 2 2 (varsOf cx.sl 2 0) k18 w24 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b33Offset) ∧
      Row cx m0 rows 2 3 (varsOf cx.sl 2 0) k18 w29 st'.data) st := by
  refine (row_run (t := 2) (i := 2) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := kCopy k18) (ks2 := k18) (ks := k18)
    (ws0 := w24) (ws1 := w28) (ws2 := w29) (ws := w29)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 2048) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b28_in_code b29_in_code b30_in_code b31_in_code b32_in_code
    (by simp [b28]) (by simp [b29]) (by simp [b30]) (by simp [b31]) (by simp [b32])
    NativeRustcVmX64.Vm.KeccakOpen.b28_next NativeRustcVmX64.Vm.KeccakOpen.b29_next NativeRustcVmX64.Vm.KeccakOpen.b30_next NativeRustcVmX64.Vm.KeccakOpen.b31_next
    (label_of_infix hp b31_in_code rfl) x28 x29 x30 x31 x32
    f28.2 f29.2 f30.2 f31.2 f32.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b32_next), hh'⟩

theorem row2_3 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b33Offset))
    (hh : Row cx m0 rows 2 3 (varsOf cx.sl 2 0) k18 w29 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b38Offset) ∧
      Row cx m0 rows 2 4 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 3) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := kCopy k18) (ks2 := k18) (ks := k18)
    (ws0 := w29) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 3072) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b33_in_code b34_in_code b35_in_code b36_in_code b37_in_code
    (by simp [b33]) (by simp [b34]) (by simp [b35]) (by simp [b36]) (by simp [b37])
    NativeRustcVmX64.Vm.KeccakOpen.b33_next NativeRustcVmX64.Vm.KeccakOpen.b34_next NativeRustcVmX64.Vm.KeccakOpen.b35_next NativeRustcVmX64.Vm.KeccakOpen.b36_next
    (label_of_infix hp b36_in_code rfl) x33 x34 x35 x36 x37
    f33.2 f34.2 f35.2 f36.2 f37.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b37_next), hh'⟩

theorem row2_4 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b38Offset))
    (hh : Row cx m0 rows 2 4 (varsOf cx.sl 2 0) k18 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b43Offset) ∧
      Row cx m0 rows 2 5 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 4) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := kCopy k18) (ks2 := k18) (ks := k18)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 4096) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b38_in_code b39_in_code b40_in_code b41_in_code b42_in_code
    (by simp [b38]) (by simp [b39]) (by simp [b40]) (by simp [b41]) (by simp [b42])
    NativeRustcVmX64.Vm.KeccakOpen.b38_next NativeRustcVmX64.Vm.KeccakOpen.b39_next NativeRustcVmX64.Vm.KeccakOpen.b40_next NativeRustcVmX64.Vm.KeccakOpen.b41_next
    (label_of_infix hp b41_in_code rfl) x38 x39 x40 x41 x42
    f38.2 f39.2 f40.2 f41.2 f42.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b42_next), hh'⟩

theorem row2_5 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b43Offset))
    (hh : Row cx m0 rows 2 5 (varsOf cx.sl 2 0) k18 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b48Offset) ∧
      Row cx m0 rows 2 6 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 5) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := kCopy k18) (ks2 := k18) (ks := k18)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 5128) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b43_in_code b44_in_code b45_in_code b46_in_code b47_in_code
    (by simp [b43]) (by simp [b44]) (by simp [b45]) (by simp [b46]) (by simp [b47])
    NativeRustcVmX64.Vm.KeccakOpen.b43_next NativeRustcVmX64.Vm.KeccakOpen.b44_next NativeRustcVmX64.Vm.KeccakOpen.b45_next NativeRustcVmX64.Vm.KeccakOpen.b46_next
    (label_of_infix hp b46_in_code rfl) x43 x44 x45 x46 x47
    f43.2 f44.2 f45.2 f46.2 f47.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b47_next), hh'⟩

theorem row2_6 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b48Offset))
    (hh : Row cx m0 rows 2 6 (varsOf cx.sl 2 0) k18 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b53Offset) ∧
      Row cx m0 rows 2 7 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 6) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := kCopy k18) (ks2 := k18) (ks := k18)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 6152) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b48_in_code b49_in_code b50_in_code b51_in_code b52_in_code
    (by simp [b48]) (by simp [b49]) (by simp [b50]) (by simp [b51]) (by simp [b52])
    NativeRustcVmX64.Vm.KeccakOpen.b48_next NativeRustcVmX64.Vm.KeccakOpen.b49_next NativeRustcVmX64.Vm.KeccakOpen.b50_next NativeRustcVmX64.Vm.KeccakOpen.b51_next
    (label_of_infix hp b51_in_code rfl) x48 x49 x50 x51 x52
    f48.2 f49.2 f50.2 f51.2 f52.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b52_next), hh'⟩

theorem row2_7 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b53Offset))
    (hh : Row cx m0 rows 2 7 (varsOf cx.sl 2 0) k18 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b58Offset) ∧
      Row cx m0 rows 2 8 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 7) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := kCopy k18) (ks2 := k18) (ks := k18)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 7168) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b53_in_code b54_in_code b55_in_code b56_in_code b57_in_code
    (by simp [b53]) (by simp [b54]) (by simp [b55]) (by simp [b56]) (by simp [b57])
    NativeRustcVmX64.Vm.KeccakOpen.b53_next NativeRustcVmX64.Vm.KeccakOpen.b54_next NativeRustcVmX64.Vm.KeccakOpen.b55_next NativeRustcVmX64.Vm.KeccakOpen.b56_next
    (label_of_infix hp b56_in_code rfl) x53 x54 x55 x56 x57
    f53.2 f54.2 f55.2 f56.2 f57.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b57_next), hh'⟩

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
