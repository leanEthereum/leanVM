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

@[expose] public def kI5 : List (Reg64 × Sym) := [(.r14, V0), (.r15, V1)]

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem inner_step5 (hp : Placed code k) (h : PreOk a s c m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {cx : Cx} (hA : cx.a = a) {rows : Array (Array EW)}
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {j : Nat} (hj : j < 64) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b91Offset))
    (hh : Inner cx m0 rows 5 0 j .rbx 0 (varsOf cx.sl 5 0) kI5 [] st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      st'.pc = (if j + 1 < 64 then Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b91Offset) else Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b93Offset)) ∧
      Inner cx m0 rows 5 0 (j + 1) .rbx 0 (varsOf cx.sl 5 0) kI5 [] st'.data) st := by
  have hc0 : reg st.data .r14 = (cx.sl.getD 5 0).c0.toBitVec := hh.known.1
  have hc1 : reg st.data .r15 = (cx.sl.getD 5 0).c1.toBitVec := hh.known.2.1
  refine (load_mul hp hmul h hA hj b91_in_code (by simp [b91]) x91 f91.2.1 hpc hh.mid
    hh.counter hc0 hc1 hh.bufA hh.bufB).bind
    fun st1 ⟨hpc1, hm1, hp0, hp1, hl0, hl1, hregs, hlow⟩ ↦ ?_
  have hkeep (r : Reg64) (hr : r ∈ [.rbx, .r14, .r15]) (hc : calleeSaved r = true) :
      reg st1.data r = reg st.data r :=
    hregs r (.reg r) hc (atoms_reg (lOk_atoms f91.2.1) hr)
  have hk1 : KAt m0 (varsOf cx.sl 5 0) kI5 st1.data :=
    ⟨(hkeep .r14 (by simp) rfl).trans hh.known.1,
      (hkeep .r15 (by simp) rfl).trans hh.known.2.1, trivial⟩
  have hib : reg st1.data .rbx = BitVec.ofNat 64 (16 * j) :=
    (hkeep .rbx (by simp) rfl).trans (by simpa only [Nat.zero_add] using hh.counter)
  have hnib : reg st1.data .r12 = BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show reg st1.data .r12 = _ from hregs .r12 _ rfl f91.2.2]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    change reg st.data .rbx + 16#64 = _
    rw [hh.counter, Nat.zero_add]
    rw [← BitVec.ofNat_add]
    congr 1
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b92Offset) := hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b91_next)
  refine store_run hp h hA (by omega) b92_in_code (by simp [b92]) x92 nofun f92.2
    hpc1' hm1 (store_match5 h hm1 hib) hp0 hp1 hl0 hl1
    fun st2 hpc2 hm2 hmid2 hv hstore ↦ ?_
  have hcnt2 : reg st2.data .rbx = BitVec.ofNat 64 (16 * (j + 1)) :=
    (hm2.regs .rbx (.reg .r12) (sOk_counter f92.2)).trans hnib
  have htest := notEnd_eval (env := storeEnv m0 st1.data j) (nib := .reg .r12) (s0 := 0)
    hj (by decide) (by
      change reg st1.data .r12 = BitVec.ofNat 64 (0 + 16 * (j + 1))
      rw [Nat.zero_add]
      exact hnib)
  have hpc2' : st2.pc = (if j + 1 < 64 then Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b91Offset) else Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b93Offset)) := by
    simpa only [PcOk, htest, decide_eq_true_eq, Nat.add_assoc, NativeRustcVmX64.Vm.KeccakOpen.b92_next,
      label_of_infix hp b91_in_code rfl] using hpc2
  have hk2 : KAt m0 (varsOf cx.sl 5 0) kI5 st2.data := hk1.regs_keep fun r hr ↦
    hm2.regs r (.reg r) (atoms_reg (sOk_atoms f92.2) hr)
  have hn : j < 4096 := by omega
  have hso : NativeRustcVm.SameOutside st.data.dmem st2.data.dmem (FoldTouch m0 j) := by
    intro q hq
    exact (hstore q fun hx ↦ hq (.inr hx)).trans (hlow q fun hx ↦ hq (.inl hx))
  have hv' : NativeRustcVm.EWAt st2.data.dmem (off (rwA m0) (16 * j)) (W cx.sl rows 6 0 j) := by
    have hc (a b : EW) : a + b = b + a := by
      change EW.mk (a.c0 ^^^ b.c0) (a.c1 ^^^ b.c1) = EW.mk (b.c0 ^^^ a.c0) (b.c1 ^^^ a.c1)
      congr 1 <;> exact UInt64.xor_comm _ _
    rw [W_succ hrsz hrow (by rw [hh.mid.sl_size]; decide) (by decide) hj, foldE,
      hc (W cx.sl rows 5 (2 * 0) j)]
    exact hv
  refine .done _ ⟨hpc2', hmid2, hk2, trivial, by simpa only [Nat.zero_add] using hcnt2,
    keep_buffer h hn (by decide) (by decide) hh.bufA hso,
    keep_buffer h hn (by decide) (by decide) hh.bufB hso,
    ?_⟩
  simpa only [Nat.mul_zero, Nat.zero_add] using
    rows_step h (i := 0) (by decide) hj (rows_low h hh.rows hlow)
      (by simpa only [Nat.mul_zero, Nat.zero_add] using hv')
      (by simpa only [Nat.mul_zero, Nat.zero_add] using hstore)

theorem round5 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {cx : Cx} (hA : cx.a = a) {rows : Array (Array EW)}
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b88Offset))
    (hm : Mid cx m0 8 st.data) (hk : KAt m0 (varsOf cx.sl 5 0) [(.rbp, P)] st.data)
    (hw : Words m0 (varsOf cx.sl 5 0) W6 st.data)
    (hr : ElemsAt st.data.dmem (rwA m0) (Fr cx.sl rows 5) 4096) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b93Offset) ∧
      Mid cx m0 8 st'.data ∧ ElemsAt st'.data.dmem (rwA m0) (Fr cx.sl rows 6) 4096) st := by
  have hr' : ElemsAt st.data.dmem (rwA m0) (F cx.sl rows 5 0 0) 4096 := by
    simpa only [F_zero] using hr
  refine (row_start (t := 5) (i := 0) (vars := varsOf cx.sl 5 0) (ks := k88) (ws := W6)
    hp hcpy h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    b88_in_code b89_in_code b90_in_code (by simp [b88]) (by simp [b89]) (by simp [b90])
    NativeRustcVmX64.Vm.KeccakOpen.b88_next NativeRustcVmX64.Vm.KeccakOpen.b89_next x88 x89 x90 f88.2 f89.2 f90.2 rfl rfl hpc hm hk hw hr').bind
    fun st1 ⟨hpc1, hh1⟩ ↦ ?_
  have hi1 : Inner cx m0 rows 5 0 0 .rbx 0 (varsOf cx.sl 5 0) kI5 [] st1.data :=
    ⟨hh1.mid, ⟨hh1.known.1, hh1.known.2.1, trivial⟩, trivial, hh1.counter, hh1.bufA, hh1.bufB, hh1.rows⟩
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b91Offset) := hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b90_next)
  refine (inner_loop (fun j hj st' hp' hh' ↦ inner_step5 hp h hmul hA hrsz hrow hj hp' hh')
    (by decide) hpc1' hi1).mono fun st2 ⟨hp2, hh2⟩ ↦ ?_
  refine ⟨hp2, hh2.mid, ?_⟩
  have hr' := hh2.rows
  rw [F_row] at hr'
  change ElemsAt st2.data.dmem (rwA m0) (F cx.sl rows 5 (half 5) 0) 4096 at hr'
  rwa [F_half] at hr'

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
