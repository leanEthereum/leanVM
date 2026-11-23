module

public import NativeRustcVmX64.Whir.SubspaceTable.Inv
public import NativeRustcVmX64.Code.Vm.Memset.Names

/-!
# `subspace_table`: from the entry to the layer (x86-64)

`start`: `b0a` pushes the callee-saved registers and opens the 792-byte frame, `b0b` zeroes the
layer (`memset`). `entry`: `b1` tests `μ < 32` (else `b5` stores `None`'s tag), `b2` spills the
output; the layer's first `μ` words are set to `2^(i+1)`, eight at a time (`b6`, `b7`) then one
at a time (`b9`, `b10`), to `Init μ` at `b11`.
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add eval_cmp_eq eval_not eval_test apart_symm not_inRange_of_apart
  written_region0)

@[expose] public section

/-- The eight-word loop's head after `d` words. -/
structure VInv (m0 : MachineData) (d : Nat) (st : MachineData) : Prop where
  init : Init m0 d st
  hd : d % 8 = 0
  hlt : d + 8 ≤ muOf m0 / 8 * 8
  r15 : reg st .r15 = fbOf m0 + BitVec.ofNat 64 (552 + 8 * d)
  rdx : reg st .rdx = BitVec.ofNat 64 d
  rsi : reg st .rsi = BitVec.ofNat 64 (muOf m0 / 8 * 8)
  rax : reg st .rax = BitVec.ofNat 64 (muOf m0 % 8)

/-- The word loop's head after `s` more words. -/
structure TInv (m0 : MachineData) (s : Nat) (st : MachineData) : Prop where
  init : Init m0 (muOf m0 / 8 * 8 + s) st
  hs : s < muOf m0 % 8
  r15 : reg st .r15 = fbOf m0 + BitVec.ofNat 64 (552 + 8 * (muOf m0 / 8 * 8))
  rdx : reg st .rdx = BitVec.ofNat 64 (muOf m0 / 8 * 8)
  rsi : reg st .rsi = BitVec.ofNat 64 s
  rax : reg st .rax = BitVec.ofNat 64 (muOf m0 % 8)

end

public section

theorem b3_vals : ∀ n < 32, 1 ≤ n →
    BinOp.apply .and .W64 (BitVec.ofNat 64 2305843009213693951)
        (BinOp.apply .add .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 18446744073709551615)) =
      BitVec.ofNat 64 (n - 1) ∧
    BinOp.apply .add .W64 (BitVec.ofNat 64 (n - 1)) (BitVec.ofNat 64 1) = BitVec.ofNat 64 n ∧
    BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 7) =
      BitVec.ofNat 64 (n % 8) ∧
    BinOp.apply .and .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 18446744073709551608) =
      BitVec.ofNat 64 (n / 8 * 8) := by
  decide +kernel

theorem zero_words : (initL 0).flatMap NativeRustcVm.wordBytes = List.replicate 248 0 := by
  rw [initL_zero]
  decide +kernel

theorem initL_getElem {i k : Nat} (hk : k < (initL i).length) :
    (initL i)[k] = if k < i then pow2 k else 0 := by
  simp [initL]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem reg_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

theorem ptr0_eval [Labels] {m0 st : MachineData} {F : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (frameEnv m0 st F vars ret) = stackBelow m0 F + BitVec.ofNat 64 o :=
  by show stackBelow m0 F + BitVec.ofInt 64 (o : Int) = _; rw [ofInt_ofNat]

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b0Offset) ∧
    b0b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b0Offset + b0a.length) := by
  have h := b0_in_code.trans hp.1 (by simp [b0])
  rw [← List.take_append_drop 8 b0] at h
  exact h.append
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b10Offset) :=
  b10_in_code.trans hp.1 (by simp [b10])

/-- **The prologue and `memset`**: at `b1`, the layer zeroed. -/
theorem start (hp : Placed code k) (hmemset : Spec (Labels.label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b1Offset) ∧ Fr m0 s.data ∧
      WordsAt s.data.dmem (fbOf m0 + BitVec.ofNat 64 552) (initL 0) ∧
      reg s.data .rbx = reg m0 .rdi ∧ reg s.data .r14 = reg m0 .rsi ∧
      reg s.data .r15 = fbOf m0 + BitVec.ofNat 64 552) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b0Offset)⟩ := by
  obtain ⟨hS, hout, hgot⟩ := hpre
  obtain ⟨hF, -, -, hle0⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hsl := slots_ok
  have hwf0 := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS hF)
    fun _ h ↦ h
  refine exec_then (hb0 hp).1 run_b0a hwf0 (by intro l h; cases h) match_frame
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show b0a.length = 8 from rfl] at hpc1
  obtain ⟨hw0, hregs0, hmem0, hsp0, hargs0⟩ := after_eq run_b0a ▸ b0a_entry
  have hfr1 : Fr m0 st1.data := Frame.of_entry hS hF hm1 hsp0 hw0 hregs0 hmem0
  have harg : ∀ r ∈ [Reg64.rdi, .rsi], reg st1.data r = reg m0 r := fun r hr ↦
    hm1.regs r (.reg r) (hargs0 r hr)
  have hwf2 := hfr1.got_wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b1Offset)).toBitVec) hS hF hgot (by simp : "memset" ∈ _)
  have hm2start := hfr1.got_match (l := "memset") (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b1Offset)).toBitVec)
    (fun i hi => hfr1.got_byte hS hgot
    (by intro ar har; simp only [List.mem_singleton] at har; subst ar; exact hout.1.2)
    (by intro r hr; simp only [outsOf, List.mem_singleton] at hr; subst r; simp)
    (by simp) hi)
  refine exec_at (hb0 hp).2 run_b0b hwf2 (fun _ _ ↦ rfl) hpc1 hm2start fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hsp2, hw2⟩ := after_eq run_b0b ▸ b0b_call
  have hrsp2 := rsp_call hm2 hsp2
  have hkept2 : Kept m0.dmem st2.data.dmem := fun p h ↦ hm2.kept hwf2 p (hfr1.kept p h)
  have hrdi2 : reg st2.data .rdi = fbOf m0 + BitVec.ofNat 64 552 :=
    (hm2.regs .rdi _ rfl).trans (gotEnv_ptr 552)
  have hrdx2 : (reg st2.data .rdx).toNat = 248 := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ rfl]; rfl
  have hrsi2 : reg st2.data .rsi = BitVec.ofNat 64 0 := hm2.regs .rsi _ rfl
  have h552 : (fbOf m0 + BitVec.ofNat 64 552).toNat = (rspOf m0).toNat - 848 + 552 := by
    rw [toNat_add_ofNat _ _ (by unfold fbOf; rw [hfe]; omega)]; unfold fbOf; rw [hfe]
  have hpre2 : MemsetPre st2.data := by
    unfold MemsetPre
    simp only [hrdi2, hrdx2]
    refine ⟨stackOk_callee hS hkept2 hrsp2 (by omega), fun i hi ↦ ?_, ?_, ?_⟩
    · rw [fbOf, addr_add]; exact hkept2 _ (hfmap _ (by omega))
    · unfold NoWrap; rw [h552]; omega
    · unfold Apart; rw [hrsp2, hfe, h552]; omega
  refine Frame.call hmemset hfr1 hS hle0 (L := 800) (by decide) hsl (out_one hout) hwf2
    hm2start hm2 hpc2 hk2 hsp2 (fun w hw ↦ ⟨(hw2 w hw).1, by have := (hw2 w hw).2; omega⟩)
    hpre2
    (fun m' ⟨_, _, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inl (by
      simp only [hrdi2, hrdx2] at h
      exact inRange_low_of hS hF (by omega) (by omega) h)))⟩)
    fun st3 hpc3 hfr3 ⟨_, hset, _, hsv3⟩ ↦ .done _ ⟨hpc3, hfr3, ?_, ?_, ?_, ?_⟩
  · simp only [hrdi2, hrdx2, hrsi2] at hset
    unfold WordsAt
    rw [zero_words]
    exact hset
  · exact (hsv3.1 .rbx rfl).trans ((hm2.regs .rbx _ rfl).trans (harg .rdi (by simp)))
  · exact (hsv3.1 .r14 rfl).trans ((hm2.regs .r14 _ rfl).trans (harg .rsi (by simp)))
  · exact (hsv3.1 .r15 rfl).trans ((hm2.regs .r15 _ rfl).trans (gotEnv_ptr 552))

end

end NativeRustcVmX64.Whir.SubspaceTable
