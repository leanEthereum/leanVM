module

public import NativeRustcVmX64.KeccakGkr.SlotWeights.Pro

/-!
# `slot_weights`: the rows zeroed (x86-64)

`NativeRustcVmX64.Vm.SlotWeights.label_2` (`b3`) starts row `r` (RAX its address plus `56`, RCX `1024 r`);
`NativeRustcVmX64.Vm.SlotWeights.label_3` (`b4`) zeroes four elements at `RAX + RDX - 56`, RDX counting the row's bytes
(`zero_in`, `row_loop`); `b5` steps to the next row (`zero_row`, `zero_loop`); after the last,
`b6` starts the segment loop at segment `0` (`SegHead`).
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.SlotWeights
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' not_inRange_of_apart
  Mapped.keeps bytesAt_congr inRange_off_self inRange_off_iff)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

@[expose] public section

/-- **The zeroing loop's inner head**: row `r`, `q` four-element groups of it zeroed. -/
structure ZeroIn (m0 : MachineData) (c : KeccakClaimW) (r q : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 c st
  r_lt : r < 64
  q_le : q ≤ 16
  rax : reg st .rax = off (rowsA m0) (1024 * r + 56)
  rcx : reg st .rcx = BitVec.ofNat 64 (1024 * r)
  rdx : reg st .rdx = BitVec.ofNat 64 (64 * q)
  rows : ElemsAt st.dmem (rowsA m0) (fun _ ↦ 0) (64 * r + 4 * q)

/-- **The segment loop's head** at segment `s`: the rows hold the products of the segments
before it. -/
structure SegHead (m0 : MachineData) (c : KeccakClaimW) (s : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 c st
  s_lt : s < (reg m0 .r9).toNat
  rcx : reg st .rcx = BitVec.ofNat 64 s
  rows : ElemsAt st.dmem (rowsA m0)
    (prog (reg m0 .rdi).toNat c (reg m0 .r8).toNat (1600 * ((reg m0 .r8).toNat + s))) 4096

end

public section

variable {c : KeccakClaimW} {m0 : MachineData}

/-- **A block without writes** keeps the context. -/
theorem Ctx.of_block [Labels] {d d' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hc : Ctx m0 c d)
    (hwf : (frameEnv m0 d 160 rest vars ret).WF) (hm : Match (frameEnv m0 d 160 rest vars ret) S d')
    (hS : MidOk 160 8 slots S = true) (hmem : S.mem = []) : Ctx m0 c d' := by
  have hd : d'.dmem = d.dmem := hm.dmem_eq hwf hmem
  exact ⟨Frame.of_block hc.frame hwf hm hS slots_le, hd ▸ hc.same, hd ▸ hc.loc⟩

theorem off_add_ofNat (a : BitVec 64) (x y : Nat) : off a x + BitVec.ofNat 64 y = off a (x + y) :=
  NativeRustcVm.Transcript.off_add a x y

variable [Host] {k : Nat}

/-- `b3`: a row's start. -/
theorem zero_start (hp : Placed code k) (h : PreOk m0 c) {r : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b3Offset)) (hI : ZeroInv m0 c r s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b4Offset) ∧ ZeroIn m0 c r 0 s'.data)
      s := by
  have hwf := wf_body h hI.ctx.frame.kept (d := s.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf nofun hpc
    (match_callS hI.ctx.frame) fun s' hm' hpc' ↦ ?_
  obtain ⟨hmid, hmem, hrax, hrcx, hrdx⟩ := ok_b3
  have hd : s'.data.dmem = s.data.dmem := hm'.dmem_eq hwf hmem
  simp only [PcOk] at hpc'
  exact .done _ ⟨hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b3_next), ⟨hI.ctx.of_block hwf hm' hmid hmem, hI.r_lt,
    by omega, (hm'.regs .rax _ hrax).trans hI.rax, (hm'.regs .rcx _ hrcx).trans hI.rcx,
    hm'.regs .rdx _ hrdx, by rw [hd]; exact hI.rows⟩⟩

/-- `b4`: four elements of a row zeroed. -/
theorem zero_in (hp : Placed code k) (h : PreOk m0 c) {r q : Nat} (hq : q < 16) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b4Offset)) (hI : ZeroIn m0 c r q s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (q + 1 < 16 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b4Offset) ∧
      ZeroIn m0 c r (q + 1) s'.data) ∨ (q + 1 = 16 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b5Offset) ∧
      ZeroIn m0 c r (q + 1) s'.data)) s := by
  have hr := hI.r_lt
  set b1 := off (rowsA m0) (1024 * r + 64 * q) with hb1
  have hrn : (rowsA m0).toNat + 65536 ≤ 2 ^ 64 := h.rows.2
  have hb1n : b1.toNat = (rowsA m0).toNat + (1024 * r + 64 * q) := toNat_off (by omega)
  have hfb := fbA_toNat h
  have hS := h.rowsS
  have hsb := sb_toNat h
  have hst := h.st.1
  have h8 := h.st.2.1
  unfold NativeRustcVm.Apart at hS
  simp only [rowsBytes, slotWeightsStack, eqKernelStack, ewMulStack] at hS hsb hst
  have hwf : (frameEnv m0 s.data 160 [(b1, 64)] (fun _ ↦ 0) 0).WF :=
    frame_wf ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq]; decide)) hI.ctx.frame.kept,
        frame_noWrap h.st (by rw [stack_eq]; decide)⟩
      (fun x hx ↦ by
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨Mapped.keeps (mapped_off h.rows.1 (by show _ ≤ 65536; omega)) hI.ctx.frame.kept,
          by show b1.toNat + 64 ≤ 2 ^ 64; omega⟩)
      (List.pairwise_pair.mpr (by show _ ∨ _; rw [hb1n, hfb]; omega))
  have hm : Match (frameEnv m0 s.data 160 [(b1, 64)] (fun _ ↦ 0) 0) zeroS s.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hI.ctx.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [show (frameEnv m0 s.data 160 [(b1, 64)] (fun _ ↦ 0) 0).regs .rax = _ from hI.rax,
          show (frameEnv m0 s.data 160 [(b1, 64)] (fun _ ↦ 0) 0).regs .rdx = _ from hI.rdx,
          show (frameEnv m0 s.data 160 [(b1, 64)] (fun _ ↦ 0) 0).base 1 = b1 from rfl,
          show BitVec.ofInt 64 56 = BitVec.ofNat 64 56 from rfl, hb1, off_add_ofNat,
          off_add_ofNat]
        congr 1
        omega, trivial⟩
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf nofun hpc hm
    fun s' hm' hpc' ↦ ?_
  obtain ⟨hmid, hrax, hrcx, hrdx, hws, hz⟩ := ok_b4
  have hso : NativeRustcVm.SameOutside s.data.dmem s'.data.dmem (NativeRustcVm.InRange b1 64) :=
    sameOutside_region hwf hm' (r := 1) rfl hws
  have e0 : (⟨UInt64.ofBitVec ((Sym.lit 0).eval (frameEnv m0 s.data 160 [(b1, 64)] (fun _ ↦ 0) 0)),
      UInt64.ofBitVec ((Sym.lit 0).eval (frameEnv m0 s.data 160 [(b1, 64)] (fun _ ↦ 0) 0))⟩ : EW) =
      0 := rfl
  have hnew : ∀ e < 4, NativeRustcVm.EWAt s'.data.dmem (off b1 (16 * e)) 0 := fun e he ↦ by
    have := Match.ewAt_write hm' (r := 1) (o := 16 * e) (v0 := .lit 0) (v1 := .lit 0) rfl (by omega)
      (fun t ht ↦ (hz e he t ht).1) (fun t ht ↦ (hz e he t ht).2)
    rw [e0] at this
    exact this
  have hrows : ElemsAt s'.data.dmem (rowsA m0) (fun _ ↦ 0) (64 * r + 4 * (q + 1)) := by
    intro i hi
    by_cases hlt : i < 64 * r + 4 * q
    · refine keep_off (hI.rows i hlt) hso fun t ht hq' ↦ ?_
      rw [NativeRustcVm.length_ewBytes] at ht
      rw [hb1, inRange_off_iff (by omega) (by omega)] at hq'
      omega
    · have := hnew (i - (64 * r + 4 * q)) (by omega)
      rwa [hb1, off_off, show 1024 * r + 64 * q + 16 * (i - (64 * r + 4 * q)) = 16 * i by omega]
        at this
  have hctx : Ctx m0 c s'.data :=
    ⟨Frame.of_block hI.ctx.frame hwf hm' hmid slots_le,
      fun q' hq' ↦ by
        rw [hso q' fun hc ↦ hq' (Or.inl (inRange_of_off (o := 1024 * r + 64 * q) (l := 64) h.rows.2 (by show _ ≤ 65536; omega)
          (by rw [← hb1]; exact hc)))]
        exact hI.ctx.same q' hq',
      hI.ctx.loc.keep hso fun j hj ↦ rows_not_frame h (by decide) (by show _ ≤ 65536; omega)
        (by omega)⟩
  have hrdx' : reg s'.data .rdx = BitVec.ofNat 64 (64 * (q + 1)) := by
    rw [show reg s'.data .rdx = _ from hm'.regs .rdx _ hrdx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show (frameEnv m0 s.data 160 [(b1, 64)] (fun _ ↦ 0) 0).regs .rdx = _ from hI.rdx,
      add_ofNat]
    congr 1
    omega
  have hI' : ZeroIn m0 c r (q + 1) s'.data :=
    ⟨hctx, hr, by omega, (hm'.regs .rax _ hrax).trans hI.rax, (hm'.regs .rcx _ hrcx).trans hI.rcx,
      hrdx', hrows⟩
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64] at hpc'
  rw [show (frameEnv m0 s.data 160 [(b1, 64)] (fun _ ↦ 0) 0).regs .rdx = _ from hI.rdx, add_ofNat,
    beq_ofNat (by omega) (by omega)] at hpc'
  by_cases hlast : q + 1 = 16
  · rw [show 64 + 64 * q = 1024 by omega] at hpc'
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    exact .done _ (Or.inr ⟨hlast, hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b4_next), hI'⟩)
  · rw [decide_eq_false (show ¬64 + 64 * q = 1024 by omega)] at hpc'
    simp only [Bool.not_false, ite_true] at hpc'
    exact .done _ (Or.inl ⟨by omega, hpc'.trans (label_of_infix hp b4_in_code rfl), hI'⟩)

/-- **A row zeroed**: from its start to `b5`. -/
theorem row_loop (hp : Placed code k) (h : PreOk m0 c) {r : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b4Offset)) (hI : ZeroIn m0 c r 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b5Offset) ∧ ZeroIn m0 c r 16 s'.data)
      s :=
  loop (fun n s ↦ ∃ q, n = 16 - q ∧ q < 16 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b4Offset) ∧ ZeroIn m0 c r q s.data)
    (fun _ s ⟨q, hn, hq, hpc, hI⟩ ↦ (zero_in hp h hq hpc hI).mono fun s' h' ↦ by
      rcases h' with ⟨hlt, hpc', hI'⟩ | ⟨hlast, hpc', hI'⟩
      · exact Or.inr ⟨16 - (q + 1), by omega, q + 1, rfl, hlt, hpc', hI'⟩
      · exact Or.inl ⟨hpc', hlast ▸ hI'⟩)
    ⟨0, rfl, by decide, hpc, hI⟩

/-- `b5`: the next row, or the rows done. -/
theorem zero_row (hp : Placed code k) (h : PreOk m0 c) {r : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b5Offset)) (hI : ZeroIn m0 c r 16 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (r + 1 < 64 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b3Offset) ∧
      ZeroInv m0 c (r + 1) s'.data) ∨ (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b6Offset) ∧ Ctx m0 c s'.data ∧
      ElemsAt s'.data.dmem (rowsA m0) (fun _ ↦ 0) 4096)) s := by
  have hr := hI.r_lt
  have hwf := wf_body h hI.ctx.frame.kept (d := s.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf nofun hpc
    (match_callS hI.ctx.frame) fun s' hm' hpc' ↦ ?_
  obtain ⟨hmid, hmem, hrax, hrcx⟩ := ok_b5
  have hd : s'.data.dmem = s.data.dmem := hm'.dmem_eq hwf hmem
  have hctx := hI.ctx.of_block hwf hm' hmid hmem
  have hrows : ElemsAt s'.data.dmem (rowsA m0) (fun _ ↦ 0) (64 * (r + 1)) := by
    rw [hd, show 64 * (r + 1) = 64 * r + 4 * 16 by omega]; exact hI.rows
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64] at hpc'
  rw [show (frameEnv m0 s.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .rcx = _ from hI.rcx,
    add_ofNat, beq_ofNat (by omega) (by omega)] at hpc'
  by_cases hlast : r + 1 = 64
  · rw [show 1024 + 1024 * r = 65536 by omega] at hpc'
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    refine .done _ (Or.inr ⟨hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b5_next), hctx, ?_⟩)
    rw [show 4096 = 64 * (r + 1) by omega]; exact hrows
  · rw [decide_eq_false (show ¬1024 + 1024 * r = 65536 by omega)] at hpc'
    simp only [Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨by omega, hpc'.trans (label_of_infix hp b3_in_code rfl),
      ⟨hctx, by omega, ?_, ?_, hrows⟩⟩)
    · rw [show reg s'.data .rax = _ from hm'.regs .rax _ hrax]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [show (frameEnv m0 s.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .rax = _ from hI.rax,
        BitVec.add_comm, off_add_ofNat, show 1024 * r + 56 + 1024 = 1024 * (r + 1) + 56 by omega]
    · rw [show reg s'.data .rcx = _ from hm'.regs .rcx _ hrcx]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [show (frameEnv m0 s.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .rcx = _ from hI.rcx,
        add_ofNat]
      congr 1
      omega

/-- **The rows zeroed**, then `b6`: the segment loop's head at segment `0`. -/
theorem zero_loop (hp : Placed code k) (h : PreOk m0 c) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b3Offset)) (hI : ZeroInv m0 c 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b9Offset) ∧ SegHead m0 c 0 s'.data)
      s := by
  refine (loop (Q := fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b6Offset) ∧ Ctx m0 c s'.data ∧
      ElemsAt s'.data.dmem (rowsA m0) (fun _ ↦ 0) 4096)
    (fun n s ↦ ∃ r, n = 64 - r ∧ r < 64 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b3Offset) ∧ ZeroInv m0 c r s.data)
    (fun _ s ⟨r, hn, hr, hpc, hI⟩ ↦ (zero_start hp h hpc hI).bind fun s1 ⟨hpc1, hI1⟩ ↦
      (row_loop hp h hpc1 hI1).bind fun s2 ⟨hpc2, hI2⟩ ↦
        (zero_row hp h hpc2 hI2).mono fun s' h' ↦ by
          rcases h' with ⟨hlt, hpc', hI'⟩ | h'
          · exact Or.inr ⟨64 - (r + 1), by omega, r + 1, rfl, hlt, hpc', hI'⟩
          · exact Or.inl h')
    ⟨0, rfl, by decide, hpc, hI⟩).bind fun s3 ⟨hpc3, hctx, hrows⟩ ↦ ?_
  have hwf := wf_body h hctx.frame.kept (d := s3.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf nofun hpc3
    (match_callS hctx.frame) fun s' hm' hpc' ↦ ?_
  obtain ⟨hmid, hmem, hrcx⟩ := ok_b6
  have hd : s'.data.dmem = s3.data.dmem := hm'.dmem_eq hwf hmem
  simp only [PcOk] at hpc'
  refine .done _ ⟨hpc'.trans (label_of_infix hp b9_in_code rfl), hctx.of_block hwf hm' hmid hmem,
    h.cnt1, hm'.regs .rcx _ hrcx, ?_⟩
  rw [hd, Nat.add_zero, prog_start]
  exact hrows

end

end NativeRustcVmX64.KeccakGkr.SlotWeights
