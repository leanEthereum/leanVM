module

public import NativeRustcVmX64.Top.Leanvm.Cond
public import NativeRustcVmX64.Code.Vm.LeanvmVerify.Names

/-!
# `leanvm_verify`: the prologue and the checks (x86-64)

From the entry, `b0` saves the registers and reads `L`; `b1` to `b5` check the counts and the
areas (`Cond`), `b6` reads the bytecode's address and the public input, `b7` checks the bytecode
when nonempty: `checks`, to `C1` at `NativeRustcVmX64.Vm.LeanvmVerify.label_8`, the frame's slots written, the context's
values in registers.
-/

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LeanvmVerify NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeVm NativeRustcVm.Transcript
open NativeRustcVm.Top (workAreaBytes usedRegions ApartFrom Aligned)
open NativeVm.Transcript (wd)

/-- After the checks: the frame, RSP at offset `8`, only the frame written; the context's values
in registers. -/
public structure C1 [Labels] (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m0 d : MachineData) : Prop where
  frame : Frame m0 112 slots 8 d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (stackBelow m0 112) 112)
  rax : reg d .rax = a.wire.toBitVec
  rbx : reg d .rbx = BitVec.ofNat 64 bytes.length
  rbp : reg d .rbp = a.bytecode.toBitVec
  r8 : reg d .r8 = pub[0].toBitVec
  rsi : reg d .rsi = pub[1].toBitVec
  rdx : reg d .rdx = pub[2].toBitVec
  rcx : reg d .rcx = pub[3].toBitVec
  r12 : reg d .r12 = a.decoded.toBitVec
  r13 : reg d .r13 = a.work.toBitVec
  r14 : reg d .r14 = BitVec.ofNat 64 bytecode.length
  r15 : reg d .r15 = BitVec.ofNat 64 (decodedWords bytes.length)

public section

variable [Host] {k : Nat}

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.LeanvmVerify.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.LeanvmVerify.entry_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.LeanvmVerify.label_8 = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b8Offset) :=
  hp.label NativeRustcVmX64.Vm.LeanvmVerify.label_8_at
theorem lbl_17 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.LeanvmVerify.label_17 = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b12Offset) :=
  hp.label NativeRustcVmX64.Vm.LeanvmVerify.label_17_at
theorem lbl_18 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.LeanvmVerify.label_18 = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b13Offset) :=
  hp.label NativeRustcVmX64.Vm.LeanvmVerify.label_18_at
theorem lbl_15 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.LeanvmVerify.label_15 = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b14Offset) :=
  hp.label NativeRustcVmX64.Vm.LeanvmVerify.label_15_at
theorem lbl_16 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.LeanvmVerify.label_16 = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b16Offset) :=
  hp.label NativeRustcVmX64.Vm.LeanvmVerify.label_16_at

/-- **The prologue and the checks.** -/
theorem checks (hp : Placed code k) {a : NativeVm.Entry.Areas} {bytes : List UInt8}
    {bytecode : List UInt64} {pub : Vector UInt64 4} {m0 : MachineData}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b8Offset) ∧
      C1 a bytes bytecode pub m0 st.data) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b0Offset)⟩ := by
  have g := geo_of hpre
  obtain ⟨hst, -, hin, hal, -, -⟩ := hpre
  have hR := g.R
  have h8 := g.e8
  have hBn := g.F
  have hce : NativeVm.Entry.ctxWords = 12 := (rfl)
  have hc : (ctxOf m0).toNat = (reg m0 .rdi).toNat := rfl
  have gc := g.ctx
  have gcN := g.ctxN
  have hfnw := frame_noWrap (F := 112) hst (by decide)
  have hFm : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (stackBelow m0 112) (112 + 8) :=
    fun d hk ↦ Mapped.keeps (frame_mapped hst (by decide)) hk
  have hcM : NativeRustcVm.Mapped m0.dmem (reg m0 .rdi) 96 :=
    NativeRustcVm.Mapped.mono (NativeRustcVm.mapped_of_wordView hin.ctxSome) (by omega)
  have hcN : NativeRustcVm.NoWrap (reg m0 .rdi) 96 := by
    unfold NativeRustcVm.NoWrap; omega
  have hap : ((stackBelow m0 112, 112 + 8) :: [(reg m0 .rdi, 96)]).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2 :=
    List.pairwise_pair.mpr (by unfold NativeRustcVm.Apart; dsimp only; rw [hBn]; omega)
  -- the context's words, kept where only the frame changed
  have ldk : ∀ (d : MachineData) (ret : BitVec 64),
      NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (stackBelow m0 112) 112) →
      ∀ {i : Nat} {v : UInt64}, i < 12 → NativeRustcVm.wordView m0.dmem (wd (ctxOf m0) i) = some v →
      (frameEnv m0 d 112 [(reg m0 .rdi, 96)] (fun _ ↦ 0) ret).load 1 (8 * i) 8 = v.toBitVec := by
    intro d ret hs i v hi h
    refine load_ofMachine (r := 1) (b := reg m0 .rdi) (n := 96) rfl ?_
    refine keep_off (ctxWord h) hs fun j h1 h2 hq ↦ ?_
    rw [NativeRustcVm.length_wordBytes] at h2
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn, toNat_off (by omega)] at hq
    omega
  have hL := hin.L32
  have hn : bytecode.length ≤ 536870910 := by have := hin.bcSmall; omega
  obtain ⟨v9, h9, hv9⟩ := hin.decLen
  obtain ⟨v11, h11, hv11⟩ := hin.workLen
  have hww : 61944 ≤ v11.toNat := by
    have := NativeRustcVm.Top.workAreaWords_le
    unfold NativeRustcVm.Top.workAreaWords at this; omega
  -- `b0`: the prologue, `L`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 112) (rest := [(reg m0 .rdi, 96)])
    (vars := fun _ ↦ 0) (ret := 0) ⟨frame_mapped hst (by decide), hfnw⟩
    (fun x hx ↦ by rw [List.mem_singleton] at hx; subst hx; exact ⟨hcM, hcN⟩) hap
  have hs0 : NativeRustcVm.SameOutside m0.dmem m0.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := fun _ _ ↦ rfl
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 nofun
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw1, hrbx1, hrdi1⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 112 slots 8 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hw1
  have hL1 := ldk m0 0 hs0 (i := 1) (by decide) hin.wireLen
  simp only [PcOk] at hpc1
  rw [cond_b0 _ hL1 hL] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  have eRbx1 : reg st1.data .rbx = BitVec.ofNat 64 bytes.length :=
    (hm1.regs .rbx _ hrbx1).trans hL1
  have eRdi1 : reg st1.data .rdi = reg m0 .rdi := (hm1.regs .rdi _ hrdi1).trans (eval_ptr rfl)
  -- `b1` to `b6`: no write, the context's values.
  have envOk : ∀ d : MachineData, Frame m0 112 slots 8 d →
      NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (stackBelow m0 112) 112) →
      reg d .rdi = reg m0 .rdi →
      (frameEnv m0 d 112 [(reg m0 .rdi, 96)] (fun _ ↦ 0) 0).WF ∧
        Match (frameEnv m0 d 112 [(reg m0 .rdi, 96)] (fun _ ↦ 0) 0) ctxS d := by
    intro d hf hs hrdi
    refine ⟨frame_wf ⟨hFm _ hf.kept, hfnw⟩ (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx; exact ⟨Mapped.keeps hcM hf.kept, hcN⟩) hap,
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, known_ptr rfl hrdi, trivial⟩ trivial
        trivial trivial⟩
  -- `b1`: `n`.
  obtain ⟨hwf1, hm1'⟩ := envOk _ hf1 hs1 eRdi1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1 nofun
    (hpc1.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b0Offset + b0.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b0_next]])) hm1' fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hmem2, hr142, hrbx2, hrdi2⟩ := after_eq run_b1 ▸ ok_b1
  have hn1 := ldk st1.data 0 hs1 (i := 3) (by decide) hin.bcLen
  simp only [PcOk] at hpc2
  rw [cond_b1 _ hn1 hn] at hpc2
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
  have hf2 : Frame m0 112 slots 8 st2.data := Frame.of_block hf1 hwf1 hm2 hmid2 slots_le
  have hs2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm2.dmem_eq hwf1 hmem2]; exact hs1
  have eR142 : reg st2.data .r14 = BitVec.ofNat 64 bytecode.length := (hm2.regs .r14 _ hr142).trans hn1
  have eRbx2 : reg st2.data .rbx = BitVec.ofNat 64 bytes.length := (hm2.regs .rbx _ hrbx2).trans eRbx1
  have eRdi2 : reg st2.data .rdi = reg m0 .rdi := (hm2.regs .rdi _ hrdi2).trans (eval_ptr rfl)
  -- `b2`: the decoded area's count.
  obtain ⟨hwf2, hm2'⟩ := envOk _ hf2 hs2 eRdi2
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf2 nofun
    (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b1Offset + b1.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b1_next]])) hm2' fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hr153, hrbx3, hr143, hrdi3⟩ := after_eq run_b2 ▸ ok_b2
  have h72 := ldk st2.data 0 hs2 (i := 9) (by decide) h9
  simp only [PcOk] at hpc3
  rw [cond_b2 _ h72 eRbx2 hL hv9] at hpc3
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
  have hf3 : Frame m0 112 slots 8 st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hs3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm3.dmem_eq hwf2 hmem3]; exact hs2
  have eR153 : reg st3.data .r15 = BitVec.ofNat 64 (decodedWords bytes.length) := by
    rw [show reg st3.data .r15 = _ from hm3.regs .r15 _ hr153]
    apply BitVec.eq_of_toNat_eq
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [show st2.data.regs.get64 .rbx = _ from eRbx2,
      dw_toNat (x := BitVec.ofNat 64 bytes.length) (by rw [BitVec.toNat_ofNat]; omega) hL,
      BitVec.toNat_ofNat]
    have : decodedWords bytes.length < 2 ^ 64 := by
      have := g.decN; omega
    omega
  have eRbx3 : reg st3.data .rbx = BitVec.ofNat 64 bytes.length := (hm3.regs .rbx _ hrbx3).trans eRbx2
  have eR143 : reg st3.data .r14 = BitVec.ofNat 64 bytecode.length := (hm3.regs .r14 _ hr143).trans eR142
  have eRdi3 : reg st3.data .rdi = reg m0 .rdi := (hm3.regs .rdi _ hrdi3).trans (eval_ptr rfl)
  -- `b3`: the working area's count.
  obtain ⟨hwf3, hm3'⟩ := envOk _ hf3 hs3 eRdi3
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf3 nofun
    (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b2Offset + b2.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b2_next]])) hm3' fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, hrbx4, hr144, hr154, hrdi4⟩ := after_eq run_b3 ▸ ok_b3
  have h88 := ldk st3.data 0 hs3 (i := 11) (by decide) h11
  simp only [PcOk] at hpc4
  rw [cond_b3 _ h88 hww] at hpc4
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
  have hf4 : Frame m0 112 slots 8 st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
  have hs4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm4.dmem_eq hwf3 hmem4]; exact hs3
  have eRbx4 := (hm4.regs .rbx _ hrbx4).trans eRbx3
  have eR144 := (hm4.regs .r14 _ hr144).trans eR143
  have eR154 := (hm4.regs .r15 _ hr154).trans eR153
  have eRdi4 : reg st4.data .rdi = reg m0 .rdi := (hm4.regs .rdi _ hrdi4).trans (eval_ptr rfl)
  -- `b4`: the decoded area.
  obtain ⟨hwf4, hm4'⟩ := envOk _ hf4 hs4 eRdi4
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf4 nofun
    (hpc4.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b3Offset + b3.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b3_next]])) hm4' fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hmem5, hr125, hrbx5, hr145, hr155, hrdi5⟩ := after_eq run_b4 ▸ ok_b4
  have h64 := ldk st4.data 0 hs4 (i := 8) (by decide) hin.decPtr
  simp only [PcOk] at hpc5
  rw [cond_area _ h64 (fun h ↦ hal.dec.1 (UInt64.toBitVec_inj.mp h)) hal.dec.2] at hpc5
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
  have hf5 : Frame m0 112 slots 8 st5.data := Frame.of_block hf4 hwf4 hm5 hmid5 slots_le
  have hs5 : NativeRustcVm.SameOutside m0.dmem st5.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm5.dmem_eq hwf4 hmem5]; exact hs4
  have eR125 : reg st5.data .r12 = a.decoded.toBitVec := (hm5.regs .r12 _ hr125).trans h64
  have eRbx5 := (hm5.regs .rbx _ hrbx5).trans eRbx4
  have eR145 := (hm5.regs .r14 _ hr145).trans eR144
  have eR155 := (hm5.regs .r15 _ hr155).trans eR154
  have eRdi5 : reg st5.data .rdi = reg m0 .rdi := (hm5.regs .rdi _ hrdi5).trans (eval_ptr rfl)
  -- `b5`: the working area.
  obtain ⟨hwf5, hm5'⟩ := envOk _ hf5 hs5 eRdi5
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf5 nofun
    (hpc5.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b4Offset + b4.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b4_next]])) hm5' fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hmem6, hr136, hr126, hrbx6, hr146, hr156, hrdi6⟩ := after_eq run_b5 ▸ ok_b5
  have h80 := ldk st5.data 0 hs5 (i := 10) (by decide) hin.workPtr
  simp only [PcOk] at hpc6
  rw [cond_area _ h80 (fun h ↦ hal.work.1 (UInt64.toBitVec_inj.mp h)) hal.work.2] at hpc6
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc6
  have hf6 : Frame m0 112 slots 8 st6.data := Frame.of_block hf5 hwf5 hm6 hmid6 slots_le
  have hs6 : NativeRustcVm.SameOutside m0.dmem st6.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm6.dmem_eq hwf5 hmem6]; exact hs5
  have eR136 : reg st6.data .r13 = a.work.toBitVec := (hm6.regs .r13 _ hr136).trans h80
  have eR126 := (hm6.regs .r12 _ hr126).trans eR125
  have eRbx6 := (hm6.regs .rbx _ hrbx6).trans eRbx5
  have eR146 := (hm6.regs .r14 _ hr146).trans eR145
  have eR156 := (hm6.regs .r15 _ hr156).trans eR155
  have eRdi6 : reg st6.data .rdi = reg m0 .rdi := (hm6.regs .rdi _ hrdi6).trans (eval_ptr rfl)
  -- `b6`: the wire's and the bytecode's addresses, the public input.
  obtain ⟨hwf6, hm6'⟩ := envOk _ hf6 hs6 eRdi6
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf6 nofun
    (hpc6.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b5Offset + b5.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b5_next]])) hm6' fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hmem7, hrax7, hrbp7, hr87, hrsi7, hrdx7, hrcx7, hr127, hr137, hrbx7, hr147,
    hr157⟩ := after_eq run_b6 ▸ ok_b6
  have hf7 : Frame m0 112 slots 8 st7.data := Frame.of_block hf6 hwf6 hm7 hmid7 slots_le
  have hs7 : NativeRustcVm.SameOutside m0.dmem st7.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 112) 112) := by
    rw [hm7.dmem_eq hwf6 hmem7]; exact hs6
  have hC : C1 a bytes bytecode pub m0 st7.data :=
    ⟨hf7, hs7, (hm7.regs .rax _ hrax7).trans (ldk st6.data 0 hs6 (i := 0) (by decide) hin.wirePtr),
      (hm7.regs .rbx _ hrbx7).trans eRbx6,
      (hm7.regs .rbp _ hrbp7).trans (ldk st6.data 0 hs6 (i := 2) (by decide) hin.bcPtr),
      (hm7.regs .r8 _ hr87).trans (ldk st6.data 0 hs6 (i := 4) (by decide) (hin.pubWords 0 (by decide))),
      (hm7.regs .rsi _ hrsi7).trans (ldk st6.data 0 hs6 (i := 5) (by decide) (hin.pubWords 1 (by decide))),
      (hm7.regs .rdx _ hrdx7).trans (ldk st6.data 0 hs6 (i := 6) (by decide) (hin.pubWords 2 (by decide))),
      (hm7.regs .rcx _ hrcx7).trans (ldk st6.data 0 hs6 (i := 7) (by decide) (hin.pubWords 3 (by decide))),
      (hm7.regs .r12 _ hr127).trans eR126, (hm7.regs .r13 _ hr137).trans eR136,
      (hm7.regs .r14 _ hr147).trans eR146, (hm7.regs .r15 _ hr157).trans eR156⟩
  simp only [PcOk] at hpc7
  rw [cond_zero _ eR146] at hpc7
  rcases Nat.eq_zero_or_pos bytecode.length with hn0 | hn0
  · -- an empty bytecode: to `NativeRustcVmX64.Vm.LeanvmVerify.label_8`
    rw [hn0] at hpc7
    simp only [show (BitVec.ofNat 64 0 == 0) = true from rfl, ↓reduceIte] at hpc7
    exact .done _ ⟨hpc7.trans (lbl_8 hp), hC⟩
  · -- `b7`: the bytecode nonzero and 8-aligned
    have hb := hal.bytecode hn0
    have hne : (BitVec.ofNat 64 bytecode.length == 0) = false := by
      rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
        ofNat_beq (X := bytecode.length) (k := 0) (by omega) (by decide)]
      simpa using (show bytecode.length ≠ 0 by omega)
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc7
    have hwf7 := frame_wf (m0 := m0) (d := st7.data) (F := 112) (rest := []) (vars := fun _ ↦ 0)
      (ret := 0) ⟨hFm _ hf7.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _)
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf7 nofun
      (hpc7.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b6Offset + b6.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b6_next]]))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf7.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st8 hm8 hpc8 ↦ ?_
    obtain ⟨hmid8, hmem8, hk8⟩ := after_eq run_b7 ▸ ok_b7
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hk8
    obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ := hk8
    simp only [PcOk] at hpc8
    rw [cond_b7 _ hC.rbp (fun h ↦ hb.1 (UInt64.toBitVec_inj.mp h)) hb.2] at hpc8
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc8
    have hd8 : st8.data.dmem = st7.data.dmem := hm8.dmem_eq hwf7 hmem8
    exact .done _ ⟨hpc8.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b7Offset + b7.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b8Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b7_next]]),
      ⟨Frame.of_block hC.frame hwf7 hm8 hmid8 slots_le, by rw [hd8]; exact hC.same,
        (hm8.regs .rax _ k0).trans hC.rax, (hm8.regs .rbx _ k8).trans hC.rbx,
        (hm8.regs .rbp _ k1).trans hC.rbp, (hm8.regs .r8 _ k2).trans hC.r8,
        (hm8.regs .rsi _ k3).trans hC.rsi, (hm8.regs .rdx _ k4).trans hC.rdx,
        (hm8.regs .rcx _ k5).trans hC.rcx, (hm8.regs .r12 _ k6).trans hC.r12,
        (hm8.regs .r13 _ k7).trans hC.r13, (hm8.regs .r14 _ k9).trans hC.r14,
        (hm8.regs .r15 _ k10).trans hC.r15⟩⟩

end

end NativeRustcVmX64.Top.Leanvm
