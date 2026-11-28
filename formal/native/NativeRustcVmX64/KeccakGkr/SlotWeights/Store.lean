module

public import NativeRustcVmX64.KeccakGkr.SlotWeights.Bit

/-!
# `slot_weights`: one bit's product stored (x86-64)

After `EW::mul` (`AfterMul`): `p1` computes the element's address (the rows' base plus `1024`
times the row, plus `16 (j % 64)`), `p2` stores the product there, `b11` counts the bit and either
loops (`Inner` at `j + 1`) or ends the segment (`SegEnd`) (`bit_store`).
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.SlotWeights
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' not_inRange_of_apart
  Mapped.keeps bytesAt_congr inRange_off_self inRange_off_iff)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

public section

variable {c : KeccakClaimW} {m0 : MachineData}

theorem p1_infix : p1.IsInfixAt code (NativeRustcVmX64.Vm.SlotWeights.b14Offset) :=
  (List.IsInfixAt.trans (infix_take b14 5) b14_in_code (by simp [b14]) :)

theorem p2_infix : p2.IsInfixAt code (NativeRustcVmX64.Vm.SlotWeights.b14Offset + p1.length) :=
  (List.IsInfixAt.trans (infix_drop b14 5) b14_in_code (by simp [b14]) :)

/-- The product's value at its flat index. -/
theorem V_flat {s j : Nat} (hj : j < 1600) :
    V (reg m0 .rdi).toNat c (reg m0 .r8).toNat (flat m0 s j) = scale m0 c s * wt c j := by
  obtain ⟨h1, h2⟩ := flat_div (m0 := m0) (s := s) hj
  rw [V, h1, h2]

variable [Host] {k : Nat}

/-- **The product stored**, the bit counted. -/
theorem bit_store (hp : Placed code k) (h : PreOk m0 c) {s j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b14Offset)) (hI : AfterMul m0 c s j st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (j + 1 < 1600 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b12Offset) ∧
      Inner m0 c s (j + 1) s'.data) ∨ (j + 1 = 1600 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b8Offset) ∧
      SegEnd m0 c s s'.data)) st := by
  have hs := hI.s_lt
  have hj := hI.j_lt
  have hc2 := h.cnt2
  have hfs : (reg m0 .r8).toNat + s ≤ 1 := by omega
  have hrowlt : rowOf m0 s j < 63 := by unfold rowOf; omega
  have hfnw : NativeRustcVm.NoWrap (fbA m0) (160 + 8) := frame_noWrap h.st (by rw [stack_eq]; decide)
  have hrn : (rowsA m0).toNat + 65536 ≤ 2 ^ 64 := h.rows.2
  -- `p1`: the element's address.
  have hwf := wf_body h hI.ctx.frame.kept (d := st.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of p1_infix (by simp [p1, b14]) hp) exit_p1 hwf nofun hpc
    (match_callS hI.ctx.frame) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hrcx, hr12, hrax, hrdx, hr13, hrbp, hr14, hr15, hrbx⟩ := ok_p1
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem1
  have hctx1 := hI.ctx.of_block hwf hm1 hmid1 hmem1
  set E := off (rowsA m0) (16 * flat m0 s j) with hE
  have h16 : 16 * flat m0 s j = 1024 * rowOf m0 s j + 16 * (j % 64) := by
    unfold flat rowOf; omega
  have hEn : E.toNat = (rowsA m0).toNat + 16 * flat m0 s j := toNat_off (by unfold flat; omega)
  have hX1 : (reg st1.data .rcx).toNat = 16 * (j % 64) := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hrcx]
    exact colS_eval _ (by
      rw [show (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .r15 = _ from hI.r15,
        toNat_ofNat_lt (by omega)])
  have hX12 : reg st1.data .r12 = off (rowsA m0) (1024 * rowOf m0 s j) := by
    rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ hr12]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [load_rows h hI.ctx.same,
      show (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .r12 = _ from hI.r12,
      show shiftCount .W64 (BitVec.ofNat 64 10) = 10 by decide]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt (by omega), Nat.shiftLeft_eq, toNat_ofNat_lt (by omega)]
    show _ % 2 ^ 64 = _
    omega
  -- `p2`: the product stored.
  have hEF : (fbA m0).toNat + (160 + 8) ≤ E.toNat ∨ E.toNat + 16 ≤ (fbA m0).toNat := by
    have : NativeRustcVm.Apart (rowsA m0) 65536 (fbA m0) (160 + 8) :=
      apart_frame (F := 160) h.rowsS h.st.1 (by rw [stack_eq]; decide)
    unfold NativeRustcVm.Apart at this
    rw [hEn]; unfold flat; omega
  have hwf1 : (frameEnv m0 st1.data 160 [(E, 16)] (fun _ ↦ 0) 0).WF :=
    frame_wf ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq]; decide)) hctx1.frame.kept, hfnw⟩
      (fun x hx ↦ by
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨Mapped.keeps (mapped_off h.rows.1 (by show _ ≤ 65536; unfold flat; omega))
          hctx1.frame.kept, by show _ + 16 ≤ 2 ^ 64; rw [hEn]; unfold flat; omega⟩)
      (List.pairwise_pair.mpr hEF)
  have hm1' : Match (frameEnv m0 st1.data 160 [(E, 16)] (fun _ ↦ 0) 0) storeS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hctx1.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [show (frameEnv m0 st1.data 160 [(E, 16)] (fun _ ↦ 0) 0).regs .r12 = _ from hX12,
          show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          show (frameEnv m0 st1.data 160 [(E, 16)] (fun _ ↦ 0) 0).base 1 = E from rfl,
          show (frameEnv m0 st1.data 160 [(E, 16)] (fun _ ↦ 0) 0).regs .rcx =
            BitVec.ofNat 64 (16 * (j % 64)) from by
              apply BitVec.eq_of_toNat_eq; rw [toNat_ofNat_lt (by omega)]; exact hX1,
          BitVec.add_comm, NativeRustcVm.Transcript.off_add, hE, h16], trivial⟩
  refine exec_at (infix_of p2_infix (by simp [p2, b14]) hp) exit_p2 hwf1 nofun
    (hpc1.trans (by rw [Nat.add_assoc])) hm1' fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hr13', hrbp', hr14', hr15', hrbx', hws2, hw0, hw1⟩ := ok_p2
  have hf2 : Frame m0 160 slots 8 st2.data := Frame.of_block hctx1.frame hwf1 hm2 hmid2 slots_le
  have hs2 : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (NativeRustcVm.InRange E 16) :=
    sameOutside_region hwf1 hm2 (r := 1) rfl hws2
  have hEr : ∀ q, NativeRustcVm.InRange E 16 q → NativeRustcVm.InRange (rowsA m0) rowsBytes q :=
    fun q hq ↦ (off_in (N := 65536) hrn (by unfold flat; omega) hq :)
  have hctx2 : Ctx m0 c st2.data :=
    hctx1.step hf2 hs2 (fun q hq ↦ Or.inl (hEr q hq))
      (fun i hi hq ↦ rows_frame_disj h (hEr _ hq) (inRange_off_self (by omega)
        (by unfold NativeRustcVm.NoWrap at hfnw; omega)))
  have hprod : NativeRustcVm.EWAt st2.data.dmem (off (rowsA m0) (16 * flat m0 s j))
      (scale m0 c s * wt c j) := by
    have := Match.ewAt_write hm2 (r := 1) (o := 0) (v0 := .reg .rax) (v1 := .reg .rdx) rfl
      (by decide) hw0 hw1
    rw [off_zero] at this
    convert this using 1
    show _ = EW.mk (UInt64.ofBitVec (reg st1.data .rax)) (UInt64.ofBitVec (reg st1.data .rdx))
    rw [show reg st1.data .rax = _ from (hm1.regs .rax _ hrax).trans hI.rax,
      show reg st1.data .rdx = _ from (hm1.regs .rdx _ hrdx).trans hI.rdx]
  have hrows2 : ElemsAt st2.data.dmem (rowsA m0)
      (prog (reg m0 .rdi).toNat c (reg m0 .r8).toNat (flat m0 s j + 1)) 4096 := by
    rw [← V_flat hj] at hprod
    rw [← prog_succ _ _ (by unfold flat; omega)]
    exact (hd1 ▸ hI.rows).update hrn (by unfold flat; omega) hs2 hprod
  have hseg2 : NativeRustcVm.WordAt st2.data.dmem (off (fbA m0) 32) (UInt64.ofNat s) :=
    bytesAt_congr (hd1 ▸ hI.segw) fun i hi ↦ by
      rw [NativeRustcVm.Transcript.off_add]
      exact hs2 _ fun hq ↦ rows_frame_disj h (hEr _ hq) (inRange_off_self (by
        rw [NativeRustcVm.length_wordBytes] at hi; omega)
        (by unfold NativeRustcVm.NoWrap at hfnw; omega))
  -- `b11`: the bit counted.
  have hwf2 := wf_body h hf2.kept (d := st2.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf2 nofun
    (hpc2.trans (label_of_infix hp b11_in_code rfl)) (match_callS hf2) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hrbx3, hr153, hr133, hrbp3, hr143⟩ := ok_b11
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hctx3 := hctx2.of_block hwf2 hm3 hmid3 hmem3
  have hrbx2 : reg st2.data .rbx = BitVec.ofNat 64 (16 * j) :=
    (hm2.regs .rbx _ hrbx').trans ((hm1.regs .rbx _ hrbx).trans hI.rbx)
  have hr152 : reg st2.data .r15 = BitVec.ofNat 64 j :=
    (hm2.regs .r15 _ hr15').trans ((hm1.regs .r15 _ hr15).trans hI.r15)
  have eRbx : reg st3.data .rbx = BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show reg st3.data .rbx = _ from hm3.regs .rbx _ hrbx3]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show (frameEnv m0 st2.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .rbx = _ from hrbx2,
      add_ofNat]
    congr 1; omega
  have eR15 : reg st3.data .r15 = BitVec.ofNat 64 (j + 1) := by
    rw [show reg st3.data .r15 = _ from hm3.regs .r15 _ hr153]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show (frameEnv m0 st2.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .r15 = _ from hr152,
      add_ofNat]
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64] at hpc3
  rw [show (frameEnv m0 st2.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .rbx = _ from hrbx2,
    add_ofNat, beq_ofNat (by omega) (by omega)] at hpc3
  by_cases hlast : j + 1 = 1600
  · rw [decide_eq_true (show 16 + 16 * j = 25600 by omega)] at hpc3
    simp only [ite_true] at hpc3
    refine .done _ (Or.inr ⟨hlast, hpc3.trans (label_of_infix hp b8_in_code rfl),
      ⟨hctx3, hs, hd3 ▸ hseg2, ?_⟩⟩)
    rw [hd3, show 1600 * ((reg m0 .r8).toNat + (s + 1)) = flat m0 s j + 1 by unfold flat; omega]
    exact hrows2
  · rw [decide_eq_false (show ¬16 + 16 * j = 25600 by omega)] at hpc3
    simp only [Bool.false_eq_true, ite_false] at hpc3
    refine .done _ (Or.inl ⟨by omega, hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b11_next),
      ⟨hctx3, hs, by omega, hd3 ▸ hseg2, ?_, ?_, ?_, eR15, eRbx, ?_⟩⟩)
    · exact (hm3.regs .r13 _ hr133).trans ((hm2.regs .r13 _ hr13').trans
        ((hm1.regs .r13 _ hr13).trans hI.r13))
    · exact (hm3.regs .rbp _ hrbp3).trans ((hm2.regs .rbp _ hrbp').trans
        ((hm1.regs .rbp _ hrbp).trans hI.rbp))
    · exact (hm3.regs .r14 _ hr143).trans ((hm2.regs .r14 _ hr14').trans
        ((hm1.regs .r14 _ hr14).trans hI.r14))
    · rw [hd3, show flat m0 s (j + 1) = flat m0 s j + 1 by unfold flat; omega]
      exact hrows2

end

end NativeRustcVmX64.KeccakGkr.SlotWeights
