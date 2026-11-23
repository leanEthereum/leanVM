module

public import NativeRustcVmArm.Wire.Decode.Dec

/-!
# `decode`'s phases

The loop at `.LDecode_6` (`b9`), `k` of the `p` phases read (`LInv`): no phase left, the check
that no byte is (`b16`, `done_spec`); else a slot left (`b10`), `phase_m`'s call (`b11`,
`call_spec`), its outcome (`b12`): the next phase, or `None` (`b13`). `loop_spec`: the whole loop.
-/

namespace NativeRustcVmArm.Wire.Decode

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeVm.Model
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVm.Transcript (DecArea DecodedAt PhaseAt)
open NativeRustcVmArm.Vm.Decode
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- What the reads before the phases fixed: the stream's `n` elements of words `ws`, the phase
count `p`, the phases from `cs`. -/
structure Fix (m0 : MachineData) (B : List UInt8) (n : Nat) (ws : List K) (p cs : Nat) : Prop where
  ws_len : ws.length = 2 * n
  n_le : n ≤ maxStream (Ln m0)
  p_le : p ≤ wireMaxPhases
  l_pos : 0 < Ln m0
  dec : decodeM B = match phasesM B p cs with
    | none => none
    | some (ps, c) => if c ≠ B.length then none else some (streamOf n ws, ps)

/-- **The loop's state** at `.LDecode_6` (`b9`), `k` phases read. -/
structure LInv [Host] (k0 : Nat) (m0 : MachineData) (B : List UInt8) (n : Nat) (ws : List K)
    (p cs k : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.Decode.b9Offset)
  fr : Frm m0 st.data
  x19 : st.data.regs.getXReg .X19 = m0.regs.X4
  x20 : st.data.regs.getXReg .X20 = m0.regs.X1
  x21 : (st.data.regs.getXReg .X21).toBitVec + BitVec.ofNat 64 phaseBytes =
    dw m0 (phaseBase (Ln m0) k)
  x22 : 9 ≤ (st.data.regs.getXReg .X22).toNat + k
  x23 : (st.data.regs.getXReg .X23).toNat + k = p
  x24 : (st.data.regs.getXReg .X24).toNat = phaseBytes
  ex : ∃ ps ck, phasesM B k cs = some (ps, ck) ∧
    ReaderAt st.data.dmem (rdr m0) (bpA m0) B ck ∧ DecF m0 st.data.dmem n ws p ps

end

public section

variable {m0 : MachineData} {B : List UInt8} {n : Nat} {ws : List K} {p cs : Nat}

theorem keepOk {S S' : SState}
    (h : keep.all (fun r ↦ S.reg r == some (.reg r) && S'.reg r == some (.reg r)) = true) :
    ∀ r ∈ keep, ∃ v, S.reg r = some v ∧ S'.reg r = some v := by
  intro r hr
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨_, h r hr⟩

theorem eq_lit (x : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  rw [eq_apply, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem Fix.hn (F : Fix m0 B n ws p cs) : 1 + 2 * n ≤ streamEnd (Ln m0) := by
  have := F.n_le; unfold streamEnd; omega

section
variable [Labels]

/-- **The round constants** for a callee using `N'` bytes of stack below the frame. -/
theorem Geo.rcAt (G : Geo m0 B) {m : MachineData} (hfr : Frm m0 m) {N' : Nat}
    (hN' : 96 + N' ≤ 1280) : NativeRustcVmArm.RcAt m N' := by
  obtain ⟨hw, hnw, hap⟩ := G.rc
  have hb := Ring.base_noWrap (m0 := m0) (F := 1280) G.sp
  refine ⟨NativeRustcVm.BytesAt.of_sameOutside hw hfr.same fun i hi hq ↦ ?_, hnw,
    hfr.apart G.sp hap hN'⟩
  have hi' : i < 192 := by
    rw [NativeRustcVm.length_wordsBytes, show keccakRC.length = 24 from rfl] at hi
    omega
  have hin : InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi' (by unfold NoWrap at hnw; omega)
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange G.sC.symm hnw hb hin hq
  · rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange G.cD hnw G.dNw hin hq
    · exact NativeRustcVm.Apart.not_inRange G.cW hnw G.wNw hin hq

end

variable [Host] {k0 : Nat}

/-- **No phase left**: the check that no byte is (`b16`). -/
theorem done_spec (hp : Placed code k0) (G : Geo m0 B) (F : Fix m0 B n ws p cs)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmArm.Vm.Decode.b16Offset)) (hfr : Frm m0 st.data)
    (x20 : st.data.regs.getXReg .X20 = m0.regs.X1) {ps : List PhaseOut} {ck : Nat}
    (hph : phasesM B p cs = some (ps, ck)) (hR : ReaderAt st.data.dmem (rdr m0) (bpA m0) B ck)
    (hD : DecF m0 st.data.dmem n ws p ps) :
    Eventually (step1 Host.exe) (Res m0 B) st := by
  have hwf := frEnv_wf G.st hfr
  have hm := frEnv_match G.st hfr
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf hpc hm fun s hm' hpc' ↦ ?_
  have hm'' := hm'
  rw [← after_eq run_b16] at hm''
  obtain ⟨hret, hsv⟩ := Fr.exit hfr hm'' hwf (by decide +kernel)
  have hd : s.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  have hcur : (frEnv m0 st.data).load 0 24 8 = ck.toUInt64.toBitVec := by
    refine load_word ?_
    have := hR.cur
    rw [cur_eq] at this
    exact this
  have hck := hR.c_le
  have hL := G.l32
  have hlen := G.len
  have hx0 : s.data.regs.X0 = if ck = Ln m0 then 1 else 0 := by
    apply UInt64.toBitVec_inj.mp
    rw [show s.data.regs.X0 = s.data.regs.getXReg .X0 from rfl, hm'.regs .X0 _ rfl]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, Sym.low_W64, hcur, Env.ofMachine_regs, x20]
    by_cases h : ck = Ln m0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      have : ck.toUInt64.toBitVec = m0.regs.X1.toBitVec := by
        apply BitVec.eq_of_toNat_eq
        rw [UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by omega), h]
        rfl
      simp [this]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
      have : (ck.toUInt64.toBitVec == m0.regs.X1.toBitVec) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        have := congrArg BitVec.toNat he
        rw [UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by omega)] at this
        exact h this
      simp [this]
  refine .done _ ⟨by simp only [PcOk] at hpc'; rw [hpc', hret], ?_, by
    rw [hd]; exact same_res hfr, hsv⟩
  rw [F.dec, hph]
  dsimp only
  rw [hx0]
  by_cases h : ck = Ln m0
  · have hc : ¬(ck ≠ B.length) := by rw [hlen]; exact not_not.mpr h
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_left_of_eq_true _ _ (eq_true h)]
    refine ⟨rfl, ?_⟩
    rw [hd]
    exact hD.decodedAt G F.ws_len F.n_le (phasesM_length B p cs hph) F.p_le
  · have hc : ck ≠ B.length := by rw [hlen]; exact h
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_right_of_eq_false _ _ (eq_false h)]

end

end NativeRustcVmArm.Wire.Decode
