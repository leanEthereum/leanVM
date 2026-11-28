module

public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfFiatShamirIv.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Top.Seed.Basic

/-!
# `seed`: the IV and the zeros

From the entry, the prologue (`b0`) saves the callee-saved registers in the frame's last 32 bytes,
`keccak256_words` writes the IV at the frame's byte 8, `b1` and `memset` zero its bytes 72 to
207: `stage1`, to `S1`.
-/

namespace NativeRustcVmArm.Top.Seed

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Seed NativeVm.Model
open NativeRustcVm (WordsAt Region)

public section

variable [Host] {k : Nat}

theorem stage1 (hp : Placed code k)
    (hkiv : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.entryLabel) Keccak256WordsIvPre Keccak256WordsIvPost)
    (hmemset : Spec (Labels.label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost) {m0 : MachineData}
    (hpre : SeedPre m0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Seed.b2Offset) ∧ S1 m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.Seed.b0Offset)⟩ := by
  have g := geo_of hpre
  obtain ⟨⟨-, -, hmap⟩, ⟨hrcW, hrcN, -⟩, -, ⟨hbcM, -⟩, -, -, -, -, -⟩ := hpre
  obtain ⟨hs928, hs16, hF, hF8, hF72, hsb0, -, -, -, -, hrcA, hrcN', hbcA, hbcN, hn32⟩ := g
  have hrcL : LeanVM.Parameters.keccakRC.length = 24 := rfl
  have hS : seedStack = 928 := rfl
  have hK : keccak256WordsStack = 688 := rfl
  have hsl := m0.regs.SP.toBitVec.isLt
  have hn := m0.regs.X2.toBitVec.isLt
  set F := frameOf m0 with hFdef
  have hFm : Mapped m0.dmem F 240 :=
    Mapped.within hmap (by rw [hsb0]; omega) (by rw [hsb0, hF]; omega) (by rw [hsb0, hF]; omega)
  -- The prologue.
  have hwf0 : (Env.ofMachine m0 [(F, 240)]).WF :=
    Env.wf_of ⟨⟨hFm, show F.toNat + 240 ≤ 2 ^ 64 by omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match (Env.ofMachine m0 [(F, 240)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ show F.toNat % 16 = 0 by omega, trivial⟩
      (show m0.regs.SP.toBitVec = F + BitVec.ofInt 64 240 by
        rw [show BitVec.ofInt 64 240 = BitVec.ofNat 64 240 from rfl, hFdef, frameOf,
          BitVec.sub_add_cancel])
      trivial trivial trivial trivial
  refine exec_then (hb0 hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have hB1 : Body m0 240 slots (InStack m0 928) st1.data := by
    refine ⟨?_, fun p hp ↦ ?_, fun r hr hn ↦ ?_, fun q hq ↦ ?_, hm1.kept hwf0⟩
    · rw [hm1.sp]; show F + BitVec.ofInt 64 0 = F; simp
    · have hw := b0_slots p hp
      rw [after_eq run_b0] at hw
      have hsl' := slotsIn p hp
      exact hm1.bytesAt_write (r := 0) (b := F) (sz := 240) rfl (by omega) hw
    · have hr' : r ∈ [XReg.X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29] := by
        cases r <;> simp_all [calleeSaved, slots]
      have h := b0_regs r hr'
      rw [after_eq run_b0] at h
      exact UInt64.toBitVec_inj.mp (hm1.regs r _ h)
    · refine hm1.get?_mem0 hwf0 fun hw ↦ hq ?_
      have hb0m := b0_mem
      rw [after_eq run_b0] at hb0m
      have := written_sub (env := Env.ofMachine m0 [(F, 240)]) (r := 0) rfl hb0m hw
      unfold InStack
      omega
  have hsp1 : st1.data.regs.SP.toBitVec = F := hB1.sp
  have hX0_1 : st1.data.regs.X0.toBitVec = F + BitVec.ofNat 64 8 := hm1.regs .X0 _ rfl
  have hX1_1 : st1.data.regs.X1.toBitVec = m0.regs.X2.toBitVec + BitVec.ofNat 64 2 := by
    have h := hm1.regs .X1 _ rfl; sym_simp at h; exact h
  have hX2_1 : st1.data.regs.X2.toBitVec = m0.regs.X2.toBitVec <<< 3 + BitVec.ofNat 64 9 := by
    have h := hm1.regs .X2 _ rfl; sym_simp at h; rw [evalUBFM_lsl3] at h; exact h
  have hX3_1 : st1.data.regs.X3.toBitVec = m0.regs.X1.toBitVec := hm1.regs .X3 _ rfl
  have hX4_1 : st1.data.regs.X4.toBitVec = m0.regs.X2.toBitVec := hm1.regs .X4 _ rfl
  have hX19_1 : st1.data.regs.X19 = m0.regs.X3 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl)
  have hX20_1 : st1.data.regs.X20 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl)
  have hX21_1 : st1.data.regs.X21.toBitVec = F + BitVec.ofNat 64 8 := hm1.regs .X21 _ rfl
  have hsb1 : (stackBelow st1.data keccak256WordsStack).toNat =
      m0.regs.SP.toBitVec.toNat - 928 := by
    show (st1.data.regs.SP.toBitVec - BitVec.ofNat 64 688).toNat = _
    rw [hsp1, toNat_subAddr (by rw [hF]; omega), hF]; omega
  have hsb1' : (st1.data.regs.SP.toBitVec - BitVec.ofNat 64 keccak256WordsStack).toNat =
      m0.regs.SP.toBitVec.toNat - 928 := hsb1
  have hn32' : 9 + 8 * m0.regs.X2.toBitVec.toNat < 2 ^ 32 := hn32
  have hn4 : st1.data.regs.X4.toNat = m0.regs.X2.toBitVec.toNat := congrArg BitVec.toNat hX4_1
  have hx3 : st1.data.regs.X3.toBitVec.toNat = m0.regs.X1.toBitVec.toNat := by rw [hX3_1]
  have hx0 : st1.data.regs.X0.toBitVec.toNat = m0.regs.SP.toBitVec.toNat - 232 := by
    rw [hX0_1, hF8]
  -- `keccak256_words`: the IV at the frame's byte 8.
  have hpre1 : Keccak256WordsIvPre st1.data := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, hrcN, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show st1.data.regs.SP.toBitVec.toNat % 16 = 0
      rw [hsp1, hF]; omega
    · show 688 ≤ st1.data.regs.SP.toBitVec.toNat
      rw [hsp1, hF]; omega
    · exact Mapped.kept (Mapped.within hmap (by omega) (by omega) (by omega)) hB1.kept
    · exact wordsAt_keep hrcW hB1.same (by rw [hrcL]; omega) fun q hq ↦ by
        unfold InStack at hq; rw [hrcL]; omega
    · show _ ∨ _
      omega
    · show st1.data.regs.X1.toBitVec.toNat = st1.data.regs.X4.toBitVec.toNat + 2
      rw [hX1_1, hX4_1, toNat_addr (by omega)]
    · show st1.data.regs.X2.toBitVec.toNat = 9 + 8 * st1.data.regs.X4.toBitVec.toNat
      rw [hX2_1, hX4_1, toNat_addr (by rw [BitVec.toNat_shiftLeft]; omega),
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      omega
    · show 9 + 8 * st1.data.regs.X4.toNat < 2 ^ 32
      omega
    · show Mapped st1.data.dmem st1.data.regs.X3.toBitVec (8 * st1.data.regs.X4.toNat)
      rw [hX3_1, hn4]; exact Mapped.kept hbcM hB1.kept
    · show st1.data.regs.X3.toBitVec.toNat + 8 * st1.data.regs.X4.toNat ≤ 2 ^ 64
      have : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toBitVec.toNat ≤ 2 ^ 64 := hbcN
      omega
    · show Mapped st1.data.dmem st1.data.regs.X0.toBitVec 32
      rw [hX0_1]
      exact Mapped.kept (Mapped.within hFm (by omega) (by rw [hF8]; omega) (by rw [hF8]; omega))
        hB1.kept
    · show st1.data.regs.X0.toBitVec.toNat + 32 ≤ 2 ^ 64
      omega
    · intro hn0
      show _ ∨ _
      have e : m0.regs.X2.toNat = m0.regs.X2.toBitVec.toNat := rfl
      have := hbcA (by omega)
      omega
    · show _ ∨ _
      omega
    · show _ ∨ _
      rw [hX0_1, hF8]; omega
  refine call_then hpc1 hkiv hpre1 fun st2 hpc2 hpost2 ↦ ?_
  obtain ⟨hiv2, hsame2, hsaved2⟩ := hpost2
  have hsl0 := m0.regs.SP.toBitVec.isLt
  have hB2 : Body m0 240 slots (InStack m0 928) st2.data := by
    refine hB1.call slotsIn (by show 240 ≤ m0.regs.SP.toBitVec.toNat; omega) hsame2 hsaved2
      fun q hq ↦ ?_
    rcases hq with hq | hq
    · rw [inRange_nat (by omega)] at hq
      unfold InStack; omega
    · change InRange (st1.data.regs.SP.toBitVec - BitVec.ofNat 64 688) 688 q at hq
      rw [inRange_below (by rw [hsp1, hF]; omega), hsp1, hF] at hq
      unfold InStack; omega
  have e2 : m0.regs.X2.toNat = m0.regs.X2.toBitVec.toNat := rfl
  -- The IV, at the frame's byte 8.
  have hiv : ∀ w : List UInt64, w.length = m0.regs.X2.toBitVec.toNat →
      WordsAt m0.dmem m0.regs.X1.toBitVec w →
      WordsAt st2.data.dmem (F + BitVec.ofNat 64 8) (fiatShamirIv w.toArray).toList := by
    intro w hw hbc
    have h := hiv2 w (by rw [hn4]; exact hw) ?_
    · rw [hX0_1] at h; exact h
    · rw [hX3_1]
      by_cases hn0 : m0.regs.X2.toBitVec.toNat = 0
      · rw [List.eq_nil_of_length_eq_zero (hw.trans hn0)]
        exact NativeRustcVm.wordsAt_nil _ _
      · have hap := hbcA (by omega)
        exact wordsAt_keep hbc hB1.same (by rw [hw]; omega) fun q hq ↦ by
          unfold InStack at hq; rw [hw]; omega
  -- `b1`: `memset`'s arguments.
  rw [show k + NativeRustcVmArm.Vm.Seed.b0Offset + b0.length = k + NativeRustcVmArm.Vm.Seed.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Seed.b0_next]] at hpc2
  refine exec_at (hb1 hp) run_b1 (Env.wf_nil st2.data) hpc2 (match_nil st2.data)
    fun st3 hm3 hpc3 ↦ ?_
  have hk1 := b1_keeps
  rw [after_eq run_b1] at hk1
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (Env.wf_nil _) hk1.2
  have hB3 : Body m0 240 slots (InStack m0 928) st3.data :=
    hB2.block slotsIn (by show 240 ≤ m0.regs.SP.toBitVec.toNat; omega) (match_nil _) hm3
      (Env.wf_nil _) rfl hk1.1 fun p ⟨w, hw, _⟩ ↦ by rw [hk1.2] at hw; cases hw
  have hX0_3 : st3.data.regs.X0.toBitVec = F + BitVec.ofNat 64 72 := by
    have h := hm3.regs .X0 _ rfl
    have h21 : st2.data.regs.X21 = st1.data.regs.X21 := hsaved2.1 .X21 rfl
    refine h.trans ?_
    sym_simp
    show st2.data.regs.X21.toBitVec + _ = _
    rw [h21, hX21_1, addr_add]
  have hX1_3 : st3.data.regs.X1 = 0 := UInt64.toBitVec_inj.mp (hm3.regs .X1 _ rfl)
  have hX2_3 : st3.data.regs.X2.toNat = 136 := by
    show (st3.data.regs.getXReg .X2).toBitVec.toNat = 136
    rw [hm3.regs .X2 _ rfl]; rfl
  have hF72 : (F + BitVec.ofNat 64 72).toNat = m0.regs.SP.toBitVec.toNat - 168 := by
    rw [toNat_addr (by omega), hF]; omega
  have hpre3 : MemsetPre st3.data := by
    refine ⟨?_, ?_⟩
    · rw [hX0_3, hX2_3]
      exact Mapped.kept (Mapped.within hFm (by omega) (by rw [hF72]; omega) (by rw [hF72]; omega))
        hB3.kept
    · show st3.data.regs.X0.toBitVec.toNat + st3.data.regs.X2.toNat ≤ 2 ^ 64
      rw [hX0_3, hX2_3, hF72]; omega
  refine call_then hpc3 hmemset hpre3 fun st4 hpc4 hpost4 ↦ ?_
  obtain ⟨-, hz4, hsame4, hsaved4⟩ := hpost4
  rw [hX0_3, hX2_3, hX1_3] at hz4
  rw [hX0_3, hX2_3] at hsame4
  have hB4 : Body m0 240 slots (InStack m0 928) st4.data := by
    refine hB3.call slotsIn (by show 240 ≤ m0.regs.SP.toBitVec.toNat; omega) hsame4 hsaved4
      fun q hq ↦ ?_
    rw [inRange_nat (by rw [hF72]; omega), hF72] at hq
    unfold InStack; omega
  have hsp4 : st4.data.regs.SP.toBitVec = F := hB4.sp
  have hiv4 : ∀ w : List UInt64, w.length = m0.regs.X2.toBitVec.toNat →
      WordsAt m0.dmem m0.regs.X1.toBitVec w →
      WordsAt st4.data.dmem (F + BitVec.ofNat 64 8) (fiatShamirIv w.toArray).toList := by
    intro w hw hbc
    have h := hiv w hw hbc
    rw [← hd3] at h
    refine wordsAt_keep h hsame4 (by simp; omega) fun q hq ↦ ?_
    rw [inRange_nat (by rw [hF72]; omega), hF72] at hq
    simp; omega
  have hX19_4 : st4.data.regs.X19 = m0.regs.X3 := by
    have h3 : st3.data.regs.X19 = st2.data.regs.X19 := UInt64.toBitVec_inj.mp (hm3.regs .X19 _ rfl)
    have h2 : st2.data.regs.X19 = st1.data.regs.X19 := hsaved2.1 .X19 rfl
    have h4 : st4.data.regs.X19 = st3.data.regs.X19 := hsaved4.1 .X19 rfl
    exact h4.trans (h3.trans (h2.trans hX19_1))
  have hX20_4 : st4.data.regs.X20 = m0.regs.X0 := by
    have h3 : st3.data.regs.X20 = st2.data.regs.X20 := UInt64.toBitVec_inj.mp (hm3.regs .X20 _ rfl)
    have h2 : st2.data.regs.X20 = st1.data.regs.X20 := hsaved2.1 .X20 rfl
    have h4 : st4.data.regs.X20 = st3.data.regs.X20 := hsaved4.1 .X20 rfl
    exact h4.trans (h3.trans (h2.trans hX20_1))
  rw [show k + NativeRustcVmArm.Vm.Seed.b1Offset + b1.length = k + NativeRustcVmArm.Vm.Seed.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Seed.b1_next]] at hpc4
  exact Eventually.done _ ⟨hpc4, hB4, hX19_4, hX20_4, hiv4, hz4⟩

end

end NativeRustcVmArm.Top.Seed
