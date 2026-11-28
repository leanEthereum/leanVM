module

public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Keccak.WordsHash.Loop
public import NativeRustcVmArm.Keccak.WordsHash.PadVals

/-!
# `keccak256_words::<hash_words's closure>`: the entry

`setup_run`: from the entry, the entry block (`entry`, `b0`) saves X19 to X30 in the frame and
calls `memset` to zero the 25 lanes at the frame's byte 8; the setup block (`setup`, `b1`) puts
`min(count, n) = n` in X22, the whole blocks' count `len / 136` in X24 (`nb_val`) and their words'
`17 nb` in X23 (`nb17_val`), and branches on `136 ≤ len` (`SetupAt`: `Ctx`, the lanes zero).
`entry_run`: then the head of the first whole block (`fullInit`, `b20`: X25 zero, X26 the slice's
byte 64), or, with no whole block, the last block's head (`TailStart`, the state `wordBlocks … 0`
zero).
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep same_region)
open NativeRustcVmArm.Keccak NativeRustcVm.Keccak Vm.Keccak256WordsOfHashWords

@[expose] public section

/-- **After the setup**: `Ctx`, the lanes zero, at the first whole block's set-up if `len` holds
one, else at the last block's head. -/
def SetupAt [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (fun _ => 0) ∧
    st.pc = if 136 ≤ m0.regs.X2.toNat then Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b20Offset) else Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b2Offset)

end

public section

theorem lane_replicate (i : Nat) : Keccak.lane (Vector.replicate 25 0 : KeccakState) i = 0 := by
  unfold Keccak.lane
  simp only [Vector.toArray_replicate, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- The saved slots are past the lanes. -/
theorem not_inRange_lanes {m0 : MachineData}
    (hstk : StackOk m0 NativeRustcVmArm.keccak256WordsStack) {o : Nat} (ho : 208 ≤ o)
    (ho' : o + 8 ≤ 288) : ∀ i < 8, ¬ InRange (frame m0 + BitVec.ofNat 64 8) 200
      (frame m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  intro i hi
  have hf := frame_noWrap hstk
  unfold NoWrap at hf
  rw [addr_add, Hasher.inRange_add_iff (by omega) (by omega) (by decide)]
  omega

/-- The lanes are in the frame. -/
theorem inFrame_of_lanes {m0 : MachineData}
    (hstk : StackOk m0 NativeRustcVmArm.keccak256WordsStack) {p : BitVec 64}
    (h : InRange (frame m0 + BitVec.ofNat 64 8) 200 p) : InRange (frame m0) 288 p := by
  have hf := frame_noWrap hstk
  unfold NoWrap at hf
  have h8 : (frame m0 + BitVec.ofNat 64 8).toNat = (frame m0).toNat + 8 :=
    toNat_add_ofNat _ _ (by omega)
  rw [inRange_iff (by rw [h8]; omega), h8] at h
  rw [inRange_iff hf]
  omega

/-- A word of zero bytes is zero. -/
theorem wordAt_zero {d : DataMem} {a : BitVec 64} {x : UInt8} (hx : x = 0)
    (h : BytesAt d a (List.replicate 200 x)) {i : Nat} (hi : i < 25) :
    WordAt d (a + BitVec.ofNat 64 (8 * i)) (0 : UInt64).toBitVec := by
  intro t ht
  simp only [List.length_map, List.length_range] at ht
  rw [addr_add, h (8 * i + t) (by rw [List.length_replicate]; omega), List.getElem_replicate, hx]
  simp [byteOf]

variable [Host]

/-- **The entry and the setup.** -/
theorem setup_run (hms : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost) {k : Nat}
    (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    (hx14 : m0.regs.X1.toNat = m0.regs.X4.toNat) :
    Eventually (step1 Host.exe) (SetupAt m0 k) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b0Offset)⟩ := by
  have hstk := g.stk
  have hf := frame_noWrap hstk
  unfold NoWrap at hf
  have h8 : (frame m0 + BitVec.ofNat 64 8).toNat = (frame m0).toNat + 8 :=
    toNat_add_ofNat _ _ (by omega)
  let env0 := Env.ofMachine m0 [(frame m0, 288)]
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk fun _ h => h, frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm0 : Match env0 startEntry m0 :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by
        show _ = frame m0 + BitVec.ofInt 64 288
        simp only [frame]
        exact (BitVec.sub_add_cancel _ _).symm) trivial trivial trivial trivial
  have hb0 : env0.regions[0]? = some (frame m0, 288) := rfl
  refine exec_then (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) entry hwf0 hm0
    fun st1 hm1 hpc1 => ?_
  have hx0 : st1.data.regs.X0.toBitVec = frame m0 + BitVec.ofNat 64 8 :=
    (hm1.regs .X0 _ rfl).trans (by simp [Sym.eval, env0])
  have hx1 : st1.data.regs.X1 = 0 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X1 _ rfl).trans (by simp [Sym.eval]))
  have hx2 : st1.data.regs.X2.toNat = 200 := by
    have := hm1.regs .X2 _ rfl
    simp only [Sym.eval] at this
    rw [← UInt64.toNat_toBitVec]
    exact (congrArg BitVec.toNat this).trans (by simp)
  have hsp1 : st1.data.regs.SP.toBitVec = frame m0 := hm1.sp.trans (by simp [Sym.eval, env0])
  have hpre1 : MemsetPre st1.data := by
    unfold MemsetPre
    rw [hx0, hx2]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [addr_add]
      exact frame_mapped hstk (hm1.kept hwf0) _ (by omega)
    · unfold NoWrap
      rw [h8]
      omega
  refine call_then hpc1 hms hpre1 fun st2 hpc2 hpost => ?_
  obtain ⟨-, hzero, hsame2, hsaved2⟩ := hpost
  simp only [hx0, hx1, hx2] at hzero hsame2
  rw [NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b0_length, NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b0Length, NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b0Offset, Nat.add_zero] at hpc2
  let env2 := Env.ofMachine st2.data [(frame m0, 288)]
  have hwf2 : env2.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk fun p h => hsaved2.2.2 p (hm1.kept hwf0 p h),
      frame_noWrap hstk⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm2 : Match env2 startMain st2.data :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by rw [hsaved2.2.1, hsp1]; simp [Sym.eval]) trivial trivial trivial trivial
  have hb2 : env2.regions[0]? = some (frame m0, 288) := rfl
  -- the registers `setup` reads
  have r2 : ∀ r, calleeSaved r = true →
      (st2.data.regs.getXReg r).toBitVec = (st1.data.regs.getXReg r).toBitVec :=
    fun r hr => by rw [hsaved2.1 r hr]
  have e20 : (st2.data.regs.getXReg .X20).toBitVec = BitVec.ofNat 64 m0.regs.X2.toNat := by
    rw [r2 .X20 rfl, hm1.regs .X20 _ rfl]
    show m0.regs.X2.toBitVec = _
    simp
  have e21 : (st2.data.regs.getXReg .X21).toBitVec = m0.regs.X3.toBitVec := by
    rw [r2 .X21 rfl, hm1.regs .X21 _ rfl]
    rfl
  have e22 : (st2.data.regs.getXReg .X22).toBitVec = m0.regs.X4.toBitVec := by
    rw [r2 .X22 rfl, hm1.regs .X22 _ rfl]
    rfl
  have e23 : (st2.data.regs.getXReg .X23).toBitVec = m0.regs.X4.toBitVec := by
    rw [r2 .X23 rfl, hm1.regs .X23 _ rfl]
    exact congrArg UInt64.toBitVec (UInt64.toNat_inj.mp hx14)
  have e19 : (st2.data.regs.getXReg .X19).toBitVec = m0.regs.X0.toBitVec := by
    rw [r2 .X19 rfl, hm1.regs .X19 _ rfl]
    rfl
  have hlt := m0.regs.X2.toNat_lt
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) setup hwf2 hpc2 hm2
    fun st3 hm3 hpc3 => .done _ ⟨?_, ?_, ?_⟩
  · -- the saved slots: written by `entry`, kept by `memset` and `setup`
    have hslot : ∀ {o : Nat} {w : BitVec 64}, 208 ≤ o → o + 8 ≤ 288 →
        WordAt st1.data.dmem (frame m0 + BitVec.ofNat 64 o) w →
        WordAt st3.data.dmem (frame m0 + BitVec.ofNat 64 o) w := fun ho ho' h =>
      wordAt_keep hm3 hb2 ho' rfl (bytesAt_of_same hsame2 h fun i hi =>
        not_inRange_lanes hstk ho ho' i (by simpa using hi))
    refine ⟨hm3.sp.trans (by simp [Sym.eval, env2]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hm3.regs .X19 _ rfl).trans e19
    · exact (hm3.regs .X20 _ rfl).trans (e20.trans (by simp))
    · exact (hm3.regs .X21 _ rfl).trans e21
    · refine (hm3.regs .X22 _ rfl).trans ?_
      simp only [Sym.eval, env2, Env.ofMachine_regs]
      rw [e23, e22, ite_self]
    · refine (hm3.regs .X23 _ rfl).trans ?_
      simp only [Sym.eval, env2, Env.ofMachine_regs]
      rw [e20, nb_val _ hlt, nb17_val]
      rfl
    · refine (hm3.regs .X24 _ rfl).trans ?_
      simp only [Sym.eval, env2, Env.ofMachine_regs]
      rw [e20, nb_val _ hlt]
      rfl
    · exact (Match.reg_eq hm2 hm3 rfl rfl).trans
        ((hsaved2.1 .X27 rfl).trans (Match.reg_eq hm0 hm1 rfl rfl))
    · exact (Match.reg_eq hm2 hm3 rfl rfl).trans
        ((hsaved2.1 .X28 rfl).trans (Match.reg_eq hm0 hm1 rfl rfl))
    · simp only [AllOf, savedSlots]
      exact ⟨hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        trivial⟩
    · intro p hp
      have hpf : ¬ InRange (frame m0) 288 p := fun h => hp (inStack_of_frame hstk h)
      exact (same_region hm3 hwf2 hb2 (fun w hw => by cases hw) p hpf).trans
        ((hsame2 p fun h => hpf (inFrame_of_lanes hstk h)).trans
          (same_region hm1 hwf0 hb0 (by decide) p hpf))
    · exact fun p h => hm3.kept hwf2 p (hsaved2.2.2 p (hm1.kept hwf0 p h))
  · intro i hi
    have h := wordAt_zero (by rfl) hzero hi
    rw [addr_add] at h
    exact wordAt_keep hm3 hb2 (by omega) rfl h
  · simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, env2, Env.ofMachine_regs] at hpc3
    rw [hpc3, e20]
    by_cases h : 136 ≤ m0.regs.X2.toNat
    · have hu : (BitVec.ofNat 64 m0.regs.X2.toNat).ult (BitVec.ofNat 64 136) = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, decide_eq_false_iff_not]
        omega
      simp only [hu, Bool.not_false, ↓reduceIte, h]
      exact label_at hp b20_in_code rfl
    · have hu : (BitVec.ofNat 64 m0.regs.X2.toNat).ult (BitVec.ofNat 64 136) = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, decide_eq_true_eq]
        omega
      simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
      rfl

/-- **The entry**: to the head of the first whole block, or with none, of the last block. -/
theorem entry_run (hms : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost) {k : Nat}
    (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    (hx14 : m0.regs.X1.toNat = m0.regs.X4.toNat) :
    Eventually (step1 Host.exe) (fun st => FullLaneAt m0 k 0 0 NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b24Offset st ∨ TailStart m0 k st)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b0Offset)⟩ := by
  refine Eventually.bind (setup_run hms hp g hx14) fun st h => ?_
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  have hstk := g.stk
  by_cases h : 136 ≤ m0.regs.X2.toNat
  · simp only [h, ↓reduceIte] at hpc
    subst hpc
    let env := Env.ofMachine m [(frame m0, 288)]
    have hwf : env.WF :=
      Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, trivial⟩
        (List.pairwise_singleton _ _)
    have hm : Match env startMain m :=
      match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
        (by rw [hc.sp]; simp [Sym.eval]) trivial trivial trivial trivial
    refine exec_then (b20_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullInit hwf hm
      fun st hm' hpc => .done _ (.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)
    · exact ctx_step hstk hc hm' hwf rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
        (fun w hw => by cases hw)
    · rw [pre_zero]
      exact fun i hi => wordAt_of_eq (wordAt_keep (r := 0) (sz := 288) hm' rfl (by omega) rfl
        (hl i hi)) (by rw [show wordBlocks (word m0) 0 = Vector.replicate 25 0 from rfl,
          lane_replicate])
    · exact (hm'.regs .X25 _ rfl).trans (by simp [Sym.eval])
    · refine (hm'.regs .X26 _ rfl).trans ?_
      show BinOp.apply .add .W64 (m.regs.getXReg .X21).toBitVec (BitVec.ofNat 64 64) = _
      rw [add64, hc.x21, blockAddr, BitVec.add_assoc]
      rfl
    · unfold nb
      omega
    · simp only [PcOk] at hpc
      rw [hpc]
      exact label_at hp b24_in_code rfl
  · simp only [h, ↓reduceIte] at hpc
    refine .done _ (.inr ⟨hc, ?_, hpc⟩)
    have h0 : nb m0 = 0 := by unfold nb; omega
    show Lanes m0 m (Keccak.lane (wordBlocks (word m0) (nb m0)))
    rw [h0]
    exact lanes_congr hl fun i _ => (lane_replicate i).symm

end

end NativeRustcVmArm.WordsHash
