module

public import NativeRustcArm.Code.Common.KeccakF.Names
public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Update.Names

public import NativeRustcArm.Hasher.UpdateLoop

/-!
# `Hasher::update` on AArch64

**`update_spec`**: rustc's `Hasher::update`, placed anywhere in the program, meets its contract
(`UpdatePre`, `UpdatePost`) given the contracts of `memcpy` and `keccak_f`. The prologue (`b0`)
saves the callee-saved registers in its 64-byte frame and enters the loop (`loop_spec`) with
nothing absorbed; the epilogue (`b8`) restores them and returns the hasher.
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Update NativeRustcArm

public section

theorem stack_frame {s : BitVec 64} {i : Nat} :
    s - BitVec.ofNat 64 256 + BitVec.ofNat 64 (192 + i) = s - 64#64 + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.isLt
  omega

theorem toBitVec_eq_ofNat (x : UInt64) : x.toBitVec = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt x.toBitVec.isLt).symm

variable [Host] {k : Nat}

set_option linter.unusedSimpArgs false in
/-- **`Hasher::update` meets its contract.** -/
theorem update_spec (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hkf : Spec (Labels.label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    Spec (Labels.label NativeRustcArm.Common.Update.entryLabel) UpdatePre UpdatePost := by
  intro m0 hpre
  have g := geo_of hpre
  have hs := g.s
  have hal := g.al
  rw [lbl_entry hp]
  -- The prologue.
  have hmapF : Mapped m0.dmem (spAt m0 - 64#64) 64 := fun i hi => by
    have := hpre.1.2.2 (192 + i) (by show 192 + i < 256; omega)
    rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 updateStack + BitVec.ofNat 64 (192 + i) =
      spAt m0 - 64#64 + BitVec.ofNat 64 i from stack_frame] at this
  have hF64 : (spAt m0 - 64#64).toNat = (spAt m0).toNat - 64 := toNat_sub_ofNat (by omega)
  have hwf0 : (Env.ofMachine m0 [(spAt m0 - 64#64, 64), (hAt m0, 344)]).WF :=
    Env.wf_of ⟨⟨hmapF, by show _ + 64 ≤ _; rw [hF64]; have := (spAt m0).isLt; omega⟩,
      ⟨hpre.2.2.2.1, g.h⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        show (spAt m0 - 64#64).toNat + 64 ≤ (hAt m0).toNat ∨ (hAt m0).toNat + 344 ≤ (spAt m0 - 64#64).toNat
        rw [hF64]; have := g.hs; omega))
  have hbF : (Env.ofMachine m0 [(spAt m0 - 64#64, 64), (hAt m0, 344)]).base 0 = spAt m0 - 64#64 :=
    Env.base_ofMachine m0 _ _ rfl
  have hbH : (Env.ofMachine m0 [(spAt m0 - 64#64, 64), (hAt m0, 344)]).base 1 = hAt m0 :=
    Env.base_ofMachine m0 _ _ rfl
  have hm0 : Match (Env.ofMachine m0 [(spAt m0 - 64#64, 64), (hAt m0, 344)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ => by rw [hF64]; omega, rfl, by simp, trivial⟩
      (by
        simp only [Sym.eval, hbF]
        show spAt m0 = spAt m0 - 64#64 + 64#64
        exact (BitVec.sub_add_cancel _ _).symm)
      ⟨by simp only [Sym.eval, hbH]; simp [hAt]; rfl, trivial⟩ trivial trivial trivial
  refine exec_then (hb0 hp) run_b0 hwf0 hm0 fun m1s hm1 hpc1 => ?_
  obtain ⟨m1, pc1⟩ := m1s
  simp only [PcOk, lbl_2 hp] at hpc1
  subst hpc1
  have hl0 := b0_mem
  rw [after_eq run_b0] at hl0
  have hsl0 := b0_slots
  rw [after_eq run_b0] at hsl0
  have h01 : SameOutside m0.dmem m1.dmem (InRange (spAt m0 - 64#64) 64) := fun p hp =>
    hm1.get?_mem0 hwf0 fun hw => hp ((inRange_iff (by rw [hF64]; have := (spAt m0).isLt; omega)).mpr
      (written_hasher hl0 hw))
  have hH1 : hasher m0 m1 = hasher m0 m0 := bytesOf_congr fun i hi => h01 _ (by
    rw [frame_iff g, toNat_add_ofNat' (by have := g.h; omega)]
    have := g.hs
    omega)
  have hkept1 := hm1.kept hwf0
  have hinv : Inv m0 m1 0 m1 := by
    refine ⟨⟨?_, ?_, ?_, ?_, fun r hr => ?_, fun _ _ => rfl, hkept1⟩, Nat.zero_le _, ?_, ?_, ?_, ?_⟩
    · rw [hm1.regs .X20 _ rfl]; simp only [Sym.eval, hbH]; simp
    · rw [hm1.regs .X23 _ rfl]; simp only [Sym.eval, hbH]; rfl
    · rw [hm1.regs .X24 _ rfl]; rfl
    · rw [hm1.sp]; simp only [Sym.eval, hbF]; simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_atom hm1 rfl
    · rw [hm1.regs .X19 _ rfl, Nat.sub_zero]
      exact toBitVec_eq_ofNat _
    · rw [hm1.regs .X21 _ rfl]
      show m0.regs.X1.toBitVec = _
      simp [dAt]
    · show (m1.regs.getXReg .X0).toBitVec.toNat = _
      rw [hm1.regs .X0 _ rfl, hH1]
      simp only [Sym.eval]
      rw [load_eq_bytesOf _ hbH (N := 344) (by omega) hpre.2.2.2.1, List.take_of_length_le
        (by simp [length_bytesOf]), bufLen_ofBytes (length_bytesOf ..)]
      rfl
    · intro a ha
      rw [List.take_zero, List.append_nil, hH1]
      exact ha
  -- The loop.
  refine NativeRustcArm.Eventually.bind (loop_spec hp hmemcpy hkf hpre h01 hinv)
    fun st ⟨hpc, hfin⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  -- The epilogue.
  have hfr := hfin.frame
  have hframe : ∀ i < 64, d.dmem.get? (spAt m0 - 64#64 + BitVec.ofNat 64 i) =
      m1.dmem.get? (spAt m0 - 64#64 + BitVec.ofNat 64 i) := fun i hi =>
    hfr.same _ (by
      rw [chg_iff g, show (spAt m0 - 64#64 + BitVec.ofNat 64 i).toNat = (spAt m0).toNat - 64 + i by
        rw [toNat_add_ofNat' (by rw [hF64]; have := (spAt m0).isLt; omega), hF64]]
      have := g.hs
      omega)
  have hwf8 : (Env.ofMachine d [(spAt m0 - 64#64, 64)]).WF :=
    Env.wf_of ⟨⟨fun i hi => hfr.kept _ (hmapF i hi),
      by show _ + 64 ≤ _; rw [hF64]; have := (spAt m0).isLt; omega⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hbase8 : (Env.ofMachine d [(spAt m0 - 64#64, 64)]).base 0 = spAt m0 - 64#64 :=
    Env.base_ofMachine d _ _ rfl
  have hm8 : Match (Env.ofMachine d [(spAt m0 - 64#64, 64)]) exitS d :=
    match_ofMachine ⟨rfl, fun _ => by rw [hF64]; omega, trivial⟩
      (by rw [hfr.sp]; simp only [Sym.eval, hbase8]; simp) trivial trivial trivial trivial
  -- The slots hold the registers at the entry.
  have hslot : ∀ p ∈ slots, (Env.ofMachine d [(spAt m0 - 64#64, 64)]).load 0 p.1 8 =
      (m0.regs.getXReg p.2).toBitVec := by
    intro p hpm
    have hle : p.1 + 8 ≤ 64 := by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hpm
      rcases hpm with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
    have hw : BytesAt m1.dmem (spAt m0 - 64#64 + BitVec.ofNat 64 p.1)
        ((List.range 8).map (byteOf (m0.regs.getXReg p.2).toBitVec)) :=
      hm1.bytesAt_write (r := 0) (o := p.1) (n := 8) (sz := 64) rfl hle (hsl0 p hpm)
    rw [Env.load_of_bytesAt (bs := (List.range 8).map (byteOf (m0.regs.getXReg p.2).toBitVec))
      (by simp) ?_, ofInt_ofBytes_byteOf]
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    rw [hbase8, add_ofNat_add, Env.ofMachine_mem0, hframe _ (by omega), ← add_ofNat_add, hw i
      (by simp [hi])]
  refine exec_then (hb8 hp) run_b8 hwf8 hm8 fun st hm' hpc' => ?_
  have hsp' : st.data.regs.SP = m0.regs.SP := by
    apply UInt64.toBitVec_inj.mp
    rw [hm'.sp]
    simp only [Sym.eval, hbase8]
    exact BitVec.sub_add_cancel _ _
  have hreg : ∀ p ∈ slots, st.data.regs.getXReg p.2 = m0.regs.getXReg p.2 := by
    intro p hpm
    apply UInt64.toBitVec_inj.mp
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hm'.regs .X19 _ rfl]; exact hslot (56, .X19) (by simp [slots])
    · rw [hm'.regs .X20 _ rfl]; exact hslot (48, .X20) (by simp [slots])
    · rw [hm'.regs .X21 _ rfl]; exact hslot (40, .X21) (by simp [slots])
    · rw [hm'.regs .X22 _ rfl]; exact hslot (32, .X22) (by simp [slots])
    · rw [hm'.regs .X23 _ rfl]; exact hslot (24, .X23) (by simp [slots])
    · rw [hm'.regs .X24 _ rfl]; exact hslot (16, .X24) (by simp [slots])
    · rw [hm'.regs .X30 _ rfl]; exact hslot (8, .X30) (by simp [slots])
    · rw [hm'.regs .X29 _ rfl]; exact hslot (0, .X29) (by simp [slots])
  have hmem' : ∀ p, st.data.dmem.get? p = d.dmem.get? p := fun p =>
    hm'.get?_mem0 hwf8 fun ⟨_, hw, _⟩ => by simp at hw
  have hX30 : retOf st.data = retOf m0 := by
    unfold retOf
    rw [show st.data.regs.X30 = m0.regs.X30 from hreg (8, .X30) (by simp [slots])]
  refine Eventually.done _ ⟨by simpa [PcOk, hX30] using hpc', ?_, ?_, ?_, ?_⟩
  · -- X0: the hasher.
    apply UInt64.toBitVec_inj.mp
    show (st.data.regs.getXReg .X0).toBitVec = _
    rw [hm'.regs .X0 _ rfl]
    exact hfr.x20
  · -- The hasher absorbed the input.
    intro a ha
    have := hfin.holds a ha
    rw [List.take_of_length_le (by rw [length_input])] at this
    show HasherHolds (hasher m0 st.data) (a ++ input m0)
    rwa [show hasher m0 st.data = hasher m0 d from bytesOf_congr fun i _ => hmem' _]
  · -- Memory outside the hasher and the stack.
    intro p hp
    have hs256 : (stackBelow m0 updateStack).toNat = (spAt m0).toNat - 256 :=
      stackBelow_toNat (by show 256 ≤ (spAt m0).toNat; omega)
    change ¬(InRange (hAt m0) 344 p ∨ InRange (stackBelow m0 updateStack) 256 p) at hp
    rw [inRange_iff g.h, inRange_iff (by rw [hs256]; have := (spAt m0).isLt; omega), hs256] at hp
    rw [hmem' p, hfr.same p (by rw [chg_iff g]; omega), h01 p (by rw [frame_iff g]; omega)]
  · -- The registers kept.
    refine ⟨fun r hr => ?_, hsp', fun p hp => ?_⟩
    · cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr
      · exact hreg (56, .X19) (by simp [slots])
      · exact hreg (48, .X20) (by simp [slots])
      · exact hreg (40, .X21) (by simp [slots])
      · exact hreg (32, .X22) (by simp [slots])
      · exact hreg (24, .X23) (by simp [slots])
      · exact hreg (16, .X24) (by simp [slots])
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X25 (by simp))
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X26 (by simp))
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X27 (by simp))
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X28 (by simp))
      · exact hreg (0, .X29) (by simp [slots])
    · rw [hmem' p]
      exact hfr.kept p hp

end

end NativeRustcArm.Hasher.Update
