module

public import NativeRustcArm.Code.Common.KeccakF.Names

public import NativeRustcArm.Hasher.UpdateB5

/-!
# `Hasher::update`'s loop: absorbing a full buffer

`b6` XORs the buffer's 17 lanes into the state's (`xorBlock`) and calls `keccak_f` on the state;
on its return the state is `absorb` of the state and the buffer (`Absorbed`, `b6_spec`).
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustc NativeRustc.Keccak LeanVM.Protocol.KeccakHash NativeRustcArm.Sym
open NativeRustcArm.Common.Update NativeRustcArm

@[expose] public section

/-- After `keccak_f`: the state absorbed the full buffer. -/
structure Absorbed (m0 m1 : MachineData) (c : Nat) (Hc : List UInt8) (m : MachineData) : Prop where
  frame : Frame m0 m1 m
  le : c ≤ nOf m0
  x19 : (m.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 (nOf m0 - c)
  x21 : (m.regs.getXReg .X21).toBitVec = dAt m0 + BitVec.ofNat 64 c
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 (takeN m0 c Hc)
  holds : Holds m0 Hc c
  lt : bufLen Hc < 136
  len : Hc.length = 344
  full : bufLen Hc + takeN m0 c Hc = 136
  bytes : hasher m0 m = writeAt (counted m0 c Hc) 0
    (absorb ((counted m0 c Hc).take 200) (((counted m0 c Hc).drop 200).take 136))

end

public section

theorem sp_sub_sub (s : BitVec 64) : s - 64#64 - BitVec.ofNat 64 192 = s - 256#64 := by
  rw [BitVec.sub_sub]
  rfl

variable [ElfHost] {sec k : Nat}

/-- **Absorbing a full buffer.** -/
theorem b6_spec (hp : PlacedIn code sec k)
    (hkf : ElfSpec (Labels.label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    {m0 m1 m : MachineData} (hpre : UpdatePre m0)
    (h01 : SameOutside m0.dmem m1.dmem (InRange (spAt m0 - 64#64) 64)) {c : Nat}
    {Hc : List UInt8} (hfu : Full m0 m1 c Hc m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b7Offset) ∧ Absorbed m0 m1 c Hc st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b6Offset)⟩ := by
  have g := geo_of hpre
  have gr := geoRc_of hpre
  have hwf := wf_head hpre hfu.frame
  have hm := match_headS hfu.frame
  have hb0 : (Env.ofMachine m [(hAt m0, 344)]).base 0 = hAt m0 := Env.base_ofMachine m _ _ rfl
  have hH : hasher m0 m = counted m0 c Hc := hfu.bytes
  generalize hc2 : counted m0 c Hc = H2 at hH
  have hlen2 : H2.length = 344 := by rw [← hH]; exact length_bytesOf ..
  refine exec_then_elf (hb6 hp) run_b6 hwf hm fun st6 hm6 hpc6 => ?_
  have hl := b6_mem
  rw [after_eq run_b6] at hl
  have hmem6 : ∀ j < 344, (st6.data.dmem.get? (hAt m0 + BitVec.ofNat 64 j)).getD 0 =
      if j < 136 then H2.getD j 0 ^^^ H2.getD (200 + j) 0 else H2.getD j 0 := by
    intro j hj
    rw [hm6.mem 0 _ 344 rfl j hj, hl]
    unfold memByte
    rw [findWrite_lanes j hj]
    by_cases h : j < 136
    · rw [ite_pos' h, ite_pos' h]
      simp only [Option.getD_some, Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [byteOf_xor, byteOf_load (by omega) (by omega), byteOf_load (by omega) (by omega), hb0,
        Env.ofMachine_mem0, show 8 * (j / 8) + j % 8 = j by omega,
        show 200 + 8 * (j / 8) + j % 8 = 200 + j by omega, ← hH, hasher,
        getD_bytesOf _ _ (by omega), getD_bytesOf _ _ (by omega)]
    · rw [ite_neg' h, ite_neg' h]
      simp only [Env.ofMachine_mem0]
      rw [← hH, hasher, getD_bytesOf _ _ hj]
  have hxor : bytesOf st6.data.dmem (hAt m0) 200 =
      NativeRustc.Keccak.xorBlock (H2.take 200) ((H2.drop 200).take 136) := by
    refine ext_getD (by simp [length_bytesOf, NativeRustc.Keccak.xorBlock, length_stateBytes])
      fun j hj => ?_
    rw [length_bytesOf] at hj
    rw [getD_bytesOf _ _ hj, hmem6 j (by omega), getD_xorBlock _ _ hj, Native.Keccak.Proof.getD_take,
      ite_pos' hj]
    by_cases h : j < 136
    · rw [ite_pos' h, ite_pos' h, Native.Keccak.Proof.getD_take, ite_pos' h,
        Native.Keccak.Proof.getD_drop]
    · rw [ite_neg' h, ite_neg' h]
  have hsp6 : st6.data.regs.SP.toBitVec = spAt m0 - 64#64 := by
    rw [hm6.sp]
    exact hfu.frame.sp
  have hs := g.s
  have hspN : st6.data.regs.SP.toNat = (spAt m0).toNat - 64 := by
    show st6.data.regs.SP.toBitVec.toNat = _
    rw [hsp6]
    exact toNat_sub_ofNat (by omega)
  have hsb : stackBelow st6.data 192 = spAt m0 - 256#64 := by
    rw [stackBelow, hsp6, sp_sub_sub]
  have hsbN : (spAt m0 - 256#64).toNat = (spAt m0).toNat - 256 := toNat_sub_ofNat (by omega)
  have hX0 : st6.data.regs.X0.toBitVec = hAt m0 := by
    show (st6.data.regs.getXReg .X0).toBitVec = _
    rw [hm6.regs .X0 _ rfl]
    simp only [Sym.eval, hb0]
    simp
  have hnw6 : ∀ p, ¬(hAt m0).toNat ≤ p.toNat ∨ ¬p.toNat < (hAt m0).toNat + 344 →
      st6.data.dmem.get? p = m.dmem.get? p := fun p hp =>
    hm6.get?_mem0 hwf fun hw => by
      have := written_hasher (by rw [hl]; decide) hw
      omega
  refine call_then_elf hpc6 hkf ?pre fun st' hpc' hpost => ?_
  case pre =>
    simp only [KeccakFPre, keccakFStack]
    refine ⟨⟨by rw [hspN]; have := g.al; omega, by rw [hspN]; omega, fun i hi => ?_⟩,
      ⟨fun i hi => ?_, gr.nw, ?_⟩, fun i hi => ?_, ?_, ?_, ?_⟩
    · rw [show st6.data.regs.SP.toBitVec - BitVec.ofNat 64 192 = stackBelow st6.data 192 from rfl,
        hsb]
      exact hm6.kept hwf _ (hfu.frame.kept _ (by
        have := hpre.1.2.2 i (by show i < 256; omega)
        rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 updateStack = spAt m0 - 256#64 from rfl]
          at this))
    · have hrc := hpre.2.1.1 i hi
      have hrcl : rcBytes.length = 192 := by
        rw [rcBytes, List.length_flatMap]
        simp only [length_wordBytes]
        rfl
      rw [hrcl] at hi
      rw [hnw6 _ (by rw [toNat_add_ofNat' (by have := gr.nw; omega)]; have := gr.hr; omega),
        rc_same g gr hfu.frame h01 hi]
      exact hrc
    · show _ + 192 ≤ (stackBelow st6.data 192).toNat ∨ (stackBelow st6.data 192).toNat + 192 ≤ _
      rw [hsb, hsbN]
      have := gr.rs
      omega
    · rw [hX0]
      exact hm6.kept hwf _ (hfu.frame.kept _ (hpre.2.2.2.1 i (by omega)))
    · show st6.data.regs.X0.toBitVec.toNat + 200 ≤ _
      rw [hX0]
      have := g.h
      omega
    · show st6.data.regs.X0.toBitVec.toNat + 200 ≤ (stackBelow st6.data 192).toNat ∨
        (stackBelow st6.data 192).toNat + 192 ≤ st6.data.regs.X0.toBitVec.toNat
      rw [hX0, hsb, hsbN]
      have := g.hs
      omega
    · show st6.data.regs.X0.toBitVec.toNat + 200 ≤ rcAddr.toNat ∨
        rcAddr.toNat + 192 ≤ st6.data.regs.X0.toBitVec.toNat
      rw [hX0]
      have := gr.hr
      omega
  obtain ⟨hbytesK, hsameK, hsavedK⟩ := hpost
  have hX0' : st6.data.regs.X0.toBitVec = _ := hX0
  rw [hX0', hxor] at hbytesK
  rw [hX0', show keccakFStack = 192 from rfl, hsb] at hsameK
  have hout : ∀ p, ¬Chg m0 p → ¬(InRange (hAt m0) 200 p ∨ InRange (spAt m0 - 256#64) 192 p) :=
    fun p hp hr => hp (by
      rcases hr with hr | hr
      · rw [inRange_iff (by have := g.h; omega)] at hr
        left
        rw [inRange_iff g.h]
        omega
      · exact Or.inr hr)
  have hreg : ∀ r, calleeSaved r = true → st'.data.regs.getXReg r = st6.data.regs.getXReg r :=
    hsavedK.1
  have hfr : Frame m0 m1 st'.data := by
    refine hfu.frame.update (fun r hr => ?_)
      (hsavedK.2.1.trans (UInt64.toBitVec_inj.mp (hm6.sp.trans hm.sp.symm)))
      (fun p hp => by
        rw [hsameK p (hout p hp)]
        exact hnw6 p (by rw [chg_iff g] at hp; omega))
      (fun p hp => hsavedK.2.2 p (hm6.kept hwf p hp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hreg _ rfl).trans (Match.reg_eq hm hm6 rfl rfl)
  refine Eventually.done _ ⟨by rw [hpc']; rfl, hfr, hfu.le, ?_, ?_, ?_, hfu.holds, hfu.lt, hfu.len,
    hfu.full, ?_⟩
  · rw [hreg .X19 rfl, Match.reg_atom hm6 rfl]
    exact hfu.x19
  · rw [hreg .X21 rfl, Match.reg_atom hm6 rfl]
    exact hfu.x21
  · rw [hreg .X22 rfl, Match.reg_atom hm6 rfl]
    exact hfu.x22
  · rw [hc2]
    have hA : (absorb (H2.take 200) ((H2.drop 200).take 136)).length = 200 := by
      rw [absorb, keccakF, length_stateBytes]
    refine ext_getD (by rw [hasher, length_bytesOf, length_writeAt (by omega), hlen2])
      fun j hj => ?_
    rw [hasher, length_bytesOf] at hj
    rw [hasher, getD_bytesOf _ _ hj, getD_writeAt _ _ _ _ (by omega), hA]
    by_cases h : j < 200
    · rw [ite_pos' ⟨Nat.zero_le _, h⟩, hbytesK j (by rw [keccakF, length_stateBytes]; exact h),
        Nat.sub_zero, absorb]
      simp [List.getD_eq_getElem?_getD, show j < (keccakF (NativeRustc.Keccak.xorBlock
        (H2.take 200) ((H2.drop 200).take 136))).length by rw [keccakF, length_stateBytes]; exact h]
    · rw [ite_neg' (by omega), hsameK _ (fun hr => ?_)]
      · have := hmem6 j hj
        rw [ite_neg' (by omega)] at this
        exact this
      rcases hr with hr | hr
      · rw [inRange_self_iff (by have := g.h; omega) (by have := g.h; omega) (by omega)] at hr
        omega
      · rw [inRange_iff (by rw [hsbN]; have := (spAt m0).isLt; omega), hsbN,
          toNat_add_ofNat' (by have := g.h; omega)] at hr
        have := g.hs
        omega

end

end NativeRustcArm.Hasher.Update
