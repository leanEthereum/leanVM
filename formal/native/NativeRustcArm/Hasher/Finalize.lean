module

public import NativeRustcArm.Code.Common.Finalize.Names
public import NativeRustcArm.Code.Common.KeccakF.Names
public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.Hasher.FinalizeC

/-!
# `Hasher::finalize` on AArch64

**`finalize_spec`**: rustc's `Hasher::finalize`, placed anywhere in the program, meets its
contract (`FinalizePre`, `FinalizePost`) given the contracts of `memcpy` and `keccak_f`: the copies
to the frame (`stage2_spec`), the padding (`stage3_spec`), the permutation (`stage4_spec`), then
`b5` copies the state's first 32 bytes to the output (`Keccak.finalize`) and restores the
callee-saved registers.
-/

namespace NativeRustcArm.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Finalize NativeRustcArm

public section

variable [Host] {k : Nat}

set_option linter.unusedSimpArgs false in
/-- **`Hasher::finalize` meets its contract.** -/
theorem finalize_spec (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hkf : Spec (Labels.label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    Spec (Labels.label NativeRustcArm.Common.Finalize.entryLabel) FinalizePre
      FinalizePost := by
  intro m0 hpre
  have g := geo_of hpre
  have hf := frAt_toNat g
  have hs := g.s
  have hFnw : (frAt m0).toNat + 384 ≤ 2 ^ 64 := by rw [hf]; have := (spAt m0).isLt; omega
  rw [lbl_entry hp]
  refine NativeRustcArm.Eventually.bind (stage2_spec hp hmemcpy hpre) fun st ⟨hpc, m1, hpro, hs2⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  refine NativeRustcArm.Eventually.bind (stage3_spec hp hpre hs2) fun st ⟨hpc, hs3⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  refine NativeRustcArm.Eventually.bind (stage4_spec hp hkf hpre hpro hs3) fun st ⟨hpc, hs4⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  -- The epilogue.
  have hfr := hs4.fr
  have hmapF : Mapped d.dmem (frAt m0) 384 := fun i hi => hfr.kept _ (by
    have := hpre.1.2.2 (192 + i) (by show 192 + i < 576; omega)
    rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 finalizeStack + BitVec.ofNat 64 (192 + i) =
      frAt m0 + BitVec.ofNat 64 i from stack_frame] at this)
  have hmapO : Mapped d.dmem (oAt m0) 32 := fun i hi => hfr.kept _ (hpre.2.2.2.2.2.1 i hi)
  have hwf : (Env.ofMachine d [(frAt m0, 384), (oAt m0, 32)]).WF :=
    Env.wf_of ⟨⟨hmapF, hFnw⟩, ⟨hmapO, g.o⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        show (frAt m0).toNat + 384 ≤ (oAt m0).toNat ∨ (oAt m0).toNat + 32 ≤ (frAt m0).toNat
        rw [hf]; have := g.os; omega))
  have hbF : (Env.ofMachine d [(frAt m0, 384), (oAt m0, 32)]).base 0 = frAt m0 :=
    Env.base_ofMachine d _ _ rfl
  have hbO : (Env.ofMachine d [(frAt m0, 384), (oAt m0, 32)]).base 1 = oAt m0 :=
    Env.base_ofMachine d _ _ rfl
  have hm : Match (Env.ofMachine d [(frAt m0, 384), (oAt m0, 32)]) outS d :=
    match_ofMachine ⟨rfl, fun _ => by rw [hf]; have := g.al; omega, rfl, by simp, trivial⟩
      (by rw [hfr.sp]; simp only [Sym.eval, hbF]; simp)
      ⟨by
        show (d.regs.getXReg .X19).toBitVec = _
        rw [hfr.x19]; simp only [Sym.eval, hbO]; simp, trivial⟩ trivial trivial trivial
  -- The slots hold the registers at the entry.
  have hslotM : ∀ i < 384, 336 ≤ i → d.dmem.get? (frAt m0 + BitVec.ofNat 64 i) =
      m1.dmem.get? (frAt m0 + BitVec.ofNat 64 i) := fun i hi h336 =>
    hfr.same _ (by
      rw [chgF_iff g, toNat_add_ofNat' (by omega), hf]
      omega)
  have hslot : ∀ p ∈ slots, (Env.ofMachine d [(frAt m0, 384), (oAt m0, 32)]).load 0 p.1 8 =
      (m0.regs.getXReg p.2).toBitVec := by
    intro p hpm
    have hle : 336 ≤ p.1 ∧ p.1 + 8 ≤ 384 := by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hpm
      rcases hpm with h | h | h | h | h | h <;> rw [h] <;> decide
    rw [Env.load_of_bytesAt (bs := (List.range 8).map (byteOf (m0.regs.getXReg p.2).toBitVec))
      (by simp) ?_, ofInt_ofBytes_byteOf]
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    rw [hbF, add_ofNat_add, Env.ofMachine_mem0, hslotM _ (by omega) (by omega), ← add_ofNat_add,
      hpro.slots p hpm i (by simp [hi])]
  refine exec_then (hb5 hp) run_b5 hwf hm fun st hm' hpc' => ?_
  have hl := b5_mem
  rw [after_eq run_b5] at hl
  have hlo := b5_out
  rw [after_eq run_b5] at hlo
  have hreg : ∀ p ∈ slots, st.data.regs.getXReg p.2 = m0.regs.getXReg p.2 := by
    intro p hpm
    apply UInt64.toBitVec_inj.mp
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hm'.regs .X19 _ rfl]; exact hslot (376, .X19) (by simp [slots])
    · rw [hm'.regs .X20 _ rfl]; exact hslot (368, .X20) (by simp [slots])
    · rw [hm'.regs .X21 _ rfl]; exact hslot (360, .X21) (by simp [slots])
    · rw [hm'.regs .X28 _ rfl]; exact hslot (352, .X28) (by simp [slots])
    · rw [hm'.regs .X30 _ rfl]; exact hslot (344, .X30) (by simp [slots])
    · rw [hm'.regs .X29 _ rfl]; exact hslot (336, .X29) (by simp [slots])
  have hmem' : ∀ p, ¬((oAt m0).toNat ≤ p.toNat ∧ p.toNat < (oAt m0).toNat + 32) →
      st.data.dmem.get? p = d.dmem.get? p := fun p hp =>
    hm'.get?_mem0 hwf fun hw => hp (written_in (r := 1) rfl hl hw)
  have hX30 : retOf st.data = retOf m0 := by
    unfold retOf
    rw [show st.data.regs.X30 = m0.regs.X30 from hreg (344, .X30) (by simp [slots])]
  have hs256 : (stackBelow m0 finalizeStack).toNat = (spAt m0).toNat - 576 :=
    toNat_sub_ofNat' (by show 576 ≤ (spAt m0).toNat; omega)
  refine Eventually.done _ ⟨by simpa [PcOk, hX30] using hpc', ?_, ?_, ?_⟩
  · -- The digest.
    intro j hj
    have hlen : (finalize (bytesOf m0.dmem m0.regs.X1.toBitVec 344)).length = 32 := by
      rw [finalize, digestOf, List.length_take, absorb, keccakF, length_stateBytes]
      rfl
    rw [hlen] at hj
    show st.data.dmem.get? (oAt m0 + BitVec.ofNat 64 j) = _
    rw [hm'.mem 1 (oAt m0) 32 rfl j hj]
    unfold memByte
    rw [hlo j hj]
    simp only [Sym.eval]
    rw [byteOf_load (by omega) (by omega), hbF, Env.ofMachine_mem0,
      show 8 * (j / 8) + j % 8 = j by omega]
    have hst := hs4.state
    have hj200 : j < 200 := by omega
    have hget := congrArg (·.getD j 0) hst
    simp only at hget
    rw [getD_bytesOf _ _ hj200] at hget
    rw [hget, getElem_eq_getD]
    have e : finalize (bytesOf m0.dmem m0.regs.X1.toBitVec 344) =
        (absorb ((hbytes m0).take 200) (finalBlock (tailOf m0))).take 32 := by
      simp only [finalize, digestOf, tailOf, lenOf, hbytes, hAt]
    rw [e, Native.Keccak.Proof.getD_take, ite_pos' hj]
  · -- Memory outside the output and the stack.
    intro p hp
    change ¬(InRange (oAt m0) 32 p ∨ InRange (stackBelow m0 finalizeStack) 576 p) at hp
    rw [inRange_iff g.o, inRange_iff (by rw [hs256]; have := (spAt m0).isLt; omega), hs256] at hp
    rw [hmem' p (by omega), hfr.same p (by rw [chgF_iff g]; omega),
      hpro.same p (by rw [frame_iff g]; omega)]
  · -- The registers kept.
    refine ⟨fun r hr => ?_, ?_, fun p hp => ?_⟩
    · cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr
      · exact hreg (376, .X19) (by simp [slots])
      · exact hreg (368, .X20) (by simp [slots])
      · exact hreg (360, .X21) (by simp [slots])
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X22 (by simp))
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X23 (by simp))
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X24 (by simp))
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X25 (by simp))
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X26 (by simp))
      · exact (Match.reg_atom hm' rfl).trans (hfr.saved .X27 (by simp))
      · exact hreg (352, .X28) (by simp [slots])
      · exact hreg (336, .X29) (by simp [slots])
    · apply UInt64.toBitVec_inj.mp
      rw [hm'.sp]
      simp only [Sym.eval, hbF]
      exact BitVec.sub_add_cancel _ _
    · by_cases hpo : (oAt m0).toNat ≤ p.toNat ∧ p.toNat < (oAt m0).toNat + 32
      · exact hm'.kept hwf p (hfr.kept p hp)
      · rw [hmem' p hpo]
        exact hfr.kept p hp

end

end NativeRustcArm.Hasher.Finalize
