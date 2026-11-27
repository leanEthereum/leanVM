module

public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.Hasher.FinalizeInv

/-!
# `Hasher::finalize`: the state and the buffer copied to the frame

From the entry, the prologue (`b0`) saves the callee-saved registers at the frame's bytes 336 to
383 (`Pro`) and copies the state's 200 bytes to the frame's start (`memcpy`); `b1`, `b2` check
`buf_len < 136` (the branches to the panics fail); `b3` zeroes the frame's bytes 200 to 335 and
copies the `buf_len` buffered bytes over their start (`memcpy`): `Stage2`, `stage2_spec`.
-/

namespace NativeRustcArm.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Finalize NativeRustcArm

@[expose] public section

/-- `buf_len` at the entry. -/
def lenOf (m0 : MachineData) : Nat := bufLen (hbytes m0)

/-- The buffered bytes at the entry. -/
def tailOf (m0 : MachineData) : List UInt8 := ((hbytes m0).drop 200).take (lenOf m0)

/-- What the prologue leaves: memory as at the entry but in the frame, the callee-saved registers
in their slots. -/
structure Pro (m0 m1 : MachineData) : Prop where
  same : SameOutside m0.dmem m1.dmem (InRange (frAt m0) 384)
  slots : ∀ p ∈ slots, BytesAt m1.dmem (frAt m0 + BitVec.ofNat 64 p.1)
    ((List.range 8).map (byteOf (m0.regs.getXReg p.2).toBitVec))

/-- After the second `memcpy`: the state, then the buffered bytes and zeros, in the frame. -/
structure Stage2 (m0 m1 m : MachineData) : Prop where
  fr : Fr m0 m1 m
  x20 : (m.regs.getXReg .X20).toBitVec.toNat = lenOf m0
  x21 : (m.regs.getXReg .X21).toBitVec = frAt m0 + 200#64
  bytes : bytesOf m.dmem (frAt m0) 336 =
    (hbytes m0).take 200 ++ (tailOf m0 ++ List.replicate (136 - lenOf m0) 0)

end

public section

theorem lenOf_lt [Labels] {m0 : MachineData} (hpre : FinalizePre m0) : lenOf m0 < 136 := by
  obtain ⟨a, ha⟩ := hpre.2.2.1
  rw [lenOf, hbytes, hAt, bufLen_of_holds ha]
  exact Nat.mod_lt _ (by omega)

theorem length_hbytes (m0 : MachineData) : (hbytes m0).length = 344 := length_bytesOf ..

theorem length_tailOf {m0 : MachineData} (h : lenOf m0 < 136) : (tailOf m0).length = lenOf m0 := by
  simp [tailOf, length_hbytes]
  omega

theorem getD_stage2 (A T : List UInt8) (hA : A.length = 200) {L : Nat} (hT : T.length = L)
    {j : Nat} :
    (A ++ (T ++ List.replicate (136 - L) 0)).getD j 0 =
      if j < 200 then A.getD j 0 else if j < 200 + L then T.getD (j - 200) 0 else 0 := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : j < 200
  · rw [List.getElem?_append_left (by omega), ite_pos' h1]
  · rw [List.getElem?_append_right (by omega), hA, ite_neg' h1]
    by_cases h2 : j < 200 + L
    · rw [List.getElem?_append_left (by omega), ite_pos' h2]
    · rw [List.getElem?_append_right (by omega), hT, List.getElem?_replicate, ite_neg' h2]
      split <;> rfl

theorem stack_frame {s : BitVec 64} {i : Nat} :
    s - BitVec.ofNat 64 576 + BitVec.ofNat 64 (192 + i) = s - 384#64 + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.isLt
  omega

variable [ElfHost] {sec k : Nat}

set_option linter.unusedSimpArgs false in
/-- **The prologue and the copies to the frame.** -/
theorem stage2_spec (hp : PlacedIn code sec k)
    (hmemcpy : ElfSpec (Labels.label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m0 : MachineData}
    (hpre : FinalizePre m0) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Finalize.b4Offset) ∧ ∃ m1, Pro m0 m1 ∧ Stage2 m0 m1 st.data)
      ⟨m0, ElfHost.addrOf sec (k + NativeRustcArm.Common.Finalize.b0Offset)⟩ := by
  have g := geo_of hpre
  have hs := g.s
  have hf := frAt_toNat g
  have hL := lenOf_lt hpre
  have hmapH : Mapped m0.dmem (hAt m0) 344 := hpre.2.2.2.1
  have hmapF : Mapped m0.dmem (frAt m0) 384 := fun i hi => by
    have := hpre.1.2.2 (192 + i) (by show 192 + i < 576; omega)
    rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 finalizeStack + BitVec.ofNat 64 (192 + i) =
      frAt m0 + BitVec.ofNat 64 i from stack_frame] at this
  have hFnw : (frAt m0).toNat + 384 ≤ 2 ^ 64 := by rw [hf]; have := (spAt m0).isLt; omega
  -- The prologue.
  have hwf0 : (Env.ofMachine m0 [(frAt m0, 384)]).WF :=
    Env.wf_of ⟨⟨hmapF, hFnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hbF0 : (Env.ofMachine m0 [(frAt m0, 384)]).base 0 = frAt m0 := Env.base_ofMachine m0 _ _ rfl
  have hm0 : Match (Env.ofMachine m0 [(frAt m0, 384)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ => by rw [hf]; have := g.al; omega, trivial⟩
      (by
        simp only [Sym.eval, hbF0]
        show spAt m0 = spAt m0 - 384#64 + 384#64
        exact (BitVec.sub_add_cancel _ _).symm)
      trivial trivial trivial trivial
  refine exec_then_elf (hb0 hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  have hl0 := b0_mem
  rw [after_eq run_b0] at hl0
  have hsl0 := b0_slots
  rw [after_eq run_b0] at hsl0
  have h01 : SameOutside m0.dmem st1.data.dmem (InRange (frAt m0) 384) := fun p hp =>
    hm1.get?_mem0 hwf0 fun hw => hp ((inRange_iff hFnw).mpr
      (written_hasher (fun w hw => ⟨(hl0 w hw).1, (hl0 w hw).2.2⟩) hw))
  have hpro : Pro m0 st1.data := ⟨h01, fun p hpm => hm1.bytesAt_write (r := 0) (o := p.1) (n := 8)
    (sz := 384) rfl (by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hpm
      rcases hpm with h | h | h | h | h | h <;> rw [h] <;> decide) (hsl0 p hpm)⟩
  have hk1 := hm1.kept hwf0
  have hH1 : ∀ i < 344, st1.data.dmem.get? (hAt m0 + BitVec.ofNat 64 i) =
      m0.dmem.get? (hAt m0 + BitVec.ofNat 64 i) := fun i hi => h01 _ (by
    rw [frame_iff g, toNat_add_ofNat' (by have := g.h; omega)]; have := g.hs; omega)
  have hX0 : st1.data.regs.X0.toBitVec = frAt m0 := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ rfl]; simp only [Sym.eval, hbF0]; simp
  have hX1 : st1.data.regs.X1.toBitVec = hAt m0 := hm1.regs .X1 _ rfl
  have hX2 : st1.data.regs.X2.toNat = 200 := by
    show (st1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl]; rfl
  have hfr1 : Fr m0 st1.data st1.data := by
    refine ⟨?_, ?_, ?_, fun r hr => ?_, fun _ _ => rfl, hk1⟩
    · rw [hm1.sp]; simp only [Sym.eval, hbF0]; simp
    · rw [hm1.regs .X19 _ rfl]; rfl
    · rw [hm1.regs .X29 _ rfl]; simp only [Sym.eval, hbF0]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_atom hm1 rfl
  -- The first `memcpy`: the state.
  refine call_then_elf hpc1 hmemcpy ?pre1 fun st2 hpc2 hpost2 => ?_
  case pre1 =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
    · rw [hX0]; rw [hX2] at hi; exact hk1 _ (hmapF i (by omega))
    · rw [hX1]; rw [hX2] at hi; exact hk1 _ (hmapH i (by omega))
    · show st1.data.regs.X0.toBitVec.toNat + st1.data.regs.X2.toNat ≤ _
      rw [hX0, hX2]; omega
    · show st1.data.regs.X1.toBitVec.toNat + st1.data.regs.X2.toNat ≤ _
      rw [hX1, hX2]; have := g.h; omega
    · show st1.data.regs.X0.toBitVec.toNat + st1.data.regs.X2.toNat ≤ st1.data.regs.X1.toBitVec.toNat ∨
        st1.data.regs.X1.toBitVec.toNat + st1.data.regs.X2.toNat ≤ st1.data.regs.X0.toBitVec.toNat
      rw [hX0, hX1, hX2, hf]; have := g.hs; omega
  obtain ⟨-, hbytes2, hsame2, hsaved2⟩ := hpost2
  rw [hX0, hX1, hX2] at hbytes2
  rw [hX0, hX2] at hsame2
  have hsrc1 : bytesOf st1.data.dmem (hAt m0) 200 = (hbytes m0).take 200 := by
    rw [bytesOf_take _ _ (show 200 ≤ 344 by omega), hbytes]
    exact congrArg _ (bytesOf_congr hH1)
  rw [hsrc1] at hbytes2
  have hfr2 : Fr m0 st1.data st2.data := hfr1.update
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hsaved2.1 _ rfl)
    hsaved2.2.1 (fun p hp => hsame2 p fun hr => hp (Or.inl (by
      rw [inRange_iff (by omega)] at hr
      rw [inRange_iff (by omega)]
      omega))) hsaved2.2.2
  have hH2 : ∀ i < 344, st2.data.dmem.get? (hAt m0 + BitVec.ofNat 64 i) =
      m0.dmem.get? (hAt m0 + BitVec.ofNat 64 i) := fun i hi => hasher_same g hfr2 h01 hi
  have hX21 : (st2.data.regs.getXReg .X21).toBitVec = hAt m0 := by
    rw [hsaved2.1 .X21 rfl, hm1.regs .X21 _ rfl]; rfl
  -- `b1`, `b2`, `b3`.
  obtain ⟨d2, pc2⟩ := st2
  have hpc2' : pc2 = ElfHost.addrOf sec (k + NativeRustcArm.Common.Finalize.b1Offset) := by rw [show pc2 = _ from hpc2]; rfl
  subst hpc2'
  have hwf2 : (Env.ofMachine d2 [(frAt m0, 384), (hAt m0, 344)]).WF :=
    Env.wf_of ⟨⟨fun i hi => hfr2.kept _ (hmapF i hi), hFnw⟩,
      ⟨fun i hi => hfr2.kept _ (hmapH i hi), g.h⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        show (frAt m0).toNat + 384 ≤ (hAt m0).toNat ∨ (hAt m0).toNat + 344 ≤ (frAt m0).toNat
        rw [hf]; have := g.hs; omega))
  have hbF : (Env.ofMachine d2 [(frAt m0, 384), (hAt m0, 344)]).base 0 = frAt m0 :=
    Env.base_ofMachine d2 _ _ rfl
  have hbH : (Env.ofMachine d2 [(frAt m0, 384), (hAt m0, 344)]).base 1 = hAt m0 :=
    Env.base_ofMachine d2 _ _ rfl
  have hm2 : Match (Env.ofMachine d2 [(frAt m0, 384), (hAt m0, 344)]) copyS d2 :=
    match_ofMachine ⟨rfl, fun _ => by rw [hf]; have := g.al; omega, rfl, by simp, trivial⟩
      (by rw [hfr2.sp]; simp only [Sym.eval, hbF]; simp)
      ⟨by
          show (d2.regs.getXReg .X21).toBitVec = _
          rw [show (d2.regs.getXReg .X21).toBitVec = hAt m0 from hX21]
          simp only [Sym.eval, hbH]; simp,
        by
          show (d2.regs.getXReg .X29).toBitVec = _
          rw [show (d2.regs.getXReg .X29).toBitVec = _ from hfr2.x29]
          simp only [Sym.eval, hbF]; rfl, trivial⟩ trivial trivial trivial
  have hload : (Env.ofMachine d2 [(frAt m0, 384), (hAt m0, 344)]).load 1 336 8 =
      BitVec.ofInt 64 (Int.ofBytes ((hbytes m0).drop 336)) := by
    rw [load_eq_bytesOf _ hbH (N := 344) (by omega) (fun i hi => hfr2.kept _ (hmapH i hi)),
      List.take_of_length_le (by simp [length_bytesOf])]
    congr 3
    exact bytesOf_congr hH2
  have hLv : (BitVec.ofInt 64 (Int.ofBytes ((hbytes m0).drop 336))).toNat = lenOf m0 :=
    bufLen_ofBytes (length_hbytes m0)
  refine exec_then_elf (hb1 hp) run_b1 hwf2 hm2 fun st3 hm3 hpc3 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hload,
    Nat.add_assoc, NativeRustcArm.Common.Finalize.b1_next] at hpc3
  rw [ite_neg' (by simp [BitVec.ult, hLv]; omega)] at hpc3
  refine exec_at_elf (hb2 hp) (exec_after run_b1 run_b2) hwf2 hpc3 hm3 fun st4 hm4 hpc4 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hload,
    Nat.add_assoc, NativeRustcArm.Common.Finalize.b2_next] at hpc4
  rw [ite_neg' (by
    simp only [beq_iff_eq]
    intro h
    have := congrArg BitVec.toNat h
    rw [hLv] at this
    simp at this
    omega)] at hpc4
  have hr3 := run_b3
  rw [after_eq run_b1] at hr3
  refine exec_at_elf (hb3 hp) (exec_after (exec_after run_b1 run_b2) hr3) hwf2 hpc4 hm4
    fun st5 hm5 hpc5 => ?_
  have hl3 := b3_mem
  rw [after_eq run_b1, after_eq (exec_after run_b1 run_b2),
    after_eq (exec_after (exec_after run_b1 run_b2) hr3)] at hl3
  have hfr5 : Fr m0 st1.data st5.data := hfr2.update
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm2 hm5 rfl rfl)
    (Match.sp_eq hm2 hm5 rfl)
    (fun p hp => hm5.get?_mem0 hwf2 fun hw => by
      obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hw
      have hw3 := b3_mem1
      rw [after_eq run_b1, after_eq (exec_after run_b1 run_b2),
        after_eq (exec_after (exec_after run_b1 run_b2) hr3)] at hw3
      obtain ⟨hr0, hoff1, hoff2⟩ := hw3 w hw
      rw [hr0] at hb
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact hp (Or.inl ((inRange_iff (by omega)).mpr ⟨by omega, by omega⟩)))
    (hm5.kept hwf2)
  -- The second `memcpy`: the buffered bytes.
  have hL5 : (BitVec.ofInt 64 (Int.ofBytes ((hbytes m0).drop 336))).toNat < 136 := by
    rw [hLv]; exact hL
  have hX0' : st5.data.regs.X0.toBitVec = frAt m0 + BitVec.ofNat 64 200 := by
    show (st5.data.regs.getXReg .X0).toBitVec = _
    rw [hm5.regs .X0 _ rfl]; simp only [Sym.eval, hbF]; rfl
  have hX1' : st5.data.regs.X1.toBitVec = hAt m0 + BitVec.ofNat 64 200 := by
    show (st5.data.regs.getXReg .X1).toBitVec = _
    rw [hm5.regs .X1 _ rfl]; simp only [Sym.eval, hbH]; rfl
  have hX2' : st5.data.regs.X2.toNat = lenOf m0 := by
    show (st5.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm5.regs .X2 _ rfl]; simp only [Sym.eval, hload]; exact hLv
  have hto200 : ∀ (a : BitVec 64) (j : Nat), a.toNat + 200 + j < 2 ^ 64 →
      (a + BitVec.ofNat 64 200).toNat = a.toNat + 200 := fun a j h =>
    toNat_add_ofNat' (by omega)
  refine call_then_elf hpc5 hmemcpy ?pre2 fun st6 hpc6 hpost6 => ?_
  case pre2 =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
    · rw [hX0', add_ofNat_add]; rw [hX2'] at hi; exact hfr5.kept _ (hmapF _ (by omega))
    · rw [hX1', add_ofNat_add]; rw [hX2'] at hi; exact hfr5.kept _ (hmapH _ (by omega))
    · show st5.data.regs.X0.toBitVec.toNat + st5.data.regs.X2.toNat ≤ _
      rw [hX0', hX2', hto200 _ 0 (by omega)]; omega
    · show st5.data.regs.X1.toBitVec.toNat + st5.data.regs.X2.toNat ≤ _
      rw [hX1', hX2', hto200 _ 0 (by have := g.h; omega)]; have := g.h; omega
    · show st5.data.regs.X0.toBitVec.toNat + st5.data.regs.X2.toNat ≤ st5.data.regs.X1.toBitVec.toNat ∨
        st5.data.regs.X1.toBitVec.toNat + st5.data.regs.X2.toNat ≤ st5.data.regs.X0.toBitVec.toNat
      rw [hX0', hX1', hX2', hto200 _ 0 (by omega), hto200 _ 0 (by have := g.h; omega), hf]
      have := g.hs; omega
  obtain ⟨-, hbytes6, hsame6, hsaved6⟩ := hpost6
  rw [hX0', hX1', hX2'] at hbytes6
  rw [hX0', hX2'] at hsame6
  have hfr6 : Fr m0 st1.data st6.data := hfr5.update
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hsaved6.1 _ rfl)
    hsaved6.2.1 (fun p hp => hsame6 p fun hr => hp (Or.inl (by
      rcases Nat.eq_zero_or_pos (lenOf m0) with h0 | h0
      · rw [h0] at hr; exact absurd hr (Nat.not_lt_zero _)
      rw [inRange_iff (by rw [hto200 _ 0 (by omega)]; omega), hto200 _ 0 (by omega)] at hr
      rw [inRange_iff (by omega)]
      omega))) hsaved6.2.2
  refine Eventually.done _ ⟨by rw [hpc6]; rfl, st1.data, hpro, hfr6, ?_, ?_, ?_⟩
  · rw [hsaved6.1 .X20 rfl, hm5.regs .X20 _ rfl]
    simp only [Sym.eval, hload]
    exact hLv
  · rw [hsaved6.1 .X21 rfl, hm5.regs .X21 _ rfl]
    simp only [Sym.eval, hbF]
    rfl
  · have hTl := length_tailOf hL
    refine ext_getD (by simp [length_bytesOf, hTl, length_hbytes]; omega) fun j hj => ?_
    rw [length_bytesOf] at hj
    rw [getD_stage2 _ _ (by simp [length_hbytes]) hTl, getD_bytesOf _ _ hj]
    have hj' : (frAt m0 + BitVec.ofNat 64 j) =
        frAt m0 + BitVec.ofNat 64 200 + BitVec.ofNat 64 (j - 200) ∨ j < 200 := by
      by_cases h : j < 200
      · exact Or.inr h
      · left; rw [add_ofNat_add, show 200 + (j - 200) = j by omega]
    by_cases h2 : 200 ≤ j ∧ j < 200 + lenOf m0
    · rw [ite_neg' (by omega), ite_pos' h2.2]
      rcases hj' with hj' | hj'
      · rw [hj', hbytes6 (j - 200) (by rw [length_bytesOf]; omega)]
        rw [Option.getD_some, getElem_eq_getD, getD_bytesOf _ _ (show j - 200 < lenOf m0 by omega),
          add_ofNat_add, tailOf, Native.Keccak.Proof.getD_take, ite_pos' (by omega),
          Native.Keccak.Proof.getD_drop, hbytes, getD_bytesOf _ _ (by omega),
          show 200 + (j - 200) = j by omega]
        exact congrArg (·.getD 0) (hasher_same g hfr5 h01 (i := j) (by omega))
      · omega
    · rw [hsame6 _ fun hr => h2 (by
        rcases Nat.eq_zero_or_pos (lenOf m0) with h0 | h0
        · rw [h0] at hr; exact absurd hr (Nat.not_lt_zero _)
        rw [inRange_add_iff (by omega) (by omega) h0] at hr
        exact hr)]
      rw [hm5.mem 0 (frAt m0) 384 rfl j (by omega)]
      unfold memByte
      rw [hl3 j (by omega)]
      by_cases h3 : 200 ≤ j ∧ j < 336
      · rw [ite_pos' h3, ite_neg' (by omega), ite_neg' (by omega)]
        simp [Sym.eval, byteOf]
      · rw [ite_neg' h3, ite_pos' (by omega)]
        simp only [Env.ofMachine_mem0]
        have hb2 := hbytes2 j (by simp [length_hbytes]; omega)
        rw [hb2, Option.getD_some, getElem_eq_getD]

end

end NativeRustcArm.Hasher.Finalize
