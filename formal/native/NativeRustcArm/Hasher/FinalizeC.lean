module

public import NativeRustcArm.Code.Common.KeccakF.Names

public import NativeRustcArm.Hasher.FinalizeB

/-!
# `Hasher::finalize`: the final block absorbed

From `Stage3`, `b4b` XORs `PAD_LAST` into the block's last byte and the block's 17 lanes into the
state's (`b4b_byte`: the state is `xorBlock` of the hasher's state and the final block) and calls
`keccak_f` on the state (`stage4_spec`).
-/

namespace NativeRustcArm.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Finalize NativeRustcArm

public section

/-- The writes `[padW]` give byte `j` of the frame. -/
theorem findWrite_padW (j : Nat) : findWrite 0 j [padW] =
    if j = 335 then some (padW.v, 0) else none := by
  by_cases h : j = 335
  · subst h; rfl
  · simp only [findWrite, padW, h, ↓reduceIte]
    rw [ite_neg' (by omega)]

section
variable [Labels]

/-- **A byte of the state after `b4b`**, from the frame's bytes before it. -/
theorem b4b_byte {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) (hwf : env.WF)
    {fr : BitVec 64} (hr : env.regions[0]? = some (fr, 384)) (hS : S.mem = finMem) {j : Nat}
    (hj : j < 200) :
    (m.dmem.get? (fr + BitVec.ofNat 64 j)).getD 0 =
      if j < 136 then (env.mem0.get? (fr + BitVec.ofNat 64 j)).getD 0 ^^^
        ((env.mem0.get? (fr + BitVec.ofNat 64 (200 + j))).getD 0 ^^^ (if j = 135 then 0x80 else 0))
      else (env.mem0.get? (fr + BitVec.ofNat 64 j)).getD 0 := by
  have hb : env.base 0 = fr := Env.base_eq hr
  rw [hm.mem 0 fr 384 hr j (by omega), hS]
  unfold memByte
  rw [findWrite_finMem j (by omega)]
  by_cases h1 : j < 128
  · rw [ite_pos' h1, ite_pos' (by omega)]
    simp only [Option.getD_some, laneW, Sym.eval]
    rw [byteOf_eorW64, byteOf_load (by omega) (by omega), byteOf_load (by omega) (by omega), hb,
      show 8 * (j / 8) + j % 8 = j by omega, show 200 + 8 * (j / 8) + j % 8 = 200 + j by omega,
      ite_neg' (by omega), UInt8.xor_zero]
  · rw [ite_neg' h1]
    by_cases h2 : j < 136
    · rw [ite_pos' h2, ite_pos' h2]
      simp only [Option.getD_some, lane16, Sym.eval]
      rw [byteOf_eorW64, byteOf_load (by omega) (by omega), hb, eval_assemble hb,
        byteOf_ofNat_ofBytes _ (by simp), show 128 + (j - 128) = j by omega]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range
        (show j - 128 < 8 by omega), Option.map_some, Option.getD_some]
      have hmb := memByte_eq (ws := [padW]) hwf hr (j := 328 + (j - 128)) (by omega)
      unfold memByte at hmb
      rw [findWrite_padW] at hmb
      by_cases h3 : j = 135
      · subst h3
        rw [ite_pos' rfl] at hmb
        simp only [Option.some.injEq] at hmb
        rw [← hmb, ite_pos' rfl]
        simp only [padW, Sym.eval]
        rw [byteOf_eorW32, byteOf_load (by omega) (by omega), hb, byteOf_ofNat_lt 128 (by omega)]
        rfl
      · rw [ite_neg' (by omega)] at hmb
        rw [ite_neg' h3, UInt8.xor_zero, show 328 + (j - 128) = 200 + j by omega] at *
        have : (env.mem0.get? (fr + BitVec.ofNat 64 (200 + j))).isSome := by
          have := hwf.mapped 0 fr 384 hr (200 + j) (by omega)
          exact this
        revert hmb this
        cases env.mem0.get? (fr + BitVec.ofNat 64 (200 + j)) <;> simp
        exact fun h => h.symm
    · rw [ite_neg' h2, ite_neg' h2, ite_neg' (by omega)]

end

variable [ElfHost] {sec k : Nat}

set_option linter.unusedSimpArgs false in
/-- **The final block absorbed.** -/
theorem stage4_spec (hp : PlacedIn code sec k)
    (hkf : ElfSpec (Labels.label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    {m0 m1 m : MachineData} (hpre : FinalizePre m0) (hpro : Pro m0 m1) (hs3 : Stage3 m0 m1 m) :
    Eventually (elfStep1 ElfHost.exe) (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Finalize.b5Offset) ∧ Stage4 m0 m1 st.data)
      ⟨m, ElfHost.addrOf sec (k + (NativeRustcArm.Common.Finalize.b4Offset + b4a.length))⟩ := by
  have g := geo_of hpre
  have gr := geoRc_of hpre
  have hf := frAt_toNat g
  have hs := g.s
  have hL := lenOf_lt hpre
  have hfr := hs3.fr
  have hFnw : (frAt m0).toNat + 384 ≤ 2 ^ 64 := by rw [hf]; have := (spAt m0).isLt; omega
  have hmapS : Mapped m0.dmem (frAt m0 - 192#64) 576 := fun i hi => by
    have := hpre.1.2.2 i (by show i < 576; exact hi)
    rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 finalizeStack = frAt m0 - 192#64 by
      apply BitVec.eq_of_toNat_eq
      have e : (spAt m0).toNat = m0.regs.SP.toBitVec.toNat := rfl
      have hfs : finalizeStack = 576 := rfl
      rw [hfs, toNat_sub_ofNat' (by omega), toNat_sub_ofNat' (by omega), hf]
      omega] at this
  have hS192 : (frAt m0 - 192#64).toNat = (spAt m0).toNat - 576 := by
    rw [toNat_sub_ofNat' (by omega), hf]; omega
  have hmapF : Mapped m.dmem (frAt m0) 384 := fun i hi => hfr.kept _ (by
    have := hmapS (192 + i) (by omega)
    rwa [show frAt m0 - 192#64 + BitVec.ofNat 64 (192 + i) = frAt m0 + BitVec.ofNat 64 i by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega), hS192, hf]
      omega] at this)
  have hwf : (Env.ofMachine m [(frAt m0, 384)]).WF :=
    Env.wf_of ⟨⟨hmapF, hFnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hbF : (Env.ofMachine m [(frAt m0, 384)]).base 0 = frAt m0 := Env.base_ofMachine m _ _ rfl
  have hmx : Match (Env.ofMachine m [(frAt m0, 384)]) xorS m :=
    match_ofMachine ⟨rfl, fun _ => by rw [hf]; have := g.al; omega, trivial⟩
      (by rw [hfr.sp]; simp only [Sym.eval, hbF]; simp)
      ⟨by
        show (m.regs.getXReg .X29).toBitVec = _
        rw [hfr.x29]; simp only [Sym.eval, hbF]; rfl, trivial⟩ trivial trivial trivial
  refine exec_then_elf (hb4b hp) run_b4b hwf hmx fun st5 hm5 hpc5 => ?_
  have hl := b4b_mem
  rw [after_eq run_b4b] at hl
  have hTl := length_tailOf hL
  -- The state XOR the final block.
  have hxor : bytesOf st5.data.dmem (frAt m0) 200 =
      NativeRustc.Keccak.xorBlock ((hbytes m0).take 200) (finalBlock (tailOf m0)) := by
    refine ext_getD (by simp [length_bytesOf, NativeRustc.Keccak.xorBlock, length_stateBytes])
      fun j hj => ?_
    rw [length_bytesOf] at hj
    rw [getD_bytesOf _ _ hj, b4b_byte hm5 hwf rfl hl hj, getD_xorBlock _ _ hj]
    have hA := hs3.bytes j (by omega)
    unfold frByte at hA
    rw [ite_pos' hj] at hA
    simp only [Env.ofMachine_mem0]
    rw [hA]
    by_cases h1 : j < 136
    · have hB := hs3.bytes (200 + j) (by omega)
      unfold frByte at hB
      rw [ite_neg' (by omega), show 200 + j - 200 = j by omega] at hB
      rw [ite_pos' h1, ite_pos' h1, hB, getD_finalBlock (by omega) h1, hTl]
      split_ifs <;> first | rfl | omega
    · rw [ite_neg' h1, ite_neg' h1]
  -- `keccak_f`.
  have hsp5 : st5.data.regs.SP.toBitVec = frAt m0 := by
    rw [Match.sp_eq hmx hm5 rfl]; exact hfr.sp
  have hspN : st5.data.regs.SP.toNat = (spAt m0).toNat - 384 := by
    show st5.data.regs.SP.toBitVec.toNat = _
    rw [hsp5, hf]
  have hsb : stackBelow st5.data 192 = frAt m0 - 192#64 := by
    rw [stackBelow, hsp5]
  have hX0 : st5.data.regs.X0.toBitVec = frAt m0 := by
    show (st5.data.regs.getXReg .X0).toBitVec = _
    rw [hm5.regs .X0 _ rfl]; simp only [Sym.eval, hbF]; simp
  have hnw5 : ∀ p, ¬((frAt m0).toNat ≤ p.toNat ∧ p.toNat < (frAt m0).toNat + 336) →
      st5.data.dmem.get? p = m.dmem.get? p := fun p hp =>
    hm5.get?_mem0 hwf fun hw => hp (by
      obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hw
      rw [hl] at hw
      obtain ⟨hr0, hoff⟩ := finMem_bounds w hw
      rw [hr0] at hb
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      omega)
  have hfr5 : Fr m0 m1 st5.data := hfr.update
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hmx hm5 rfl rfl)
    (Match.sp_eq hmx hm5 rfl)
    (fun p hp => hnw5 p fun h => hp (Or.inl ((inRange_iff (by omega)).mpr h)))
    (hm5.kept hwf)
  refine call_then_elf hpc5 hkf ?pre fun st6 hpc6 hpost6 => ?_
  case pre =>
    simp only [KeccakFPre, keccakFStack]
    refine ⟨⟨by rw [hspN]; have := g.al; omega, by rw [hspN]; omega, fun i hi => ?_⟩,
      ⟨fun i hi => ?_, gr.nw, ?_⟩, fun i hi => ?_, ?_, ?_, ?_⟩
    · rw [show st5.data.regs.SP.toBitVec - BitVec.ofNat 64 192 = stackBelow st5.data 192 from rfl,
        hsb]
      exact hfr5.kept _ (hmapS i (by omega))
    · have hrcl : rcBytes.length = 192 := by
        rw [rcBytes, List.length_flatMap]
        simp only [length_wordBytes]
        rfl
      rw [hrcl] at hi
      rw [rc_same g gr hfr5 hpro.same hi]
      exact hpre.2.1.1 i (by rw [hrcl]; exact hi)
    · show _ + 192 ≤ (stackBelow st5.data 192).toNat ∨ (stackBelow st5.data 192).toNat + 192 ≤ _
      rw [hsb, hS192]
      have := gr.rs
      omega
    · rw [hX0]
      exact hfr5.kept _ (hmapS (192 + i) (by omega) |> fun h => by
        rwa [show frAt m0 - 192#64 + BitVec.ofNat 64 (192 + i) = frAt m0 + BitVec.ofNat 64 i by
          apply BitVec.eq_of_toNat_eq
          rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega), hS192, hf]
          omega] at h)
    · show st5.data.regs.X0.toBitVec.toNat + 200 ≤ _
      rw [hX0]; omega
    · show st5.data.regs.X0.toBitVec.toNat + 200 ≤ (stackBelow st5.data 192).toNat ∨
        (stackBelow st5.data 192).toNat + 192 ≤ st5.data.regs.X0.toBitVec.toNat
      rw [hX0, hsb, hS192, hf]
      omega
    · show st5.data.regs.X0.toBitVec.toNat + 200 ≤ rcAddr.toNat ∨
        rcAddr.toNat + 192 ≤ st5.data.regs.X0.toBitVec.toNat
      rw [hX0, hf]
      have := gr.rs
      omega
  obtain ⟨hbytesK, hsameK, hsavedK⟩ := hpost6
  have hX0' : st5.data.regs.X0.toBitVec = _ := hX0
  rw [hX0', hxor] at hbytesK
  rw [hX0', show keccakFStack = 192 from rfl, hsb] at hsameK
  have hfr6 : Fr m0 m1 st6.data := hfr5.update
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hsavedK.1 _ rfl)
    hsavedK.2.1
    (fun p hp => hsameK p fun hr => hp (by
      rcases hr with hr | hr
      · left
        rw [inRange_iff (by omega)] at hr
        rw [inRange_iff (by omega)]
        omega
      · exact Or.inr hr))
    hsavedK.2.2
  refine Eventually.done _ ⟨by rw [hpc6]; rfl, hfr6, ?_⟩
  have := bytesOf_of_bytesAt hbytesK
  rwa [keccakF, length_stateBytes, ← keccakF] at this

end

end NativeRustcArm.Hasher.Finalize
