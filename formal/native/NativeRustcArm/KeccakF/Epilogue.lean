module

public import NativeRustcArm.KeccakF.Inv
public import NativeRustcArm.KeccakF.Blocks

/-!
# `keccak_f`'s epilogue

`epilogue_step`: from the loop's exit after the 24 rounds (`At m0 24`), the machine inevitably
returns to the entry's return address in a state satisfying `KeccakFPost`: the epilogue
(`epilogue`, run in the environment of the machine at the exit, the state as region 1 through the
pointer the frame's slot 8 holds) stores the 25 lanes of Keccak-f[1600] of the entry's state,
restores the callee-saved registers and X30 from the frame and SP, and returns.
-/

namespace NativeRustcArm.KeccakF

open NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics NativeRustcArm

public section

variable [ElfHost]

set_option linter.unusedSimpArgs false in
/-- **The epilogue.** -/
theorem epilogue_step {sec k : Nat} (hp : PlacedIn Common.KeccakF.code sec k) {m0 : MachineData}
    (hpre : KeccakFPre m0) {m : MachineData} (hA : At m0 24 m) :
    Eventually (elfStep1 ElfHost.exe) (fun st => st.pc = retOf m0 ∧ KeccakFPost m0 st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcArm.Common.KeccakF.b2Offset)⟩ := by
  obtain ⟨hstk, -, hmap, hnw, hap, -⟩ := hpre
  have hk : Common.KeccakF.b2.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcArm.Common.KeccakF.b2Offset) :=
    Common.KeccakF.b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine m [(frame m0, 192), (m0.regs.X0.toBitVec, 200)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun j hj => hA.kept _ (hstk.2.2 j hj), frame_noWrap hstk⟩,
      ⟨fun j hj => hA.kept _ (hmap j hj), hnw⟩, trivial⟩ (List.pairwise_pair.mpr hap.symm)
  have hb0 : env.regions[0]? = some (frame m0, 192) := rfl
  have hb1 : env.regions[1]? = some (m0.regs.X0.toBitVec, 200) := rfl
  have hsv := hA.saved
  simp only [AllOf, savedSlots] at hsv
  obtain ⟨s8, s96, s112, s120, s128, s136, s144, s152, s160, s168, s176, s184, -⟩ := hsv
  have hm : Match env startEpi m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl, fun h => absurd h (by decide), trivial⟩
      (by rw [hA.sp]; simp [Sym.eval, Env.base, env]) trivial trivial trivial
      ⟨by
        show env.load 0 8 8 = _
        rw [load_of_wordAt (r := 0) s8]
        simp [Env.base, env]
        rfl, trivial⟩
  have hregs := hA.regs
  have hslots := hA.slots
  simp only [AllOf, laneRegs, laneSlots] at hregs hslots
  obtain ⟨h4, h6, h8, h9, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, -⟩ := hregs
  obtain ⟨h0, h1, h2, h3, h5, h7, h10, -⟩ := hslots
  have e4 : env.regs .X22 = (Keccak.lane (stAfter m0 24) 4).toBitVec := h4
  have e6 : env.regs .X4 = (Keccak.lane (stAfter m0 24) 6).toBitVec := h6
  have e8 : env.regs .X12 = (Keccak.lane (stAfter m0 24) 8).toBitVec := h8
  have e9 : env.regs .X6 = (Keccak.lane (stAfter m0 24) 9).toBitVec := h9
  have e11 : env.regs .X2 = (Keccak.lane (stAfter m0 24) 11).toBitVec := h11
  have e12 : env.regs .X1 = (Keccak.lane (stAfter m0 24) 12).toBitVec := h12
  have e13 : env.regs .X7 = (Keccak.lane (stAfter m0 24) 13).toBitVec := h13
  have e14 : env.regs .X5 = (Keccak.lane (stAfter m0 24) 14).toBitVec := h14
  have e15 : env.regs .X18 = (Keccak.lane (stAfter m0 24) 15).toBitVec := h15
  have e16 : env.regs .X19 = (Keccak.lane (stAfter m0 24) 16).toBitVec := h16
  have e17 : env.regs .X3 = (Keccak.lane (stAfter m0 24) 17).toBitVec := h17
  have e18 : env.regs .X25 = (Keccak.lane (stAfter m0 24) 18).toBitVec := h18
  have e19 : env.regs .X20 = (Keccak.lane (stAfter m0 24) 19).toBitVec := h19
  have e20 : env.regs .X23 = (Keccak.lane (stAfter m0 24) 20).toBitVec := h20
  have e21 : env.regs .X21 = (Keccak.lane (stAfter m0 24) 21).toBitVec := h21
  have e22 : env.regs .X16 = (Keccak.lane (stAfter m0 24) 22).toBitVec := h22
  have e23 : env.regs .X24 = (Keccak.lane (stAfter m0 24) 23).toBitVec := h23
  have e24 : env.regs .X27 = (Keccak.lane (stAfter m0 24) 24).toBitVec := h24
  have e0 : env.load 0 48 8 = (Keccak.lane (stAfter m0 24) 0).toBitVec :=
    load_of_wordAt (r := 0) h0
  have e1 : env.load 0 88 8 = (Keccak.lane (stAfter m0 24) 1).toBitVec :=
    load_of_wordAt (r := 0) h1
  have e2 : env.load 0 80 8 = (Keccak.lane (stAfter m0 24) 2).toBitVec :=
    load_of_wordAt (r := 0) h2
  have e3 : env.load 0 56 8 = (Keccak.lane (stAfter m0 24) 3).toBitVec :=
    load_of_wordAt (r := 0) h3
  have e5 : env.load 0 72 8 = (Keccak.lane (stAfter m0 24) 5).toBitVec :=
    load_of_wordAt (r := 0) h5
  have e7 : env.load 0 64 8 = (Keccak.lane (stAfter m0 24) 7).toBitVec :=
    load_of_wordAt (r := 0) h7
  have e10 : env.load 0 40 8 = (Keccak.lane (stAfter m0 24) 10).toBitVec :=
    load_of_wordAt (r := 0) h10
  have t96 : env.load 0 96 8 = (m0.regs.getXReg .X30).toBitVec := load_of_wordAt (r := 0) s96
  have t112 : env.load 0 112 8 = (m0.regs.getXReg .X28).toBitVec := load_of_wordAt (r := 0) s112
  have t120 : env.load 0 120 8 = (m0.regs.getXReg .X27).toBitVec := load_of_wordAt (r := 0) s120
  have t128 : env.load 0 128 8 = (m0.regs.getXReg .X26).toBitVec := load_of_wordAt (r := 0) s128
  have t136 : env.load 0 136 8 = (m0.regs.getXReg .X25).toBitVec := load_of_wordAt (r := 0) s136
  have t144 : env.load 0 144 8 = (m0.regs.getXReg .X24).toBitVec := load_of_wordAt (r := 0) s144
  have t152 : env.load 0 152 8 = (m0.regs.getXReg .X23).toBitVec := load_of_wordAt (r := 0) s152
  have t160 : env.load 0 160 8 = (m0.regs.getXReg .X22).toBitVec := load_of_wordAt (r := 0) s160
  have t168 : env.load 0 168 8 = (m0.regs.getXReg .X21).toBitVec := load_of_wordAt (r := 0) s168
  have t176 : env.load 0 176 8 = (m0.regs.getXReg .X20).toBitVec := load_of_wordAt (r := 0) s176
  have t184 : env.load 0 184 8 = (m0.regs.getXReg .X19).toBitVec := load_of_wordAt (r := 0) s184
  refine exec_then_elf hk epilogue hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hx30 : st.data.regs.getXReg .X30 = m0.regs.getXReg .X30 :=
      UInt64.toBitVec_inj.mp ((hm'.regs .X30 _ rfl).trans (by sym_simp; exact t96))
    simp only [PcOk] at hpc
    rw [hpc, retOf, retOf]
    rw [show st.data.regs.X30 = m0.regs.X30 from hx30]
  · show BytesAt st.data.dmem m0.regs.X0.toBitVec (keccakF (bytesOf m0.dmem m0.regs.X0.toBitVec 200))
    rw [keccakF, ← roundsTo_24]
    refine bytesAt_stateBytes fun j hj => ?_
    show WordAt _ _ (Keccak.lane (stAfter m0 24) j).toBitVec
    generalize stAfter m0 24 = A at *
    interval_cases j <;>
    · refine wordAt_of_eq (wordAt_write hm' hb1 (by decide) rfl) ?_
      sym_simp
      simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  · intro p hp
    refine (same_region2 hm' hwf hb0 hb1 (by decide) p ?_).trans (hA.same p ?_)
    · rintro (h | h)
      · exact hp (.inr h)
      · exact hp (.inl h)
    · exact fun h => hp (.inr h)
  · intro r hr
    cases r <;> try exact absurd hr (by decide)
    all_goals first
      | exact (Match.reg_eq hm hm' rfl rfl).trans hA.x29
      | exact UInt64.toBitVec_inj.mp ((hm'.regs _ _ rfl).trans (by sym_simp; simp only [t96, t112, t120, t128, t136, t144, t152, t160, t168, t176, t184]))
  · apply UInt64.toBitVec_inj.mp
    rw [hm'.sp]
    show m0.regs.SP.toBitVec - BitVec.ofNat 64 192 + BitVec.ofInt 64 192 = _
    exact BitVec.sub_add_cancel _ _
  · exact fun p h => hm'.kept hwf p (hA.kept p h)

end

end NativeRustcArm.KeccakF
