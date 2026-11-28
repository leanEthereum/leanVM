module

public import NativeRustcVmArm.Keccak.KeccakF.Inv
public import NativeRustcVmArm.Keccak.KeccakF.Blocks

/-!
# `keccak_f`'s epilogue

`epilogue_step`: from the loop's exit after the 24 rounds (`At m0 24`), the machine inevitably
returns to the entry's return address in a state satisfying `KeccakFPost`: the epilogue
(`epilogue`, run in the environment of the machine at the exit, the state as region 1 through the
pointer the frame's slot 16 holds) stores the 25 lanes of Keccak-f[1600] of the entry's state,
restores X29, X30 and the callee-saved registers from the frame and SP, and returns.
-/

namespace NativeRustcVmArm.KeccakF

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write same_region2 load_of_wordAt
  bytesAt_stateBytes)

public section

variable [Host]

set_option linter.unusedSimpArgs false in
/-- **The epilogue.** -/
theorem epilogue_step {k : Nat} (hp : Placed Vm.KeccakF.code k) {m0 : MachineData}
    (hpre : NativeRustcVmArm.KeccakFPre m0) {m : MachineData} (hA : At m0 24 m) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = retOf m0 ∧ NativeRustcVmArm.KeccakFPost m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.KeccakF.b3Offset)⟩ := by
  obtain ⟨hstk, -, hmap, hnw, hap, -⟩ := hpre
  have hk : Vm.KeccakF.b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.KeccakF.b3Offset) :=
    Vm.KeccakF.b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine m [(frame m0, 400), (m0.regs.X0.toBitVec, 200)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun j hj => hA.kept _ (hstk.2.2 j hj), frame_noWrap hstk⟩,
      ⟨fun j hj => hA.kept _ (hmap j hj), hnw⟩, trivial⟩ (List.pairwise_pair.mpr hap.symm)
  have hb0 : env.regions[0]? = some (frame m0, 400) := rfl
  have hb1 : env.regions[1]? = some (m0.regs.X0.toBitVec, 200) := rfl
  have hsv := hA.saved
  simp only [AllOf, savedSlots] at hsv
  obtain ⟨s16, s304, s312, s320, s328, s336, s344, s352, s360, s368, s376, s384, s392, -⟩ := hsv
  have hm : Match env startEpi m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl, fun h => absurd h (by decide), trivial⟩
      (by rw [hA.sp]; simp [Sym.eval, Env.base, env]) trivial trivial trivial
      ⟨by
        show env.load 0 16 8 = _
        rw [load_of_wordAt (r := 0) s16]
        simp [Env.base, env]
        rfl, trivial⟩
  have hregs := hA.regs
  have hslots := hA.slots
  simp only [AllOf, laneRegs, laneSlots] at hregs hslots
  obtain ⟨h0, h1, h4, h5, h6, h8, h10, h11, h12, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, -⟩ := hregs
  obtain ⟨h7, h9, h3, h13, h2, -⟩ := hslots
  have e0 : env.regs .X27 = (Keccak.lane (stAfter m0 24) 0).toBitVec := h0
  have e1 : env.regs .X11 = (Keccak.lane (stAfter m0 24) 1).toBitVec := h1
  have e4 : env.regs .X18 = (Keccak.lane (stAfter m0 24) 4).toBitVec := h4
  have e5 : env.regs .X5 = (Keccak.lane (stAfter m0 24) 5).toBitVec := h5
  have e6 : env.regs .X12 = (Keccak.lane (stAfter m0 24) 6).toBitVec := h6
  have e8 : env.regs .X16 = (Keccak.lane (stAfter m0 24) 8).toBitVec := h8
  have e10 : env.regs .X10 = (Keccak.lane (stAfter m0 24) 10).toBitVec := h10
  have e11 : env.regs .X0 = (Keccak.lane (stAfter m0 24) 11).toBitVec := h11
  have e12 : env.regs .X17 = (Keccak.lane (stAfter m0 24) 12).toBitVec := h12
  have e14 : env.regs .X6 = (Keccak.lane (stAfter m0 24) 14).toBitVec := h14
  have e15 : env.regs .X25 = (Keccak.lane (stAfter m0 24) 15).toBitVec := h15
  have e16 : env.regs .X2 = (Keccak.lane (stAfter m0 24) 16).toBitVec := h16
  have e17 : env.regs .X1 = (Keccak.lane (stAfter m0 24) 17).toBitVec := h17
  have e18 : env.regs .X4 = (Keccak.lane (stAfter m0 24) 18).toBitVec := h18
  have e19 : env.regs .X22 = (Keccak.lane (stAfter m0 24) 19).toBitVec := h19
  have e20 : env.regs .X3 = (Keccak.lane (stAfter m0 24) 20).toBitVec := h20
  have e21 : env.regs .X21 = (Keccak.lane (stAfter m0 24) 21).toBitVec := h21
  have e22 : env.regs .X7 = (Keccak.lane (stAfter m0 24) 22).toBitVec := h22
  have e23 : env.regs .X26 = (Keccak.lane (stAfter m0 24) 23).toBitVec := h23
  have e24 : env.regs .X23 = (Keccak.lane (stAfter m0 24) 24).toBitVec := h24
  have e7 : env.load 0 56 8 = (Keccak.lane (stAfter m0 24) 7).toBitVec :=
    load_of_wordAt (r := 0) h7
  have e9 : env.load 0 64 8 = (Keccak.lane (stAfter m0 24) 9).toBitVec :=
    load_of_wordAt (r := 0) h9
  have e3 : env.load 0 72 8 = (Keccak.lane (stAfter m0 24) 3).toBitVec :=
    load_of_wordAt (r := 0) h3
  have e13 : env.load 0 80 8 = (Keccak.lane (stAfter m0 24) 13).toBitVec :=
    load_of_wordAt (r := 0) h13
  have e2 : env.load 0 88 8 = (Keccak.lane (stAfter m0 24) 2).toBitVec :=
    load_of_wordAt (r := 0) h2
  have t304 : env.load 0 304 8 = (m0.regs.getXReg .X29).toBitVec := load_of_wordAt (r := 0) s304
  have t312 : env.load 0 312 8 = (m0.regs.getXReg .X30).toBitVec := load_of_wordAt (r := 0) s312
  have t320 : env.load 0 320 8 = (m0.regs.getXReg .X28).toBitVec := load_of_wordAt (r := 0) s320
  have t328 : env.load 0 328 8 = (m0.regs.getXReg .X27).toBitVec := load_of_wordAt (r := 0) s328
  have t336 : env.load 0 336 8 = (m0.regs.getXReg .X26).toBitVec := load_of_wordAt (r := 0) s336
  have t344 : env.load 0 344 8 = (m0.regs.getXReg .X25).toBitVec := load_of_wordAt (r := 0) s344
  have t352 : env.load 0 352 8 = (m0.regs.getXReg .X24).toBitVec := load_of_wordAt (r := 0) s352
  have t360 : env.load 0 360 8 = (m0.regs.getXReg .X23).toBitVec := load_of_wordAt (r := 0) s360
  have t368 : env.load 0 368 8 = (m0.regs.getXReg .X22).toBitVec := load_of_wordAt (r := 0) s368
  have t376 : env.load 0 376 8 = (m0.regs.getXReg .X21).toBitVec := load_of_wordAt (r := 0) s376
  have t384 : env.load 0 384 8 = (m0.regs.getXReg .X20).toBitVec := load_of_wordAt (r := 0) s384
  have t392 : env.load 0 392 8 = (m0.regs.getXReg .X19).toBitVec := load_of_wordAt (r := 0) s392
  refine exec_then hk epilogue hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_⟩
  · have hx30 : st.data.regs.getXReg .X30 = m0.regs.getXReg .X30 :=
      UInt64.toBitVec_inj.mp ((hm'.regs .X30 _ rfl).trans (by sym_simp; exact t312))
    simp only [PcOk] at hpc
    rw [hpc, retOf, retOf]
    rw [show st.data.regs.X30 = m0.regs.X30 from hx30]
  · intro A hA0
    have hb : bytesOf m0.dmem m0.regs.X0.toBitVec 200 = stateBytes A := by
      rw [← length_stateBytes A]
      exact Hasher.bytesOf_of_bytesAt hA0
    have hst : stAfter m0 24 = keccakF1600 A := by
      rw [stAfter, hb, stateOf_stateBytes, roundsTo_24]
    show BytesAt st.data.dmem m0.regs.X0.toBitVec (stateBytes (keccakF1600 A))
    rw [← hst]
    refine bytesAt_stateBytes fun j hj => ?_
    generalize stAfter m0 24 = B at *
    interval_cases j <;>
    · refine wordAt_of_eq (wordAt_write hm' hb1 (by decide) rfl) ?_
      sym_simp
      simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17,
        e18, e19, e20, e21, e22, e23, e24]
  · intro p hp
    refine (same_region2 hm' hwf hb0 hb1 (by decide) p ?_).trans (hA.same p ?_)
    · rintro (h | h)
      · exact hp (.inr h)
      · exact hp (.inl h)
    · exact fun h => hp (.inr h)
  · refine ⟨fun r hr => ?_, ?_, fun p h => hm'.kept hwf p (hA.kept p h)⟩
    · cases r <;> try exact absurd hr (by decide)
      all_goals exact UInt64.toBitVec_inj.mp ((hm'.regs _ _ rfl).trans (by
        sym_simp
        simp only [t304, t320, t328, t336, t344, t352, t360, t368, t376, t384, t392]))
    · apply UInt64.toBitVec_inj.mp
      rw [hm'.sp]
      show m0.regs.SP.toBitVec - BitVec.ofNat 64 400 + BitVec.ofInt 64 400 = _
      exact BitVec.sub_add_cancel _ _

end

end NativeRustcVmArm.KeccakF
