module

public import NativeRustcVmX64.Keccak.KeccakF.Inv
public import NativeRustcVmX64.Keccak.KeccakF.Blocks

/-!
# `keccak_f`'s epilogue (x86-64)

`epilogue_step`: from the loop's exit after the 24 rounds (`At m0 24`), the machine inevitably
returns to the entry's return address, with RSP 8 above the entry's, in a state satisfying
`KeccakFPost`: the epilogue (`epilogue`, run in the environment of the machine at the exit, the
state as region 1 through the pointer the frame's offset 184 holds) stores the 25 lanes of
Keccak-f[1600] of the entry's state, pops the callee-saved registers and returns to the address
the frame's last 8 bytes hold, the entry's (`retOf`).
-/

namespace NativeRustcVmX64.KeccakF

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write same_region2 load_of_wordAt
  bytesAt_stateBytes)

public section

/-- The return address: the frame's last 8 bytes, the entry's 8 bytes at RSP. -/
theorem load_ret {env : Env} {m0 m : MachineData} {i : Nat}
    (hstk : StackOk m0 NativeRustcVmX64.keccakFStack) (hA : At m0 i m) (hb : env.base 0 = frame m0)
    (hd : env.mem0 = m.dmem) :
    env.load 0 480 8 = BitVec.ofInt 64 ((Mem.loadInt m0.dmem (rspOf m0) 8).getD 0) := by
  have haddr : ∀ j, frame m0 + BitVec.ofNat 64 (480 + j) = rspOf m0 + BitVec.ofNat 64 j :=
    fun j => by rw [← addr_add, frame_add]
  have hget : ∀ j < 8, m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      some ((m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)).getD 0) := fun j hj => by
    have := hstk.2.2 (480 + j) (by simp only [NativeRustcVmX64.keccakFStack]; omega)
    rw [show rspOf m0 - BitVec.ofNat 64 NativeRustcVmX64.keccakFStack = frame m0 from rfl,
      haddr] at this
    revert this
    cases m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) <;> simp
  rw [loadInt_of_get? _ _ 8 _ hget, Option.getD_some]
  unfold Env.load
  congr 2
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [hb, hd, haddr, hA.same]
  have hf := frame_noWrap hstk
  have h1 := hstk.1
  have h2 := hstk.2.1
  unfold NoWrap at hf
  rw [inRange_iff (by simp only [NativeRustcVmX64.keccakFStack] at hf ⊢; omega),
    toNat_add_ofNat _ _ (by omega), frame_toNat hstk]
  simp only [NativeRustcVmX64.keccakFStack] at h1 ⊢
  omega

variable [Host]

set_option linter.unusedSimpArgs false in
/-- **The epilogue.** -/
theorem epilogue_step {k : Nat} (hp : Placed Vm.KeccakF.code k) {m0 : MachineData}
    (hpre : NativeRustcVmX64.KeccakFPre m0) {m : MachineData} (hA : At m0 24 m) :
    Eventually (step1 Host.exe) (fun st => st.pc = retOf m0 ∧
      rspOf st.data = rspOf m0 + 8#64 ∧ NativeRustcVmX64.KeccakFPost m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b3Offset)⟩ := by
  obtain ⟨hstk, -, hmap, hnw, hap, -⟩ := hpre
  have hk : Vm.KeccakF.b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.KeccakF.b3Offset) :=
    Vm.KeccakF.b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine m [(frame m0, 488), (m0.regs.get64 .rdi, 200)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun j hj => hA.kept _ (hstk.2.2 j hj), frame_noWrap hstk⟩,
      ⟨fun j hj => hA.kept _ (hmap j hj), hnw⟩, trivial⟩ (List.pairwise_pair.mpr hap.symm)
  have hb0 : env.regions[0]? = some (frame m0, 488) := rfl
  have hb1 : env.regions[1]? = some (m0.regs.get64 .rdi, 200) := rfl
  have hsv := hA.saved
  simp only [AllOf, savedSlots] at hsv
  obtain ⟨s432, s440, s448, s456, s464, s472, -⟩ := hsv
  have hm : Match env startEpi m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨show rspOf m = _ from hA.rsp.trans rfl, trivial⟩
      trivial trivial
      ⟨show env.load 0 184 8 = _ from (load_of_wordAt (r := 0) hA.ptr).trans
        (BitVec.add_zero _).symm, trivial⟩
  have hregs := hA.regs
  have hslots := hA.slots
  simp only [AllOf, laneRegs, laneSlots] at hregs hslots
  obtain ⟨h3, h6, h7, h8, h11, h12, h13, h15, h16, h17, h18, -⟩ := hregs
  obtain ⟨h0, h1, h2, h4, h5, h9, h10, h14, h19, h20, h21, h22, h23, h24, -⟩ := hslots
  have e3 : env.regs .r12 = (Keccak.lane (stAfter m0 24) 3).toBitVec := h3
  have e6 : env.regs .r15 = (Keccak.lane (stAfter m0 24) 6).toBitVec := h6
  have e7 : env.regs .r14 = (Keccak.lane (stAfter m0 24) 7).toBitVec := h7
  have e8 : env.regs .r13 = (Keccak.lane (stAfter m0 24) 8).toBitVec := h8
  have e11 : env.regs .r11 = (Keccak.lane (stAfter m0 24) 11).toBitVec := h11
  have e12 : env.regs .rbp = (Keccak.lane (stAfter m0 24) 12).toBitVec := h12
  have e13 : env.regs .rdi = (Keccak.lane (stAfter m0 24) 13).toBitVec := h13
  have e15 : env.regs .r8 = (Keccak.lane (stAfter m0 24) 15).toBitVec := h15
  have e16 : env.regs .rsi = (Keccak.lane (stAfter m0 24) 16).toBitVec := h16
  have e17 : env.regs .r9 = (Keccak.lane (stAfter m0 24) 17).toBitVec := h17
  have e18 : env.regs .r10 = (Keccak.lane (stAfter m0 24) 18).toBitVec := h18
  have e0 : env.load 0 40 8 = (Keccak.lane (stAfter m0 24) 0).toBitVec :=
    load_of_wordAt (r := 0) h0
  have e1 : env.load 0 112 8 = (Keccak.lane (stAfter m0 24) 1).toBitVec :=
    load_of_wordAt (r := 0) h1
  have e2 : env.load 0 104 8 = (Keccak.lane (stAfter m0 24) 2).toBitVec :=
    load_of_wordAt (r := 0) h2
  have e4 : env.load 0 120 8 = (Keccak.lane (stAfter m0 24) 4).toBitVec :=
    load_of_wordAt (r := 0) h4
  have e5 : env.load 0 56 8 = (Keccak.lane (stAfter m0 24) 5).toBitVec :=
    load_of_wordAt (r := 0) h5
  have e9 : env.load 0 48 8 = (Keccak.lane (stAfter m0 24) 9).toBitVec :=
    load_of_wordAt (r := 0) h9
  have e10 : env.load 0 32 8 = (Keccak.lane (stAfter m0 24) 10).toBitVec :=
    load_of_wordAt (r := 0) h10
  have e14 : env.load 0 8 8 = (Keccak.lane (stAfter m0 24) 14).toBitVec :=
    load_of_wordAt (r := 0) h14
  have e19 : env.load 0 16 8 = (Keccak.lane (stAfter m0 24) 19).toBitVec :=
    load_of_wordAt (r := 0) h19
  have e20 : env.load 0 96 8 = (Keccak.lane (stAfter m0 24) 20).toBitVec :=
    load_of_wordAt (r := 0) h20
  have e21 : env.load 0 72 8 = (Keccak.lane (stAfter m0 24) 21).toBitVec :=
    load_of_wordAt (r := 0) h21
  have e22 : env.load 0 88 8 = (Keccak.lane (stAfter m0 24) 22).toBitVec :=
    load_of_wordAt (r := 0) h22
  have e23 : env.load 0 80 8 = (Keccak.lane (stAfter m0 24) 23).toBitVec :=
    load_of_wordAt (r := 0) h23
  have e24 : env.load 0 24 8 = (Keccak.lane (stAfter m0 24) 24).toBitVec :=
    load_of_wordAt (r := 0) h24
  have t432 : env.load 0 432 8 = m0.regs.get64 .rbx := load_of_wordAt (r := 0) s432
  have t440 : env.load 0 440 8 = m0.regs.get64 .r12 := load_of_wordAt (r := 0) s440
  have t448 : env.load 0 448 8 = m0.regs.get64 .r13 := load_of_wordAt (r := 0) s448
  have t456 : env.load 0 456 8 = m0.regs.get64 .r14 := load_of_wordAt (r := 0) s456
  have t464 : env.load 0 464 8 = m0.regs.get64 .r15 := load_of_wordAt (r := 0) s464
  have t472 : env.load 0 472 8 = m0.regs.get64 .rbp := load_of_wordAt (r := 0) s472
  refine exec_then hk epilogue hwf nofun hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    sym_simp
    rw [retOf, load_ret hstk hA rfl rfl]
  · refine (hm'.regs .rsp _ rfl).trans ?_
    show frame m0 + BitVec.ofInt 64 488 = _
    rw [← frame_add m0, BitVec.add_assoc]
    rfl
  · intro A hA0
    have hb : bytesOf m0.dmem (m0.regs.get64 .rdi) 200 = stateBytes A := by
      rw [← length_stateBytes A]
      exact Hasher.bytesOf_of_bytesAt hA0
    have hst : stAfter m0 24 = keccakF1600 A := by
      rw [stAfter, hb, stateOf_stateBytes, roundsTo_24]
    show BytesAt st.data.dmem (m0.regs.get64 .rdi) (stateBytes (keccakF1600 A))
    rw [← hst]
    refine bytesAt_stateBytes fun j hj => ?_
    generalize stAfter m0 24 = B at *
    interval_cases j <;>
    · refine wordAt_of_eq (wordAt_write hm' hb1 (by decide) rfl) ?_
      sym_simp
      simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17,
        e18, e19, e20, e21, e22, e23, e24]
  · intro p hp
    refine (same_region2 (lim := 480) hm' hwf hb0 hb1 (by decide) (by decide) p ?_).trans
      (hA.same p ?_)
    · rintro (h | h)
      · exact hp (.inr h)
      · exact hp (.inl h)
    · exact fun h => hp (.inr h)
  · intro r hr
    cases r <;> try exact absurd hr (by decide)
    all_goals exact (hm'.regs _ _ rfl).trans (by
      sym_simp
      simp only [t432, t440, t448, t456, t464, t472])
  · exact fun p h => hm'.kept hwf p (hA.kept p h)

end

end NativeRustcVmX64.KeccakF
