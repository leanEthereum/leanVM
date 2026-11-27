module

public import NativeRustcX64.KeccakF.Inv
public import NativeRustcX64.KeccakF.Blocks

/-!
# `keccak_f`'s prologue (x86-64)

`prologue_step`: from `keccak_f`'s entry, in a state satisfying `KeccakFPre`, the machine
inevitably reaches the round loop's head with the loop invariant before the first round
(`At m0 0`): the prologue (`prologue`, run in the environment of the entry state with the frame
and the state as regions) pushes the callee-saved registers, stores the state pointer, initializes
the counter slot to 8, loads the lanes into registers and frame slots, and XORs the column
parities.
-/

namespace NativeRustcX64.KeccakF

open NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics

public section

variable [ElfHost]

set_option linter.unusedSimpArgs false in
/-- **The prologue.** -/
theorem prologue_step {sec k : Nat} (hp : PlacedIn Common.KeccakF.code sec k) {m0 : MachineData}
    (hpre : KeccakFPre m0) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => At m0 0 st.data ∧ st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.KeccakF.b1Offset))
      ⟨m0, ElfHost.addrOf sec k⟩ := by
  obtain ⟨hstk, -, hmap, hnw, hap, -⟩ := hpre
  have hk : Common.KeccakF.b0.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.KeccakF.b0Offset) :=
    Common.KeccakF.b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine m0 [(frame m0, 296), (m0.regs.get64 .rdi, 200)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨hstk.2.2, frame_noWrap hstk⟩, ⟨hmap, hnw⟩, trivial⟩
      (List.pairwise_pair.mpr hap.symm)
  have hm : Match env startPro m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨show rspOf m0 = _ from (frame_add m0).symm.trans rfl,
        show m0.regs.get64 .rdi = _ from (BitVec.add_zero _).symm.trans rfl, trivial⟩
      trivial trivial trivial
  have hb0 : env.regions[0]? = some (frame m0, 296) := rfl
  have hl : ∀ {off : Nat} (j : Nat), off = 8 * j → j < 25 →
      env.load 1 off 8 = (Keccak.lane (stAfter m0 0) j).toBitVec :=
    fun j hoff hj => load_lane' hoff hj
  have hl0 : env.load 1 0 8 = (Keccak.lane (stAfter m0 0) 0).toBitVec :=
    hl 0 rfl (by decide)
  have hl1 : env.load 1 8 8 = (Keccak.lane (stAfter m0 0) 1).toBitVec :=
    hl 1 rfl (by decide)
  have hl2 : env.load 1 16 8 = (Keccak.lane (stAfter m0 0) 2).toBitVec :=
    hl 2 rfl (by decide)
  have hl3 : env.load 1 24 8 = (Keccak.lane (stAfter m0 0) 3).toBitVec :=
    hl 3 rfl (by decide)
  have hl4 : env.load 1 32 8 = (Keccak.lane (stAfter m0 0) 4).toBitVec :=
    hl 4 rfl (by decide)
  have hl5 : env.load 1 40 8 = (Keccak.lane (stAfter m0 0) 5).toBitVec :=
    hl 5 rfl (by decide)
  have hl6 : env.load 1 48 8 = (Keccak.lane (stAfter m0 0) 6).toBitVec :=
    hl 6 rfl (by decide)
  have hl7 : env.load 1 56 8 = (Keccak.lane (stAfter m0 0) 7).toBitVec :=
    hl 7 rfl (by decide)
  have hl8 : env.load 1 64 8 = (Keccak.lane (stAfter m0 0) 8).toBitVec :=
    hl 8 rfl (by decide)
  have hl9 : env.load 1 72 8 = (Keccak.lane (stAfter m0 0) 9).toBitVec :=
    hl 9 rfl (by decide)
  have hl10 : env.load 1 80 8 = (Keccak.lane (stAfter m0 0) 10).toBitVec :=
    hl 10 rfl (by decide)
  have hl11 : env.load 1 88 8 = (Keccak.lane (stAfter m0 0) 11).toBitVec :=
    hl 11 rfl (by decide)
  have hl12 : env.load 1 96 8 = (Keccak.lane (stAfter m0 0) 12).toBitVec :=
    hl 12 rfl (by decide)
  have hl13 : env.load 1 104 8 = (Keccak.lane (stAfter m0 0) 13).toBitVec :=
    hl 13 rfl (by decide)
  have hl14 : env.load 1 112 8 = (Keccak.lane (stAfter m0 0) 14).toBitVec :=
    hl 14 rfl (by decide)
  have hl15 : env.load 1 120 8 = (Keccak.lane (stAfter m0 0) 15).toBitVec :=
    hl 15 rfl (by decide)
  have hl16 : env.load 1 128 8 = (Keccak.lane (stAfter m0 0) 16).toBitVec :=
    hl 16 rfl (by decide)
  have hl17 : env.load 1 136 8 = (Keccak.lane (stAfter m0 0) 17).toBitVec :=
    hl 17 rfl (by decide)
  have hl18 : env.load 1 144 8 = (Keccak.lane (stAfter m0 0) 18).toBitVec :=
    hl 18 rfl (by decide)
  have hl19 : env.load 1 152 8 = (Keccak.lane (stAfter m0 0) 19).toBitVec :=
    hl 19 rfl (by decide)
  have hl20 : env.load 1 160 8 = (Keccak.lane (stAfter m0 0) 20).toBitVec :=
    hl 20 rfl (by decide)
  have hl21 : env.load 1 168 8 = (Keccak.lane (stAfter m0 0) 21).toBitVec :=
    hl 21 rfl (by decide)
  have hl22 : env.load 1 176 8 = (Keccak.lane (stAfter m0 0) 22).toBitVec :=
    hl 22 rfl (by decide)
  have hl23 : env.load 1 184 8 = (Keccak.lane (stAfter m0 0) 23).toBitVec :=
    hl 23 rfl (by decide)
  have hl24 : env.load 1 192 8 = (Keccak.lane (stAfter m0 0) 24).toBitVec :=
    hl 24 rfl (by decide)
  refine exec_then_elf hk prologue hwf nofun hm fun st hm' hpc => .done _ ⟨?_, hpc⟩
  refine ⟨(hm'.regs .rsp _ rfl).trans rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    same_region hm' hwf hb0 (by decide) (by decide), hm'.kept hwf⟩
  · exact wordAt_of_eq (wordAt_write hm' hb0 (by decide) rfl) rfl
  · refine wordAt_of_eq (wordAt_write hm' hb0 (by decide) rfl) ?_
    exact BitVec.add_zero _
  all_goals simp only [AllOf, laneRegs, laneSlots, parRegs, savedSlots]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    · refine (hm'.regs _ _ rfl).trans ?_
      sym_simp
      simp only [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14, hl15, hl16, hl17, hl18, hl19, hl20, hl21, hl22, hl23, hl24]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    · refine wordAt_of_eq (wordAt_write hm' hb0 (by decide) rfl) ?_
      sym_simp
      simp only [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14, hl15, hl16, hl17, hl18, hl19, hl20, hl21, hl22, hl23, hl24]
  · refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    · refine (hm'.regs _ _ rfl).trans ?_
      sym_simp
      generalize stAfter m0 0 = A at *
      simp only [hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14, hl15, hl16, hl17, hl18, hl19, hl20, hl21, hl22, hl23, hl24, par, UInt64.toBitVec_xor, Nat.reduceAdd]
      ac_rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    exact wordAt_of_eq (wordAt_write hm' hb0 (by decide) rfl) rfl

end

end NativeRustcX64.KeccakF
