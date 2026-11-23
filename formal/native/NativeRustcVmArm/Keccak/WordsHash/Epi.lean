module

public import NativeRustcVmArm.Keccak.WordsHash.PadRun

/-!
# `keccak256_words::<hash_words's closure>`: the epilogue

`epi_run`: from the epilogue (`EpiAt`), the machine returns with the first four lanes of
`keccakF1600 (lastB m0)` at `out`, which are `hashWords` of the slice's words (`digest_eq`),
restoring the callee-saved registers from the frame (`Keccak256WordsHashPost`).
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write load_of_wordAt byteOf_toBitVec)
open NativeRustcVm.Keccak Vm.Keccak256WordsOfHashWords NativeRustcVmArm.Keccak

public section

/-- The words the slice holds at entry. -/
theorem word_eq {m0 : MachineData} {w : List UInt64} (hlen : w.length = m0.regs.X4.toNat)
    (hw : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec w) (i : Nat) :
    word m0 i = w.getD i 0 := by
  have hb : bytesOf m0.dmem m0.regs.X3.toBitVec (8 * m0.regs.X4.toNat) =
      Native.Keccak.wordsBytes w := by
    rw [← hlen, ← Native.Keccak.Proof.length_wordsBytes]
    exact Hasher.bytesOf_of_bytesAt hw
  rw [word, hb, Native.Keccak.Proof.littleEndianLane_wordsBytes]

/-- **The digest is `hashWords`** of the slice's words. -/
theorem digest_eq {m0 : MachineData} (g : Geo m0) {w : List UInt64}
    (hlen : w.length = m0.regs.X4.toNat)
    (hw : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec w) :
    (NativeVm.Model.hashWords w.toArray).toList =
      [Keccak.lane (keccakF1600 (lastB m0)) 0, Keccak.lane (keccakF1600 (lastB m0)) 1,
        Keccak.lane (keccakF1600 (lastB m0)) 2, Keccak.lane (keccakF1600 (lastB m0)) 3] := by
  have hf : (fun i => if i < w.length then w.getD i 0 else 0) = word m0 := by
    funext i
    rw [word_eq hlen hw]
    split
    · rfl
    · rw [getD_eq_zero (by omega)]
  have hF : keccakF1600 (lastB m0) =
      finalState (fun i => if i < w.length then w.getD i 0 else 0) (8 * w.length) := by
    rw [hf, hlen, ← g.len]
    rfl
  rw [hashWords_eq, hF]
  rfl

variable [Host]

/-- **The epilogue.** -/
theorem epi_run {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData}
    (g : Geo m0) (hout : Mapped m0.dmem m0.regs.X0.toBitVec 32 ∧ NoWrap m0.regs.X0.toBitVec 32 ∧
      Apart m0.regs.X0.toBitVec 32 (stackBelow m0 NativeRustcVmArm.keccak256WordsStack)
        NativeRustcVmArm.keccak256WordsStack)
    {st : MachineState} (h : EpiAt m0 k st) :
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = retOf m0 ∧ NativeRustcVmArm.Keccak256WordsHashPost m0 st'.data) st := by
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  subst hpc
  have hstk := g.stk
  obtain ⟨hmap, hnw, hap⟩ := hout
  obtain ⟨hS, hF, hS688, hlt⟩ := stack_facts hstk
  have hK : NativeRustcVmArm.keccak256WordsStack = 688 := rfl
  have hap1 : Apart (frame m0) 288 m0.regs.X0.toBitVec 32 := by
    unfold Apart at hap ⊢
    omega
  let env := Env.ofMachine m [(frame m0, 288), (m0.regs.X0.toBitVec, 32)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩,
      ⟨fun i hi => hc.kept _ (hmap i hi), hnw⟩, trivial⟩ (List.pairwise_pair.mpr hap1)
  have hm : Match env startEpi m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl, fun h => absurd h (by decide), trivial⟩
      (by rw [hc.sp]; simp [Sym.eval])
      ⟨by show (m.regs.getXReg .X19).toBitVec = _; rw [hc.x19]; simp [Sym.eval], trivial⟩ trivial
      trivial trivial
  have hb0 : env.regions[0]? = some (frame m0, 288) := rfl
  have hb1 : env.regions[1]? = some (m0.regs.X0.toBitVec, 32) := rfl
  have hbase : env.base 0 = frame m0 := rfl
  have hsv := hc.saved
  simp only [AllOf, savedSlots] at hsv
  obtain ⟨s208, s216, s224, s232, s240, s248, s256, s264, s272, s280, -⟩ := hsv
  have t : ∀ {o : Nat} {r : XReg}, WordAt m.dmem (frame m0 + BitVec.ofNat 64 o)
      (m0.regs.getXReg r).toBitVec → env.load 0 o 8 = (m0.regs.getXReg r).toBitVec :=
    fun h => load_of_wordAt (r := 0) h
  have hk : b77.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b77Offset) := b77_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk epi hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_⟩
  · have hx30 : st.data.regs.getXReg .X30 = m0.regs.getXReg .X30 :=
      UInt64.toBitVec_inj.mp ((hm'.regs .X30 _ rfl).trans (t s216))
    simp only [PcOk] at hpc
    rw [hpc, retOf, retOf]
    rw [show st.data.regs.X30 = m0.regs.X30 from hx30]
  · intro w hlen hw
    rw [digest_eq g hlen hw]
    generalize keccakF1600 (lastB m0) = F at hl
    have hw4 : ∀ j < 4, WordAt st.data.dmem (m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 * j))
        (Keccak.lane F j).toBitVec := by
      intro j hj
      have hlj : env.load 0 (8 + 8 * j) 8 = (Keccak.lane F j).toBitVec :=
        load_of_wordAt (r := 0) (hl j (by omega))
      interval_cases j <;> exact wordAt_of_eq (wordAt_write hm' hb1 (by decide) rfl) hlj
    exact bytesAt_words fun j hj => match j, hj with
      | 0, _ => hw4 0 (by decide)
      | 1, _ => hw4 1 (by decide)
      | 2, _ => hw4 2 (by decide)
      | 3, _ => hw4 3 (by decide)
  · intro p hp
    refine (KeccakF.same_region hm' hwf hb1 (by decide) p fun h => hp (.inl h)).trans
      (hc.same p fun h => hp (.inr h))
  · refine ⟨fun r hr => ?_, ?_, fun p h => hm'.kept hwf p (hc.kept p h)⟩
    · cases r <;> try exact absurd hr (by decide)
      · exact UInt64.toBitVec_inj.mp ((hm'.regs .X19 _ rfl).trans (t s280))
      · exact UInt64.toBitVec_inj.mp ((hm'.regs .X20 _ rfl).trans (t s272))
      · exact UInt64.toBitVec_inj.mp ((hm'.regs .X21 _ rfl).trans (t s264))
      · exact UInt64.toBitVec_inj.mp ((hm'.regs .X22 _ rfl).trans (t s256))
      · exact UInt64.toBitVec_inj.mp ((hm'.regs .X23 _ rfl).trans (t s248))
      · exact UInt64.toBitVec_inj.mp ((hm'.regs .X24 _ rfl).trans (t s240))
      · exact UInt64.toBitVec_inj.mp ((hm'.regs .X25 _ rfl).trans (t s232))
      · exact UInt64.toBitVec_inj.mp ((hm'.regs .X26 _ rfl).trans (t s224))
      · exact (Match.reg_eq hm hm' rfl rfl).trans hc.x27
      · exact (Match.reg_eq hm hm' rfl rfl).trans hc.x28
      · exact UInt64.toBitVec_inj.mp ((hm'.regs .X29 _ rfl).trans (t s208))
    · apply UInt64.toBitVec_inj.mp
      rw [hm'.sp]
      show frame m0 + BitVec.ofInt 64 288 = _
      simp only [frame]
      exact BitVec.sub_add_cancel _ _

end

end NativeRustcVmArm.WordsHash
