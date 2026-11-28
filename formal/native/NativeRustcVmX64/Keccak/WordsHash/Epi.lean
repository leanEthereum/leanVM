module

public import NativeRustcVmX64.Keccak.WordsHash.PadRun

/-!
# `keccak256_words::<hash_words's closure>` (x86-64): the epilogue

`epi_run`: from the epilogue (`EpiAt`, `b83`), the machine returns with the first four lanes of
`keccakF1600 (lastB m0)` at `out` (the slot at 32), which are `hashWords` of the slice's words
(`digest_eq`), the callee-saved registers popped from the frame (`Keccak256WordsHashPost`).
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write load_of_wordAt byteOf_toBitVec
  same_region)
open NativeRustcVm.Keccak (finalState hashWords_eq getD_eq_zero)
open Vm.Keccak256WordsOfHashWords

public section

/-- Words' bytes from their words. -/
theorem bytesAt_words {d : DataMem} {a : BitVec 64} {ws : List UInt64}
    (h : ∀ j < ws.length, WordAt d (a + BitVec.ofNat 64 (8 * j)) (ws.getD j 0).toBitVec) :
    NativeRustcVm.WordsAt d a ws := by
  intro p hp
  rw [NativeRustcVm.length_wordsBytes] at hp
  have := h (p / 8) (by omega) (p % 8) (by simp; omega)
  rw [addr_add, show 8 * (p / 8) + p % 8 = p by omega] at this
  rw [this, List.getElem_map, List.getElem_range, byteOf_toBitVec _ (by omega),
    KeccakF.getElem_eq_getD', show ws.flatMap NativeRustcVm.wordBytes =
      Native.Keccak.wordsBytes ws from rfl, Native.Keccak.Proof.getD_wordsBytes]

/-- The words the slice holds at entry. -/
theorem word_eq {m0 : MachineData} {w : List UInt64} (hlen : w.length = nW m0)
    (hw : NativeRustcVm.WordsAt m0.dmem (ws m0) w) (i : Nat) : word m0 i = w.getD i 0 := by
  have hb : NativeRustcX64.bytesOf m0.dmem (ws m0) (8 * nW m0) = Native.Keccak.wordsBytes w := by
    rw [← hlen, ← Native.Keccak.Proof.length_wordsBytes]
    exact Hasher.bytesOf_of_bytesAt hw
  rw [word, hb, Native.Keccak.Proof.littleEndianLane_wordsBytes]

/-- **The digest is `hashWords`** of the slice's words. -/
theorem digest_eq [Labels] {m0 : MachineData} (g : Geo m0) {w : List UInt64}
    (hlen : w.length = nW m0) (hw : NativeRustcVm.WordsAt m0.dmem (ws m0) w) :
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
theorem epi_run {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    (hmo : Mapped m0.dmem (m0.regs.get64 .rdi) 32) (hno : NoWrap (m0.regs.get64 .rdi) 32)
    (hapo : Apart (m0.regs.get64 .rdi) 32 (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
      (NativeRustcVmX64.keccak256WordsStack + 8))
    {st : MachineState} (h : EpiAt m0 k st) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧
      NativeRustcVmX64.Keccak256WordsHashPost m0 st'.data) st := by
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  subst hpc
  have hstk := g.stk
  obtain ⟨hF, hS, h768, hlt⟩ := stack_facts hstk
  rw [stk_eq] at hapo
  have hapo' := hapo
  have hno' := hno
  unfold Apart at hapo'
  unfold NoWrap at hno'
  have hap1 : Apart (frame m0) 296 (m0.regs.get64 .rdi) 32 := by
    unfold Apart
    omega
  let env := Env.ofMachine m [(frame m0, 296), (m0.regs.get64 .rdi, 32)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩,
      ⟨fun i hi => hc.kept _ (hmo i hi), hno⟩, trivial⟩ (List.pairwise_pair.mpr hap1)
  have hb0 : env.regions[0]? = some (frame m0, 296) := rfl
  have hb1 : env.regions[1]? = some (m0.regs.get64 .rdi, 32) := rfl
  have hslot : ∀ {o : Nat} {w : BitVec 64}, WordAt m.dmem (frame m0 + BitVec.ofNat 64 o) w →
      env.load 0 o 8 = w := fun h => load_of_wordAt (r := 0) h
  have hm : Match env startEpi m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨rsp_eval hc.rsp rfl, trivial⟩ trivial trivial
      ⟨(hslot hc.slots.2.2.1).trans (BitVec.add_zero _).symm, trivial⟩
  -- the return address, as at the entry
  have hread := hm.read hwf (r := 0) (o := 288) (n := 8) rfl (by decide) (by decide)
  have hb288 : env.base 0 + BitVec.ofNat 64 288 = rspOf m0 := frame_add m0
  have hrs : ∀ i < 8, m.dmem.get? (rspOf m0 + BitVec.ofNat 64 i) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 i) := fun i hi => by
    refine hc.same _ fun h => ?_
    rw [stk_eq, inRange_iff (by omega), Hasher.toNat_add_ofNat' (by omega)] at h
    omega
  rw [hb288, loadInt_congr hrs] at hread
  have hsv := hc.saved
  simp only [SlotsAt, savedSlots, AllOf] at hsv
  obtain ⟨s240, s248, s256, s264, s272, s280, -⟩ := hsv
  refine exec_then (b83_in_code.trans hp.1 (List.cons_ne_nil _ _)) epi hwf (fun _ h => by cases h)
    hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact (retOf_of_loadInt hread).symm
  · rw [rsp_of hm' rfl rfl, show BitVec.ofNat 64 296 = BitVec.ofNat 64 288 + 8#64 from rfl,
      ← BitVec.add_assoc, frame_add]
  · intro w hlen hw
    rw [digest_eq g hlen hw]
    generalize keccakF1600 (lastB m0) = F at hl
    have hw4 : ∀ j < 4, WordAt st.data.dmem (m0.regs.get64 .rdi + BitVec.ofNat 64 (8 * j))
        (Keccak.lane F j).toBitVec := by
      intro j hj
      have hlj : env.load 0 (40 + 8 * j) 8 = (Keccak.lane F j).toBitVec :=
        load_of_wordAt (r := 0) (hl j (by omega))
      interval_cases j <;> exact wordAt_of_eq (wordAt_write hm' hb1 (by decide) rfl) hlj
    exact bytesAt_words fun j hj => match j, hj with
      | 0, _ => hw4 0 (by decide)
      | 1, _ => hw4 1 (by decide)
      | 2, _ => hw4 2 (by decide)
      | 3, _ => hw4 3 (by decide)
  · intro p hp
    exact (same_region hm' hwf hb1 (lim := 32) (by decide) (by decide) p
      fun h => hp (.inl h)).trans (hc.same p fun h => hp (.inr h))
  · refine ⟨fun r hr => ?_, fun p h => hm'.kept hwf p (hc.kept p h)⟩
    cases r <;> try exact absurd hr (by decide)
    · exact (hm'.regs .rbx _ rfl).trans (hslot s240)
    · exact (hm'.regs .rbp _ rfl).trans (hslot s280)
    · exact (hm'.regs .r12 _ rfl).trans (hslot s248)
    · exact (hm'.regs .r13 _ rfl).trans (hslot s256)
    · exact (hm'.regs .r14 _ rfl).trans (hslot s264)
    · exact (hm'.regs .r15 _ rfl).trans (hslot s272)

end

end NativeRustcVmX64.WordsHash
