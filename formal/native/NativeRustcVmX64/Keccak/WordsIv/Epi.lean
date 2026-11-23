module

public import NativeRustcVmX64.Keccak.WordsIv.Pad
public import NativeRustcVmX64.Keccak.WordsHash.Epi

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` (x86-64): the epilogue

`epi_run`: from the epilogue (`EpiAt`, `b111`), the machine returns with the first four lanes of
`keccakF1600 (lastI m0)` at `out` (the slot at 32), which are `fiatShamirIv` of the bytecode
(`digest_eq`), the callee-saved registers popped from the frame (`Keccak256WordsIvPost`).
-/

namespace NativeRustcVmX64.WordsIv

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write load_of_wordAt same_region)
open NativeRustcVm.Keccak (finalState fiatShamirIv_eq keccak256Words ivWord)
open NativeRustcVmX64.WordsHash (frame Ctx Lanes stack_facts stk_eq frame_mapped frame_noWrap
  frame_add rsp_of rsp_eval bytesAt_words)
open Vm.Keccak256WordsOfFiatShamirIv

public section

/-- **The digest is `fiatShamirIv`** of the bytecode. -/
theorem digest_eq [Labels] {m0 : MachineData} (g : Geo m0) {w : List UInt64}
    (hlen : w.length = nW m0) (hw : NativeRustcVm.WordsAt m0.dmem (bc m0) w) :
    (NativeVm.Model.fiatShamirIv w.toArray).toList =
      [Keccak.lane (keccakF1600 (lastI m0)) 0, Keccak.lane (keccakF1600 (lastI m0)) 1,
        Keccak.lane (keccakF1600 (lastI m0)) 2, Keccak.lane (keccakF1600 (lastI m0)) 3] := by
  have hb := eq_bcw g hlen hw
  have hf : (fun i => if i < w.length + 2 then ivWord w i else 0) = wv m0 := by
    funext i
    rw [wv, g.cnt, ← hlen, hb]
  have hF : keccakF1600 (lastI m0) =
      finalState (fun i => if i < w.length + 2 then ivWord w i else 0) (9 + 8 * w.length) := by
    rw [hf, hlen, ← g.len]
    rfl
  rw [fiatShamirIv_eq, keccak256Words, hF]
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
      NativeRustcVmX64.Keccak256WordsIvPost m0 st'.data) st := by
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
  simp only [NativeRustcVmX64.WordsHash.SlotsAt, NativeRustcVmX64.WordsHash.savedSlots, AllOf]
    at hsv
  obtain ⟨s240, s248, s256, s264, s272, s280, -⟩ := hsv
  refine exec_then (ic hp b111_in_code (List.cons_ne_nil _ _)) epi hwf (fun _ h => by cases h)
    hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact (retOf_of_loadInt hread).symm
  · rw [rsp_of hm' rfl rfl, show BitVec.ofNat 64 296 = BitVec.ofNat 64 288 + 8#64 from rfl,
      ← BitVec.add_assoc, frame_add]
  · intro w hlen hw
    rw [digest_eq g hlen hw]
    generalize keccakF1600 (lastI m0) = F at hl
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

end NativeRustcVmX64.WordsIv
