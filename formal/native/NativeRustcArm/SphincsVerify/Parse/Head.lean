module

public import NativeRustcArm.SphincsVerify.Parse.Open

/-!
# The parse's head: from the entry to `b16` (`parseHead_spec : ParseHeadSpec`)

`b11` copies the signature's last words 973 .. 976, stores the key's words at `8208` and the
randomizer at `27808`, and sets up the openings' loop (`AtOpen 0`). Composed with the
prologue (`prologue_spec`), the words' loops (`words_spec`) and the openings' loop (`open_loop`),
the machine reaches `b16` in `AtParse16`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

public section

/-- A register stored whole holds the word it has. -/
theorem bytesAt_reg_word [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o : Nat} {B : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (B, sz)) (hle : o + 8 ≤ sz)
    {x : XReg} (hc : holdsReg S.mem r o x = true) {v : UInt64} (hv : env.regs x = v.toBitVec) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) (wordBytes v) := by
  have := bytesAt_reg hm hb hle hc
  rwa [hv] at this

variable (r : Run) [NativeRustcArm.Host]

/-- **`b11`**: the last words, the key, the randomizer; the openings' loop's registers. -/
theorem b11_spec (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (hA : AtWords r m)
    (hraw : BytesAt m.dmem (r.off 468) (pre10 r.w)) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b12Offset ∧ AtOpen r 0 st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b11Offset⟩ := by
  have hk : b11.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b11Offset) :=
    b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := straight_wf r hpre hA.1
  have hS := hA.1.2.2.2.1
  have hm := straight_match r hpre hA
  refine exec_then hk run_b11 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hF', hout⟩ := frame_block r hpre hA.1 (d := 0) (lo := 8176) (hi := 29264) rfl
    (by decide) (by decide) (by decide) hm hm' hwf (by decide) (by decide)
  have hb0 : (straightEnv r m).regions[0]? = some (r.off 0, 29376) := rfl
  have hmsg := keep r hpre hA.2.1 hout (length_wb r.w 4 4) (by left; decide) (by decide) (by decide)
  have hpre10 := keep r hpre hraw hout (length_pre10 r.w) (by left; decide) (by decide) (by decide)
  have hlast := copy hm' (r := 0) (o := 8176) (r' := 1) (o' := 7784) (n := 32) rfl (by decide)
    (by decide) (length_wb r.w 973 4)
    (bytesAt_wb' r hpre hS (s := 0) (o := 7784) (k := 973) (n := 4) rfl (by decide))
  have hsig : BytesAt st.data.dmem (r.off 468) (sigBytes r.w) := by
    rw [sigBytes_pre10]
    refine BytesAt.append hpre10 ?_
    rw [length_pre10, off_add]
    rw [off_add] at hlast
    exact hlast
  have h21 : (m.regs.getXReg .X21).toBitVec = (r.w 0).toBitVec := hA.2.2.2.2.1
  have h22 : (m.regs.getXReg .X22).toBitVec = (r.w 3).toBitVec := hA.2.2.2.2.2.1
  have h23 : (m.regs.getXReg .X23).toBitVec = (r.w 1).toBitVec := hA.2.2.2.2.2.2.1
  have h24 : (m.regs.getXReg .X24).toBitVec = (r.w 2).toBitVec := hA.2.2.2.2.2.2.2.1
  have hpk : BytesAt st.data.dmem (r.off 8208) (pkBytes r.w) := by
    show BytesAt _ _ (Native.Keccak.wordsBytes [r.w 0, r.w 1, r.w 2, r.w 3])
    refine bytesAt_words _ fun i hi ↦ ?_
    simp only [List.length_cons, List.length_nil] at hi
    rw [off_add]
    interval_cases i
    · have := bytesAt_reg_word hm' hb0 (o := 8208) (x := .X21) (by decide) (by decide) h21
      rwa [off_add] at this
    · have := bytesAt_reg_word hm' hb0 (o := 8216) (x := .X23) (by decide) (by decide) h23
      rwa [off_add] at this
    · have := bytesAt_reg_word hm' hb0 (o := 8224) (x := .X24) (by decide) (by decide) h24
      rwa [off_add] at this
    · have := bytesAt_reg_word hm' hb0 (o := 8232) (x := .X22) (by decide) (by decide) h22
      rwa [off_add] at this
  have hrand : BytesAt st.data.dmem (r.off 27808) r.sig.randomizer := by
    rw [randomizer_eq]
    have := copy hm' (r := 0) (o := 27808) (r' := 0) (o' := 468) (n := 16)
      (bs := slice (pre10 r.w) 0 16) rfl (by decide) (by decide) (by rw [slice, List.length_take, List.length_drop, length_pre10]; rfl)
      (by
        have h := bytesAt_sub hraw (k := 0) (n := 16) (by rw [length_pre10]; decide)
        rw [off_add] at h
        show BytesAt m.dmem (r.off 0 + BitVec.ofNat 64 468) _
        rw [off_add]
        exact h)
    rwa [off_add] at this
  refine .done _ ⟨hpc, hF', ⟨hmsg, hsig, hpk, hrand, fun i hi ↦ by simp at hi⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact (hm'.regs .X19 _ rfl).trans (straight_ptr0 r m 8208)
  · exact (hm'.regs .X20 _ rfl).trans (straight_ptr0 r m 468)
  · exact (hm'.regs .X21 _ rfl).trans (straight_ptr0 r m 26768)
  · exact (hm'.regs .X22 _ rfl).trans (straight_ptr0 r m 8244)
  · exact (hm'.regs .X23 _ rfl).trans (straight_ptr0 r m 564)
  · exact (hm'.regs .X24 _ rfl).trans rfl
  · exact (hm'.regs .X25 _ rfl).trans (straight_ptr0 r m 16400)
  · exact (hm'.regs .X26 _ rfl).trans rfl

end

/-- **The parse's head** (`b0 .. b15`): from the entry, the machine inevitably reaches `b16` with
the message, the raw signature, the key, the randomizer and the FORS openings in the frame. -/
public theorem parseHead_spec [NativeRustcArm.Host] : ParseHeadSpec := by
  intro r hp hc hpre m hm
  subst hm
  refine Eventually.bind (prologue_spec r hp hc hpre) fun st ⟨hpc, hA⟩ ↦ ?_
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.bind (words_spec r hp hpre hA) fun st ⟨hpc, hA, hraw⟩ ↦ ?_
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.bind (b11_spec r hp hpre hA hraw) fun st h ↦ ?_
  refine Eventually.mono (open_loop r hp hc hpre h) fun st ⟨hpc, hF, hM, hR⟩ ↦ ?_
  refine ⟨hpc, hF, hM.1, hM.2.1, hM.2.2.1, ?_, hM.2.2.2.1, hR.1, hR.2.1⟩
  rw [openings_eq]
  exact hM.2.2.2.2

end NativeRustcArm.SphincsVerifyProof.Parse
