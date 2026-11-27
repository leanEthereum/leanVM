module

public import NativeRustcX64.SphincsVerify.Parse.Call
public import NativeRustcX64.SphincsVerify.Parse.OpenExec

/-!
# The parse, part 1: the prologue (`b0`) and the openings' state (`OS`, x86-64)

`b0` pushes the callee-saved registers, probes and allocates the 21624-byte frame, keeps `sigPtr`
in RBX, stores `msgPtr` at `8`, copies the 32-byte `pk` to `112`, and sets up the FORS openings
loop's registers (`R15 = 576`, `R12 = 176`, `R14 = 12780`, `R13 = 560`, `RBP = memcpy`).
Result: `OS 0` at `b1` (`prologue_spec`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- What the parse keeps from `b0` on: the message pointer at `8`, the public key at `112`. -/
def base3 (r : Run) : List (Nat × Nat × List UInt8) :=
  [(8, 8, wordBytes (UInt64.ofBitVec r.msgPtr)), (112, 32, r.pkB)]

/-- **The openings' loop at turn `c`**: the first `c` openings at `4072`; RBX `sigPtr`,
R15 `576`, R14 `12780`, R13 `560`, R12 `176 (c + 1)`, RBP `memcpy`. -/
def OS (r : Run) [Labels] (c : Nat) (m : MachineData) : Prop :=
  r.Frame m ∧ Facts r m.dmem (base3 r) ∧
    BytesAt m.dmem (r.off 4072) ((List.range c).map (obytesB r.sigB)).flatten ∧
    Run.RegIs m .rbx r.sigPtr ∧ Run.RegIs m .r15 (r.off 576) ∧
    Run.RegIs m .r14 (r.off 12780) ∧ Run.RegIs m .r13 (r.off 560) ∧
    Run.RegIs m .r12 (BitVec.ofNat 64 (176 * (c + 1))) ∧
    Run.RegIs m .rbp (Labels.label "memcpy").toBitVec

end

public section

theorem factsOK_base3 (r : Run) (S : SState) :
    factsOK S (base3 r) = factsOK S [(8, 8, []), (112, 32, [])] := by
  simp only [factsOK, base3, List.all_cons, List.all_nil]

theorem factsApart_base3 (r : Run) (a n : Nat) :
    factsApart (base3 r) a n = factsApart [(8, 8, []), (112, 32, [])] a n := by
  simp only [factsApart, base3, List.all_cons, List.all_nil]

variable (r : Run) [ElfHost]

/-- **`b0`**: prologue, `msgPtr` at `8`, `pk` at `112`, openings loop registers -> `OS 0` at `b1`. -/
theorem prologue_spec (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b1Offset ∧ OS r 0 st.data)
      ⟨r.m0, r.pc NativeRustcX64.Sphincs.SphincsVerify.b0Offset⟩ := by
  have hk : b0.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + NativeRustcX64.Sphincs.SphincsVerify.b0Offset) :=
    b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := wfPk r hpre (fun _ ↦ 0) 0
  have hS0 : SameOutside r.m0.dmem r.m0.dmem r.StackArea := fun _ _ ↦ rfl
  have hm : Match (envExt r.m0 (regsPk r) (fun _ ↦ 0) 0) entryS r.m0 := by
    apply Match.withKnownBytes
    · apply Match.withKnownBytes
      · exact match_ofMachine_ro ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
          ⟨by
            show rspOf r.m0 = r.base + BitVec.ofInt 64 ((21624 : Nat) : Int)
            rw [BitVec.ofInt_natCast]
            simp [Run.base, frameSize],
          by
            show reg r.m0 .rdi = r.pkPtr + BitVec.ofInt 64 0
            simp [Run.pkPtr], trivial⟩
          trivial trivial
          ⟨r.alias8, by
            show r.base + BitVec.ofInt 64 (-16) = (r.base - 16#64) + BitVec.ofInt 64 0
            rw [show BitVec.ofInt 64 (-16) = -16#64 by decide, show BitVec.ofInt 64 0 = 0#64 by decide]
            bv_omega,
          by simp [Sym.eval, Env.base, regsPk, Run.frameRegs, gotAddr],
          by simp [Sym.eval, Env.base, regsPk, Run.frameRegs, gotAddr], trivial⟩
      · intro i hi
        simpa [Sym.eval, Env.base, regsPk, Run.frameRegs] using
          r.got_byte hpre hS0 (by simp : "memcpy" ∈ _) hi
    · intro i hi
      simpa [Sym.eval, Env.base, regsPk, Run.frameRegs] using
        r.got_byte hpre hS0 (by simp : "memset" ∈ _) hi
  refine exec_then_elf_ro hk run_b0 hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ .done _ ?_
  have h0 : (envExt r.m0 (regsPk r) (fun _ ↦ 0) 0).regions[0]? = some (r.base, 21632) := rfl
  have hF : r.Frame st.data := by
    refine ⟨?_, ?_, (hm'.sameOutside_ro hwf).mono (written_stack r hpre h0 rfl (by decide)),
      hm'.kept_ro hwf⟩
    · rw [rspOf, hm'.regs .rsp _ rfl]
      simp [Sym.eval, Env.base]
    · refine bytesAt_words _ fun i hi ↦ ?_
      simp only [List.length_map, List.length_cons, List.length_nil] at hi
      rw [off_add, Run.off]
      interval_cases i
      · exact bytesAt_reg hm' h0 (o := 21576) (x := .rbx) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 21584) (x := .r12) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 21592) (x := .r13) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 21600) (x := .r14) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 21608) (x := .r15) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 21616) (x := .rbp) (by decide) (by decide) rfl
  have hmp : BytesAt st.data.dmem (r.off 8) (wordBytes (UInt64.ofBitVec r.msgPtr)) :=
    bytesAt_reg hm' h0 (o := 8) (x := .rsi) (by decide) (by decide) rfl
  have hpk : BytesAt st.data.dmem (r.off 112) r.pkB :=
    copy hm' (r := 0) (o := 112) (r' := 4) (o' := 0) (n := 32) h0 (by decide) (by decide) r.hpk
      (by simpa [Env.base, regsPk, Run.frameRegs] using (r.pk_pre hpre).1)
  refine ⟨pc_next r hpc rfl, hF,
    ⟨⟨NativeRustc.length_wordBytes _, hmp⟩, ⟨r.hpk, hpk⟩, trivial⟩,
    fun i hi ↦ by simp at hi,
    (hm'.regs .rbx _ rfl).trans rfl,
    regIs_ptr0 r h0 hm' rfl,
    regIs_ptr0 r h0 hm' rfl,
    regIs_ptr0 r h0 hm' rfl,
    (hm'.regs .r12 _ rfl).trans rfl,
    hm'.regs .rbp _ rfl⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
