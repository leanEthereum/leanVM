module

public import NativeRustcX64.SphincsVerify.Parse.Env
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify

/-!
# The parse, part 1: the prologue and the raw signature's `memset` (`b0`, `b1`, x86-64)

`b0` pushes RBP, R15, R14, R13, R12, RBX, probes and allocates the frame, keeps the context in
RBX, the key's words 0 .. 3 in R14, R15, R13, RBP, stores the message's words 4 .. 7 at `1600`,
and calls `memset` on the raw signature's 7740 bytes at `12416`; `b1` is an alignment. Result:
`AtW` at `b2` (directive 41).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

@[expose] public section

/-- At the entry: region 0 the frame (RSP its top `29384`), region 1 the slots below it, region 2
the input (RDI 1024 below it), then the loader's memcpy and memset slots. -/
def entryS : SState :=
  (init [29392, 16, 7816, 8, 8] [(.rsp, .ptr 0 29384), (.rdi, .ptr 2 (-1024))] [] []
    (Run.frameAliases ++ [(.gotSlot "memset", 4, 0)])).withKnownBytes 4 0 8 (.label "memset")

/-- The key's words in registers: R14, R15, R13, RBP the words 0 .. 3. -/
def KeyRegs (r : Run) (m : MachineData) : Prop :=
  Run.RegIs m .r14 (r.w 0).toBitVec ∧ Run.RegIs m .r15 (r.w 1).toBitVec ∧
    Run.RegIs m .r13 (r.w 2).toBitVec ∧ Run.RegIs m .rbp (r.w 3).toBitVec

/-- **At `b2`**: the frame, the message at `1600`; RBX the context, the key in registers, R12
`0`. -/
def AtW (r : Run) (m : MachineData) : Prop :=
  r.Frame m ∧ Facts r m.dmem [(1600, 32, r.msg)] ∧ Run.RegIs m .rbx (ctx r) ∧ KeyRegs r m ∧
    Run.RegIs m .r12 0

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (init [])

public section

theorem input_sub (r : Run) : r.input + BitVec.ofInt 64 (-1024) = ctx r := by
  rw [show (-1024 : Int) = -((1024 : Nat) : Int) from rfl, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  simp only [Run.input, ctx]
  bv_omega

theorem length_msg (r : Run) : r.msg.length = 32 := length_wb r.w 4 4

variable (r : Run) [Host]

omit [Host] in
theorem keyRegs_of_saved {m m' : MachineData} (hS : Saved m m') (h : KeyRegs r m) :
    KeyRegs r m' := by
  obtain ⟨h14, h15, h13, hbp⟩ := h
  unfold Run.RegIs at *
  exact ⟨(hS.1 .r14 rfl).trans h14, (hS.1 .r15 rfl).trans h15, (hS.1 .r13 rfl).trans h13,
    (hS.1 .rbp rfl).trans hbp⟩

/-- **`b0` and the raw signature's `memset`, then `b1`**. -/
theorem prologue_spec (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b2Offset ∧ AtW r st.data) ⟨r.m0, r.pc NativeRustcX64.Sphincs.SphincsVerify.b0Offset⟩ := by
  have hk : b0.IsInfixAt Host.prog (r.k + NativeRustcX64.Sphincs.SphincsVerify.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := wf3 r hpre (m := r.m0) (fun _ h ↦ h) (fun _ _ ↦ rfl) (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b1Offset).toBitVec
  have hS0 : SameOutside r.m0.dmem r.m0.dmem r.StackArea := fun _ _ ↦ rfl
  have hm : Match (Env.ofMachine r.m0 (regs3 r) (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b1Offset).toBitVec) entryS r.m0 := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
        ⟨by
          show rspOf r.m0 = r.base + BitVec.ofInt 64 ((29384 : Nat) : Int)
          rw [BitVec.ofInt_natCast]
          simp [Run.base, frameSize],
        by
          show reg r.m0 .rdi = r.input + BitVec.ofInt 64 (-1024)
          rw [input_sub], trivial⟩
        trivial trivial
        ⟨r.alias8, by
          show r.base + BitVec.ofInt 64 (-16) = (r.base - 16#64) + BitVec.ofInt 64 0
          rw [show BitVec.ofInt 64 (-16) = -16#64 by decide, show BitVec.ofInt 64 0 = 0#64 by decide]
          bv_omega, by simp [Sym.eval, Env.base, regs3, gotAddr], trivial⟩
    · intro i hi
      simpa [Sym.eval, Env.base, regs3] using r.got_byte hpre hS0 (by simp : "memset" ∈ _) hi
  refine exec_then hk run_b0 hwf (fun _ _ ↦ rfl) hm fun st hm' hpc ↦ ?_
  have h0 : (regs3 r)[0]? = some (r.base, 29392) := rfl
  have hcall : r.AtCall st.data := by
    refine ⟨?_, ?_, (hm'.sameOutside hwf).mono (written_stack r hpre h0 rfl (by decide)),
      hm'.kept hwf⟩
    · rw [rspOf, hm'.regs .rsp _ rfl, eval_ptr h0, show BitVec.ofInt 64 (-8) = -8#64 by decide]
      bv_omega
    · refine bytesAt_words _ fun i hi ↦ ?_
      simp only [List.length_map, List.length_cons, List.length_nil] at hi
      rw [off_add, Run.off]
      interval_cases i
      · exact bytesAt_reg hm' h0 (o := 29336) (x := .rbx) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 29344) (x := .r12) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 29352) (x := .r13) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 29360) (x := .r14) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 29368) (x := .r15) (by decide) (by decide) rfl
      · exact bytesAt_reg hm' h0 (o := 29376) (x := .rbp) (by decide) (by decide) rfl
  have hmsg : Facts r st.data.dmem [(1600, 32, r.msg)] := by
    refine ⟨⟨length_msg r, ?_⟩, trivial⟩
    exact copy hm' (r := 0) (o := 1600) (r' := 2) (o' := 32) (n := 32) h0 (by decide) (by decide)
      (length_msg r) (input_words r hpre hS0 (s := 4) (n := 4) (by decide))
  have hE : ∀ o k, o = 8 * k → k < 977 →
      (Env.ofMachine r.m0 (regs3 r) (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b1Offset).toBitVec).load 2 o 8 = (r.w k).toBitVec :=
    fun o k ho hk ↦ load_word (input_word r hpre hS0 ho hk)
  have hkey : KeyRegs r st.data :=
    ⟨(hm'.regs .r14 _ rfl).trans (hE 0 0 rfl (by decide)),
      (hm'.regs .r15 _ rfl).trans (hE 8 1 rfl (by decide)),
      (hm'.regs .r13 _ rfl).trans (hE 16 2 rfl (by decide)),
      (hm'.regs .rbp _ rfl).trans (hE 24 3 rfl (by decide))⟩
  have hrbx : Run.RegIs st.data .rbx (ctx r) :=
    (hm'.regs .rbx _ rfl).trans ((eval_ptr rfl _).trans (input_sub r))
  have h12 : Run.RegIs st.data .rdi (r.off 12416) := (hm'.regs .rdi _ rfl).trans (eval_base r h0 _)
  have h2 : (reg st.data .rdx).toNat = 7740 := by
    rw [show reg st.data .rdx = _ from hm'.regs .rdx _ rfl]
    rfl
  refine call_then hpc hc.2.1 (r.memset_pre hpre hcall h12 h2 (by decide))
    fun st2 hpc2 hsp2 hQ ↦ ?_
  obtain ⟨-, hout, hS⟩ := r.memset_out h12 h2 hQ
  have hF2 := r.frame_of_call hpre hcall hS hsp2 (by decide) (Nat.zero_le _) hout
  have hmsg2 := Facts.of_call r hpre hcall (by decide) (Nat.zero_le _) hout hmsg rfl
  have hk1 : b1.IsInfixAt Host.prog (r.k + NativeRustcX64.Sphincs.SphincsVerify.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk1 run_b1 (Env.wf_nil st2.data) (fun _ h ↦ nomatch h) hpc2 (match_nil _)
    fun st3 hm3 hpc3 ↦ .done _ ⟨hpc3, ?_⟩
  have hd : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  have hreg := keepsRegs_regs (rs := [.rsp, .rbx, .r12, .r13, .r14, .r15, .rbp]) (match_nil _) hm3
    (by decide)
  have hr12 : Run.RegIs st.data .r12 0 := (hm'.regs .r12 _ rfl).trans rfl
  refine ⟨?_, hd ▸ hmsg2, ?_, ?_, ?_⟩
  · refine ⟨by rw [rspOf, hreg .rsp (by simp)]; exact hF2.1, hd ▸ hF2.2.1, hd ▸ hF2.2.2.1,
      hd ▸ hF2.2.2.2⟩
  · unfold Run.RegIs
    rw [show reg st3.data .rbx = reg st2.data .rbx from hreg .rbx (by simp),
      show reg st2.data .rbx = reg st.data .rbx from hS.1 .rbx rfl]
    exact hrbx
  · have hk2 := keyRegs_of_saved r hS hkey
    unfold KeyRegs Run.RegIs at *
    rw [show reg st3.data .r14 = reg st2.data .r14 from hreg .r14 (by simp),
      show reg st3.data .r15 = reg st2.data .r15 from hreg .r15 (by simp),
      show reg st3.data .r13 = reg st2.data .r13 from hreg .r13 (by simp),
      show reg st3.data .rbp = reg st2.data .rbp from hreg .rbp (by simp)]
    exact hk2
  · unfold Run.RegIs
    rw [show reg st3.data .r12 = reg st2.data .r12 from hreg .r12 (by simp),
      show reg st2.data .r12 = reg st.data .r12 from hS.1 .r12 rfl]
    exact hr12

end

end NativeRustcX64.SphincsVerifyProof.Parse
