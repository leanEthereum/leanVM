module

public import NativeRustcX64.SphincsVerify.Parse.WordsC
public import NativeRustcX64.SphincsVerify.Parse.Call
public import NativeRustcX64.SphincsVerify.Parse.OpenExec

/-!
# The parse, part 5: the key and the FORS openings (`b9 .. b13`, x86-64)

`b9` stores the key's words at `112` and sets up the openings' loop; turn `c` of the loop
(`open_turn`): `b10` copies opening `c`'s path (the raw signature's `32 + 176 c`) to `560` and
its secret (`16 + 176 c`) to `20716`, `memcpy`s the path to `20556`; `b11` `memcpy`s the 176
bytes at `20556` to `560`; `b12` `memcpy`s them to `4104 + 176 c`; `b13` counts (R13
`176 (c + 1)`). Result: `OS 24` at `b14` (directive 178): the 24 openings in rustc's layout at
`4104` (`open_spec`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- What the parse keeps from `b9` on: the message, the raw signature, the key. -/
def base3 (r : Run) : List (Nat × Nat × List UInt8) :=
  [(2008, 32, r.msg), (11404, 7740, sigBytes r.w), (112, 32, pkBytes r.w)]

/-- **The openings' loop at turn `c`**: the first `c` openings at `4104`; RBP, RBX, R14, R12 the
frame's `20716`, `20556`, `560`, `576`; R13 `176 (c + 1)`, R15 the memcpy entry. -/
def OS (r : Run) [Labels] (c : Nat) (m : MachineData) : Prop :=
  r.Frame m ∧ Facts r m.dmem (base3 r) ∧
    BytesAt m.dmem (r.off 4104) ((List.range c).map (obytes r.w)).flatten ∧
    Run.RegIs m .rbp (r.off 20716) ∧ Run.RegIs m .rbx (r.off 20556) ∧
    Run.RegIs m .r14 (r.off 560) ∧ Run.RegIs m .r12 (r.off 576) ∧
    Run.RegIs m .r13 (BitVec.ofNat 64 (176 * (c + 1))) ∧
    Run.RegIs m .r15 (Labels.label "memcpy").toBitVec

end

public section

theorem length_pk (w : Nat → UInt64) : (pkBytes w).length = 32 := length_wb w 0 4

/-- What the kept facts' check is, their bytes aside. -/
theorem factsOK_base3 (r : Run) (S : SState) :
    factsOK S (base3 r) = factsOK S [(2008, 32, []), (11404, 7740, []), (112, 32, [])] := by
  simp only [factsOK, base3, List.all_cons, List.all_nil]

theorem factsApart_base3 (r : Run) (a n : Nat) :
    factsApart (base3 r) a n = factsApart [(2008, 32, []), (11404, 7740, []), (112, 32, [])] a n := by
  simp only [factsApart, base3, List.all_cons, List.all_nil]

variable (r : Run) [Host]

omit [Host] in
/-- The raw signature's bytes `k .. k + n` at the frame's `11404 + k`. -/
theorem raw_slice {d : DataMem} (h : BytesAt d (r.off 11404) (sigBytes r.w)) {k n : Nat}
    (hk : k + n ≤ 7740) : BytesAt d (r.off (11404 + k)) (slice (sigBytes r.w) k n) := by
  have := bytesAt_sub h (k := k) (n := n) (by rw [length_sigBytes]; exact hk)
  rwa [off_add] at this

/-- **`b9`**: the key at `112`, the openings' loop's registers. -/
theorem b9_spec (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData}
    (h : WS r (sigBytes r.w) m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b10Offset ∧ OS r 0 st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b9Offset⟩ := by
  have hk : b9.IsInfixAt Host.prog (r.k + NativeRustcX64.Sphincs.SphincsVerify.b9Offset) := b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre h.1.2.2.2 (fun _ ↦ 0) 0
  have hm : Match (r.env m (fun _ ↦ 0) 0) (fS []) m :=
    r.match_frame hpre h.1 (known := []) trivial trivial trivial trivial
  refine exec_then hk run_b9 hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ ?_
  obtain ⟨hF, hmsg, hraw, -, h14, h15, h13, hbp⟩ := h
  have hF' := frame_of_block r hpre hF rfl rfl hm' hwf rfl (by decide)
  have hpk : BytesAt st.data.dmem (r.off 112) (pkBytes r.w) := by
    show BytesAt _ _ (Native.Keccak.wordsBytes [r.w 0, r.w 1, r.w 2, r.w 3])
    refine bytesAt_words _ fun i hi ↦ ?_
    simp only [List.length_cons, List.length_nil] at hi
    rw [off_add]
    interval_cases i
    · exact bytesAt_reg hm' (r := 0) (sz := 29408) (o := 112) (x := .r14) rfl (by decide) (by decide) h14
    · exact bytesAt_reg hm' (r := 0) (sz := 29408) (o := 120) (x := .r12) rfl (by decide) (by decide) h15
    · exact bytesAt_reg hm' (r := 0) (sz := 29408) (o := 128) (x := .r13) rfl (by decide) (by decide) h13
    · exact bytesAt_reg hm' (r := 0) (sz := 29408) (o := 136) (x := .rbp) rfl (by decide) (by decide) hbp
  refine .done _ ⟨hpc, hF', ⟨⟨length_msg r, bytesAt_of_block r rfl hm' hmsg (N := 32) (by decide)
      (by rw [length_msg]) (by decide)⟩,
    ⟨length_sigBytes r.w, bytesAt_of_block r rfl hm' hraw (N := 7740) (by decide)
      (by rw [length_sigBytes]) (by decide)⟩, ⟨length_pk r.w, hpk⟩, trivial⟩,
    fun i hi ↦ by simp at hi, regIs_ptr0 r hm' rfl, regIs_ptr0 r hm' rfl, regIs_ptr0 r hm' rfl,
    regIs_ptr0 r hm' rfl, (hm'.regs .r13 _ rfl).trans rfl, hm'.regs .r15 _ rfl⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
