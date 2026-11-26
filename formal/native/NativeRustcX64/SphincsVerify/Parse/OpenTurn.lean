module

public import NativeRustcX64.SphincsVerify.Parse.Prologue

/-!
# The openings' loop (`b1 .. b4`, x86-64)

Turn `c`: `b1` copies opening `c`'s secret (`16 + 176 c`) to `12940` and its path (`32 + 176 c`)
to `560` and `memcpy`s the path to `12780` (`open_b1`); `b2` `memcpy`s the 176 bytes at `12780`
to `560` (`open_b2`); `b3` `memcpy`s them to `4072 + 176 c` and `b4` counts `r12 += 176` up to
`4400` (`open_b3`). Result: `OS 24` at `b5` (`open_loop`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- After `b1` and its `memcpy`: the path at `12780`, the secret at `12940`. -/
def OS1 (r : Run) [Labels] (c : Nat) (m : MachineData) : Prop :=
  OS r c m ∧ BytesAt m.dmem (r.off 12780) (obytesB r.sigB c)

/-- After `b2` and its `memcpy`: opening `c` at `560`. -/
def OS2 (r : Run) [Labels] (c : Nat) (m : MachineData) : Prop :=
  OS r c m ∧ BytesAt m.dmem (r.off 560) (obytesB r.sigB c)

end

public section

variable (r : Run) [Host]

/-- The loop's registers through a call. -/
theorem os_regs {c : Nat} {m₁ m₂ : MachineData} (hS : Saved m₁ m₂)
    (hbx : Run.RegIs m₁ .rbx r.sigPtr) (h15 : Run.RegIs m₁ .r15 (r.off 576))
    (h14 : Run.RegIs m₁ .r14 (r.off 12780)) (h13 : Run.RegIs m₁ .r13 (r.off 560))
    (h12 : Run.RegIs m₁ .r12 (BitVec.ofNat 64 (176 * (c + 1))))
    (hbp : Run.RegIs m₁ .rbp (Labels.label "memcpy").toBitVec) (hF : r.Frame m₂)
    (hfa : Facts r m₂.dmem (base3 r))
    (hop : BytesAt m₂.dmem (r.off 4072) ((List.range c).map (obytesB r.sigB)).flatten) : OS r c m₂ := by
  unfold Run.RegIs at *
  exact ⟨hF, hfa, hop, (hS.1 .rbx rfl).trans hbx, (hS.1 .r15 rfl).trans h15,
    (hS.1 .r14 rfl).trans h14, (hS.1 .r13 rfl).trans h13,
    (hS.1 .r12 rfl).trans h12, (hS.1 .rbp rfl).trans hbp⟩

/-- **`b1` and its `memcpy`**. -/
theorem open_b1 (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {c : Nat} (hc24 : c < 24)
    {m : MachineData} (h : OS r c m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b2Offset ∧ OS1 r c st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b1Offset⟩ := by
  obtain ⟨hF, hfa, hop, hbx, h15, h14, h13, h12, hbp⟩ := h
  have hwf := wfOpen r hpre hF.2.2.2 hF.2.2.1 hc24 (fun _ ↦ 0) (r.pc b2Offset).toBitVec
  have hk' : b1.IsInfixAt Host.prog (r.k + b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hm : Match (Env.ofMachine m (regsOpen r c) (fun _ ↦ 0) (r.pc b2Offset).toBitVec) openS m := by
    apply Match.withKnownBytes
    · apply Match.withKnownBytes
      · apply match_ofMachine
        · exact ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
        · exact ⟨by show rspOf m = r.base + BitVec.ofInt 64 0; simpa only [BitVec.ofInt_ofNat, BitVec.add_zero] using hF.1,
            h15.trans (eval_base r rfl 576).symm, h14.trans (eval_base r rfl 12780).symm,
            h13.trans (eval_base r rfl 560).symm, hbp, trivial⟩
        · exact trivial
        · exact trivial
        · refine ⟨r.alias8, ?_, ?_, ?_, ?_, trivial⟩
          · change r.base + BitVec.ofInt 64 (-16) = (r.base - 16#64) + BitVec.ofInt 64 0
            rw [show BitVec.ofInt 64 (-16) = -16#64 by decide, show BitVec.ofInt 64 0 = 0#64 by decide]
            bv_omega
          · simp [Sym.eval, Env.base, regsOpen, Run.frameRegs, gotAddr]
          · simp [Sym.eval, Env.base, regsOpen, Run.frameRegs, gotAddr]
          · sym_simp
            simp only [Env.ofMachine_regs, Env.base, regsOpen, Run.frameRegs]
            show reg m .rbx + reg m .r12 = r.sigPtr + BitVec.ofNat 64 (16 + 176 * c) + BitVec.ofInt 64 160
            rw [show reg m .rbx = r.sigPtr from hbx, show reg m .r12 = BitVec.ofNat 64 (176 * (c + 1)) from h12]
            rw [show BitVec.ofInt 64 160 = BitVec.ofNat 64 160 from rfl]
            bv_lin
      · intro i hi
        simpa [Sym.eval, Env.base, regsOpen, Run.frameRegs] using
          r.got_byte hpre hF.2.2.1 (by simp : "memcpy" ∈ _) hi
    · intro i hi
      simpa [Sym.eval, Env.base, regsOpen, Run.frameRegs] using
        r.got_byte hpre hF.2.2.1 (by simp : "memset" ∈ _) hi
  refine exec_then hk' run_b1 hwf (fun _ _ ↦ by rw [← b1_next, Nat.add_assoc]; rfl) hm fun st hm₁ hpc ↦ ?_
  have hc₁ := atCall_of_block r hpre hF rfl rfl hm₁ hwf rfl (by decide)
  have h0 : Run.RegIs st.data .rdi (r.off 12780) := regIs_ptr0 r rfl hm₁ rfl
  have h1 : Run.RegIs st.data .rsi (r.off 560) := regIs_ptr0 r rfl hm₁ rfl
  have h2 : (reg st.data .rdx).toNat = 160 := rdx_lit hm₁ rfl (by decide)
  refine call_then hpc hc.1 (r.memcpy_pre hpre hc₁ h0 h1 h2 (by decide) (by decide) (by decide))
    fun st₂ hpc₂ hsp₂ hQ ↦ ?_
  obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 hQ
  obtain ⟨m₂, pc⟩ := st₂
  simp only at hpc₂
  subst hpc₂
  have hpc_eq : Host.addrOf (r.k + b1Offset + b1.length) = r.pc b2Offset := by
    rw [Run.pc, Nat.add_assoc, b1_next]
  rw [hpc_eq]
  have hF₂ := r.frame_of_call hpre hc₁ hS hsp₂ (by decide) (Nat.zero_le _) hout
  have hpath : BytesAt st.data.dmem (r.off 560) (slice r.sigB (32 + 176 * c) 160) :=
    copy hm₁ (r := 0) (o := 560) (r' := 4) (o' := 16) (n := 160) rfl (by decide) (by decide)
      (length_slice (by rw [r.hsig]; omega)) (by
        show BytesAt m.dmem (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c) + BitVec.ofNat 64 16) _
        rw [addr_add, show 16 + 176 * c + 16 = 32 + 176 * c by omega]
        exact sig_slice r hpre hF.2.2.1 (by omega))
  have hsec : BytesAt st.data.dmem (r.off 12940) (slice r.sigB (16 + 176 * c) 16) :=
    copy hm₁ (r := 0) (o := 12940) (r' := 4) (o' := 0) (n := 16) rfl (by decide) (by decide)
      (length_slice (by rw [r.hsig]; omega)) (by
        show BytesAt m.dmem (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c) + BitVec.ofNat 64 0) _
        rw [addr_add, Nat.add_zero]
        exact sig_slice r hpre hF.2.2.1 (by omega))
  have hfa₁ := Facts.of_block r rfl hm₁ hfa (by rw [factsOK_base3]; decide)
  have hop₁ := bytesAt_of_block r rfl hm₁ hop (N := 4224) (by decide)
    (by rw [length_openingsB r.hsig (by omega)]; omega) (by decide)
  have hfa₂ := Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hfa₁
    (by rw [factsApart_base3]; decide)
  have hop₂ := r.bytesAt_of_call hpre hc₁ (a := 12780) (n := 160) (by decide) (Nat.zero_le _) hout
    (by rw [length_openingsB r.hsig (by omega)]; omega)
    (by left; rw [length_openingsB r.hsig (by omega)]; omega) hop₁
  have hsec₂ := r.bytesAt_of_call hpre hc₁ (a := 12780) (n := 160) (by decide) (Nat.zero_le _) hout
    (by rw [length_slice (by rw [r.hsig]; omega)]; decide) (by right; decide) hsec
  have hp₂ : BytesAt m₂.dmem (r.off 12780) (slice r.sigB (32 + 176 * c) 160) := by
    have hl : (slice r.sigB (32 + 176 * c) 160).length = 160 := length_slice (by rw [r.hsig]; omega)
    rwa [← hl, bytesOf_of_bytesAt hpath] at hB
  refine .done _ ⟨rfl, os_regs r hS ((hm₁.regs .rbx _ rfl).trans hbx)
    (regIs_ptr0 r rfl hm₁ rfl) (regIs_ptr0 r rfl hm₁ rfl) (regIs_ptr0 r rfl hm₁ rfl)
    ((hm₁.regs .r12 _ rfl).trans h12) (hm₁.regs .rbp _ rfl) hF₂ hfa₂ hop₂, ?_⟩
  refine BytesAt.append hp₂ ?_
  rw [length_slice (by rw [r.hsig]; omega), off_add]
  exact hsec₂

/-- **`b2` and its `memcpy`**: opening `c` from `12780` to `560`. -/
theorem open_b2 (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {c : Nat} (hc24 : c < 24)
    {m : MachineData} (h : OS1 r c m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b3Offset ∧ OS2 r c st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b2Offset⟩ := by
  obtain ⟨⟨hF, hfa, hop, hbx, h15, h14, h13, h12, hbp⟩, hob⟩ := h
  refine memcpy_block r hp hpre hc b2_in_code (jn := b3Offset) rfl run_b2 (by decide) rfl hF
    ⟨h13.trans (eval_base r rfl 560).symm, h14.trans (eval_base r rfl 12780).symm, hbp, trivial⟩ trivial
    (a := 560) (s := 12780) (n := 176) (by decide) (by decide) (by decide) fun m₁ hm₁ ↦ ?_
  refine ⟨regIs_ptr0 r rfl hm₁ rfl, regIs_ptr0 r rfl hm₁ rfl, rdx_lit hm₁ rfl (by decide),
    fun m₂ hF₂ hS hB hout hc₁ ↦ .done _ ⟨rfl, ?_⟩⟩
  have hob₁ := bytesAt_of_block r rfl hm₁ hob (N := 176) (by decide)
    (by rw [length_obytesB r.hsig hc24]) (by decide)
  have hfa₁ := Facts.of_block r rfl hm₁ hfa (by rw [factsOK_base3]; decide)
  have hop₁ := bytesAt_of_block r rfl hm₁ hop (N := 4224) (by decide)
    (by rw [length_openingsB r.hsig (by omega)]; omega) (by decide)
  have hfa₂ := Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hfa₁
    (by rw [factsApart_base3]; decide)
  have hop₂ := r.bytesAt_of_call hpre hc₁ (a := 560) (n := 176) (by decide) (Nat.zero_le _) hout
    (by rw [length_openingsB r.hsig (by omega)]; omega) (by right; decide) hop₁
  have hB' : BytesAt m₂.dmem (r.off 560) (obytesB r.sigB c) := by
    rwa [← length_obytesB r.hsig hc24, bytesOf_of_bytesAt hob₁] at hB
  exact ⟨os_regs r hS ((hm₁.regs .rbx _ rfl).trans hbx) ((hm₁.regs .r15 _ rfl).trans h15)
    (regIs_ptr0 r rfl hm₁ rfl) (regIs_ptr0 r rfl hm₁ rfl) ((hm₁.regs .r12 _ rfl).trans h12)
    (hm₁.regs .rbp _ rfl) hF₂ hfa₂ hop₂, hB'⟩

/-- **`b3` and its `memcpy`, then `b4`**: opening `c` to `4072 + 176 c`, the count. -/
theorem open_b3 (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {c : Nat} (hc24 : c < 24)
    {m : MachineData} (h : OS2 r c m) :
    Eventually (step1 Host.exe) (fun st ↦ (st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b5Offset ∧ OS r 24 st.data) ∨
      (c + 1 < 24 ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b1Offset ∧ OS r (c + 1) st.data))
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b3Offset⟩ := by
  obtain ⟨⟨hF, hfa, hop, hbx, h15, h14, h13, h12, hbp⟩, hob⟩ := h
  have h12' : reg m .r12 = BitVec.ofNat 64 (176 * (c + 1)) := h12
  refine memcpy_block r hp hpre hc b3_in_code (jn := b4Offset) rfl run_b3 (by decide) rfl hF
    ⟨h13.trans (eval_base r rfl 560).symm, hbp, trivial⟩ trivial
    (a := 4072 + 176 * c) (s := 560) (n := 176) (by omega) (by decide) (by right; omega)
    fun m₁ hm₁ ↦ ?_
  refine ⟨?_, regIs_ptr0 r rfl hm₁ rfl, rdx_lit hm₁ rfl (by decide),
    fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  · refine (hm₁.regs .rdi _ rfl).trans ?_
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [show (r.env m (fun _ ↦ 0) (r.pc b4Offset).toBitVec).base 0 = r.base from rfl]
    show BitVec.ofNat 64 3896 + (r.base + BitVec.ofInt 64 0 + reg m .r12) = _
    rw [h12']
    simp only [BitVec.ofInt_ofNat]
    bv_lin
  have hob₁ := bytesAt_of_block r rfl hm₁ hob (N := 176) (by decide)
    (by rw [length_obytesB r.hsig hc24]) (by decide)
  have hfa₁ := Facts.of_block r rfl hm₁ hfa (by rw [factsOK_base3]; decide)
  have hop₁ := bytesAt_of_block r rfl hm₁ hop (N := 4224) (by decide)
    (by rw [length_openingsB r.hsig (by omega)]; omega) (by decide)
  have hfa₂ := Facts.of_call r hpre hc₁ (by omega) (Nat.zero_le _) hout hfa₁
    (by rw [factsApart_base3]; simp only [factsApart, List.all_cons, List.all_nil]; simp; omega)
  have hop₂ := r.bytesAt_of_call hpre hc₁ (a := 4072 + 176 * c) (n := 176) (by omega)
    (Nat.zero_le _) hout (by rw [length_openingsB r.hsig (by omega)]; omega)
    (by left; rw [length_openingsB r.hsig (by omega)]) hop₁
  have hB' : BytesAt m₂.dmem (r.off (4072 + 176 * c)) (obytesB r.sigB c) := by
    have e := bytesOf_of_bytesAt hob₁
    rw [length_obytesB r.hsig hc24] at e
    rwa [e] at hB
  have hop' : BytesAt m₂.dmem (r.off 4072) ((List.range (c + 1)).map (obytesB r.sigB)).flatten := by
    rw [List.range_succ, List.map_append, List.flatten_append]
    refine BytesAt.append hop₂ ?_
    rw [length_openingsB r.hsig (by omega), off_add]
    simpa using hB'
  have hr : OS r c m₂ := os_regs r hS ((hm₁.regs .rbx _ rfl).trans hbx)
    ((hm₁.regs .r15 _ rfl).trans h15) ((hm₁.regs .r14 _ rfl).trans h14)
    (regIs_ptr0 r rfl hm₁ rfl) ((hm₁.regs .r12 _ rfl).trans h12)
    (hm₁.regs .rbp _ rfl) hF₂ hfa₂ hop₂
  have hk : b4.IsInfixAt Host.prog (r.k + b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk run_b4 (Env.wf_nil m₂) (fun _ h ↦ nomatch h) (match_nil m₂)
    fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m₂.dmem := hm'.dmem_eq (Env.wf_nil _) rfl
  have hreg := keepsRegs_regs (rs := [.rsp, .rbx, .r15, .r14, .r13, .rbp]) (match_nil m₂) hm' (by decide)
  obtain ⟨hF₃, hfa₃, -, hbx₃, h15₃, h14₃, h13₃, h12₃, hbp₃⟩ := hr
  have h12₃' : reg m₂ .r12 = BitVec.ofNat 64 (176 * (c + 1)) := h12₃
  have hv : Sym.eval (Env.ofMachine m₂ [] (fun _ ↦ 0) 0) (.bin .add .W64 (.lit 176) (.reg .r12)) =
      BitVec.ofNat 64 (176 * (c + 2)) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    show BitVec.ofNat 64 176 + reg m₂ .r12 = _
    rw [h12₃']
    bv_lin
  have hOS : OS r (c + 1) st.data := by
    refine ⟨⟨by rw [rspOf, hreg .rsp (by simp)]; exact hF₃.1, hd ▸ hF₃.2.1, hd ▸ hF₃.2.2.1,
      hd ▸ hF₃.2.2.2⟩, hd ▸ hfa₃, hd ▸ hop',
      (hreg .rbx (by simp)).trans hbx₃, (hreg .r15 (by simp)).trans h15₃,
      (hreg .r14 (by simp)).trans h14₃, (hreg .r13 (by simp)).trans h13₃,
      (hm'.regs .r12 _ rfl).trans hv, (hreg .rbp (by simp)).trans hbp₃⟩
  obtain ⟨hne, heq⟩ := pc_cond hpc hv (by omega) (by decide)
  by_cases hc1 : c + 1 < 24
  · rw [hp.label NativeRustcX64.Sphincs.SphincsVerify.label_1_at] at hne
    exact .done _ (Or.inr ⟨hc1, hne (by omega), hOS⟩)
  · obtain rfl : c = 23 := by omega
    exact .done _ (Or.inl ⟨pc_next r (heq rfl) rfl, hOS⟩)

/-- **The openings' loop**: from `OS 0` at `b1` to `OS 24` at `b5`. -/
theorem open_loop (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : OS r 0 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b5Offset ∧ OS r 24 st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b1Offset⟩ :=
  count_loop (σ := MachineState) (P := fun c st ↦ st.pc = r.pc b1Offset ∧ OS r c st.data) 24
    (fun c st hc24 ⟨hpc, h⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      refine Eventually.bind (open_b1 r hp hpre hc hc24 h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
      simp only at hpc
      subst hpc
      refine Eventually.bind (open_b2 r hp hpre hc hc24 h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
      simp only at hpc
      subst hpc
      exact open_b3 r hp hpre hc hc24 h) (j := 0) (s := ⟨m, r.pc b1Offset⟩) (by decide) ⟨rfl, h⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
