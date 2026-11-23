module

public import NativeRustcX64.SphincsVerify.Parse.Open

/-!
# The openings' loop (`b10 .. b13`, x86-64)

Turn `c` (`open_turn`): `b10` and its `memcpy` (`open_b10`), `b11` and its `memcpy`
(`open_b11`), `b12` and its `memcpy`, `b13` (`open_b12`). From `OS 0` at `b10` the loop reaches
`OS 24` at `b14` (`open_loop`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- After `b10` and its `memcpy`: the path at `20556`, the secret at `20716`. -/
def OS1 (r : Run) [Labels] (c : Nat) (m : MachineData) : Prop :=
  OS r c m ∧ BytesAt m.dmem (r.off 20556) (obytes r.w c)

/-- After `b11` and its `memcpy`: opening `c` at `560`. -/
def OS2 (r : Run) [Labels] (c : Nat) (m : MachineData) : Prop :=
  OS r c m ∧ BytesAt m.dmem (r.off 560) (obytes r.w c)

end

public section

variable (r : Run) [Host]

/-- The loop's registers through a call. -/
theorem os_regs {c : Nat} {m₁ m₂ : MachineData} (hS : Saved m₁ m₂)
    (h1 : Run.RegIs m₁ .rbp (r.off 20716)) (h2 : Run.RegIs m₁ .rbx (r.off 20556))
    (h3 : Run.RegIs m₁ .r14 (r.off 560)) (h4 : Run.RegIs m₁ .r12 (r.off 576))
    (h5 : Run.RegIs m₁ .r13 (BitVec.ofNat 64 (176 * (c + 1))))
    (h12 : Run.RegIs m₁ .r15 (Labels.label "memcpy").toBitVec) (hF : r.Frame m₂)
    (hfa : Facts r m₂.dmem (base3 r))
    (hop : BytesAt m₂.dmem (r.off 4104) ((List.range c).map (obytes r.w)).flatten) : OS r c m₂ := by
  unfold Run.RegIs at *
  exact ⟨hF, hfa, hop, (hS.1 .rbp rfl).trans h1, (hS.1 .rbx rfl).trans h2, (hS.1 .r14 rfl).trans h3,
    (hS.1 .r12 rfl).trans h4, (hS.1 .r13 rfl).trans h5, (hS.1 .r15 rfl).trans h12⟩

/-- **`b10` and its `memcpy`**. -/
theorem open_b10 (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {c : Nat} (hc24 : c < 24)
    {m : MachineData} (h : OS r c m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b11Offset ∧ OS1 r c st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b10Offset⟩ := by
  obtain ⟨hF, hfa, hop, hbp, hbx, h14, h15, h13, h12⟩ := h
  have hraw : BytesAt m.dmem (r.off 11404) (sigBytes r.w) := hfa.get (n := 7740) (by simp [base3])
  refine memcpy_block r hp hpre hc b10_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b11Offset) rfl run_b10 (by decide) rfl hF
    ⟨hbp.trans (eval_base r rfl 20716).symm, h15.trans (eval_base r rfl 576).symm, h12, trivial⟩
    ⟨by
      show (reg m .r13).toNat < 4225
      rw [show reg m .r13 = _ from h13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega, trivial⟩
    (a := 20556) (s := 560) (n := 160) (by decide) (by decide) (by decide) fun m₁ hm₁ ↦ ?_
  refine ⟨(hm₁.regs .rdi _ rfl).trans hbx, (hm₁.regs .rsi _ rfl).trans h14, rdx_lit hm₁ rfl
    (by decide), fun m₂ hF₂ hS hB hout hc₁ ↦ .done _ ⟨rfl, ?_⟩⟩
  have hidx : ((Sym.reg .r13).eval (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b11Offset).toBitVec)).toNat =
      176 * (c + 1) := by
    show (reg m .r13).toNat = _
    rw [show reg m .r13 = _ from h13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpath : BytesAt m₁.dmem (r.off 560) (slice (sigBytes r.w) (32 + 176 * c) 160) :=
    copyX hm₁ (r := 0) (o := 560) (r' := 0) (o' := 11260) (I := .reg .r13) (n := 160) rfl
      (by decide) (by decide) (length_slice_sig r.w (by omega)) (by
        rw [hidx, show (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b11Offset).toBitVec).base 0 = r.base from rfl,
          show r.base + BitVec.ofNat 64 (11260 + 176 * (c + 1)) = r.off (11404 + (32 + 176 * c)) by
            simp only [Run.off]; congr 2; omega]
        exact raw_slice r hraw (by omega))
  have hsec : BytesAt m₁.dmem (r.off 20716) (slice (sigBytes r.w) (16 + 176 * c) 16) :=
    copyX hm₁ (r := 0) (o := 20716) (r' := 0) (o' := 11244) (I := .reg .r13) (n := 16) rfl
      (by decide) (by decide) (length_slice_sig r.w (by omega)) (by
        rw [hidx, show (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b11Offset).toBitVec).base 0 = r.base from rfl,
          show r.base + BitVec.ofNat 64 (11244 + 176 * (c + 1)) = r.off (11404 + (16 + 176 * c)) by
            simp only [Run.off]; congr 2; omega]
        exact raw_slice r hraw (by omega))
  have hfa₁ := Facts.of_block r rfl hm₁ hfa (by rw [factsOK_base3]; decide)
  have hop₁ := bytesAt_of_block r rfl hm₁ hop (N := 4224) (by decide)
    (by rw [length_openings r.w (by omega)]; omega) (by decide)
  have hfa₂ := Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hfa₁
    (by rw [factsApart_base3]; decide)
  have hop₂ := r.bytesAt_of_call hpre hc₁ (a := 20556) (n := 160) (by decide) (Nat.zero_le _) hout
    (by rw [length_openings r.w (by omega)]; omega) (by left; rw [length_openings r.w (by omega)]; omega)
    hop₁
  have hsec₂ := r.bytesAt_of_call hpre hc₁ (a := 20556) (n := 160) (by decide) (Nat.zero_le _) hout
    (by rw [length_slice_sig r.w (by omega)]; decide) (by right; decide) hsec
  have hp₂ : BytesAt m₂.dmem (r.off 20556) (slice (sigBytes r.w) (32 + 176 * c) 160) := by
    have hl := length_slice_sig r.w (a := 32 + 176 * c) (n := 160) (by omega)
    rwa [← hl, bytesOf_of_bytesAt hpath] at hB
  refine ⟨os_regs r hS ((hm₁.regs .rbp _ rfl).trans (eval_base r rfl 20716))
    ((hm₁.regs .rbx _ rfl).trans hbx) ((hm₁.regs .r14 _ rfl).trans h14)
    ((hm₁.regs .r12 _ rfl).trans (eval_base r rfl 576)) ((hm₁.regs .r13 _ rfl).trans h13)
    (hm₁.regs .r15 _ rfl) hF₂ hfa₂
    hop₂, ?_⟩
  refine BytesAt.append hp₂ ?_
  rw [length_slice_sig r.w (by omega), off_add]
  exact hsec₂

/-- **`b11` and its `memcpy`**: opening `c` from `20556` to `560`. -/
theorem open_b11 (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {c : Nat} (hc24 : c < 24)
    {m : MachineData} (h : OS1 r c m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b12Offset ∧ OS2 r c st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b11Offset⟩ := by
  obtain ⟨⟨hF, hfa, hop, hbp, hbx, h14, h15, h13, h12⟩, hob⟩ := h
  refine memcpy_block r hp hpre hc b11_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b12Offset) rfl run_b11 (by decide) rfl hF
    ⟨h14.trans (eval_base r rfl 560).symm, hbx.trans (eval_base r rfl 20556).symm, h12, trivial⟩ trivial
    (a := 560) (s := 20556) (n := 176) (by decide) (by decide) (by decide) fun m₁ hm₁ ↦ ?_
  refine ⟨regIs_ptr0 r hm₁ rfl, regIs_ptr0 r hm₁ rfl, rdx_lit hm₁ rfl (by decide),
    fun m₂ hF₂ hS hB hout hc₁ ↦ .done _ ⟨rfl, ?_⟩⟩
  have hob₁ := bytesAt_of_block r rfl hm₁ hob (N := 176) (by decide)
    (by rw [length_obytes r.w hc24]) (by decide)
  have hfa₁ := Facts.of_block r rfl hm₁ hfa (by rw [factsOK_base3]; decide)
  have hop₁ := bytesAt_of_block r rfl hm₁ hop (N := 4224) (by decide)
    (by rw [length_openings r.w (by omega)]; omega) (by decide)
  have hfa₂ := Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hfa₁
    (by rw [factsApart_base3]; decide)
  have hop₂ := r.bytesAt_of_call hpre hc₁ (a := 560) (n := 176) (by decide) (Nat.zero_le _) hout
    (by rw [length_openings r.w (by omega)]; omega) (by right; decide) hop₁
  have hB' : BytesAt m₂.dmem (r.off 560) (obytes r.w c) := by
    rwa [← length_obytes r.w hc24, bytesOf_of_bytesAt hob₁] at hB
  exact ⟨os_regs r hS ((hm₁.regs .rbp _ rfl).trans hbp) ((hm₁.regs .rbx _ rfl).trans
    (eval_base r rfl 20556)) ((hm₁.regs .r14 _ rfl).trans (eval_base r rfl 560))
    ((hm₁.regs .r12 _ rfl).trans h15) ((hm₁.regs .r13 _ rfl).trans h13)
    (hm₁.regs .r15 _ rfl) hF₂ hfa₂ hop₂, hB'⟩

/-- **`b12` and its `memcpy`, then `b13`**: opening `c` to `4104 + 176 c`, the count. -/
theorem open_b12 (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {c : Nat} (hc24 : c < 24)
    {m : MachineData} (h : OS2 r c m) :
    Eventually (step1 Host.exe) (fun st ↦ (st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b14Offset ∧ OS r 24 st.data) ∨
      (c + 1 < 24 ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b10Offset ∧ OS r (c + 1) st.data)) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b12Offset⟩ := by
  obtain ⟨⟨hF, hfa, hop, hbp, hbx, h14, h15, h13, h12⟩, hob⟩ := h
  have h13' : reg m .r13 = BitVec.ofNat 64 (176 * (c + 1)) := h13
  refine memcpy_block r hp hpre hc b12_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b13Offset) rfl run_b12 (by decide) rfl hF
    ⟨h14.trans (eval_base r rfl 560).symm, h12, trivial⟩ trivial
    (a := 4104 + 176 * c) (s := 560) (n := 176) (by omega) (by decide) (by right; omega)
    fun m₁ hm₁ ↦ ?_
  refine ⟨?_, regIs_ptr0 r hm₁ rfl, rdx_lit hm₁ rfl (by decide),
    fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  · refine (hm₁.regs .rdi _ rfl).trans ?_
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [show (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b13Offset).toBitVec).base 0 = r.base from rfl]
    show BitVec.ofNat 64 3928 + (r.base + BitVec.ofInt 64 0 + reg m .r13) = _
    rw [h13']
    simp only [BitVec.ofInt_ofNat]
    bv_lin
  have hob₁ := bytesAt_of_block r rfl hm₁ hob (N := 176) (by decide)
    (by rw [length_obytes r.w hc24]) (by decide)
  have hfa₁ := Facts.of_block r rfl hm₁ hfa (by rw [factsOK_base3]; decide)
  have hop₁ := bytesAt_of_block r rfl hm₁ hop (N := 4224) (by decide)
    (by rw [length_openings r.w (by omega)]; omega) (by decide)
  have hfa₂ := Facts.of_call r hpre hc₁ (by omega) (Nat.zero_le _) hout hfa₁
    (by rw [factsApart_base3]; simp only [factsApart, List.all_cons, List.all_nil]; simp; omega)
  have hop₂ := r.bytesAt_of_call hpre hc₁ (a := 4104 + 176 * c) (n := 176) (by omega)
    (Nat.zero_le _) hout (by rw [length_openings r.w (by omega)]; omega)
    (by left; rw [length_openings r.w (by omega)]) hop₁
  have hB' : BytesAt m₂.dmem (r.off (4104 + 176 * c)) (obytes r.w c) := by
    have e := bytesOf_of_bytesAt hob₁
    rw [length_obytes r.w hc24] at e
    rwa [e] at hB
  have hop' : BytesAt m₂.dmem (r.off 4104) ((List.range (c + 1)).map (obytes r.w)).flatten := by
    rw [List.range_succ, List.map_append, List.flatten_append]
    refine BytesAt.append hop₂ ?_
    rw [length_openings r.w (by omega), off_add]
    simpa using hB'
  have hr : OS r c m₂ := os_regs r hS ((hm₁.regs .rbp _ rfl).trans hbp)
    ((hm₁.regs .rbx _ rfl).trans hbx) ((hm₁.regs .r14 _ rfl).trans (eval_base r rfl 560))
    ((hm₁.regs .r12 _ rfl).trans h15) ((hm₁.regs .r13 _ rfl).trans h13)
    (hm₁.regs .r15 _ rfl) hF₂ hfa₂ hop₂
  have hk : b13.IsInfixAt Host.prog (r.k + NativeRustcX64.Sphincs.SphincsVerify.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk run_b13 (Env.wf_nil m₂) (fun _ h ↦ nomatch h) (match_nil m₂)
    fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m₂.dmem := hm'.dmem_eq (Env.wf_nil _) rfl
  have hreg := keepsRegs_regs (rs := [.rsp, .rbp, .rbx, .r14, .r12, .r15]) (match_nil m₂) hm' (by decide)
  obtain ⟨hF₃, hfa₃, -, hbp₃, hbx₃, h14₃, h15₃, h13₃, h12₃⟩ := hr
  have h13₃' : reg m₂ .r13 = BitVec.ofNat 64 (176 * (c + 1)) := h13₃
  have hv : Sym.eval (Env.ofMachine m₂ [] (fun _ ↦ 0) 0) (.bin .add .W64 (.lit 176) (.reg .r13)) =
      BitVec.ofNat 64 (176 * (c + 2)) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    show BitVec.ofNat 64 176 + reg m₂ .r13 = _
    rw [h13₃']
    bv_lin
  have hOS : OS r (c + 1) st.data := by
    refine ⟨⟨by rw [rspOf, hreg .rsp (by simp)]; exact hF₃.1, hd ▸ hF₃.2.1, hd ▸ hF₃.2.2.1,
      hd ▸ hF₃.2.2.2⟩, hd ▸ hfa₃, hd ▸ hop', ?_, ?_, ?_, ?_, (hm'.regs .r13 _ rfl).trans hv,
      (hreg .r15 (by simp)).trans h12₃⟩
    · unfold Run.RegIs; rw [show reg st.data .rbp = reg m₂ .rbp from hreg .rbp (by simp)]
      exact hbp₃
    · unfold Run.RegIs; rw [show reg st.data .rbx = reg m₂ .rbx from hreg .rbx (by simp)]
      exact hbx₃
    · unfold Run.RegIs; rw [show reg st.data .r14 = reg m₂ .r14 from hreg .r14 (by simp)]
      exact h14₃
    · unfold Run.RegIs; rw [show reg st.data .r12 = reg m₂ .r12 from hreg .r12 (by simp)]
      exact h15₃
  obtain ⟨hne, heq⟩ := pc_cond hpc hv (by omega) (by decide)
  by_cases hc1 : c + 1 < 24
  · rw [hp.label NativeRustcX64.Sphincs.SphincsVerify.label_9_at] at hne
    exact .done _ (Or.inr ⟨hc1, hne (by omega), hOS⟩)
  · obtain rfl : c = 23 := by omega
    exact .done _ (Or.inl ⟨pc_next r (heq rfl) rfl, hOS⟩)

/-- **The openings' loop**. -/
theorem open_loop (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : OS r 0 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b14Offset ∧ OS r 24 st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b10Offset⟩ :=
  count_loop (σ := MachineState) (P := fun c st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b10Offset ∧ OS r c st.data) 24
    (fun c st hc24 ⟨hpc, h⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      refine Eventually.bind (open_b10 r hp hpre hc hc24 h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
      simp only at hpc
      subst hpc
      refine Eventually.bind (open_b11 r hp hpre hc hc24 h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
      simp only at hpc
      subst hpc
      exact open_b12 r hp hpre hc hc24 h) (j := 0) (s := ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b10Offset⟩) (by decide) ⟨rfl, h⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
