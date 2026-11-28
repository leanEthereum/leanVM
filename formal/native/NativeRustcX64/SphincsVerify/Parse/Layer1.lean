module

public import NativeRustcX64.SphincsVerify.Parse.Layer0

/-!
# The parse, part 7: the second layer (`b23 .. b30`, x86-64)

`b23` loads the second layer's counter bytes into R15D; the loop `b24` copies the layer's chain
values (the raw signature's `5400`) to `20556`; `b25` `memcpy`s them to `560`; `b26` copies the
layer's path (`6424`, 128 bytes) to `1720` and `memcpy`s the chain values to `2056`;
`b27 .. b30` `memcpy` them to `3080`, `19144`, `10376`, `8328`. Result: `LS2` at `b31`
(directive 337).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The facts after the second layer's path. -/
def L1p (r : Run) : List (Nat × Nat × List UInt8) :=
  L1 r ++ [(1720, 128, slice (sigBytes r.w) 6424 128)]

/-- After the second layer: its path at `1720`, its chain values at `8328`. -/
def L2 (r : Run) : List (Nat × Nat × List UInt8) :=
  L1 r ++ [(1720, 128, slice (sigBytes r.w) 6424 128), (8328, 1024, slice (sigBytes r.w) 5400 1024)]

/-- **At `b31`**: two layers parsed; EBP, R15D the first two counters' bytes. -/
def LS2 (r : Run) [Labels] (m : MachineData) : Prop :=
  r.Frame m ∧ Facts r m.dmem (L2 r) ∧ Low4 (reg m .r15) (be32 (r.w 538).toUInt32) ∧
    Low4 (reg m .r12) (be32 (r.w 683).toUInt32) ∧
    Run.RegIs m .rbp (Labels.label "memcpy").toBitVec

end

public section

/-- Decides the second layer's facts' checks. -/
macro "facts_dec2" : tactic => `(tactic| (
  simp only [L2, L1p, L1, L0, base3, List.cons_append, List.nil_append, List.singleton_append]
  facts_dec))

variable (r : Run) [Host]

/-- **`b23 .. b25`**: the second layer's chain values at `560`, R15D its counter's bytes. -/
theorem layer1_a (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS1 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b26Offset ∧ r.Frame st.data ∧
      Facts r st.data.dmem (L1 r) ∧
      BytesAt st.data.dmem (r.off 560) (slice (sigBytes r.w) 5400 1024) ∧
      Run.RegIs st.data .rbx (r.off 1720) ∧ Run.RegIs st.data .r14 (r.off 560) ∧
      Low4 (reg st.data .r15) (be32 (r.w 538).toUInt32) ∧
      Low4 (reg st.data .r12) (be32 (r.w 683).toUInt32) ∧
      Run.RegIs st.data .rbp (Labels.label "memcpy").toBitVec) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b23Offset⟩ := by
  obtain ⟨hF, hL, hbx, hbp⟩ := h
  -- `b23`: the counter's bytes
  have hk : b23.IsInfixAt Host.prog (r.k + NativeRustcX64.Sphincs.SphincsVerify.b23Offset) := b23_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) 0
  have hm₀ : Match (r.env m (fun _ ↦ 0) 0) (fS []) m :=
    r.match_frame hpre hF (known := []) trivial trivial trivial trivial
  refine exec_then hk run_b23 hwf (fun _ h ↦ nomatch h) hm₀ fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  have hreg := keepsRegs_regs (rs := [.rsp, .rbx, .r15, .rbp, .r13, .r14]) hm₀ hm' (by decide)
  have hF₁ : r.Frame st.data := frame_of_block r hpre hF rfl rfl hm' hwf rfl (by decide)
  have h15 : Low4 (reg st.data .r12) (be32 (r.w 683).toUInt32) :=
    (low4_counter_load r (hL.get (raw_mem1 r)) (l := 1) (by decide) rfl).of_eq
      (hm'.regs .r12 _ rfl)
  have hax : Run.RegIs st.data .rax 0 := (hm'.regs .rax _ rfl).trans rfl
  have hpc' : st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b24Offset := pc_next r hpc rfl
  obtain ⟨m₁, pc⟩ := st
  simp only at hpc'
  subst hpc'
  simp only at hF₁ hd hreg h15 hax
  -- `b24`: the chain values to `20556`
  refine Eventually.bind (span_loop r hp hpre b24_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b25Offset) rfl (hp.label NativeRustcX64.Sphincs.SphincsVerify.label_13_at)
    .rax 16804 (by decide) (by decide) run_b24 rfl (by decide) (by decide)
    (rs := [.rsp, .rbx, .r15, .rbp, .r13, .r14, .r12]) (by decide) (by simp) (L := L1 r)
    (by facts_dec2) (raw_mem1 r) (P := fun m ↦ Run.RegIs m .rbx (r.off 1720) ∧
      Low4 (reg m .r15) (be32 (r.w 538).toUInt32) ∧ Low4 (reg m .r12) (be32 (r.w 683).toUInt32))
    (fun m m' he ⟨h1, h2, h3⟩ ↦ ⟨(he .rbx (by simp)).trans h1, h2.of_eq (he .r15 (by simp)),
      h3.of_eq (he .r12 (by simp))⟩)
    ⟨hF₁, hd ▸ hL, hax, (hreg .rbx (by simp)).trans hbx, hbp.of_eq (hreg .r15 (by simp)), h15⟩)
    fun ⟨m₂, pc⟩ ⟨hpc, hF₂, hL₂, hcv, hbx₂, hbp₂, h15₂⟩ ↦ ?_
  simp only at hpc
  subst hpc
  -- `b25`: to `560`
  refine memcpy_pure r hp hpre hc b25_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b26Offset) rfl run_b25 (by decide) rfl hF₂ trivial
    hL₂ (by facts_dec2) (a := 560) (s := 20556) (n := 1024) (by facts_dec2) hcv
    (length_slice_sig r.w (by decide)) (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r hm₃ rfl, regIs_ptr0 r hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS hL₄ hB ↦ .done _ ⟨rfl, hF₄, hL₄, hB,
        regIs_saved hS rfl ((hm₃.regs .rbx _ rfl).trans hbx₂),
        regIs_saved hS rfl (regIs_ptr0 r hm₃ (y := .r14) rfl),
        low4_saved hS rfl (hbp₂.of_eq (hm₃.regs .r15 _ rfl)),
        low4_saved hS rfl (h15₂.of_eq (hm₃.regs .r12 _ rfl)),
        regIs_saved hS rfl (hm₃.regs .rbp _ rfl)⟩⟩

/-- **`b26 .. b30`**: the second layer's path at `1720`, its chain values at `8328`. -/
theorem layer1_b (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem (L1 r) ∧
      BytesAt m.dmem (r.off 560) (slice (sigBytes r.w) 5400 1024) ∧
      Run.RegIs m .rbx (r.off 1720) ∧ Run.RegIs m .r14 (r.off 560) ∧
      Low4 (reg m .r15) (be32 (r.w 538).toUInt32) ∧ Low4 (reg m .r12) (be32 (r.w 683).toUInt32) ∧
      Run.RegIs m .rbp (Labels.label "memcpy").toBitVec) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b31Offset ∧ LS2 r st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b26Offset⟩ := by
  obtain ⟨hF, hL, hcv, hbx, h14, hbp, h15, h12⟩ := h
  have hl : (slice (sigBytes r.w) 5400 1024).length = 1024 := length_slice_sig r.w (by decide)
  -- `b26`: the path to `1720`, the chain values to `2056`
  refine memcpy_block r hp hpre hc b26_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b27Offset) rfl run_b26 (by decide) rfl hF
    ⟨hbx.trans (eval_base r rfl 1720).symm, h14.trans (eval_base r rfl 560).symm, h12, trivial⟩ trivial
    (a := 2056) (s := 560) (n := 1024) (by decide) (by decide) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r hm₁ rfl, regIs_ptr0 r hm₁ rfl, rdx_lit hm₁ rfl (by decide),
      fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  have hpath : BytesAt m₁.dmem (r.off 1720) (slice (sigBytes r.w) 6424 128) :=
    copy hm₁ (r := 0) (o := 1720) (r' := 0) (o' := 17828) (n := 128) rfl (by decide) (by decide)
      (length_slice_sig r.w (by decide)) (raw_slice r (hL.get (raw_mem1 r)) (k := 6424) (n := 128)
        (by decide))
  have hL₁ := Facts.of_block r rfl hm₁ hL (by facts_dec2)
  have hcv₁ := bytesAt_of_block r rfl hm₁ hcv (N := 1024) (by decide) hl.le (by decide)
  have hL₂ : Facts r m₂.dmem (L1p r) := by
    rw [L1p, facts_append]
    exact ⟨Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hL₁ (by facts_dec2),
      ⟨length_slice_sig r.w (by decide), r.bytesAt_of_call hpre hc₁ (by decide) (Nat.zero_le _) hout
        (by rw [length_slice_sig r.w (by decide)]; decide)
        (by left; rw [length_slice_sig r.w (by decide)]; decide) hpath⟩, trivial⟩
  have hB' : BytesAt m₂.dmem (r.off 2056) (slice (sigBytes r.w) 5400 1024) := by
    rwa [← hl, bytesOf_of_bytesAt hcv₁] at hB
  have hbp₂ := low4_saved hS rfl (hbp.of_eq (hm₁.regs .r15 _ rfl))
  have h15₂ := low4_saved hS rfl (h15.of_eq (hm₁.regs .r12 _ rfl))
  have hbx₂ := regIs_saved hS rfl (regIs_ptr0 r hm₁ (y := .rbx) rfl)
  have h12₂ := regIs_saved hS rfl (hm₁.regs .rbp _ rfl : Run.RegIs m₁ .rbp (Labels.label "memcpy").toBitVec)
  -- `b27`: to `3080`
  refine memcpy_pure r hp hpre hc b27_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b28Offset) rfl run_b27 (by decide) rfl hF₂
    ⟨hbx₂.trans (eval_base r rfl 2056).symm, h12₂, trivial⟩ hL₂ (by facts_dec2) (a := 3080) (s := 2056)
    (n := 1024) (by facts_dec2) hB' hl (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r hm₃ rfl, regIs_ptr0 r hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS₄ hL₄ hB₄ ↦ ?_⟩
  have hbp₄ := low4_saved hS₄ rfl (hbp₂.of_eq (hm₃.regs .r15 _ rfl))
  have h15₄ := low4_saved hS₄ rfl (h15₂.of_eq (hm₃.regs .r12 _ rfl))
  have h14₄ := regIs_saved hS₄ rfl (regIs_ptr0 r hm₃ (y := .r14) rfl)
  have h12₄ := regIs_saved hS₄ rfl (hm₃.regs .rbp _ rfl : Run.RegIs m₃ .rbp (Labels.label "memcpy").toBitVec)
  -- `b28`: to `19144`
  refine memcpy_pure r hp hpre hc b28_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b29Offset) rfl run_b28 (by decide) rfl hF₄
    ⟨h14₄.trans (eval_base r rfl 3080).symm, h12₄, trivial⟩ hL₄ (by facts_dec2) (a := 19144) (s := 3080)
    (n := 1024) (by facts_dec2) hB₄ hl (by decide) (by decide) (by decide) (by decide)
    fun m₅ hm₅ ↦ ⟨regIs_ptr0 r hm₅ rfl, regIs_ptr0 r hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS₆ hL₆ hB₆ ↦ ?_⟩
  have hbp₆ := low4_saved hS₆ rfl (hbp₄.of_eq (hm₅.regs .r15 _ rfl))
  have h15₆ := low4_saved hS₆ rfl (h15₄.of_eq (hm₅.regs .r12 _ rfl))
  have hbx₆ := regIs_saved hS₆ rfl (regIs_ptr0 r hm₅ (y := .rbx) rfl)
  have h12₆ := regIs_saved hS₆ rfl (hm₅.regs .rbp _ rfl : Run.RegIs m₅ .rbp (Labels.label "memcpy").toBitVec)
  -- `b29`: to `10376`
  refine memcpy_pure r hp hpre hc b29_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b30Offset) rfl run_b29 (by decide) rfl hF₆
    ⟨hbx₆.trans (eval_base r rfl 19144).symm, h12₆, trivial⟩ hL₆ (by facts_dec2) (a := 10376) (s := 19144)
    (n := 1024) (by facts_dec2) hB₆ hl (by decide) (by decide) (by decide) (by decide)
    fun m₇ hm₇ ↦ ⟨regIs_ptr0 r hm₇ rfl, regIs_ptr0 r hm₇ rfl, rdx_lit hm₇ rfl (by decide),
      fun m₈ hF₈ hS₈ hL₈ hB₈ ↦ ?_⟩
  have hbp₈ := low4_saved hS₈ rfl (hbp₆.of_eq (hm₇.regs .r15 _ rfl))
  have h15₈ := low4_saved hS₈ rfl (h15₆.of_eq (hm₇.regs .r12 _ rfl))
  have h14₈ := regIs_saved hS₈ rfl (regIs_ptr0 r hm₇ (y := .r14) rfl)
  have h12₈ := regIs_saved hS₈ rfl (hm₇.regs .rbp _ rfl : Run.RegIs m₇ .rbp (Labels.label "memcpy").toBitVec)
  -- `b30`: to `8328`
  refine memcpy_pure r hp hpre hc b30_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b31Offset) rfl run_b30 (by decide) rfl hF₈
    ⟨h14₈.trans (eval_base r rfl 10376).symm, h12₈, trivial⟩ hL₈ (by facts_dec2) (a := 8328)
    (s := 10376) (n := 1024) (by facts_dec2) hB₈ hl (by decide) (by decide) (by decide) (by decide)
    fun m₉ hm₉ ↦ ⟨regIs_ptr0 r hm₉ rfl, regIs_ptr0 r hm₉ rfl, rdx_lit hm₉ rfl (by decide),
      fun m₁₀ hF₁₀ hS₁₀ hL₁₀ hB₁₀ ↦ .done _ ⟨rfl, hF₁₀, ?_,
        low4_saved hS₁₀ rfl (hbp₈.of_eq (hm₉.regs .r15 _ rfl)),
        low4_saved hS₁₀ rfl (h15₈.of_eq (hm₉.regs .r12 _ rfl)),
        regIs_saved hS₁₀ rfl (hm₉.regs .rbp _ rfl)⟩⟩
  rw [L2, ← List.singleton_append, ← List.append_assoc, facts_append, ← L1p]
  exact ⟨hL₁₀, ⟨hl, hB₁₀⟩, trivial⟩

/-- **The second layer**: from `LS1` at `b23` to `LS2` at `b31`. -/
theorem layer1_spec (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS1 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b31Offset ∧ LS2 r st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b23Offset⟩ :=
  Eventually.bind (layer1_a r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ by
    simp only at hpc
    subst hpc
    exact layer1_b r hp hpre hc h

end

end NativeRustcX64.SphincsVerifyProof.Parse
