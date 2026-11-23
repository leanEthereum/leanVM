module

public import NativeRustcX64.SphincsVerify.Parse.Layer1

/-!
# The parse, part 8: the third layer (`b31 .. b37`, x86-64)

`b31` loads the third layer's counter bytes into R13D; the loop `b32` copies the layer's chain
values (the raw signature's `6556`) to `20540`; `b33` `memcpy`s them to `576`; `b34` copies the
layer's path (`7580`, 160 bytes) to `1888`, swaps the three counters' bytes, and `memcpy`s the
chain values to `2048`; `b35 .. b37` `memcpy` them to `9344`, `3072`, `11392` (`b36` moves the
first two counters to R15D, R14D). Result: `LS3` at `b38` (directive 422).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The facts after the third layer's path. -/
def L2p (r : Run) : List (Nat × Nat × List UInt8) :=
  L2 r ++ [(1888, 160, slice (sigBytes r.w) 7580 160)]

/-- After the third layer: its path at `1888`, its chain values at `11392`. -/
def L3 (r : Run) : List (Nat × Nat × List UInt8) :=
  L2 r ++ [(1888, 160, slice (sigBytes r.w) 7580 160), (11392, 1024, slice (sigBytes r.w) 6556 1024)]

/-- **At `b38`**: three layers parsed; RBX the frame's `11392`, R15D, R14D, R13D the counters'
bytes little-endian. -/
def LS3 (r : Run) [Labels] (m : MachineData) : Prop :=
  r.Frame m ∧ Facts r m.dmem (L3 r) ∧ Run.RegIs m .rbx (r.off 11392) ∧
    Low4 (reg m .r15) (be32 (r.w 538).toUInt32).reverse ∧
    Low4 (reg m .r14) (be32 (r.w 683).toUInt32).reverse ∧
    Low4 (reg m .r13) (be32 (r.w 828).toUInt32).reverse ∧
    Run.RegIs m .r12 (Labels.label "memcpy").toBitVec

end

public section

/-- Decides the third layer's facts' checks. -/
macro "facts_dec3" : tactic => `(tactic| (
  simp only [L3, L2p, L2, L1, L0, base3, List.cons_append, List.nil_append, List.singleton_append]
  facts_dec))

theorem raw_mem2 (r : Run) : (12416, 7740, sigBytes r.w) ∈ L2 r := by simp [L2, L1, L0, base3]

variable (r : Run) [Host]

/-- **`b31 .. b33`**: the third layer's chain values at `576`, R13D its counter's bytes. -/
theorem layer2_a (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS2 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b34Offset ∧ r.Frame st.data ∧
      Facts r st.data.dmem (L2 r) ∧
      BytesAt st.data.dmem (r.off 576) (slice (sigBytes r.w) 6556 1024) ∧
      Run.RegIs st.data .rbx (r.off 576) ∧
      Low4 (reg st.data .rbp) (be32 (r.w 538).toUInt32) ∧
      Low4 (reg st.data .r15) (be32 (r.w 683).toUInt32) ∧
      Low4 (reg st.data .r13) (be32 (r.w 828).toUInt32) ∧
      Run.RegIs st.data .r12 (Labels.label "memcpy").toBitVec) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b31Offset⟩ := by
  obtain ⟨hF, hL, hbp, h15, h12⟩ := h
  -- `b31`: the counter's bytes
  have hk : b31.IsInfixAt Host.prog (r.k + NativeRustcX64.Sphincs.SphincsVerify.b31Offset) := b31_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) 0
  have hm₀ : Match (r.env m (fun _ ↦ 0) 0) (fS []) m :=
    r.match_frame hpre hF (known := []) trivial trivial trivial trivial
  refine exec_then hk run_b31 hwf (fun _ h ↦ nomatch h) hm₀ fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  have hreg := keepsRegs_regs (rs := [.rsp, .rbx, .rbp, .r12, .r14, .r15]) hm₀ hm' (by decide)
  have hF₁ : r.Frame st.data := frame_of_block r hpre hF rfl rfl hm' hwf rfl (by decide)
  have h13 : Low4 (reg st.data .r13) (be32 (r.w 828).toUInt32) :=
    (low4_counter_load r (hL.get (raw_mem2 r)) (l := 2) (by decide) rfl).of_eq
      (hm'.regs .r13 _ rfl)
  have hax : Run.RegIs st.data .rax 0 := (hm'.regs .rax _ rfl).trans rfl
  have hpc' : st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b32Offset := pc_next r hpc rfl
  obtain ⟨m₁, pc⟩ := st
  simp only at hpc'
  subst hpc'
  simp only at hF₁ hd hreg h13 hax
  -- `b32`: the chain values to `20540`
  refine Eventually.bind (span_loop r hp hpre b32_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b33Offset) rfl (hp.label NativeRustcX64.Sphincs.SphincsVerify.label_15_at)
    .rax 18972 (by decide) (by decide) run_b32 rfl (by decide) (by decide)
    (rs := [.rsp, .rbx, .rbp, .r12, .r13, .r14, .r15]) (by decide) (by simp) (L := L2 r)
    (by facts_dec3) (raw_mem2 r) (P := fun m ↦ Low4 (reg m .rbp) (be32 (r.w 538).toUInt32) ∧
      Low4 (reg m .r15) (be32 (r.w 683).toUInt32) ∧ Low4 (reg m .r13) (be32 (r.w 828).toUInt32) ∧
      Run.RegIs m .r12 (Labels.label "memcpy").toBitVec)
    (fun m m' he ⟨h1, h2, h3, h4⟩ ↦ ⟨h1.of_eq (he .rbp (by simp)), h2.of_eq (he .r15 (by simp)),
      h3.of_eq (he .r13 (by simp)), (he .r12 (by simp)).trans h4⟩)
    ⟨hF₁, hd ▸ hL, hax, hbp.of_eq (hreg .rbp (by simp)), h15.of_eq (hreg .r15 (by simp)), h13,
      (hreg .r12 (by simp)).trans h12⟩)
    fun ⟨m₂, pc⟩ ⟨hpc, hF₂, hL₂, hcv, hbp₂, h15₂, h13₂, h12₂⟩ ↦ ?_
  simp only at hpc
  subst hpc
  -- `b33`: to `576`
  refine memcpy_pure r hp hpre hc b33_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b34Offset) rfl run_b33 (by decide) rfl hF₂ ⟨h12₂, trivial⟩
    hL₂ (by facts_dec3) (a := 576) (s := 20540) (n := 1024) (by facts_dec3) hcv
    (length_slice_sig r.w (by decide)) (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r hm₃ rfl, regIs_ptr0 r hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS hL₄ hB ↦ .done _ ⟨rfl, hF₄, hL₄, hB,
        regIs_saved hS rfl (regIs_ptr0 r hm₃ (y := .rbx) rfl),
        low4_saved hS rfl (hbp₂.of_eq (hm₃.regs .rbp _ rfl)),
        low4_saved hS rfl (h15₂.of_eq (hm₃.regs .r15 _ rfl)),
        low4_saved hS rfl (h13₂.of_eq (hm₃.regs .r13 _ rfl)),
        regIs_saved hS rfl (hm₃.regs .r12 _ rfl)⟩⟩

/-- **`b34 .. b37`**: the third layer's path at `1888`, its chain values at `11392`, the counters
swapped. -/
theorem layer2_b (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem (L2 r) ∧
      BytesAt m.dmem (r.off 576) (slice (sigBytes r.w) 6556 1024) ∧
      Run.RegIs m .rbx (r.off 576) ∧ Low4 (reg m .rbp) (be32 (r.w 538).toUInt32) ∧
      Low4 (reg m .r15) (be32 (r.w 683).toUInt32) ∧ Low4 (reg m .r13) (be32 (r.w 828).toUInt32) ∧
      Run.RegIs m .r12 (Labels.label "memcpy").toBitVec) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b38Offset ∧ LS3 r st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b34Offset⟩ := by
  obtain ⟨hF, hL, hcv, hbx, hbp, h15, h13, h12⟩ := h
  have hl : (slice (sigBytes r.w) 6556 1024).length = 1024 := length_slice_sig r.w (by decide)
  -- `b34`: the path to `1888`, the counters swapped, the chain values to `2048`
  refine memcpy_block r hp hpre hc b34_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b35Offset) rfl run_b34 (by decide) rfl hF
    ⟨hbx.trans (eval_base r rfl 576).symm, h12, trivial⟩ trivial
    (a := 2048) (s := 576) (n := 1024) (by decide) (by decide) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r hm₁ rfl, regIs_ptr0 r hm₁ rfl, rdx_lit hm₁ rfl (by decide),
      fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  have hpath : BytesAt m₁.dmem (r.off 1888) (slice (sigBytes r.w) 7580 160) :=
    copy hm₁ (r := 0) (o := 1888) (r' := 0) (o' := 19996) (n := 160) rfl (by decide) (by decide)
      (length_slice_sig r.w (by decide)) (raw_slice r (hL.get (raw_mem2 r)) (k := 7580) (n := 160)
        (by decide))
  have hL₁ := Facts.of_block r rfl hm₁ hL (by facts_dec3)
  have hcv₁ := bytesAt_of_block r rfl hm₁ hcv (N := 1024) (by decide) hl.le (by decide)
  have hL₂ : Facts r m₂.dmem (L2p r) := by
    rw [L2p, facts_append]
    exact ⟨Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hL₁ (by facts_dec3),
      ⟨length_slice_sig r.w (by decide), r.bytesAt_of_call hpre hc₁ (by decide) (Nat.zero_le _) hout
        (by rw [length_slice_sig r.w (by decide)]; decide)
        (by left; rw [length_slice_sig r.w (by decide)]) hpath⟩, trivial⟩
  have hB' : BytesAt m₂.dmem (r.off 2048) (slice (sigBytes r.w) 6556 1024) := by
    rwa [← hl, bytesOf_of_bytesAt hcv₁] at hB
  have hbp₂ := low4_saved hS rfl (hbp.bswap.of_eq (hm₁.regs .rbp _ rfl))
  have h15₂ := low4_saved hS rfl (h15.bswap.of_eq (hm₁.regs .r15 _ rfl))
  have h13₂ := low4_saved hS rfl (h13.bswap.of_eq (hm₁.regs .r13 _ rfl))
  have h14₂ := regIs_saved hS rfl (regIs_ptr0 r hm₁ (y := .r14) rfl)
  have h12₂ := regIs_saved hS rfl (hm₁.regs .r12 _ rfl : Run.RegIs m₁ .r12 (Labels.label "memcpy").toBitVec)
  -- `b35`: to `9344`
  refine memcpy_pure r hp hpre hc b35_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b36Offset) rfl run_b35 (by decide) rfl hF₂
    ⟨h14₂.trans (eval_base r rfl 2048).symm, h12₂, trivial⟩ hL₂ (by facts_dec3) (a := 9344) (s := 2048)
    (n := 1024) (by facts_dec3) hB' hl (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r hm₃ rfl, regIs_ptr0 r hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS₄ hL₄ hB₄ ↦ ?_⟩
  have hbp₄ := low4_saved hS₄ rfl (hbp₂.of_eq (hm₃.regs .rbp _ rfl))
  have h15₄ := low4_saved hS₄ rfl (h15₂.of_eq (hm₃.regs .r15 _ rfl))
  have h13₄ := low4_saved hS₄ rfl (h13₂.of_eq (hm₃.regs .r13 _ rfl))
  have hbx₄ := regIs_saved hS₄ rfl (regIs_ptr0 r hm₃ (y := .rbx) rfl)
  have h12₄ := regIs_saved hS₄ rfl (hm₃.regs .r12 _ rfl : Run.RegIs m₃ .r12 (Labels.label "memcpy").toBitVec)
  -- `b36`: to `3072`, the first two counters moved
  refine memcpy_pure r hp hpre hc b36_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b37Offset) rfl run_b36 (by decide) rfl hF₄
    ⟨hbx₄.trans (eval_base r rfl 9344).symm, h12₄, trivial⟩ hL₄ (by facts_dec3) (a := 3072) (s := 9344)
    (n := 1024) (by facts_dec3) hB₄ hl (by decide) (by decide) (by decide) (by decide)
    fun m₅ hm₅ ↦ ⟨regIs_ptr0 r hm₅ rfl, regIs_ptr0 r hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS₆ hL₆ hB₆ ↦ ?_⟩
  have h15₆ := low4_saved hS₆ rfl (hbp₄.trunc.of_eq (hm₅.regs .r15 _ rfl))
  have h14₆ := low4_saved hS₆ rfl (h15₄.trunc.of_eq (hm₅.regs .r14 _ rfl))
  have h13₆ := low4_saved hS₆ rfl (h13₄.of_eq (hm₅.regs .r13 _ rfl))
  have hbp₆ := regIs_saved hS₆ rfl (regIs_ptr0 r hm₅ (y := .rbp) rfl)
  have h12₆ := regIs_saved hS₆ rfl (hm₅.regs .r12 _ rfl : Run.RegIs m₅ .r12 (Labels.label "memcpy").toBitVec)
  -- `b37`: to `11392`
  refine memcpy_pure r hp hpre hc b37_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b38Offset) rfl run_b37 (by decide) rfl hF₆
    ⟨hbp₆.trans (eval_base r rfl 3072).symm, h12₆, trivial⟩ hL₆ (by facts_dec3) (a := 11392) (s := 3072)
    (n := 1024) (by facts_dec3) hB₆ hl (by decide) (by decide) (by decide) (by decide)
    fun m₇ hm₇ ↦ ⟨regIs_ptr0 r hm₇ rfl, regIs_ptr0 r hm₇ rfl, rdx_lit hm₇ rfl (by decide),
      fun m₈ hF₈ hS₈ hL₈ hB₈ ↦ .done _ ⟨rfl, hF₈, ?_,
        regIs_saved hS₈ rfl (regIs_ptr0 r hm₇ (y := .rbx) rfl),
        low4_saved hS₈ rfl (h15₆.of_eq (hm₇.regs .r15 _ rfl)),
        low4_saved hS₈ rfl (h14₆.of_eq (hm₇.regs .r14 _ rfl)),
        low4_saved hS₈ rfl (h13₆.of_eq (hm₇.regs .r13 _ rfl)),
        regIs_saved hS₈ rfl (hm₇.regs .r12 _ rfl)⟩⟩
  rw [L3, ← List.singleton_append, ← List.append_assoc, facts_append, ← L2p]
  exact ⟨hL₈, ⟨hl, hB₈⟩, trivial⟩

/-- **The third layer**: from `LS2` at `b31` to `LS3` at `b38`. -/
theorem layer2_spec (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS2 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b38Offset ∧ LS3 r st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b31Offset⟩ :=
  Eventually.bind (layer2_a r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ by
    simp only at hpc
    subst hpc
    exact layer2_b r hp hpre hc h

end

end NativeRustcX64.SphincsVerifyProof.Parse
