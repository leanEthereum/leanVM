module

public import NativeRustcX64.SphincsVerify.Parse.Layer0

/-!
# The parse, part 4: the second layer (`b14 .. b21`, x86-64)

`b14` loads layer 1's counter bytes (`sigPtr + 5396`) into R12D; `b15` copies layer 1's chain
values (`sigPtr + 5400`, 1024 bytes) to `12780`; `b16` `memcpy`s them to `560`; `b17` copies layer
1's path (`sigPtr + 6424`, 128 bytes) to `1720` and `memcpy`s the chain values to `2024`;
`b18 .. b21` `memcpy` them through `3048`, `11368`, `10344`, to `8296`. Result: `LS2` at `b22`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The facts after the second layer's path. -/
def L1p (r : Run) : List (Nat × Nat × List UInt8) :=
  L1 r ++ [(1720, 128, slice r.sigB 6424 128)]

/-- After the second layer (`b22`): its path at `1720`, its chain values at `8296`. -/
def L2 (r : Run) : List (Nat × Nat × List UInt8) :=
  L1 r ++ [(1720, 128, slice r.sigB 6424 128), (8296, 1024, slice r.sigB 5400 1024)]

/-- **At `b22`**: two layers parsed; RBX `sigPtr`, R12D layer 1's counter bytes (big-endian). -/
def LS2 (r : Run) (m : MachineData) : Prop :=
  r.Frame m ∧ Facts r m.dmem (L2 r) ∧ Run.RegIs m .rbx r.sigPtr ∧
    Low4 (reg m .r12) (slice r.sigB 5396 4)

end

public section

/-- Decides the second layer's facts' checks. -/
macro "facts_dec2" : tactic => `(tactic| (
  simp only [L2, L1p, L1, L0c, L0, base3, List.cons_append, List.nil_append, List.singleton_append]
  facts_dec))

variable (r : Run) [ElfHost]

/-- **`b14 .. b16`**: layer 1's counter in R12D, its chain values at `560`. -/
theorem layer1_a (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS1 r m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc b17Offset ∧ r.Frame st.data ∧
      Facts r st.data.dmem (L1 r) ∧
      BytesAt st.data.dmem (r.off 560) (slice r.sigB 5400 1024) ∧
      Run.RegIs st.data .rbx r.sigPtr ∧ Run.RegIs st.data .r14 (r.off 1720) ∧
      Run.RegIs st.data .r13 (r.off 560) ∧
      Low4 (reg st.data .r12) (slice r.sigB 5396 4) ∧
      Run.RegIs st.data .r15 (Labels.label "memcpy").toBitVec) ⟨m, r.pc b14Offset⟩ := by
  obtain ⟨hF, hL, hbx, h14⟩ := h
  -- `b14`: load layer 1 counter into R12D, zero RAX
  have hk : b14.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + b14Offset) := b14_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := wfSig r hpre hF.2.2.2 hF.2.2.1 (fun _ ↦ 0) 0
  have hm₀ := match_sig r hpre hF hbx (k := []) (vars := fun _ ↦ 0) (ret := 0) trivial
  refine exec_then_elf_ro hk run_b14 hwf (fun _ h ↦ nomatch h) hm₀ fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq_ro hwf rfl
  have hreg := keepsRegs_regs (rs := [.rsp, .rbx, .r14]) hm₀ hm' (by decide)
  have hF₁ : r.Frame st.data := frame_of_block r hpre hF rfl rfl hm' hwf rfl (by decide)
  have h12 : Low4 (reg st.data .r12) (slice r.sigB 5396 4) :=
    (low4_sig_counter r hpre hF.2.2.1 (off := 5396) (by decide)).of_eq (hm'.regs .r12 _ rfl)
  have hax : Run.RegIs st.data .rax 0 := (hm'.regs .rax _ rfl).trans rfl
  have hpc' : st.pc = r.pc b15Offset := pc_next r hpc rfl
  obtain ⟨m₁, pc⟩ := st
  simp only at hpc'
  subst hpc'
  simp only at hF₁ hd hreg h12 hax
  -- `b15`: copy 1024 chain bytes from `sigPtr + 5400` to `12780(%rsp)`
  refine Eventually.bind_elf (sig_loop r hp hpre b15_in_code (jn := b16Offset) rfl (hp.label label_5_at)
    .rax 5400 (by decide) run_b15 rfl (by decide) (by decide)
    (rs := [.rsp, .rbx, .r14, .r12]) (by decide) (by simp) (by simp) (L := L1 r) (by facts_dec2)
    (P := fun m ↦ Run.RegIs m .r14 (r.off 1720) ∧ Low4 (reg m .r12) (slice r.sigB 5396 4))
    (fun m m' he ⟨h1, h2⟩ ↦ ⟨(he .r14 (by simp)).trans h1, h2.of_eq (he .r12 (by simp))⟩)
    ⟨hF₁, hd ▸ hL, (hreg .rbx (by simp)).trans hbx, hax, (hreg .r14 (by simp)).trans h14, h12⟩)
    fun ⟨m₂, pc⟩ ⟨hpc, hF₂, hL₂, hcv, hbx₂, h14₂, h12₂⟩ ↦ ?_
  simp only at hpc
  subst hpc
  -- `b16`: memcpy(560, 12780, 1024)
  refine memcpy_pure r hp hpre hc b16_in_code (jn := b17Offset) rfl run_b16 (by decide) rfl hF₂ trivial
    hL₂ (by facts_dec2) (a := 560) (s := 12780) (n := 1024) (by facts_dec2) hcv
    (length_slice (by rw [r.hsig]; decide)) (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r rfl hm₃ rfl, regIs_ptr0 r rfl hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS hL₄ hB ↦ .done _ ⟨rfl, hF₄, hL₄, hB,
        regIs_saved hS rfl ((hm₃.regs .rbx _ rfl).trans hbx₂),
        regIs_saved hS rfl ((hm₃.regs .r14 _ rfl).trans h14₂),
        regIs_saved hS rfl (regIs_ptr0 r rfl hm₃ (y := .r13) rfl),
        low4_saved hS rfl (h12₂.of_eq (hm₃.regs .r12 _ rfl)),
        regIs_saved hS rfl (hm₃.regs .r15 _ rfl)⟩⟩

/-- **`b17 .. b21`**: layer 1's path at `1720`, its chain values at `8296`. -/
theorem layer1_b (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem (L1 r) ∧
      BytesAt m.dmem (r.off 560) (slice r.sigB 5400 1024) ∧
      Run.RegIs m .rbx r.sigPtr ∧ Run.RegIs m .r14 (r.off 1720) ∧
      Run.RegIs m .r13 (r.off 560) ∧
      Low4 (reg m .r12) (slice r.sigB 5396 4) ∧
      Run.RegIs m .r15 (Labels.label "memcpy").toBitVec) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc b22Offset ∧ LS2 r st.data) ⟨m, r.pc b17Offset⟩ := by
  obtain ⟨hF, hL, hcv, hbx, h14, h13, h12, h15⟩ := h
  have hl : (slice r.sigB 5400 1024).length = 1024 := length_slice (by rw [r.hsig]; decide)
  -- `b17`: path to `1720`, chain values to `2024`
  refine memcpy_block_sig r hp hpre hc b17_in_code (jn := b18Offset) rfl run_b17 (by decide) rfl hF hbx
    ⟨h14.trans (eval_base r rfl 1720).symm, h13.trans (eval_base r rfl 560).symm, h15, trivial⟩
    (a := 2024) (s := 560) (n := 1024) (by decide) (by decide) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r rfl hm₁ rfl, regIs_ptr0 r rfl hm₁ rfl, rdx_lit hm₁ rfl (by decide),
      fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  have hpath : BytesAt m₁.dmem (r.off 1720) (slice r.sigB 6424 128) :=
    copy hm₁ (r := 0) (o := 1720) (r' := 4) (o' := 6424) (n := 128) rfl (by decide) (by decide)
      (length_slice (by rw [r.hsig]; decide))
      (by simpa [Env.base, regsSig, Run.frameRegs] using sig_slice r hpre hF.2.2.1 (k := 6424) (n := 128) (by decide))
  have hL₁ := Facts.of_block r rfl hm₁ hL (by facts_dec2)
  have hcv₁ := bytesAt_of_block r rfl hm₁ hcv (N := 1024) (by decide) hl.le (by decide)
  have hL₂ : Facts r m₂.dmem (L1p r) := by
    rw [L1p, facts_append]
    exact ⟨Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hL₁ (by facts_dec2),
      ⟨length_slice (by rw [r.hsig]; decide), r.bytesAt_of_call hpre hc₁ (by decide) (Nat.zero_le _) hout
        (by rw [length_slice (by rw [r.hsig]; decide)]; decide)
        (by left; rw [length_slice (by rw [r.hsig]; decide)]; decide) hpath⟩, trivial⟩
  have hB' : BytesAt m₂.dmem (r.off 2024) (slice r.sigB 5400 1024) := by
    rwa [← hl, bytesOf_of_bytesAt hcv₁] at hB
  have hbx₂ : Run.RegIs m₂ .rbx r.sigPtr :=
    regIs_saved hS rfl ((hm₁.regs .rbx _ rfl).trans (by simp [Sym.eval, Env.base, regsSig, Run.frameRegs]))
  have h12₂ := low4_saved hS rfl (h12.of_eq (hm₁.regs .r12 _ rfl))
  have h14₂ := regIs_saved hS rfl (regIs_ptr0 r rfl hm₁ (y := .r14) rfl)
  have h15₂ := regIs_saved hS rfl (hm₁.regs .r15 _ rfl : Run.RegIs m₁ .r15 (Labels.label "memcpy").toBitVec)
  -- `b18`: to `3048`
  refine memcpy_pure r hp hpre hc b18_in_code (jn := b19Offset) rfl run_b18 (by decide) rfl hF₂
    ⟨h14₂.trans (eval_base r rfl 2024).symm, h15₂, trivial⟩ hL₂ (by facts_dec2) (a := 3048) (s := 2024)
    (n := 1024) (by facts_dec2) hB' hl (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r rfl hm₃ rfl, regIs_ptr0 r rfl hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS₄ hL₄ hB₄ ↦ ?_⟩
  have hbx₄ := regIs_saved hS₄ rfl ((hm₃.regs .rbx _ rfl).trans hbx₂)
  have h12₄ := low4_saved hS₄ rfl (h12₂.of_eq (hm₃.regs .r12 _ rfl))
  have h13₄ := regIs_saved hS₄ rfl (regIs_ptr0 r rfl hm₃ (y := .r13) rfl)
  have h15₄ := regIs_saved hS₄ rfl (hm₃.regs .r15 _ rfl : Run.RegIs m₃ .r15 (Labels.label "memcpy").toBitVec)
  -- `b19`: to `11368`
  refine memcpy_pure r hp hpre hc b19_in_code (jn := b20Offset) rfl run_b19 (by decide) rfl hF₄
    ⟨h13₄.trans (eval_base r rfl 3048).symm, h15₄, trivial⟩ hL₄ (by facts_dec2) (a := 11368) (s := 3048)
    (n := 1024) (by facts_dec2) hB₄ hl (by decide) (by decide) (by decide) (by decide)
    fun m₅ hm₅ ↦ ⟨regIs_ptr0 r rfl hm₅ rfl, regIs_ptr0 r rfl hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS₆ hL₆ hB₆ ↦ ?_⟩
  have hbx₆ := regIs_saved hS₆ rfl ((hm₅.regs .rbx _ rfl).trans hbx₄)
  have h12₆ := low4_saved hS₆ rfl (h12₄.of_eq (hm₅.regs .r12 _ rfl))
  have h14₆ := regIs_saved hS₆ rfl (regIs_ptr0 r rfl hm₅ (y := .r14) rfl)
  have h15₆ := regIs_saved hS₆ rfl (hm₅.regs .r15 _ rfl : Run.RegIs m₅ .r15 (Labels.label "memcpy").toBitVec)
  -- `b20`: to `10344`
  refine memcpy_pure r hp hpre hc b20_in_code (jn := b21Offset) rfl run_b20 (by decide) rfl hF₆
    ⟨h14₆.trans (eval_base r rfl 11368).symm, h15₆, trivial⟩ hL₆ (by facts_dec2) (a := 10344) (s := 11368)
    (n := 1024) (by facts_dec2) hB₆ hl (by decide) (by decide) (by decide) (by decide)
    fun m₇ hm₇ ↦ ⟨regIs_ptr0 r rfl hm₇ rfl, regIs_ptr0 r rfl hm₇ rfl, rdx_lit hm₇ rfl (by decide),
      fun m₈ hF₈ hS₈ hL₈ hB₈ ↦ ?_⟩
  have hbx₈ := regIs_saved hS₈ rfl ((hm₇.regs .rbx _ rfl).trans hbx₆)
  have h12₈ := low4_saved hS₈ rfl (h12₆.of_eq (hm₇.regs .r12 _ rfl))
  have h13₈ := regIs_saved hS₈ rfl (regIs_ptr0 r rfl hm₇ (y := .r13) rfl)
  have h15₈ := regIs_saved hS₈ rfl (hm₇.regs .r15 _ rfl : Run.RegIs m₇ .r15 (Labels.label "memcpy").toBitVec)
  -- `b21`: to `8296`
  refine memcpy_pure r hp hpre hc b21_in_code (jn := b22Offset) rfl run_b21 (by decide) rfl hF₈
    ⟨h13₈.trans (eval_base r rfl 10344).symm, h15₈, trivial⟩ hL₈ (by facts_dec2) (a := 8296)
    (s := 10344) (n := 1024) (by facts_dec2) hB₈ hl (by decide) (by decide) (by decide) (by decide)
    fun m₉ hm₉ ↦ ⟨regIs_ptr0 r rfl hm₉ rfl, regIs_ptr0 r rfl hm₉ rfl, rdx_lit hm₉ rfl (by decide),
      fun m₁₀ hF₁₀ hS₁₀ hL₁₀ hB₁₀ ↦ .done _ ⟨rfl, hF₁₀, ?_,
        regIs_saved hS₁₀ rfl ((hm₉.regs .rbx _ rfl).trans hbx₈),
        low4_saved hS₁₀ rfl (h12₈.of_eq (hm₉.regs .r12 _ rfl))⟩⟩
  rw [L2, ← List.singleton_append, ← List.append_assoc, facts_append, ← L1p]
  exact ⟨hL₁₀, ⟨hl, hB₁₀⟩, trivial⟩

/-- **The second layer**: from `LS1` at `b14` to `LS2` at `b22`. -/
theorem layer1_spec (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS1 r m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc b22Offset ∧ LS2 r st.data) ⟨m, r.pc b14Offset⟩ :=
  Eventually.bind_elf (layer1_a r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ by
    simp only at hpc
    subst hpc
    exact layer1_b r hp hpre hc h

end

end NativeRustcX64.SphincsVerifyProof.Parse
