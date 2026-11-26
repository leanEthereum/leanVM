module

public import NativeRustcX64.SphincsVerify.Parse.Layer1

/-!
# The parse, part 5: the third layer (`b22 .. b28`, x86-64)

`b22` loads layer 2's counter bytes (`sigPtr + 6552`) into R15D; `b23` copies layer 2's chain
values (`sigPtr + 6556`, 1024 bytes) to `12780`; `b24` `memcpy`s them to `560`; `b25` copies layer
2's path (`sigPtr + 7580`, 160 bytes) to `1848`, byte-swaps layer 1's counter into `16(%rsp)`,
loads and byte-swaps layer 0's counter from `24(%rsp)` into R12D, byte-swaps layer 2's counter
in R15D, and `memcpy`s the chain values to `2024`; `b26 .. b28` `memcpy` them through `3048` and
`11368` to `10344`. Result: `LS3` at `b29`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- After `b25`: layer 2's path at `1848`, layer 1's counter (little-endian) at `16`. -/
def L2p (r : Run) : List (Nat × Nat × List UInt8) :=
  L2 r ++ [(1848, 160, slice r.sigB 7580 160), (16, 4, (slice r.sigB 5396 4).reverse)]

/-- After the third layer (`b29`): also layer 2's chain values at `10344`. -/
def L3 (r : Run) : List (Nat × Nat × List UInt8) :=
  L2p r ++ [(10344, 1024, slice r.sigB 6556 1024)]

/-- **At `b29`**: three layers parsed; RBX `sigPtr`, R14 `10344`, R12D and R15D layer 0 and 2
counters little-endian, RBP `memcpy`. -/
def LS3 (r : Run) [Labels] (m : MachineData) : Prop :=
  r.Frame m ∧ Facts r m.dmem (L3 r) ∧ Run.RegIs m .rbx r.sigPtr ∧
    Run.RegIs m .r14 (r.off 10344) ∧
    Low4 (reg m .r12) (slice r.sigB 4240 4).reverse ∧
    Low4 (reg m .r15) (slice r.sigB 6552 4).reverse ∧
    Run.RegIs m .rbp (Labels.label "memcpy").toBitVec

end

public section

/-- Decides the third layer's facts' checks. -/
macro "facts_dec3" : tactic => `(tactic| (
  simp only [L3, L2p, L2, L1, L0c, L0, base3, List.cons_append, List.nil_append, List.singleton_append,
    List.append_assoc]
  facts_dec))

variable (r : Run) [Host]

/-- **`b22 .. b24`**: layer 2's counter in R15D, its chain values at `560`. -/
theorem layer2_a (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS2 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc b25Offset ∧ r.Frame st.data ∧
      Facts r st.data.dmem (L2 r) ∧
      BytesAt st.data.dmem (r.off 560) (slice r.sigB 6556 1024) ∧
      Run.RegIs st.data .rbx r.sigPtr ∧ Run.RegIs st.data .r14 (r.off 560) ∧
      Low4 (reg st.data .r12) (slice r.sigB 5396 4) ∧
      Low4 (reg st.data .r15) (slice r.sigB 6552 4) ∧
      Run.RegIs st.data .rbp (Labels.label "memcpy").toBitVec) ⟨m, r.pc b22Offset⟩ := by
  obtain ⟨hF, hL, hbx, h12⟩ := h
  -- `b22`: load layer 2 counter into R15D, zero RAX
  have hk : b22.IsInfixAt Host.prog (r.k + b22Offset) := b22_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := wfSig r hpre hF.2.2.2 hF.2.2.1 (fun _ ↦ 0) 0
  have hm₀ := match_sig r hpre hF hbx (k := []) (vars := fun _ ↦ 0) (ret := 0) trivial
  refine exec_then hk run_b22 hwf (fun _ h ↦ nomatch h) hm₀ fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  have hreg := keepsRegs_regs (rs := [.rsp, .rbx, .r12]) hm₀ hm' (by decide)
  have hF₁ : r.Frame st.data := frame_of_block r hpre hF rfl rfl hm' hwf rfl (by decide)
  have h15 : Low4 (reg st.data .r15) (slice r.sigB 6552 4) :=
    (low4_sig_counter r hpre hF.2.2.1 (off := 6552) (by decide)).of_eq (hm'.regs .r15 _ rfl)
  have hax : Run.RegIs st.data .rax 0 := (hm'.regs .rax _ rfl).trans rfl
  have hpc' : st.pc = r.pc b23Offset := pc_next r hpc rfl
  obtain ⟨m₁, pc⟩ := st
  simp only at hpc'
  subst hpc'
  simp only at hF₁ hd hreg h15 hax
  -- `b23`: copy 1024 chain bytes from `sigPtr + 6556` to `12780(%rsp)`
  refine Eventually.bind (sig_loop r hp hpre b23_in_code (jn := b24Offset) rfl (hp.label label_7_at)
    .rax 6556 (by decide) run_b23 rfl (by decide) (by decide)
    (rs := [.rsp, .rbx, .r12, .r15]) (by decide) (by simp) (by simp) (L := L2 r) (by facts_dec3)
    (P := fun m ↦ Low4 (reg m .r12) (slice r.sigB 5396 4) ∧ Low4 (reg m .r15) (slice r.sigB 6552 4))
    (fun m m' he ⟨h1, h2⟩ ↦ ⟨h1.of_eq (he .r12 (by simp)), h2.of_eq (he .r15 (by simp))⟩)
    ⟨hF₁, hd ▸ hL, (hreg .rbx (by simp)).trans hbx, hax, h12.of_eq (hreg .r12 (by simp)), h15⟩)
    fun ⟨m₂, pc⟩ ⟨hpc, hF₂, hL₂, hcv, hbx₂, h12₂, h15₂⟩ ↦ ?_
  simp only at hpc
  subst hpc
  -- `b24`: memcpy(560, 12780, 1024)
  refine memcpy_pure r hp hpre hc b24_in_code (jn := b25Offset) rfl run_b24 (by decide) rfl hF₂ trivial
    hL₂ (by facts_dec3) (a := 560) (s := 12780) (n := 1024) (by facts_dec3) hcv
    (length_slice (by rw [r.hsig]; decide)) (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r rfl hm₃ rfl, regIs_ptr0 r rfl hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS hL₄ hB ↦ .done _ ⟨rfl, hF₄, hL₄, hB,
        regIs_saved hS rfl ((hm₃.regs .rbx _ rfl).trans hbx₂),
        regIs_saved hS rfl (regIs_ptr0 r rfl hm₃ (y := .r14) rfl),
        low4_saved hS rfl (h12₂.of_eq (hm₃.regs .r12 _ rfl)),
        low4_saved hS rfl (h15₂.of_eq (hm₃.regs .r15 _ rfl)),
        regIs_saved hS rfl (hm₃.regs .rbp _ rfl)⟩⟩

/-- **`b25 .. b28`**: layer 2's path at `1848`, counters byte-swapped, chain values at `10344`. -/
theorem layer2_b (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem (L2 r) ∧
      BytesAt m.dmem (r.off 560) (slice r.sigB 6556 1024) ∧
      Run.RegIs m .rbx r.sigPtr ∧ Run.RegIs m .r14 (r.off 560) ∧
      Low4 (reg m .r12) (slice r.sigB 5396 4) ∧ Low4 (reg m .r15) (slice r.sigB 6552 4) ∧
      Run.RegIs m .rbp (Labels.label "memcpy").toBitVec) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc b29Offset ∧ LS3 r st.data) ⟨m, r.pc b25Offset⟩ := by
  obtain ⟨hF, hL, hcv, hbx, h14, h12, h15, hbp⟩ := h
  have hl : (slice r.sigB 6556 1024).length = 1024 := length_slice (by rw [r.hsig]; decide)
  have hl4 : ∀ k, k + 4 ≤ 7740 → (slice r.sigB k 4).reverse.length = 4 := fun k hk ↦ by
    rw [List.length_reverse, length_slice (by rw [r.hsig]; omega)]
  -- `b25`: path to `1848`, swap counters, chain values to `2024`
  refine memcpy_block_sig r hp hpre hc b25_in_code (jn := b26Offset) rfl run_b25 (by decide) rfl hF hbx
    ⟨h14.trans (eval_base r rfl 560).symm, hbp, trivial⟩
    (a := 2024) (s := 560) (n := 1024) (by decide) (by decide) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r rfl hm₁ rfl, regIs_ptr0 r rfl hm₁ rfl, rdx_lit hm₁ rfl (by decide),
      fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  have hpath : BytesAt m₁.dmem (r.off 1848) (slice r.sigB 7580 160) :=
    copy hm₁ (r := 0) (o := 1848) (r' := 4) (o' := 7580) (n := 160) rfl (by decide) (by decide)
      (length_slice (by rw [r.hsig]))
      (by simpa [Env.base, regsSig, Run.frameRegs] using sig_slice r hpre hF.2.2.1 (k := 7580) (n := 160) (by decide))
  have hc1 : BytesAt m₁.dmem (r.off 16) (slice r.sigB 5396 4).reverse :=
    bytesAt_low hm₁ (r := 0) (o := 16) (sz := 21632)
      (v := .un .trunc .W32 (.un .bswap .W32 (.reg .r12))) rfl (by decide) (by decide)
      h12.bswap.trunc
  have hc0_mem : BytesAt m.dmem (r.off 24) (slice r.sigB 4240 4) :=
    hL.get (o := 24) (n := 4) (by simp [L2, L1, L0c])
  have hc0_load : Low4 ((Env.ofMachine m (regsSig r) (fun _ ↦ 0) (r.pc b26Offset).toBitVec).load 0 24 4)
      (slice r.sigB 4240 4) :=
    Low4.load (length_slice (by rw [r.hsig]; decide)) (by simpa [Run.off, Env.base, regsSig, Run.frameRegs] using hc0_mem)
  have hL₁ := Facts.of_block r rfl hm₁ hL (by facts_dec3)
  have hcv₁ := bytesAt_of_block r rfl hm₁ hcv (N := 1024) (by decide) hl.le (by decide)
  have hL₂ : Facts r m₂.dmem (L2p r) := by
    rw [L2p, facts_append]
    exact ⟨Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hL₁ (by facts_dec3),
      ⟨length_slice (by rw [r.hsig]), r.bytesAt_of_call hpre hc₁ (by decide) (Nat.zero_le _) hout
        (by rw [length_slice (by rw [r.hsig])]; decide)
        (by left; rw [length_slice (by rw [r.hsig])]; decide) hpath⟩,
      ⟨hl4 5396 (by decide), r.bytesAt_of_call hpre hc₁ (by decide) (Nat.zero_le _) hout
        (by rw [hl4 5396 (by decide)]; decide)
        (by left; rw [hl4 5396 (by decide)]; decide) hc1⟩, trivial⟩
  have hB' : BytesAt m₂.dmem (r.off 2024) (slice r.sigB 6556 1024) := by
    rwa [← hl, bytesOf_of_bytesAt hcv₁] at hB
  have hbx₂ : Run.RegIs m₂ .rbx r.sigPtr :=
    regIs_saved hS rfl ((hm₁.regs .rbx _ rfl).trans (by simp [Sym.eval, Env.base, regsSig, Run.frameRegs]))
  have h12₂ := low4_saved hS rfl (hc0_load.bswap.of_eq (hm₁.regs .r12 _ rfl))
  have h15₂ := low4_saved hS rfl (h15.bswap.of_eq (hm₁.regs .r15 _ rfl))
  have h13₂ := regIs_saved hS rfl (regIs_ptr0 r rfl hm₁ (y := .r13) rfl)
  have hbp₂ := regIs_saved hS rfl (hm₁.regs .rbp _ rfl : Run.RegIs m₁ .rbp (Labels.label "memcpy").toBitVec)
  -- `b26`: to `3048`
  refine memcpy_pure r hp hpre hc b26_in_code (jn := b27Offset) rfl run_b26 (by decide) rfl hF₂
    ⟨h13₂.trans (eval_base r rfl 2024).symm, hbp₂, trivial⟩ hL₂ (by facts_dec3) (a := 3048) (s := 2024)
    (n := 1024) (by facts_dec3) hB' hl (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r rfl hm₃ rfl, regIs_ptr0 r rfl hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS₄ hL₄ hB₄ ↦ ?_⟩
  have hbx₄ := regIs_saved hS₄ rfl ((hm₃.regs .rbx _ rfl).trans hbx₂)
  have h12₄ := low4_saved hS₄ rfl (h12₂.of_eq (hm₃.regs .r12 _ rfl))
  have h15₄ := low4_saved hS₄ rfl (h15₂.of_eq (hm₃.regs .r15 _ rfl))
  have h14₄ := regIs_saved hS₄ rfl (regIs_ptr0 r rfl hm₃ (y := .r14) rfl)
  have hbp₄ := regIs_saved hS₄ rfl (hm₃.regs .rbp _ rfl : Run.RegIs m₃ .rbp (Labels.label "memcpy").toBitVec)
  -- `b27`: to `11368`
  refine memcpy_pure r hp hpre hc b27_in_code (jn := b28Offset) rfl run_b27 (by decide) rfl hF₄
    ⟨h14₄.trans (eval_base r rfl 3048).symm, hbp₄, trivial⟩ hL₄ (by facts_dec3) (a := 11368) (s := 3048)
    (n := 1024) (by facts_dec3) hB₄ hl (by decide) (by decide) (by decide) (by decide)
    fun m₅ hm₅ ↦ ⟨regIs_ptr0 r rfl hm₅ rfl, regIs_ptr0 r rfl hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS₆ hL₆ hB₆ ↦ ?_⟩
  have hbx₆ := regIs_saved hS₆ rfl ((hm₅.regs .rbx _ rfl).trans hbx₄)
  have h12₆ := low4_saved hS₆ rfl (h12₄.of_eq (hm₅.regs .r12 _ rfl))
  have h15₆ := low4_saved hS₆ rfl (h15₄.of_eq (hm₅.regs .r15 _ rfl))
  have h13₆ := regIs_saved hS₆ rfl (regIs_ptr0 r rfl hm₅ (y := .r13) rfl)
  have hbp₆ := regIs_saved hS₆ rfl (hm₅.regs .rbp _ rfl : Run.RegIs m₅ .rbp (Labels.label "memcpy").toBitVec)
  -- `b28`: to `10344`
  refine memcpy_pure r hp hpre hc b28_in_code (jn := b29Offset) rfl run_b28 (by decide) rfl hF₆
    ⟨h13₆.trans (eval_base r rfl 11368).symm, hbp₆, trivial⟩ hL₆ (by facts_dec3) (a := 10344) (s := 11368)
    (n := 1024) (by facts_dec3) hB₆ hl (by decide) (by decide) (by decide) (by decide)
    fun m₇ hm₇ ↦ ⟨regIs_ptr0 r rfl hm₇ rfl, regIs_ptr0 r rfl hm₇ rfl, rdx_lit hm₇ rfl (by decide),
      fun m₈ hF₈ hS₈ hL₈ hB₈ ↦ .done _ ⟨rfl, hF₈, ?_,
        regIs_saved hS₈ rfl ((hm₇.regs .rbx _ rfl).trans hbx₆),
        regIs_saved hS₈ rfl (regIs_ptr0 r rfl hm₇ (y := .r14) rfl),
        low4_saved hS₈ rfl (h12₆.of_eq (hm₇.regs .r12 _ rfl)),
        low4_saved hS₈ rfl (h15₆.of_eq (hm₇.regs .r15 _ rfl)),
        regIs_saved hS₈ rfl (hm₇.regs .rbp _ rfl)⟩⟩
  rw [L3, facts_append]
  exact ⟨hL₈, ⟨hl, hB₈⟩, trivial⟩

/-- **The third layer**: from `LS2` at `b22` to `LS3` at `b29`. -/
theorem layer2_spec (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : LS2 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc b29Offset ∧ LS3 r st.data) ⟨m, r.pc b22Offset⟩ :=
  Eventually.bind (layer2_a r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ by
    simp only at hpc
    subst hpc
    exact layer2_b r hp hpre hc h

end

end NativeRustcX64.SphincsVerifyProof.Parse
