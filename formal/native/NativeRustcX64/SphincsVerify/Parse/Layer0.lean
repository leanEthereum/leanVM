module

public import NativeRustcX64.SphincsVerify.Parse.LayerGlue
public import NativeRustcX64.SphincsVerify.Parse.LayerExec

/-!
# The parse, part 3: the first layer (`b5 .. b13`, x86-64)

`b5` `memset`s the paths' scratch (`1720`, 288 bytes) and zeroes R15; `b6` copies layer 0's
big-endian counter (`sigPtr + 4240`, 4 bytes) to `24(%rsp)`; `b7` copies layer 0's chain values
(`sigPtr + 4244`, 1024 bytes) to `12780`; `b8` `memcpy`s them to `560`; `b9` copies layer 0's path
(`sigPtr + 5268`, 128 bytes) to `1592` and `memcpy`s the chain values to `2024`; `b10 .. b13`
`memcpy` them through `3048`, `11368`, `10344`, to `9320`. Result: `LS1` at `b14`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The 24 openings in rustc's layout. -/
def opens (r : Run) : List UInt8 := ((List.range 24).map (obytesB r.sigB)).flatten

/-- What the layers keep initially: `base3` and the 24 openings at `4072`. -/
def L0 (r : Run) : List (Nat × Nat × List UInt8) := base3 r ++ [(4072, 4224, opens r)]

/-- After `b6`: layer 0's counter (big-endian) spilled at `24`. -/
def L0c (r : Run) : List (Nat × Nat × List UInt8) := L0 r ++ [(24, 4, slice r.sigB 4240 4)]

/-- After `b9`: layer 0's path at `1592`. -/
def L0p (r : Run) : List (Nat × Nat × List UInt8) := L0c r ++ [(1592, 128, slice r.sigB 5268 128)]

/-- After the first layer (`b14`): its path at `1592`, its chain values at `9320`. -/
def L1 (r : Run) : List (Nat × Nat × List UInt8) :=
  L0c r ++ [(1592, 128, slice r.sigB 5268 128), (9320, 1024, slice r.sigB 4244 1024)]

/-- **At `b14`**: the first layer parsed; RBX `sigPtr`, R14 `1720(%rsp)`. -/
def LS1 (r : Run) (m : MachineData) : Prop :=
  r.Frame m ∧ Facts r m.dmem (L1 r) ∧ Run.RegIs m .rbx r.sigPtr ∧ Run.RegIs m .r14 (r.off 1720)

end

public section

/-- Decides the first layer's facts' checks. -/
macro "facts_dec'" : tactic => `(tactic| (
  simp only [L1, L0p, L0c, L0, base3, List.cons_append, List.nil_append, List.singleton_append]
  facts_dec))

theorem regIs_saved {m₁ m₂ : MachineData} (hS : Saved m₁ m₂) {x : Reg64}
    (hx : calleeSaved x = true) {v : BitVec 64} (h : Run.RegIs m₁ x v) : Run.RegIs m₂ x v :=
  (hS.1 x hx).trans h

theorem low4_saved {m₁ m₂ : MachineData} (hS : Saved m₁ m₂) {x : Reg64}
    (hx : calleeSaved x = true) {bs : List UInt8} (h : Low4 (reg m₁ x) bs) : Low4 (reg m₂ x) bs :=
  h.of_eq (hS.1 x hx)

variable (r : Run) [ElfHost]

/-- Layer `l`'s counter bytes loaded from region 4 (`sigPtr`). -/
theorem low4_sig_counter {m : MachineData} (hpre : r.Pre) (hS : SameOutside r.m0.dmem m.dmem r.StackArea)
    {off : Nat} (hoff : off + 4 ≤ 7740) {vars : Nat → BitVec 64} {ret : BitVec 64} :
    Low4 ((envExt m (regsSig r) vars ret).load 4 off 4) (slice r.sigB off 4) := by
  refine Low4.load (length_slice (by rw [r.hsig]; omega)) ?_
  simpa [Env.base, regsSig, Run.frameRegs] using sig_slice r hpre hS hoff

/-- **`b5 .. b8`**: paths scratch zeroed, counter 0 spilled at `24`, layer 0 chain values at `560`. -/
theorem layer0_a (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : OS r 24 m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc b9Offset ∧ r.Frame st.data ∧
      Facts r st.data.dmem (L0c r) ∧
      BytesAt st.data.dmem (r.off 560) (slice r.sigB 4244 1024) ∧
      Run.RegIs st.data .rbx r.sigPtr ∧ Run.RegIs st.data .r14 (r.off 1720) ∧
      Run.RegIs st.data .r13 (r.off 560) ∧
      Run.RegIs st.data .r15 (Labels.label "memcpy").toBitVec) ⟨m, r.pc b5Offset⟩ := by
  obtain ⟨hF, hfa, hop, hbx, -⟩ := h
  have hL : Facts r m.dmem (L0 r) := by
    rw [L0, facts_append]
    exact ⟨hfa, ⟨length_openingsB r.hsig le_rfl, hop⟩, trivial⟩
  -- `b5`: memset(1720, 0, 288)
  refine memset_block r hp hpre hc b5_in_code (jn := b6Offset) rfl run_b5 (by decide) rfl hF trivial
    (a := 1720) (n := 288) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r rfl hm₁ rfl, rdx_lit hm₁ rfl (by decide), fun m₂ hF₂ hS hout hc₁ ↦ ?_⟩
  have hL₂ := Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout
    (Facts.of_block r rfl hm₁ hL (by facts_dec')) (by facts_dec')
  have hbx₂ := regIs_saved hS rfl ((hm₁.regs .rbx _ rfl).trans hbx)
  have h14₂ := regIs_saved hS rfl (regIs_ptr0 r rfl hm₁ (y := .r14) rfl)
  have h15₂ := regIs_saved hS rfl ((hm₁.regs .r15 _ rfl).trans rfl : Run.RegIs m₁ .r15 0)
  -- `b6`: spill counter 0 from `4240(%rbx)` to `24(%rsp)`
  have hk6 : b6.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := wfSig r hpre hF₂.2.2.2 hF₂.2.2.1 (fun _ ↦ 0) 0
  have hm₀ := match_sig r hpre hF₂ hbx₂ (k := []) (vars := fun _ ↦ 0) (ret := 0) trivial
  refine exec_then_elf_ro hk6 run_b6 hwf (fun _ h ↦ nomatch h) hm₀ fun st hm' hpc ↦ ?_
  have hreg := keepsRegs_regs (rs := [.rsp, .rbx, .r14, .r15]) hm₀ hm' (by decide)
  have hF₃ : r.Frame st.data := frame_of_block r hpre hF₂ rfl rfl hm' hwf rfl (by decide)
  have hc0 : BytesAt st.data.dmem (r.off 24) (slice r.sigB 4240 4) :=
    copy hm' (r := 0) (o := 24) (r' := 4) (o' := 4240) (n := 4) rfl (by decide) (by decide)
      (length_slice (by rw [r.hsig]; decide))
      (by simpa [Env.base, regsSig, Run.frameRegs] using sig_slice r hpre hF₂.2.2.1 (k := 4240) (n := 4) (by decide))
  have hL₃ : Facts r st.data.dmem (L0c r) := by
    rw [L0c, facts_append]
    exact ⟨Facts.of_block r rfl hm' hL₂ (by facts_dec'), ⟨length_slice (by rw [r.hsig]; decide), hc0⟩, trivial⟩
  have hpc' : st.pc = r.pc b7Offset := pc_next r hpc rfl
  obtain ⟨m₃, pc⟩ := st
  simp only at hpc'
  subst hpc'
  simp only at hF₃ hL₃ hreg
  -- `b7`: copy 1024 chain bytes from `sigPtr + 4244` to `12780(%rsp)`
  refine Eventually.bind_elf (sig_loop r hp hpre b7_in_code (jn := b8Offset) rfl (hp.label label_3_at)
    .r15 4244 (by decide) run_b7 rfl (by decide) (by decide)
    (rs := [.rsp, .rbx, .r14]) (by decide) (by simp) (by simp) (L := L0c r) (by facts_dec')
    (P := fun m ↦ Run.RegIs m .r14 (r.off 1720))
    (fun m m' he h1 ↦ (he .r14 (by simp)).trans h1)
    ⟨hF₃, hL₃, (hreg .rbx (by simp)).trans hbx₂, (hreg .r15 (by simp)).trans h15₂,
      (hreg .r14 (by simp)).trans h14₂⟩)
    fun ⟨m₄, pc⟩ ⟨hpc, hF₄, hL₄, hcv, hbx₄, h14₄⟩ ↦ ?_
  simp only at hpc
  subst hpc
  -- `b8`: memcpy(560, 12780, 1024)
  refine memcpy_pure r hp hpre hc b8_in_code (jn := b9Offset) rfl run_b8 (by decide) rfl hF₄ trivial
    hL₄ (by facts_dec') (a := 560) (s := 12780) (n := 1024) (by facts_dec') hcv
    (length_slice (by rw [r.hsig]; decide)) (by decide) (by decide) (by decide) (by decide)
    fun m₅ hm₅ ↦ ⟨regIs_ptr0 r rfl hm₅ rfl, regIs_ptr0 r rfl hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS hL₆ hB ↦ .done _ ⟨rfl, hF₆, hL₆, hB,
        regIs_saved hS rfl ((hm₅.regs .rbx _ rfl).trans hbx₄),
        regIs_saved hS rfl ((hm₅.regs .r14 _ rfl).trans h14₄),
        regIs_saved hS rfl (regIs_ptr0 r rfl hm₅ (y := .r13) rfl),
        regIs_saved hS rfl (hm₅.regs .r15 _ rfl)⟩⟩

/-- **`b9 .. b13`**: layer 0's path at `1592`, its chain values at `9320`. -/
theorem layer0_b (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem (L0c r) ∧
      BytesAt m.dmem (r.off 560) (slice r.sigB 4244 1024) ∧
      Run.RegIs m .rbx r.sigPtr ∧ Run.RegIs m .r14 (r.off 1720) ∧
      Run.RegIs m .r13 (r.off 560) ∧
      Run.RegIs m .r15 (Labels.label "memcpy").toBitVec) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc b14Offset ∧ LS1 r st.data) ⟨m, r.pc b9Offset⟩ := by
  obtain ⟨hF, hL, hcv, hbx, h14, h13, h15⟩ := h
  have hl : (slice r.sigB 4244 1024).length = 1024 := length_slice (by rw [r.hsig]; decide)
  -- `b9`: path to `1592`, chain values to `2024`
  refine memcpy_block_sig r hp hpre hc b9_in_code (jn := b10Offset) rfl run_b9 (by decide) rfl hF hbx
    ⟨h13.trans (eval_base r rfl 560).symm, h15, trivial⟩ (a := 2024) (s := 560) (n := 1024)
    (by decide) (by decide) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r rfl hm₁ rfl, regIs_ptr0 r rfl hm₁ rfl, rdx_lit hm₁ rfl (by decide),
      fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  have hpath : BytesAt m₁.dmem (r.off 1592) (slice r.sigB 5268 128) :=
    copy hm₁ (r := 0) (o := 1592) (r' := 4) (o' := 5268) (n := 128) rfl (by decide) (by decide)
      (length_slice (by rw [r.hsig]; decide))
      (by simpa [Env.base, regsSig, Run.frameRegs] using sig_slice r hpre hF.2.2.1 (k := 5268) (n := 128) (by decide))
  have hL₁ := Facts.of_block r rfl hm₁ hL (by facts_dec')
  have hcv₁ := bytesAt_of_block r rfl hm₁ hcv (N := 1024) (by decide) hl.le (by decide)
  have hL₂ : Facts r m₂.dmem (L0p r) := by
    rw [L0p, facts_append]
    exact ⟨Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hL₁ (by facts_dec'),
      ⟨length_slice (by rw [r.hsig]; decide), r.bytesAt_of_call hpre hc₁ (by decide) (Nat.zero_le _) hout
        (by rw [length_slice (by rw [r.hsig]; decide)]; decide)
        (by left; rw [length_slice (by rw [r.hsig]; decide)]; decide) hpath⟩, trivial⟩
  have hB' : BytesAt m₂.dmem (r.off 2024) (slice r.sigB 4244 1024) := by
    rwa [← hl, bytesOf_of_bytesAt hcv₁] at hB
  have hbx₂ : Run.RegIs m₂ .rbx r.sigPtr :=
    regIs_saved hS rfl ((hm₁.regs .rbx _ rfl).trans (by simp [Sym.eval, Env.base, regsSig, Run.frameRegs]))
  have h14₂ := regIs_saved hS rfl ((hm₁.regs .r14 _ rfl).trans h14)
  have hbp₂ := regIs_saved hS rfl (regIs_ptr0 r rfl hm₁ (y := .rbp) rfl)
  have h15₂ := regIs_saved hS rfl (hm₁.regs .r15 _ rfl : Run.RegIs m₁ .r15 (Labels.label "memcpy").toBitVec)
  -- `b10`: to `3048`
  refine memcpy_pure r hp hpre hc b10_in_code (jn := b11Offset) rfl run_b10 (by decide) rfl hF₂
    ⟨hbp₂.trans (eval_base r rfl 2024).symm, h15₂, trivial⟩ hL₂ (by facts_dec') (a := 3048) (s := 2024)
    (n := 1024) (by facts_dec') hB' hl (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r rfl hm₃ rfl, regIs_ptr0 r rfl hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS₄ hL₄ hB₄ ↦ ?_⟩
  have hbx₄ := regIs_saved hS₄ rfl ((hm₃.regs .rbx _ rfl).trans hbx₂)
  have h14₄ := regIs_saved hS₄ rfl ((hm₃.regs .r14 _ rfl).trans h14₂)
  have h13₄ := regIs_saved hS₄ rfl (regIs_ptr0 r rfl hm₃ (y := .r13) rfl)
  have h15₄ := regIs_saved hS₄ rfl (hm₃.regs .r15 _ rfl : Run.RegIs m₃ .r15 (Labels.label "memcpy").toBitVec)
  -- `b11`: to `11368`
  refine memcpy_pure r hp hpre hc b11_in_code (jn := b12Offset) rfl run_b11 (by decide) rfl hF₄
    ⟨h13₄.trans (eval_base r rfl 3048).symm, h15₄, trivial⟩ hL₄ (by facts_dec') (a := 11368) (s := 3048)
    (n := 1024) (by facts_dec') hB₄ hl (by decide) (by decide) (by decide) (by decide)
    fun m₅ hm₅ ↦ ⟨regIs_ptr0 r rfl hm₅ rfl, regIs_ptr0 r rfl hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS₆ hL₆ hB₆ ↦ ?_⟩
  have hbx₆ := regIs_saved hS₆ rfl ((hm₅.regs .rbx _ rfl).trans hbx₄)
  have h14₆ := regIs_saved hS₆ rfl ((hm₅.regs .r14 _ rfl).trans h14₄)
  have hbp₆ := regIs_saved hS₆ rfl (regIs_ptr0 r rfl hm₅ (y := .rbp) rfl)
  have h15₆ := regIs_saved hS₆ rfl (hm₅.regs .r15 _ rfl : Run.RegIs m₅ .r15 (Labels.label "memcpy").toBitVec)
  -- `b12`: to `10344`
  refine memcpy_pure r hp hpre hc b12_in_code (jn := b13Offset) rfl run_b12 (by decide) rfl hF₆
    ⟨hbp₆.trans (eval_base r rfl 11368).symm, h15₆, trivial⟩ hL₆ (by facts_dec') (a := 10344) (s := 11368)
    (n := 1024) (by facts_dec') hB₆ hl (by decide) (by decide) (by decide) (by decide)
    fun m₇ hm₇ ↦ ⟨regIs_ptr0 r rfl hm₇ rfl, regIs_ptr0 r rfl hm₇ rfl, rdx_lit hm₇ rfl (by decide),
      fun m₈ hF₈ hS₈ hL₈ hB₈ ↦ ?_⟩
  have hbx₈ := regIs_saved hS₈ rfl ((hm₇.regs .rbx _ rfl).trans hbx₆)
  have h14₈ := regIs_saved hS₈ rfl ((hm₇.regs .r14 _ rfl).trans h14₆)
  have h13₈ := regIs_saved hS₈ rfl (regIs_ptr0 r rfl hm₇ (y := .r13) rfl)
  have h15₈ := regIs_saved hS₈ rfl (hm₇.regs .r15 _ rfl : Run.RegIs m₇ .r15 (Labels.label "memcpy").toBitVec)
  -- `b13`: to `9320`
  refine memcpy_pure r hp hpre hc b13_in_code (jn := b14Offset) rfl run_b13 (by decide) rfl hF₈
    ⟨h13₈.trans (eval_base r rfl 10344).symm, h15₈, trivial⟩ hL₈ (by facts_dec') (a := 9320) (s := 10344)
    (n := 1024) (by facts_dec') hB₈ hl (by decide) (by decide) (by decide) (by decide)
    fun m₉ hm₉ ↦ ⟨regIs_ptr0 r rfl hm₉ rfl, regIs_ptr0 r rfl hm₉ rfl, rdx_lit hm₉ rfl (by decide),
      fun m₁₀ hF₁₀ hS₁₀ hL₁₀ hB₁₀ ↦ .done _ ⟨rfl, hF₁₀, ?_,
        regIs_saved hS₁₀ rfl ((hm₉.regs .rbx _ rfl).trans hbx₈),
        regIs_saved hS₁₀ rfl ((hm₉.regs .r14 _ rfl).trans h14₈)⟩⟩
  rw [L1, ← List.singleton_append, ← List.append_assoc, facts_append]
  exact ⟨hL₁₀, ⟨hl, hB₁₀⟩, trivial⟩

/-- **The first layer**: from `OS 24` at `b5` to `LS1` at `b14`. -/
theorem layer0_spec (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : OS r 24 m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc b14Offset ∧ LS1 r st.data) ⟨m, r.pc b5Offset⟩ :=
  Eventually.bind_elf (layer0_a r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ by
    simp only at hpc
    subst hpc
    exact layer0_b r hp hpre hc h

end

end NativeRustcX64.SphincsVerifyProof.Parse
