module

public import NativeRustcX64.SphincsVerify.Parse.LayerGlue
public import NativeRustcX64.SphincsVerify.Parse.LayerExec

/-!
# The parse, part 6: the first layer (`b14 .. b22`, x86-64)

`b14` `memset`s the paths' scratch; `b15` loads the first layer's counter bytes into EBP; the loop
`b16` copies the layer's chain values (the raw signature's `4244`) to `20540`; `b17` `memcpy`s
them to `576`; `b18` copies the layer's path (`5268`, 128 bytes) to `1632` and `memcpy`s the chain
values to `2048`; `b19 .. b22` `memcpy` them to `9344`, `3072`, `11392`, `8320`. Result: `LS1` at
`b23` (directive 260).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The 24 openings in rustc's layout. -/
def opens (r : Run) : List UInt8 := ((List.range 24).map (obytes r.w)).flatten

/-- What the layers keep: the message, the raw signature, the key, the openings. -/
def L0 (r : Run) : List (Nat × Nat × List UInt8) := base3 r ++ [(4096, 4224, opens r)]

/-- The facts after the first layer's path. -/
def L0p (r : Run) : List (Nat × Nat × List UInt8) :=
  L0 r ++ [(1632, 128, slice (sigBytes r.w) 5268 128)]

/-- After the first layer: its path at `1632`, its chain values at `8320`. -/
def L1 (r : Run) : List (Nat × Nat × List UInt8) :=
  L0 r ++ [(1632, 128, slice (sigBytes r.w) 5268 128), (8320, 1024, slice (sigBytes r.w) 4244 1024)]

/-- **At `b23`**: the first layer parsed; RBX the frame's `1760`, EBP the first counter's bytes. -/
def LS1 (r : Run) (m : MachineData) : Prop :=
  r.Frame m ∧ Facts r m.dmem (L1 r) ∧ Run.RegIs m .rbx (r.off 1760) ∧
    Low4 (reg m .rbp) (be32 (r.w 538).toUInt32)

end

public section

/-- Decides the layers' facts' checks. -/
macro "facts_dec'" : tactic => `(tactic| (
  simp only [L1, L0p, L0, base3, List.cons_append, List.nil_append, List.singleton_append]
  facts_dec))

theorem raw_mem0 (r : Run) : (12416, 7740, sigBytes r.w) ∈ L0 r := by simp [L0, base3]

theorem raw_mem1 (r : Run) : (12416, 7740, sigBytes r.w) ∈ L1 r := by simp [L1, L0, base3]

/-- Layer `l`'s counter in the raw signature. -/
theorem counter_slice (w : Nat → UInt64) {l : Nat} (hl : l < 3) :
    slice (sigBytes w) (sigLayerOff l) 4 = be32 (w (layerWordOff l)).toUInt32 :=
  slice_counter w hl

theorem regIs_saved {m₁ m₂ : MachineData} (hS : Saved m₁ m₂) {x : Reg64}
    (hx : calleeSaved x = true) {v : BitVec 64} (h : Run.RegIs m₁ x v) : Run.RegIs m₂ x v :=
  (hS.1 x hx).trans h

theorem low4_saved {m₁ m₂ : MachineData} (hS : Saved m₁ m₂) {x : Reg64}
    (hx : calleeSaved x = true) {bs : List UInt8} (h : Low4 (reg m₁ x) bs) : Low4 (reg m₂ x) bs :=
  h.of_eq (hS.1 x hx)

variable (r : Run) [Host]

/-- The counter `l`'s bytes, loaded. -/
theorem low4_counter_load {m : MachineData} (h : BytesAt m.dmem (r.off 12416) (sigBytes r.w))
    {l : Nat} (hl : l < 3) {o : Nat} (ho : o = 12416 + sigLayerOff l) {vars : Nat → BitVec 64}
    {ret : BitVec 64} :
    Low4 ((r.env m vars ret).load 0 o 4) (be32 (r.w (layerWordOff l)).toUInt32) := by
  refine Low4.load (by simp [be32]) ?_
  have := raw_slice r h (k := sigLayerOff l) (n := 4) (by
    have := sigLayerOff_le hl; interval_cases l <;> decide)
  rw [counter_slice r.w hl, ← ho] at this
  exact this

/-- **`b14 .. b17`**: the first layer's chain values at `576`, EBP its counter's bytes. -/
theorem layer0_a (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : OS r 24 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b18Offset ∧ r.Frame st.data ∧
      Facts r st.data.dmem (L0 r) ∧
      BytesAt st.data.dmem (r.off 576) (slice (sigBytes r.w) 4244 1024) ∧
      Run.RegIs st.data .rbx (r.off 1760) ∧ Run.RegIs st.data .r14 (r.off 576) ∧
      Low4 (reg st.data .rbp) (be32 (r.w 538).toUInt32) ∧
      Run.RegIs st.data .r12 (Labels.label "memcpy").toBitVec) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b14Offset⟩ := by
  obtain ⟨hF, hfa, hop, -⟩ := h
  have hL : Facts r m.dmem (L0 r) := by
    rw [L0, facts_append]
    exact ⟨hfa, ⟨length_openings r.w le_rfl, hop⟩, trivial⟩
  -- `b14`: the paths' scratch
  refine memset_block r hp hpre hc b14_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b15Offset) rfl run_b14 (by decide) rfl hF trivial
    (a := 1760) (n := 288) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r hm₁ rfl, rdx_lit hm₁ rfl (by decide), fun m₂ hF₂ hS hout hc₁ ↦ ?_⟩
  have hL₂ := Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout
    (Facts.of_block r rfl hm₁ hL (by facts_dec')) (by facts_dec')
  have hbx₂ := regIs_saved hS rfl (regIs_ptr0 r hm₁ (y := .rbx) rfl)
  have h14₂ := regIs_saved hS rfl ((hm₁.regs .r14 _ rfl).trans rfl : Run.RegIs m₁ .r14 0)
  -- `b15`: the counter's bytes
  have hk15 : b15.IsInfixAt Host.prog (r.k + NativeRustcX64.Sphincs.SphincsVerify.b15Offset) := b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF₂.2.2.2 (fun _ ↦ 0) 0
  have hm₀ : Match (r.env m₂ (fun _ ↦ 0) 0) (fS []) m₂ :=
    r.match_frame hpre hF₂ (known := []) trivial trivial trivial trivial
  refine exec_then hk15 run_b15 hwf (fun _ h ↦ nomatch h) hm₀ fun st hm' hpc ↦ ?_
  have hd : st.data.dmem = m₂.dmem := hm'.dmem_eq hwf rfl
  have hreg := keepsRegs_regs (rs := [.rsp, .rbx, .r12, .r13, .r14, .r15]) hm₀ hm' (by decide)
  have hF₃ : r.Frame st.data := frame_of_block r hpre hF₂ rfl rfl hm' hwf rfl (by decide)
  have hbp : Low4 (reg st.data .rbp) (be32 (r.w 538).toUInt32) :=
    (low4_counter_load r (hL₂.get (raw_mem0 r)) (l := 0) (by decide) rfl).of_eq
      (hm'.regs .rbp _ rfl)
  -- `b16`: the chain values to `20540`
  have hpc' : st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b16Offset := pc_next r hpc rfl
  obtain ⟨m₃, pc⟩ := st
  simp only at hpc'
  subst hpc'
  simp only at hF₃ hd hreg hbp
  refine Eventually.bind (span_loop r hp hpre b16_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b17Offset) rfl (hp.label NativeRustcX64.Sphincs.SphincsVerify.label_11_at)
    .r14 16660 (by decide) (by decide) run_b16 rfl (by decide) (by decide)
    (rs := [.rsp, .rbx, .rbp, .r12, .r13, .r15]) (by decide) (by simp) (L := L0 r) (by facts_dec')
    (raw_mem0 r) (P := fun m ↦ Run.RegIs m .rbx (r.off 1760) ∧
      Low4 (reg m .rbp) (be32 (r.w 538).toUInt32))
    (fun m m' he ⟨h1, h2⟩ ↦ ⟨(he .rbx (by simp)).trans h1, h2.of_eq (he .rbp (by simp))⟩)
    ⟨hF₃, hd ▸ hL₂, (hreg .r14 (by simp)).trans h14₂,
      (hreg .rbx (by simp)).trans hbx₂, hbp⟩) fun ⟨m₄, pc⟩ ⟨hpc, hF₄, hL₄, hcv, hbx₄, hbp₄⟩ ↦ ?_
  simp only at hpc
  subst hpc
  -- `b17`: to `576`
  refine memcpy_pure r hp hpre hc b17_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b18Offset) rfl run_b17 (by decide) rfl hF₄ trivial
    hL₄ (by facts_dec') (a := 576) (s := 20540) (n := 1024) (by facts_dec') hcv
    (length_slice_sig r.w (by decide)) (by decide) (by decide) (by decide) (by decide)
    fun m₅ hm₅ ↦ ⟨regIs_ptr0 r hm₅ rfl, regIs_ptr0 r hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS hL₆ hB ↦ .done _ ⟨rfl, hF₆, hL₆, hB,
        regIs_saved hS rfl ((hm₅.regs .rbx _ rfl).trans hbx₄),
        regIs_saved hS rfl (regIs_ptr0 r hm₅ (y := .r14) rfl),
        low4_saved hS rfl (hbp₄.of_eq (hm₅.regs .rbp _ rfl)),
        regIs_saved hS rfl (hm₅.regs .r12 _ rfl)⟩⟩

/-- **`b18 .. b22`**: the first layer's path at `1632`, its chain values at `8320`. -/
theorem layer0_b (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem (L0 r) ∧
      BytesAt m.dmem (r.off 576) (slice (sigBytes r.w) 4244 1024) ∧
      Run.RegIs m .rbx (r.off 1760) ∧ Run.RegIs m .r14 (r.off 576) ∧
      Low4 (reg m .rbp) (be32 (r.w 538).toUInt32) ∧
      Run.RegIs m .r12 (Labels.label "memcpy").toBitVec) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b23Offset ∧ LS1 r st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b18Offset⟩ := by
  obtain ⟨hF, hL, hcv, hbx, h14, hbp, h12⟩ := h
  have hl : (slice (sigBytes r.w) 4244 1024).length = 1024 := length_slice_sig r.w (by decide)
  -- `b18`: the path to `1632`, the chain values to `2048`
  refine memcpy_block r hp hpre hc b18_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b19Offset) rfl run_b18 (by decide) rfl hF
    ⟨h14.trans (eval_base r rfl 576).symm, h12, trivial⟩ trivial (a := 2048) (s := 576) (n := 1024)
    (by decide) (by decide) (by decide) fun m₁ hm₁ ↦
    ⟨regIs_ptr0 r hm₁ rfl, regIs_ptr0 r hm₁ rfl, rdx_lit hm₁ rfl (by decide),
      fun m₂ hF₂ hS hB hout hc₁ ↦ ?_⟩
  have hpath : BytesAt m₁.dmem (r.off 1632) (slice (sigBytes r.w) 5268 128) :=
    copy hm₁ (r := 0) (o := 1632) (r' := 0) (o' := 17684) (n := 128) rfl (by decide) (by decide)
      (length_slice_sig r.w (by decide)) (raw_slice r (hL.get (raw_mem0 r)) (k := 5268) (n := 128)
        (by decide))
  have hL₁ := Facts.of_block r rfl hm₁ hL (by facts_dec')
  have hcv₁ := bytesAt_of_block r rfl hm₁ hcv (N := 1024) (by decide) hl.le (by decide)
  have hL₂ : Facts r m₂.dmem (L0p r) := by
    rw [L0p, facts_append]
    exact ⟨Facts.of_call r hpre hc₁ (by decide) (Nat.zero_le _) hout hL₁ (by facts_dec'),
      ⟨length_slice_sig r.w (by decide), r.bytesAt_of_call hpre hc₁ (by decide) (Nat.zero_le _) hout
        (by rw [length_slice_sig r.w (by decide)]; decide)
        (by left; rw [length_slice_sig r.w (by decide)]; decide) hpath⟩, trivial⟩
  have hB' : BytesAt m₂.dmem (r.off 2048) (slice (sigBytes r.w) 4244 1024) := by
    rwa [← hl, bytesOf_of_bytesAt hcv₁] at hB
  have hbx₂ := regIs_saved hS rfl ((hm₁.regs .rbx _ rfl).trans hbx)
  have hbp₂ := low4_saved hS rfl (hbp.of_eq (hm₁.regs .rbp _ rfl))
  have h15₂ := regIs_saved hS rfl (regIs_ptr0 r hm₁ (y := .r15) rfl)
  have h12₂ := regIs_saved hS rfl (hm₁.regs .r12 _ rfl : Run.RegIs m₁ .r12 (Labels.label "memcpy").toBitVec)
  -- `b19`: to `9344`
  refine memcpy_pure r hp hpre hc b19_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b20Offset) rfl run_b19 (by decide) rfl hF₂
    ⟨h15₂.trans (eval_base r rfl 2048).symm, h12₂, trivial⟩ hL₂ (by facts_dec') (a := 9344) (s := 2048)
    (n := 1024) (by facts_dec') hB' hl (by decide) (by decide) (by decide) (by decide)
    fun m₃ hm₃ ↦ ⟨regIs_ptr0 r hm₃ rfl, regIs_ptr0 r hm₃ rfl, rdx_lit hm₃ rfl (by decide),
      fun m₄ hF₄ hS₄ hL₄ hB₄ ↦ ?_⟩
  have hbx₄ := regIs_saved hS₄ rfl ((hm₃.regs .rbx _ rfl).trans hbx₂)
  have hbp₄ := low4_saved hS₄ rfl (hbp₂.of_eq (hm₃.regs .rbp _ rfl))
  have h14₄ := regIs_saved hS₄ rfl (regIs_ptr0 r hm₃ (y := .r14) rfl)
  have h12₄ := regIs_saved hS₄ rfl (hm₃.regs .r12 _ rfl : Run.RegIs m₃ .r12 (Labels.label "memcpy").toBitVec)
  -- `b20`: to `3072`
  refine memcpy_pure r hp hpre hc b20_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b21Offset) rfl run_b20 (by decide) rfl hF₄
    ⟨h14₄.trans (eval_base r rfl 9344).symm, h12₄, trivial⟩ hL₄ (by facts_dec') (a := 3072) (s := 9344)
    (n := 1024) (by facts_dec') hB₄ hl (by decide) (by decide) (by decide) (by decide)
    fun m₅ hm₅ ↦ ⟨regIs_ptr0 r hm₅ rfl, regIs_ptr0 r hm₅ rfl, rdx_lit hm₅ rfl (by decide),
      fun m₆ hF₆ hS₆ hL₆ hB₆ ↦ ?_⟩
  have hbx₆ := regIs_saved hS₆ rfl ((hm₅.regs .rbx _ rfl).trans hbx₄)
  have hbp₆ := low4_saved hS₆ rfl (hbp₄.of_eq (hm₅.regs .rbp _ rfl))
  have h15₆ := regIs_saved hS₆ rfl (regIs_ptr0 r hm₅ (y := .r15) rfl)
  have h12₆ := regIs_saved hS₆ rfl (hm₅.regs .r12 _ rfl : Run.RegIs m₅ .r12 (Labels.label "memcpy").toBitVec)
  -- `b21`: to `11392`
  refine memcpy_pure r hp hpre hc b21_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b22Offset) rfl run_b21 (by decide) rfl hF₆
    ⟨h15₆.trans (eval_base r rfl 3072).symm, h12₆, trivial⟩ hL₆ (by facts_dec') (a := 11392) (s := 3072)
    (n := 1024) (by facts_dec') hB₆ hl (by decide) (by decide) (by decide) (by decide)
    fun m₇ hm₇ ↦ ⟨regIs_ptr0 r hm₇ rfl, regIs_ptr0 r hm₇ rfl, rdx_lit hm₇ rfl (by decide),
      fun m₈ hF₈ hS₈ hL₈ hB₈ ↦ ?_⟩
  have hbx₈ := regIs_saved hS₈ rfl ((hm₇.regs .rbx _ rfl).trans hbx₆)
  have hbp₈ := low4_saved hS₈ rfl (hbp₆.of_eq (hm₇.regs .rbp _ rfl))
  have h14₈ := regIs_saved hS₈ rfl (regIs_ptr0 r hm₇ (y := .r14) rfl)
  have h12₈ := regIs_saved hS₈ rfl (hm₇.regs .r12 _ rfl : Run.RegIs m₇ .r12 (Labels.label "memcpy").toBitVec)
  -- `b22`: to `8320`
  refine memcpy_pure r hp hpre hc b22_in_code (jn := NativeRustcX64.Sphincs.SphincsVerify.b23Offset) rfl run_b22 (by decide) rfl hF₈
    ⟨h14₈.trans (eval_base r rfl 11392).symm, h12₈, trivial⟩ hL₈ (by facts_dec') (a := 8320) (s := 11392)
    (n := 1024) (by facts_dec') hB₈ hl (by decide) (by decide) (by decide) (by decide)
    fun m₉ hm₉ ↦ ⟨regIs_ptr0 r hm₉ rfl, regIs_ptr0 r hm₉ rfl, rdx_lit hm₉ rfl (by decide),
      fun m₁₀ hF₁₀ hS₁₀ hL₁₀ hB₁₀ ↦ .done _ ⟨rfl, hF₁₀, ?_,
        regIs_saved hS₁₀ rfl ((hm₉.regs .rbx _ rfl).trans hbx₈),
        low4_saved hS₁₀ rfl (hbp₈.of_eq (hm₉.regs .rbp _ rfl))⟩⟩
  rw [L1, ← List.singleton_append, ← List.append_assoc, facts_append]
  exact ⟨hL₁₀, ⟨hl, hB₁₀⟩, trivial⟩

/-- **The first layer**: from `OS 24` at `b14` to `LS1` at `b23`. -/
theorem layer0_spec (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {m : MachineData}
    (h : OS r 24 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b23Offset ∧ LS1 r st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b14Offset⟩ :=
  Eventually.bind (layer0_a r hp hpre hc h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ by
    simp only at hpc
    subst hpc
    exact layer0_b r hp hpre hc h

end

end NativeRustcX64.SphincsVerifyProof.Parse
