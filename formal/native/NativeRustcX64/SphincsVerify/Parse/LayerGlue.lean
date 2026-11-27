module

public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.SphincsVerify.Parse.OpenTurn

/-!
# What the layers' proofs share (x86-64)

- `memcpy_pure`: a pure frame block ending in `memcpy` of known bytes.
- `sig_loop`: a layer's chain-value copy loop (`b7`, `b15`, `b23`), copying 32 × 32 = 1024 bytes
  from `sigPtr + src` to `12780(%rsp)`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

public section

theorem factsApart_mono {L : List (Nat × Nat × List UInt8)} {a n a' n' : Nat}
    (h : factsApart L a n = true) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) :
    factsApart L a' n' = true := by
  simp only [factsApart, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h ⊢
  intro p hp
  obtain ⟨h3, h4⟩ := h p hp
  exact ⟨h3, by omega⟩

/-- Decides the facts' checks on a literal layout. -/
macro "facts_dec" : tactic => `(tactic| (
  simp only [factsOK_layout, factsApart_layout, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.singleton_append]
  decide))

variable (r : Run) [ElfHost]

/-- **A pure block, then `memcpy(a, s, n)` of known bytes**. -/
theorem memcpy_pure (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) (hc : Callees) {ds : List Directive}
    {jd jn : Nat} (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn)
    {k : List (Reg64 × Sym)} {S' : SState}
    (hx : exec ds (fS k) = some (S', .call NativeRustcX64.Common.Memcpy.entryLabel)) (hfw : Run.frameWrites S' = true)
    (hrsp : S'.reg .rsp = some (.ptr 0 (-8))) {m : MachineData} (hF : r.Frame m)
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) (r.pc jn).toBitVec)) k)
    {L : List (Nat × Nat × List UInt8)} (hL : Facts r m.dmem L) (hok : factsOK S' L = true)
    {a s n : Nat} (hap : factsApart L a n = true) {bs : List UInt8}
    (hsrc : BytesAt m.dmem (r.off s) bs) (hl : bs.length = n) (hsok : noW0 S' s n = true)
    (ha : a + n ≤ 21576) (hs : s + n ≤ 21624) (hd : a + n ≤ s ∨ s + n ≤ a)
    {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) (r.pc jn).toBitVec) S' m₁ →
      Run.RegIs m₁ .rdi (r.off a) ∧ Run.RegIs m₁ .rsi (r.off s) ∧ (reg m₁ .rdx).toNat = n ∧
      ∀ m₂, r.Frame m₂ → Saved m₁ m₂ → Facts r m₂.dmem L → BytesAt m₂.dmem (r.off a) bs →
        Eventually (elfStep1 ElfHost.exe) R ⟨m₂, r.pc jn⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc jd⟩ := by
  refine memcpy_block r hp hpre hc hb hjn hx hfw hrsp hF hk trivial ha hs hd fun m₁ hm₁ ↦ ?_
  obtain ⟨h0, h1, h2, hcont⟩ := h m₁ hm₁
  refine ⟨h0, h1, h2, fun m₂ hF₂ hS hB hout hc₁ ↦ hcont m₂ hF₂ hS ?_ ?_⟩
  · exact Facts.of_call r hpre hc₁ (by omega) (Nat.zero_le _) hout (Facts.of_block r rfl hm₁ hL hok)
      hap
  · have hs₁ := bytesAt_of_block r rfl hm₁ hsrc hsok hl.le (by omega)
    rwa [← hl, bytesOf_of_bytesAt hs₁] at hB

/-- **A turn of a layer's chain-value copy loop** from `sigPtr + src` to `12780(%rsp)`. -/
theorem sig_turn (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) {ds : List Directive} {jd jn : Nat}
    (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn) {lab : Label}
    (hlab : Labels.label lab = r.pc jd) (i : Reg64) (src : Nat) (hsrc : src + 1024 ≤ 7740)
    {S' : SState}
    (hx : exec ds (sigTurnS i src) =
      some (S', .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 32) (.reg i)) (.lit 1024))) lab))
    (hi : S'.reg i = some (.bin .add .W64 (.lit 32) (.reg i)))
    (hc : copies S'.mem 1 0 0 0 32 = true)
    (hw : writesIn S' 1 0 32 = true) {rs : List Reg64}
    (hk : keepsRegs rs (sigTurnS i src) S' = true) (hrsp : .rsp ∈ rs) (hrbx : .rbx ∈ rs)
    {L : List (Nat × Nat × List UInt8)} (hLa : factsApart L 12780 1024 = true)
    {P : MachineData → Prop}
    (hP : ∀ m m', (∀ x ∈ rs, m'.regs.get64 x = m.regs.get64 x) → P m → P m') {j : Nat}
    (hj : j < 32) {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem L ∧
      BytesAt m.dmem (r.off 12780) (slice r.sigB src (32 * j)) ∧
      Run.RegIs m .rbx r.sigPtr ∧ Run.RegIs m i (BitVec.ofNat 64 (32 * j)) ∧ P m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦
      (st.pc = r.pc jn ∧ r.Frame st.data ∧ Facts r st.data.dmem L ∧
        BytesAt st.data.dmem (r.off 12780) (slice r.sigB src 1024) ∧
        Run.RegIs st.data .rbx r.sigPtr ∧ P st.data) ∨
      (j + 1 < 32 ∧ st.pc = r.pc jd ∧ r.Frame st.data ∧ Facts r st.data.dmem L ∧
        BytesAt st.data.dmem (r.off 12780) (slice r.sigB src (32 * (j + 1))) ∧
        Run.RegIs st.data .rbx r.sigPtr ∧
        Run.RegIs st.data i (BitVec.ofNat 64 (32 * (j + 1))) ∧ P st.data)) ⟨m, r.pc jd⟩ := by
  obtain ⟨hF, hL, hdst, hbx, hii, hPm⟩ := h
  have hk' : ds.IsInfixAt (ElfHost.sectionProg r.sec) (r.k + jd) := hb.trans hp.1 (by rintro rfl; cases hx)
  have hwf := wfSigTurn r hpre hF.2.2.2 hF.2.2.1 (off := src + 32 * j) (d := 12780 + 32 * j)
    (by omega) (by omega) (fun _ ↦ 0) 0
  have hbx' : reg m .rbx = r.sigPtr := hbx
  have hii' : reg m i = BitVec.ofNat 64 (32 * j) := hii
  have hm : Match (Env.ofMachine m [(r.sigPtr + BitVec.ofNat 64 (src + 32 * j), 32),
      (r.off (12780 + 32 * j), 32)] (fun _ ↦ 0) 0) (sigTurnS i src) m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial
      ⟨by
        sym_simp
        simp only [Env.ofMachine_regs]
        show reg m .rbx + reg m i = r.sigPtr + BitVec.ofNat 64 (src + 32 * j) + BitVec.ofInt 64 (-(src : Int))
        rw [hbx', hii']
        refine alias_neg src ?_
        bv_lin,
      by
        sym_simp
        simp only [Env.ofMachine_regs]
        show reg m .rsp + reg m i = r.off (12780 + 32 * j) + BitVec.ofInt 64 (-((12780 : Nat) : Int))
        rw [show reg m .rsp = r.base from hF.1, hii']
        refine alias_neg 12780 ?_
        bv_lin, trivial⟩
  refine exec_then_elf hk' hx hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ ?_
  have hreg := keepsRegs_regs hm hm' hk
  obtain ⟨hF', hout⟩ := frame_of_hull r hpre hF (ri := 1) (d := 12780 + 32 * j) (lo := 0) (hi := 32)
    rfl le_rfl (Nat.zero_le _) (by omega) hm' hwf hw (by rw [rspOf, hreg .rsp hrsp]; exact hF.1)
  rw [Nat.add_zero, Nat.sub_zero] at hout
  have hL' := Facts.keep r hpre (by omega) hout hL (factsApart_mono hLa (by omega) (by omega))
  have hnew : BytesAt st.data.dmem (r.off (12780 + 32 * j)) (slice r.sigB (src + 32 * j) 32) := by
    have := copy hm' (r := 1) (o := 0) (r' := 0) (o' := 0) (n := 32)
      (bs := slice r.sigB (src + 32 * j) 32) rfl (by decide) hc
      (length_slice (by rw [r.hsig]; omega)) (by
        show BytesAt m.dmem (r.sigPtr + BitVec.ofNat 64 (src + 32 * j) + BitVec.ofNat 64 0) _
        rw [addr_add, Nat.add_zero]
        exact sig_slice r hpre hF.2.2.1 (by omega))
    rwa [off_add, Nat.add_zero] at this
  have hdst' : BytesAt st.data.dmem (r.off 12780) (slice r.sigB src (32 * (j + 1))) := by
    rw [show 32 * (j + 1) = 32 * j + 32 by omega, slice_add]
    refine BytesAt.append (fact_keep r hpre hdst hout (length_slice (by rw [r.hsig]; omega))
      (by left; omega) (by omega) (by omega)) ?_
    rw [length_slice (by rw [r.hsig]; omega), off_add]
    exact hnew
  have hv : Sym.eval (Env.ofMachine m [(r.sigPtr + BitVec.ofNat 64 (src + 32 * j), 32),
      (r.off (12780 + 32 * j), 32)] (fun _ ↦ 0) 0) (.bin .add .W64 (.lit 32) (.reg i)) =
      BitVec.ofNat 64 (32 * (j + 1)) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    show BitVec.ofNat 64 32 + reg m i = _
    rw [hii']
    bv_lin
  have hbx'' : Run.RegIs st.data .rbx r.sigPtr := (hreg .rbx hrbx).trans hbx
  have hP' := hP m st.data hreg hPm
  obtain ⟨hne, heq⟩ := pc_cond hpc hv (by omega) (by decide)
  by_cases hj1 : j + 1 < 32
  · rw [hlab] at hne
    exact .done _ (Or.inr ⟨hj1, hne (by omega), hF', hL', hdst', hbx'', (hm'.regs i _ hi).trans hv, hP'⟩)
  · obtain rfl : j = 31 := by omega
    exact .done _ (Or.inl ⟨pc_next r (heq rfl) hjn, hF', hL', hdst', hbx'', hP'⟩)

/-- **A layer's chain-value copy loop**: 32 × 32 bytes from `sigPtr + src` to `12780(%rsp)`. -/
theorem sig_loop (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) {ds : List Directive} {jd jn : Nat}
    (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn) {lab : Label}
    (hlab : Labels.label lab = r.pc jd) (i : Reg64) (src : Nat) (hsrc : src + 1024 ≤ 7740)
    {S' : SState}
    (hx : exec ds (sigTurnS i src) =
      some (S', .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 32) (.reg i)) (.lit 1024))) lab))
    (hi : S'.reg i = some (.bin .add .W64 (.lit 32) (.reg i)))
    (hc : copies S'.mem 1 0 0 0 32 = true)
    (hw : writesIn S' 1 0 32 = true) {rs : List Reg64}
    (hk : keepsRegs rs (sigTurnS i src) S' = true) (hrsp : .rsp ∈ rs) (hrbx : .rbx ∈ rs)
    {L : List (Nat × Nat × List UInt8)} (hLa : factsApart L 12780 1024 = true)
    {P : MachineData → Prop}
    (hP : ∀ m m', (∀ x ∈ rs, m'.regs.get64 x = m.regs.get64 x) → P m → P m') {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem L ∧ Run.RegIs m .rbx r.sigPtr ∧ Run.RegIs m i 0 ∧ P m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc jn ∧ r.Frame st.data ∧
      Facts r st.data.dmem L ∧ BytesAt st.data.dmem (r.off 12780) (slice r.sigB src 1024) ∧
      Run.RegIs st.data .rbx r.sigPtr ∧ P st.data) ⟨m, r.pc jd⟩ :=
  count_loop (σ := MachineState) (P := fun j st ↦ st.pc = r.pc jd ∧ r.Frame st.data ∧
      Facts r st.data.dmem L ∧ BytesAt st.data.dmem (r.off 12780) (slice r.sigB src (32 * j)) ∧
      Run.RegIs st.data .rbx r.sigPtr ∧ Run.RegIs st.data i (BitVec.ofNat 64 (32 * j)) ∧ P st.data) 32
    (fun j st hj ⟨hpc, h⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      exact sig_turn r hp hpre hb hjn hlab i src hsrc hx hi hc hw hk hrsp hrbx hLa hP hj h)
    (j := 0) (s := ⟨m, r.pc jd⟩) (by decide)
    ⟨rfl, h.1, h.2.1, fun _ hi ↦ by simp [slice] at hi, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
