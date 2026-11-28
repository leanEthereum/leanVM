module

public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.SphincsVerify.Parse.OpenTurn

/-!
# What the layers' proofs share (x86-64)

A block of the frame writing nothing but the return address's slot, then `memcpy` of known
bytes (`memcpy_pure`): the facts kept and the copied bytes. A layer's chain-value loop
(`span_loop`): 32 turns of 32 bytes from the raw signature's `src - 11404` to `20556`, the facts
and a register predicate kept.
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

variable (r : Run) [Host]

/-- **A pure block, then `memcpy(a, s, n)` of known bytes**. -/
theorem memcpy_pure (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {ds : List Directive}
    {jd jn : Nat} (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn)
    {k : List (Reg64 × Sym)} {S' : SState}
    (hx : exec ds (fS k) = some (S', .call NativeRustcX64.Common.Memcpy.entryLabel)) (hfw : Run.frameWrites S' = true)
    (hrsp : S'.reg .rsp = some (.ptr 0 (-8))) {m : MachineData} (hF : r.Frame m)
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) (r.pc jn).toBitVec)) k)
    {L : List (Nat × Nat × List UInt8)} (hL : Facts r m.dmem L) (hok : factsOK S' L = true)
    {a s n : Nat} (hap : factsApart L a n = true) {bs : List UInt8}
    (hsrc : BytesAt m.dmem (r.off s) bs) (hl : bs.length = n) (hsok : noW0 S' s n = true)
    (ha : a + n ≤ 29352) (hs : s + n ≤ 29400) (hd : a + n ≤ s ∨ s + n ≤ a)
    {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) (r.pc jn).toBitVec) S' m₁ →
      Run.RegIs m₁ .rdi (r.off a) ∧ Run.RegIs m₁ .rsi (r.off s) ∧ (reg m₁ .rdx).toNat = n ∧
      ∀ m₂, r.Frame m₂ → Saved m₁ m₂ → Facts r m₂.dmem L → BytesAt m₂.dmem (r.off a) bs →
        Eventually (step1 Host.exe) R ⟨m₂, r.pc jn⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc jd⟩ := by
  refine memcpy_block r hp hpre hc hb hjn hx hfw hrsp hF hk trivial ha hs hd fun m₁ hm₁ ↦ ?_
  obtain ⟨h0, h1, h2, hcont⟩ := h m₁ hm₁
  refine ⟨h0, h1, h2, fun m₂ hF₂ hS hB hout hc₁ ↦ hcont m₂ hF₂ hS ?_ ?_⟩
  · exact Facts.of_call r hpre hc₁ (by omega) (Nat.zero_le _) hout (Facts.of_block r rfl hm₁ hL hok)
      hap
  · have hs₁ := bytesAt_of_block r rfl hm₁ hsrc hsok hl.le (by omega)
    rwa [← hl, bytesOf_of_bytesAt hs₁] at hB

/-- **A turn of a layer's chain-value loop**. -/
theorem span_turn (hp : Placed code r.k) (hpre : r.Pre) {ds : List Directive} {jd jn : Nat}
    (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn) {lab : Label}
    (hlab : Labels.label lab = r.pc jd) (i : Reg64) (src : Nat) (hsrc : 11404 ≤ src)
    (hsrc' : src + 1024 ≤ 19144) {S' : SState}
    (hx : exec ds (spanS i (20588 - src) (-(src : Int))) =
      some (S', .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 32) (.reg i)) (.lit 1024))) lab))
    (hi : S'.reg i = some (.bin .add .W64 (.lit 32) (.reg i)))
    (hc : copies S'.mem 0 (20556 - src) 0 0 32 = true)
    (hw : writesIn S' 0 (20556 - src) (20588 - src) = true) {rs : List Reg64}
    (hk : keepsRegs rs (spanS i (20588 - src) (-(src : Int))) S' = true) (hrsp : .rsp ∈ rs)
    {L : List (Nat × Nat × List UInt8)} (hLa : factsApart L 20556 1024 = true)
    (hraw : (11404, 7740, sigBytes r.w) ∈ L) {P : MachineData → Prop}
    (hP : ∀ m m', (∀ x ∈ rs, m'.regs.get64 x = m.regs.get64 x) → P m → P m') {j : Nat}
    (hj : j < 32) {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem L ∧
      BytesAt m.dmem (r.off 20556) (slice (sigBytes r.w) (src - 11404) (32 * j)) ∧
      Run.RegIs m i (BitVec.ofNat 64 (32 * j)) ∧ P m) :
    Eventually (step1 Host.exe) (fun st ↦
      (st.pc = r.pc jn ∧ r.Frame st.data ∧ Facts r st.data.dmem L ∧
        BytesAt st.data.dmem (r.off 20556) (slice (sigBytes r.w) (src - 11404) 1024) ∧ P st.data) ∨
      (j + 1 < 32 ∧ st.pc = r.pc jd ∧ r.Frame st.data ∧ Facts r st.data.dmem L ∧
        BytesAt st.data.dmem (r.off 20556) (slice (sigBytes r.w) (src - 11404) (32 * (j + 1))) ∧
        Run.RegIs st.data i (BitVec.ofNat 64 (32 * (j + 1))) ∧ P st.data)) ⟨m, r.pc jd⟩ := by
  obtain ⟨hF, hL, hdst, hii, hPm⟩ := h
  have hk' : ds.IsInfixAt Host.prog (r.k + jd) := hb.trans hp.1 (by rintro rfl; cases hx)
  have hb0 := r.base_toNat hpre
  have hwf : (Env.ofMachine m [(r.off (src + 32 * j), 20588 - src)] (fun _ ↦ 0) 0).WF :=
    Sym.Env.wf_of ⟨r.frame_mapped hpre hF.2.2.2 (by omega), trivial⟩ (List.pairwise_singleton _ _)
  have hii' : reg m i = BitVec.ofNat 64 (32 * j) := hii
  have hm : Match (Env.ofMachine m [(r.off (src + 32 * j), 20588 - src)] (fun _ ↦ 0) 0)
      (spanS i (20588 - src) (-(src : Int))) m :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial
      ⟨by
        sym_simp
        simp only [Env.ofMachine_regs]
        show reg m .rsp + reg m i = r.off (src + 32 * j) + BitVec.ofInt 64 (-(src : Int))
        rw [show reg m .rsp = r.base from hF.1, hii']
        refine alias_neg src ?_
        bv_lin, trivial⟩
  refine exec_then hk' hx hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ ?_
  have hreg := keepsRegs_regs hm hm' hk
  obtain ⟨hF', hout⟩ := frame_of_hull r hpre hF (ri := 0) (d := src + 32 * j) (lo := 20556 - src)
    (hi := 20588 - src) rfl le_rfl (by omega) (by omega) hm' hwf hw
    (by rw [rspOf, hreg .rsp hrsp]; exact hF.1)
  rw [show src + 32 * j + (20556 - src) = 20556 + 32 * j by omega,
    show 20588 - src - (20556 - src) = 32 by omega] at hout
  have hL' := Facts.keep r hpre (by omega) hout hL (factsApart_mono hLa (by omega) (by omega))
  have hnew : BytesAt st.data.dmem (r.off (20556 + 32 * j))
      (slice (sigBytes r.w) (src - 11404 + 32 * j) 32) := by
    have := copy hm' (r := 0) (o := 20556 - src) (r' := 0) (o' := 0) (n := 32) rfl (by omega) hc
      (length_slice_sig r.w (a := src - 11404 + 32 * j) (n := 32) (by omega)) (by
        show BytesAt m.dmem (r.off (src + 32 * j) + BitVec.ofNat 64 0) _
        rw [off_add, Nat.add_zero, show src + 32 * j = 11404 + (src - 11404 + 32 * j) by omega]
        exact raw_slice r (hL.get hraw) (k := src - 11404 + 32 * j) (n := 32) (by omega))
    rwa [off_add, show src + 32 * j + (20556 - src) = 20556 + 32 * j by omega] at this
  have hdst' : BytesAt st.data.dmem (r.off 20556)
      (slice (sigBytes r.w) (src - 11404) (32 * (j + 1))) := by
    rw [show 32 * (j + 1) = 32 * j + 32 by omega, slice_add]
    refine BytesAt.append (fact_keep r hpre hdst hout (length_slice_sig r.w (by omega))
      (by left; omega) (by omega) (by omega)) ?_
    rw [length_slice_sig r.w (by omega), off_add]
    exact hnew
  have hv : Sym.eval (Env.ofMachine m [(r.off (src + 32 * j), 20588 - src)] (fun _ ↦ 0) 0)
      (.bin .add .W64 (.lit 32) (.reg i)) = BitVec.ofNat 64 (32 * (j + 1)) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    show BitVec.ofNat 64 32 + reg m i = _
    rw [hii']
    bv_lin
  have hP' := hP m st.data hreg hPm
  obtain ⟨hne, heq⟩ := pc_cond hpc hv (by omega) (by decide)
  by_cases hj1 : j + 1 < 32
  · rw [hlab] at hne
    exact .done _ (Or.inr ⟨hj1, hne (by omega), hF', hL', hdst', (hm'.regs i _ hi).trans hv, hP'⟩)
  · obtain rfl : j = 31 := by omega
    exact .done _ (Or.inl ⟨pc_next r (heq rfl) hjn, hF', hL', hdst', hP'⟩)

/-- **A layer's chain-value loop**. -/
theorem span_loop (hp : Placed code r.k) (hpre : r.Pre) {ds : List Directive} {jd jn : Nat}
    (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn) {lab : Label}
    (hlab : Labels.label lab = r.pc jd) (i : Reg64) (src : Nat) (hsrc : 11404 ≤ src)
    (hsrc' : src + 1024 ≤ 19144) {S' : SState}
    (hx : exec ds (spanS i (20588 - src) (-(src : Int))) =
      some (S', .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 32) (.reg i)) (.lit 1024))) lab))
    (hi : S'.reg i = some (.bin .add .W64 (.lit 32) (.reg i)))
    (hc : copies S'.mem 0 (20556 - src) 0 0 32 = true)
    (hw : writesIn S' 0 (20556 - src) (20588 - src) = true) {rs : List Reg64}
    (hk : keepsRegs rs (spanS i (20588 - src) (-(src : Int))) S' = true) (hrsp : .rsp ∈ rs)
    {L : List (Nat × Nat × List UInt8)} (hLa : factsApart L 20556 1024 = true)
    (hraw : (11404, 7740, sigBytes r.w) ∈ L) {P : MachineData → Prop}
    (hP : ∀ m m', (∀ x ∈ rs, m'.regs.get64 x = m.regs.get64 x) → P m → P m') {m : MachineData}
    (h : r.Frame m ∧ Facts r m.dmem L ∧ Run.RegIs m i 0 ∧ P m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc jn ∧ r.Frame st.data ∧
      Facts r st.data.dmem L ∧
      BytesAt st.data.dmem (r.off 20556) (slice (sigBytes r.w) (src - 11404) 1024) ∧ P st.data)
      ⟨m, r.pc jd⟩ :=
  count_loop (σ := MachineState) (P := fun j st ↦ st.pc = r.pc jd ∧ r.Frame st.data ∧
      Facts r st.data.dmem L ∧
      BytesAt st.data.dmem (r.off 20556) (slice (sigBytes r.w) (src - 11404) (32 * j)) ∧
      Run.RegIs st.data i (BitVec.ofNat 64 (32 * j)) ∧ P st.data) 32
    (fun j st hj ⟨hpc, h⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      exact span_turn r hp hpre hb hjn hlab i src hsrc hsrc' hx hi hc hw hk hrsp hLa hraw hP hj h)
    (j := 0) (s := ⟨m, r.pc jd⟩) (by decide)
    ⟨rfl, h.1, h.2.1, fun _ hi ↦ by simp [slice] at hi, h.2.2.1, h.2.2.2⟩

end

end NativeRustcX64.SphincsVerifyProof.Parse
