module

public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names

public import NativeRustcX64.SphincsVerify.Parse.Env

/-!
# A block of the frame ending in `memcpy` or `memset` (x86-64)

`memcpy_block`, `memcpy_block_sig`, `memset_block`: execute a block in `fS` or `fSig` ending in
a call to `memcpy` or `memset`, discharge the callee contract, and continue at the return address.
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

public section

theorem noW0_mono {S : SState} {o n o' n' : Nat} (h : noW0 S o n = true) (h1 : o ≤ o')
    (h2 : o' + n' ≤ o + n) : noW0 S o' n' = true := by
  simp only [noW0, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h ⊢
  intro w hw
  rcases h w hw with (h | h) | h
  · exact .inl (.inl h)
  · exact .inl (.inr (by omega))
  · exact .inr (by omega)

/-- **Frame bytes kept by a block** of an environment whose region 0 is the frame, which does not
write them. -/
theorem bytesAt_of_block (r : Run) [Labels] {m m' : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hb : regions[0]? = some (r.base, 21632))
    {S' : SState} (hm' : Match (Env.ofMachine m regions vars ret) S' m') {o N : Nat}
    {bs : List UInt8} (h : BytesAt m.dmem (r.off o) bs) (hn : noW0 S' o N = true)
    (hl : bs.length ≤ N) (ho : o + N ≤ 21624) : BytesAt m'.dmem (r.off o) bs := by
  have := Facts.of_block r (L := [(o, bs.length, bs)]) hb hm' ⟨⟨rfl, h⟩, trivial⟩ (by
    simp only [factsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨by omega, noW0_mono hn le_rfl (by omega)⟩)
  exact this.1.2

variable (r : Run) [Host]

/-- **A block of the frame, then `memcpy(a, s, n)`**. -/
theorem memcpy_block (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {ds : List Directive}
    {jd jn : Nat} (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn)
    {k : List (Reg64 × Sym)} {bd : List (Sym × Nat)} {S' : SState}
    (hx : exec ds (fS k bd) = some (S', .call NativeRustcX64.Common.Memcpy.entryLabel)) (hfw : Run.frameWrites S' = true)
    (hrsp : S'.reg .rsp = some (.ptr 0 (-8))) {m : MachineData} (hF : r.Frame m)
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) (r.pc jn).toBitVec)) k)
    (hbd : AllOf (fun p ↦ (p.1.eval (r.env m (fun _ ↦ 0) (r.pc jn).toBitVec)).toNat < p.2) bd)
    {a s n : Nat} (ha : a + n ≤ 21576) (hs : s + n ≤ 21624) (hd : a + n ≤ s ∨ s + n ≤ a)
    {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) (r.pc jn).toBitVec) S' m₁ →
      Run.RegIs m₁ .rdi (r.off a) ∧ Run.RegIs m₁ .rsi (r.off s) ∧ (reg m₁ .rdx).toNat = n ∧
      ∀ m₂, r.Frame m₂ → Saved m₁ m₂ → BytesAt m₂.dmem (r.off a) (bytesOf m₁.dmem (r.off s) n) →
        SameOutside m₁.dmem m₂.dmem (r.CallOut m₁ a n 0) → r.AtCall m₁ →
        Eventually (step1 Host.exe) R ⟨m₂, r.pc jn⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc jd⟩ := by
  have hwf := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) (r.pc jn).toBitVec
  have hk' : ds.IsInfixAt Host.prog (r.k + jd) := hb.trans hp.1 (by rintro rfl; cases hx)
  refine exec_then hk' hx hwf (fun _ _ ↦ by rw [← hjn, Nat.add_assoc]; rfl)
    (r.match_frame hpre hF hk trivial hbd trivial) fun st hm₁ hpc ↦ ?_
  have hc₁ := Run.AtCall.of_match r hpre hF hm₁ hwf hrsp hfw
  obtain ⟨h0, h1, h2, hcont⟩ := h st.data hm₁
  refine call_then hpc hc.1 (r.memcpy_pre hpre hc₁ h0 h1 h2 (by omega) hs hd)
    fun st₂ hpc₂ hsp₂ hQ ↦ ?_
  obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 hQ
  obtain ⟨m₂, pc⟩ := st₂
  simp only at hpc₂
  subst hpc₂
  rw [Nat.add_assoc, hjn]
  exact hcont m₂ (r.frame_of_call hpre hc₁ hS hsp₂ ha (Nat.zero_le _) hout) hS hB hout hc₁

/-- **A block reading `sigPtr` (`fSig`), then `memcpy(a, s, n)`**. -/
theorem memcpy_block_sig (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {ds : List Directive}
    {jd jn : Nat} (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn)
    {k : List (Reg64 × Sym)} {S' : SState}
    (hx : exec ds (fSig k) = some (S', .call NativeRustcX64.Common.Memcpy.entryLabel))
    (hfw : Run.frameWrites S' = true) (hrsp : S'.reg .rsp = some (.ptr 0 (-8)))
    {m : MachineData} (hF : r.Frame m) (hrbx : Run.RegIs m .rbx r.sigPtr)
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (Env.ofMachine m (regsSig r) (fun _ ↦ 0) (r.pc jn).toBitVec)) k)
    {a s n : Nat} (ha : a + n ≤ 21576) (hs : s + n ≤ 21624) (hd : a + n ≤ s ∨ s + n ≤ a)
    {R : MachineState → Prop}
    (h : ∀ m₁, Match (Env.ofMachine m (regsSig r) (fun _ ↦ 0) (r.pc jn).toBitVec) S' m₁ →
      Run.RegIs m₁ .rdi (r.off a) ∧ Run.RegIs m₁ .rsi (r.off s) ∧ (reg m₁ .rdx).toNat = n ∧
      ∀ m₂, r.Frame m₂ → Saved m₁ m₂ → BytesAt m₂.dmem (r.off a) (bytesOf m₁.dmem (r.off s) n) →
        SameOutside m₁.dmem m₂.dmem (r.CallOut m₁ a n 0) → r.AtCall m₁ →
        Eventually (step1 Host.exe) R ⟨m₂, r.pc jn⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc jd⟩ := by
  have hwf := wfSig r hpre hF.2.2.2 hF.2.2.1 (fun _ ↦ 0) (r.pc jn).toBitVec
  have hk' : ds.IsInfixAt Host.prog (r.k + jd) := hb.trans hp.1 (by rintro rfl; cases hx)
  refine exec_then hk' hx hwf (fun _ _ ↦ by rw [← hjn, Nat.add_assoc]; rfl)
    (match_sig r hpre hF hrbx hk) fun st hm₁ hpc ↦ ?_
  have hc₁ := atCall_of_block r hpre hF rfl rfl hm₁ hwf hrsp hfw
  obtain ⟨h0, h1, h2, hcont⟩ := h st.data hm₁
  refine call_then hpc hc.1 (r.memcpy_pre hpre hc₁ h0 h1 h2 (by omega) hs hd)
    fun st₂ hpc₂ hsp₂ hQ ↦ ?_
  obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 hQ
  obtain ⟨m₂, pc⟩ := st₂
  simp only at hpc₂
  subst hpc₂
  rw [Nat.add_assoc, hjn]
  exact hcont m₂ (r.frame_of_call hpre hc₁ hS hsp₂ ha (Nat.zero_le _) hout) hS hB hout hc₁

/-- **A block of the frame, then `memset(a, 0, n)`**. -/
theorem memset_block (hp : Placed code r.k) (hpre : r.Pre) (hc : Callees) {ds : List Directive}
    {jd jn : Nat} (hb : ds.IsInfixAt code jd) (hjn : jd + ds.length = jn)
    {k : List (Reg64 × Sym)} {S' : SState}
    (hx : exec ds (fS k) = some (S', .call NativeRustcX64.Common.Memset.entryLabel)) (hfw : Run.frameWrites S' = true)
    (hrsp : S'.reg .rsp = some (.ptr 0 (-8))) {m : MachineData} (hF : r.Frame m)
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) (r.pc jn).toBitVec)) k)
    {a n : Nat} (ha : a + n ≤ 21576) {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) (r.pc jn).toBitVec) S' m₁ →
      Run.RegIs m₁ .rdi (r.off a) ∧ (reg m₁ .rdx).toNat = n ∧
      ∀ m₂, r.Frame m₂ → Saved m₁ m₂ → SameOutside m₁.dmem m₂.dmem (r.CallOut m₁ a n 0) →
        r.AtCall m₁ → Eventually (step1 Host.exe) R ⟨m₂, r.pc jn⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc jd⟩ := by
  have hwf := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) (r.pc jn).toBitVec
  have hk' : ds.IsInfixAt Host.prog (r.k + jd) := hb.trans hp.1 (by rintro rfl; cases hx)
  refine exec_then hk' hx hwf (fun _ _ ↦ by rw [← hjn, Nat.add_assoc]; rfl)
    (r.match_frame hpre hF hk trivial trivial trivial) fun st hm₁ hpc ↦ ?_
  have hc₁ := Run.AtCall.of_match r hpre hF hm₁ hwf hrsp hfw
  obtain ⟨h0, h2, hcont⟩ := h st.data hm₁
  refine call_then hpc hc.2.1 (r.memset_pre hpre hc₁ h0 h2 (by omega)) fun st₂ hpc₂ hsp₂ hQ ↦ ?_
  obtain ⟨-, hout, hS⟩ := r.memset_out h0 h2 hQ
  obtain ⟨m₂, pc⟩ := st₂
  simp only at hpc₂
  subst hpc₂
  rw [Nat.add_assoc, hjn]
  exact hcont m₂ (r.frame_of_call hpre hc₁ hS hsp₂ ha (Nat.zero_le _) hout) hS hout hc₁

/-- A frame pointer the block sets (for any environment whose region 0 is `r.base`). -/
theorem regIs_ptr0 {m m' : MachineData} {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {n : Nat} (hb : regions[0]? = some (r.base, n))
    (hm : Match (Env.ofMachine m regions vars ret) S m') {y : Reg64} {o : Nat}
    (h : S.reg y = some (.ptr 0 o)) : Run.RegIs m' y (r.off o) :=
  (hm.regs y _ h).trans (eval_base r hb o)

/-- RDX a literal. -/
theorem rdx_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {c : Nat}
    (h : S.reg .rdx = some (.lit c)) (hc : c < 2 ^ 64) : (reg m' .rdx).toNat = c := by
  rw [show reg m' .rdx = _ from hm.regs .rdx _ h]
  simp only [Sym.eval, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hc

end

end NativeRustcX64.SphincsVerifyProof.Parse
