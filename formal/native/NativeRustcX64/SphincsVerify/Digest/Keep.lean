module

public import NativeRustcX64.SphincsVerify.Calls
public import NativeRustc.Sphincs.SigMem
public import NativeRustcX64.SphincsVerify.Digest.State

/-!
# What the digest and the FORS key keep, and their steps (x86-64)

The digest and the FORS key write only the frame's scratch (`Scratch`: from `192`, off the parsed
signature at `20556 .. 28296`, below the saved registers) and the small spills below the key
(`60`, `80`), and the slots below the frame (`call`'s return address). The frame's invariant, the
inputs (the key at `112`, the parsed signature at `20556`) and the first layer's chain values'
address at `184` stay (`Keep`): through a call changing scratch (`Keep.of_call`), through a block
whose writes miss them (`keepOK`, `Keep.of_block`, `Keep.of_call_block`).

A block run by the executor from the frame's symbolic state (`frameS k`, the registers `k`
known, `KnownOK`) then its callee's contract (`Run.frameCall`), or a block falling through
(`Run.frameFall`), take the machine from one block's start to the next's; the frame's bytes the
block did not write are kept (`KB`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym

@[expose] public section

theorem length_pkBytes (r : Run) : r.pkB.length = 32 := r.hpk

theorem length_sigMem' (r : Run) : (sigMem r.sig).length = 7740 := SigMemBytes.length_sigMem r.sigB r.hsig

/-- **What the digest keeps**: the frame, the inputs, the first layer's chain values' address. -/
def Keep (r : Run) (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ r.WordAt m 184 (r.addr 17436)

/-- The frame's scratch bytes `a .. a + n` the digest's calls change. -/
def Scratch (a n : Nat) : Prop :=
  (192 ≤ a ∧ a + n ≤ 12780) ∨ (20520 ≤ a ∧ a + n ≤ 21576)

/-- A block's literal state keeps what the digest keeps: its writes in the frame below the saved
registers or the slots below it, off the key, the parsed signature and `184`. -/
def keepOK (S : SState) : Bool :=
  Run.frameWrites S && Run.noWriteIn S 112 32 && Run.noWriteIn S 184 8 &&
    Run.noWriteIn S 12780 7740

/-- The frame's bytes a block from `m` to `m₁` (literal state `S`) did not write are kept. -/
def KB (r : Run) (S : SState) (m m₁ : MachineData) : Prop :=
  ∀ o (bs : List UInt8), o + bs.length ≤ 21624 → Run.noWriteIn S o bs.length = true →
    BytesAt m.dmem (r.off o) bs → BytesAt m₁.dmem (r.off o) bs

/-- The frame's bytes apart from `a .. a + n` are kept from `m₁` to `m₂`. -/
def KC (r : Run) (m₁ m₂ : MachineData) (a n : Nat) : Prop :=
  ∀ o (bs : List UInt8), o + bs.length ≤ 21624 → (o + bs.length ≤ a ∨ a + n ≤ o) →
    BytesAt m₁.dmem (r.off o) bs → BytesAt m₂.dmem (r.off o) bs

/-- The known registers of `frameS k` hold their values. -/
def KnownOK [Labels] (r : Run) (m : MachineData) (ret : BitVec 64) (k : List (Reg64 × Sym)) :
    Prop :=
  AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) ret)) k

end

public section

section
variable {r : Run} [Labels]

omit [Labels] in
/-- No write of `S` in the frame's bytes `o .. o + n` is none in a part. -/
theorem noWriteIn_mono {S : SState} {o n o' n' : Nat} (h : Run.noWriteIn S o n = true)
    (h1 : o ≤ o') (h2 : o' + n' ≤ o + n) : Run.noWriteIn S o' n' = true := by
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  intro w hw
  rcases h w hw with ⟨h0, h⟩ | h
  · exact .inl ⟨h0, by omega⟩
  · exact .inr h

omit [Labels] in
/-- A callee-saved register stays through a call. -/
theorem regIs_of_saved {m m' : MachineData} (hS : Saved m m') {y : Reg64} {v : BitVec 64}
    (hy : calleeSaved y = true) (h : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs at *
  rw [show reg m' y = reg m y from hS.1 y hy]
  exact h

/-- **A call changing scratch keeps what the digest keeps.** -/
theorem Keep.of_call (hpre : r.Pre) {m m' : MachineData} (hc : r.AtCall m) (hI : r.Inputs m)
    (h176 : r.WordAt m 184 (r.addr 17436)) (hS : Saved m m') (hsp : rspOf m' = rspOf m + 8#64)
    {a n N : Nat} (ha : Scratch a n) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : Keep r m' := by
  obtain ⟨h1, h2⟩ := hI
  unfold Scratch at ha
  have hk : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 192 ∨
      (12780 ≤ o ∧ o + bs.length ≤ 20520) → BytesAt m.dmem (r.off o) bs →
      BytesAt m'.dmem (r.off o) bs := fun ho h ↦
    r.bytesAt_of_call hpre hc (by omega) hN hout (by omega) (by omega) h
  refine ⟨r.frame_of_call hpre hc hS hsp (by omega) hN hout, ⟨hk ?_ h1, hk ?_ h2⟩, hk ?_ h176⟩ <;>
    simp only [length_pkBytes, length_sigMem', NativeRustc.length_wordBytes] <;> omega

/-- **A block whose writes miss the kept bytes**: the inputs and `184` kept. -/
theorem inputs_of_block (hpre : r.Pre) {m m' : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m (fun _ ↦ 0) ret) S m') (hwf : (r.env m (fun _ ↦ 0) ret).WF)
    (hok : keepOK S = true) (hI : r.Inputs m) (h176 : r.WordAt m 184 (r.addr 17436)) :
    r.Inputs m' ∧ r.WordAt m' 184 (r.addr 17436) := by
  simp only [keepOK, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨-, n1⟩, n2⟩, n3⟩ := hok
  refine ⟨⟨r.bytesAt_kept hpre hm hwf (by rw [length_pkBytes]; omega) hI.1
      (by rw [length_pkBytes]; exact n1),
    r.bytesAt_kept hpre hm hwf (by rw [length_sigMem']; omega) hI.2
      (by rw [length_sigMem']; exact n3)⟩,
    r.bytesAt_kept hpre hm hwf (by rw [NativeRustc.length_wordBytes]; omega) h176
      (by rw [NativeRustc.length_wordBytes]; exact n2)⟩

theorem eval_ptr0 (m : MachineData) (vars : Nat → BitVec 64) (ret : BitVec 64) (o : Nat) :
    (Sym.ptr 0 o).eval (r.env m vars ret) = r.off o := by
  simp only [Sym.eval, Run.off, BitVec.ofInt_natCast]
  rfl

/-- **A register the block sets to the frame's byte `o`.** -/
theorem regIs_ptr {m m' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m vars ret) S m') {y : Reg64} {o : Nat} (h : S.reg y = some (.ptr 0 o)) :
    Run.RegIs m' y (r.off o) := by
  unfold Run.RegIs
  rw [show reg m' y = _ from hm.regs y _ h, eval_ptr0]

/-- **A register the block sets to a literal.** -/
theorem regIs_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : Reg64}
    {c : Nat} (h : S.reg y = some (.lit c)) : Run.RegIs m' y (BitVec.ofNat 64 c) := by
  unfold Run.RegIs
  rw [show reg m' y = _ from hm.regs y _ h]
  rfl

/-- **A register the block keeps.** -/
theorem regIs_keep {m m' : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m regions vars ret) S m') {y : Reg64} {v : BitVec 64}
    (h : S.reg y = some (.reg y)) (hv : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs at *
  rw [show reg m' y = _ from hm.regs y _ h]
  exact hv

/-- RDX a literal `c < 2 ^ 64`: its value. -/
theorem rdx_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {c : Nat}
    (h : S.reg .rdx = some (.lit c)) (hc : c < 2 ^ 64) : (reg m' .rdx).toNat = c := by
  have := regIs_lit hm h
  unfold Run.RegIs at this
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem knownOK_nil (m : MachineData) (ret : BitVec 64) : KnownOK r m ret [] := trivial

theorem knownOK_ptr {m : MachineData} {ret : BitVec 64} {y : Reg64} {o : Nat}
    {k : List (Reg64 × Sym)} (h : Run.RegIs m y (r.off o)) (hk : KnownOK r m ret k) :
    KnownOK r m ret ((y, .ptr 0 o) :: k) :=
  ⟨by show _ = (Sym.ptr 0 o).eval (r.env m (fun _ ↦ 0) ret); rw [eval_ptr0]; exact h, hk⟩

theorem knownOK_lit {m : MachineData} {ret : BitVec 64} {y : Reg64} {c : Nat}
    {k : List (Reg64 × Sym)} (h : Run.RegIs m y (BitVec.ofNat 64 c)) (hk : KnownOK r m ret k) :
    KnownOK r m ret ((y, .lit c) :: k) :=
  ⟨h, hk⟩

theorem knownOK_reg {m : MachineData} {ret : BitVec 64} {y : Reg64} {k : List (Reg64 × Sym)}
    (hk : KnownOK r m ret k) : KnownOK r m ret ((y, .reg y) :: k) :=
  ⟨rfl, hk⟩

/-- The frame's symbolic state for a state of the frame. -/
theorem Run.frame_match (r : Run) (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {ret : BitVec 64}
    {k : List (Reg64 × Sym)} (hk : KnownOK r m ret k) :
    Match (r.env m (fun _ ↦ 0) ret) (frameS k) m :=
  r.match_frame hpre hF hk trivial trivial trivial

omit [Labels] in
/-- **Bytes in memory, two pieces.** -/
theorem bytesAt_append {d : DataMem} {a : BitVec 64} {xs ys : List UInt8} (hx : BytesAt d a xs)
    (hy : BytesAt d (a + BitVec.ofNat 64 xs.length) ys) : BytesAt d a (xs ++ ys) := by
  intro i hi
  by_cases h : i < xs.length
  · rw [List.getElem_append_left h]
    exact hx i h
  · rw [List.getElem_append_right (by omega)]
    have := hy (i - xs.length) (by simp at hi; omega)
    rwa [addr_add, Nat.add_sub_cancel' (by omega)] at this

omit [Labels] in
/-- The frame's bytes `xs` at `o`, `ys` right after. -/
theorem bytesAt_cat {d : DataMem} {o k o' : Nat} {xs ys : List UInt8}
    (hx : BytesAt d (r.off o) xs) (hl : xs.length = k) (ho : o + k = o')
    (hy : BytesAt d (r.off o') ys) : BytesAt d (r.off o) (xs ++ ys) :=
  bytesAt_append hx (by rw [Run.off_add, hl, ho]; exact hy)

end

/-! ## Steps -/

variable [ElfHost]

/-- From one block's start in a state `P` to another's, then on. -/
theorem Run.stage (r : Run) {j : Nat} {P : MachineData → Prop} {s : MachineState}
    {R : MachineState → Prop}
    (h : Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc j ∧ P st.data) s)
    (k : ∀ m, P m → Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩) :
    Eventually (elfStep1 ElfHost.exe) R s :=
  Eventually.bind_elf h fun ⟨m, pc⟩ ⟨hpc, hP⟩ ↦ by
    simp only at hpc
    subst hpc
    exact k m hP

/-- **A block of the frame, then its callee**: the callee entered at a call (`AtCall`), what the
digest keeps there, its return at the block's end `j'` RSP 8 above. -/
theorem Run.frameCall (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {ds : List Directive} {j j' : Nat} (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    (hj : j + ds.length = j') {k : List (Reg64 × Sym)} {S' : SState} {l : Label}
    (hx : exec ds (frameS k) = some (S', .call l)) (hok : keepOK S' = true)
    (hrsp : S'.reg .rsp = some (.ptr 0 (-8)))
    {m : MachineData} (hK : Keep r m) (hk : KnownOK r m (r.pc j').toBitVec k)
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : ElfSpec (Labels.label l) P Q) {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) (r.pc j').toBitVec) S' m₁ → r.AtCall m₁ →
      r.Inputs m₁ → r.WordAt m₁ 184 (r.addr 17436) → KB r S' m m₁ → P m₁ ∧
      ∀ m₂, rspOf m₂ = rspOf m₁ + 8#64 → Q m₁ m₂ →
        Eventually (elfStep1 ElfHost.exe) R ⟨m₂, r.pc j'⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc j').toBitVec
  have hk' := hb.trans hp.1 (by rintro rfl; cases hx)
  refine exec_then_elf hk' hx hwf (fun _ _ ↦ by show (r.pc j').toBitVec = _; rw [Run.pc, ← hj, Nat.add_assoc])
    (Run.frame_match r hpre hK.1 hk) fun st hm₁ hpc ↦ ?_
  have hok' := hok
  simp only [keepOK, Bool.and_eq_true] at hok'
  have hc := Run.AtCall.of_match r hpre hK.1 hm₁ hwf hrsp hok'.1.1.1
  obtain ⟨hI, h176⟩ := inputs_of_block hpre hm₁ hwf hok hK.2.1 hK.2.2
  obtain ⟨hP, hc'⟩ := h st.data hm₁ hc hI h176
    fun _ _ ho hn hb ↦ r.bytesAt_kept hpre hm₁ hwf ho hb hn
  refine call_then_elf hpc hspec hP fun st' hpc' hsp hq ↦ ?_
  obtain ⟨m₂, pc⟩ := st'
  simp only at hpc'
  subst hpc'
  rw [Nat.add_assoc, hj]
  exact hc' m₂ hsp hq

/-- **A block of the frame falling through** to directive `j'`. -/
theorem Run.frameFall (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {ds : List Directive} {j j' : Nat} (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    (hj : j + ds.length = j') (hne : ds ≠ []) {k : List (Reg64 × Sym)} {S' : SState}
    (hx : exec ds (frameS k) = some (S', .fall)) (hok : keepOK S' = true)
    (hrsp : S'.reg .rsp = some (.ptr 0 0)) {m : MachineData} (hK : Keep r m)
    (hk : KnownOK r m 0 k) {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) 0) S' m₁ → Keep r m₁ → KB r S' m m₁ →
      Eventually (elfStep1 ElfHost.exe) R ⟨m₁, r.pc j'⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) 0
  have hk' := hb.trans hp.1 hne
  refine exec_then_elf hk' hx hwf (fun _ h ↦ nomatch h) (Run.frame_match r hpre hK.1 hk)
    fun st hm₁ hpc ↦ ?_
  obtain ⟨m₁, pc⟩ := st
  simp only [PcOk] at hpc
  subst hpc
  have hok' := hok
  simp only [keepOK, Bool.and_eq_true] at hok'
  obtain ⟨hI, h176⟩ := inputs_of_block hpre hm₁ hwf hok hK.2.1 hK.2.2
  rw [show ElfHost.addrOf r.sec (r.k + j + ds.length) = r.pc j' by rw [Run.pc, Nat.add_assoc, hj]]
  exact h m₁ hm₁ ⟨Run.Frame.of_match r hpre hK.1 hm₁ hwf hrsp hok'.1.1.1, hI, h176⟩
    fun _ _ ho hn hb ↦ r.bytesAt_kept hpre hm₁ hwf ho hb hn

/-- **A label of the function** is the address of the block it starts. -/
theorem Run.label_of_block (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k)
    {b : List Directive} {j : Nat} (hb : b.IsInfixAt Sphincs.SphincsVerify.code j) {l : Label}
    {b' : List Directive} (h : b = .label l :: b') : Labels.label l = r.pc j := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

end

end NativeRustcX64.SphincsVerifyProof.Digest
