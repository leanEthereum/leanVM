module

public import NativeRustcArm.SphincsVerify.Calls
public import NativeRustcArm.SphincsVerify.SigMem

/-!
# What the digest and the FORS key keep, and their steps

The digest and the FORS key write only the frame's scratch from byte `15984` on (the hashers,
the hash inputs and outputs, the leaves, the roots, `signed`) and, at the FORS key's end, the
layer loop's spill at `0`. The frame's bytes below `15984` (the spills, the message, the key, the
parsed signature) stay through a call changing scratch (`Run.low_of_call`) and through a block
whose writes miss them (`Run.low_of_block`); so do the frame's invariant and the inputs
(`Keep`). A block run by the executor then its callee's contract (`Run.callStep`), or a block
falling through (`Run.fallStep`), take the machine from one block's start to the next's.
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

@[expose] public section

theorem length_pkBytes (w : Nat → UInt64) : (pkBytes w).length = 32 := by
  simp [pkBytes, Native.Keccak.Proof.length_wordsBytes]

/-- **What the digest keeps**: the frame, the inputs, the first layer's address at `392`. -/
def Keep (r : Run) (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ r.WordAt m 392 (r.addr 12900)

/-- The frame's scratch bytes `a .. a + n` the digest changes. -/
def Scratch (a n : Nat) : Prop := 15984 ≤ a ∧ a + n ≤ 29280

section
variable {r : Run} [Labels]

/-- **A frame byte below `15984` stays through a call changing scratch.** -/
theorem low_of_call (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {a n N : Nat}
    (ha : Scratch a n) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 15984) (h : BytesAt m.dmem (r.off o) bs) : BytesAt m'.dmem (r.off o) bs :=
  r.bytesAt_of_call hpre hF (by unfold Scratch at ha; omega) hN hout (by omega)
    (by unfold Scratch at ha; omega) h

omit [Labels] in
/-- A callee-saved register stays through a call. -/
theorem regIs_of_saved {m m' : MachineData} (hS : Saved m m') {y : XReg} {v : BitVec 64}
    (hy : calleeSaved y = true) (h : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs at *
  rw [hS.1 _ hy]
  exact h

/-- **A call changing scratch keeps what the digest keeps.** -/
theorem Keep.of_call (hpre : r.Pre) {m m' : MachineData} (hK : Keep r m) (hS : Saved m m')
    {a n N : Nat} (ha : Scratch a n) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : Keep r m' := by
  obtain ⟨hF, ⟨h1, h2, h3⟩, h4⟩ := hK
  have hk := fun {o} {bs} ho h ↦ low_of_call (o := o) (bs := bs) hpre hF ha hN hout ho h
  refine ⟨r.frame_of_call hpre hF hS (by unfold Scratch at ha; omega) hN hout,
    ⟨hk ?_ h1, hk ?_ h2, hk ?_ h3⟩, hk ?_ h4⟩ <;>
    simp only [length_pkBytes, r.length_sigMem, NativeRustc.length_wordBytes] <;> omega

omit [Labels] in
/-- No write of `S` in the region-0 bytes `o .. o + n` (`Run.noWriteIn`) is none in a part. -/
theorem noWriteIn_mono {S : SState} {o n o' n' : Nat} (h : Run.noWriteIn S o n = true)
    (h1 : o ≤ o') (h2 : o' + n' ≤ o + n) : Run.noWriteIn S o' n' = true := by
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h ⊢
  intro w hw
  have := h w hw
  omega

/-- A block's literal state keeps what the digest keeps: its writes in the frame's scratch, SP
and X29 as they were. -/
def keepOK (S : SState) : Bool :=
  Run.frameWrites S && Run.noWriteIn S 0 15984 && S.sp == .ptr 0 0 &&
    S.reg .X29 == some (.ptr 0 29280)

/-- **A frame byte below `15984` stays through a block** whose writes miss it. -/
theorem low_of_block (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF) (hok : keepOK S = true)
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 15984) (h : BytesAt m.dmem (r.off o) bs) :
    BytesAt m'.dmem (r.off o) bs := by
  simp only [keepOK, Bool.and_eq_true, beq_iff_eq] at hok
  exact r.bytesAt_kept hpre hm hwf (by omega) h (noWriteIn_mono hok.1.1.2 (by omega) ho)

/-- **A block whose writes miss the kept bytes keeps what the digest keeps.** -/
theorem Keep.of_block (hpre : r.Pre) {m m' : MachineData} (hK : Keep r m)
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.env m vars) S m')
    (hwf : (r.env m vars).WF) (hok : keepOK S = true) : Keep r m' := by
  obtain ⟨hF, ⟨h1, h2, h3⟩, h4⟩ := hK
  have hk := fun {o} {bs} ho h ↦ low_of_block (o := o) (bs := bs) hpre hm hwf hok ho h
  simp only [keepOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hw, -⟩, hsp⟩, hx29⟩ := hok
  refine ⟨Run.Frame.of_match r hpre hF hm hwf hsp hx29 hw, ⟨hk ?_ h1, hk ?_ h2, hk ?_ h3⟩, hk ?_ h4⟩ <;>
    simp only [length_pkBytes, r.length_sigMem, NativeRustc.length_wordBytes] <;> omega

theorem eval_ptr0 (m : MachineData) (vars : Nat → BitVec 64) (o : Nat) :
    (Sym.ptr 0 o).eval (r.env m vars) = r.off o := by
  simp only [Sym.eval, Run.off, BitVec.ofInt_natCast]
  rfl

/-- **A register the block sets to the frame's byte `o`.** -/
theorem regIs_ptr {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {y : XReg} {o : Nat} (h : S.reg y = some (.ptr 0 o)) :
    Run.RegIs m' y (r.off o) := by
  unfold Run.RegIs
  rw [hm.regs y _ h, eval_ptr0]

/-- **A register the block sets to a literal.** -/
theorem regIs_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : XReg}
    {c : Nat} (h : S.reg y = some (.lit c)) : Run.RegIs m' y (BitVec.ofNat 64 c) := by
  unfold Run.RegIs
  rw [hm.regs y _ h]
  rfl

/-- X2 a literal `c < 2 ^ 64`: its value. -/
theorem x2_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {c : Nat}
    (h : S.reg .X2 = some (.lit c)) (hc : c < 2 ^ 64) : m'.regs.X2.toNat = c := by
  have := regIs_lit hm h
  unfold Run.RegIs at this
  rw [← getXReg_X2, UInt64.toNat, this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

/-- The frame's known registers for `Run.match_frame`: `RegIs` of each. -/
theorem known_cons {m : MachineData} {vars : Nat → BitVec 64} {y : XReg} {o : Nat}
    {k : List (XReg × Sym)} (h : Run.RegIs m y (r.off o))
    (hk : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars)) k) :
    AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars))
      ((y, .ptr 0 o) :: k) :=
  ⟨by show _ = (Sym.ptr 0 o).eval (r.env m vars); rw [eval_ptr0]; exact h, hk⟩

/-- A known register holding a literal. -/
theorem known_lit {m : MachineData} {vars : Nat → BitVec 64} {y : XReg} {c : Nat}
    {k : List (XReg × Sym)} (h : Run.RegIs m y (BitVec.ofNat 64 c))
    (hk : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars)) k) :
    AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars))
      ((y, .lit c) :: k) :=
  ⟨h, hk⟩

/-- **A register the block keeps** (its symbolic value its own atom). -/
theorem regIs_keep {m m' : MachineData} {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (Env.ofMachine m regions vars) S m') {y : XReg} {v : BitVec 64}
    (h : S.reg y = some (.reg y)) (hv : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs at *
  rw [hm.regs y _ h]
  exact hv

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

/-- **Frame bytes kept** by a change in another range of the frame. -/
theorem keep_range (hpre : r.Pre) {d d' : DataMem} {o a n : Nat} {bs : List UInt8}
    (h : BytesAt d (r.off o) bs) (hs : SameOutside d d' (InRange (r.off a) n))
    (hd : o + bs.length ≤ a ∨ a + n ≤ o) (ho : o + bs.length ≤ 29376) (ha : a + n ≤ 29376) :
    BytesAt d' (r.off o) bs :=
  bytesAt_of_sameOutside h hs fun i hi hin => by
    have hb := r.base_toNat hpre
    have := r.m0.regs.SP.toNat_lt
    rw [Run.off_add, Sym.inRange_iff (by rw [r.off_toNat hpre (by omega)]; omega),
      r.off_toNat hpre (by omega), r.off_toNat hpre (by omega)] at hin
    omega

/-- **A change in scratch keeps what the digest keeps**, SP, X29 and the mapped bytes as they
were. -/
theorem Keep.of_range (hpre : r.Pre) {m m' : MachineData} (hK : Keep r m) {a n : Nat}
    (ha : Scratch a n) (hs : SameOutside m.dmem m'.dmem (InRange (r.off a) n))
    (hsp : m'.regs.SP.toBitVec = r.base) (hx29 : (m'.regs.getXReg .X29).toBitVec = r.off 29280)
    (hk : Kept m.dmem m'.dmem) : Keep r m' := by
  obtain ⟨hF, ⟨h1, h2, h3⟩, h4⟩ := hK
  unfold Scratch at ha
  have hk' : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 15984 → BytesAt m.dmem (r.off o) bs →
      BytesAt m'.dmem (r.off o) bs := fun ho h ↦ keep_range hpre h hs (by omega) (by omega) (by omega)
  refine ⟨hF.of_block hsp hx29 hs (fun _ hp ↦ r.inRange_off hpre (by omega) hp) hk,
    ⟨hk' ?_ h1, hk' ?_ h2, hk' ?_ h3⟩, hk' ?_ h4⟩ <;>
    simp only [length_pkBytes, r.length_sigMem, NativeRustc.length_wordBytes] <;> omega

/-- **A block's writes all in region `k`**: memory changed only there. -/
theorem sameOutside_region {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {k : Nat} {B : BitVec 64} {sz : Nat} (hb : env.regions[k]? = some (B, sz))
    (hall : S.mem.all (fun w ↦ w.r == k && decide (w.off + w.n ≤ sz)) = true) :
    SameOutside env.mem0 m.dmem (InRange B sz) := by
  have hnw := hwf.noWrap k B sz hb
  intro p hp
  apply hm.get?_mem0 hwf
  rintro ⟨w, hw, b, sz', hb', h1, h2⟩
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨hr, hn⟩ := this
  rw [hr, hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  apply hp
  rw [Sym.inRange_iff (by omega)]
  omega

/-- **Two apart frame ranges** make a well-formed environment. -/
theorem wf_frame2 (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a n a' n' : Nat}
    (ha : a + n ≤ 29376) (ha' : a' + n' ≤ 29376) (h : a + n ≤ a' ∨ a' + n' ≤ a)
    (vars : Nat → BitVec 64) :
    (Env.ofMachine m [(r.off a, n), (r.off a', n')] vars).WF :=
  Env.wf_of ⟨r.frame_mapped hpre hF ha, r.frame_mapped hpre hF ha', trivial⟩
    (List.pairwise_pair.mpr (r.apart_off hpre ha ha' h))

end

/-! ## Steps -/

variable [NativeRustcArm.Host]

/-- **A block ending in a call**: the block run by the executor from `m` at directive `j`, the
callee's contract from where it calls, then the machine at the block's end `j'`. -/
theorem Run.callStep (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) {ds : List Directive}
    {j j' : Nat} (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {env : Env} (hwf : env.WF) {S S' : SState} {l : Label} (hx : exec ds S = some (S', .call l))
    {m : MachineData} (hm : Match env S m) {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (hspec : Spec (Labels.label l) P Q)
    {R : MachineState → Prop}
    (h : ∀ m₁, Match env S' m₁ → P m₁ ∧
      ∀ m₂, Q m₁ m₂ → Eventually (step1 NativeRustcArm.Host.exe) R ⟨m₂, r.pc j'⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ := by
  have hk := hb.trans hp.1 (by rintro rfl; cases hx)
  refine exec_then hk hx hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hP, hc⟩ := h st.data hm'
  refine call_then hpc hspec hP fun st' hpc' hq ↦ ?_
  obtain ⟨m₂, pc⟩ := st'
  simp only at hpc'
  subst hpc'
  rw [Nat.add_assoc, hj]
  exact hc m₂ hq

/-- **A block falling through** to directive `j'`. -/
theorem Run.fallStep (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) {ds : List Directive}
    {j j' : Nat} (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    (hne : ds ≠ []) {env : Env} (hwf : env.WF) {S S' : SState} (hx : exec ds S = some (S', .fall))
    {m : MachineData} (hm : Match env S m) {R : MachineState → Prop}
    (h : ∀ m₁, Match env S' m₁ → Eventually (step1 NativeRustcArm.Host.exe) R ⟨m₁, r.pc j'⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ := by
  have hk := hb.trans hp.1 hne
  refine exec_then hk hx hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨m₁, pc⟩ := st
  simp only [PcOk] at hpc
  subst hpc
  rw [Nat.add_assoc, hj]
  exact h m₁ hm'


/-- **A label of the function** is the address of the block it starts. -/
theorem Run.label_of_block (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) {b : List Directive}
    {j : Nat} (hb : b.IsInfixAt Sphincs.SphincsVerify.code j) {l : Label} {b' : List Directive}
    (h : b = .label l :: b') : Labels.label l = r.pc j := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

end

end NativeRustcArm.SphincsVerifyProof.Digest
