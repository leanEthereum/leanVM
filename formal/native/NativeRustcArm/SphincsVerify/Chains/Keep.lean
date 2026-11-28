module

public import NativeRustcArm.SphincsVerify.Chains.Bytes
public import NativeRustcArm.SphincsVerify.SigMem

/-!
# What the chains keep

Through the chains the frame's invariant, the inputs, the layer's spills, the hashers' registers
(X19, X21, X25, X27), the codeword at `15936` and the ends so far at `20464` stay (`Keep`). A call that
changes only scratch bytes (`Scratch`: `8224 .. 15936`, `16000 .. 20464`, `21488 .. 21520`) and
its stack keeps them (`Keep.of_call`), as does a block whose writes miss them (`keepOK`, decided on
the literal state, `Keep.of_block`). A label of the function is its directive's address
(`labelAt`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

@[expose] public section

/-- **What the chains keep**: the frame, the inputs, the layer's spills, X19, X21, X25 and X27, the
codeword `x` at `15936`, the ends so far `E` at `20464`. -/
def Keep (r : Run) (l : Nat) (x E : List UInt8) (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧ Run.RegIs m .X19 136 ∧
    Run.RegIs m .X21 (r.off 19208) ∧ Run.RegIs m .X25 (r.off 8840) ∧
    Run.RegIs m .X27 (r.off 19008) ∧ BytesAt m.dmem (r.off 15936) x ∧
    BytesAt m.dmem (r.off 20464) E

/-- The frame's scratch bytes `a .. a + n` the chains' calls and blocks change. -/
def Scratch (a n : Nat) : Prop :=
  (8224 ≤ a ∧ a + n ≤ 15936) ∨ (16000 ≤ a ∧ a + n ≤ 20464) ∨ (21488 ≤ a ∧ a + n ≤ 21520)

theorem length_be32 (v : UInt32) : (be32 v).length = 4 := rfl
theorem length_be64 (v : UInt64) : (be64 v).length = 8 := rfl

section
variable {r : Run} [Labels]

/-- **A call changing scratch bytes keeps what the chains keep.** -/
theorem Keep.of_call (hpre : r.Pre) {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {m m' : MachineData} (hK : Keep r l x E m) (hS : Saved m m')
    {a n N : Nat} (ha : Scratch a n) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : Keep r l x E m' := by
  obtain ⟨hF, ⟨h1, h2, h3⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, h19, h21, h25, h27, hxa,
    hEa⟩ := hK
  have ha' : a + n ≤ 21520 := by unfold Scratch at ha; omega
  have hk : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 8224 ∨ (15936 ≤ o ∧ o + bs.length ≤ 16000)
      ∨ (20464 ≤ o ∧ o + bs.length ≤ 21488) → BytesAt m.dmem (r.off o) bs →
      BytesAt m'.dmem (r.off o) bs := fun ho h ↦
    r.bytesAt_of_call hpre hF (by omega) hN hout (by omega) (by unfold Scratch at ha; omega) h
  have hreg : ∀ {y : XReg} {v : BitVec 64}, calleeSaved y = true → Run.RegIs m y v →
      Run.RegIs m' y v := fun hy h ↦ by
    unfold Run.RegIs at *
    rw [hS.1 _ hy]
    exact h
  refine ⟨r.frame_of_call hpre hF hS ha' hN hout, ⟨hk ?_ h1, hk ?_ h2, hk ?_ h3⟩,
    ⟨hk ?_ s1, hk ?_ s2, hk ?_ s3, hk ?_ s4, hk ?_ s5, hk ?_ s6, hk ?_ s7, hk ?_ s8, hk ?_ s9,
      hk ?_ s10, hk ?_ s11⟩, hreg rfl h19, hreg rfl h21, hreg rfl h25, hreg rfl h27, hk ?_ hxa,
    hk ?_ hEa⟩ <;>
    (try simp only [r.hpk, r.length_sigMem, NativeRustc.length_wordBytes, length_be32,
      length_be64, hx]) <;> omega

omit [Labels] in
/-- No write of `S` in the region-0 bytes `o .. o + n` (`Run.noWriteIn`) is none in a part. -/
theorem noWriteIn_mono {S : SState} {o n o' n' : Nat} (h : Run.noWriteIn S o n = true)
    (h1 : o ≤ o') (h2 : o' + n' ≤ o + n) : Run.noWriteIn S o' n' = true := by
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h ⊢
  intro w hw
  have := h w hw
  omega

/-- A block's literal state keeps what the chains keep: its writes in the frame below the saved
registers and off the kept bytes, SP, X29, X19, X21, X25, X27 as they were. -/
def keepOK (S : SState) : Bool :=
  Run.frameWrites S && Run.noWriteIn S 0 448 && Run.noWriteIn S 448 7776 &&
    Run.noWriteIn S 15936 64 && Run.noWriteIn S 20464 1024 && S.sp == .ptr 0 0 &&
    S.reg .X29 == some (.ptr 0 21520) && S.reg .X19 == some (.lit 136) &&
    S.reg .X21 == some (.ptr 0 19208) && S.reg .X25 == some (.ptr 0 8840) &&
    S.reg .X27 == some (.ptr 0 19008)

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

/-- **A block whose writes miss the kept bytes keeps what the chains keep.** -/
theorem Keep.of_block (hpre : r.Pre) {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {m m' : MachineData} (hK : Keep r l x E m) {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF)
    (hok : keepOK S = true) : Keep r l x E m' := by
  obtain ⟨hF, ⟨h1, h2, h3⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, -, -, -, -, hxa,
    hEa⟩ := hK
  simp only [keepOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, n0⟩, n1⟩, n2⟩, n3⟩, hsp⟩, hx29⟩, h19⟩, h21⟩, h25⟩, h27⟩ := hok
  have hk : ∀ {o : Nat} {bs : List UInt8}, (o + bs.length ≤ 448 ∨
      (448 ≤ o ∧ o + bs.length ≤ 8224)) ∨ (15936 ≤ o ∧ o + bs.length ≤ 16000) ∨
      (20464 ≤ o ∧ o + bs.length ≤ 21488) → BytesAt m.dmem (r.off o) bs →
      BytesAt m'.dmem (r.off o) bs := fun ho h ↦ by
    refine r.bytesAt_kept hpre hm hwf (by omega) h ?_
    rcases ho with (ho | ho) | ho | ho
    · exact noWriteIn_mono n0 (by omega) (by omega)
    · exact noWriteIn_mono n1 (by omega) (by omega)
    · exact noWriteIn_mono n2 (by omega) (by omega)
    · exact noWriteIn_mono n3 (by omega) (by omega)
  refine ⟨Run.Frame.of_match r hpre hF hm hwf hsp hx29 hw, ⟨hk ?_ h1, hk ?_ h2, hk ?_ h3⟩,
    ⟨hk ?_ s1, hk ?_ s2, hk ?_ s3, hk ?_ s4, hk ?_ s5, hk ?_ s6, hk ?_ s7, hk ?_ s8, hk ?_ s9,
      hk ?_ s10, hk ?_ s11⟩, regIs_lit hm h19, regIs_ptr hm h21, regIs_ptr hm h25, regIs_ptr hm h27,
    hk ?_ hxa, hk ?_ hEa⟩ <;>
    (try simp only [r.hpk, r.length_sigMem, NativeRustc.length_wordBytes, length_be32,
      length_be64, hx]) <;> omega

end

/-! ## Labels -/

variable [NativeRustcArm.Host]

/-- **A label of the function** is the address of the block it starts. -/
theorem labelAt (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) {b : List Directive}
    {j : Nat} (hb : b.IsInfixAt Sphincs.SphincsVerify.code j) {l : Label} {b' : List Directive}
    (h : b = .label l :: b') : Labels.label l = r.pc j := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

end

end NativeRustcArm.SphincsVerifyProof.Chains
