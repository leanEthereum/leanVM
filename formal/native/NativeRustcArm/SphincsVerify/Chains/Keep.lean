module

public import NativeRustcArm.SphincsVerify.Chains.Bytes
public import NativeRustcArm.SphincsVerify.SigMem

/-!
# What the chains keep

Through the chains the frame's invariant, the inputs, the layer's spills, the hashers' registers
(X21, X25, X26), the codeword at `23696` and the ends so far at `28224` stay (`Keep`). A call that
changes only scratch bytes (`Scratch`: `15984 .. 23696`, `23760 .. 28224`, `29248 .. 29280`) and
its stack keeps them (`Keep.of_call`), as does a block whose writes miss them (`keepOK`, decided on
the literal state, `Keep.of_block`). A label of the function is its directive's address
(`labelAt`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

@[expose] public section

/-- **What the chains keep**: the frame, the inputs, the layer's spills, X21, X25 and X26, the
codeword `x` at `23696`, the ends so far `E` at `28224`. -/
def Keep (r : Run) (l : Nat) (x E : List UInt8) (m : MachineData) : Prop :=
  r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧ Run.RegIs m .X21 (r.off 26968) ∧
    Run.RegIs m .X25 (r.off 16600) ∧ Run.RegIs m .X26 136 ∧ BytesAt m.dmem (r.off 23696) x ∧
    BytesAt m.dmem (r.off 28224) E

/-- The frame's scratch bytes `a .. a + n` the chains' calls and blocks change. -/
def Scratch (a n : Nat) : Prop :=
  (15984 ≤ a ∧ a + n ≤ 23696) ∨ (23760 ≤ a ∧ a + n ≤ 28224) ∨ (29248 ≤ a ∧ a + n ≤ 29280)

theorem length_pkBytes (w : Nat → UInt64) : (pkBytes w).length = 32 := by
  simp [pkBytes, Native.Keccak.Proof.length_wordsBytes]

theorem length_be32 (v : UInt32) : (be32 v).length = 4 := rfl
theorem length_be64 (v : UInt64) : (be64 v).length = 8 := rfl

section
variable {r : Run} [Labels]

/-- **A call changing scratch bytes keeps what the chains keep.** -/
theorem Keep.of_call (hpre : r.Pre) {l : Nat} {x E : List UInt8} (hx : x.length = 64)
    (hE : E.length ≤ 1024) {m m' : MachineData} (hK : Keep r l x E m) (hS : Saved m m')
    {a n N : Nat} (ha : Scratch a n) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : Keep r l x E m' := by
  obtain ⟨hF, ⟨h1, h2, h3⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, h21, h25, h26, hxa,
    hEa⟩ := hK
  have ha' : a + n ≤ 29280 := by unfold Scratch at ha; omega
  have hk : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 15984 ∨ (23696 ≤ o ∧ o + bs.length ≤ 23760)
      ∨ (28224 ≤ o ∧ o + bs.length ≤ 29248) → BytesAt m.dmem (r.off o) bs →
      BytesAt m'.dmem (r.off o) bs := fun ho h ↦
    r.bytesAt_of_call hpre hF (by omega) hN hout (by omega) (by unfold Scratch at ha; omega) h
  have hreg : ∀ {y : XReg} {v : BitVec 64}, calleeSaved y = true → Run.RegIs m y v →
      Run.RegIs m' y v := fun hy h ↦ by
    unfold Run.RegIs at *
    rw [hS.1 _ hy]
    exact h
  refine ⟨r.frame_of_call hpre hF hS ha' hN hout, ⟨hk ?_ h1, hk ?_ h2, hk ?_ h3⟩,
    ⟨hk ?_ s1, hk ?_ s2, hk ?_ s3, hk ?_ s4, hk ?_ s5, hk ?_ s6, hk ?_ s7, hk ?_ s8, hk ?_ s9,
      hk ?_ s10, hk ?_ s11⟩, hreg rfl h21, hreg rfl h25, hreg rfl h26, hk ?_ hxa, hk ?_ hEa⟩ <;>
    (try simp only [length_pkBytes, r.length_sigMem, NativeRustc.length_wordBytes, length_be32,
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
registers and off the kept bytes, SP, X29, X21, X25, X26 as they were. -/
def keepOK (S : SState) : Bool :=
  Run.frameWrites S && Run.noWriteIn S 0 432 && Run.noWriteIn S 8208 7776 &&
    Run.noWriteIn S 23696 64 && Run.noWriteIn S 28224 1024 && S.sp == .ptr 0 0 &&
    S.reg .X29 == some (.ptr 0 29280) && S.reg .X21 == some (.ptr 0 26968) &&
    S.reg .X25 == some (.ptr 0 16600) && S.reg .X26 == some (.lit 136)

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
  obtain ⟨hF, ⟨h1, h2, h3⟩, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, -, -, -, hxa,
    hEa⟩ := hK
  simp only [keepOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, n0⟩, n1⟩, n2⟩, n3⟩, hsp⟩, hx29⟩, h21⟩, h25⟩, h26⟩ := hok
  have hk : ∀ {o : Nat} {bs : List UInt8}, (o + bs.length ≤ 432 ∨
      (8208 ≤ o ∧ o + bs.length ≤ 15984)) ∨ (23696 ≤ o ∧ o + bs.length ≤ 23760) ∨
      (28224 ≤ o ∧ o + bs.length ≤ 29248) → BytesAt m.dmem (r.off o) bs →
      BytesAt m'.dmem (r.off o) bs := fun ho h ↦ by
    refine r.bytesAt_kept hpre hm hwf (by omega) h ?_
    rcases ho with (ho | ho) | ho | ho
    · exact noWriteIn_mono n0 (by omega) (by omega)
    · exact noWriteIn_mono n1 (by omega) (by omega)
    · exact noWriteIn_mono n2 (by omega) (by omega)
    · exact noWriteIn_mono n3 (by omega) (by omega)
  refine ⟨Run.Frame.of_match r hpre hF hm hwf hsp hx29 hw, ⟨hk ?_ h1, hk ?_ h2, hk ?_ h3⟩,
    ⟨hk ?_ s1, hk ?_ s2, hk ?_ s3, hk ?_ s4, hk ?_ s5, hk ?_ s6, hk ?_ s7, hk ?_ s8, hk ?_ s9,
      hk ?_ s10, hk ?_ s11⟩, regIs_ptr hm h21, regIs_ptr hm h25, regIs_lit hm h26, hk ?_ hxa,
    hk ?_ hEa⟩ <;>
    (try simp only [length_pkBytes, r.length_sigMem, NativeRustc.length_wordBytes, length_be32,
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
