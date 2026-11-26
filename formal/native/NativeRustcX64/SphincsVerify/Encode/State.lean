module

public import NativeRustcX64.SphincsVerify.Calls
public import NativeRustc.Sphincs.EncodeFacts

/-!
# The encoding's invariant

From `b95`'s call to `b104` the encoding keeps (`Run.EncData l s c`): the inputs, the layer's
spills, R12 hasher A, RBP hasher B, R13 the address `base + 2024`, R15 `s`'s place `base + 144`, the
message `s` at `144`, and the counter `c` in EBX; with the frame's invariant and `l < 3`, `s` 16
bytes: `Run.EncBase`. Its bytes are below `560` or the parsed signature (`EncPlace`): a call
changing only hasher A (`4072 .. 4416`) or B (`560 .. 904`) keeps them, and so does a block that
writes none of them (`encKeeps`, decided on the block's literal result).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs LeanVM.Protocol.KeccakHash

@[expose] public section

/-- No write of `S` in the bytes `o' .. o' + n'` inside `o .. o + n` it writes none of. -/
theorem noWriteIn_mono {S : Sym.SState} {o n o' n' : Nat} (h : Run.noWriteIn S o n = true)
    (h1 : o ≤ o') (h2 : o' + n' ≤ o + n) : Run.noWriteIn S o' n' = true := by
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  intro w hw
  rcases h w hw with ⟨h0, h | h⟩ | h
  · exact .inl ⟨h0, .inl (by omega)⟩
  · exact .inl ⟨h0, .inr (by omega)⟩
  · exact .inr h

/-- The registers a block keeps and the invariant's bytes it does not write. -/
def encKeeps (S : Sym.SState) : Bool :=
  Run.frameWrites S && S.reg .rbx == some (.reg .rbx) && S.reg .rbp == some (.reg .rbp) &&
    S.reg .r12 == some (.reg .r12) && S.reg .r13 == some (.reg .r13) &&
    S.reg .r15 == some (.reg .r15) && Run.noWriteIn S 0 560 && Run.noWriteIn S 12780 7740 &&
    S.reg .r14 == some (.label "memcpy")

/-- `encKeeps` but for EBX (a block that swaps the counter). -/
def encKeepsNoBx (S : Sym.SState) : Bool :=
  Run.frameWrites S && S.reg .rbp == some (.reg .rbp) && S.reg .r12 == some (.reg .r12) &&
    S.reg .r13 == some (.reg .r13) && S.reg .r15 == some (.reg .r15) &&
    Run.noWriteIn S 0 560 && Run.noWriteIn S 12780 7740 &&
    S.reg .r14 == some (.label "memcpy")

namespace Run

variable (r : Run) [Labels]

/-- The invariant's places: below `560`, or the parsed signature. -/
def EncPlace (o n : Nat) : Prop := o + n ≤ 560 ∨ (12780 ≤ o ∧ o + n ≤ 20520)

/-- **The encoding's data** for layer `l`, message `s`, counter `c`. -/
def EncData (l : Nat) (s : List UInt8) (c : UInt32) (m : MachineData) : Prop :=
  r.Inputs m ∧ r.LayerSpills l m ∧ RegIs m .r12 (r.off 4072) ∧ RegIs m .rbp (r.off 560) ∧
    RegIs m .r13 (r.off 2024) ∧ RegIs m .r15 (r.off 144) ∧ BytesAt m.dmem (r.off 144) s ∧
    UInt32.ofNat (reg m .rbx).toNat = c ∧ RegIs m .r14 (label "memcpy").toBitVec

theorem EncData.memcpy {l : Nat} {s : List UInt8} {c : UInt32} {m : MachineData}
    (h : r.EncData l s c m) : RegIs m .r14 (label "memcpy").toBitVec :=
  h.2.2.2.2.2.2.2.2

/-- **The encoding's invariant.** -/
def EncBase (l : Nat) (s : List UInt8) (c : UInt32) (m : MachineData) : Prop :=
  l < 3 ∧ s.length = 16 ∧ r.Frame m ∧ r.EncData l s c m

omit [Labels] in
theorem length_be64 (x : UInt64) : (be64 x).length = 8 := rfl
omit [Labels] in
theorem length_be32 (x : UInt32) : (be32 x).length = 4 := rfl

omit [Labels] in
theorem length_pkBytes : r.pkB.length = 32 := r.hpk

omit [Labels] in
theorem length_sigMem : (sigMem r.sig).length = 7740 := SigMemBytes.length_sigMem r.sigB r.hsig

/-- **The data, from bytes kept** at its places, its registers kept and EBX's counter `c'`. -/
theorem encData_of_bytes' {l : Nat} {s : List UInt8} {c c' : UInt32} {m m' : MachineData}
    (h : r.EncData l s c m) (hs : s.length = 16)
    (hk : ∀ {o : Nat} {bs : List UInt8}, EncPlace o bs.length →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs)
    (hreg : ∀ x : Reg64, x = .rbp ∨ x = .r12 ∨ x = .r13 ∨ x = .r15 ∨ x = .r14 → reg m' x = reg m x)
    (hc : UInt32.ofNat (reg m' .rbx).toNat = c') : r.EncData l s c' m' := by
  obtain ⟨⟨hpk, hsig⟩, ⟨s96, s200, s208, s160, s216, s104, s88, s60, s568, s176⟩, h12, hbp, h13,
    h15, hsm, -, h14⟩ := h
  have w : ∀ o, o + 8 ≤ 560 → ∀ v : UInt64, r.WordAt m o v → r.WordAt m' o v := fun o ho v hv ↦
    hk (by rw [EncPlace, length_wordBytes]; omega) hv
  refine ⟨⟨hk (by rw [EncPlace, r.length_pkBytes]; omega) hpk,
    hk (by rw [EncPlace, r.length_sigMem]; omega) hsig⟩,
    ⟨w 96 (by omega) _ s96, w 192 (by omega) _ s200, w 200 (by omega) _ s208,
      w 168 (by omega) _ s160, w 208 (by omega) _ s216,
      hk (by rw [EncPlace, length_be32]; omega) s104, hk (by rw [EncPlace, length_be64]; omega) s88,
      hk (by rw [EncPlace, length_be32]; omega) s60, w 552 (by omega) _ s568,
      w 184 (by omega) _ s176⟩, ?_, ?_, ?_, ?_, hk (by rw [EncPlace, hs]; omega) hsm, hc, ?_⟩
  · rw [RegIs, hreg .r12 (by simp)]; exact h12
  · rw [RegIs, hreg .rbp (by simp)]; exact hbp
  · rw [RegIs, hreg .r13 (by simp)]; exact h13
  · rw [RegIs, hreg .r15 (by simp)]; exact h15
  · rw [RegIs, hreg .r14 (by simp)]; exact h14

/-- **The data, from bytes kept** at its places and its registers kept. -/
theorem encData_of_bytes {l : Nat} {s : List UInt8} {c : UInt32} {m m' : MachineData}
    (h : r.EncData l s c m) (hs : s.length = 16)
    (hk : ∀ {o : Nat} {bs : List UInt8}, EncPlace o bs.length →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs)
    (hreg : ∀ x : Reg64, x = .rbx ∨ x = .rbp ∨ x = .r12 ∨ x = .r13 ∨ x = .r15 ∨ x = .r14 →
      reg m' x = reg m x) : r.EncData l s c m' :=
  r.encData_of_bytes' h hs hk (fun x hx ↦ hreg x (.inr hx))
    (by rw [hreg .rbx (.inl rfl)]; exact h.2.2.2.2.2.2.2.1)

/-- **A call keeps the data** when it changes only bytes of hasher A or hasher B. -/
theorem encData_of_call (hpre : r.Pre) {l : Nat} {s : List UInt8} {c : UInt32}
    {m m' : MachineData} (hc : r.AtCall m) (h : r.EncData l s c m) (hs : s.length = 16)
    (hS : Saved m m') {a n N : Nat}
    (ha : (4072 ≤ a ∧ a + n ≤ 4416) ∨ (560 ≤ a ∧ a + n ≤ 904)) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : r.EncData l s c m' :=
  r.encData_of_bytes h hs
    (fun hp hb ↦ r.bytesAt_of_call hpre hc (by omega) hN hout (by unfold EncPlace at hp; omega)
      (by unfold EncPlace at hp; omega) hb)
    fun x hx ↦ hS.1 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

/-- **A block keeps the data** when it keeps the registers and writes none of its bytes. -/
theorem encData_of_block (hpre : r.Pre) {l : Nat} {s : List UInt8} {c : UInt32}
    {m m' : MachineData} (h : r.EncData l s c m) (hs : s.length = 16) {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : Sym.SState} (hm : Sym.Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hS : encKeeps S = true) : r.EncData l s c m' := by
  simp only [encKeeps, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hbx⟩, hbp⟩, h12⟩, h13⟩, h15⟩, k0⟩, ksig⟩, h14⟩ := hS
  refine r.encData_of_bytes h hs (fun hp hb ↦ r.bytesAt_kept hpre hm hwf
    (by unfold EncPlace at hp; omega) hb ?_) fun x hx ↦ ?_
  · unfold EncPlace at hp
    rcases hp with hp | hp
    · exact noWriteIn_mono k0 (Nat.zero_le _) (by omega)
    · exact noWriteIn_mono ksig hp.1 (by omega)
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm.regs .rbx _ hbx
    · exact hm.regs .rbp _ hbp
    · exact hm.regs .r12 _ h12
    · exact hm.regs .r13 _ h13
    · exact hm.regs .r15 _ h15
    · exact (hm.regs .r14 _ h14).trans h.2.2.2.2.2.2.2.2.symm

/-- **A block that changes EBX keeps the data**, with EBX's new counter. -/
theorem encData_of_block' (hpre : r.Pre) {l : Nat} {s : List UInt8} {c : UInt32}
    {m m' : MachineData} (h : r.EncData l s c m) (hs : s.length = 16) {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : Sym.SState} (hm : Sym.Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hS : encKeepsNoBx S = true) :
    r.EncData l s (UInt32.ofNat (reg m' .rbx).toNat) m' := by
  simp only [encKeepsNoBx, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hbp⟩, h12⟩, h13⟩, h15⟩, k0⟩, ksig⟩, h14⟩ := hS
  refine r.encData_of_bytes' h hs (fun hp hb ↦ r.bytesAt_kept hpre hm hwf
    (by unfold EncPlace at hp; omega) hb ?_) (fun x hx ↦ ?_) rfl
  · unfold EncPlace at hp
    rcases hp with hp | hp
    · exact noWriteIn_mono k0 (Nat.zero_le _) (by omega)
    · exact noWriteIn_mono ksig hp.1 (by omega)
  · rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hm.regs .rbp _ hbp
    · exact hm.regs .r12 _ h12
    · exact hm.regs .r13 _ h13
    · exact hm.regs .r15 _ h15
    · exact (hm.regs .r14 _ h14).trans h.2.2.2.2.2.2.2.2.symm

end Run

end

end NativeRustcX64.SphincsVerifyProof
