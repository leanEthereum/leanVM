module

public import NativeRustcVmArm.Field.Frame
public import NativeRustcVmArm.Spec.Field

/-!
# Functions with a frame and calls

The field functions that call others (`kinv::sq`, `kinv`, `kpow`, `EW::sq_iter`) save X30 and the
callee-saved registers they use (`used`) in an `F`-byte frame below SP at the entry and use `N`
bytes of stack with their callees'. From the entry state `m0` and the state `m1` after the prologue,
every state between the prologue and the epilogue keeps (`Fr`): SP at the frame's base, the other
callee-saved registers, the frame's bytes as `m1` left them, every byte outside the `N` bytes below
the entry's SP, every mapped byte. The prologue (`prologue`) establishes it and stores the saved
registers (`Slots`); a callee's contract (`Fr.stackOk`, `Fr.call`) and a block without memory
accesses (`Fr.block`) keep it; the epilogue (`epilogue`) restores the registers and SP.
-/

namespace NativeRustcVmArm.Field

open NativeRustcArm NativeRustcArm.Sym

@[expose] public section

/-- **Between prologue and epilogue.** -/
structure Fr (m0 m1 : MachineData) (F N : Nat) (used : List XReg) (m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = stackBelow m0 F
  regs : ∀ r, calleeSaved r = true → r ∉ used → m.regs.getXReg r = m0.regs.getXReg r
  frame : ∀ i < F, m.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 i) =
    m1.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 i)
  same : SameOutside m0.dmem m.dmem (InRange (stackBelow m0 N) N)
  kept : Kept m0.dmem m.dmem

/-- The prologue's stores: register `r` of the entry at `off` in the frame. -/
def Slots (m0 m1 : MachineData) (F : Nat) (slots : List (XReg × Nat)) : Prop :=
  ∀ p ∈ slots, p.2 + 8 ≤ F ∧
    BytesAt m1.dmem (stackBelow m0 F + BitVec.ofNat 64 p.2)
      ((List.range 8).map (byteOf (m0.regs.getXReg p.1).toBitVec))

/-- A block's summary keeps the callee-saved registers outside `used`. -/
def keepsExcept (used : List XReg) (S : SState) : Bool :=
  allXRegs.all fun r ↦ !calleeSaved r || used.any (·.idx == r.idx) || S.reg r == some (.reg r)

/-- An epilogue's summary restores X30 and the registers of `slots` from their slots, and keeps the
other callee-saved registers, outside `used`. -/
def restores (slots : List (XReg × Nat)) (used : List XReg) (S : SState) : Bool :=
  slots.all (fun p ↦ S.reg p.1 == some (.load 0 p.2 8)) && slots.any (·.1.idx == 30) &&
    allXRegs.all fun r ↦ !calleeSaved r || slots.any (·.1.idx == r.idx) ||
      (!used.any (·.idx == r.idx) && S.reg r == some (.reg r))

end

public section

theorem keepsExcept_reg {used : List XReg} {S : SState} (h : keepsExcept used S = true) {r : XReg}
    (hr : calleeSaved r = true) (hu : r ∉ used) : S.reg r = some (.reg r) := by
  have := List.all_eq_true.mp h r (mem_allXRegs r)
  simp only [hr, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h | h
  · obtain ⟨u, hu', he⟩ := List.any_eq_true.mp h
    rw [XReg.idx_inj (beq_iff_eq.mp he)] at hu'
    exact absurd hu' hu
  · exact h

theorem sub_ofNat_toNat {a : BitVec 64} {n : Nat} (h : n ≤ a.toNat) :
    (a - BitVec.ofNat 64 n).toNat = a.toNat - n := by
  have := a.isLt
  rw [toNat_sub_of_le _ _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem stackBelow_toNat' {m : MachineData} {n : Nat} (h : n ≤ m.regs.SP.toNat) :
    (stackBelow m n).toNat = m.regs.SP.toNat - n := sub_ofNat_toNat h

theorem add_ofNat_toNat {a : BitVec 64} {i : Nat} (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := toNat_add_ofNat a i h

/-- Less stack below SP. -/
theorem StackOk.mono {m : MachineData} {n N : Nat} (h : StackOk m N) (hle : n ≤ N) :
    StackOk m n := by
  obtain ⟨hal, hN, hmap⟩ := h
  refine ⟨hal, by omega, fun i hi ↦ ?_⟩
  have hlt := m.regs.SP.toNat_lt
  have := hmap (N - n + i) (by omega)
  rwa [show m.regs.SP.toBitVec - BitVec.ofNat 64 N + BitVec.ofNat 64 (N - n + i) =
    m.regs.SP.toBitVec - BitVec.ofNat 64 n + BitVec.ofNat 64 i from
    BitVec.eq_of_toNat_eq (by
      rw [add_ofNat_toNat (by rw [sub_ofNat_toNat (by show N ≤ m.regs.SP.toNat; omega)]; omega),
        add_ofNat_toNat (by rw [sub_ofNat_toNat (by show n ≤ m.regs.SP.toNat; omega)]; omega),
        sub_ofNat_toNat (by show N ≤ m.regs.SP.toNat; omega),
        sub_ofNat_toNat (by show n ≤ m.regs.SP.toNat; omega)]
      show m.regs.SP.toNat - N + (N - n + i) = m.regs.SP.toNat - n + i
      omega)] at this

/-- The stack below SP, after a callee keeping SP and every mapped byte. -/
theorem StackOk.of_saved {m m' : MachineData} {n : Nat} (h : StackOk m n) (hs : Saved m m') :
    StackOk m' n := by
  obtain ⟨hal, hN, hmap⟩ := h
  have hsp : m'.regs.SP = m.regs.SP := hs.2.1
  refine ⟨by rw [hsp]; exact hal, by rw [hsp]; exact hN, fun i hi ↦ ?_⟩
  rw [hsp]
  exact hs.2.2 _ (hmap i hi)

/-- A byte of the `n` below SP is one of the `N ≥ n` below it. -/
theorem inRange_mono {m : MachineData} {n N : Nat} (hle : n ≤ N) (hN : N ≤ m.regs.SP.toNat)
    {p : BitVec 64} (h : InRange (stackBelow m n) n p) : InRange (stackBelow m N) N p := by
  have hlt := m.regs.SP.toNat_lt
  have hn := stackBelow_toNat' (m := m) (n := n) (by omega)
  have hN' := stackBelow_toNat' (m := m) (n := N) hN
  rw [inRange_iff (by rw [hn]; omega), hn] at h
  rw [inRange_iff (by rw [hN']; omega), hN']
  omega

section
variable {m0 m1 m m' : MachineData} {F N : Nat} {used : List XReg}

/-- The geometry: the entry's SP leaves `N` bytes, the frame its top `F`. -/
structure Geo (m0 : MachineData) (F N : Nat) : Prop where
  ok : StackOk m0 N
  f16 : F % 16 = 0
  le : F ≤ N

theorem Geo.sp_toNat (g : Geo m0 F N) : N ≤ m0.regs.SP.toNat := g.ok.2.1

theorem Geo.base_toNat (g : Geo m0 F N) : (stackBelow m0 F).toNat = m0.regs.SP.toNat - F :=
  stackBelow_toNat' (by have := g.sp_toNat; have := g.le; omega)

theorem Geo.below_toNat (g : Geo m0 F N) : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N :=
  stackBelow_toNat' g.sp_toNat

/-- An address of the `N` bytes below the entry's SP is mapped. -/
theorem Geo.mapped (g : Geo m0 F N) {p : BitVec 64} (h1 : m0.regs.SP.toNat - N ≤ p.toNat)
    (h2 : p.toNat < m0.regs.SP.toNat) : (m0.dmem.get? p).isSome := by
  have hb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 N).toNat = m0.regs.SP.toNat - N := g.below_toNat
  have := g.ok.2.2 (p.toNat - (m0.regs.SP.toNat - N)) (by omega)
  have hlt := m0.regs.SP.toNat_lt
  rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 N +
      BitVec.ofNat 64 (p.toNat - (m0.regs.SP.toNat - N)) = p from
    BitVec.eq_of_toNat_eq (by rw [add_ofNat_toNat (by omega), hb]; omega)] at this

theorem Fr.sp_toNat (g : Geo m0 F N) (h : Fr m0 m1 F N used m) :
    m.regs.SP.toNat = m0.regs.SP.toNat - F := by
  show m.regs.SP.toBitVec.toNat = _
  rw [h.sp, g.base_toNat]

/-- **A callee's stack**: `S` bytes below the frame. -/
theorem Fr.stackOk (g : Geo m0 F N) (h : Fr m0 m1 F N used m) {S : Nat} (hS : F + S ≤ N) :
    StackOk m S := by
  have hsp := h.sp_toNat g
  have hal := g.ok.1
  have hn := g.sp_toNat
  refine ⟨by rw [hsp]; have := g.f16; omega, by rw [hsp]; omega, fun i hi ↦ ?_⟩
  have hlt := m0.regs.SP.toNat_lt
  have hb : (m.regs.SP.toBitVec - BitVec.ofNat 64 S + BitVec.ofNat 64 i).toNat =
      m0.regs.SP.toNat - F - S + i := by
    rw [add_ofNat_toNat (by rw [sub_ofNat_toNat (by show S ≤ m.regs.SP.toNat; omega)]; omega),
      sub_ofNat_toNat (by show S ≤ m.regs.SP.toNat; omega)]
    show m.regs.SP.toNat - S + i = _
    omega
  exact h.kept _ (g.mapped (by omega) (by omega))

/-- **After a callee** using `S` bytes below the frame. -/
theorem Fr.call (g : Geo m0 F N) (h : Fr m0 m1 F N used m) {S : Nat} (hS : F + S ≤ N)
    (hsv : Saved m m') (hso : SameOutside m.dmem m'.dmem (InRange (stackBelow m S) S)) :
    Fr m0 m1 F N used m' := by
  have hsp := h.sp_toNat g
  have hn := g.sp_toNat
  have hlt := m0.regs.SP.toNat_lt
  have hcb : (stackBelow m S).toNat = m0.regs.SP.toNat - F - S := by
    rw [stackBelow_toNat' (by omega), hsp]
  have hin : ∀ p : BitVec 64, InRange (stackBelow m S) S p →
      m0.regs.SP.toNat - F - S ≤ p.toNat ∧ p.toNat < m0.regs.SP.toNat - F := fun p hp ↦ by
    rw [inRange_iff (by rw [hcb]; omega), hcb] at hp
    omega
  refine ⟨by rw [← h.sp]; exact congrArg UInt64.toBitVec hsv.2.1, fun r hr hu ↦ ?_,
    fun i hi ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ hsv.2.2 p (h.kept p hp)⟩
  · rw [hsv.1 r hr, h.regs r hr hu]
  · rw [hso _ fun hp ↦ ?_, h.frame i hi]
    have := hin _ hp
    rw [add_ofNat_toNat (by rw [g.base_toNat]; omega), g.base_toNat] at this
    omega
  · rw [hso p fun hp' ↦ hp ?_, h.same p hp]
    have := hin p hp'
    rw [inRange_iff (by rw [g.below_toNat]; omega), g.below_toNat]
    omega

/-- **After a block** without memory accesses, run from `init [] .sp`, keeping SP and the
callee-saved registers outside `used`. -/
theorem Fr.block [Labels] (h : Fr m0 m1 F N used m) {S : SState}
    (hm : Match (Env.ofMachine m []) S m') (hmem : S.mem = []) (hsp : S.sp = .sp)
    (hk : keepsExcept used S = true) : Fr m0 m1 F N used m' := by
  have hd : m'.dmem = m.dmem := hm.dmem_eq (Env.wf_nil m) hmem
  refine ⟨?_, fun r hr hu ↦ ?_, fun i hi ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rw [hm.sp, hsp]
    exact h.sp
  · rw [← h.regs r hr hu]
    exact UInt64.toBitVec_inj.mp (hm.regs r _ (keepsExcept_reg hk hr hu))
  · rw [hd]; exact h.frame i hi
  · rw [hd]; exact h.same p hp
  · rw [hd]; exact h.kept p hp

end

end

end NativeRustcVmArm.Field
