module

public import Native.Frame
public import Kraken.AArch64.OmniSemantics
import all Kraken.Mem

/-!
# QM on Kraken's AArch64 machine

Each QM register lives in an AArch64 register (`Reg64.toX`); the compiled code may also clobber
the scratch registers X4 to X8 (`XReg.scratch`) and writes no other register (`XReg.reserved`: X14
to X18, X25 to X30 and SP among them). `StateRel s m`: the machine `m` holds the QM state `s`, every
word of `s.mem` eight little-endian bytes of `m`'s memory at an aligned address. Kraken's flags are
unconstrained.
-/

open Native Std

namespace NativeArm

@[expose] public section

/-- The AArch64 register holding a QM register. -/
def _root_.Native.Reg64.toX : Reg64 → XReg
  | .rax => .X9 | .rbx => .X19 | .rcx => .X10 | .rdx => .X11 | .rsi => .X12 | .rdi => .X0
  | .rsp => .X25 | .rbp => .X20 | .r8 => .X13 | .r9 => .X1 | .r10 => .X2 | .r11 => .X3
  | .r12 => .X21 | .r13 => .X22 | .r14 => .X23 | .r15 => .X24

/-- The QM register an AArch64 register holds, if any. -/
def ofX : XReg → Option Reg64
  | .X9 => some .rax | .X19 => some .rbx | .X10 => some .rcx | .X11 => some .rdx
  | .X12 => some .rsi | .X0 => some .rdi | .X25 => some .rsp | .X20 => some .rbp
  | .X13 => some .r8 | .X1 => some .r9 | .X2 => some .r10 | .X3 => some .r11
  | .X21 => some .r12 | .X22 => some .r13 | .X23 => some .r14 | .X24 => some .r15
  | _ => none

/-- The scratch registers the compiled code may clobber. -/
def _root_.XReg.scratch : XReg → Bool
  | .X4 | .X5 | .X6 | .X7 | .X8 => true
  | _ => false

/-- The registers the compiled code never writes: neither a QM register's nor scratch. -/
def _root_.XReg.reserved : XReg → Bool
  | .X14 | .X15 | .X16 | .X17 | .X18 | .X26 | .X27 | .X28 | .X29 | .X30 => true
  | _ => false

/-- A 64-bit register operand. -/
abbrev xr (r : XReg) : RegOrZr .W64 := .low (.reg r) .W64

/-- A 64-bit register operand where index 31 is SP. -/
abbrev xs (r : XReg) : RegOrSp .W64 := .low (.reg r) .W64

/-- `m` with register `r` set to `v`. -/
def _root_.MachineData.setX (m : MachineData) (r : XReg) (v : BitVec 64) : MachineData :=
  { m with regs := m.regs.setXReg r v }

/-- The words of `q` are in `d`: each at an aligned address, its eight bytes little-endian. -/
def MemRel (q : UInt64 → Option UInt64) (d : DataMem) : Prop :=
  ∀ a v, q a = some v → a.toNat % 8 = 0 ∧ d.loadBytes a.toBitVec 8 = some v.toBytes

/-- `m` holds `s`: each QM register in its image, and the memory. -/
def StateRel (s : QState) (m : MachineData) : Prop :=
  (∀ r, m.regs.getXReg r.toX = s.reg r) ∧ MemRel s.mem m.dmem

/-- `m'` agrees with `m` on the reserved registers and SP. -/
def Keeps (m m' : MachineData) : Prop :=
  (∀ r, r.reserved = true → m'.regs.getXReg r = m.regs.getXReg r) ∧ m'.regs.SP = m.regs.SP

end

public section

/-! ## Registers -/

theorem ofX_toX (r : Reg64) : ofX r.toX = some r := by cases r <;> rfl

theorem toX_ofX {x : XReg} {r : Reg64} (h : ofX x = some r) : r.toX = x := by
  cases x <;> simp only [ofX, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

theorem toX_inj {a b : Reg64} (h : a.toX = b.toX) : a = b := by
  have := ofX_toX a
  rw [h, ofX_toX] at this
  exact (Option.some.inj this).symm

theorem reserved_of_ofX {x : XReg} (h : ofX x = none) (hs : x.scratch = false) :
    x.reserved = true := by
  cases x <;> first | rfl | exact absurd hs (by decide) | exact absurd h (by decide)

@[simp] theorem toX_scratch (r : Reg64) : r.toX.scratch = false := by cases r <;> rfl

@[simp] theorem toX_ne_X4 (r : Reg64) : (r.toX = .X4) = False := by cases r <;> simp [Reg64.toX]

@[simp] theorem toX_ne_X5 (r : Reg64) : (r.toX = .X5) = False := by cases r <;> simp [Reg64.toX]

@[simp] theorem toX_ne_X6 (r : Reg64) : (r.toX = .X6) = False := by cases r <;> simp [Reg64.toX]

@[simp] theorem toX_reserved (r : Reg64) : r.toX.reserved = false := by cases r <;> rfl

@[simp] theorem getXReg_setXReg (regs : Reg64s) (a b : XReg) (v : BitVec 64) :
    (regs.setXReg a v).getXReg b = if b = a then UInt64.ofBitVec v else regs.getXReg b := by
  cases a <;> cases b <;> rfl

@[simp] theorem SP_setXReg (regs : Reg64s) (a : XReg) (v : BitVec 64) :
    (regs.setXReg a v).SP = regs.SP := by
  cases a <;> rfl

@[simp] theorem setX_regs (m : MachineData) (r : XReg) (v : BitVec 64) :
    (m.setX r v).regs = m.regs.setXReg r v := rfl

@[simp] theorem setX_dmem (m : MachineData) (r : XReg) (v : BitVec 64) :
    (m.setX r v).dmem = m.dmem := rfl

@[simp] theorem setX_status (m : MachineData) (r : XReg) (v : BitVec 64) :
    (m.setX r v).status = m.status := rfl

@[simp] theorem getRegOrZr_xr (regs : Reg64s) (r : XReg) :
    regs.getRegOrZr (xr r) = (regs.getXReg r).toBitVec := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]

@[simp] theorem getRegOrZr_xzr (regs : Reg64s) :
    regs.getRegOrZr (.low .XZR .W64 : RegOrZr .W64) = 0#64 := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]

@[simp] theorem getRegOrSp_xs (regs : Reg64s) (r : XReg) :
    regs.getRegOrSp (xs r) = (regs.getXReg r).toBitVec := by
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take]

@[simp] theorem ofInt_toInt64 (k : Int64) : BitVec.ofInt 64 k.toInt = k.toBitVec := by
  rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]

theorem StateRel.get {s : QState} {m : MachineData} (h : StateRel s m) (r : Reg64) :
    m.regs.getXReg r.toX = s.reg r := h.1 r

/-- Setting a register that holds no QM register keeps the relation. -/
theorem StateRel.setX_other {s : QState} {m : MachineData} (h : StateRel s m) {x : XReg}
    (hx : ofX x = none) (v : BitVec 64) : StateRel s (m.setX x v) := by
  refine ⟨fun r => ?_, h.2⟩
  have : r.toX ≠ x := fun e => by rw [← e, ofX_toX] at hx; cases hx
  simp [this, h.1 r]

theorem StateRel.setX_scratch {s : QState} {m : MachineData} (h : StateRel s m) {x : XReg}
    (hx : x.scratch = true) (v : BitVec 64) : StateRel s (m.setX x v) :=
  h.setX_other (by cases x <;> first | rfl | simp [XReg.scratch] at hx) v

/-- Setting a QM register's image. -/
theorem StateRel.setX {s : QState} {m : MachineData} (h : StateRel s m) (d : Reg64) {v : UInt64}
    {w : BitVec 64} (hw : w = v.toBitVec) : StateRel (s.setReg d v) (m.setX d.toX w) := by
  refine ⟨fun r => ?_, h.2⟩
  by_cases hrd : r = d
  · subst hrd; simp [hw]
  · have : r.toX ≠ d.toX := fun e => hrd (toX_inj e)
    simp [this, hrd, h.1 r]

theorem StateRel.status {s : QState} {m : MachineData} (h : StateRel s m) (f : StatusFlags) :
    StateRel s { m with status := f } := h

theorem Keeps.refl (m : MachineData) : Keeps m m := ⟨fun _ _ => rfl, rfl⟩

theorem Keeps.trans {m₁ m₂ m₃ : MachineData} (h₁ : Keeps m₁ m₂) (h₂ : Keeps m₂ m₃) :
    Keeps m₁ m₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.trans h₁.2⟩

theorem Keeps.setX {m m' : MachineData} (h : Keeps m m') {x : XReg} (hx : x.reserved = false)
    (v : BitVec 64) : Keeps m (m'.setX x v) := by
  refine ⟨fun r hr => ?_, by simp [h.2]⟩
  have : r ≠ x := fun e => by rw [e] at hr; rw [hr] at hx; cases hx
  simp [this, h.1 r hr]

theorem Keeps.status {m m' : MachineData} (h : Keeps m m') (f : StatusFlags) :
    Keeps m { m' with status := f } := h

theorem Keeps.dmem {m m' : MachineData} (h : Keeps m m') (d : DataMem) :
    Keeps m { m' with dmem := d } := h

/-! ## Memory -/

theorem loadBytes_congr {d₁ d₂ : DataMem} {a : BitVec 64} {n : Nat}
    (h : ∀ i < n, d₁.get? (a + .ofNat 64 i) = d₂.get? (a + .ofNat 64 i)) :
    d₁.loadBytes a n = d₂.loadBytes a n := by
  unfold Mem.loadBytes
  congr 1
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem loadBytes_At (bs : List UInt8) (a : BitVec 64) (hl : bs.length ≤ 2 ^ 64)
    (d : DataMem) : Mem.loadBytes (d.union (bs.At a)) a bs.length = some bs := by
  unfold Mem.loadBytes
  have hget : ∀ i ∈ List.range bs.length,
      (d.union (bs.At a)).get? (a + .ofNat 64 i) = some bs[i]! := by
    intro i hi
    have hi := List.mem_range.mp hi
    rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq, ExtHashMap.getElem?_union,
      ← ExtHashMap.get?_eq_getElem?, get?_At_idx _ _ _ (by omega) hl,
      List.getElem?_eq_getElem hi, getElem!_pos bs i hi]
    rfl
  rw [List.map_congr_left hget]
  have : (List.range bs.length).map (fun i => some bs[i]!) = bs.map some := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.length_map, List.length_range] at h₁
    simp [List.getElem?_eq_getElem h₁]
  rw [this, List.mapM_map]
  simpa using List.mapM_pure (m := Option) (f := id) (l := bs)

/-- Two aligned words at different addresses share no byte. -/
theorem aligned_disjoint {a b : UInt64} (ha : a.toNat % 8 = 0) (hb : b.toNat % 8 = 0) (hab : b ≠ a)
    {i j : Nat} (hi : i < 8) (hj : j < 8) :
    b.toBitVec + .ofNat 64 i ≠ a.toBitVec + .ofNat 64 j := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec] at h'
  have hb' := b.toNat_lt_size
  have ha' := a.toNat_lt_size
  have hba : b.toNat ≠ a.toNat := fun e => hab (UInt64.toNat_inj.mp e)
  simp only [UInt64.size] at hb' ha'
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  omega

theorem MemRel.store {q : UInt64 → Option UInt64} {d : DataMem} (hm : MemRel q d) {a v : UInt64}
    (h : q a = some v) (x : UInt64) :
    MemRel (Function.update q a (some x)) (Mem.storeInt d a.toBitVec 8 x.toBitVec.toInt) := by
  have ha := (hm a v h).1
  have hlen : (Int.toBytes 8 x.toBitVec.toInt).length = 8 := Int.toBytes_length _ _
  intro b y hb
  by_cases hba : b = a
  · subst hba
    simp only [Function.update_self, Option.some.injEq] at hb
    subst hb
    refine ⟨ha, ?_⟩
    unfold Mem.storeInt Mem.storeBytes
    have := loadBytes_At (Int.toBytes 8 x.toBitVec.toInt) b.toBitVec (by omega) d
    rwa [hlen] at this
  · rw [Function.update_of_ne hba] at hb
    obtain ⟨hb8, hload⟩ := hm b y hb
    refine ⟨hb8, ?_⟩
    rw [← hload]
    apply loadBytes_congr
    intro i hi
    unfold Mem.storeInt Mem.storeBytes
    rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq,
      ExtHashMap.getElem?_union_of_not_mem_right]
    rw [mem_At_iff]
    rintro ⟨j, hj, he⟩
    exact aligned_disjoint ha hb8 hba hi (hlen ▸ hj) he

theorem loadInt_of_rel {q : UInt64 → Option UInt64} {d : DataMem} (hm : MemRel q d) {a v : UInt64}
    (h : q a = some v) : Mem.loadInt d a.toBitVec 8 = some (Int.ofBytes v.toBytes) := by
  simp [Mem.loadInt, (hm a v h).2]

theorem load_All {q : UInt64 → Option UInt64} {m : MachineData} (hm : MemRel q m.dmem)
    {a v : UInt64} (h : q a = some v) (ret : BitVec 64 → MachineData → Effects)
    (P : MachineState → Prop) :
    (m.load a.toBitVec .W64 ret).All P = (ret v.toBitVec m).All P := by
  unfold MachineData.load
  simp only [Effects.All, MemWidth.bytes, loadInt_of_rel hm h]
  rw [UInt64.toBytes, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]

theorem store_All {q : UInt64 → Option UInt64} {m : MachineData} (hm : MemRel q m.dmem)
    {a v : UInt64} (h : q a = some v) (x : BitVec 64) (ret : MachineData → Effects)
    (P : MachineState → Prop) :
    (m.store (w := .W64) a.toBitVec x ret).All P =
      (ret { m with dmem := Mem.storeInt m.dmem a.toBitVec 8 x.toInt }).All P := by
  unfold MachineData.store
  simp only [Effects.All, MemWidth.bytes, loadInt_of_rel hm h]

theorem StateRel.store {s : QState} {m : MachineData} (hr : StateRel s m) {a v : UInt64}
    (h : s.mem a = some v) (x : UInt64) :
    StateRel (s.setMem a x) { m with dmem := Mem.storeInt m.dmem a.toBitVec 8 x.toBitVec.toInt } :=
  ⟨hr.1, hr.2.store h x⟩

/-! ## `Effects.All` -/

theorem Effects.All.mono {P Q : MachineState → Prop} (hPQ : ∀ st, P st → Q st) {e : Effects}
    (h : e.All P) : e.All Q := by
  induction e with
  | done => exact hPQ _ h
  | unimplemented | unaligned_sp | nonmem_load | nonmem_store => exact h
  | undefined _ ih => exact fun v => ih v (h v)
  | require_read_access _ _ _ ih | require_write_access _ _ _ ih | require_exec_access _ _ ih =>
    exact ih () h

end

end NativeArm
