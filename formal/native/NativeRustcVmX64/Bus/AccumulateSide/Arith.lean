module

public import NativeRustcVmX64.Bus.AccumulateSide.Kit
public import NativeRustcVmX64.Bus.AccumulateSide.Vals

/-!
# `accumulate_side`: numbers, words and the stack arguments (x86-64)

Words as numbers (`tb`, `u64_eq`, `ult_ofNat`, `shl4`); the stack arguments' words
(`argWord0`) and their description (`holdsArgs`); an input's word in the body (`St.load`);
a description's locations evaluated in a block's environment (`St.ev`).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

theorem tb (n : Nat) : (n.toUInt64).toBitVec = BitVec.ofNat 64 n := rfl

theorem u64_ofNat (n : Nat) : UInt64.ofBitVec (BitVec.ofNat 64 n) = n.toUInt64 := rfl

theorem bv_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)]; exact h)

theorem u64_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : UInt64.ofBitVec x = n.toUInt64 := by
  rw [bv_eq h]; rfl

theorem ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem toNat_ofNat_lt {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem shl4 (x : BitVec 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * x.toNat) := by
  have h4 : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := rfl
  simp only [BinOp.apply, low_W64, ext_W64, h4]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm]

theorem addr16 (a : BitVec 64) {x : Nat} (h : a.toNat + 16 + 16 * x < 2 ^ 64) :
    (a + 16#64 + BitVec.ofNat 64 (16 * x)).toNat = a.toNat + 16 + 16 * x := by
  have h1 : (a + 16#64).toNat = a.toNat + 16 :=
    NativeRustcVm.toNat_add_ofNat (a := a) (i := 16) (by omega)
  rw [NativeRustcVm.toNat_add_ofNat (by rw [h1]; omega), h1]

theorem step16 (a : BitVec 64) (x : Nat) :
    16#64 + (a + 16#64 + BitVec.ofNat 64 (16 * x)) = a + 16#64 + BitVec.ofNat 64 (16 * (x + 1)) := by
  rw [show 16 * (x + 1) = 16 * x + 16 by omega, BitVec.ofNat_add]
  ac_rfl

theorem ofBitVec_xor (x y : BitVec 64) :
    UInt64.ofBitVec (x ^^^ y) = UInt64.ofBitVec x ^^^ UInt64.ofBitVec y := rfl

theorem xor64 (x y : BitVec 64) : BinOp.apply .xor .W64 x y = x ^^^ y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem eq64 (x y : BitVec 64) : CmpOp.apply .eq .W64 x y = decide (x = y) := by
  simp only [CmpOp.apply, low_W64]
  by_cases h : x = y <;> simp [h]

theorem add64 (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp only [BinOp.apply, low_W64, ext_W64]

section
variable [Labels] {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {D : List (Sym × Nat)}
  {m : MachineData}

/-- A register's value. -/
theorem holds_reg {r : Reg64} {i : Nat} (h : m.regs.get64 r = (V i).toBitVec)
    (h' : Holds rs V D m) : Holds rs V ((Sym.reg r, i) :: D) m :=
  holds_cons (by unfold tval; rw [Sym.eval, Env.ofMachine_regs, h]) h'

/-- A word of region `0`'s value. -/
theorem holds_word {b : BitVec 64} {n o i : Nat} (hb : rs[0]? = some (b, n))
    (h : NativeRustcVm.WordAt m.dmem (off b o) (V i)) (h' : Holds rs V D m) :
    Holds rs V ((Sym.load 0 o 8, i) :: D) m :=
  holds_cons (by unfold tval; rw [Sym.eval, load_ofMachine hb h]) h'

/-- A location's value from its content after a block. -/
theorem holds_content {s : Sym} {i : Nat} {e : Env} {c : Sym}
    (h : tval rs m s = UInt64.ofBitVec (c.eval e)) (hc : c.eval e = (V i).toBitVec)
    (h' : Holds rs V D m) : Holds rs V ((s, i) :: D) m :=
  holds_cons (by rw [h, hc]) h'

end

theorem allOf_append {α : Type} {P : α → Prop} {l l' : List α} (h : AllOf P l) (h' : AllOf P l') :
    AllOf P (l ++ l') := by
  induction l with
  | nil => exact h'
  | cons a l ih => exact ⟨h.1, ih h.2⟩

section
variable [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

/-- A stack argument's word at the entry. -/
theorem argWord0 (h : Pre L rows bl Fm SL m0) {i : Nat} (hi : i < 11) :
    NativeRustcVm.WordAt m0.dmem (off (rspOf m0 + 8#64) (8 * i)) (UInt64.ofBitVec (stackArg m0 i)) := by
  rw [Ring.stackArg_eq]
  show NativeRustcVm.WordAt _ _ (UInt64.ofBitVec (UInt64.toBitVec _))
  rw [UInt64.ofBitVec_toBitVec]
  exact NativeRustcVm.wordAt_of_mapped (NativeRustcVm.Mapped.sub h.args.1 (by omega))

/-- **The stack arguments' description** where their words are the entry's. -/
theorem holdsArgs {rest : List (BitVec 64 × Nat)} {m : MachineData} {lp : Nat → UInt64}
    (hw : ∀ i < 11, NativeRustcVm.WordAt m.dmem (off (rspOf m0 + 8#64) (8 * i))
      (UInt64.ofBitVec (stackArg m0 i))) :
    Holds ((fb m0, F + 8) :: (rspOf m0 + 8#64, 88) :: rest) (Vt SL m0 lp) DA m := by
  have key : ∀ i < 11, tval ((fb m0, F + 8) :: (rspOf m0 + 8#64, 88) :: rest) m
      (.load 1 (8 * i) 8) = UInt64.ofBitVec (stackArg m0 i) := fun i hi ↦ by
    unfold tval
    rw [Sym.eval, load_ofMachine (r := 1) (n := 88) rfl (hw i hi)]
  intro p hp
  simp only [DA, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [key 0 (by decide), key 1 (by decide), key 2 (by decide), key 3 (by decide),
    key 4 (by decide), key 5 (by decide), key 6 (by decide), key 7 (by decide), key 8 (by decide),
    key 9 (by decide), key 10 (by decide)]

/-- The literals' description. -/
theorem holdsDl {rs : List (BitVec 64 × Nat)} {m : MachineData} {lp : Nat → UInt64} :
    Holds rs (Vt SL m0 lp) Dl m := by
  intro p hp
  simp only [Dl, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> rfl

/-- **A body state's stack arguments.** -/
theorem St.holdsDA (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {o : Nat} {m : MachineData} (hst : St m0 O V D o m)
    (hO : ∀ q, O q → outs m0 q) {rest : List (BitVec 64 × Nat)} {lp : Nat → UInt64} :
    Holds ((fb m0, F + 8) :: (rspOf m0 + 8#64, 88) :: rest) (Vt SL m0 lp) DA m :=
  holdsArgs fun i hi ↦ St.word h hst hO h.argsIn (by omega) (argWord0 h hi)

/-- **A word of an input** read by a block of the body, its region `r` at `b + j`. -/
theorem St.load (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {o : Nat} {m : MachineData} (hst : St m0 O V D o m)
    (hO : ∀ q, O q → outs m0 q) {a : BitVec 64} {n : Nat} (hi : In m0 a n)
    {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {ret : BitVec 64} {r j sz : Nat}
    (hr : rs[r]? = some (off a j, sz)) {o' : Nat} (ho : j + o' + 8 ≤ n) {w : UInt64}
    (hw : NativeRustcVm.WordAt m0.dmem (off a (j + o')) w) :
    (Env.ofMachine m rs vs ret).load r o' 8 = w.toBitVec := by
  have := St.word h hst hO hi ho hw
  rw [← off_off] at this
  exact load_ofMachine hr this

end

end

end NativeRustcVmX64.Bus.AccumulateSide
