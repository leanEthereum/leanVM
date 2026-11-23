module

public import NativeRustcArm.Sym
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.MemLemmas

/-!
# Frames read by words

The tables' functions keep their values in callee-saved registers and in 8-byte slots of their
frame. A block runs from a fresh environment of the machine state (`Env.ofMachine`), its frame
region 0. This module reads words out of the executor's results: a word the environment loads is
`wordOf` of its memory (`load8`); a word of a region after a block is the value of its symbolic
load (`match_wordOf`), the environment's word where no write of the block covers it
(`match_wordOf_keep`).
-/

namespace NativeRustcVmArm.Tables

open NativeRustcArm NativeRustcArm.Sym
open NativeRustcVm (wordOf bytesFrom leNat)

public section

theorem leNat_eq_ofBytes : ∀ bs : List UInt8, leNat bs = Nat.ofBytes bs
  | [] => rfl
  | b :: bs => by
    rw [NativeRustcVm.leNat_cons, leNat_eq_ofBytes bs]
    show _ = Nat.ofBytes bs * 256 + b.toNat
    omega

theorem toBitVec_wordOf (d : Mem 64) (a : BitVec 64) :
    (wordOf d a).toBitVec = BitVec.ofNat 64 (Nat.ofBytes (bytesFrom d a 8)) := by
  rw [wordOf, ← leNat_eq_ofBytes]
  rfl

/-- **A word the environment loads**: `wordOf` of its memory. -/
theorem load8 (env : Env) (r o : Nat) :
    env.load r o 8 = (wordOf env.mem0 (env.base r + BitVec.ofNat 64 o)).toBitVec := by
  rw [toBitVec_wordOf, Env.load, ofBytes_natCast, BitVec.ofInt_natCast]
  congr 3
  funext i
  rw [addr_add]

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **A word of a region after a block**: its symbolic load's value. -/
theorem match_wordOf (hm : Match env S m) (hwf : env.WF) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) :
    (NativeRustcVm.wordOf m.dmem (b + BitVec.ofNat 64 o)).toBitVec =
      (loadSym S.mem r o 8).eval env := by
  have h1 := (hm.loadSym hwf hb hle le_rfl).1
  have hget : ∀ i < 8, m.dmem.get? (b + BitVec.ofNat 64 o + BitVec.ofNat 64 i) =
      some (memByteD env S.mem r b (o + i)) := fun i hi => by
    rw [addr_add, hm.mem r b sz hb (o + i) (by omega), memByte_eq hwf hb (by omega)]
  rw [loadInt_of_get? _ _ 8 _ hget, ofBytes_natCast, Option.some.injEq] at h1
  have hbs : bytesFrom m.dmem (b + BitVec.ofNat 64 o) 8 =
      (List.range 8).map fun i => memByteD env S.mem r b (o + i) := by
    unfold bytesFrom
    apply List.map_congr_left
    intro i hi
    rw [hget i (List.mem_range.mp hi)]
    rfl
  rw [toBitVec_wordOf, hbs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have h2 := (hm.loadSym hwf hb hle le_rfl).2
  omega

/-- A word of a region no write of the block covers: the environment's. -/
theorem match_wordOf_keep (hm : Match env S m) (hwf : env.WF) {r o : Nat} {b : BitVec 64}
    {sz : Nat} (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz)
    (hk : loadSym S.mem r o 8 = .load r o 8) :
    NativeRustcVm.wordOf m.dmem (b + BitVec.ofNat 64 o) =
      NativeRustcVm.wordOf env.mem0 (b + BitVec.ofNat 64 o) := by
  apply UInt64.toBitVec_inj.mp
  rw [match_wordOf hm hwf hb hle, hk]
  show env.load r o 8 = _
  rw [load8, Env.base_eq hb]

omit [Labels] in
/-- `cmp x, #v` unsigned below: `x < v`. -/
theorem cmp_ult_lit (x : UInt64) (v : Nat) (hv : v < 2 ^ 64) :
    CmpOp.ult.apply .W64 x.toBitVec (BitVec.ofNat 64 v) = decide (x.toNat < v) := by
  simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  rfl

omit [Labels] in
/-- `cmp x, #v` equal: `x = v`. -/
theorem cmp_eq_lit (x : UInt64) (v : Nat) (hv : v < 2 ^ 64) :
    CmpOp.eq.apply .W64 x.toBitVec (BitVec.ofNat 64 v) = decide (x.toNat = v) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv]
  rfl

omit [Labels] in
theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simpa [Nat.toUInt64] using h

omit [Labels] in
/-- `x - v` of a word at least `v`. -/
theorem sub_lit (x : BitVec 64) (v : Nat) (h : v ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 v)).toNat = x.toNat - v := by
  have hx := x.isLt
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega)]
  omega

omit [Labels] in
/-- `x + v` without overflow. -/
theorem add_lit (x : BitVec 64) (v : Nat) (h : x.toNat + v < 2 ^ 64) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 v)).toNat = x.toNat + v := by
  simp only [BinOp.apply, low_W64, ext_W64]
  exact NativeRustcVm.toNat_add_ofNat h

/-- A pointer into region `0` of a machine state's environment. -/
theorem eval_ptr0 (m : MachineData) (b : BitVec 64) (F : Nat) (rs : List (BitVec 64 × Nat))
    (o : Int) : (Sym.ptr 0 o).eval (Env.ofMachine m ((b, F) :: rs)) = b + BitVec.ofInt 64 o := by
  simp [Sym.eval]

end

end NativeRustcVmArm.Tables
