import LeanVM.Arithmetization.Channels
import LeanVM.Semantics.Lemmas
import Clean.Air.Balance

/-!
# Tests: the bus channels

A classic test for kernel evaluation. The six channels' separators and directions are pinned
against specification §5.1 and `tables.rs:94-96`, the three element orders against §6.1, §6.2,
§6.4 and the flush builders of `tables.rs:131-170`, on literal messages, and the sixteen-slot
tuples against §5.1. The read gadgets are checked to emit a `pull` then a `push` with the count
advanced by `g`. `imageOf` is read off a two-row prover data, which is `WellShapedData`, and a
correct memory read satisfies `MemPull.Guarantees` while a wrong word does not; a three-row
store and the empty store are shown truncated and not well shaped. The bytecode guarantee is
decodability alone, program- and data-free: an instruction's entry passes on
every data, a flag pair that is no store mode and a nonzero spare slot fail at every counter,
and the guarantee is the same proposition on any two data.

The last section exhibits Clean's bus over `K`: `-1 = 1`,
so a push-multiplicity interaction on a pull channel is granted the typed guarantee, every
`Requirements` of `Channel.toRaw` holds at the multiplicities `0` and `1`, and
`BalancedInteractions` is unsatisfiable for two or more interactions. These are the facts the
channel pairs and `BalancedPair` work around, and that an upstream change to Clean's balance
must remove.
-/

namespace LeanVMTests.Arithmetization

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization

/-! ## Separators and directions (specification §5.1; `tables.rs:94-96`) -/

#guard channelSep StatePull.toRaw = gpow 0
#guard channelSep StatePush.toRaw = gpow 0
#guard channelSep MemPull.toRaw = gpow 1
#guard channelSep MemPush.toRaw = gpow 1
#guard channelSep BytecodePull.toRaw = gpow 2
#guard channelSep BytecodePush.toRaw = gpow 2

#guard channelDir StatePull.toRaw = .pull
#guard channelDir MemPull.toRaw = .pull
#guard channelDir BytecodePull.toRaw = .pull
#guard channelDir StatePush.toRaw = .push
#guard channelDir MemPush.toRaw = .push
#guard channelDir BytecodePush.toRaw = .push

-- The separators are the words `1, 2, 4`: `g^0, g^1, g^2` with `g = 0x2`.
#guard channelSep StatePull.toRaw = 0x1
#guard channelSep MemPull.toRaw = K.ofBits 0x2
#guard channelSep BytecodePull.toRaw = K.ofBits 0x4

/-- Separators and directions decide in the kernel. -/
example : channelSep MemPull.toRaw = gpow 1 ∧ channelDir MemPull.toRaw = .pull ∧
    channelDir MemPush.toRaw = .push := by
  decide

/-- The two channels of a pair are distinct raw channels, by name. -/
example : StatePull.toRaw ≠ StatePush.toRaw :=
  fun h ↦ absurd (congrArg RawChannel.name h) (by decide)

/-- A channel that is none of the six has separator `0`, which is no separator. -/
def foreign : RawChannel K where
  name := "other"
  arity := 0
  Guarantees _ _ _ := True
  Requirements _ _ _ := True

#guard channelSep foreign = 0
#guard channelDir foreign = .push
example : channelSep foreign ≠ channelSep MemPull.toRaw := by decide

/-! ## Element orders (specification §6.1, §6.2, §6.4; `tables.rs:131-170`) -/

def st : Regs K := ⟨gpow 3, gpow 5⟩
def mm : MemMsg K := ⟨gpow 3 * gpow 5, gpow 2, #v[K.ofBits 7, K.ofBits 8, K.ofBits 9]⟩
def bm : BytecodeMsg K := ⟨gpow 3, gpow 4, Opcode.deref.code, #v[gpow 4, 1, gpow 5, 1, 0, 0, 0]⟩

#guard (toElements st).toList = [gpow 3, gpow 5]
#guard (toElements mm).toList = [gpow 3 * gpow 5, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9]
#guard (toElements bm).toList =
  [gpow 3, gpow 4, Opcode.deref.code, gpow 4, 1, gpow 5, 1, 0, 0, 0]

/-- The orders as theorems, through the three `toElements` lemmas. -/
example : (toElements st).toList = [gpow 3, gpow 5] := regs_toElements st
example : (toElements mm).toList = [gpow 3 * gpow 5, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9] := by
  rw [memMsg_toElements]; rfl
example : (toElements bm).toList =
    [gpow 3, gpow 4, Opcode.deref.code, gpow 4, 1, gpow 5, 1, 0, 0, 0] := by
  rw [bytecodeMsg_toElements]; rfl

-- Sizes: two, five, and ten coordinates after the separator.
example : size Regs = 2 := rfl
example : size MemMsg = 5 := rfl
example : size BytecodeMsg = 10 := rfl

/-- The state message is the machine's register pair: `Regs.initial` is a message. -/
example : (toElements Regs.initial).toList = [1, 1] := by
  rw [regs_toElements]
  rfl

/-! ## The sixteen-slot tuples (specification §5.1) -/

#guard (busTuple StatePull.toRaw (toElements st).toList).toList =
  [1, gpow 3, gpow 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (busTuple MemPush.toRaw (toElements mm).toList).toList =
  [g, gpow 3 * gpow 5, gpow 2, K.ofBits 7, K.ofBits 8, K.ofBits 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (busTuple BytecodePull.toRaw (toElements bm).toList).toList =
  [g ^ 2, gpow 3, gpow 4, Opcode.deref.code, gpow 4, 1, gpow 5, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Slot `0` is the separator, slot `3` the first limb, slot `6` the padding. -/
example : (busTuple MemPull.toRaw (toElements mm).toList)[0] = g ∧
    (busTuple MemPull.toRaw (toElements mm).toList)[3] = K.ofBits 7 ∧
    (busTuple MemPull.toRaw (toElements mm).toList)[6] = 0 := by
  simp only [busTuple_getElem, memMsg_toElements]
  decide

/-! ## The read gadgets (specification §6.2 "Flush rules") -/

/-- `memRead` is a `pull` then a `push`, the count advanced by `g`. -/
example (a c : Expression K) (v : Vector (Expression K) 3) :
    (memRead a c v).operations 0 =
      [.interact ⟨MemPull.toRaw, -1, toElements (⟨a, c, v⟩ : MemMsg (Expression K)), true⟩,
       .interact ⟨MemPush.toRaw, 1,
         toElements (⟨a, Expression.const g * c, v⟩ : MemMsg (Expression K)), false⟩] :=
  rfl

/-- `bytecodeRead` likewise. -/
example (pc c o : Expression K) (op : Vector (Expression K) 7) :
    (bytecodeRead pc c o op).operations 0 =
      [.interact ⟨BytecodePull.toRaw, -1,
         toElements (⟨pc, c, o, op⟩ : BytecodeMsg (Expression K)), true⟩,
       .interact ⟨BytecodePush.toRaw, 1,
         toElements (⟨pc, Expression.const g * c, o, op⟩ : BytecodeMsg (Expression K)),
         false⟩] :=
  rfl

/-- The pull's multiplicity `-1` evaluates to `1`: every interaction has multiplicity `1`. -/
example (env : Environment K) : Expression.eval env (-1 : Expression K) = 1 := by
  show (-1 : K) * 1 = 1
  decide

/-! ## The image in the prover data -/

/-- Two memory words, matched on arity so that the kernel never compares table names. The
program has no table: it is public. -/
def sampleData : ProverData K := fun _ n ↦
  match n with
  | 3 => #[#v[1, K.ofBits 2, K.ofBits 3], #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]]
  | _ => #[]

/-- A store whose table is told apart by name: `imageOf` reads `"mem"`. -/
def namedData : ProverData K := fun name n ↦
  match name, n with
  | "mem", 3 => #[#v[K.ofBits 9, K.ofBits 9, K.ofBits 9]]
  | _, _ => #[]

/-- Three memory words: not a power of two. -/
def threeRows : ProverData K := fun _ n ↦
  match n with
  | 3 => #[#v[1, K.ofBits 2, K.ofBits 3], #v[K.ofBits 4, K.ofBits 5, K.ofBits 6], #v[K.ofBits 7, K.ofBits 8, K.ofBits 9]]
  | _ => #[]

/-- The empty store. -/
def emptyData : ProverData K := fun _ _ ↦ #[]

#guard (imageOf sampleData).1 = 1
#guard (imageOf sampleData).2 0 = E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3)
#guard (imageOf sampleData).2 1 = E.ofLimbs (K.ofBits 4) (K.ofBits 5) (K.ofBits 6)
#guard (imageOf namedData).1 = 0
#guard (imageOf namedData).2 0 = E.ofLimbs (K.ofBits 9) (K.ofBits 9) (K.ofBits 9)

-- The floor logarithm truncates: three rows give a one-bit image without the third word.
#guard (imageOf threeRows).1 = 1
#guard (imageOf threeRows).2 1 = E.ofLimbs (K.ofBits 4) (K.ofBits 5) (K.ofBits 6)
-- The empty store: one word `0`.
#guard (imageOf emptyData).1 = 0
#guard (imageOf emptyData).2 0 = 0

/-- The log-size of two rows is `1`, through `Nat.log_pow`, under the cap. -/
theorem sampleData_logSize : (imageOf sampleData).1 = 1 := by
  show min (Nat.log 2 (#[(#v[1, K.ofBits 2, K.ofBits 3] : Vector K 3), #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]]).size) maxLogMem = 1
  have h := Nat.log_pow (b := 2) (by norm_num) 1
  rw [pow_one] at h
  rw [show (#[(#v[1, K.ofBits 2, K.ofBits 3] : Vector K 3), #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]]).size = 2 from rfl, h]
  decide

/-- The two-row store is well shaped. -/
theorem sampleData_wellShaped : WellShapedData sampleData where
  memRows_size := by rw [sampleData_logSize]; decide +kernel

/-- The same, through the power-of-two reading. -/
example : WellShapedData sampleData :=
  (wellShapedData_iff _).mpr ⟨1, by decide, by decide +kernel⟩

/-- The floor logarithm of three rows is `1`, under the cap. -/
theorem threeRows_logSize : (imageOf threeRows).1 = 1 := by
  show min (Nat.log 2 (memRows threeRows).size) maxLogMem = 1
  rw [Nat.log_eq_of_pow_le_of_lt_pow (b := 2) (m := 1) (n := (memRows threeRows).size)
    (by decide +kernel) (by decide +kernel)]
  decide

/-- Three rows are not well shaped: the third is dropped. -/
theorem threeRows_not_wellShaped : ¬ WellShapedData threeRows := by
  intro h
  have hsize := h.memRows_size
  rw [threeRows_logSize] at hsize
  exact absurd hsize (by decide +kernel)

/-- The empty store is not well shaped: its image still has one word. -/
example : ¬ WellShapedData emptyData := by
  intro h
  have hsize := h.memRows_size
  rw [show (imageOf emptyData).1 = 0 by
    show min (Nat.log 2 (memRows emptyData).size) maxLogMem = 0
    rw [show (memRows emptyData).size = 0 from rfl, Nat.log_zero_right]
    decide] at hsize
  exact absurd hsize (by decide)

/-- Index `1` of the sample image. -/
def one : Fin (2 ^ (imageOf sampleData).1) := ⟨1, by rw [sampleData_logSize]; decide⟩

/-- A correct read satisfies the memory guarantee: word `1` sits at `g^1`. -/
example : MemPull.Guarantees ⟨gpow 1, gpow 0, #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩ sampleData := by
  show (imageOf sampleData).2.read (gpow 1) = some (E.ofLimbs (K.ofBits 4) (K.ofBits 5) (K.ofBits 6))
  rw [show gpow 1 = gpow (one : ℕ) from rfl,
    MemImage.read_gpow (by rw [sampleData_logSize]; decide),
    imageOf_apply sampleData_wellShaped one (v := #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]) (by decide +kernel)]
  rfl

/-- A wrong word does not: the guarantee is a statement about the committed image. -/
example : ¬ MemPull.Guarantees ⟨gpow 1, gpow 0, #v[K.ofBits 4, K.ofBits 5, K.ofBits 7]⟩ sampleData := by
  show ¬ (imageOf sampleData).2.read (gpow 1) = some (E.ofLimbs (K.ofBits 4) (K.ofBits 5) (K.ofBits 7))
  rw [show gpow 1 = gpow (one : ℕ) from rfl,
    MemImage.read_gpow (by rw [sampleData_logSize]; decide),
    imageOf_apply sampleData_wellShaped one (v := #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]) (by decide +kernel)]
  decide +kernel

/-- The bytecode guarantee is decodability alone: an instruction's entry passes, at any counter
and with any count, over every data (the guarantee reads no data). -/
example (pc c : K) (data : ProverData K) :
    BytecodePull.Guarantees ⟨pc, c, Opcode.jump.code, #v[1, 1, 1, 0, 0, 0, 0]⟩ data :=
  ⟨_, decode_entry (.jump 1 1 1)⟩

/-- An entry that decodes to nothing is no bytecode read at any counter: the flag pair `(1, 1)`
is no store mode. -/
example (pc c : K) (data : ProverData K) :
    ¬ BytecodePull.Guarantees ⟨pc, c, Opcode.deref.code, #v[1, 1, 1, 1, 1, 0, 0]⟩ data := by
  rintro ⟨ins, hdec⟩
  have h : decode (#v[Opcode.deref.code] ++ #v[(1: K), 1, 1, 1, 1, 0, 0]) = none := by
    decide +kernel
  exact nomatch h.symm.trans hdec

/-- Nor is a nonzero spare slot. -/
example (pc c : K) (data : ProverData K) :
    ¬ BytecodePull.Guarantees ⟨pc, c, Opcode.xor.code, #v[1, 1, 1, 0, 0, 0, 1]⟩ data := by
  rintro ⟨ins, hdec⟩
  have h : decode (#v[Opcode.xor.code] ++ #v[(1: K), 1, 1, 0, 0, 0, 1]) = none := by
    decide +kernel
  exact nomatch h.symm.trans hdec

/-- The guarantee names no program and reads no data: it is the same proposition on any two
data, where the memory guarantee reads its image off the data. -/
example (b : BytecodeMsg K) (data data' : ProverData K) :
    BytecodePull.Guarantees b data ↔ BytecodePull.Guarantees b data' :=
  Iff.rfl

/-- The state pull guarantees nothing. -/
example (s : Regs K) (data : ProverData K) : StatePull.Guarantees s data := trivial

/-! ## Clean's bus over `K` -/

/-- `-1 = 1` in `K`: a multiplicity carries no direction. -/
example : (-1 : K) = 1 := by decide

/-- Clean's `toRaw` grants the typed guarantee at the multiplicity of a push. -/
example (v : Vector K 5) (data : ProverData K) :
    MemPull.toRaw.Guarantees 1 v data ↔ MemPull.Guarantees (fromElements v) data := by
  have h : (1: K) = -1 := by decide
  simp only [Channel.toRaw]
  exact ⟨fun f ↦ f h, fun g _ ↦ g⟩

/-- Clean's `Requirements` hold of every interaction a component emits, at multiplicity `1` … -/
example (v : Vector K 5) (data : ProverData K) : MemPull.toRaw.Requirements 1 v data :=
  fun h ↦ absurd (by decide : (1: K) = -1) h

/-- … and at multiplicity `0`. -/
example (v : Vector K 5) (data : ProverData K) : MemPull.toRaw.Requirements 0 v data :=
  fun _ h ↦ absurd rfl h

/-- A `pull` on a push channel is granted nothing: the push channels carry `True`. -/
example (v : Vector K 5) (data : ProverData K) : MemPush.toRaw.Guarantees (-1) v data :=
  fun _ ↦ trivial

/-- Clean's balance is a field sum with the side condition `length < ringChar F`, and
`ringChar K = 2`: no two interactions balance. -/
example : ringChar K = 2 := ringChar.eq K 2

example (i j : Interaction K) (rest : List (Interaction K)) :
    ¬ BalancedInteractions (i :: j :: rest) := by
  rintro ⟨h, -⟩
  rw [ringChar.eq K 2] at h
  simp at h

end LeanVMTests.Arithmetization
