import Rv64Verifier.Proofs.Bytecode.Contracts
import Rv64Verifier.Proofs.Bytecode.Bits

/-!
# `Bytecode::evaluate`: the loop's environment

The prologue (`Proofs/Bytecode/EvalSetup.lean`) saves the callee-saved registers, checks the
point's size, computes the two eq tables (`eq_kernel`) and the 2048 buckets (`vec![ZERO; 2048]`)
and caches the fields the loop reads on the stack; `Env` names the state there (`tL`) and the
three buffers, `EnvOk` says what holds of them. From there on the loop writes only the callees'
stack, the frame's scratch slots and the buckets (`Scratch`): `LoopMem e t` says every other
doubleword is `tL`'s. Reads through `LoopMem`: the cached fields (`LoopMem.slot`), the eq tables
(`LoopMem.low`, `LoopMem.high`), the `Bytecode`'s parts (`LoopMem.bc_getMem`,
`LoopMem.bc_getHalfword`).
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts

/-- `sp` inside `evaluate`. -/
@[rv_addr] def fp (s : MachineState) : Word := s.getReg .x2 - 1968

/-- The prologue's frame: `sp`, the return address and the callee-saved registers below the
entry's `sp`. -/
structure Saved (s t : MachineState) : Prop where
  sp : t.getReg .x2 = fp s
  r1 : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  r8 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  r9 : t.getMem (s.getReg .x2 - 24) = s.getReg .x9
  r18 : t.getMem (s.getReg .x2 - 32) = s.getReg .x18
  r19 : t.getMem (s.getReg .x2 - 40) = s.getReg .x19
  r20 : t.getMem (s.getReg .x2 - 48) = s.getReg .x20
  r21 : t.getMem (s.getReg .x2 - 56) = s.getReg .x21
  r22 : t.getMem (s.getReg .x2 - 64) = s.getReg .x22
  r23 : t.getMem (s.getReg .x2 - 72) = s.getReg .x23
  r24 : t.getMem (s.getReg .x2 - 80) = s.getReg .x24
  r25 : t.getMem (s.getReg .x2 - 88) = s.getReg .x25
  r26 : t.getMem (s.getReg .x2 - 96) = s.getReg .x26
  r27 : t.getMem (s.getReg .x2 - 104) = s.getReg .x27

/-- `Saved` carries over a step that keeps `sp` and the frame's top. -/
theorem Saved.of_frame {s t u : MachineState} (h : Saved s t) (hsp : u.getReg .x2 = t.getReg .x2)
    (hm : ∀ a, (s.getReg .x2).toNat - 104 ≤ a.toNat → a.toNat + 8 ≤ (s.getReg .x2).toNat →
      u.getMem a = t.getMem a)
    (hb : 1968 ≤ (s.getReg .x2).toNat) : Saved s u where
  sp := hsp.trans h.sp
  r1 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r1
  r8 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r8
  r9 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r9
  r18 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r18
  r19 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r19
  r20 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r20
  r21 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r21
  r22 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r22
  r23 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r23
  r24 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r24
  r25 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r25
  r26 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r26
  r27 := (hm _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.r27

/-- The entry state, the state at the loop's head the first time, and the three buffers. -/
structure Env where
  s : MachineState
  tL : MachineState
  low : Word
  high : Word
  bk : Word

namespace Env

@[rv_addr] def bcp (e : Env) : Word := e.s.getReg .x11
def bc (e : Env) : Model.BytecodeRust := readBytecode e.s e.bcp
def n (e : Env) : Nat := (e.s.getReg .x13).toNat
def m (e : Env) : Nat := min e.n 14
def point (e : Env) : List E := eListAt e.s (e.s.getReg .x12) e.n
def lowW (e : Env) : List E := Model.eqKernelRust (e.point.take e.m)
def highW (e : Env) : List E := Model.eqKernelRust (e.point.drop e.m)
@[rv_addr] def blocksPtr (e : Env) : Word := vecPtr e.s e.bcp
@[rv_addr] def blocksLen (e : Env) : Word := vecLen e.s e.bcp
@[rv_addr] def wordsPtr (e : Env) : Word := vecPtr e.s (e.bcp + 24)
@[rv_addr] def wordsLen (e : Env) : Word := vecLen e.s (e.bcp + 24)
@[rv_addr] def posPtr (e : Env) : Word := vecPtr e.s (e.bcp + 48)
@[rv_addr] def posLen (e : Env) : Word := vecLen e.s (e.bcp + 48)
@[rv_addr] def bytesPtr (e : Env) : Word := vecPtr e.s (e.bcp + 72)
@[rv_addr] def bytesLen (e : Env) : Word := vecLen e.s (e.bcp + 72)

end Env

/-- What the loop may write: the callees' stack below the frame, the frame's scratch slots
(`sp + 72 .. sp + 128`, `sp + 176 .. sp + 1864`) and the buckets. -/
@[rv_addr] def Scratch (e : Env) (a : Word) : Prop :=
  Within a (stackLo e.s evalStack) eqKernelStack ∨ Within a (fp e.s + 72) 56 ∨
    Within a (fp e.s + 176) 1688 ∨ Within a e.bk 49152

/-- Everything but the scratch is as at the loop's head. -/
def LoopMem (e : Env) (t : MachineState) : Prop := ∀ a, ¬ Scratch e a → t.getMem a = e.tL.getMem a

/-- What holds at the loop's head the first time. -/
structure EnvOk (e : Env) : Prop where
  pre : EvaluatePre e.s
  rodataL : RodataOk e.tL
  short : e.n < 64
  len : e.bc.len = 2 ^ e.n
  saved : Saved e.s e.tL
  out : e.tL.getMem (e.s.getReg .x2 - 1960) = e.s.getReg .x10
  c16 : e.tL.getMem (e.s.getReg .x2 - 1952) = e.bytesPtr
  c24 : e.tL.getMem (e.s.getReg .x2 - 1944) = e.wordsPtr
  c32 : e.tL.getMem (e.s.getReg .x2 - 1936) = e.blocksPtr + (e.blocksLen * 16 + e.blocksLen * 8)
  c40 : e.tL.getMem (e.s.getReg .x2 - 1928) = e.bytesLen
  c48 : e.tL.getMem (e.s.getReg .x2 - 1920) = e.wordsLen
  c56 : e.tL.getMem (e.s.getReg .x2 - 1912) = e.high
  c64 : (e.tL.getMem (e.s.getReg .x2 - 1904)).toNat = 2 ^ (e.n - e.m)
  c128 : e.tL.getMem (e.s.getReg .x2 - 1840) = e.posPtr
  c136 : e.tL.getMem (e.s.getReg .x2 - 1832) = e.posLen
  c144 : e.tL.getMem (e.s.getReg .x2 - 1824) = 2048
  c152 : e.tL.getMem (e.s.getReg .x2 - 1816) = e.bk
  c160 : (e.tL.getMem (e.s.getReg .x2 - 1808)).toNat = 2 ^ e.m
  c168 : e.tL.getMem (e.s.getReg .x2 - 1800) = e.low
  heapL : HeapOk e.tL
  monoL : heapNext e.s ≤ heapNext e.tL
  lowIn : heapNext e.s ≤ e.low.toNat ∧ e.low.toNat + 24 * 2 ^ e.m ≤ heapNext e.tL ∧
    e.low.toNat % 8 = 0
  highIn : heapNext e.s ≤ e.high.toNat ∧ e.high.toNat + 24 * 2 ^ (e.n - e.m) ≤ heapNext e.tL ∧
    e.high.toNat % 8 = 0
  bkIn : heapNext e.s ≤ e.bk.toNat ∧ e.bk.toNat + 49152 ≤ heapNext e.tL ∧ e.bk.toNat % 8 = 0
  lowBk : Apart e.low (24 * 2 ^ e.m) e.bk 49152
  highBk : Apart e.high (24 * 2 ^ (e.n - e.m)) e.bk 49152
  lowVals : eListAt e.tL e.low (2 ^ e.m) = e.lowW
  highVals : eListAt e.tL e.high (2 ^ (e.n - e.m)) = e.highW
  bkVals : eListAt e.tL e.bk 2048 = List.replicate 2048 0
  frame : Transcript.DFrame e.s e.tL fun a ↦
    Within a (stackLo e.s evalStack) evalStack ∨ Within a nextAddr 8 ∨ Fresh e.s e.tL a

/-! ## Facts for `addr_omega` -/

namespace EnvOk

variable {e : Env} (he : EnvOk e)
include he

/-- `sp`, as numbers. -/
theorem sp : heapEnd + evalStack ≤ (e.s.getReg .x2).toNat ∧ (e.s.getReg .x2).toNat ≤ 0xc0000008 ∧
    (e.s.getReg .x2).toNat % 16 = 0 := by
  have h := he.pre.stack.bounds (by decide) (by decide)
  have ha := he.pre.stack.above
  simp only [stackLo, BitVec.toNat_sub, BitVec.toNat_ofNat] at ha
  have := (e.s.getReg .x2).isLt
  simp only [evalStack, eqKernelStack, mulStack, heapEnd] at h ha ⊢
  omega

/-- The heap's bounds at the loop's head. -/
theorem heap : heapStart ≤ heapNext e.s ∧ heapNext e.tL ≤ heapEnd :=
  ⟨he.pre.heap.lo, he.heapL.hi⟩

end EnvOk

/-! ## Reading through `LoopMem` -/

namespace LoopMem

variable {e : Env} {t : MachineState}

/-- A doubleword outside the scratch. -/
theorem get (hm : LoopMem e t) {a : Word} (ha : ¬ Scratch e a) : t.getMem a = e.tL.getMem a :=
  hm a ha

/-- A block whose writes are scratch keeps `LoopMem`. -/
theorem step {x : Sym.Expect} {t' : MachineState} (hm : LoopMem e t) (h : x.Holds t t')
    (hw : ∀ k ∈ x.writes, Scratch e (k.eval t)) : LoopMem e t' := by
  intro a ha
  rw [h.frame a fun k hk heq ↦ ha (heq ▸ hw k hk)]
  exact hm a ha

/-- A step that writes nothing keeps `LoopMem`. -/
theorem same {t' : MachineState} (hm : LoopMem e t) (h : ∀ a, t'.getMem a = t.getMem a) :
    LoopMem e t' :=
  fun a ha ↦ (h a).trans (hm a ha)

/-- A frame within the scratch keeps `LoopMem`. -/
theorem frame {t' : MachineState} (hm : LoopMem e t)
    (h : ∀ a, ¬ Scratch e a → t'.getMem a = t.getMem a) : LoopMem e t' :=
  fun a ha ↦ (h a ha).trans (hm a ha)

end LoopMem

/-! ## Lists of `E` in memory -/

/-- A list of `E`s whose doublewords are unchanged. -/
theorem eListAt_congr {s t : MachineState} {p : Word} {n : Nat}
    (h : ∀ i < n, ∀ j < 3, t.getMem (p + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 (8 * j)) =
      s.getMem (p + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 (8 * j))) :
    eListAt t p n = eListAt s p n := by
  unfold eListAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have h0 := h i hi 0 (by decide)
  have h1 := h i hi 1 (by decide)
  have h2 := h i hi 2 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.mul_one] at h0 h1 h2
  unfold eAt
  rw [h0, show (8 : Word) = BitVec.ofNat 64 8 from rfl, h1,
    show (16 : Word) = BitVec.ofNat 64 (8 * 2) from rfl, h2]

/-- Writing element `idx` of a list of `E`s, and nothing else of it. -/
theorem eListAt_set {s t : MachineState} {p : Word} {n idx : Nat} (hidx : idx < n)
    (hw : p.toNat + 24 * n ≤ 2 ^ 64) {v : E}
    (hv : eAt t (p + BitVec.ofNat 64 (24 * idx)) = v)
    (hother : ∀ a, ¬ Within a (p + BitVec.ofNat 64 (24 * idx)) 24 → t.getMem a = s.getMem a) :
    eListAt t p n = (eListAt s p n).set idx v := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i h1 h2
  rw [List.getElem_set]
  split
  · rename_i h; subst h; rw [eListAt_getElem, hv]
  · rename_i h
    rw [eListAt_getElem, eListAt_getElem]
    simp only [eListAt_length] at h1
    unfold eAt
    have hi : i < n := h1
    rw [hother _ (by addr_omega [hidx, hi, hw, h]), hother _ (by addr_omega [hidx, hi, hw, h]),
      hother _ (by addr_omega [hidx, hi, hw, h])]

theorem eListAt_take (s : MachineState) (p : Word) {n m : Nat} (h : m ≤ n) :
    eListAt s p m = (eListAt s p n).take m := by
  apply List.ext_getElem (by simp [eListAt_length]; omega)
  intro i h1 h2
  rw [List.getElem_take, eListAt_getElem, eListAt_getElem]

theorem eListAt_drop (s : MachineState) (p : Word) (n m : Nat) :
    eListAt s (p + BitVec.ofNat 64 (24 * m)) (n - m) = (eListAt s p n).drop m := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i h1 h2
  rw [List.getElem_drop, eListAt_getElem, eListAt_getElem, BitVec.add_assoc, ← BitVec.ofNat_add,
    Nat.mul_add]

/-- `x * 24`, as the compiler writes it. -/
theorem mul24 (x : Word) : x * 16 + x * 8 = BitVec.ofNat 64 (24 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [Sym.wordToNatLit]
  omega

/-- `.rodata` stays in place where its doublewords do. -/
theorem RodataOk.of_dwords {s t : MachineState} (h : RodataOk s)
    (hm : ∀ a, Within a rodataBase rodataSize → t.getMem a = s.getMem a) : RodataOk t :=
  fun p hp ↦ (hm p.1 (within_of_mem_rodataWords hp)).trans (h p hp)

end Rv64Verifier.Proofs.Bytecode.Eval
