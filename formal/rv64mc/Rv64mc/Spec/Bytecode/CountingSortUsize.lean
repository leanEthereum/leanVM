/-
  Rv64mc.Spec.Bytecode.CountingSortUsize

  The contract of `counting_sort::<usize, block_members::{closure#0}>(items: &[usize], keys, key) -> Vec<usize>`,
  the key of an index its member's position count, `members[index].1.len()`: the result's header at `sret` (`a0`),
  the items as a slice (`a1`, `a2`, 8-aligned, allocated before), `keys` in `a3`, and the closure's captured
  `&Vec<(K, Vec<u16>)>` passed as the members' pointer and length (`a4`, `a5`; read off the code, rustc prints no
  layout for a closure). The result is `Model.countingSortRust`'s, in a fresh block (`FreshVecW`). `keys` is at
  least `1`: the one caller passes `block.len() + 1`, and the compiled prefix-sum loop runs once before its test.
-/

import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Bytecode

namespace Rv64mc.Spec.Bytecode.CountingSortUsize

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- Member `i`'s position count at its `Vec<u16>`'s length. -/
def lenAt (base : Word) (i : Nat) : Word :=
  base + BitVec.ofNat 64 (Layouts.KVecU16.byteSize * i + Layouts.KVecU16.f1 + Layouts.Vec.len)

/-- The members' position counts `lens`, from `base`. -/
def LensAt (m : MachineState) (base : Word) (lens : List Nat) : Prop :=
  base.toNat + Layouts.KVecU16.byteSize * lens.length < 2 ^ 64 ∧
    ∀ i (h : i < lens.length), m.getMem (lenAt base i) = BitVec.ofNat 64 lens[i] ∧ lens[i] < 2 ^ 64

/-- The key of an index: its member's position count. -/
def key (lens : List Nat) (i : Nat) : Nat := lens.getD i 0

def Pre (env : Env) (items : List Nat) (keys : Nat) (lens : List Nat) (regs : Reg → Word) (m : MachineState) :
    Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧
    SliceArgs WordsAt m (regs .x11) (regs .x12) (items.map (BitVec.ofNat 64)) ∧ (regs .x11).toNat % 8 = 0 ∧
    env.Live m (regs .x11) (8 * items.length) ∧ (∀ x ∈ items, x < 2 ^ 64) ∧
    regs .x13 = BitVec.ofNat 64 keys ∧ 1 ≤ keys ∧ keys < 2 ^ 59 ∧
    regs .x15 = BitVec.ofNat 64 lens.length ∧ LensAt m (regs .x14) lens ∧
    env.Live m (regs .x14) (Layouts.KVecU16.byteSize * lens.length)

def Post (env : Env) (items : List Nat) (keys : Nat) (lens : List Nat) (regs : Reg → Word) (m : MachineState)
    (_r' : Reg → Word) (m' : MachineState) : Prop :=
  Whir.FreshVecW env m m' (regs .x10) ((Model.countingSortRust items keys (key lens)).map (BitVec.ofNat 64))

/-- **The contract of this `counting_sort`**, function `i` of `p` with `need` bytes of stack (its frame is 112
    bytes; it calls `try_allocate_in`, `alloc`, `memcpy` and the panics), for every slice of items. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ items keys lens, Holds env p i need (Pre env items keys lens) (Post env items keys lens)
    (Whir.SretOut Layouts.Vec.byteSize)

end Rv64mc.Spec.Bytecode.CountingSortUsize
