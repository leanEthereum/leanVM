/-
  Rv64mc.Proof.Runtime.VecReprT

  What a vector's header promises its users' total proofs: the representation predicates the growth chain
  (`try_allocate_in`, `grow_amortized`, `grow_one`, `do_reserve_and_handle`, `reserve`) takes and gives, and that
  every caller reading or writing a vector's elements needs. A buffer (`BufT`) is either none (capacity `0`, its
  pointer dangling) or a block allocated before (below `NEXT`) from the input and heap window's start, 8-byte
  aligned, so its bytes lie in a window (`InWin`) and its doublewords are aligned. A header (`RawVecT`, `VecT`) lies in
  a window, 8-byte aligned, with its buffer `BufT`.

  Every block the bump allocator returns satisfies `BufT` (`bufT_of_alloc`), and so does an empty vector, so the
  predicates are not vacuous.

  ## Main definitions

  * `BufT`, `RawVecT`, `VecT`

  ## Main results

  * `BufT.inWin`, `BufT.mono`, `BufT.of_fresh`, `bufT_of_alloc`, `BufT.live`
  * `RawVecT.keep`, `RawVecT.lt`
-/

import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Spec.Runtime.RawVec
import Rv64mc.Spec.Runtime.Alloc

namespace Rv64mc.Proof.Runtime.VecReprT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)

variable {env : Env}

/-- **A vector's buffer** of `cap` elements of `size` bytes at `ptr`, in `m`: none (capacity `0`), or a block
    allocated before `m` (`Live`), from the input and heap window's start, 8-byte aligned. -/
def BufT (env : Env) (m : MachineState) (cap ptr : Word) (size : Nat) : Prop :=
  cap.toNat = 0 ∨ (0x10000000 ≤ ptr.toNat ∧ env.Live m ptr (cap.toNat * size) ∧ ptr.toNat % 8 = 0)

/-- **The `RawVecInner` at `a`** (capacity, pointer), for elements of `size` bytes: its 16 bytes in a window and
    8-byte aligned, its buffer `BufT`, of fewer than `2^63` bytes. -/
def RawVecT (env : Env) (m : MachineState) (a : Word) (size : Nat) : Prop :=
  InWin env a Layouts.RawVecInner.byteSize ∧ a.toNat % 8 = 0 ∧
    BufT env m (m.getMem (rvCapAt a)) (m.getMem (rvPtrAt a)) size ∧ (m.getMem (rvCapAt a)).toNat * size < 2 ^ 63

/-- **The `Vec` at `a`**, for elements of `size` bytes: its 24 bytes in a window, its `RawVecInner` (at offset `0`)
    `RawVecT`, its length at most its capacity. -/
def VecT (env : Env) (m : MachineState) (a : Word) (size : Nat) : Prop :=
  InWin env a Layouts.Vec.byteSize ∧ RawVecT env m a size ∧ (vecLen m a).toNat ≤ (vecCap m a).toNat

namespace BufT

variable {m m' : MachineState} {cap ptr : Word} {size : Nat}

/-- A buffer's bytes lie in a window, when it has any. -/
theorem inWin (h : BufT env m cap ptr size) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    cap.toNat * size = 0 ∨ InWin env ptr (cap.toNat * size) := by
  rcases h with h | ⟨h1, h2, -⟩
  · exact .inl (by rw [h, Nat.zero_mul])
  · unfold Env.Live at h2
    exact .inr (.inl ⟨h1, by omega⟩)

/-- A buffer is allocated before `m`, when it has any bytes: `GrowPre`'s and `FinishGrowPre`'s form. -/
theorem live (h : BufT env m cap ptr size) : cap.toNat = 0 ∨ env.Live m ptr (cap.toNat * size) :=
  h.imp id fun h => h.2.1

/-- `NEXT` only grows. -/
theorem mono (h : BufT env m cap ptr size) (hn : (env.next m).toNat ≤ (env.next m').toNat) :
    BufT env m' cap ptr size :=
  h.imp id fun ⟨h1, h2, h3⟩ => ⟨h1, by unfold Env.Live at h2 ⊢; omega, h3⟩

/-- A block allocated between `m` and `m'`, 8-byte aligned. -/
theorem of_fresh (hf : env.Fresh m m' ptr (cap.toNat * size)) (hge : 0x10000000 ≤ (env.next m).toNat)
    (hal : ptr.toNat % 8 = 0) : BufT env m' cap ptr size :=
  .inr ⟨by have := hf.1; omega, hf.live, hal⟩

end BufT

/-- **What `alloc` returns is a buffer**: a block of the size asked for. -/
theorem bufT_of_alloc {regs r' : Reg → Word} {m m' : MachineState} {cap : Word} {size : Nat}
    (h : AllocPost env regs m r' m') (hn : (regs .x10).toNat = cap.toNat * size)
    (hge : 0x10000000 ≤ (env.next m).toNat) : BufT env m' cap (r' .x10) size :=
  BufT.of_fresh (hn ▸ h.fresh) hge h.2.1

/-- An empty vector's header, whatever its pointer. -/
theorem bufT_zero {m : MachineState} {ptr : Word} {size : Nat} : BufT env m 0#64 ptr size := .inl rfl

namespace RawVecT

variable {m m' : MachineState} {a : Word} {size : Nat}

/-- The header's words. -/
theorem lt (h : RawVecT env m a size) : a.toNat + 16 < 2 ^ 64 := h.1.lt

/-- A header whose two words are kept, after `NEXT` grew. -/
theorem keep (h : RawVecT env m a size) (hc : m'.getMem (rvCapAt a) = m.getMem (rvCapAt a))
    (hp : m'.getMem (rvPtrAt a) = m.getMem (rvPtrAt a)) (hn : (env.next m).toNat ≤ (env.next m').toNat) :
    RawVecT env m' a size := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, by rw [hc, hp]; exact h3.mono hn, by rw [hc]; exact h4⟩

end RawVecT

end Rv64mc.Proof.Runtime.VecReprT
