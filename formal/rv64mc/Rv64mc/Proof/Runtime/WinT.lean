/-
  Rv64mc.Proof.Runtime.WinT

  Lemmas the total contracts of wave 1 share about objects a function is passed in a window (`InWin`,
  `MemsetT.lean`'s): an aligned doubleword of one is in a window and aligned, an element of a slice is at its
  address as a number, and the coarsest memory frame (`Out` everywhere) of stores into such objects.

  ## Main results

  * `MemsetT.InWin.dword`, `MemsetT.InWin.ne_next`, `MemsetT.InWin.lt`, `MemsetT.InWin.dword_add`,
    `MemsetT.InWin.ne_next_add`, `elem_toNat`, `frame_true`, `frame_true_setMem`
-/

import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.Heap

namespace Rv64mc.Proof.Runtime.WinT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime.MemsetT (InWin)

variable {env : Env}

/-- A doubleword at offset `o` of a range in a window, both 8-byte aligned, is in a window and aligned. -/
theorem _root_.Rv64mc.Proof.Runtime.MemsetT.InWin.dword {q x : Word} {n o : Nat} {top : Word} {m : MachineState}
    (h : InWin env q n) (hW : Windows env top m) (hal : q.toNat % 8 = 0) (hx : x.toNat = q.toNat + o) (ho : o + 8 ≤ n)
    (ho8 : o % 8 = 0) : inWindow x 8 = true ∧ x.toNat % 8 = 0 :=
  ⟨(MemsetT.InWin.sub h (by omega) (by omega)).inWindow hW, by omega⟩

/-- A word of a range in a window is not `NEXT`'s. -/
theorem _root_.Rv64mc.Proof.Runtime.MemsetT.InWin.ne_next {q x : Word} {n : Nat} (h : InWin env q n)
    (h1 : q.toNat ≤ x.toNat) (h2 : x.toNat < q.toNat + n) : x ≠ env.nextAddr :=
  (MemsetT.InWin.apart h (by omega) h2).2

/-- A range in a window does not wrap. -/
theorem _root_.Rv64mc.Proof.Runtime.MemsetT.InWin.lt {q : Word} {n : Nat} (h : InWin env q n) :
    q.toNat + n < 2 ^ 64 := by
  have := env.heapEnd.isLt
  unfold InWin at h
  omega

/-- A doubleword `k` bytes past offset `o` of a range in a window, both 8-byte aligned, is in a window and
    aligned. -/
theorem _root_.Rv64mc.Proof.Runtime.MemsetT.InWin.dword_add {q x : Word} {n o k : Nat} {top : Word}
    {m : MachineState} (h : InWin env q n) (hW : Windows env top m) (hal : q.toNat % 8 = 0)
    (hx : x.toNat = q.toNat + o) (ho : o + k + 8 ≤ n) (ho8 : (o + k) % 8 = 0) :
    inWindow (x + BitVec.ofNat 64 k) 8 = true ∧ (x + BitVec.ofNat 64 k).toNat % 8 = 0 :=
  have := h.lt
  h.dword hW hal ((toNat_add_ofNat (by omega)).trans (by omega)) ho ho8

/-- A word at offset `o` of a range in a window is not `NEXT`'s. -/
theorem _root_.Rv64mc.Proof.Runtime.MemsetT.InWin.ne_next_add {q : Word} {n o : Nat} (h : InWin env q n)
    (ho : o < n) : q + BitVec.ofNat 64 o ≠ env.nextAddr :=
  have := h.lt
  h.ne_next (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)

/-- Element `o` of a slice of `2 ^ s`-byte elements from `q`, as the code addresses it, as a number. -/
theorem elem_toNat {q o : Word} {s : Nat} (h : q.toNat + 2 ^ s * o.toNat < 2 ^ 64) :
    (q + o <<< s).toNat = q.toNat + 2 ^ s * o.toNat := by
  have : 2 ^ s * o.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm o.toNat,
    Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h]

/-- The coarsest memory frame, where `NEXT` is as at entry. -/
theorem frame_true {top : Word} {m M : MachineState} (hn : env.next M = env.next m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : env.Frame top (fun _ => True) m M :=
  ⟨by rw [hn], by rw [hn]; exact hnx, fun _ h => absurd (Or.inr (Or.inr (Or.inr trivial))) h⟩

/-- The coarsest memory frame, after a store that misses `NEXT`. -/
theorem frame_true_setMem {top a v : Word} {m M : MachineState} (h : env.Frame top (fun _ => True) m M)
    (ha : a ≠ env.nextAddr) : env.Frame top (fun _ => True) m (M.setMem a v) :=
  ⟨by rw [Tactic.next_setMem ha]; exact h.1, by rw [Tactic.next_setMem ha]; exact h.2.1,
    fun _ h => absurd (Or.inr (Or.inr (Or.inr trivial))) h⟩

end Rv64mc.Proof.Runtime.WinT
