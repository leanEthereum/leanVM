/-
  Rv64mc.Proof.Layout.PairT

  `Flushes::pair(&mut self, push, pull)` is total: it pushes the 24-byte `Vec<Form>` headers `push` (`a1`) and `pull`
  (`a2`) onto the vectors `self.push` (at `a0`) and `self.pull` (at `a0 + 24`), each through `RawVec::grow_one`
  when full. Both vectors stay vectors' (`VecReprT.VecT`) with their buffers apart, each one longer, its earlier
  elements kept (moved with the buffer when it grew, by `grow_one`'s `Grown` bytes) and its last one the three words
  of `push` (`pull`) at entry (`PushedT`); the run ends with the guest's abort (`AbortStop`) where `grow_one` does.
  What it writes besides its stack and fresh blocks is `self`'s 48 bytes and each vector's next slot when it has room
  (`OutT`), so a caller keeps whatever its pushed headers point to.

  The precondition: `self`'s two vectors `VecT` with their buffers apart and its 48 bytes a caller's frame object
  (`FlushesT`), `push` and `pull` caller's frame objects apart from `self`, all aligned. Each buffer lies in the heap
  and `self` on the stack, so the element stores keep `self`. At the image's two call sites (`state_derived`,
  `counted`) `push` and `pull` are slots of the caller's frame and `self` is the caller's own argument, a `Flushes`
  that `tables` keeps in its frame.

  The body is cut where `rv_symT` would carry a chain of stores into a call: at instruction 30 (after the first
  `grow_one`), 52 (the element's address), 60 (after the element and the length are stored, before the second
  `grow_one`) and 86 (the second element's address); each part starts from an invariant over an opaque memory, and
  the contents (`Cont1`, `Cont60`, `Cont2`) as a separate hypothesis.

  ## Main definitions

  * `FlushesT`, `BufsApart`, `PreT`, `ElemsEq`, `PushedT`, `PostT`, `OutT`, `SpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.PlacementNextT
import Rv64mc.Proof.Runtime.GrowOneT
import Rv64mc.Proof.Transcript.Bytes
import Rv64mc.Gen.Tmpl.Verifier.Layout.Flushes.Pair

namespace Rv64mc.Proof.Layout.PairT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.GrowOneT (GrowOneSpecT)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Gen.Verifier.Layout.Flushes.Pair (Link tmpl)

/-- `self`'s two buffers, at `a` and `a + 24`, apart when both have bytes. -/
def BufsApart (m : MachineState) (a : Word) : Prop :=
  (m.getMem a).toNat = 0 ∨ (m.getMem (a + 24#64)).toNat = 0 ∨
    (m.getMem (a + 8#64)).toNat + (m.getMem a).toNat * 24 ≤ (m.getMem (a + 32#64)).toNat ∨
    (m.getMem (a + 32#64)).toNat + (m.getMem (a + 24#64)).toNat * 24 ≤ (m.getMem (a + 8#64)).toNat

/-- `self` at `a`: its two vectors of 24-byte elements `VecT`, their buffers apart, its 48 bytes a caller's frame
    object. -/
def FlushesT (env : Env) (m : MachineState) (sp a : Word) : Prop :=
  VecT env m a 24 ∧ VecT env m (a + 24#64) 24 ∧ StackObj sp a 48 ∧ BufsApart m a

/-- `[a, a + n)` and `[b, b + k)` apart. -/
def Apart (a : Word) (n : Nat) (b : Word) (k : Nat) : Prop := a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat

/-- The total precondition: `self` `FlushesT`; `push` and `pull` caller's frame objects apart from `self`; all
    aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  FlushesT env m (regs .x2) (regs .x10) ∧ (regs .x10).toNat % 8 = 0 ∧
    StackObj (regs .x2) (regs .x11) 24 ∧ (regs .x11).toNat % 8 = 0 ∧
    StackObj (regs .x2) (regs .x12) 24 ∧ (regs .x12).toNat % 8 = 0 ∧
    Apart (regs .x10) 48 (regs .x11) 24 ∧ Apart (regs .x10) 48 (regs .x12) 24

/-- The first `n` 24-byte elements at `P'` in `m'` hold the words of those at `P` in `m`. -/
def ElemsEq (m m' : MachineState) (P P' : Word) (n : Nat) : Prop :=
  ∀ w, w < 3 * n → m'.getMem (P' + BitVec.ofNat 64 (8 * w)) = m.getMem (P + BitVec.ofNat 64 (8 * w))

/-- The vector at `v` in `m'` is the one in `m` with the 24 bytes at `src` in `m` pushed: its elements kept (moved
    with the buffer when it grew), the new last one `src`'s three words. -/
def PushedT (m m' : MachineState) (v src : Word) : Prop :=
  ElemsEq m m' (vecPtr m v) (vecPtr m' v) (vecLen m v).toNat ∧
    ∀ j, j < 3 → m'.getMem (vecPtr m' v + BitVec.ofNat 64 (24 * (vecLen m v).toNat + 8 * j)) =
      m.getMem (src + BitVec.ofNat 64 (8 * j))

/-- `PostT` at the stack pointer `sp`: `self` `FlushesT` again, each vector one longer, `push` and `pull` pushed. -/
def PostM (env : Env) (regs : Reg → Word) (m : MachineState) (sp : Word) (m' : MachineState) : Prop :=
  FlushesT env m' sp (regs .x10) ∧
    (vecLen m' (regs .x10)).toNat = (vecLen m (regs .x10)).toNat + 1 ∧
    (vecLen m' (regs .x10 + 24#64)).toNat = (vecLen m (regs .x10 + 24#64)).toNat + 1 ∧
    PushedT m m' (regs .x10) (regs .x11) ∧ PushedT m m' (regs .x10 + 24#64) (regs .x12)

/-- The total postcondition: `self` `FlushesT` again, each vector one longer, `push` and `pull` pushed. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  PostM env regs m (r' .x2) m'

/-- The slot after the last element of the vector at `v` in `m`, when it has room. -/
def SlotOut (m : MachineState) (v b : Word) : Prop :=
  (m.getMem (v + 16#64)).toNat < (m.getMem v).toNat ∧
    (m.getMem (v + 8#64)).toNat + 24 * (m.getMem (v + 16#64)).toNat ≤ b.toNat ∧
    b.toNat < (m.getMem (v + 8#64)).toNat + 24 * (m.getMem (v + 16#64)).toNat + 24

/-- What `pair` writes besides its stack and what it allocates: `self`, and each vector's next slot when it has
    room. -/
def OutT (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) 48 b ∨ SlotOut m (regs .x10) b ∨ SlotOut m (regs .x10 + 24#64) b

/-- **The total contract of `Flushes::pair`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-- The prologue's five saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)

/-- A word at or above the stack top, or below the frame, is the entry's after the prologue. -/
theorem saved_get {m : MachineState} {top ret b : Word} {regs : Reg → Word} (h48 : 48 ≤ top.toNat)
    (hb : top.toNat ≤ b.toNat ∨ b.toNat + 48 ≤ top.toNat) : (saved m top ret regs).getMem b = m.getMem b := by
  have hne : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 40 → b ≠ top + c := fun c k hc hk0 hk he => by
    have := congrArg BitVec.toNat he
    rw [Runtime.CloneT.toNat_add_neg hc (by omega)] at this
    omega
  simp only [saved]
  rw [MachineState.getMem_setMem_ne (hne _ 40 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 32 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 24 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 16 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 8 rfl (by omega) (by omega))]

/-- The frame's saved words in `M`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19

/-- The prologue's stores: in the frame, `env.Static` and `NEXT` kept, the slots holding the saved words. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 48 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) :
    env.Frame top out m (saved m top ret regs) ∧ env.Static (saved m top ret regs) ∧
      env.next (saved m top ret regs) = env.next m ∧ Slots (saved m top ret regs) top ret regs := by
  have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 48 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e8 := e 18446744073709551608#64 8 rfl (by omega)
  have e16 := e 18446744073709551600#64 16 rfl (by omega)
  have e24 := e 18446744073709551592#64 24 rfl (by omega)
  have e32 := e 18446744073709551584#64 32 rfl (by omega)
  have e40 := e 18446744073709551576#64 40 rfl (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [saved]
    repeat (first | exact Env.Frame.refl hnx | refine Tactic.frame_slot ?_ (by omega) (by omega))
  · simp only [saved]
    repeat (first | exact hS | refine Env.static_setMem_stack ?_ (by omega))
  · simp only [saved]
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega),
      Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h; simp only [e8, e16, e24, e32, e40] at h'; omega)])

/-- `top - 48` as a number. -/
theorem top48 {top : Word} (h : 48 ≤ top.toNat) : (top + 18446744073709551568#64).toNat = top.toNat - 48 :=
  Runtime.CloneT.toNat_add_neg rfl h

/-- A word apart from a header's two is not in `grow_one`'s `GrowOut`. -/
theorem not_growOut {R : Reg → Word} {M : MachineState} {a b : Word} (hR : R .x10 = a) (h1 : b.toNat ≠ a.toNat)
    (h2 : b.toNat ≠ (a + 8#64).toNat) : ¬ GrowOut R M b := by
  rintro (h | h)
  · exact h1 (by rw [h, hR, Runtime.GrowOne.rvCapAt_eq])
  · exact h2 (by rw [h, hR, Runtime.GrowOne.rvPtrAt_eq])

/-- A word of a header at `a + k` in `self`'s 48 bytes at `a` is in `grow_one`'s `GrowOut` only there. -/
theorem growOut_in {R : Reg → Word} {M : MachineState} {a b : Word} {k : Nat} (hR : (R .x10).toNat = a.toNat + k)
    (hk : k + 16 ≤ 48) (ha : a.toNat + 48 < 2 ^ 64) (hb : GrowOut R M b) : InRange a 48 b := by
  rcases hb with h | h
  · rw [h, Runtime.GrowOne.rvCapAt_eq]; exact ⟨by omega, by omega⟩
  · rw [h, Runtime.GrowOne.rvPtrAt_eq]
    have e8 : (R .x10 + 8#64).toNat = a.toNat + k + 8 := by rw [toNat_add_ofNat (by omega), hR]
    exact ⟨by omega, by omega⟩

/-- The state at instruction 30, `self.push` with room: its length the entry's, below its capacity, its buffer in
    the heap, the entry's or fresh; `self.pull`'s header the entry's. -/
def MInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551568#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x12 ∧ R .x18 = regs .x11 ∧
    R .x19 = m.getMem (regs .x10 + 16#64) ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    (m.getMem (regs .x10 + 16#64)).toNat < (M.getMem (regs .x10)).toNat ∧
    (M.getMem (regs .x10)).toNat * 24 < 2 ^ 63 ∧
    0x10000000 ≤ (M.getMem (regs .x10 + 8#64)).toNat ∧
    (M.getMem (regs .x10 + 8#64)).toNat + (M.getMem (regs .x10)).toNat * 24 ≤ (env.next M).toNat ∧
    (M.getMem (regs .x10 + 8#64)).toNat % 8 = 0 ∧
    ((M.getMem (regs .x10 + 8#64) = m.getMem (regs .x10 + 8#64) ∧ M.getMem (regs .x10) = m.getMem (regs .x10)) ∨
      (env.next m).toNat ≤ (M.getMem (regs .x10 + 8#64)).toNat) ∧
    M.getMem (regs .x10 + 16#64) = m.getMem (regs .x10 + 16#64) ∧
    M.getMem (regs .x10 + 24#64) = m.getMem (regs .x10 + 24#64) ∧
    M.getMem (regs .x10 + 32#64) = m.getMem (regs .x10 + 32#64) ∧
    M.getMem (regs .x10 + 40#64) = m.getMem (regs .x10 + 40#64) ∧
    Slots M top ret regs ∧ env.Frame top (OutT regs m) m M ∧ env.Static M ∧ M.code = m.code

/-- Element `L` of a buffer of 24-byte elements at `P`, as the code addresses it, as a number. -/
theorem addr24 {P L : Word} (h : P.toNat + 24 * L.toNat < 2 ^ 64) :
    (P + (L <<< 4 + L <<< 3)).toNat = P.toNat + 24 * L.toNat := by
  have h4 : (L <<< 4).toNat = 16 * L.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have h3 : (L <<< 3).toNat = 8 * L.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_add, BitVec.toNat_add, h4, h3]
  omega

/-- **A vector of 24-byte elements from its header's words**: the header in a window, aligned; the length within
    the capacity, the buffer in the heap below `NEXT`, aligned. -/
theorem vecT_mk {env : Env} {m : MachineState} {v : Word} (hw : InWin env v 24) (h8 : v.toNat % 8 = 0)
    (hl : (m.getMem (v + 16#64)).toNat ≤ (m.getMem v).toNat) (hc : (m.getMem v).toNat * 24 < 2 ^ 63)
    (hp : 0x10000000 ≤ (m.getMem (v + 8#64)).toNat)
    (hp2 : (m.getMem (v + 8#64)).toNat + (m.getMem v).toNat * 24 ≤ (env.next m).toNat)
    (hp8 : (m.getMem (v + 8#64)).toNat % 8 = 0) : VecT env m v 24 := by
  have hc0 : rvCapAt v = v := by simp [rvCapAt]
  have hp0 : rvPtrAt v = v + 8#64 := rfl
  refine ⟨hw, ⟨Runtime.MemsetT.InWin.sub hw (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega), h8, ?_, by rw [hc0]; exact hc⟩, ?_⟩
  · rw [hc0, hp0]; exact .inr ⟨hp, by unfold Env.Live; omega, hp8⟩
  · rw [Runtime.ReserveT.vecLen_eq, Runtime.ReserveT.vecCap_eq]; exact hl

/-- **One store into a buffer of 24-byte elements** `[P, P + 24 C)` below `NEXT`: into `out`, or into a block
    allocated since the entry. -/
theorem frame_buf {env : Env} {top b v P C : Word} {out : Word → Prop} {m N : MachineState}
    (h1 : env.Frame top out m N) (hP : P.toNat + C.toNat * 24 ≤ (env.next N).toNat) (hb1 : P.toNat ≤ b.toNat)
    (hb2 : b.toNat < P.toNat + C.toNat * 24) (hold : out b ∨ (env.next m).toNat ≤ P.toNat) :
    env.Frame top out m (N.setMem b v) ∧ env.next (N.setMem b v) = env.next N := by
  have := env.layout
  have h2 := h1.2.1
  have hne : b ≠ env.nextAddr := fun e => by rw [e] at hb2; omega
  refine ⟨?_, Tactic.next_setMem hne⟩
  rcases hold with ho | hf
  · exact Tactic.frame_out h1 ho hne
  · exact Tactic.frame_fresh h1 rfl (by omega) (by omega)

/-- **The three stores of an element** at `A`, element `L < C` of the buffer `[P, P + 24 C)`: its 24 bytes in
    `out`, or the buffer allocated since the entry. -/
theorem frame_elem {env : Env} {top A P C v1 v2 v3 : Word} {L : Nat} {out : Word → Prop}
    {m N : MachineState} (h1 : env.Frame top out m N)
    (hP : P.toNat + C.toNat * 24 ≤ (env.next N).toNat) (hA : A.toNat = P.toNat + 24 * L) (hL : L < C.toNat)
    (hold : (∀ c : Word, A.toNat ≤ c.toNat → c.toNat < A.toNat + 24 → out c) ∨ (env.next m).toNat ≤ P.toNat) :
    env.Frame top out m (((N.setMem A v1).setMem (A + 8#64) v2).setMem (A + 16#64) v3) ∧
      env.next (((N.setMem A v1).setMem (A + 8#64) v2).setMem (A + 16#64) v3) = env.next N := by
  have := env.layout
  have h2 := h1.2.1
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  obtain ⟨f1, n1⟩ := frame_buf (b := A) (v := v1) h1 hP (by omega) (by omega)
    (hold.imp (fun h => h _ (by omega) (by omega)) id)
  obtain ⟨f2, n2⟩ := frame_buf (b := A + 8#64) (v := v2) f1 (by rw [n1]; exact hP) (by omega) (by omega)
    (hold.imp (fun h => h _ (by omega) (by omega)) id)
  obtain ⟨f3, n3⟩ := frame_buf (b := A + 16#64) (v := v3) f2 (by rw [n2, n1]; exact hP) (by omega) (by omega)
    (hold.imp (fun h => h _ (by omega) (by omega)) id)
  exact ⟨f3, by rw [n3, n2, n1]⟩

/-- A word on the stack is kept by three stores below the heap's end. -/
theorem get_elem {env : Env} {A b v1 v2 v3 : Word} {N : MachineState}
    (hA : A.toNat + 24 ≤ env.heapEnd.toNat) (hb : env.stackLimit.toNat ≤ b.toNat) :
    (((N.setMem A v1).setMem (A + 8#64) v2).setMem (A + 16#64) v3).getMem b = N.getMem b := by
  have := env.layout
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  rw [MachineState.getMem_setMem_ne (fun e => by rw [e, e16] at hb; omega),
    MachineState.getMem_setMem_ne (fun e => by rw [e, e8] at hb; omega),
    MachineState.getMem_setMem_ne (fun e => by rw [e] at hb; omega)]

theorem add24_8 (a : Word) : a + 24#64 + 8#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl

theorem add24_16 (a : Word) : a + 24#64 + 16#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl

theorem vp (m : MachineState) (a : Word) : vecPtr m a = m.getMem (a + 8#64) := rfl

theorem vl (m : MachineState) (a : Word) : vecLen m a = m.getMem (a + 16#64) := rfl

/-- The prologue keeps `[a, a + n)` at or above the stack top or below the frame. -/
theorem keeps_saved {m : MachineState} {top ret a : Word} {regs : Reg → Word} {n : Nat} (h48 : 48 ≤ top.toNat)
    (ha : n = 0 ∨ top.toNat ≤ a.toNat ∨ a.toNat + n + 48 ≤ top.toNat) : Keeps m (saved m top ret regs) a n :=
  fun b hb => saved_get h48 (by unfold InRange at hb; omega)

/-- **A 24-byte element's three stores and one more** keep `[a, a + n)` apart from them. -/
theorem keeps_stores {M : MachineState} {A s a v1 v2 v3 v4 : Word} {n : Nat} (hA : A.toNat + 24 < 2 ^ 64)
    (h : n = 0 ∨ A.toNat + 24 ≤ a.toNat ∨ a.toNat + n ≤ A.toNat) (hs : s.toNat < a.toNat ∨ a.toNat + n ≤ s.toNat) :
    Keeps M ((((M.setMem A v1).setMem (A + 8#64) v2).setMem (A + 16#64) v3).setMem s v4) a n := by
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  refine (((Keeps.setMem ?_).trans (Keeps.setMem ?_)).trans (Keeps.setMem ?_)).trans (Keeps.setMem ?_) <;>
    simp only [InRange, e8, e16] <;> omega

/-- The three words at `src` stored as an element at `A`, read back. -/
theorem get3 {M M0 : MachineState} {A B src v1 v2 v3 : Word} {j : Nat} (hj : j < 3) (hA : A.toNat + 24 < 2 ^ 64)
    (hB : B.toNat = A.toNat + 8 * j) (h1 : v1 = M0.getMem src) (h2 : v2 = M0.getMem (src + 8#64))
    (h3 : v3 = M0.getMem (src + 16#64)) :
    (((M.setMem A v1).setMem (A + 8#64) v2).setMem (A + 16#64) v3).getMem B =
      M0.getMem (src + BitVec.ofNat 64 (8 * j)) := by
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  interval_cases j
  · obtain rfl : B = A := BitVec.eq_of_toNat_eq (by omega)
    rw [MachineState.getMem_setMem_ne (fun e => by have := congrArg BitVec.toNat e; omega),
      MachineState.getMem_setMem_ne (fun e => by have := congrArg BitVec.toNat e; omega),
      MachineState.getMem_setMem_eq, h1]
    simp
  · obtain rfl : B = A + 8#64 := BitVec.eq_of_toNat_eq (by omega)
    rw [MachineState.getMem_setMem_ne (fun e => by have := congrArg BitVec.toNat e; omega),
      MachineState.getMem_setMem_eq, h2]
  · obtain rfl : B = A + 16#64 := BitVec.eq_of_toNat_eq (by omega)
    rw [MachineState.getMem_setMem_eq, h3]

theorem ElemsEq.keep {m M M' : MachineState} {P P' : Word} {n : Nat} (h : ElemsEq m M P P' n)
    (hk : Keeps M M' P' (24 * n)) (hP : P'.toNat + 24 * n < 2 ^ 64) : ElemsEq m M' P P' n := fun w hw => by
  have e : (P' + BitVec.ofNat 64 (8 * w)).toNat = P'.toNat + 8 * w := toNat_add_ofNat (by omega)
  rw [hk _ ⟨by omega, by omega⟩]
  exact h w hw

theorem ElemsEq.of_keeps {m M : MachineState} {P : Word} {n : Nat} (hk : Keeps m M P (24 * n))
    (hP : P.toNat + 24 * n < 2 ^ 64) : ElemsEq m M P P n := fun w hw => by
  have e : (P + BitVec.ofNat 64 (8 * w)).toNat = P.toNat + 8 * w := toNat_add_ofNat (by omega)
  exact hk _ ⟨by omega, by omega⟩

/-- **Elements moved by a grow**: the new block at `P'` holds the old block's bytes at `P`. -/
theorem ElemsEq.grown {m M M' : MachineState} {P0 P P' : Word} {n C : Nat} (h : ElemsEq m M P0 P n)
    (hb : ∀ k, k < C * 24 → M'.getByte (P' + BitVec.ofNat 64 k) = M.getByte (P + BitVec.ofNat 64 k))
    (hn : n ≤ C) (hP : P.toNat + C * 24 < 2 ^ 64) (hP' : P'.toNat + C * 24 < 2 ^ 64)
    (h8 : 0 < n → P.toNat % 8 = 0) (h8' : P'.toNat % 8 = 0) : ElemsEq m M' P0 P' n := fun w hw => by
  have e : (P + BitVec.ofNat 64 (8 * w)).toNat = P.toNat + 8 * w := toNat_add_ofNat (by omega)
  have e' : (P' + BitVec.ofNat 64 (8 * w)).toNat = P'.toNat + 8 * w := toNat_add_ofNat (by omega)
  have h8 := h8 (by omega)
  rw [← h w hw]
  refine Transcript.getMem_of_bytes (by omega) (by omega) fun k hk => ?_
  have := hb (8 * w + k) (by omega)
  rwa [BitVec.ofNat_add, ← BitVec.add_assoc, ← BitVec.add_assoc] at this

theorem PushedT.keep {m M M' : MachineState} {v src : Word} (h : PushedT m M v src)
    (hk : Keeps M M' (vecPtr M v) (24 * ((vecLen m v).toNat + 1))) (hp : vecPtr M' v = vecPtr M v)
    (hP : (vecPtr M v).toNat + 24 * ((vecLen m v).toNat + 1) < 2 ^ 64) : PushedT m M' v src := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hp]
    exact h.1.keep (hk.mono (Nat.le_refl _) (by omega)) (by omega)
  · have e : (vecPtr M v + BitVec.ofNat 64 (24 * (vecLen m v).toNat + 8 * j)).toNat =
        (vecPtr M v).toNat + (24 * (vecLen m v).toNat + 8 * j) := toNat_add_ofNat (by omega)
    rw [hp, hk _ ⟨by omega, by omega⟩]
    exact h.2 j hj

/-- The pull vector's length and buffer from its `VecT`. -/
theorem pull_live {env : Env} {m : MachineState} {a : Word} (h : VecT env m (a + 24#64) 24) :
    (m.getMem (a + 40#64)).toNat ≤ (m.getMem (a + 24#64)).toNat ∧ (m.getMem (a + 24#64)).toNat * 24 < 2 ^ 63 ∧
      ((m.getMem (a + 24#64)).toNat = 0 ∨ ((m.getMem (a + 32#64)).toNat + (m.getMem (a + 24#64)).toNat * 24 ≤
        (env.next m).toNat ∧ (m.getMem (a + 32#64)).toNat % 8 = 0)) := by
  have hl := h.2.2
  rw [Runtime.ReserveT.vecLen_eq, Runtime.ReserveT.vecCap_eq, add24_16] at hl
  have hb := h.2.1.2.2.1
  have hc := h.2.1.2.2.2
  simp only [Runtime.GrowOne.rvCapAt_eq, Runtime.GrowOne.rvPtrAt_eq, add24_8] at hb hc
  exact ⟨hl, hc, hb.imp id fun h => ⟨h.2.1, h.2.2⟩⟩

/-- The words `pair` reads from a source at `src`, loaded into `r0`, `r8`, `r16`. -/
def Loaded (R : Reg → Word) (r0 r8 r16 : Reg) (m : MachineState) (src : Word) : Prop :=
  R r0 = m.getMem src ∧ R r8 = m.getMem (src + 8#64) ∧ R r16 = m.getMem (src + 16#64)

/-- The contents at instructions 30 and 52: `self.push`'s elements moved with its buffer, `self.pull`'s and both
    sources kept, the buffers apart. -/
def Cont1 (m : MachineState) (regs : Reg → Word) (M : MachineState) : Prop :=
  ElemsEq m M (m.getMem (regs .x10 + 8#64)) (M.getMem (regs .x10 + 8#64)) (m.getMem (regs .x10 + 16#64)).toNat ∧
    Keeps m M (m.getMem (regs .x10 + 32#64)) (24 * (m.getMem (regs .x10 + 40#64)).toNat) ∧
    Keeps m M (regs .x11) 24 ∧ Keeps m M (regs .x12) 24 ∧ BufsApart M (regs .x10)

/-- The contents at instruction 60: `push` pushed, `self.pull`'s elements and `pull` kept, the buffers apart. -/
def Cont60 (m : MachineState) (regs : Reg → Word) (M : MachineState) : Prop :=
  PushedT m M (regs .x10) (regs .x11) ∧
    Keeps m M (m.getMem (regs .x10 + 32#64)) (24 * (m.getMem (regs .x10 + 40#64)).toNat) ∧
    Keeps m M (regs .x12) 24 ∧ BufsApart M (regs .x10)

/-- The contents at instruction 86: `push` pushed, `self.pull`'s elements moved with its buffer, `pull`'s words
    loaded, the buffers apart. -/
def Cont2 (m : MachineState) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) : Prop :=
  PushedT m M (regs .x10) (regs .x11) ∧
    ElemsEq m M (m.getMem (regs .x10 + 32#64)) (M.getMem (regs .x10 + 32#64)) (m.getMem (regs .x10 + 40#64)).toNat ∧
    Loaded R .x12 .x13 .x15 m (regs .x12) ∧ BufsApart M (regs .x10)

/-- The state at instruction 86, past `self.pull`'s check: `self.push` one longer, its buffer in the heap with room
    for it; `self.pull` with room, its buffer in the heap, the entry's or fresh; the element's address in `x10`. -/
def SInv2 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551568#64 ∧ R .x8 = regs .x10 ∧
    R .x18 = m.getMem (regs .x10 + 40#64) + 1#64 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    (R .x10).toNat = (M.getMem (regs .x10 + 32#64)).toNat + 24 * (m.getMem (regs .x10 + 40#64)).toNat ∧
    (M.getMem (regs .x10 + 16#64)).toNat = (m.getMem (regs .x10 + 16#64)).toNat + 1 ∧
    (M.getMem (regs .x10 + 16#64)).toNat ≤ (M.getMem (regs .x10)).toNat ∧
    (M.getMem (regs .x10)).toNat * 24 < 2 ^ 63 ∧ 0x10000000 ≤ (M.getMem (regs .x10 + 8#64)).toNat ∧
    (M.getMem (regs .x10 + 8#64)).toNat + (M.getMem (regs .x10)).toNat * 24 ≤ (env.next M).toNat ∧
    (M.getMem (regs .x10 + 8#64)).toNat % 8 = 0 ∧
    (m.getMem (regs .x10 + 40#64)).toNat < (M.getMem (regs .x10 + 24#64)).toNat ∧
    (M.getMem (regs .x10 + 24#64)).toNat * 24 < 2 ^ 63 ∧ 0x10000000 ≤ (M.getMem (regs .x10 + 32#64)).toNat ∧
    (M.getMem (regs .x10 + 32#64)).toNat + (M.getMem (regs .x10 + 24#64)).toNat * 24 ≤ (env.next M).toNat ∧
    (M.getMem (regs .x10 + 32#64)).toNat % 8 = 0 ∧
    ((M.getMem (regs .x10 + 32#64) = m.getMem (regs .x10 + 32#64) ∧
        M.getMem (regs .x10 + 24#64) = m.getMem (regs .x10 + 24#64)) ∨
      (env.next m).toNat ≤ (M.getMem (regs .x10 + 32#64)).toNat) ∧
    Slots M top ret regs ∧ env.Frame top (OutT regs m) m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **From instruction 86 to the return**: `pull` stored into `self.pull`, its length stored. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {need : Nat} (hn : 48 ≤ need)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    (hk : ∀ r' m', HoldsT.post env Post OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (_hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (ha : top.toNat ≤ (regs .x10).toNat) (ha2 : (regs .x10).toNat + 48 ≤ 0xc0000000) (ha8 : (regs .x10).toNat % 8 = 0)
    (hPost : ∀ r' m', r' .x2 = top → PostM env regs m top m' → Post regs m r' m') :
    ∀ R M, SInv2 env m top ret regs R M → Cont2 m regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 86, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hC
  obtain ⟨c1, c2, ⟨l0, l8, l16⟩, c4⟩ := hC
  have hlay := env.layout
  rv_introT hI
  have hnM := hI_30.2.1
  have hW' := hW.heapEnd_le
  have hst := hW.nextAddr_ge
  obtain ⟨hf3, hn3⟩ := frame_elem (v1 := R .x12) (v2 := R .x13) (v3 := R .x15) hI_30 hI_22 hI_12 hI_19
    (hI_24.imp (fun ⟨e32, e24⟩ c hc1 hc2 => Or.inr (Or.inr (by
      simp only [SlotOut, add24_8, add24_16]; rw [← e32, ← e24]; omega))) id)
  have e40 : (regs .x10 + 40#64).toNat = (regs .x10).toNat + 40 := toNat_add_ofNat (by omega)
  have hA : (R .x10).toNat + 24 ≤ env.heapEnd.toNat := by omega
  have rd : ∀ b : Word, env.stackLimit.toNat ≤ b.toNat → b ≠ regs .x10 + 40#64 →
      ((((M.setMem (R .x10) (R .x12)).setMem (R .x10 + 8#64) (R .x13)).setMem (R .x10 + 16#64) (R .x15)).setMem
        (regs .x10 + 40#64) (m.getMem (regs .x10 + 40#64) + 1#64)).getMem b = M.getMem b := fun b hb hne => by
    rw [MachineState.getMem_setMem_ne hne, get_elem hA hb]
  have ne : ∀ k : Nat, k < 40 → regs .x10 + BitVec.ofNat 64 k ≠ regs .x10 + 40#64 := fun k hk e => by
    have := congrArg BitVec.toNat e
    rw [toNat_add_ofNat (by omega), e40] at this
    omega
  have tk : ∀ k : Nat, k ≤ 40 → (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k :=
    fun k hk => toNat_add_ofNat (by omega)
  rv_symT hp with [_hL]
  · exact Tactic.frame_out hf3 (Or.inl ⟨by omega, by omega⟩) (fun e => by rw [e] at e40; omega)
  · have r0 := rd (regs .x10) (by omega) (by simp)
    have r8 := rd (regs .x10 + 8#64) (by rw [tk 8 (by omega)]; omega) (ne 8 (by omega))
    have r16 := rd (regs .x10 + 16#64) (by rw [tk 16 (by omega)]; omega) (ne 16 (by omega))
    have r24 := rd (regs .x10 + 24#64) (by rw [tk 24 (by omega)]; omega) (ne 24 (by omega))
    have r32 := rd (regs .x10 + 32#64) (by rw [tk 32 (by omega)]; omega) (ne 32 (by omega))
    have r40 := MachineState.getMem_setMem_eq (s := (((M.setMem (R .x10) (R .x12)).setMem (R .x10 + 8#64)
      (R .x13)).setMem (R .x10 + 16#64) (R .x15))) (a := regs .x10 + 40#64)
      (v := m.getMem (regs .x10 + 40#64) + 1#64)
    have hl1 : (m.getMem (regs .x10 + 40#64) + 1#64).toNat = (m.getMem (regs .x10 + 40#64)).toNat + 1 :=
      toNat_add_ofNat (by omega)
    have hnext : env.next ((((M.setMem (R .x10) (R .x12)).setMem (R .x10 + 8#64) (R .x13)).setMem
        (R .x10 + 16#64) (R .x15)).setMem (regs .x10 + 40#64) (m.getMem (regs .x10 + 40#64) + 1#64)) =
        env.next M := by
      rw [Tactic.next_setMem (fun e => by rw [e] at e40; omega), hn3]
    have ba := c4
    unfold BufsApart at ba
    have hs40 : (regs .x10 + 40#64).toNat < (M.getMem (regs .x10 + 8#64)).toNat ∨
        (M.getMem (regs .x10 + 8#64)).toNat + 24 * ((m.getMem (regs .x10 + 16#64)).toNat + 1) ≤
          (regs .x10 + 40#64).toNat := by omega
    refine hPost _ _ rfl ⟨⟨?_, ?_, ⟨ha, ha2⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
    · refine vecT_mk (.inr ⟨by omega, by omega⟩) ha8 ?_ ?_ ?_ ?_ ?_ <;>
        simp only [r0, r8, r16, hnext] <;> omega
    · refine vecT_mk (.inr ⟨by rw [tk 24 (by omega)]; omega, by rw [tk 24 (by omega)]; omega⟩)
        (by rw [tk 24 (by omega)]; omega) ?_ ?_ ?_ ?_ ?_ <;>
        simp only [add24_8, add24_16, r24, r32, r40, hnext, hl1] <;> omega
    · simp only [BufsApart, r0, r8, r24, r32]; exact c4
    · rw [Runtime.ReserveT.vecLen_eq, Runtime.ReserveT.vecLen_eq, r16]; omega
    · rw [Runtime.ReserveT.vecLen_eq, Runtime.ReserveT.vecLen_eq, add24_16, r40, hl1]
    · refine c1.keep ?_ (by rw [vp, vp, r8]) ?_ <;> simp only [vp, vl]
      · exact keeps_stores (by omega) (by omega) hs40
      · omega
    · refine ⟨?_, fun j hj => ?_⟩ <;> simp only [vp, vl, add24_8, add24_16, r32]
      · exact c2.keep (keeps_stores (by omega) (by omega) (by omega)) (by omega)
      · have eB : (M.getMem (regs .x10 + 32#64) + BitVec.ofNat 64 (24 * (m.getMem (regs .x10 + 40#64)).toNat +
            8 * j)).toNat = (M.getMem (regs .x10 + 32#64)).toNat + (24 * (m.getMem (regs .x10 + 40#64)).toNat +
            8 * j) := toNat_add_ofNat (by omega)
        rw [MachineState.getMem_setMem_ne (fun e => by rw [e] at eB; omega)]
        exact get3 hj (by omega) (by omega) l0 l8 l16

/-- The state at instruction 60, `push` and `self.push`'s length stored: `self.push` one longer, `self.pull`'s
    header the entry's, its capacity and length in `x16`, `x18`. -/
def SInv60 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551568#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x12 ∧
    R .x16 = m.getMem (regs .x10 + 24#64) ∧ R .x18 = m.getMem (regs .x10 + 40#64) ∧ R .x20 = regs .x20 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    (M.getMem (regs .x10 + 16#64)).toNat = (m.getMem (regs .x10 + 16#64)).toNat + 1 ∧
    (M.getMem (regs .x10 + 16#64)).toNat ≤ (M.getMem (regs .x10)).toNat ∧
    (M.getMem (regs .x10)).toNat * 24 < 2 ^ 63 ∧ 0x10000000 ≤ (M.getMem (regs .x10 + 8#64)).toNat ∧
    (M.getMem (regs .x10 + 8#64)).toNat + (M.getMem (regs .x10)).toNat * 24 ≤ (env.next M).toNat ∧
    (M.getMem (regs .x10 + 8#64)).toNat % 8 = 0 ∧
    M.getMem (regs .x10 + 24#64) = m.getMem (regs .x10 + 24#64) ∧
    M.getMem (regs .x10 + 32#64) = m.getMem (regs .x10 + 32#64) ∧
    M.getMem (regs .x10 + 40#64) = m.getMem (regs .x10 + 40#64) ∧
    Slots M top ret regs ∧ env.Frame top (OutT regs m) m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **From instruction 60 to 86**: `grow_one(self.pull)` when it is full, `pull`'s element's address. -/
theorem call {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG : Nat} (hn : 48 ≤ need) (hnG : 48 + needG ≤ need)
    (hg : GrowOneSpecT env Layouts.Vec.byteAlign Layouts.Vec.byteSize p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    (hk : ∀ r' m', HoldsT.post env Post OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (ha : top.toNat ≤ (regs .x10).toNat) (ha2 : (regs .x10).toNat + 48 ≤ 0xc0000000) (ha8 : (regs .x10).toNat % 8 = 0)
    (hq : top.toNat ≤ (regs .x12).toNat) (hq2 : (regs .x12).toNat + 24 ≤ 0xc0000000) (hq8 : (regs .x12).toNat % 8 = 0)
    (hap2 : Apart (regs .x10) 48 (regs .x12) 24) (hV2 : VecT env m (regs .x10 + 24#64) 24)
    (hPost : ∀ r' m', r' .x2 = top → PostM env regs m top m' → Post regs m r' m') :
    ∀ R M, SInv60 env m top ret regs R M → Cont60 m regs M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 60, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hC
  obtain ⟨c1, c2, c3, c4⟩ := hC
  unfold Apart at hap2
  have hlay := env.layout
  rv_introT hI
  obtain ⟨-, -, hb2'⟩ := pull_live hV2
  have hltm := (env.next m).isLt
  have eq8 : (regs .x12 + 8#64).toNat = (regs .x12).toNat + 8 := toNat_add_ofNat (by omega)
  have eq16 : (regs .x12 + 16#64).toNat = (regs .x12).toNat + 16 := toNat_add_ofNat (by omega)
  have p0 := c3 (regs .x12) ⟨by omega, by omega⟩
  have p8 := c3 (regs .x12 + 8#64) ⟨by omega, by omega⟩
  have p16 := c3 (regs .x12 + 16#64) ⟨by omega, by omega⟩
  have hlen : (m.getMem (regs .x10 + 40#64)).toNat ≤ (m.getMem (regs .x10 + 24#64)).toNat := by
    have := hV2.2.2; rwa [Runtime.ReserveT.vecLen_eq, Runtime.ReserveT.vecCap_eq, add24_16] at this
  have hc24 : M.getMem (rvCapAt (regs .x10 + 24#64)) = m.getMem (rvCapAt (regs .x10 + 24#64)) := by
    rw [Runtime.GrowOne.rvCapAt_eq]; exact hI_20
  have hp32 : M.getMem (rvPtrAt (regs .x10 + 24#64)) = m.getMem (rvPtrAt (regs .x10 + 24#64)) := by
    rw [Runtime.GrowOne.rvPtrAt_eq, add24_8]; exact hI_21
  have hRV : RawVecT env M (regs .x10 + 24#64) 24 := hV2.2.1.keep hc24 hp32 hI_28.1
  have hnM := hI_28.2.1
  have hlt := (env.next M).isLt
  have tk : ∀ k : Nat, k ≤ 48 → (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k :=
    fun k hk => toNat_add_ofNat (by omega)
  have hB := hRV.2.2.1
  rw [Runtime.GrowOne.rvCapAt_eq, Runtime.GrowOne.rvPtrAt_eq, add24_8, hI_20, hI_21] at hB
  rv_symT hp stop [86] with [hL] using [hg]
  · -- room: `pull`'s element at index `len`
    have hne : (m.getMem (regs .x10 + 40#64)).toNat ≠ (m.getMem (regs .x10 + 24#64)).toNat :=
      fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hb1, hb2, hb3⟩ := hB.resolve_left (by omega)
    unfold Env.Live at hb2
    refine fin hp hL hn hk hstk hnx hW h16 ha ha2 ha8 hPost _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hI_14, hI_15, hI_16, hI_17, hI_18, hI_19, ?_, ?_,
        ?_, ?_, ?_, Or.inl ⟨hI_21, hI_20⟩, ⟨hI_23, hI_24, hI_25, hI_26, hI_27⟩, hI_28, hI_29, hI_30⟩
      ⟨c1, by rw [hI_21]; exact ElemsEq.of_keeps c2 (by omega),
        ⟨by simp only [Tactic.rf]; exact p0, by simp only [Tactic.rf]; exact p8,
          by simp only [Tactic.rf]; exact p16⟩, c4⟩
    · simp only [Tactic.rf]; rw [hI_21, addr24 (by omega)]
    all_goals first | (rw [hI_20]; omega) | (rw [hI_21]; omega) | (rw [hI_20, hI_21]; omega)
  · -- full: `grow_one(self.pull)`, then the element at index `len` of the grown buffer
    have e24 := tk 24 (by omega)
    have e32 : (regs .x10 + 24#64 + 8#64).toNat = (regs .x10).toNat + 32 := by rw [add24_8]; exact tk 32 (by omega)
    have hR1 : ∀ b : Word, top.toNat - 48 ≤ b.toNat → b.toNat ≠ (regs .x10 + 24#64).toNat →
        b.toNat ≠ (regs .x10 + 24#64 + 8#64).toNat → m1.getMem b = M.getMem b := fun b h1 h2 h3 =>
      keep1_1 b (BitVec.le_def.2 (by rw [top48 (by omega)]; exact h1)) (not_growOut rfl h2 h3)
    simp only [Runtime.GrowOne.rvCapAt_eq, Runtime.GrowOne.rvPtrAt_eq, add24_8] at hret1_16 hret1_17 hret1_18
    simp only [Runtime.GrowOne.rvCapAt_eq, Runtime.GrowOne.rvPtrAt_eq, add24_8] at hret1_21 hret1_22
    rw [hI_20] at hret1_16
    rw [hI_20, hI_21, show Layouts.Vec.byteSize = 24 from rfl] at hret1_18
    have hcap : (m.getMem (regs .x10 + 24#64)).toNat + 1 ≤ (m1.getMem (regs .x10 + 24#64)).toNat := hret1_16
    have hfr := hret1_17
    unfold Env.Fresh at hfr
    rw [show Layouts.Vec.byteSize = 24 from rfl] at hfr
    have hc' := congrArg BitVec.toNat hc
    obtain ⟨hb1, -, hb3⟩ := hret1_21.resolve_left (by omega)
    have hnm1 := hret1_14.1
    have k0 := hR1 (regs .x10) (by omega) (by omega) (by omega)
    have k8 := hR1 (regs .x10 + 8#64) (by rw [tk 8 (by omega)]; omega) (by rw [tk 8 (by omega)]; omega)
      (by rw [tk 8 (by omega)]; omega)
    have k16 := hR1 (regs .x10 + 16#64) (by rw [tk 16 (by omega)]; omega) (by rw [tk 16 (by omega)]; omega)
      (by rw [tk 16 (by omega)]; omega)
    have k40 := hR1 (regs .x10 + 40#64) (by rw [tk 40 (by omega)]; omega) (by rw [tk 40 (by omega)]; omega)
      (by rw [tk 40 (by omega)]; omega)
    have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 48 → (top + c).toNat = top.toNat - k :=
      fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
    have ks : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 40 → m1.getMem (top + c) = M.getMem (top + c) :=
      fun c k hc h0 hk => hR1 _ (by rw [e c k hc (by omega)]; omega) (by rw [e c k hc (by omega)]; omega)
        (by rw [e c k hc (by omega)]; omega)
    have hW' := hW.heapEnd_le
    have hH : ∀ b : Word, b.toNat < (env.next M).toNat → m1.getMem b = M.getMem b := fun b hb =>
      hret1_14.getMem_below_next hnM hb (not_growOut (a := regs .x10 + 24#64) rfl (by omega) (by omega))
    have q0 := hR1 (regs .x12) (by omega) (by omega) (by omega)
    have q8 := hR1 (regs .x12 + 8#64) (by omega) (by omega) (by omega)
    have q16 := hR1 (regs .x12 + 16#64) (by omega) (by omega) (by omega)
    have hlt1 := (env.next m1).isLt
    refine fin hp hL hn hk hstk hnx hW h16 ha ha2 ha8 hPost _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hret1_22, hb1, ?_, hb3,
        Or.inr (by have := hI_28.1; omega), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hret1_15, hret1_23.trans hI_30⟩
      ⟨c1.keep (fun b hb => hH b (by simp only [InRange, vp, vl] at hb; omega)) (by rw [vp, vp, k8])
          (by simp only [vp, vl]; omega),
        ElemsEq.grown (ElemsEq.of_keeps c2 (by omega)) hret1_18 (by omega) (by omega) (by omega)
          (fun h => by rcases hb2' with h0 | ⟨-, h8⟩ <;> omega) hb3,
        ⟨by simp only [Tactic.rf]; rw [q0, p0], by simp only [Tactic.rf]; rw [q8, p8],
          by simp only [Tactic.rf]; rw [q16, p16]⟩,
        by simp only [BufsApart, k0, k8]; omega⟩
    · simp only [Tactic.rf]; rw [addr24 (by omega)]
    · rw [k16]; exact hI_14
    · rw [k16, k0]; exact hI_15
    · rw [k0]; exact hI_16
    · rw [k8]; exact hI_17
    · rw [k8, k0]; omega
    · rw [k8]; exact hI_19
    · omega
    · exact hfr.2
    · rw [ks _ 8 rfl (by omega) (by omega)]; exact hI_23
    · rw [ks _ 16 rfl (by omega) (by omega)]; exact hI_24
    · rw [ks _ 24 rfl (by omega) (by omega)]; exact hI_25
    · rw [ks _ 32 rfl (by omega) (by omega)]; exact hI_26
    · rw [ks _ 40 rfl (by omega) (by omega)]; exact hI_27
    · exact hI_28.trans hret1_14 (by rw [top48 (by omega)]; omega) fun b hb =>
        Or.inr (Or.inr (Or.inr (Or.inl (growOut_in (k := 24) (by exact tk 24 (by omega)) (by omega) (by omega) hb))))

/-- The state at instruction 52, `MInv`'s with the element's address in `x10`, the new length in `x19`, `self.pull`'s
    capacity and length in `x16`, `x18`. -/
def SInv1 (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551568#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x12 ∧
    R .x16 = M.getMem (regs .x10 + 24#64) ∧ R .x18 = M.getMem (regs .x10 + 40#64) ∧
    R .x19 = m.getMem (regs .x10 + 16#64) + 1#64 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧
    R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27 ∧
    (R .x10).toNat = (M.getMem (regs .x10 + 8#64)).toNat + 24 * (m.getMem (regs .x10 + 16#64)).toNat ∧
    (m.getMem (regs .x10 + 16#64)).toNat < (M.getMem (regs .x10)).toNat ∧
    (M.getMem (regs .x10)).toNat * 24 < 2 ^ 63 ∧
    0x10000000 ≤ (M.getMem (regs .x10 + 8#64)).toNat ∧
    (M.getMem (regs .x10 + 8#64)).toNat + (M.getMem (regs .x10)).toNat * 24 ≤ (env.next M).toNat ∧
    (M.getMem (regs .x10 + 8#64)).toNat % 8 = 0 ∧
    ((M.getMem (regs .x10 + 8#64) = m.getMem (regs .x10 + 8#64) ∧ M.getMem (regs .x10) = m.getMem (regs .x10)) ∨
      (env.next m).toNat ≤ (M.getMem (regs .x10 + 8#64)).toNat) ∧
    M.getMem (regs .x10 + 24#64) = m.getMem (regs .x10 + 24#64) ∧
    M.getMem (regs .x10 + 32#64) = m.getMem (regs .x10 + 32#64) ∧
    M.getMem (regs .x10 + 40#64) = m.getMem (regs .x10 + 40#64) ∧
    Slots M top ret regs ∧ env.Frame top (OutT regs m) m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **From instruction 52 to 60**: `push` stored, `self.push`'s length stored. -/
theorem stores {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG : Nat} (hn : 48 ≤ need) (hnG : 48 + needG ≤ need)
    (hg : GrowOneSpecT env Layouts.Vec.byteAlign Layouts.Vec.byteSize p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    (hk : ∀ r' m', HoldsT.post env Post OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (ha : top.toNat ≤ (regs .x10).toNat) (ha2 : (regs .x10).toNat + 48 ≤ 0xc0000000) (ha8 : (regs .x10).toNat % 8 = 0)
    (hq : top.toNat ≤ (regs .x12).toNat) (hq2 : (regs .x12).toNat + 24 ≤ 0xc0000000) (hq8 : (regs .x12).toNat % 8 = 0)
    (hap2 : Apart (regs .x10) 48 (regs .x12) 24) (hV2 : VecT env m (regs .x10 + 24#64) 24)
    (hPost : ∀ r' m', r' .x2 = top → PostM env regs m top m' → Post regs m r' m') :
    ∀ R M, SInv1 env m top ret regs R M → Cont1 m regs M → Loaded R .x13 .x14 .x15 m (regs .x11) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 52, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hC hld
  obtain ⟨c1, c2, -, c4, c5⟩ := hC
  obtain ⟨l0, l8, l16⟩ := hld
  have hap := hap2
  unfold Apart at hap
  have hlay := env.layout
  rv_introT hI
  obtain ⟨hl2, -, hb2'⟩ := pull_live hV2
  have hnm := hI_30.1
  have ba := c5
  unfold BufsApart at ba
  rw [hI_22, hI_23] at ba
  have hnM := hI_30.2.1
  have hW' := hW.heapEnd_le
  obtain ⟨hf3, hn3⟩ := frame_elem (v1 := R .x13) (v2 := R .x14) (v3 := R .x15) hI_30 hI_19 hI_15 hI_16
    (hI_21.imp (fun ⟨e8, e0⟩ c hc1 hc2 => Or.inr (Or.inl (by
      unfold SlotOut; rw [← e0, ← e8]; exact ⟨hI_16, by omega, by omega⟩))) id)
  have tk : ∀ k : Nat, k ≤ 48 → (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k :=
    fun k hk => toNat_add_ofNat (by omega)
  have e16 := tk 16 (by omega)
  have hA : (R .x10).toNat + 24 ≤ env.heapEnd.toNat := by omega
  have rd : ∀ b : Word, env.stackLimit.toNat ≤ b.toNat → b ≠ regs .x10 + 16#64 →
      ((((M.setMem (R .x10) (R .x13)).setMem (R .x10 + 8#64) (R .x14)).setMem (R .x10 + 16#64) (R .x15)).setMem
        (regs .x10 + 16#64) (m.getMem (regs .x10 + 16#64) + 1#64)).getMem b = M.getMem b := fun b hb hne => by
    rw [MachineState.getMem_setMem_ne hne, get_elem hA hb]
  have ne : ∀ k : Nat, k ≤ 48 → k ≠ 16 → regs .x10 + BitVec.ofNat 64 k ≠ regs .x10 + 16#64 := fun k hk hk' e => by
    have := congrArg BitVec.toNat e
    rw [tk k hk, e16] at this
    omega
  have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 48 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have rs : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 48 →
      ((((M.setMem (R .x10) (R .x13)).setMem (R .x10 + 8#64) (R .x14)).setMem (R .x10 + 16#64) (R .x15)).setMem
        (regs .x10 + 16#64) (m.getMem (regs .x10 + 16#64) + 1#64)).getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk => rd _ (by rw [e c k hc hk]; omega) fun he => by
      have := congrArg BitVec.toNat he; rw [e c k hc hk, e16] at this; omega
  have hl1 : (m.getMem (regs .x10 + 16#64) + 1#64).toNat = (m.getMem (regs .x10 + 16#64)).toNat + 1 :=
    toNat_add_ofNat (by omega)
  have hnext : env.next ((((M.setMem (R .x10) (R .x13)).setMem (R .x10 + 8#64) (R .x14)).setMem
      (R .x10 + 16#64) (R .x15)).setMem (regs .x10 + 16#64) (m.getMem (regs .x10 + 16#64) + 1#64)) = env.next M := by
    rw [Tactic.next_setMem (fun h => by rw [h] at e16; omega), hn3]
  have r0 := rd (regs .x10) (by omega) (by simp)
  have r8 := rd (regs .x10 + 8#64) (by rw [tk 8 (by omega)]; omega) (ne 8 (by omega) (by omega))
  have r24 := rd (regs .x10 + 24#64) (by rw [tk 24 (by omega)]; omega) (ne 24 (by omega) (by omega))
  have r32 := rd (regs .x10 + 32#64) (by rw [tk 32 (by omega)]; omega) (ne 32 (by omega) (by omega))
  have r40 := rd (regs .x10 + 40#64) (by rw [tk 40 (by omega)]; omega) (ne 40 (by omega) (by omega))
  rv_symT hp stop [60] with [hL]
  have eq8 : (regs .x12 + 8#64).toNat = (regs .x12).toNat + 8 := toNat_add_ofNat (by omega)
  have hs16 : (regs .x10 + 16#64).toNat < (regs .x12).toNat ∨ (regs .x12).toNat + 24 ≤ (regs .x10 + 16#64).toNat := by
    omega
  refine call hp hL hn hnG hg hk hstop hstk hnx hW h16 ha ha2 ha8 hq hq2 hq8 hap2 hV2 hPost _ _
    ⟨rfl, rfl, rfl, hI_22, hI_24, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, by simp only [MachineState.code_setMem, hI_32]⟩
    ⟨⟨by simp only [vp, vl, r8]; exact c1.keep (keeps_stores (by omega) (by omega) (by omega)) (by omega),
        fun j hj => by
          simp only [vp, vl, r8]
          have eB : (M.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 (24 * (m.getMem (regs .x10 + 16#64)).toNat +
              8 * j)).toNat = (M.getMem (regs .x10 + 8#64)).toNat + (24 * (m.getMem (regs .x10 + 16#64)).toNat +
              8 * j) := toNat_add_ofNat (by omega)
          rw [MachineState.getMem_setMem_ne (fun h => by rw [h] at eB; omega)]
          exact get3 hj (by omega) (by omega) l0 l8 l16⟩,
      c2.trans (keeps_stores (by omega) (by omega) (by omega)),
      c4.trans (keeps_stores (by omega) (by omega) hs16),
      by simp only [BufsApart, r0, r8, r24, r32]; exact c5⟩
  · rw [MachineState.getMem_setMem_eq, hl1]
  · rw [MachineState.getMem_setMem_eq, hl1, r0]; omega
  · rw [r0]; exact hI_17
  · rw [r8]; exact hI_18
  · rw [r0, r8, hnext]; exact hI_19
  · rw [r8]; exact hI_20
  · rw [r24]; exact hI_22
  · rw [r32]; exact hI_23
  · rw [r40]; exact hI_24
  · rw [rs _ 8 rfl (by omega) (by omega)]; exact hI_25
  · rw [rs _ 16 rfl (by omega) (by omega)]; exact hI_26
  · rw [rs _ 24 rfl (by omega) (by omega)]; exact hI_27
  · rw [rs _ 32 rfl (by omega) (by omega)]; exact hI_28
  · rw [rs _ 40 rfl (by omega) (by omega)]; exact hI_29
  · exact Tactic.frame_out hf3 (Or.inl ⟨by rw [e16]; omega, by rw [e16]; omega⟩) (fun h => by rw [h] at e16; omega)
  · have hR := hI_15
    refine Tactic.static_store (Tactic.static_store (Tactic.static_store (Tactic.static_store hI_31 ?_) ?_) ?_) ?_
    all_goals first
      | (left; omega)
      | (left; rw [toNat_add_ofNat (by omega)]; omega)
      | (right; rw [e16]; omega)

set_option rv_sym.heap true in
/-- **From instruction 30 to 52**: the element's address. -/
theorem mid {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG : Nat} (hn : 48 ≤ need) (hnG : 48 + needG ≤ need)
    (hg : GrowOneSpecT env Layouts.Vec.byteAlign Layouts.Vec.byteSize p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    (hk : ∀ r' m', HoldsT.post env Post OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (ha : top.toNat ≤ (regs .x10).toNat) (ha2 : (regs .x10).toNat + 48 ≤ 0xc0000000) (ha8 : (regs .x10).toNat % 8 = 0)
    (hs : top.toNat ≤ (regs .x11).toNat) (hs2 : (regs .x11).toNat + 24 ≤ 0xc0000000) (hs8 : (regs .x11).toNat % 8 = 0)
    (hq : top.toNat ≤ (regs .x12).toNat) (hq2 : (regs .x12).toNat + 24 ≤ 0xc0000000) (hq8 : (regs .x12).toNat % 8 = 0)
    (hap2 : Apart (regs .x10) 48 (regs .x12) 24) (hV2 : VecT env m (regs .x10 + 24#64) 24)
    (hPost : ∀ r' m', r' .x2 = top → PostM env regs m top m' → Post regs m r' m') :
    ∀ R M, MInv env m top ret regs R M → Cont1 m regs M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 30, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hC
  have es8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
  have es16 : (regs .x11 + 16#64).toNat = (regs .x11).toNat + 16 := toNat_add_ofNat (by omega)
  have u0 := hC.2.2.1 (regs .x11) ⟨by omega, by omega⟩
  have u8 := hC.2.2.1 (regs .x11 + 8#64) ⟨by omega, by omega⟩
  have u16 := hC.2.2.1 (regs .x11 + 16#64) ⟨by omega, by omega⟩
  have hlay := env.layout
  rv_introT hI
  have hnM := hI_29.2.1
  have hlt := (env.next M).isLt
  rv_symT hp stop [52] with [hL]
  refine stores hp hL hn hnG hg hk hstop hstk hnx hW h16 ha ha2 ha8 hq hq2 hq8 hap2 hV2 hPost _ _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hI_14, hI_15, hI_16, hI_17, hI_18,
      hI_19, hI_21, hI_22, hI_23, ⟨hI_24, hI_25, hI_26, hI_27, hI_28⟩, hI_29, hI_30, hI_31⟩ hC
    ⟨by simp only [Tactic.rf]; exact u0, by simp only [Tactic.rf]; exact u8,
      by simp only [Tactic.rf]; exact u16⟩
  simp only [Tactic.rf]
  rw [addr24 (by omega)]

set_option rv_sym.heap true in
/-- **From the entry to instruction 30**: `grow_one` when `self.push` is full. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needG : Nat} (hnG : 48 + needG ≤ need)
    (hg : GrowOneSpecT env Layouts.Vec.byteAlign Layouts.Vec.byteSize p L.growOne.idx needG) :
    SpecT env p i need := by
  rv_autoT hp stop [30] with [hL] using [hg]
  all_goals
    have hlay := env.layout
    rw [hpre_2] at hpre_18 hpre_22 hpre_25
    have hap2 : Apart (regs .x10) 48 (regs .x12) 24 := hpre_29
    have hap1' : Apart (regs .x10) 48 (regs .x11) 24 := hpre_28
    have hap2' := hap2
    unfold Apart at hap1' hap2'
    have hltm := (env.next m).isLt
    have hlim : env.stackLimit.toNat + 48 ≤ top.toNat := by omega
    obtain ⟨hF0, hS0, hn0, hsl⟩ := saved_ok (out := OutT regs m) (ret := ret) (regs := regs) hlim hpre_5 hpre_4
    have sv : ∀ b : Word, top.toNat ≤ b.toNat → (saved m top ret regs).getMem b = m.getMem b :=
      fun b hb => saved_get (by omega) (.inl hb)
    have tk : ∀ k : Nat, k ≤ 48 → (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k :=
      fun k hk => toNat_add_ofNat (by omega)
    have hV2 : VecT env m (regs .x10 + 24#64) 24 := ⟨hpre_12, ⟨hpre_13, hpre_14, hpre_15, hpre_16⟩, hpre_17⟩
    obtain ⟨hl2, -, hb2'⟩ := pull_live hV2
    have hB := hpre_9
    simp only [Runtime.GrowOne.rvCapAt_eq, Runtime.GrowOne.rvPtrAt_eq, Env.Live] at hB hpre_10
    have hlen := hpre_11
    rw [Runtime.ReserveT.vecLen_eq, Runtime.ReserveT.vecCap_eq] at hlen
    have ks1 : Keeps m (saved m top ret regs) (m.getMem (regs .x10 + 8#64))
        (24 * (m.getMem (regs .x10 + 16#64)).toNat) := keeps_saved (by omega) (by omega)
    have ks2 : Keeps m (saved m top ret regs) (m.getMem (regs .x10 + 32#64))
        (24 * (m.getMem (regs .x10 + 40#64)).toNat) := keeps_saved (by omega) (by omega)
    have ks3 : Keeps m (saved m top ret regs) (regs .x11) 24 := keeps_saved (by omega) (.inr (.inl hpre_22))
    have ks4 : Keeps m (saved m top ret regs) (regs .x12) 24 := keeps_saved (by omega) (.inr (.inl hpre_25))
    simp only [saved] at hF0 hS0 hn0 hsl sv ks1 ks2 ks3 ks4
    have s0 := sv (regs .x10) (by omega)
    have s8 := sv (regs .x10 + 8#64) (by rw [tk 8 (by omega)]; omega)
    have s16 := sv (regs .x10 + 16#64) (by rw [tk 16 (by omega)]; omega)
    have s24 := sv (regs .x10 + 24#64) (by rw [tk 24 (by omega)]; omega)
    have s32 := sv (regs .x10 + 32#64) (by rw [tk 32 (by omega)]; omega)
    have s40 := sv (regs .x10 + 40#64) (by rw [tk 40 (by omega)]; omega)
    have hPost : ∀ r' m', r' .x2 = top → PostM env regs m top m' → PostT env regs m r' m' :=
      fun r' m' h1 h2 => by unfold PostT; rw [h1]; exact h2
  · -- room
    have hne : (m.getMem (regs .x10 + 16#64)).toNat ≠ (m.getMem (regs .x10)).toNat :=
      fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hb1, hb2, hb3⟩ := hB.resolve_left (by omega)
    refine mid hp hL (by omega) hnG hg hk hstop hpre_3 hpre_5 hpre_31 hpre_30 hpre_18 hpre_19 hpre_21 hpre_22 hpre_23
      hpre_24 hpre_25 hpre_26 hpre_27 hap2 hV2 hPost _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_,
        Or.inl ⟨s8, s0⟩, s16, s24, s32, s40, hsl, hF0, hS0, by simp only [MachineState.code_setMem]⟩
      ⟨by rw [s8]; exact ElemsEq.of_keeps ks1 (by omega), ks2, ks3, ks4,
        by simp only [BufsApart, s0, s8, s24, s32]; exact hpre_20⟩
    all_goals simp only [s0, s8, hn0]
    all_goals omega
  all_goals try
    (simp only [Runtime.GrowOne.rvCapAt_eq, Runtime.GrowOne.rvPtrAt_eq, Env.Live, s0, s8, hn0]
     first | exact hpre_10 | exact hB | exact hB.imp id fun h => h.2.1)
  · -- full: `grow_one(self.push)`, then room
    have hR1 : ∀ b : Word, top.toNat - 48 ≤ b.toNat → b.toNat ≠ (regs .x10).toNat →
        b.toNat ≠ (regs .x10 + 8#64).toNat → MachineState.getMem m1 b = _ := fun b h1 h2 h3 =>
      keep1_1 b (BitVec.le_def.2 (by rw [top48 (by omega)]; exact h1)) (not_growOut rfl h2 h3)
    simp only [Runtime.GrowOne.rvCapAt_eq, Runtime.GrowOne.rvPtrAt_eq, s0] at hret1_16 hret1_17 hret1_18
    simp only [Runtime.GrowOne.rvCapAt_eq, Runtime.GrowOne.rvPtrAt_eq] at hret1_21 hret1_22
    rw [s8, show Layouts.Vec.byteSize = 24 from rfl] at hret1_18
    have hfr := hret1_17
    unfold Env.Fresh at hfr
    rw [show Layouts.Vec.byteSize = 24 from rfl, hn0] at hfr
    have hc' := congrArg BitVec.toNat hc
    obtain ⟨hb1, -, hb3⟩ := hret1_21.resolve_left (by omega)
    have k16 := hR1 (regs .x10 + 16#64) (by rw [tk 16 (by omega)]; omega) (by rw [tk 16 (by omega)]; omega)
      (by rw [tk 16 (by omega), tk 8 (by omega)]; omega)
    have k24 := hR1 (regs .x10 + 24#64) (by rw [tk 24 (by omega)]; omega) (by rw [tk 24 (by omega)]; omega)
      (by rw [tk 24 (by omega), tk 8 (by omega)]; omega)
    have k32 := hR1 (regs .x10 + 32#64) (by rw [tk 32 (by omega)]; omega) (by rw [tk 32 (by omega)]; omega)
      (by rw [tk 32 (by omega), tk 8 (by omega)]; omega)
    have k40 := hR1 (regs .x10 + 40#64) (by rw [tk 40 (by omega)]; omega) (by rw [tk 40 (by omega)]; omega)
      (by rw [tk 40 (by omega), tk 8 (by omega)]; omega)
    have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 48 → (top + c).toNat = top.toNat - k :=
      fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
    have ks : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 40 → MachineState.getMem m1 (top + c) = _ :=
      fun c k hc h0 hk => hR1 _ (by rw [e c k hc (by omega)]; omega) (by rw [e c k hc (by omega)]; omega)
        (by rw [e c k hc (by omega), tk 8 (by omega)]; omega)
    obtain ⟨l8, l16, l24, l32, l40⟩ := hsl
    have hW' := hpre_31.heapEnd_le
    have hH : ∀ b : Word, b.toNat < (env.next m).toNat → MachineState.getMem m1 b = _ := fun b hb =>
      hret1_14.getMem_below_next (by rw [hn0]; exact hpre_5) (by rw [hn0]; exact hb)
        (not_growOut (a := regs .x10) rfl (by omega) (by rw [tk 8 (by omega)]; omega))
    have hlt1 := (env.next m1).isLt
    have hfr1 := hfr.1
    have hfr2 := hfr.2
    refine mid hp hL (by omega) hnG hg hk hstop hpre_3 hpre_5 hpre_31 hpre_30 hpre_18 hpre_19 hpre_21 hpre_22 hpre_23
      hpre_24 hpre_25 hpre_26 hpre_27 hap2 hV2 hPost _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by omega, hret1_22, hb1, hfr.2, hb3,
        Or.inr hfr.1, by rw [k16, s16], by rw [k24, s24], by rw [k32, s32], by rw [k40, s40],
        ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hret1_15, by rw [hret1_23]; simp only [MachineState.code_setMem]⟩
      ⟨ElemsEq.grown (ElemsEq.of_keeps ks1 (by omega)) hret1_18 hlen (by omega) (by omega)
          (fun h => by rcases hB with h0 | ⟨-, -, h8⟩ <;> omega) hb3,
        ks2.trans fun b hb => hH b (by unfold InRange at hb; omega),
        ks3.trans fun b hb => hR1 b (by unfold InRange at hb; omega) (by unfold InRange at hb; omega)
          (by rw [tk 8 (by omega)]; unfold InRange at hb; omega),
        ks4.trans fun b hb => hR1 b (by unfold InRange at hb; omega) (by unfold InRange at hb; omega)
          (by rw [tk 8 (by omega)]; unfold InRange at hb; omega),
        by simp only [BufsApart, k24, k32, s24, s32]; omega⟩
    · rw [ks _ 8 rfl (by omega) (by omega)]; exact l8
    · rw [ks _ 16 rfl (by omega) (by omega)]; exact l16
    · rw [ks _ 24 rfl (by omega) (by omega)]; exact l24
    · rw [ks _ 32 rfl (by omega) (by omega)]; exact l32
    · rw [ks _ 40 rfl (by omega) (by omega)]; exact l40
    · exact hF0.trans hret1_14 (by rw [top48 (by omega)]; omega) fun b hb =>
        Or.inr (Or.inr (Or.inr (Or.inl (growOut_in (k := 0) (by exact rfl) (by omega) (by omega) hb))))

end Rv64mc.Proof.Layout.PairT

/-- info: 'Rv64mc.Proof.Layout.PairT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.PairT.total
