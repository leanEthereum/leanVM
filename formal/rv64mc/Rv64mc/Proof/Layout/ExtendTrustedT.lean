/-
  Rv64mc.Proof.Layout.ExtendTrustedT

  `Vec<BusBlock>::extend_trusted` over `build_layout`'s closure (`push.extend(table.flushes.push.iter().map(block))`)
  is total: called with the vector's header (`a0`) and the iterator (`a1`: the slice `[begin, end)` of `n` source
  `Vec<Form>` headers, then the closure's three captures), it reserves `n` more elements (`Vec::reserve`), then for
  each source clones the `Vec<Form>` (`<Vec<Form> as Clone>::clone`, through `CloneFormsFreshT`'s contract), reads
  the captures, and stores the 48-byte `BusBlock` (the clone's header and three words) into the next slot; it stores
  the new length last. The run ends with the guest's abort (`AbortStop`) where `reserve` or the clone does. A
  safety-only contract (class D); it does not state the three words.

  The precondition: the vector `VecT` with its header at or above the stack pointer, its `BusBlock`s' coordinates
  `Vec<Form>`s (`BlocksT`) whose footprints (`InFoot`: the `Form`s' headers and their terms' blocks) avoid its buffer;
  the iterator a caller's frame object apart from the header; the source whole 24-byte headers, unless empty apart
  from the stack below the stack pointer, from the heap not yet allocated, from the buffer and from the header, each
  a `Vec<Form>` whose footprint avoids the buffer; the three captures' addresses in windows and aligned. At its call
  sites (`build_layout`, `push` and `pull` per table) the headers are slots of `build_layout`'s frame, the iterator
  another, the sources a table's `Flushes` vectors and the buffer, empty at first, allocated by an earlier call, after
  the tables were built.

  The postcondition: the vector `VecT` again, its length grown by `n`, its buffer the entry's or allocated since the
  entry (`PairT.KeptOrFresh`), all its `BusBlock`s' coordinates `Vec<Form>`s whose footprints avoid it. What it
  writes besides its stack and fresh blocks is the header and the buffer at entry (`OutT`). When `reserve` grows the
  buffer, the old `BusBlock`s' headers move with its bytes (`Grown`, `word_of_grown`) and their footprints, below
  `NEXT` at entry, stay below the new block.

  The body is cut at the loop's head (instruction 78, measure the sources left), after the clone (92) and the
  return (118). Every part keeps `MInv`: `MemOk`, the header's capacity and pointer after `reserve`, the old
  `BusBlock`s and the new ones (`DoneB`: their footprints allocated since `reserve`).

  ## Main definitions

  * `cnt`, `InFoot`, `FootApart`, `FootIn`, `BlocksT`, `bufHi`, `PreT`, `PostT`, `OutT`, `SpecT`, `DoneB`, `Slots`,
    `MemOk`, `Args`, `Buf`, `MInv`, `LRegs`, `LInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.SpecExtendFormT
import Rv64mc.Proof.Layout.FromElemVecFormT
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecBusBlock.ExtendTrustedMapIterVecFH61757d77

namespace Rv64mc.Proof.Layout.ExtendTrustedT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.ReserveT (ReserveSpecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Layout.FromElemVecFormT (VecFormT)
open Rv64mc.Proof.Layout.CloneFormsT (vecT_copy es)
open Rv64mc.Proof.Layout.SpecExtendFormT (keepF)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Proof.Layout.PairT (Apart KeptOrFresh)
open Rv64mc.Gen.Alloc.Vec.VecBusBlock.ExtendTrustedMapIterVecFH61757d77 (Link tmpl)

/-- The source's count: `(end - begin) / 24`, the iterator's slice `[begin, end)` at `a1` and `a1 + 8`. -/
def cnt (regs : Reg → Word) (m : MachineState) : Nat :=
  ((m.getMem (regs .x11 + 8#64)).toNat - (m.getMem (regs .x11)).toNat) / 24

/-- **`b` is in the footprint of the `Vec<Form>` at `a`**: in its `Form`s' headers or in one of their terms'
    blocks. -/
def InFoot (m : MachineState) (a b : Word) : Prop :=
  ((vecPtr m a).toNat ≤ b.toNat ∧ b.toNat < (vecPtr m a).toNat + 24 * (vecLen m a).toNat) ∨
    ∃ i, i < (vecLen m a).toNat ∧
      (vecPtr m (vecPtr m a + BitVec.ofNat 64 (24 * i))).toNat ≤ b.toNat ∧
      b.toNat < (vecPtr m (vecPtr m a + BitVec.ofNat 64 (24 * i))).toNat +
        40 * (vecLen m (vecPtr m a + BitVec.ofNat 64 (24 * i))).toNat

/-- **The footprint of the `Vec<Form>` at `a` avoids `[lo, hi)`**. -/
def FootApart (m : MachineState) (a : Word) (lo hi : Nat) : Prop :=
  ∀ b : Word, InFoot m a b → b.toNat < lo ∨ hi ≤ b.toNat

/-- **The footprint of the `Vec<Form>` at `a` lies in `[lo, hi)`**. -/
def FootIn (m : MachineState) (a : Word) (lo hi : Nat) : Prop :=
  ∀ b : Word, InFoot m a b → lo ≤ b.toNat ∧ b.toNat < hi

/-- **`n` `BusBlock`s from `q`**, 48 bytes each: each one's coordinates (its first 24 bytes) a `Vec<Form>` whose
    footprint avoids `[lo, hi)`. -/
def BlocksT (env : Env) (m : MachineState) (q : Word) (n lo hi : Nat) : Prop :=
  ∀ i, i < n → VecFormT env m (q + BitVec.ofNat 64 (48 * i)) ∧ FootApart m (q + BitVec.ofNat 64 (48 * i)) lo hi

/-- The end of the vector's buffer at `a`, as a number. -/
def bufHi (m : MachineState) (a : Word) : Nat := (vecPtr m a).toNat + 48 * (vecCap m a).toNat

/-- The total precondition: the vector with its `BusBlock`s, its header a caller's frame object; the iterator a
    caller's frame object; the source `Vec<Form>`s whole, apart from the stack below the stack pointer, the heap not
    yet allocated, the header and the buffer; every footprint apart from the buffer; the captures readable. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  VecT env m (regs .x10) 48 ∧ StackObj (regs .x2) (regs .x10) 24 ∧
    BlocksT env m (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat (vecPtr m (regs .x10)).toNat
      (bufHi m (regs .x10)) ∧
    StackObj (regs .x2) (regs .x11) 40 ∧ (regs .x11).toNat % 8 = 0 ∧ Apart (regs .x11) 40 (regs .x10) 24 ∧
    (m.getMem (regs .x11)).toNat ≤ (m.getMem (regs .x11 + 8#64)).toNat ∧
    ((m.getMem (regs .x11 + 8#64)).toNat - (m.getMem (regs .x11)).toNat) % 24 = 0 ∧
    (cnt regs m = 0 ∨ (OffStack env (regs .x2) (m.getMem (regs .x11)) (24 * cnt regs m) ∧
      ((m.getMem (regs .x11)).toNat + 24 * cnt regs m ≤ (env.next m).toNat ∨
        env.heapEnd.toNat ≤ (m.getMem (regs .x11)).toNat) ∧
      ((m.getMem (regs .x11)).toNat + 24 * cnt regs m ≤ (vecPtr m (regs .x10)).toNat ∨
        bufHi m (regs .x10) ≤ (m.getMem (regs .x11)).toNat) ∧
      Apart (m.getMem (regs .x11)) (24 * cnt regs m) (regs .x10) 24)) ∧
    (∀ i, i < cnt regs m → VecFormT env m (m.getMem (regs .x11) + BitVec.ofNat 64 (24 * i)) ∧
      FootApart m (m.getMem (regs .x11) + BitVec.ofNat 64 (24 * i)) (vecPtr m (regs .x10)).toNat
        (bufHi m (regs .x10))) ∧
    InWin env (m.getMem (regs .x11 + 16#64)) 8 ∧ (m.getMem (regs .x11 + 16#64)).toNat % 8 = 0 ∧
    InWin env (m.getMem (regs .x11 + 24#64)) 8 ∧ (m.getMem (regs .x11 + 24#64)).toNat % 8 = 0 ∧
    InWin env (m.getMem (regs .x11 + 32#64) + 0x48#64) 8 ∧ (m.getMem (regs .x11 + 32#64) + 0x48#64).toNat % 8 = 0

/-- The total postcondition: the vector `n` longer, its buffer the entry's or fresh, its `BusBlock`s' coordinates
    `Vec<Form>`s whose footprints avoid it. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 48 ∧
    (vecLen m' (regs .x10)).toNat = (vecLen m (regs .x10)).toNat + cnt regs m ∧
    KeptOrFresh env m m' (regs .x10) ∧
    BlocksT env m' (vecPtr m' (regs .x10)) (vecLen m' (regs .x10)).toNat (vecPtr m' (regs .x10)).toNat
      (bufHi m' (regs .x10))

/-- What `extend_trusted` writes besides its stack and what it allocates: the header and the buffer at entry. -/
def OutT (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.Vec.byteSize b ∨
    ((vecPtr m (regs .x10)).toNat ≤ b.toNat ∧ b.toNat < bufHi m (regs .x10))

/-- **The total contract of `Vec<BusBlock>::extend_trusted`** over `build_layout`'s closure. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-! ## A `Vec<Form>`'s footprint -/

/-- A `Vec<Form>`'s footprint lies below `NEXT`. -/
theorem VecFormT.foot_lt {env : Env} {m : MachineState} {a b : Word} (h : VecFormT env m a) (hb : InFoot m a b) :
    b.toNat < (env.next m).toNat := by
  rcases hb with ⟨h1, h2⟩ | ⟨i, hi, h1, h2⟩
  · rcases (vecT_buf h.1).1 with h0 | ⟨-, h3, -⟩
    · omega
    · unfold Env.Live at h3; omega
  · have := (h.2 i hi).foot; omega

/-- A `Vec<Form>`'s `Form` headers lie in its footprint, and do not wrap. -/
theorem VecFormT.buf_lt {env : Env} {m : MachineState} {a : Word} (h : VecFormT env m a) :
    (vecPtr m a).toNat + 24 * (vecLen m a).toNat < 2 ^ 64 := by
  rcases (vecT_buf h.1).1 with h0 | ⟨-, h3, -⟩
  · rw [h0]; have := (vecPtr m a).isLt; omega
  · unfold Env.Live at h3; have := (env.next m).isLt; omega

/-- **A `Vec<Form>` is kept** by a memory agreeing on its header and its footprint, `NEXT` no lower. -/
theorem VecFormT.keep {env : Env} {m M : MachineState} {a : Word} (h : VecFormT env m a)
    (hn : (env.next m).toNat ≤ (env.next M).toNat)
    (hh : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 24 → M.getMem b = m.getMem b)
    (hf : ∀ b : Word, InFoot m a b → M.getMem b = m.getMem b) : VecFormT env M a := by
  have hlt := vecT_lt h.1
  have ep : vecPtr M a = vecPtr m a := by
    rw [vecPtr_eq, vecPtr_eq]; exact hh _ (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega)
  have el : vecLen M a = vecLen m a := by
    rw [vecLen_eq, vecLen_eq]; exact hh _ (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega)
  refine ⟨vecT_keep h.1 hn hh, ?_⟩
  rw [ep, el]
  intro i hi
  have hF := h.2 i hi
  have hl2 := VecFormT.buf_lt h
  have e : (vecPtr m a + BitVec.ofNat 64 (24 * i)).toNat = (vecPtr m a).toNat + 24 * i := toNat_add_ofNat (by omega)
  exact hF.keep hn (fun b h1 h2 => hf b (.inl ⟨by omega, by omega⟩)) fun b h1 h2 => hf b (.inr ⟨i, hi, h1, h2⟩)

/-- **A `Vec<Form>`'s header copied** to `b`, in a window and aligned, its footprint kept: a `Vec<Form>` at `b`
    with the same footprint. -/
theorem VecFormT.move {env : Env} {m M : MachineState} {a b : Word} (h : VecFormT env m a)
    (hn : (env.next m).toNat ≤ (env.next M).toNat) (hw : InWin env b 24) (hal : b.toNat % 8 = 0)
    (h0 : M.getMem b = m.getMem a) (h8 : M.getMem (b + 8#64) = m.getMem (a + 8#64))
    (h16 : M.getMem (b + 16#64) = m.getMem (a + 16#64))
    (hf : ∀ x : Word, InFoot m a x → M.getMem x = m.getMem x) :
    VecFormT env M b ∧ vecPtr M b = vecPtr m a ∧ vecLen M b = vecLen m a := by
  have ep : vecPtr M b = vecPtr m a := by rw [vecPtr_eq, vecPtr_eq, h8]
  have el : vecLen M b = vecLen m a := by rw [vecLen_eq, vecLen_eq, h16]
  refine ⟨⟨vecT_copy h.1 hw hal hn h0 h8 h16, ?_⟩, ep, el⟩
  rw [ep, el]
  intro i hi
  have hF := h.2 i hi
  have hl2 := VecFormT.buf_lt h
  have e : (vecPtr m a + BitVec.ofNat 64 (24 * i)).toNat = (vecPtr m a).toNat + 24 * i := toNat_add_ofNat (by omega)
  exact hF.keep hn (fun x h1 h2 => hf x (.inl ⟨by omega, by omega⟩)) fun x h1 h2 => hf x (.inr ⟨i, hi, h1, h2⟩)

/-- **`InFoot` in a memory with the header's two words and the `Form`s' headers the same.** -/
theorem InFoot.of_eq {m M : MachineState} {a b x : Word} (hp : vecPtr M b = vecPtr m a)
    (hl : vecLen M b = vecLen m a)
    (hbuf : ∀ y : Word, (vecPtr m a).toNat ≤ y.toNat → y.toNat < (vecPtr m a).toNat + 24 * (vecLen m a).toNat →
      M.getMem y = m.getMem y)
    (hl2 : (vecPtr m a).toNat + 24 * (vecLen m a).toNat < 2 ^ 64) (hx : InFoot M b x) : InFoot m a x := by
  unfold InFoot at hx ⊢
  rw [hp, hl] at hx
  rcases hx with h | ⟨i, hi, h1, h2⟩
  · exact .inl h
  · have e : (vecPtr m a + BitVec.ofNat 64 (24 * i)).toNat = (vecPtr m a).toNat + 24 * i :=
      toNat_add_ofNat (by omega)
    have e8 : (vecPtr m a + BitVec.ofNat 64 (24 * i) + 8#64).toNat = (vecPtr m a).toNat + 24 * i + 8 := by
      rw [toNat_add_ofNat (by omega), e]
    have e16 : (vecPtr m a + BitVec.ofNat 64 (24 * i) + 16#64).toNat = (vecPtr m a).toNat + 24 * i + 16 := by
      rw [toNat_add_ofNat (by omega), e]
    have p8 : vecPtr M (vecPtr m a + BitVec.ofNat 64 (24 * i)) = vecPtr m (vecPtr m a + BitVec.ofNat 64 (24 * i)) := by
      show M.getMem (vecPtr m a + BitVec.ofNat 64 (24 * i) + 8#64) =
        m.getMem (vecPtr m a + BitVec.ofNat 64 (24 * i) + 8#64)
      exact hbuf _ (by omega) (by omega)
    have p16 : vecLen M (vecPtr m a + BitVec.ofNat 64 (24 * i)) = vecLen m (vecPtr m a + BitVec.ofNat 64 (24 * i)) := by
      show M.getMem (vecPtr m a + BitVec.ofNat 64 (24 * i) + 16#64) =
        m.getMem (vecPtr m a + BitVec.ofNat 64 (24 * i) + 16#64)
      exact hbuf _ (by omega) (by omega)
    rw [p8] at h1 h2
    rw [p16] at h2
    exact .inr ⟨i, hi, h1, h2⟩

/-- **A `Vec<Form>` whose header's words were copied** from `a` to `b`, its footprint kept: the same footprint, and
    whatever avoids or contains it still does. -/
theorem VecFormT.move' {env : Env} {m M : MachineState} {a b : Word} (h : VecFormT env m a)
    (hn : (env.next m).toNat ≤ (env.next M).toNat) (hw : InWin env b 24) (hal : b.toNat % 8 = 0)
    (h0 : M.getMem b = m.getMem a) (h8 : M.getMem (b + 8#64) = m.getMem (a + 8#64))
    (h16 : M.getMem (b + 16#64) = m.getMem (a + 16#64))
    (hf : ∀ x : Word, InFoot m a x → M.getMem x = m.getMem x) :
    VecFormT env M b ∧ ∀ x, InFoot M b x → InFoot m a x := by
  obtain ⟨hv, ep, el⟩ := VecFormT.move h hn hw hal h0 h8 h16 hf
  exact ⟨hv, fun x hx => InFoot.of_eq ep el (fun y h1 h2 => hf y (.inl ⟨h1, h2⟩)) (VecFormT.buf_lt h) hx⟩

/-- **A `Vec<Form>` kept in place**, with its footprint. -/
theorem VecFormT.keep' {env : Env} {m M : MachineState} {a : Word} (h : VecFormT env m a)
    (hn : (env.next m).toNat ≤ (env.next M).toNat)
    (hh : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 24 → M.getMem b = m.getMem b)
    (hf : ∀ x : Word, InFoot m a x → M.getMem x = m.getMem x) :
    VecFormT env M a ∧ ∀ x, InFoot M a x → InFoot m a x := by
  have hlt := vecT_lt h.1
  have e8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (a + 16#64).toNat = a.toNat + 16 := toNat_add_ofNat (by omega)
  refine ⟨VecFormT.keep h hn hh hf, fun x hx => InFoot.of_eq ?_ ?_ (fun y h1 h2 => hf y (.inl ⟨h1, h2⟩))
    (VecFormT.buf_lt h) hx⟩
  · show M.getMem (a + 8#64) = m.getMem (a + 8#64)
    exact hh _ (by omega) (by omega)
  · show M.getMem (a + 16#64) = m.getMem (a + 16#64)
    exact hh _ (by omega) (by omega)

/-- The new `BusBlock`s after the `l` the vector had, at `P + 48 (l + i)`: each one's coordinates a `Vec<Form>` whose
    footprint lies in `[lo, H)`. -/
def DoneB (env : Env) (M : MachineState) (P : Word) (l j lo H : Nat) : Prop :=
  ∀ i, i < j → VecFormT env M (P + BitVec.ofNat 64 (48 * (l + i))) ∧
    FootIn M (P + BitVec.ofNat 64 (48 * (l + i))) lo H

/-- **`DoneB` is kept** by a memory agreeing on the new `BusBlock`s and on `[lo, H)`, `NEXT` no lower. -/
theorem DoneB.keep {env : Env} {M M' : MachineState} {P : Word} {l j lo H : Nat} (h : DoneB env M P l j lo H)
    (hP : P.toNat + 48 * (l + j) < 2 ^ 64) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ b : Word, (P.toNat + 48 * l ≤ b.toNat ∧ b.toNat < P.toNat + 48 * (l + j)) ∨ (lo ≤ b.toNat ∧ b.toNat < H) →
      M'.getMem b = M.getMem b) : DoneB env M' P l j lo H := by
  intro i hi
  obtain ⟨hv, hin⟩ := h i hi
  have e : (P + BitVec.ofNat 64 (48 * (l + i))).toNat = P.toNat + 48 * (l + i) := toNat_add_ofNat (by omega)
  obtain ⟨hv', hft⟩ := VecFormT.keep' hv hn (fun b h1 h2 => hk b (.inl ⟨by omega, by omega⟩))
    fun x hx => hk x (.inr (hin x hx))
  exact ⟨hv', fun x hx => hin x (hft x hx)⟩

/-- `DoneB`'s bound only grows. -/
theorem DoneB.mono {env : Env} {M : MachineState} {P : Word} {l j lo H H' : Nat} (h : DoneB env M P l j lo H)
    (hH : H ≤ H') : DoneB env M P l j lo H' := fun i hi =>
  ⟨(h i hi).1, fun x hx => by have := (h i hi).2 x hx; omega⟩

/-- **`BlocksT` is kept** by a memory agreeing on the `BusBlock`s' coordinates and their footprints, `NEXT` no
    lower. -/
theorem BlocksT.keep {env : Env} {M M' : MachineState} {P : Word} {n lo hi : Nat} (h : BlocksT env M P n lo hi)
    (hP : P.toNat + 48 * n < 2 ^ 64) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ b : Word, (P.toNat ≤ b.toNat ∧ b.toNat < P.toNat + 48 * n) →  M'.getMem b = M.getMem b)
    (hf : ∀ i, i < n → ∀ x : Word, InFoot M (P + BitVec.ofNat 64 (48 * i)) x → M'.getMem x = M.getMem x) :
    BlocksT env M' P n lo hi := by
  intro i hi'
  obtain ⟨hv, hap⟩ := h i hi'
  have e : (P + BitVec.ofNat 64 (48 * i)).toNat = P.toNat + 48 * i := toNat_add_ofNat (by omega)
  obtain ⟨hv', hft⟩ := VecFormT.keep' hv hn (fun b h1 h2 => hk b ⟨by omega, by omega⟩) (hf i hi')
  exact ⟨hv', fun x hx => hap x (hft x hx)⟩

/-! ## The frame -/

/-- The prologue's eleven saved words in `M`, at `top - 8` down to `top - 88`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25

/-- What every part keeps of memory: the slots, the frame with `out`, the static data, the code. -/
def MemOk (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (out : Word → Prop)
    (M : MachineState) : Prop :=
  Slots M top ret regs ∧ env.Frame top out m M ∧ env.Static M ∧ M.code = m.code

theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 144 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 88 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 88 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := es (top := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hsl
  exact ⟨(g _ 8 rfl (by omega) (by omega)).trans s1, (g _ 16 rfl (by omega) (by omega)).trans s2,
    (g _ 24 rfl (by omega) (by omega)).trans s3, (g _ 32 rfl (by omega) (by omega)).trans s4,
    (g _ 40 rfl (by omega) (by omega)).trans s5, (g _ 48 rfl (by omega) (by omega)).trans s6,
    (g _ 56 rfl (by omega) (by omega)).trans s7, (g _ 64 rfl (by omega) (by omega)).trans s8,
    (g _ 72 rfl (by omega) (by omega)).trans s9, (g _ 80 rfl (by omega) (by omega)).trans s10,
    (g _ 88 rfl (by omega) (by omega)).trans s11⟩

/-- **A store at `a` the frame allows**: into a block allocated since the entry, or into `out` below `NEXT` at entry;
    `MemOk`, `NEXT` and every other word kept. -/
theorem heap_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (h144 : 144 ≤ top.toNat) (hM : MemOk env m top ret regs out M)
    (ha : ((env.next m).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (env.next M).toNat) ∨
      (out a ∧ a.toNat + 8 ≤ (env.next m).toNat)) :
    MemOk env m top ret regs out (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ b : Word, b ≠ a → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have hnm := hF.1
  have hlt : a.toNat + 8 ≤ (env.next M).toNat := by rcases ha with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at hlt; omega
  refine ⟨⟨slots_keep h144 (fun b h1 _ => MachineState.getMem_setMem_ne fun e => by rw [e] at h1; omega) hsl, ?_,
    Tactic.static_store hS (.inl (by omega)), by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne,
    fun b hb => MachineState.getMem_setMem_ne hb⟩
  rcases ha with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Tactic.frame_fresh hF rfl h1 (by omega)
  · exact Tactic.frame_out hF h1 hne

/-- **A store into the frame below the slots** (`top - 144` to `top - 88`): `MemOk`, `NEXT` and every other word
    kept. -/
theorem frame_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (h144 : 144 ≤ top.toNat) (hM : MemOk env m top ret regs out M)
    (ha1 : top.toNat - 144 ≤ a.toNat) (ha2 : a.toNat + 8 ≤ top.toNat - 88) :
    MemOk env m top ret regs out (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ b : Word, b ≠ a → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  exact ⟨⟨slots_keep h144 (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_slot hF (by omega) (by omega), Env.static_setMem_stack hS (by omega),
    by rw [MachineState.code_setMem, hc]⟩, Env.next_setMem_stack (by omega),
    fun b hb => MachineState.getMem_setMem_ne hb⟩

/-- The prologue's eleven saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)).setMem (top + 18446744073709551536#64) (regs .x24)).setMem
    (top + 18446744073709551528#64) (regs .x25)

/-- A word off the frame is the entry's after the prologue. -/
theorem saved_get {m : MachineState} {top ret b : Word} {regs : Reg → Word} (h144 : 144 ≤ top.toNat)
    (hb : b.toNat + 8 ≤ top.toNat - 88 ∨ top.toNat ≤ b.toNat) : (saved m top ret regs).getMem b = m.getMem b := by
  have hne : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 88 → b ≠ top + c := fun c k hc h0 hk he => by
    have := congrArg BitVec.toNat he
    rw [es hc (by omega)] at this
    omega
  simp only [saved]
  rw [MachineState.getMem_setMem_ne (hne _ 88 rfl (by omega) le_rfl),
    MachineState.getMem_setMem_ne (hne _ 80 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 72 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 64 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 56 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 48 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 40 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 32 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 24 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 16 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 8 rfl (by omega) (by omega))]

/-- The prologue's stores: `MemOk` at the entry's frame. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (h144 : 144 ≤ top.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hS : env.Static m) :
    MemOk env m top ret regs Tactic.F (saved m top ret regs) := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 144 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => es hc (by omega)
  have e1 := g 18446744073709551608#64 8 rfl (by omega)
  have e2 := g 18446744073709551600#64 16 rfl (by omega)
  have e3 := g 18446744073709551592#64 24 rfl (by omega)
  have e4 := g 18446744073709551584#64 32 rfl (by omega)
  have e5 := g 18446744073709551576#64 40 rfl (by omega)
  have e6 := g 18446744073709551568#64 48 rfl (by omega)
  have e7 := g 18446744073709551560#64 56 rfl (by omega)
  have e8 := g 18446744073709551552#64 64 rfl (by omega)
  have e9 := g 18446744073709551544#64 72 rfl (by omega)
  have e10 := g 18446744073709551536#64 80 rfl (by omega)
  have e11 := g 18446744073709551528#64 88 rfl (by omega)
  refine ⟨?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at h'; omega)])
  · simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  · simp only [saved]
    repeat (first | refine Env.static_setMem_stack ?_ (by omega) | exact hS)

/-! ## The invariant -/

/-- The facts of the entry every part reads. -/
def Args (env : Env) (m : MachineState) (top : Word) (regs : Reg → Word) : Prop :=
  env.stackLimit.toNat + 144 ≤ top.toNat ∧ Windows env top m ∧ top.toNat % 16 = 0 ∧ regs .x2 = top ∧
    PreT env regs m

/-- **The buffer after `reserve`**: `P1` of capacity `C1`, a block below `N1` (or no capacity), with room for the new
    `BusBlock`s, the entry's buffer or one allocated since the entry. -/
def Buf (env : Env) (m : MachineState) (regs : Reg → Word) (P1 C1 : Word) (N1 : Nat) : Prop :=
  (C1.toNat = 0 ∨ (0x10000000 ≤ P1.toNat ∧ P1.toNat + 48 * C1.toNat ≤ N1 ∧ P1.toNat % 8 = 0)) ∧
    (vecLen m (regs .x10)).toNat + cnt regs m ≤ C1.toNat ∧ C1.toNat * 48 < 2 ^ 63 ∧ (env.next m).toNat ≤ N1 ∧
    ((P1 = vecPtr m (regs .x10) ∧ C1 = vecCap m (regs .x10)) ∨ (env.next m).toNat ≤ P1.toNat)

/-- What the loop keeps of memory with `j` new `BusBlock`s: `MemOk`, the header's capacity and pointer, the old
    `BusBlock`s at `P1` (their footprints apart from the buffer), the new ones (their footprints from `N1`). -/
def MInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (P1 C1 : Word) (N1 j : Nat)
    (M : MachineState) : Prop :=
  MemOk env m top ret regs (OutT regs m) M ∧ M.getMem (regs .x10) = C1 ∧ M.getMem (regs .x10 + 8#64) = P1 ∧
    N1 ≤ (env.next M).toNat ∧
    BlocksT env M P1 (vecLen m (regs .x10)).toNat P1.toNat (P1.toNat + 48 * C1.toNat) ∧
    DoneB env M P1 (vecLen m (regs .x10)).toNat j N1 (env.next M).toNat

/-- The header's facts: at or above the stack top, so apart from every block and slot. -/
theorem Args.hdr {env : Env} {m : MachineState} {top : Word} {regs : Reg → Word} (hA : Args env m top regs) :
    top.toNat ≤ (regs .x10).toNat ∧ (regs .x10).toNat + 24 ≤ 0xc0000000 := by
  obtain ⟨-, -, -, h2, -, hso, -⟩ := hA
  rw [← h2]; exact hso

/-! ## The return -/

/-- **The postcondition at the return**, from the invariant: the new length stored. -/
theorem exit_post {env : Env} {m M : MachineState} {top ret P1 C1 v : Word} {regs : Reg → Word} {N1 : Nat}
    (hA : Args env m top regs) (hB : Buf env m regs P1 C1 N1)
    (hv : v.toNat = (vecLen m (regs .x10)).toNat + cnt regs m)
    (hM : MInv env m top ret regs P1 C1 N1 (cnt regs m) M) {r : Reg → Word} :
    PostT env regs m r (M.setMem (regs .x10 + 16#64) v) ∧
      env.Frame top (OutT regs m) m (M.setMem (regs .x10 + 16#64) v) ∧
      env.Static (M.setMem (regs .x10 + 16#64) v) ∧
      BlocksT env (M.setMem (regs .x10 + 16#64) v) P1 ((vecLen m (regs .x10)).toNat + cnt regs m) P1.toNat
        (P1.toNat + 48 * C1.toNat) ∧ bufHi (M.setMem (regs .x10 + 16#64) v) (regs .x10) = P1.toNat + 48 * C1.toNat := by
  have hlay := env.layout
  obtain ⟨hstk, hW, -, -, hV, -⟩ := id hA
  obtain ⟨hhd1, hhd2⟩ := hA.hdr
  obtain ⟨⟨-, hF, hS, -⟩, c0, c8, hN1, hold, hnew⟩ := hM
  obtain ⟨hb1, hroom, hb48, hmN, hkf⟩ := hB
  have hnM := hF.2.1
  have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hn16 : regs .x10 + 16#64 ≠ env.nextAddr := fun e => by
    have := congrArg BitVec.toNat e; rw [e16] at this; omega
  have ne16 : ∀ b : Word, b.toNat < (env.next M).toNat →
      (M.setMem (regs .x10 + 16#64) v).getMem b = M.getMem b := fun b hb =>
    MachineState.getMem_setMem_ne fun e => by rw [e, e16] at hb; omega
  have hN : env.next (M.setMem (regs .x10 + 16#64) v) = env.next M := Tactic.next_setMem hn16
  have r0 : (M.setMem (regs .x10 + 16#64) v).getMem (regs .x10) = C1 := by
    rw [MachineState.getMem_setMem_ne fun e => by have := congrArg BitVec.toNat e; rw [e16] at this; omega, c0]
  have r8 : (M.setMem (regs .x10 + 16#64) v).getMem (regs .x10 + 8#64) = P1 := by
    rw [MachineState.getMem_setMem_ne fun e => by have := congrArg BitVec.toNat e; rw [e16, e8] at this; omega, c8]
  have ecap : vecCap (M.setMem (regs .x10 + 16#64) v) (regs .x10) = C1 := by rw [vecCap_eq, r0]
  have eptr : vecPtr (M.setMem (regs .x10 + 16#64) v) (regs .x10) = P1 := by rw [vecPtr_eq, r8]
  have elen : vecLen (M.setMem (regs .x10 + 16#64) v) (regs .x10) = v := by
    rw [vecLen_eq, MachineState.getMem_setMem_eq]
  have hBlk : BlocksT env (M.setMem (regs .x10 + 16#64) v) P1 ((vecLen m (regs .x10)).toNat + cnt regs m) P1.toNat
      (P1.toNat + 48 * C1.toNat) := by
    intro i hi
    have hC : 0 < C1.toNat := by omega
    obtain ⟨hP1, hP2, -⟩ := hb1.resolve_left (by omega)
    rcases Nat.lt_or_ge i (vecLen m (regs .x10)).toNat with hi' | hi'
    · obtain ⟨hv', hap⟩ := hold i hi'
      have e : (P1 + BitVec.ofNat 64 (48 * i)).toNat = P1.toNat + 48 * i := toNat_add_ofNat (by omega)
      obtain ⟨hv2, hft⟩ := VecFormT.keep' hv' (by rw [hN])
        (fun b h1 h2 => ne16 b (by omega)) fun x hx => ne16 x (VecFormT.foot_lt hv' hx)
      exact ⟨hv2, fun x hx => hap x (hft x hx)⟩
    · obtain ⟨hv', hin⟩ := hnew (i - (vecLen m (regs .x10)).toNat) (by omega)
      rw [Nat.add_sub_cancel' hi'] at hv' hin
      have e : (P1 + BitVec.ofNat 64 (48 * i)).toNat = P1.toNat + 48 * i := toNat_add_ofNat (by omega)
      obtain ⟨hv2, hft⟩ := VecFormT.keep' hv' (by rw [hN])
        (fun b h1 h2 => ne16 b (by omega)) fun x hx => ne16 x (VecFormT.foot_lt hv' hx)
      exact ⟨hv2, fun x hx => by have := hin x (hft x hx); omega⟩
  refine ⟨⟨⟨hV.1, ⟨hV.2.1.1, hV.2.1.2.1, ?_, ?_⟩, by rw [elen, ecap, hv]; exact hroom⟩, by rw [elen, hv], ?_, ?_⟩,
    Tactic.frame_out (SpecExtendFormT.frame_mono hF fun b h => h) (.inl (by
      unfold InRange; simp only [Layouts.Vec.byteSize]; rw [e16]; omega)) hn16,
    Tactic.static_store hS (.inr (by rw [e16]; omega)), hBlk, by unfold bufHi; rw [eptr, ecap]⟩
  · rw [rvCapAt_eq, rvPtrAt_eq, r0, r8]
    exact hb1.imp_right fun ⟨h1, h2, h3⟩ => ⟨h1, by unfold Env.Live; rw [hN]; omega, h3⟩
  · rw [rvCapAt_eq, r0]; exact hb48
  · unfold KeptOrFresh
    rw [eptr, ecap]
    rcases hkf with ⟨h1, h2⟩ | h1
    · exact .inl ⟨h1, h2⟩
    · exact .inr h1
  · rw [eptr, elen, hv]
    unfold bufHi
    rw [eptr, ecap]
    exact hBlk

/-- The registers the return reads: the stack pointer, the header, and the two saved registers it does not save. -/
def XRegs (top : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x10 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

set_option rv_sym.heap true in
/-- **The return**, from instruction 118: the new length stored at `a0 + 16`, the saved registers. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {P1 C1 : Word} {N1 : Nat}
    (hB : Buf env m regs P1 C1 N1) :
    ∀ R M, XRegs top regs R → (R .x19).toNat = (vecLen m (regs .x10)).toNat + cnt regs m →
      MInv env m top ret regs P1 C1 N1 (cnt regs m) M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR h19 hM
  have hlay := env.layout
  obtain ⟨hPost, hF', hS', hBlk, hHi⟩ := exit_post (r := fun _ => 0#64) hA hB h19 hM
  obtain ⟨-, hroom, -, -, hkf⟩ := id hB
  obtain ⟨hstk, hW, h16, -⟩ := id hA
  obtain ⟨hhd1, hhd2⟩ := hA.hdr
  obtain ⟨⟨hsl, -, -, hc0⟩, c0, c8, -⟩ := hM
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩ := hsl
  have := hW.nextAddr_ge
  have w16 : inWindow (regs .x10 + 16#64) 8 = true := by
    rw [inWindow_iff, toNat_add_ofNat (by omega)]; omega
  rv_introT hR
  rv_symT hp with [_hL]
  all_goals first
    | (rw [c8, c0]; rw [vecCap_eq] at hkf; exact hkf)
    | (rw [c8, hHi, h19]; exact hBlk)

/-! ## The loop -/

/-- The buffer's numbers when there is a `BusBlock` to push. -/
theorem Buf.pos {env : Env} {m : MachineState} {regs : Reg → Word} {P1 C1 : Word} {N1 : Nat}
    (hB : Buf env m regs P1 C1 N1) (hn : 0 < cnt regs m) :
    0x10000000 ≤ P1.toNat ∧ P1.toNat + 48 * C1.toNat ≤ N1 ∧ P1.toNat % 8 = 0 :=
  hB.1.resolve_left (by have := hB.2.1; omega)

/-- The entry's buffer, when it has capacity: below `NEXT`. -/
theorem Args.buf {env : Env} {m : MachineState} {top : Word} {regs : Reg → Word} (hA : Args env m top regs) :
    (vecCap m (regs .x10)).toNat = 0 ∨ (0x10000000 ≤ (vecPtr m (regs .x10)).toNat ∧
      (vecPtr m (regs .x10)).toNat + 48 * (vecCap m (regs .x10)).toNat ≤ (env.next m).toNat) := by
  obtain ⟨-, -, -, -, ⟨-, ⟨-, -, hB, -⟩, -⟩, -⟩ := hA
  rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq] at hB
  rcases hB with h0 | ⟨h1, h2, -⟩
  · exact .inl h0
  · unfold Env.Live at h2; exact .inr ⟨h1, by omega⟩

/-- The source's headers lie below the stack window's end. -/
theorem Args.src_lt {env : Env} {m : MachineState} {top : Word} {regs : Reg → Word} (hA : Args env m top regs)
    (hn : 0 < cnt regs m) : (m.getMem (regs .x11)).toNat + 24 * cnt regs m ≤ 0xc0000000 := by
  obtain ⟨-, hW, -, -, -, -, -, -, -, -, h1, h2, -, hsrc, -⟩ := hA
  have hlt : (m.getMem (regs .x11)).toNat + 24 * cnt regs m ≤ (m.getMem (regs .x11 + 8#64)).toNat := by
    unfold cnt; omega
  have := (m.getMem (regs .x11 + 8#64)).isLt
  have hw := (hsrc (cnt regs m - 1) (by omega)).1.1.1
  have e : (m.getMem (regs .x11) + BitVec.ofNat 64 (24 * (cnt regs m - 1))).toNat =
      (m.getMem (regs .x11)).toNat + 24 * (cnt regs m - 1) := toNat_add_ofNat (by omega)
  unfold InWin at hw
  simp only [Layouts.Vec.byteSize, e] at hw
  have := hW.heapEnd_le
  rcases hw with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

/-- **A new `BusBlock`'s six stores** at `A = P1 + 48 (l + j)`: the clone's header copied from the frame's slot `S`,
    then three words; `MemOk` and `NEXT` kept, `j + 1` new `BusBlock`s. -/
theorem blk_mem {env : Env} {m M : MachineState} {top ret A S P1 C1 u w z : Word} {regs : Reg → Word} {N1 j : Nat}
    (hA : Args env m top regs) (h144 : 144 ≤ top.toNat) (hB : Buf env m regs P1 C1 N1) (hj : j < cnt regs m)
    (hM : MInv env m top ret regs P1 C1 N1 j M) (hS : VecFormT env M S)
    (hSf : FootIn M S N1 (env.next M).toNat)
    (hAeq : A = P1 + BitVec.ofNat 64 (48 * ((vecLen m (regs .x10)).toNat + j))) :
    MInv env m top ret regs P1 C1 N1 (j + 1) ((((((M.setMem A (M.getMem S)).setMem (A + 8#64)
        (M.getMem (S + 8#64))).setMem (A + 16#64) (M.getMem (S + 16#64))).setMem (A + 24#64) u).setMem
        (A + 32#64) w).setMem (A + 40#64) z) ∧
      env.next ((((((M.setMem A (M.getMem S)).setMem (A + 8#64) (M.getMem (S + 8#64))).setMem (A + 16#64)
        (M.getMem (S + 16#64))).setMem (A + 24#64) u).setMem (A + 32#64) w).setMem (A + 40#64) z) = env.next M := by
  have hlay := env.layout
  have hstk := hA.1
  obtain ⟨hhd1, hhd2⟩ := hA.hdr
  obtain ⟨hP1, hP2, hP8⟩ := hB.pos (by omega)
  obtain ⟨-, hroom, -, hmN, hkf⟩ := hB
  obtain ⟨hMo, c0, c8, hN1, hold, hdone⟩ := hM
  have hnM := hMo.2.1.2.1
  have hnm := hMo.2.1.1
  have hbuf0 := hA.buf
  have eA : A.toNat = P1.toNat + 48 * ((vecLen m (regs .x10)).toNat + j) := by
    rw [hAeq]; exact toNat_add_ofNat (by omega)
  have hok : ∀ o : Nat, o < 48 → o % 8 = 0 → ((env.next m).toNat ≤ (A + BitVec.ofNat 64 o).toNat ∧
      (A + BitVec.ofNat 64 o).toNat + 8 ≤ (env.next M).toNat) ∨
      (OutT regs m (A + BitVec.ofNat 64 o) ∧ (A + BitVec.ofNat 64 o).toNat + 8 ≤ (env.next m).toNat) :=
    fun o ho _ => by
      have e : (A + BitVec.ofNat 64 o).toNat = A.toNat + o := toNat_add_ofNat (by omega)
      rcases hkf with ⟨h1, h2⟩ | h1
      · have hC : 0 < (vecCap m (regs .x10)).toNat := by rw [← h2]; omega
        rcases hbuf0 with h0 | ⟨-, h3⟩
        · omega
        · subst h1 h2
          exact .inr ⟨.inr ⟨by rw [e]; omega, by unfold bufHi; rw [e]; omega⟩, by rw [e]; omega⟩
      · exact .inl ⟨by rw [e]; omega, by rw [e]; omega⟩
  have g8 : A + 8#64 = A + BitVec.ofNat 64 8 := rfl
  have g16 : A + 16#64 = A + BitVec.ofNat 64 16 := rfl
  have g24 : A + 24#64 = A + BitVec.ofNat 64 24 := rfl
  have g32 : A + 32#64 = A + BitVec.ofNat 64 32 := rfl
  have g40 : A + 40#64 = A + BitVec.ofNat 64 40 := rfl
  have g0 : A = A + BitVec.ofNat 64 0 := by simp
  have hstk' := hstk
  obtain ⟨m1, n1, k1⟩ := heap_store (a := A) (v := M.getMem S) hstk h144 hMo
    (by rw [g0]; exact hok 0 (by omega) rfl)
  obtain ⟨m2, n2, k2⟩ := heap_store (a := A + 8#64) (v := M.getMem (S + 8#64)) hstk h144 m1
    (by rw [g8, n1]; exact hok 8 (by omega) rfl)
  obtain ⟨m3, n3, k3⟩ := heap_store (a := A + 16#64) (v := M.getMem (S + 16#64)) hstk h144 m2
    (by rw [g16, n2, n1]; exact hok 16 (by omega) rfl)
  obtain ⟨m4, n4, k4⟩ := heap_store (a := A + 24#64) (v := u) hstk h144 m3
    (by rw [g24, n3, n2, n1]; exact hok 24 (by omega) rfl)
  obtain ⟨m5, n5, k5⟩ := heap_store (a := A + 32#64) (v := w) hstk h144 m4
    (by rw [g32, n4, n3, n2, n1]; exact hok 32 (by omega) rfl)
  obtain ⟨m6, n6, k6⟩ := heap_store (a := A + 40#64) (v := z) hstk h144 m5
    (by rw [g40, n5, n4, n3, n2, n1]; exact hok 40 (by omega) rfl)
  have hN : env.next ((((((M.setMem A (M.getMem S)).setMem (A + 8#64) (M.getMem (S + 8#64))).setMem (A + 16#64)
      (M.getMem (S + 16#64))).setMem (A + 24#64) u).setMem (A + 32#64) w).setMem (A + 40#64) z) = env.next M := by
    rw [n6, n5, n4, n3, n2, n1]
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  have e24 : (A + 24#64).toNat = A.toNat + 24 := toNat_add_ofNat (by omega)
  have e32 : (A + 32#64).toNat = A.toNat + 32 := toNat_add_ofNat (by omega)
  have e40 : (A + 40#64).toNat = A.toNat + 40 := toNat_add_ofNat (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hk : ∀ b : Word, (b.toNat < A.toNat ∨ A.toNat + 48 ≤ b.toNat) →
      ((((((M.setMem A (M.getMem S)).setMem (A + 8#64) (M.getMem (S + 8#64))).setMem (A + 16#64)
        (M.getMem (S + 16#64))).setMem (A + 24#64) u).setMem (A + 32#64) w).setMem (A + 40#64) z).getMem b =
        M.getMem b := fun b hb => by
    rw [k6 b (ne _ _ (by omega)), k5 b (ne _ _ (by omega)), k4 b (ne _ _ (by omega)), k3 b (ne _ _ (by omega)),
      k2 b (ne _ _ (by omega)), k1 b (ne _ _ (by omega))]
  have r0 : ((((((M.setMem A (M.getMem S)).setMem (A + 8#64) (M.getMem (S + 8#64))).setMem (A + 16#64)
      (M.getMem (S + 16#64))).setMem (A + 24#64) u).setMem (A + 32#64) w).setMem (A + 40#64) z).getMem A =
      M.getMem S := by
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), k3 _ (ne _ _ (by omega)),
      k2 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r8 : ((((((M.setMem A (M.getMem S)).setMem (A + 8#64) (M.getMem (S + 8#64))).setMem (A + 16#64)
      (M.getMem (S + 16#64))).setMem (A + 24#64) u).setMem (A + 32#64) w).setMem (A + 40#64) z).getMem (A + 8#64) =
      M.getMem (S + 8#64) := by
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), k3 _ (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r16 : ((((((M.setMem A (M.getMem S)).setMem (A + 8#64) (M.getMem (S + 8#64))).setMem (A + 16#64)
      (M.getMem (S + 16#64))).setMem (A + 24#64) u).setMem (A + 32#64) w).setMem (A + 40#64) z).getMem
      (A + 16#64) = M.getMem (S + 16#64) := by
    rw [k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have hSft : ∀ x : Word, InFoot M S x → N1 ≤ x.toNat ∧ x.toNat < (env.next M).toNat := hSf
  have ea8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  obtain ⟨hvA, hftA⟩ := VecFormT.move' hS (by rw [hN]) (.inl ⟨by omega, by omega⟩) (by omega) r0 r8 r16
    fun x hx => hk x (by have := hSft x hx; omega)
  refine ⟨⟨m6, by rw [hk _ (by omega)]; exact c0, by rw [hk _ (by omega)]; exact c8, by rw [hN]; exact hN1,
    BlocksT.keep hold (by omega) (by rw [hN]) (fun b hb => hk b (.inl (by obtain ⟨h1, h2⟩ := hb; omega)))
      fun i hi x hx => hk x ?_, fun i hi => ?_⟩,
    hN⟩
  · rcases (hold i hi).2 x hx with h | h <;> omega
  · rw [hN]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · obtain ⟨hv, hin⟩ := hdone i hi
      have e : (P1 + BitVec.ofNat 64 (48 * ((vecLen m (regs .x10)).toNat + i))).toNat =
          P1.toNat + 48 * ((vecLen m (regs .x10)).toNat + i) := toNat_add_ofNat (by omega)
      obtain ⟨hv', hft⟩ := VecFormT.keep' hv (by rw [hN]) (fun b h1 h2 => hk b (by omega))
        fun x hx => hk x (by have := hin x hx; omega)
      exact ⟨hv', fun x hx => hin x (hft x hx)⟩
    · rw [hi, ← hAeq]
      exact ⟨hvA, fun x hx => hSft x (hftA x hx)⟩

/-- The registers the loop keeps: the stack pointer, the header, the closure's three captures, the end, the new
    length, and the two saved registers it does not save. -/
def LRegs (top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x8 = regs .x10 ∧ R .x9 = m.getMem (regs .x11 + 32#64) ∧
    R .x20 = m.getMem (regs .x11 + 16#64) ∧ R .x21 = m.getMem (regs .x11 + 24#64) ∧
    (R .x18).toNat = (m.getMem (regs .x11)).toNat + 16 + 24 * cnt regs m ∧
    (R .x19).toNat = (vecLen m (regs .x10)).toNat + cnt regs m ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The loop's head (instruction 78) with `k + 1` `BusBlock`s left, from source `j`. -/
def LInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (P1 C1 : Word) (N1 k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  LRegs top regs m R ∧ ∃ j, j + k + 1 = cnt regs m ∧
    (R .x22).toNat = (m.getMem (regs .x11)).toNat + 16 + 24 * j ∧
    (R .x23).toNat = P1.toNat + 48 * ((vecLen m (regs .x10)).toNat + j) ∧ MInv env m top ret regs P1 C1 N1 j M

set_option rv_sym.heap true in
/-- **After the clone** (instruction 92): the new `BusBlock` stored, then the next source (78) or the return. -/
theorem body {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {P1 C1 : Word} {N1 j k : Nat}
    (hB : Buf env m regs P1 C1 N1)
    (h78 : 0 < k → ∀ R M, LInv env m top ret regs P1 C1 N1 (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, LRegs top regs m R → j + k + 1 = cnt regs m →
      (R .x22).toNat = (m.getMem (regs .x11)).toNat + 16 + 24 * j →
      (R .x23).toNat = P1.toNat + 48 * ((vecLen m (regs .x10)).toNat + j) → MInv env m top ret regs P1 C1 N1 j M →
      VecFormT env M (top + 18446744073709551480#64) →
      FootIn M (top + 18446744073709551480#64) N1 (env.next M).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 92, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hjk h22 h23 hM hS hSf
  have hlay := env.layout
  have hex := exit hp hL hk hA hB
  obtain ⟨hstk, hW, h16, -⟩ := id hA
  have := hW.nextAddr_ge
  have h144 : 144 ≤ top.toNat := by omega
  obtain ⟨hP1, hP2, hP8⟩ := hB.pos (by omega)
  have hroom := hB.2.1
  have hAw : R .x23 = P1 + BitVec.ofNat 64 (48 * ((vecLen m (regs .x10)).toNat + j)) :=
    BitVec.eq_of_toNat_eq (by rw [h23, toNat_add_ofNat (by omega)])
  have e136 := es (top := top) (c := 18446744073709551480#64) (k := 136) rfl (by omega)
  have hs8 : top + 18446744073709551480#64 + 8#64 = top + 18446744073709551488#64 := by rw [BitVec.add_assoc]; rfl
  have hs16 : top + 18446744073709551480#64 + 16#64 = top + 18446744073709551496#64 := by
    rw [BitVec.add_assoc]; rfl
  have hcM : M.code = m.code := hM.1.2.2.2
  have hnM := hM.1.2.1.2.1
  have hN1 := hM.2.2.2.1
  have hsl := hA.src_lt (by omega)
  have e22 : (R .x22 + 24#64).toNat = (m.getMem (regs .x11)).toNat + 16 + 24 * (j + 1) := by
    rw [toNat_add_ofNat (by omega)]; omega
  obtain ⟨hR1, hR2, hR3, hR4, hR5, hR18, hR19, hR26, hR27⟩ := id hR
  have hAe : (R .x23).toNat + 48 ≤ env.heapEnd.toNat := by omega
  have hA0 : 0x10000000 ≤ (R .x23).toNat := by omega
  have w8 : (R .x23 + 8#64).toNat = (R .x23).toNat + 8 := toNat_add_ofNat (by omega)
  have w16 : (R .x23 + 16#64).toNat = (R .x23).toNat + 16 := toNat_add_ofNat (by omega)
  have w24 : (R .x23 + 24#64).toNat = (R .x23).toNat + 24 := toNat_add_ofNat (by omega)
  have w32 : (R .x23 + 32#64).toNat = (R .x23).toNat + 32 := toNat_add_ofNat (by omega)
  have w40 : (R .x23 + 40#64).toNat = (R .x23).toNat + 40 := toNat_add_ofNat (by omega)
  rv_introT hR
  obtain ⟨hM6, -⟩ := blk_mem (u := R .x24) (w := R .x25)
    (z := M.getMem (m.getMem (regs .x11 + 32#64) + 72#64)) hA h144 hB (by omega) hM hS hSf hAw
  rw [hs8, hs16] at hM6
  rv_symT hp stop [78, 118] with [hL]
  · have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [e22, hR18]; omega)) hc
      · exact h
    clear hc
    exact h78 hk0 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hR18, hR19, rfl, rfl⟩, j + 1, by omega, e22,
      by show (R .x23 + 48#64).toNat = _; rw [toNat_add_ofNat (by omega), h23]; omega, hM6⟩
  · have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [e22, hR18] at this; omega
    clear hc
    have hj1 : j + 1 = cnt regs m := by omega
    rw [hj1] at hM6
    exact hex _ _ ⟨rfl, rfl, rfl, rfl⟩ hR19 hM6

/-- **A call writing at most the clone's slot** (`top - 136` to `top - 112`): the invariant kept, every word below
    `NEXT` before the call or at or above the stack pointer and apart from the slot kept. -/
theorem call_mem {env : Env} {m M M' : MachineState} {top ret P1 C1 : Word} {regs : Reg → Word} {N1 j : Nat}
    {out : Word → Prop} (hA : Args env m top regs) (h144 : 144 ≤ top.toNat) (hB : Buf env m regs P1 C1 N1)
    (hj : j < cnt regs m) (hM : MInv env m top ret regs P1 C1 N1 j M)
    (hF : env.Frame (top + 18446744073709551472#64) out M M') (hSt : env.Static M') (hc : M'.code = M.code)
    (hout : ∀ b, out b → top.toNat - 136 ≤ b.toNat ∧ b.toNat < top.toNat - 112)
    (hkeep : ∀ a : Word, a.toNat < (env.next M).toNat ∨ (top + 18446744073709551472#64).toNat ≤ a.toNat → ¬ out a →
      M'.getMem a = M.getMem a) :
    MInv env m top ret regs P1 C1 N1 j M' ∧ (env.next M).toNat ≤ (env.next M').toNat := by
  have hlay := env.layout
  have hstk := hA.1
  obtain ⟨hhd1, hhd2⟩ := hA.hdr
  obtain ⟨⟨hsl, hF0, -, hc0⟩, c0, c8, hN1, hold, hdone⟩ := hM
  have hnM := hF0.2.1
  have e144 := es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have hk : ∀ a : Word, (a.toNat < (env.next M).toNat ∨ top.toNat - 144 ≤ a.toNat) →
      (a.toNat < top.toNat - 136 ∨ top.toNat - 112 ≤ a.toNat) → M'.getMem a = M.getMem a := fun a h1 h2 =>
    hkeep a (by rw [e144]; exact h1) fun ho => by have := hout a ho; omega
  have hn := hF.1
  have ea8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  obtain ⟨hP1, hP2, -⟩ := hB.pos (by omega)
  have hroom := hB.2.1
  have hlow : ∀ x : Word, x.toNat < (env.next M).toNat → M'.getMem x = M.getMem x := fun x hx =>
    hk x (.inl hx) (.inl (by omega))
  refine ⟨⟨⟨slots_keep h144 (fun a h1 _ => hk a (.inr (by omega)) (.inr (by omega))) hsl,
    hF0.trans hF (by rw [e144]; omega) fun b hb => Or.inl (by have := hout b hb; omega), hSt, hc.trans hc0⟩,
    by rw [hk _ (.inr (by omega)) (.inr (by omega))]; exact c0,
    by rw [hk _ (.inr (by omega)) (.inr (by omega))]; exact c8, by omega,
    BlocksT.keep hold ?_ hn (fun b hb => hlow b ?_) fun i hi x hx => hlow x (VecFormT.foot_lt (hold i hi).1 hx),
    (DoneB.keep hdone ?_ hn fun b hb => hlow b ?_).mono hn⟩, hn⟩
  · omega
  · omega
  · omega
  · omega

/-- **The source's `Vec<Form>` `j`** in a memory the frame keeps: a `Vec<Form>` still. -/
theorem Args.srcM {env : Env} {m M : MachineState} {top : Word} {regs : Reg → Word} (hA : Args env m top regs)
    {j : Nat} (hj : j < cnt regs m) (hF : env.Frame top (OutT regs m) m M) :
    VecFormT env M (m.getMem (regs .x11) + BitVec.ofNat 64 (24 * j)) ∧
      (m.getMem (regs .x11) + BitVec.ofNat 64 (24 * j)).toNat = (m.getMem (regs .x11)).toNat + 24 * j := by
  have hlay := env.layout
  obtain ⟨hstk, hW, -, h2, -, -, -, -, -, -, h1, h11, hsr, hsrc, -⟩ := id hA
  obtain ⟨hhd1, hhd2⟩ := hA.hdr
  have hsl := hA.src_lt (by omega)
  obtain ⟨hoff, hnx, hsp, hap⟩ := hsr.resolve_left (by omega)
  obtain ⟨hv, hfa⟩ := hsrc j hj
  have e : (m.getMem (regs .x11) + BitVec.ofNat 64 (24 * j)).toNat = (m.getMem (regs .x11)).toNat + 24 * j :=
    toNat_add_ofNat (by omega)
  have hw := hv.1.1
  unfold InWin at hw
  simp only [Layouts.Vec.byteSize, e] at hw
  unfold OffStack at hoff
  rw [h2] at hoff
  unfold Apart at hap
  have hbuf := hA.buf
  have hnm := hF.1
  have hnM := hF.2.1
  refine ⟨(VecFormT.keep' hv hnm (fun b h3 h4 => keepF hF (by omega) ?_ ?_) fun x hx => keepF hF (by omega) ?_ ?_).1,
    e⟩
  · rw [e] at h3 h4
    rcases hw with ⟨h', h⟩ | ⟨h', h⟩ <;> rcases hnx with h5 | h5 <;> rcases hoff with h6 | h6 <;> omega
  · rw [e] at h3 h4
    rintro (h | ⟨h5, h6⟩)
    · unfold InRange at h; simp only [Layouts.Vec.byteSize] at h; omega
    · unfold bufHi at *; rcases hsp with h7 | h7 <;> omega
  · exact .inl (VecFormT.foot_lt hv hx)
  · have hlt := VecFormT.foot_lt hv hx
    rintro (h | ⟨h5, h6⟩)
    · unfold InRange at h; simp only [Layouts.Vec.byteSize] at h; have := hW.heapEnd_le; omega
    · rcases hfa x hx with h7 | h7 <;> omega

set_option rv_sym.heap true in
/-- **The loop**, from its head (instruction 78) to the return: each source `Vec<Form>` cloned and its `BusBlock`
    stored. -/
theorem loop {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hnC : 144 + needC ≤ need) (hcl : CloneFormsFreshT.SpecT env p L.clone.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) {P1 C1 : Word} {N1 : Nat}
    (hB : Buf env m regs P1 C1 N1) :
    ∀ k R M, LInv env m top ret regs P1 C1 N1 k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env m top ret regs P1 C1 N1) fun k R M hI ih => ?_
  have hlay := env.layout
  have h78 : 0 < k → ∀ R M, LInv env m top ret regs P1 C1 N1 (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := fun hk0 R' M' h => ih (k - 1) R' M'
    (by omega) h
  obtain ⟨hR, j, hjk, h22, h23, hM⟩ := hI
  obtain ⟨hstk, hW, h16, -, -, -, -, -, -, -, -, -, -, -, w20, a20, w21, a21, w9, a9⟩ := id hA
  have := hW.nextAddr_ge
  have h144 : 144 ≤ top.toNat := by omega
  have hsl := hA.src_lt (by omega)
  have hbd := body hp hL hk hA hB h78 (j := j)
  obtain ⟨hs, es'⟩ := hA.srcM (j := j) (by omega) hM.1.2.1
  have e16 : R .x22 = m.getMem (regs .x11) + BitVec.ofNat 64 (24 * j) + 16#64 :=
    BitVec.eq_of_toNat_eq (by rw [h22, toNat_add_ofNat (by omega), es']; omega)
  have e8 : R .x22 + 18446744073709551608#64 = m.getMem (regs .x11) + BitVec.ofNat 64 (24 * j) + 8#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, h22, toNat_add_ofNat (by omega), es']
    simp only [BitVec.toNat_ofNat]
    omega
  have hBt : BufT env M (M.getMem (R .x22)) (M.getMem (R .x22 + 18446744073709551608#64)) 24 := by
    rw [e8, e16]; exact (vecT_buf hs.1).1
  have hFt : FormsT env M (M.getMem (R .x22 + 18446744073709551608#64)) (M.getMem (R .x22)).toNat := by
    rw [e8, e16]; exact hs.2
  have hcM : M.code = m.code := hM.1.2.2.2
  have hSt : env.Static M := hM.1.2.2.1
  have hnM := hM.1.2.1.2.1
  have hsw := hs.1.1
  have hsa : (m.getMem (regs .x11) + BitVec.ofNat 64 (24 * j)).toNat % 8 = 0 := hs.1.2.1.2.1
  unfold InWin at hsw
  simp only [Layouts.Vec.byteSize] at hsw
  have hW1 := hW.heapEnd_le
  have ws8 : inWindow (R .x22 + 18446744073709551608#64) 8 = true ∧
      (R .x22 + 18446744073709551608#64).toNat % 8 = 0 := by
    rw [e8, inWindow_iff, toNat_add_ofNat (by omega)]; omega
  have ws16 : inWindow (R .x22) 8 = true ∧ (R .x22).toNat % 8 = 0 := by
    rw [e16, inWindow_iff, toNat_add_ofNat (by omega)]; omega
  obtain ⟨ws8a, ws8b⟩ := ws8
  obtain ⟨ws16a, ws16b⟩ := ws16
  clear hsw hsa
  have hR' := hR
  obtain ⟨hR1, hR2, hR3, hR4, hR5, hR18, hR19, hR26, hR27⟩ := hR'
  clear hs
  rv_introT hR
  have hN1 := hM.2.2.2.1
  rv_symT hp stop [92] with [hL] using [hcl]
  · exact ws8a
  · exact ws16a
  · exact hFt
  obtain ⟨hM1, hn1⟩ := call_mem hA h144 hB (by omega) hM hret1_14 hret1_15 hret1_27 (fun b hb => by
    obtain ⟨h1, h2⟩ := hb
    have e136 := es (top := top) (c := 18446744073709551480#64) (k := 136) rfl (by omega)
    change (top + 18446744073709551480#64).toNat ≤ b.toNat at h1
    change b.toNat < (top + 18446744073709551480#64).toNat + 24 at h2
    omega) keep1_2
  have hv : VecFormT env m1 (top + 18446744073709551480#64) :=
    ⟨⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩, by rw [hret1_22]; exact hret1_24⟩
  have hfoot : FootIn m1 (top + 18446744073709551480#64) N1 (env.next m1).toNat := by
    intro x hx
    rcases hx with ⟨h1, h2⟩ | ⟨i', hi', h1, h2⟩
    · rw [hret1_22] at h2
      rcases hret1_23 with h0 | ⟨h3, h4⟩
      · omega
      · omega
    · rw [hret1_22] at hi'
      have := hret1_25 i' hi'; omega
  exact hbd _ _ ⟨rfl, rfl, rfl, rfl, rfl, hR18, hR19, rfl, rfl⟩ hjk h22 h23 hM1 hv hfoot

/-- **A doubleword moved by a grow**: the new block at `P1` holds the old block's bytes at `P`. -/
theorem word_of_grown {ms m1 : MachineState} {P P1 : Word} {C o : Nat}
    (hb : ∀ k, k < C * 48 → m1.getByte (P1 + BitVec.ofNat 64 k) = ms.getByte (P + BitVec.ofNat 64 k))
    (hP8 : P.toNat % 8 = 0) (hP18 : P1.toNat % 8 = 0) (hP : P.toNat + C * 48 < 2 ^ 64)
    (hP1 : P1.toNat + C * 48 < 2 ^ 64) (ho : o + 8 ≤ C * 48) (ho8 : o % 8 = 0) :
    m1.getMem (P1 + BitVec.ofNat 64 o) = ms.getMem (P + BitVec.ofNat 64 o) := by
  have e : (P + BitVec.ofNat 64 o).toNat = P.toNat + o := toNat_add_ofNat (by omega)
  have e' : (P1 + BitVec.ofNat 64 o).toNat = P1.toNat + o := toNat_add_ofNat (by omega)
  refine Transcript.getMem_of_bytes (by omega) (by omega) fun k hk => ?_
  have := hb (o + k) (by omega)
  rwa [BitVec.ofNat_add, ← BitVec.add_assoc, ← BitVec.add_assoc] at this

/-! ## The entry -/

/-- The source's count, as the code computes it: `((end - begin) >> 3) * (3⁻¹ mod 2^64)`. -/
theorem cnt_toNat {regs : Reg → Word} {m : MachineState}
    (h1 : (m.getMem (regs .x11)).toNat ≤ (m.getMem (regs .x11 + 8#64)).toNat)
    (h2 : ((m.getMem (regs .x11 + 8#64)).toNat - (m.getMem (regs .x11)).toNat) % 24 = 0) :
    ((m.getMem (regs .x11 + 8#64) - m.getMem (regs .x11)) >>> 3 * 12297829382473034411#64).toNat = cnt regs m := by
  have e : (m.getMem (regs .x11 + 8#64) - m.getMem (regs .x11)).toNat =
      (m.getMem (regs .x11 + 8#64)).toNat - (m.getMem (regs .x11)).toNat := BitVec.toNat_sub_of_le (BitVec.le_def.2 h1)
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e]
  have := (m.getMem (regs .x11 + 8#64)).isLt
  simp only [BitVec.toNat_ofNat]
  unfold cnt
  omega

/-- **After `reserve`**: the invariant with no new `BusBlock`, the buffer `P1` of capacity `C1` (the entry's when it
    had room, a fresh one holding the old `BusBlock`s' words otherwise), and every word at or above the stack top but
    the header's the entry's. -/
theorem after_reserve {env : Env} {m m1 : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hA : Args env m top regs) (h144 : 144 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m)
    (hF1 : env.Frame (top + 18446744073709551472#64) out (saved m top ret regs) m1) (hS1 : env.Static m1)
    (hc1 : m1.code = (saved m top ret regs).code)
    (hout : ∀ b, out b → b = rvCapAt (regs .x10) ∨ b = rvPtrAt (regs .x10))
    (hV1 : VecT env m1 (regs .x10) 48)
    (hlen : vecLen m1 (regs .x10) = vecLen (saved m top ret regs) (regs .x10))
    (hkeep : cnt regs m ≤ (vecCap (saved m top ret regs) (regs .x10)).toNat -
        (vecLen (saved m top ret regs) (regs .x10)).toNat →
      vecCap m1 (regs .x10) = vecCap (saved m top ret regs) (regs .x10) ∧
        vecPtr m1 (regs .x10) = vecPtr (saved m top ret regs) (regs .x10))
    (hgrow : ¬ cnt regs m ≤ (vecCap (saved m top ret regs) (regs .x10)).toNat -
        (vecLen (saved m top ret regs) (regs .x10)).toNat →
      Grown env (saved m top ret regs) m1 (regs .x10)
        ((vecLen (saved m top ret regs) (regs .x10)).toNat + cnt regs m) 48) :
    MInv env m top ret regs (m1.getMem (regs .x10 + 8#64)) (m1.getMem (regs .x10)) (env.next m1).toNat 0 m1 ∧
      Buf env m regs (m1.getMem (regs .x10 + 8#64)) (m1.getMem (regs .x10)) (env.next m1).toNat ∧
      (∀ b : Word, top.toNat ≤ b.toNat → ¬ InRange (regs .x10) 24 b → m1.getMem b = m.getMem b) ∧
      m1.getMem (regs .x10 + 16#64) = vecLen m (regs .x10) := by
  have hlay := env.layout
  obtain ⟨hstk, hW, -, h2, hV, -, hold, -⟩ := id hA
  obtain ⟨hhd1, hhd2⟩ := hA.hdr
  obtain ⟨hsl, hF0, -, hc0⟩ := saved_ok (ret := ret) (regs := regs) hstk h144 hnx hS
  have e144 := es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have hn1 := hF1.1
  have hn0 := hF0.1
  have hn2 := hF1.2.1
  have hW1 := hW.heapEnd_le
  have := hW.nextAddr_ge
  have ea8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have ea16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hsN : env.next (saved m top ret regs) = env.next m := by
    show (saved m top ret regs).getMem env.nextAddr = m.getMem env.nextAddr
    exact saved_get h144 (.inl (by omega))
  -- what `reserve` keeps: every word but the header's two below `NEXT` or at or above the stack top
  have hk' : ∀ a : Word, (a.toNat < (env.next m).toNat ∨ top.toNat ≤ a.toNat) → ¬ out a →
      m1.getMem a = m.getMem a := fun a h1 ho => by
    have e1 : m1.getMem a = (saved m top ret regs).getMem a := hF1.2.2 a fun hw => by
      rcases hw with hw | hw | hw | hw
      · have := hw.2; rw [e144] at this; omega
      · rw [hsN] at hw; omega
      · rw [hw] at h1; omega
      · exact ho hw
    rw [e1]
    exact saved_get h144 (by omega)
  have kLow : ∀ a : Word, a.toNat < (env.next m).toNat → m1.getMem a = m.getMem a := fun a ha =>
    hk' a (.inl ha) fun ho => by
      rcases hout a ho with rfl | rfl
      · rw [rvCapAt_eq] at ha; omega
      · rw [rvPtrAt_eq, ea8] at ha; omega
  have kTop : ∀ b : Word, top.toNat ≤ b.toNat → ¬ InRange (regs .x10) 24 b → m1.getMem b = m.getMem b :=
    fun b hb hr => hk' b (.inr hb) fun ho => hr (by
      rcases hout b ho with rfl | rfl
      · unfold InRange; rw [rvCapAt_eq]; omega
      · unfold InRange; rw [rvPtrAt_eq, ea8]; omega)
  have sv : ∀ b : Word, top.toNat ≤ b.toNat → (saved m top ret regs).getMem b = m.getMem b := fun b hb =>
    saved_get h144 (.inr hb)
  have l1 : m1.getMem (regs .x10 + 16#64) = vecLen m (regs .x10) := by
    have := hlen; rw [vecLen_eq, vecLen_eq, sv _ (by omega)] at this; exact this
  -- the header's numbers at the entry
  have hcap0 : vecCap (saved m top ret regs) (regs .x10) = vecCap m (regs .x10) := by
    rw [vecCap_eq, vecCap_eq, sv _ (by omega)]
  have hptr0 : vecPtr (saved m top ret regs) (regs .x10) = vecPtr m (regs .x10) := by
    rw [vecPtr_eq, vecPtr_eq, sv _ (by omega)]
  have hlen0 : vecLen (saved m top ret regs) (regs .x10) = vecLen m (regs .x10) := by
    rw [vecLen_eq, vecLen_eq, sv _ (by omega)]
  rw [hcap0, hlen0] at hkeep hgrow
  rw [hptr0] at hkeep
  obtain ⟨-, ⟨-, -, hB1, hB2⟩, hB3⟩ := hV1
  rw [rvCapAt_eq, rvPtrAt_eq] at hB1
  rw [rvCapAt_eq] at hB2
  rw [vecLen_eq, vecCap_eq, l1] at hB3
  have hbuf := hA.buf
  have hroom0 : (vecLen m (regs .x10)).toNat ≤ (vecCap m (regs .x10)).toNat := hV.2.2
  -- the frame, through the prologue's stores and `reserve`'s
  have hk'' : ∀ a : Word, ¬ (env.stackLimit.toNat ≤ a.toNat ∧ a.toNat < top.toNat) →
      ¬ ((env.next m).toNat ≤ a.toNat ∧ a.toNat < (env.next m1).toNat) → a ≠ env.nextAddr → ¬ out a →
      m1.getMem a = m.getMem a := fun a h1 h2 h3 ho => by
    have e1 : m1.getMem a = (saved m top ret regs).getMem a := hF1.2.2 a fun hw => by
      rcases hw with hw | hw | hw | hw
      · exact h1 ⟨hw.1, by have := hw.2; rw [e144] at this; omega⟩
      · rw [hsN] at hw; exact h2 hw
      · exact h3 hw
      · exact ho hw
    rw [e1]
    exact hF0.2.2 a fun hw => by
      rcases hw with hw | hw | hw | hw
      · exact h1 hw
      · exact h2 ⟨hw.1, by rw [hsN] at hw; omega⟩
      · exact h3 hw
      · exact hw
  have hMo : MemOk env m top ret regs (OutT regs m) m1 := by
    refine ⟨slots_keep h144 (fun b h1 h3 => hF1.2.2 b fun hw => ?_) hsl, ⟨by omega, hn2, fun a ha => ?_⟩, hS1,
      hc1.trans hc0⟩
    · rcases hw with hw | hw | hw | hw
      · have := hw.2; rw [e144] at this; omega
      · omega
      · rw [hw] at h1; omega
      · rcases hout b hw with rfl | rfl
        · rw [rvCapAt_eq] at h3; omega
        · rw [rvPtrAt_eq, ea8] at h3; omega
    · refine hk'' a (fun h => ha (.inl h)) (fun h => ha (.inr (.inl h))) (fun h => ha (.inr (.inr (.inl h))))
        fun ho => ha (.inr (.inr (.inr (.inl ?_))))
      unfold InRange; simp only [Layouts.Vec.byteSize]
      rcases hout a ho with rfl | rfl
      · rw [rvCapAt_eq]; omega
      · rw [rvPtrAt_eq, ea8]; omega
  refine ⟨⟨hMo, rfl, rfl, Nat.le_refl _, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩, ?_, kTop, l1⟩
  · by_cases hr : cnt regs m ≤ (vecCap m (regs .x10)).toNat - (vecLen m (regs .x10)).toNat
    · obtain ⟨hc, hp⟩ := hkeep hr
      rw [vecCap_eq] at hc
      rw [vecPtr_eq] at hp
      rw [hc, hp]
      have hb : (vecPtr m (regs .x10)).toNat + 48 * (vecLen m (regs .x10)).toNat ≤ (env.next m).toNat ∨
          (vecLen m (regs .x10)).toNat = 0 := by
        rcases hbuf with h0 | ⟨-, h3⟩
        · exact .inr (by omega)
        · exact .inl (by omega)
      have hold' := BlocksT.keep hold (by rcases hb with h | h <;> [have := env.heapEnd.isLt; skip] <;> omega)
        (by omega) (fun b hb' => kLow b (by rcases hb with h | h <;> omega))
        fun i hi x hx => kLow x (VecFormT.foot_lt (hold i hi).1 hx)
      exact hold'
    · obtain ⟨g1, g2, g3⟩ := hgrow hr
      rw [rvPtrAt_eq, rvCapAt_eq, sv _ (by omega), sv _ (by omega)] at g3
      rw [rvPtrAt_eq, rvCapAt_eq] at g2
      rw [rvCapAt_eq] at g1
      unfold Env.Fresh at g2
      rw [hsN] at g2
      intro i hi
      obtain ⟨hv, hap⟩ := hold i hi
      have hC : 0 < (vecCap m (regs .x10)).toNat := by omega
      obtain ⟨hP1, hP2⟩ := hbuf.resolve_left (by omega)
      have hP8 : (vecPtr m (regs .x10)).toNat % 8 = 0 := by
        rcases (vecT_buf hV).1 with h0 | ⟨-, -, h3⟩
        · omega
        · exact h3
      obtain ⟨hQ1, hQ2, hQ8⟩ := hB1.resolve_left (by omega)
      unfold Env.Live at hQ2
      rw [vecCap_eq] at hP2 hC
      rw [vecPtr_eq] at hP1 hP2 hP8 hap hv
      have hlen : i < (m.getMem (regs .x10)).toNat := by rw [vecCap_eq] at hroom0; omega
      have wd : ∀ o, o + 8 ≤ 48 * (i + 1) → o % 8 = 0 → m1.getMem (m1.getMem (regs .x10 + 8#64) +
          BitVec.ofNat 64 o) = m.getMem (m.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 o) := fun o ho ho8 => by
        rw [word_of_grown (C := (m.getMem (regs .x10)).toNat) g3 hP8 hQ8 (by omega) (by omega) (by omega) ho8]
        exact saved_get h144 (.inl (by rw [toNat_add_ofNat (by omega)]; omega))
      have a8 : ∀ q : Word, q + BitVec.ofNat 64 (48 * i) + 8#64 = q + BitVec.ofNat 64 (48 * i + 8) := fun q => by
        rw [BitVec.add_assoc, BitVec.ofNat_add]
      have a16 : ∀ q : Word, q + BitVec.ofNat 64 (48 * i) + 16#64 = q + BitVec.ofNat 64 (48 * i + 16) := fun q => by
        rw [BitVec.add_assoc, BitVec.ofNat_add]
      have e1 : (m1.getMem (regs .x10 + 8#64) + BitVec.ofNat 64 (48 * i)).toNat =
          (m1.getMem (regs .x10 + 8#64)).toNat + 48 * i := toNat_add_ofNat (by omega)
      obtain ⟨hv', hft⟩ := VecFormT.move' hv (by omega) (.inl ⟨by omega, by omega⟩) (by omega)
        (wd _ (by omega) (by omega)) (by rw [a8, a8]; exact wd _ (by omega) (by omega))
        (by rw [a16, a16]; exact wd _ (by omega) (by omega)) fun x hx => kLow x (VecFormT.foot_lt hv hx)
      exact ⟨hv', fun x hx => .inl (by have := VecFormT.foot_lt hv (hft x hx); omega)⟩
  · by_cases hr : cnt regs m ≤ (vecCap m (regs .x10)).toNat - (vecLen m (regs .x10)).toNat
    · obtain ⟨hc, hp⟩ := hkeep hr
      rw [vecCap_eq] at hc
      rw [vecPtr_eq] at hp
      refine ⟨?_, by rw [hc]; rw [vecCap_eq] at hr hroom0 ⊢; omega, hB2, by omega, .inl ⟨hp, by rw [hc, vecCap_eq]⟩⟩
      rcases hB1 with h0 | ⟨h1, h3, h4⟩
      · exact .inl h0
      · unfold Env.Live at h3; exact .inr ⟨h1, by omega, h4⟩
    · obtain ⟨g1, g2, -⟩ := hgrow hr
      rw [rvPtrAt_eq, rvCapAt_eq] at g2
      rw [rvCapAt_eq] at g1
      unfold Env.Fresh at g2
      rw [hsN] at g2
      refine ⟨?_, by omega, hB2, by omega, .inr g2.1⟩
      rcases hB1 with h0 | ⟨h1, h3, h4⟩
      · exact .inl h0
      · unfold Env.Live at h3; exact .inr ⟨h1, by omega, h4⟩

-- The entry steps `reserve`'s call with the thirty conjuncts of `PreT` in every goal's context: twice the default.
set_option maxHeartbeats 400000 in
set_option rv_sym.heap true in
/-- **`Vec<BusBlock>::extend_trusted` is total**, with 144 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR needC : Nat} (hnR : 144 + needR ≤ need) (hnC : 144 + needC ≤ need)
    (hres : ReserveSpecT env 8 48 p L.reserve.idx needR) (hcl : CloneFormsFreshT.SpecT env p L.clone.idx needC) :
    SpecT env p i need := by
  rv_autoT hp stop [78, 118] with [hL] using [hres]
  all_goals
    have hlay := env.layout
    have h144 : 144 ≤ top.toNat := by have := hpre_30.nextAddr_ge; omega
  -- `reserve`'s precondition, read through the prologue's stores
  all_goals try
    have hx8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
    have hcap0 : (saved m top ret regs).getMem (regs .x10) = m.getMem (regs .x10) :=
      saved_get h144 (.inr (by rw [← hpre_2]; exact hpre_12))
    have hptr0 : (saved m top ret regs).getMem (regs .x10 + 8#64) = m.getMem (regs .x10 + 8#64) :=
      saved_get h144 (.inr (by rw [← hpre_2, hx8]; omega))
    have hSn : (saved m top ret regs).getMem env.nextAddr = m.getMem env.nextAddr :=
      saved_get h144 (.inl (by omega))
    simp only [saved] at hcap0 hptr0 hSn
    simp only [rvCapAt_eq, rvPtrAt_eq, hcap0, hptr0, Env.Live, Env.next, hSn] at hpre_9 hpre_10 hpre_11 ⊢
    first
    | exact hpre_9
    | exact hpre_10
    | exact hpre_9.imp id fun h => h.2.1
    | (rwa [vecLen_eq, vecCap_eq] at hpre_11)
  all_goals
    have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
    have hA : Args env m top regs := ⟨hlim, hpre_30, hpre_29, hpre_2, ⟨hpre_6, ⟨hpre_7, hpre_8, hpre_9, hpre_10⟩,
      hpre_11⟩, ⟨hpre_12, hpre_13⟩, hpre_14, ⟨hpre_15, hpre_16⟩, hpre_17, hpre_18, hpre_19, hpre_20, hpre_21,
      hpre_22, hpre_23, hpre_24, hpre_25, hpre_26, hpre_27, hpre_28⟩
  -- after `reserve`
  all_goals
    have hn : ((m.getMem (regs .x11 + 8#64) - m.getMem (regs .x11)) >>> 3 * 12297829382473034411#64).toNat =
        cnt regs m := cnt_toNat hpre_19 hpre_20
    rw [hn] at hret1_17 hret1_18
    obtain ⟨hMI, hBuf, kTop, l1⟩ := after_reserve hA h144 hpre_5 hpre_4 hret1_14 hret1_15 hret1_25 (fun b hb => hb)
      ⟨hret1_19, ⟨hret1_20, hret1_21, hret1_22, hret1_23⟩, hret1_24⟩ hret1_16 hret1_17 hret1_18
    have ha16 : (regs .x11 + 16#64).toNat = (regs .x11).toNat + 16 := toNat_add_ofNat (by omega)
    have ha24 : (regs .x11 + 24#64).toNat = (regs .x11).toNat + 24 := toNat_add_ofNat (by omega)
    have ha32 : (regs .x11 + 32#64).toNat = (regs .x11).toNat + 32 := toNat_add_ofNat (by omega)
    have kI : ∀ o : Nat, o < 40 → ∀ b : Word, b.toNat = (regs .x11).toNat + o → m1.getMem b = m.getMem b :=
      fun o ho b hb => kTop b (by rw [← hpre_2] at *; omega) fun h => by
        unfold InRange at h; rcases hpre_18 with h' | h' <;> omega
  · -- `begin = end`: no `BusBlock`s
    have hn0 : cnt regs m = 0 := by unfold cnt; rw [hc]; simp
    exact exit hp hL hk hA hBuf _ _ ⟨rfl, rfl, rfl, rfl⟩ (by simp only [Tactic.rf]; rw [l1, hn0, Nat.add_zero]) (hn0 ▸ hMI)
  · -- into the loop
    have hn0 : 0 < cnt regs m := by
      have : (m.getMem (regs .x11 + 8#64)).toNat ≠ (m.getMem (regs .x11)).toNat := by
        intro h; apply hc; exact BitVec.eq_of_toNat_eq h
      unfold cnt; omega
    have hsl := hA.src_lt hn0
    obtain ⟨hQ1, hQ2, hQ8⟩ := hBuf.pos hn0
    have hroom := hBuf.2.1
    have hN1 := hMI.2.2.2.1
    have hnM := hMI.1.2.1.2.1
    have hdiv : (m.getMem (regs .x11 + 8#64)).toNat - (m.getMem (regs .x11)).toNat = 24 * cnt regs m := by
      unfold cnt; omega
    exact loop hp hL hnC hcl hk hstop hpre_3 hA hBuf (cnt regs m - 1) _ _
      ⟨⟨rfl, rfl, kI 32 (by omega) _ ha32, kI 16 (by omega) _ ha16, kI 24 (by omega) _ ha24, by
        simp only [Tactic.rf]
        rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (BitVec.le_def.2 hpre_19), toNat_add_ofNat (by omega), hdiv]
        omega, by
        simp only [Tactic.rf]
        rw [BitVec.toNat_add, l1, hn]
        have := (vecLen m (regs .x10)).isLt
        omega, rfl, rfl⟩, 0, by omega, by simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)], by
        simp only [Tactic.rf]
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
          Nat.shiftLeft_eq, l1]
        have := (vecLen m (regs .x10)).isLt
        omega, hMI⟩

end Rv64mc.Proof.Layout.ExtendTrustedT

/-- info: 'Rv64mc.Proof.Layout.ExtendTrustedT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.ExtendTrustedT.total
