/-
  Rv64mc.Proof.Layout.SpecExtendFormT

  `<Vec<Form> as SpecExtend<&Form, slice::Iter<Form>>>::spec_extend` (`extend_from_slice` for `Form`s) is total:
  called with the vector's header (`a0`) and the source slice `[a1, a2)` of `n = (a2 - a1) / 24` `Form`s, it
  reserves `n` more elements (`Vec::reserve`), then clones each source `Form` into the next spare slot: it checks the
  `Form`'s length against `isize::MAX / 40` (a word of the static data), allocates its terms' block, and for each term
  clones the monomial (`Vec<usize>::clone`) and copies the coefficient's two words; it stores the new length last.
  The run ends with the guest's abort (`AbortStop`) where `alloc` or `handle_error` does. A safety-only contract (the
  function is class D: no spec); it does not state the terms' values.

  The precondition: the vector `VecT` with room for the `n` new `Form`s (`len + n ≤ cap`), its header at or above the
  stack pointer (`StackObj`), its elements `Form`s (`FormReprT.FormsT`); the source whole 24-byte elements, unless
  empty apart from the stack below the stack pointer, from the heap not yet allocated and from the buffer's spare
  slots, each a `Form`; and every terms' block of the elements and of the source apart from the spare slots
  (`TermsApart`). At the image's five call sites (three in `<[&[Form]]>::concat`, two in `Flushes::bytecode`) the
  header is a slot of the caller's frame and the buffer is allocated by the caller with the total count as its
  capacity, after every block the sources' `Form`s point to, so `reserve` never grows it.

  The postcondition: the vector `VecT` again with its pointer and capacity, its length grown by `n`, all its elements
  `Form`s, their terms' blocks apart from the new spare slots, the new ones' allocated by the call
  (`CloneFormsFreshT.FreshTermsT`). What it writes besides its stack and fresh blocks is the header and the new
  `Form`s' slots (`OutT`).

  The body is cut at the outer loop's head (instruction 66, measure the `Form`s left), the inner loop's head (124,
  measure the terms left), after the monomial's clone (138), the inner loop's back edge (168), the join where a new
  `Form`'s header is stored (186) and the return (206). Every part keeps `CloneFormsT.MemOk` with the slots as `out`:
  `reserve`'s writes to the header keep its values, so the header is not written until the return.

  ## Main definitions

  * `cnt`, `TermsApart`, `PreT`, `PostT`, `SlotOut`, `OutT`, `SpecT`, `DoneT`, `Args`, `JRegs`, `OInv`, `KRegs`,
    `TInv`, `IInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.CloneFormsFreshT
import Rv64mc.Proof.Layout.PairT
import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Gen.Tmpl.Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend

namespace Rv64mc.Proof.Layout.SpecExtendFormT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT CloneSpecT)
open Rv64mc.Proof.Runtime.ReserveT (ReserveSpecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Layout.CloneFormsT (Slots MemOk es slots_keep vecT_copy new_form TermsT.keep saved data_ok)
open Rv64mc.Proof.Layout.CloneFormsFreshT (FreshTermsT)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Gen.Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend (Link tmpl d_c8_51ab739d_words)

/-- The source's `Form`s: `(a2 - a1) / 24`. -/
def cnt (regs : Reg → Word) : Nat := ((regs .x12).toNat - (regs .x11).toNat) / 24

/-- **The terms' blocks of the `n` `Form`s from `q` avoid `[lo, hi)`**: each `Form` has no terms, or its block lies
    below `lo` or from `hi`. -/
def TermsApart (m : MachineState) (q : Word) (n lo hi : Nat) : Prop :=
  ∀ i, i < n → (vecLen m (q + BitVec.ofNat 64 (24 * i))).toNat = 0 ∨
    (vecPtr m (q + BitVec.ofNat 64 (24 * i))).toNat + 40 * (vecLen m (q + BitVec.ofNat 64 (24 * i))).toNat ≤ lo ∨
    hi ≤ (vecPtr m (q + BitVec.ofNat 64 (24 * i))).toNat

/-- The first of the vector's spare slots at `a`, as a number. -/
def spareLo (m : MachineState) (a : Word) : Nat := (vecPtr m a).toNat + 24 * (vecLen m a).toNat

/-- The end of the vector's buffer at `a`, as a number. -/
def spareHi (m : MachineState) (a : Word) : Nat := (vecPtr m a).toNat + 24 * (vecCap m a).toNat

/-- The total precondition: the vector with room, its header a caller's frame object, its elements `Form`s; the
    source whole `Form`s apart from the stack below the stack pointer, the heap not yet allocated and the spare slots;
    the terms' blocks of both apart from the spare slots. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  VecT env m (regs .x10) 24 ∧ StackObj (regs .x2) (regs .x10) 24 ∧
    FormsT env m (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat ∧
    TermsApart m (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat (spareLo m (regs .x10))
      (spareHi m (regs .x10)) ∧
    (regs .x11).toNat ≤ (regs .x12).toNat ∧ ((regs .x12).toNat - (regs .x11).toNat) % 24 = 0 ∧
    (vecLen m (regs .x10)).toNat + cnt regs ≤ (vecCap m (regs .x10)).toNat ∧
    (cnt regs = 0 ∨ (OffStack env (regs .x2) (regs .x11) (24 * cnt regs) ∧
      ((regs .x11).toNat + 24 * cnt regs ≤ (env.next m).toNat ∨ env.heapEnd.toNat ≤ (regs .x11).toNat) ∧
      ((regs .x11).toNat + 24 * cnt regs ≤ spareLo m (regs .x10) ∨ spareHi m (regs .x10) ≤ (regs .x11).toNat))) ∧
    FormsT env m (regs .x11) (cnt regs) ∧
    TermsApart m (regs .x11) (cnt regs) (spareLo m (regs .x10)) (spareHi m (regs .x10))

/-- The total postcondition: the vector with its buffer, `n` longer, its elements `Form`s with their terms' blocks
    apart from the new spare slots, the new ones' allocated by the call. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 24 ∧ (vecLen m' (regs .x10)).toNat = (vecLen m (regs .x10)).toNat + cnt regs ∧
    vecCap m' (regs .x10) = vecCap m (regs .x10) ∧ vecPtr m' (regs .x10) = vecPtr m (regs .x10) ∧
    FormsT env m' (vecPtr m (regs .x10)) ((vecLen m (regs .x10)).toNat + cnt regs) ∧
    TermsApart m' (vecPtr m (regs .x10)) ((vecLen m (regs .x10)).toNat + cnt regs) (spareLo m' (regs .x10))
      (spareHi m' (regs .x10)) ∧
    FreshTermsT env m m' (vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * (vecLen m (regs .x10)).toNat)) (cnt regs)

/-- The slots the new `Form`s' headers go to. -/
def SlotOut (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  spareLo m (regs .x10) ≤ b.toNat ∧ b.toNat < spareLo m (regs .x10) + 24 * cnt regs

/-- What `spec_extend` writes besides its stack and what it allocates. -/
def OutT (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.Vec.byteSize b ∨ SlotOut regs m b

/-- **The total contract of `Vec<Form>::spec_extend` from a slice.** -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-! ## The frame -/

/-- **A word the frame does not let the function write** (below `NEXT` at entry or at or above the stack top, and
    outside `out`) is the entry's. -/
theorem keepF {env : Env} {top b : Word} {out : Word → Prop} {m M : MachineState} (hF : env.Frame top out m M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : b.toNat < (env.next m).toNat ∨ top.toNat ≤ b.toNat)
    (ho : ¬ out b) : M.getMem b = m.getMem b :=
  hF.2.2 b fun hw => by
    have := env.layout
    have := hF.1
    have := hF.2.1
    rcases hw with hw | hw | hw | hw
    · omega
    · omega
    · rw [hw] at hb; omega
    · exact ho hw

/-- A frame's `out` widened. -/
theorem frame_mono {env : Env} {top : Word} {out out' : Word → Prop} {m M : MachineState}
    (h : env.Frame top out m M) (ho : ∀ b, out b → out' b) : env.Frame top out' m M :=
  ⟨h.1, h.2.1, fun a ha => h.2.2 a fun hw => ha (hw.imp_right (Or.imp_right (Or.imp_right (ho a))))⟩

/-- **A store into the frame below the slots** (`top - 160` to `top - 104`): `MemOk`, `NEXT` and every other word
    kept. -/
theorem frame_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (h176 : 176 ≤ top.toNat) (hM : MemOk env m top ret regs out M)
    (ha1 : top.toNat - 160 ≤ a.toNat) (ha2 : a.toNat + 8 ≤ top.toNat - 104) :
    MemOk env m top ret regs out (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ b : Word, b ≠ a → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  exact ⟨⟨slots_keep h176 (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_slot hF (by omega) (by omega), Env.static_setMem_stack hS (by omega),
    by rw [MachineState.code_setMem, hc]⟩, Env.next_setMem_stack (by omega),
    fun b hb => MachineState.getMem_setMem_ne hb⟩

/-- **A store into a block allocated since the entry**: `MemOk`, `NEXT` and every word apart from it kept. -/
theorem heap_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (h176 : 176 ≤ top.toNat) (hM : MemOk env m top ret regs out M)
    (ha1 : (env.next m).toNat ≤ a.toNat) (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    MemOk env m top ret regs out (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ b : Word, b ≠ a → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  exact ⟨⟨slots_keep h176 (fun b h1 _ => MachineState.getMem_setMem_ne fun e => by rw [e] at h1; omega) hsl,
    Tactic.frame_fresh hF rfl ha1 (by omega), Tactic.static_store hS (.inl (by omega)),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne, fun b hb => MachineState.getMem_setMem_ne hb⟩

/-- **A store into a new `Form`'s slot**: `MemOk`, `NEXT` and every other word kept. -/
theorem slot_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (h176 : 176 ≤ top.toNat)
    (hM : MemOk env m top ret regs (SlotOut regs m) M) (ha : SlotOut regs m a)
    (ha2 : a.toNat + 8 ≤ (env.next m).toNat) :
    MemOk env m top ret regs (SlotOut regs m) (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ b : Word, b ≠ a → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have hnm := hF.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  exact ⟨⟨slots_keep h176 (fun b h1 _ => MachineState.getMem_setMem_ne fun e => by rw [e] at h1; omega) hsl,
    Tactic.frame_out hF ha hne, Tactic.static_store hS (.inl (by omega)),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne, fun b hb => MachineState.getMem_setMem_ne hb⟩

/-! ## The new `Form`s -/

/-- **The `j` new `Form`s** after the `l` the vector had, at `P + 24 (l + i)`: each a `Form` whose terms' block lies
    between `lo` and `H`. -/
def DoneT (env : Env) (M : MachineState) (P : Word) (l j lo H : Nat) : Prop :=
  ∀ i, i < j → FormT env M (P + BitVec.ofNat 64 (24 * (l + i))) ∧
    ((vecLen M (P + BitVec.ofNat 64 (24 * (l + i)))).toNat = 0 ∨
      (lo ≤ (vecPtr M (P + BitVec.ofNat 64 (24 * (l + i)))).toNat ∧
        (vecPtr M (P + BitVec.ofNat 64 (24 * (l + i)))).toNat +
          40 * (vecLen M (P + BitVec.ofNat 64 (24 * (l + i)))).toNat ≤ H))

/-- **`DoneT` is kept** by a memory agreeing on the new headers and on `[lo, H)`, `NEXT` no lower. -/
theorem DoneT.keep {env : Env} {M M' : MachineState} {P : Word} {l j lo H : Nat} (h : DoneT env M P l j lo H)
    (hP : P.toNat + 24 * (l + j) < 2 ^ 64) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ b : Word, (P.toNat + 24 * l ≤ b.toNat ∧ b.toNat < P.toNat + 24 * (l + j)) ∨ (lo ≤ b.toNat ∧ b.toNat < H) →
      M'.getMem b = M.getMem b) : DoneT env M' P l j lo H := by
  intro i hi
  obtain ⟨hF, hfoot⟩ := h i hi
  have e : (P + BitVec.ofNat 64 (24 * (l + i))).toNat = P.toNat + 24 * (l + i) := toNat_add_ofNat (by omega)
  have hk1 : ∀ b : Word, (P + BitVec.ofNat 64 (24 * (l + i))).toNat ≤ b.toNat →
      b.toNat < (P + BitVec.ofNat 64 (24 * (l + i))).toNat + 24 → M'.getMem b = M.getMem b :=
    fun b h1 h2 => hk b (.inl ⟨by omega, by omega⟩)
  have hlt := vecT_lt hF.1
  have e8 : (P + BitVec.ofNat 64 (24 * (l + i)) + 8#64).toNat = (P + BitVec.ofNat 64 (24 * (l + i))).toNat + 8 :=
    toNat_add_ofNat (by omega)
  have e16 : (P + BitVec.ofNat 64 (24 * (l + i)) + 16#64).toNat = (P + BitVec.ofNat 64 (24 * (l + i))).toNat + 16 :=
    toNat_add_ofNat (by omega)
  have ep : vecPtr M' (P + BitVec.ofNat 64 (24 * (l + i))) = vecPtr M (P + BitVec.ofNat 64 (24 * (l + i))) := by
    rw [vecPtr_eq, vecPtr_eq]; exact hk1 _ (by rw [e8]; omega) (by rw [e8]; omega)
  have el : vecLen M' (P + BitVec.ofNat 64 (24 * (l + i))) = vecLen M (P + BitVec.ofNat 64 (24 * (l + i))) := by
    rw [vecLen_eq, vecLen_eq]; exact hk1 _ (by rw [e16]; omega) (by rw [e16]; omega)
  refine ⟨hF.keep hn hk1 fun b h1 h2 => hk b (.inr ?_), by rw [ep, el]; exact hfoot⟩
  omega

/-- `DoneT`'s bound only grows. -/
theorem DoneT.mono {env : Env} {M : MachineState} {P : Word} {l j lo H H' : Nat} (h : DoneT env M P l j lo H)
    (hH : H ≤ H') : DoneT env M P l j lo H' := fun i hi =>
  ⟨(h i hi).1, (h i hi).2.imp id fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩

/-! ## The precondition's facts -/

/-- The facts of the entry every part reads. -/
def Args (env : Env) (m : MachineState) (top : Word) (regs : Reg → Word) : Prop :=
  env.stackLimit.toNat + 160 ≤ top.toNat ∧ Windows env top m ∧ top.toNat % 16 = 0 ∧ regs .x2 = top ∧
    PreT env regs m

/-- **The buffer's numbers**, when there is a `Form` to push: from the heap's start, below `NEXT`, aligned, with room;
    and the header above the stack top. -/
theorem Args.buf {env : Env} {m : MachineState} {top : Word} {regs : Reg → Word} (hA : Args env m top regs)
    (hn : 0 < cnt regs) :
    0x10000000 ≤ (vecPtr m (regs .x10)).toNat ∧
      (vecPtr m (regs .x10)).toNat + 24 * (vecCap m (regs .x10)).toNat ≤ (env.next m).toNat ∧
      (vecPtr m (regs .x10)).toNat % 8 = 0 ∧
      (vecLen m (regs .x10)).toNat + cnt regs ≤ (vecCap m (regs .x10)).toNat := by
  obtain ⟨-, -, -, -, hV, -, -, -, -, -, hroom, -⟩ := hA
  obtain ⟨hb, -, -⟩ := vecT_buf hV
  obtain ⟨-, ⟨-, -, hB, -⟩, -⟩ := hV
  rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq] at hB
  rcases hB with h0 | ⟨h1, h2, h3⟩
  · omega
  · unfold Env.Live at h2
    exact ⟨h1, by omega, h3, hroom⟩

/-- A new `Form`'s slot lies in the buffer, below `NEXT` at entry. -/
theorem Args.slot {env : Env} {m : MachineState} {top b : Word} {regs : Reg → Word} (hA : Args env m top regs)
    (hb : SlotOut regs m b) :
    spareLo m (regs .x10) ≤ b.toNat ∧ b.toNat < spareLo m (regs .x10) + 24 * cnt regs ∧
      spareLo m (regs .x10) + 24 * cnt regs ≤ (env.next m).toNat ∧ 0 < cnt regs := by
  obtain ⟨h1, h2⟩ := hb
  have hn : 0 < cnt regs := by omega
  obtain ⟨-, h3, -, h4⟩ := hA.buf hn
  unfold spareLo at *
  exact ⟨h1, h2, by omega, hn⟩

/-- The header lies at or above the stack top, so apart from every slot, block and `NEXT`. -/
theorem Args.hdr {env : Env} {m : MachineState} {top : Word} {regs : Reg → Word} (hA : Args env m top regs) :
    top.toNat ≤ (regs .x10).toNat ∧ (regs .x10).toNat + 24 ≤ 0xc0000000 := by
  obtain ⟨-, -, -, h2, -, hso, -⟩ := hA
  rw [← h2]; exact hso

/-! ## The return -/

/-- A `Form` below `NEXT` is kept by a store at or above the stack top. -/
theorem FormT.store_top {env : Env} {M : MachineState} {a s v top : Word} (h : FormT env M a)
    (ha : a.toNat + 24 ≤ (env.next M).toNat) (hnx : (env.next M).toNat ≤ env.heapEnd.toNat)
    (hs : top.toNat ≤ s.toNat) (htop : env.stackLimit.toNat ≤ top.toNat) (hn : s ≠ env.nextAddr) :
    FormT env (M.setMem s v) a := by
  have hlay := env.layout
  have ne : ∀ b : Word, b.toNat < (env.next M).toNat → (M.setMem s v).getMem b = M.getMem b := fun b hb =>
    MachineState.getMem_setMem_ne fun e => by rw [e] at hb; omega
  refine h.keep (by rw [Tactic.next_setMem hn]) (fun b _ h2 => ne b (by omega)) fun b _ h2 => ne b ?_
  have := h.foot; omega

/-- The registers the return reads: the stack pointer and the header. -/
def XRegs (top : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551456#64 ∧ R .x9 = regs .x10

/-- **The postcondition at the return**, from the invariant: the new length stored. -/
theorem exit_post {env : Env} {m M : MachineState} {top ret : Word} {regs : Reg → Word} {v : Word}
    (hA : Args env m top regs) (hv : v.toNat = (vecLen m (regs .x10)).toNat + cnt regs)
    (hM : MemOk env m top ret regs (SlotOut regs m) M)
    (hdone : DoneT env M (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat (cnt regs) (env.next m).toNat
      (env.next M).toNat) {r : Reg → Word} :
    PostT env regs m r (M.setMem (regs .x10 + 16#64) v) ∧
      env.Frame top (OutT regs m) m (M.setMem (regs .x10 + 16#64) v) ∧
      env.Static (M.setMem (regs .x10 + 16#64) v) := by
  have hlay := env.layout
  obtain ⟨hstk, hW, -, h2, hV, hso, hold, hTA, -, -, hroom, -, -, -⟩ := id hA
  obtain ⟨hhd1, hhd2⟩ := hA.hdr
  obtain ⟨-, hF, hS, -⟩ := hM
  have hnm := hF.1
  have hnM := hF.2.1
  have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hn16 : regs .x10 + 16#64 ≠ env.nextAddr := fun e => by
    have := congrArg BitVec.toNat e; rw [e16] at this; omega
  have hslot : ∀ b : Word, SlotOut regs m b → b.toNat < (env.next m).toNat := fun b hb => by
    have := hA.slot hb; omega
  have kH : ∀ b : Word, top.toNat ≤ b.toNat → M.getMem b = m.getMem b := fun b hb =>
    keepF hF (by omega) (.inr hb) fun h => by have := hslot b h; omega
  have ne16 : ∀ b : Word, b.toNat ≠ (regs .x10).toNat + 16 →
      (M.setMem (regs .x10 + 16#64) v).getMem b = M.getMem b := fun b hb =>
    MachineState.getMem_setMem_ne fun e => hb (by rw [e, e16])
  have c0 : (M.setMem (regs .x10 + 16#64) v).getMem (regs .x10) = m.getMem (regs .x10) := by
    rw [ne16 _ (by omega), kH _ (by omega)]
  have c8 : (M.setMem (regs .x10 + 16#64) v).getMem (regs .x10 + 8#64) = m.getMem (regs .x10 + 8#64) := by
    rw [ne16 _ (by omega), kH _ (by omega)]
  have c16 : (M.setMem (regs .x10 + 16#64) v).getMem (regs .x10 + 16#64) = v := MachineState.getMem_setMem_eq
  have hN : env.next (M.setMem (regs .x10 + 16#64) v) = env.next M := Tactic.next_setMem hn16
  have ecap : vecCap (M.setMem (regs .x10 + 16#64) v) (regs .x10) = vecCap m (regs .x10) := by
    rw [vecCap_eq, vecCap_eq, c0]
  have eptr : vecPtr (M.setMem (regs .x10 + 16#64) v) (regs .x10) = vecPtr m (regs .x10) := by
    rw [vecPtr_eq, vecPtr_eq, c8]
  have elen : vecLen (M.setMem (regs .x10 + 16#64) v) (regs .x10) = v := by rw [vecLen_eq, c16]
  -- the old `Form`s' headers and blocks, and the new ones', below `NEXT`
  obtain ⟨hB1, hB2, hB3⟩ : (cnt regs = 0 ∨ (0x10000000 ≤ (vecPtr m (regs .x10)).toNat ∧
      (vecPtr m (regs .x10)).toNat + 24 * (vecCap m (regs .x10)).toNat ≤ (env.next m).toNat)) ∧
      ((vecLen m (regs .x10)).toNat = 0 ∨
        (vecPtr m (regs .x10)).toNat + 24 * (vecCap m (regs .x10)).toNat ≤ (env.next m).toNat) ∧
      (vecPtr m (regs .x10)).toNat + 24 * (vecCap m (regs .x10)).toNat < 2 ^ 64 := by
    obtain ⟨-, ⟨-, -, hB, hB4⟩, -⟩ := hV
    rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq] at hB
    rw [rvCapAt_eq, ← vecCap_eq] at hB4
    rcases hB with h0 | ⟨h1, h3, -⟩
    · refine ⟨.inl (by omega), .inl (by omega), ?_⟩
      have := (vecPtr m (regs .x10)).isLt; omega
    · unfold Env.Live at h3
      exact ⟨.inr ⟨h1, by omega⟩, .inr (by omega), by omega⟩
  have hHS : env.heapEnd.toNat < top.toNat := by omega
  have hold' : FormsT env (M.setMem (regs .x10 + 16#64) v) (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat := by
    intro k hk
    have hFk := hold k hk
    have e : (vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * k)).toNat = (vecPtr m (regs .x10)).toNat + 24 * k :=
      toNat_add_ofNat (by omega)
    have hkM : ∀ b : Word, b.toNat < (env.next m).toNat → ¬ (spareLo m (regs .x10) ≤ b.toNat ∧
        b.toNat < spareLo m (regs .x10) + 24 * cnt regs) → (M.setMem (regs .x10 + 16#64) v).getMem b = m.getMem b :=
      fun b h1 h2 => by rw [ne16 _ (by omega)]; exact keepF hF (by omega) (.inl h1) h2
    refine hFk.keep (by rw [hN]; omega) (fun b h1 h2 => hkM b ?_ ?_) fun b h1 h2 => hkM b ?_ ?_
    · rw [e] at h2; omega
    · rw [e] at h2; unfold spareLo; omega
    · have := hFk.foot; omega
    · rcases hTA k hk with h0 | h3 | h3
      · omega
      · unfold spareLo at h3 ⊢; omega
      · unfold spareLo spareHi at *; omega
  have hnew : DoneT env (M.setMem (regs .x10 + 16#64) v) (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat
      (cnt regs) (env.next m).toNat (env.next M).toNat :=
    DoneT.keep hdone (by omega) (by rw [hN]) fun b hb => ne16 b (by omega)
  have eidx : ∀ k, vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * (vecLen m (regs .x10)).toNat) +
      BitVec.ofNat 64 (24 * k) = vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * ((vecLen m (regs .x10)).toNat + k)) :=
    fun k => by rw [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨⟨⟨hV.1, hV.2.1.keep (by rw [rvCapAt_eq]; exact c0) (by rw [rvPtrAt_eq]; exact c8)
      (by rw [hN]; omega), by rw [elen, ecap, hv]; exact hroom⟩, by rw [elen, hv], ecap, eptr, fun k hk => ?_, ?_,
      fun k hk => ?_⟩,
    Tactic.frame_out (frame_mono hF fun b h => .inr h) (.inl (by unfold InRange; simp only [Layouts.Vec.byteSize]; rw [e16]; omega)) hn16,
    Tactic.static_store hS (.inr (by rw [e16]; omega))⟩
  · rcases Nat.lt_or_ge k (vecLen m (regs .x10)).toNat with hk' | hk'
    · exact hold' k hk'
    · have := (hnew (k - (vecLen m (regs .x10)).toNat) (by omega)).1
      rwa [Nat.add_sub_cancel' hk'] at this
  · intro k hk
    unfold spareLo spareHi
    rw [eptr, elen, ecap, hv]
    rcases Nat.lt_or_ge k (vecLen m (regs .x10)).toNat with hk' | hk'
    · have e : (vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * k)).toNat = (vecPtr m (regs .x10)).toNat + 24 * k :=
        toNat_add_ofNat (by omega)
      have g : ∀ o, o < 24 → (M.setMem (regs .x10 + 16#64) v).getMem (vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * k)
          + BitVec.ofNat 64 o) = m.getMem (vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * k) + BitVec.ofNat 64 o) :=
        fun o ho => by
          have eo : (vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * k) + BitVec.ofNat 64 o).toNat =
              (vecPtr m (regs .x10)).toNat + 24 * k + o := by rw [toNat_add_ofNat (by omega), e]
          rw [ne16 _ (by omega)]
          refine keepF hF (by omega) (.inl (by omega)) fun h => ?_
          obtain ⟨h1, -⟩ := h
          unfold spareLo at h1
          omega
      have gl := g 16 (by omega)
      have gp := g 8 (by omega)
      rw [vecLen_eq (M.setMem (regs .x10 + 16#64) v), vecPtr_eq (M.setMem (regs .x10 + 16#64) v), gl, gp,
        ← vecLen_eq, ← vecPtr_eq]
      rcases hTA k hk' with h0 | h3 | h3
      · exact .inl h0
      · unfold spareLo at h3; exact .inr (.inl (by omega))
      · unfold spareHi at h3; exact .inr (.inr h3)
    · have := (hnew (k - (vecLen m (regs .x10)).toNat) (by omega)).2
      rw [Nat.add_sub_cancel' hk'] at this
      rcases this with h0 | ⟨h3, -⟩
      · exact .inl h0
      · rcases hB2 with h0 | h4
        · omega
        · exact .inr (.inr (by omega))
  · rw [eidx]
    exact (hnew k hk).2.imp_right fun ⟨h3, h4⟩ => ⟨h3, by rw [hN]; exact h4⟩

set_option rv_sym.heap true in
/-- **The return**, from instruction 206: the new length stored at `a0 + 16`, the saved registers. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) :
    ∀ R M, XRegs top regs R → (R .x21).toNat = (vecLen m (regs .x10)).toNat + cnt regs →
      MemOk env m top ret regs (SlotOut regs m) M →
      DoneT env M (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat (cnt regs) (env.next m).toNat
        (env.next M).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 206, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR h21 hM hdone
  have hlay := env.layout
  obtain ⟨hPost, hF', hS'⟩ := exit_post (r := fun _ => 0#64) hA h21 hM hdone
  obtain ⟨hstk, hW, h16, -⟩ := id hA
  obtain ⟨hhd1, hhd2⟩ := hA.hdr
  obtain ⟨hsl, -, -, hc0⟩ := hM
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13⟩ := hsl
  have := hW.nextAddr_ge
  have w16 : inWindow (regs .x10 + 16#64) 8 = true := by
    rw [inWindow_iff, toNat_add_ofNat (by omega)]; omega
  rv_introT hR
  rv_symT hp with [_hL]
  exact ⟨⟨rfl, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13⟩, hF', hS', hPost⟩

/-! ## The join: a new `Form`'s header stored -/

/-- **The join's three stores** at `A = P + 24 (l + j)`, the header `(c, Q, L)` of a new `Form` with its terms'
    block between `H` and `NEXT`: `MemOk` and `NEXT` kept, `j + 1` new `Form`s. -/
theorem join_mem {env : Env} {m M : MachineState} {top ret A c Q L : Word} {regs : Reg → Word} {j H : Nat}
    (hA : Args env m top regs) (h176 : 176 ≤ top.toNat) (hM : MemOk env m top ret regs (SlotOut regs m) M)
    (hAeq : A = vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * ((vecLen m (regs .x10)).toNat + j)))
    (hj : j < cnt regs) (hmH : (env.next m).toNat ≤ H) (hH : H ≤ (env.next M).toNat)
    (hdone : DoneT env M (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat j (env.next m).toNat H)
    (hL : L.toNat * 40 < 2 ^ 63)
    (hnew : (c.toNat = 0 ∧ L.toNat = 0) ∨ (c = L ∧ H ≤ Q.toNat ∧ Q.toNat + 40 * L.toNat ≤ (env.next M).toNat ∧
      Q.toNat % 8 = 0 ∧ TermsT env M Q L.toNat)) :
    MemOk env m top ret regs (SlotOut regs m) (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L) ∧
      env.next (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L) = env.next M ∧
      DoneT env (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L) (vecPtr m (regs .x10))
        (vecLen m (regs .x10)).toNat (j + 1) (env.next m).toNat
        (env.next (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L)).toNat := by
  have hlay := env.layout
  have hstk := hA.1
  obtain ⟨b1, b2, b3, b4⟩ := hA.buf (by omega)
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have eA : A.toNat = (vecPtr m (regs .x10)).toNat + 24 * ((vecLen m (regs .x10)).toNat + j) := by
    rw [hAeq]; exact toNat_add_ofNat (by omega)
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  have hs : ∀ b : Word, A.toNat ≤ b.toNat → b.toNat < A.toNat + 24 → SlotOut regs m b := fun b h1 h2 => by
    unfold SlotOut spareLo; omega
  obtain ⟨m1, n1, k1⟩ := slot_store (a := A) (v := c) hstk h176 hM (hs _ (by omega) (by omega)) (by omega)
  obtain ⟨m2, n2, k2⟩ := slot_store (a := A + 8#64) (v := Q) hstk h176 m1 (hs _ (by omega) (by omega)) (by omega)
  obtain ⟨m3, n3, k3⟩ := slot_store (a := A + 16#64) (v := L) hstk h176 m2 (hs _ (by omega) (by omega)) (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hk : ∀ b : Word, (b.toNat < A.toNat ∨ A.toNat + 24 ≤ b.toNat) →
      (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L).getMem b = M.getMem b := fun b hb => by
    rw [k3 b (ne _ _ (by omega)), k2 b (ne _ _ (by omega)), k1 b (ne _ _ (by omega))]
  have hN : env.next (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L) = env.next M := by
    rw [n3, n2, n1]
  have r0 : (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L).getMem A = c := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L).getMem (A + 8#64) = Q := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r16 : (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L).getMem (A + 16#64) = L :=
    MachineState.getMem_setMem_eq
  have hold := (DoneT.keep hdone (by omega) (by rw [hN]) fun b hb => hk b (by omega)).mono
    (H' := (env.next M).toNat) hH
  have hF : FormT env (((M.setMem A c).setMem (A + 8#64) Q).setMem (A + 16#64) L) A := by
    refine new_form (.inl ⟨by omega, by omega⟩) (by omega) r0 r8 r16 hL ?_
    rcases hnew with h | ⟨h1, h2, h3, h4, h5⟩
    · exact .inl h
    · refine .inr ⟨h1, by omega, by rw [hN]; exact h3, h4,
        TermsT.keep h5 (by omega) (by rw [hN]) fun b h6 h7 => hk b ?_⟩
      omega
  refine ⟨m3, hN, fun i hi => ?_⟩
  rw [hN]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
  · exact hold i hi
  · rw [hi, ← hAeq]
    refine ⟨hF, ?_⟩
    rw [vecLen_eq, vecPtr_eq, r8, r16]
    rcases hnew with ⟨-, h⟩ | ⟨-, h2, h3, -, -⟩
    · exact .inl h
    · exact .inr ⟨by omega, h3⟩

/-- The registers every part keeps: the stack pointer, the source, the header, the count, the buffer, the bound. -/
def JRegs (top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551456#64 ∧ R .x8 = regs .x11 ∧ R .x9 = regs .x10 ∧ (R .x18).toNat = cnt regs ∧
    R .x24 = vecPtr m (regs .x10) ∧ R .x27 = 0x0333333333333333#64

/-- The outer loop's head (instruction 66) with `k + 1` `Form`s left, from `Form` `j`. -/
def OInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  JRegs top regs m R ∧ ∃ j, j + k + 1 = cnt regs ∧ (R .x22).toNat = j ∧
    (R .x21).toNat = (vecLen m (regs .x10)).toNat + j ∧
    DoneT env M (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat j (env.next m).toNat (env.next M).toNat ∧
    MemOk env m top ret regs (SlotOut regs m) M

set_option rv_sym.heap true in
/-- **The join**, from instruction 186: `Form` `j`'s header stored at `P + 24 (l + j)`, then the next `Form` (66) or
    the return. -/
theorem join {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {H j k : Nat}
    (h66 : 0 < k → ∀ R M, OInv env m top ret regs (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, JRegs top regs m R → (R .x22).toNat = j → (R .x21).toNat = (vecLen m (regs .x10)).toNat + j →
      j + k + 1 = cnt regs → (R .x25).toNat * 40 < 2 ^ 63 →
      ((R .x10).toNat = 0 ∧ (R .x25).toNat = 0 ∨ R .x10 = R .x25 ∧ H ≤ (R .x23).toNat ∧
        (R .x23).toNat + 40 * (R .x25).toNat ≤ (env.next M).toNat ∧ (R .x23).toNat % 8 = 0 ∧
        TermsT env M (R .x23) (R .x25).toNat) →
      (env.next m).toNat ≤ H → H ≤ (env.next M).toNat →
      DoneT env M (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat j (env.next m).toNat H →
      MemOk env m top ret regs (SlotOut regs m) M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 186, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR h22 h21 hjk hL40 hnew hmH hH hdone hM
  have hlay := env.layout
  have hex := exit hp hL hk hA
  obtain ⟨hstk, hW, h16, -⟩ := id hA
  have := hW.nextAddr_ge
  have h176 : 176 ≤ top.toNat := by omega
  obtain ⟨b1, b2, b3, b4⟩ := hA.buf (by omega)
  have hnM := hM.2.1.2.1
  have eS : (R .x21 <<< 4 + R .x21 <<< 3).toNat = 24 * ((vecLen m (regs .x10)).toNat + j) := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq, h21]
    omega
  have eA : (vecPtr m (regs .x10) + (R .x21 <<< 4 + R .x21 <<< 3)).toNat =
      (vecPtr m (regs .x10)).toNat + 24 * ((vecLen m (regs .x10)).toNat + j) := by
    rw [BitVec.toNat_add, eS]; omega
  have hAw : vecPtr m (regs .x10) + (R .x21 <<< 4 + R .x21 <<< 3) =
      vecPtr m (regs .x10) + BitVec.ofNat 64 (24 * ((vecLen m (regs .x10)).toNat + j)) :=
    BitVec.eq_of_toNat_eq (by rw [eA, toNat_add_ofNat (by omega)])
  obtain ⟨m3, n3, d3⟩ := join_mem (A := vecPtr m (regs .x10) + (R .x21 <<< 4 + R .x21 <<< 3)) (c := R .x10)
    (Q := R .x23) (L := R .x25) hA h176 hM hAw (by omega) hmH hH hdone hL40 hnew
  have e22 : (R .x22 + 1#64).toNat = j + 1 := by rw [toNat_add_ofNat (by omega)]; omega
  have e21 : (R .x21 + 1#64).toNat = (vecLen m (regs .x10)).toNat + (j + 1) := by
    rw [toNat_add_ofNat (by omega)]; omega
  have h18 := hR.2.2.2.1
  have hcM : M.code = m.code := hM.2.2.2
  rv_introT hR
  rv_symT hp stop [66, 206] with [hL]
  · have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [e22, h18]; omega)) hc
      · exact h
    clear hc
    exact h66 hk0 _ _ ⟨⟨rfl, rfl, rfl, h18, rfl, rfl⟩, j + 1, by omega, e22, e21, d3, m3⟩
  · have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [e22, h18] at this; omega
    clear hc
    have hj1 : j + 1 = cnt regs := by omega
    rw [hj1] at d3 e21
    exact hex _ _ ⟨rfl, rfl⟩ e21 m3 d3

/-! ## The inner loop's memory -/

/-- **A call writing at most the clone's slot** (`top - 144` to `top - 120`): `MemOk` kept, every word apart from
    the slot below `NEXT` before the call or at or above the stack pointer kept. -/
theorem call_keep {env : Env} {m M M' : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (h176 : 176 ≤ top.toNat)
    (hM : MemOk env m top ret regs (SlotOut regs m) M)
    (hF : env.Frame (top + 18446744073709551456#64) out M M') (hSt : env.Static M') (hc : M'.code = M.code)
    (hout : ∀ b, out b → top.toNat - 144 ≤ b.toNat ∧ b.toNat < top.toNat - 120)
    (hkeep : ∀ a : Word, a.toNat < (env.next M).toNat ∨ (top + 18446744073709551456#64).toNat ≤ a.toNat → ¬ out a →
      M'.getMem a = M.getMem a) :
    MemOk env m top ret regs (SlotOut regs m) M' ∧ (env.next M).toNat ≤ (env.next M').toNat ∧
      ∀ a : Word, (a.toNat < (env.next M).toNat ∨ top.toNat - 160 ≤ a.toNat) →
        (a.toNat < top.toNat - 144 ∨ top.toNat - 120 ≤ a.toNat) → M'.getMem a = M.getMem a := by
  have hlay := env.layout
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  have e160 := es (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have hk : ∀ a : Word, (a.toNat < (env.next M).toNat ∨ top.toNat - 160 ≤ a.toNat) →
      (a.toNat < top.toNat - 144 ∨ top.toNat - 120 ≤ a.toNat) → M'.getMem a = M.getMem a := fun a h1 h2 =>
    hkeep a (by rw [e160]; exact h1) fun ho => by have := hout a ho; omega
  refine ⟨⟨slots_keep h176 (fun a h1 _ => hk a (.inr (by omega)) (.inr (by omega))) hsl,
    hF0.trans hF (by rw [e160]; omega) fun b hb => Or.inl (by have := hout b hb; omega), hSt, hc.trans hc0⟩,
    hF.1, hk⟩

/-- **The term's seven stores**: the clone's three words and the coefficient's two at `A = T + 40 t`, after two
    stores into the frame at `top - 120` and `top - 112`: `MemOk`, `NEXT`, the saved words at `top - 160` and
    `top - 152`, `DoneT` kept, `t + 1` terms. -/
theorem term_mem {env : Env} {m M : MachineState} {top ret A T P u1 u2 e0 e1 : Word} {regs : Reg → Word}
    {l j t FL H : Nat} (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (h176 : 176 ≤ top.toNat)
    (hM : MemOk env m top ret regs (SlotOut regs m) M)
    (hV : VecT env M (top + 18446744073709551472#64) 8) (hA : A.toNat = T.toNat + 40 * t) (ht : t < FL)
    (hTm : (env.next m).toNat ≤ T.toNat) (hHT : H ≤ T.toNat) (hT2 : T.toNat + 40 * FL ≤ (env.next M).toNat)
    (hT8 : T.toNat % 8 = 0) (hterms : TermsT env M T t) (hdone : DoneT env M P l j (env.next m).toNat H)
    (hP : P.toNat + 24 * (l + j) ≤ (env.next m).toNat) (hge : 0x10000000 ≤ (env.next m).toNat) :
    let M7 := (((((((M.setMem (top + 18446744073709551496#64) u1).setMem (top + 18446744073709551504#64) u2).setMem A
      (M.getMem (top + 18446744073709551472#64))).setMem (A + 8#64) (M.getMem (top + 18446744073709551480#64))).setMem
      (A + 16#64) (M.getMem (top + 18446744073709551488#64))).setMem (A + 24#64) e0).setMem (A + 32#64) e1)
    MemOk env m top ret regs (SlotOut regs m) M7 ∧ env.next M7 = env.next M ∧
      M7.getMem (top + 18446744073709551456#64) = M.getMem (top + 18446744073709551456#64) ∧
      M7.getMem (top + 18446744073709551464#64) = M.getMem (top + 18446744073709551464#64) ∧
      TermsT env M7 T (t + 1) ∧ DoneT env M7 P l j (env.next m).toNat H := by
  intro M7
  have hlay := env.layout
  have hnM := hM.2.1.2.1
  have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => es hc (by omega)
  have e120 := e 18446744073709551496#64 120 rfl (by omega)
  have e112 := e 18446744073709551504#64 112 rfl (by omega)
  have e144 := e 18446744073709551472#64 144 rfl (by omega)
  have e136 := e 18446744073709551480#64 136 rfl (by omega)
  have e128 := e 18446744073709551488#64 128 rfl (by omega)
  have e160 := e 18446744073709551456#64 160 rfl (by omega)
  have e152 := e 18446744073709551464#64 152 rfl (by omega)
  have hs144 : (top + 18446744073709551472#64 + 8#64) = top + 18446744073709551480#64 := by
    rw [BitVec.add_assoc]; rfl
  have hs128 : (top + 18446744073709551472#64 + 16#64) = top + 18446744073709551488#64 := by
    rw [BitVec.add_assoc]; rfl
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  have e24 : (A + 24#64).toNat = A.toNat + 24 := toNat_add_ofNat (by omega)
  have e32 : (A + 32#64).toNat = A.toNat + 32 := toNat_add_ofNat (by omega)
  obtain ⟨m1, n1, k1⟩ := frame_store (a := top + 18446744073709551496#64) (v := u1) hlim h176 hM (by omega)
    (by omega)
  obtain ⟨m2, n2, k2⟩ := frame_store (a := top + 18446744073709551504#64) (v := u2) hlim h176 m1 (by omega)
    (by omega)
  obtain ⟨m3, n3, k3⟩ := heap_store (a := A) (v := M.getMem (top + 18446744073709551472#64)) hlim h176 m2 (by omega)
    (by rw [n2, n1]; omega)
  obtain ⟨m4, n4, k4⟩ := heap_store (a := A + 8#64) (v := M.getMem (top + 18446744073709551480#64)) hlim h176 m3
    (by omega) (by rw [n3, n2, n1]; omega)
  obtain ⟨m5, n5, k5⟩ := heap_store (a := A + 16#64) (v := M.getMem (top + 18446744073709551488#64)) hlim h176 m4
    (by omega) (by rw [n4, n3, n2, n1]; omega)
  obtain ⟨m6, n6, k6⟩ := heap_store (a := A + 24#64) (v := e0) hlim h176 m5 (by omega)
    (by rw [n5, n4, n3, n2, n1]; omega)
  obtain ⟨m7, n7, k7⟩ := heap_store (a := A + 32#64) (v := e1) hlim h176 m6 (by omega)
    (by rw [n6, n5, n4, n3, n2, n1]; omega)
  have hN : env.next M7 = env.next M := by rw [n7, n6, n5, n4, n3, n2, n1]
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hk : ∀ b : Word, b.toNat ≠ top.toNat - 120 → b.toNat ≠ top.toNat - 112 →
      (b.toNat < A.toNat ∨ A.toNat + 40 ≤ b.toNat) → M7.getMem b = M.getMem b := fun b h1 h2 h3 => by
    rw [k7 b (ne _ _ (by omega)), k6 b (ne _ _ (by omega)), k5 b (ne _ _ (by omega)), k4 b (ne _ _ (by omega)),
      k3 b (ne _ _ (by omega)), k2 b (ne _ _ (by omega)), k1 b (ne _ _ (by omega))]
  have hvA : VecT env M7 A 8 := by
    refine vecT_copy hV (.inl ⟨by omega, by omega⟩) (by omega) (by rw [hN]) ?_ ?_ ?_
    · rw [k7 _ (ne _ _ (by omega)), k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)),
        MachineState.getMem_setMem_eq]
    · rw [hs144, k7 _ (ne _ _ (by omega)), k6 _ (ne _ _ (by omega)), k5 _ (ne _ _ (by omega)),
        MachineState.getMem_setMem_eq]
    · rw [hs128, k7 _ (ne _ _ (by omega)), k6 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  refine ⟨m7, hN, hk _ (by omega) (by omega) (by omega), hk _ (by omega) (by omega) (by omega), fun s hs => ?_,
    DoneT.keep hdone (by omega) (by rw [hN]) fun b hb => hk b (by omega) (by omega) (by omega)⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | hs
  · have hT := hterms s hs
    refine vecT_keep hT (by rw [hN]) fun b h1 h2 => ?_
    rw [toNat_add_ofNat (by omega)] at h1 h2
    exact hk b (by omega) (by omega) (by omega)
  · have eA : T + BitVec.ofNat 64 (40 * s) = A := BitVec.eq_of_toNat_eq (by rw [toNat_add_ofNat (by omega)]; omega)
    rw [eA]; exact hvA

/-! ## The inner loop: one term cloned -/

/-- The registers the inner loop keeps: the stack pointer, the source, the header, the count. -/
def KRegs (top : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551456#64 ∧ R .x8 = regs .x11 ∧ R .x9 = regs .x10 ∧ (R .x18).toNat = cnt regs

/-- The inner loop's registers and memory with `t` terms of the source `Form` at `a` done and `q` left, its clone's
    terms' block `T`. -/
def TInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (H j : Nat) (a T : Word) (t q : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  KRegs top regs R ∧ (R .x22).toNat = j ∧ (R .x21).toNat = (vecLen m (regs .x10)).toNat + j ∧
    R .x25 = vecLen m a ∧ R .x23 = T ∧ (R .x20).toNat = 40 * q ∧
    (R .x27).toNat = (vecPtr m a).toNat + 40 * (vecLen m a).toNat ∧
    M.getMem (top + 18446744073709551456#64) = 0x0333333333333333#64 ∧
    M.getMem (top + 18446744073709551464#64) = vecPtr m (regs .x10) ∧
    H ≤ T.toNat ∧ T.toNat + 40 * (vecLen m a).toNat ≤ (env.next M).toNat ∧ T.toNat % 8 = 0 ∧
    DoneT env M (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat j (env.next m).toNat H ∧
    MemOk env m top ret regs (SlotOut regs m) M ∧
    t + q = (vecLen m a).toNat ∧ (R .x26).toNat = (vecPtr m a).toNat + 40 * t ∧
    (R .x19).toNat = T.toNat + 40 * t ∧ TermsT env M T t

/-- The inner loop's head (instruction 124) with `q` terms left. -/
def IInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (H j : Nat) (a T : Word) (q : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  ∃ t, TInv env m top ret regs H j a T t q R M

set_option rv_sym.heap true in
/-- **The inner loop's back edge** (instruction 168, `x24` the next term): the head again (124), or the join once
    the last term is done. -/
theorem back {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {a T : Word} {H j k t q : Nat}
    (hjk : j + k + 1 = cnt regs) (hmH : (env.next m).toNat ≤ H) (hFL40 : (vecLen m a).toNat * 40 < 2 ^ 63)
    (h66 : 0 < k → ∀ R M, OInv env m top ret regs (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩)
    (h124 : ∀ R M, IInv env m top ret regs H j a T q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 124, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, R .x24 = R .x26 → TInv env m top ret regs H j a T t q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 168, ret, top⟩ :: rest, R, M⟩ := by
  intro R M h24 hI
  have hJ := join hp hL hk hA h66 (H := H) (j := j) (k := k)
  obtain ⟨hR, h22, h21, h25, h23, h20, h27, s160, s152, hHT, hT2, hT8, hdone, hM, htq, h26, h19, hterms⟩ := hI
  obtain ⟨hstk, hW, h16, -⟩ := hA
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hR' := And.intro hR h24
  rv_introT hR'
  rv_symT hp stop [124, 186] with [hL]
  · have hq0 : q ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h26, h27]; omega))
    clear hc
    exact h124 _ _ ⟨t, ⟨rfl, rfl, rfl, hR.2.2.2⟩, h22, h21, h25, h23, h20, h27, s160, s152, hHT, hT2, hT8, hdone, hM,
      htq, h26, h19, hterms⟩
  · have hq0 : q = 0 := by have := congrArg BitVec.toNat hc; rw [h26, h27] at this; omega
    clear hc
    have hfl : t = (vecLen m a).toNat := by omega
    refine hJ _ _ ⟨rfl, rfl, rfl, hR.2.2.2, ?_, ?_⟩ h22 h21 hjk ?_ (.inr ⟨rfl, ?_, ?_, ?_, ?_⟩) hmH (by omega) hdone hM
    · simp only [Tactic.rf]; exact s152
    · simp only [Tactic.rf]; exact s160
    · simp only [Tactic.rf]; rw [h25]; exact hFL40
    · simp only [Tactic.rf]; rw [h23]; exact hHT
    · simp only [Tactic.rf]; rw [h23, h25]; exact hT2
    · simp only [Tactic.rf]; rw [h23]; exact hT8
    · simp only [Tactic.rf]; rw [h23, h25, ← hfl]; exact hterms

set_option rv_sym.heap true in
/-- **After the monomial's clone** (instruction 138): the term stored at `T + 40 t`, then the back edge. -/
theorem after {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {a T : Word} {H j k t q : Nat}
    (hjk : j + k + 1 = cnt regs) (hmH : (env.next m).toNat ≤ H) (hFL40 : (vecLen m a).toNat * 40 < 2 ^ 63)
    (hP1 : 0x10000000 ≤ (vecPtr m a).toNat)
    (hP2 : (vecPtr m a).toNat + 40 * (vecLen m a).toNat ≤ (env.next m).toNat) (hP8 : (vecPtr m a).toNat % 8 = 0)
    (h66 : 0 < k → ∀ R M, OInv env m top ret regs (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩)
    (h124 : ∀ R M, IInv env m top ret regs H j a T (q - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 124, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, (KRegs top regs R ∧ R .x24 = R .x26 + 40#64) → (R .x22).toNat = j →
      (R .x21).toNat = (vecLen m (regs .x10)).toNat + j → R .x25 = vecLen m a → R .x23 = T →
      (R .x20).toNat = 40 * q → (R .x27).toNat = (vecPtr m a).toNat + 40 * (vecLen m a).toNat →
      (R .x26).toNat = (vecPtr m a).toNat + 40 * t → (R .x19).toNat = T.toNat + 40 * t → t + q = (vecLen m a).toNat →
      0 < q → M.getMem (top + 18446744073709551456#64) = 0x0333333333333333#64 →
      M.getMem (top + 18446744073709551464#64) = vecPtr m (regs .x10) →
      H ≤ T.toNat → T.toNat + 40 * (vecLen m a).toNat ≤ (env.next M).toNat → T.toNat % 8 = 0 →
      DoneT env M (vecPtr m (regs .x10)) (vecLen m (regs .x10)).toNat j (env.next m).toNat H →
      MemOk env m top ret regs (SlotOut regs m) M → TermsT env M T t → VecT env M (top + 18446744073709551472#64) 8 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 138, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR h22 h21 h25 h23 h20 h27 h26 h19 htq hq s160 s152 hHT hT2 hT8 hdone hM hterms hV
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, -⟩ := id hA
  have := hW.nextAddr_ge
  have h176 : 176 ≤ top.toNat := by omega
  obtain ⟨b1, b2, b3, b4⟩ := hA.buf (by omega)
  have hge := hW.next_ge
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hcM : M.code = m.code := hM.2.2.2
  have hW1 := hW.heapEnd_le
  have hTm : (env.next m).toNat ≤ T.toNat := by omega
  obtain ⟨m7, n7, s160', s152', ht7, hd7⟩ := term_mem (A := R .x19) (u1 := M.getMem (R .x26 + 24#64))
    (u2 := M.getMem (R .x26 + 32#64)) (e0 := M.getMem (R .x26 + 24#64)) (e1 := M.getMem (R .x26 + 32#64)) hstk h176
    hM hV h19 (by omega : t < (vecLen m a).toNat) hTm hHT hT2 hT8 hterms hdone (by omega) hge
  have w24 : (R .x26 + 24#64).toNat = (R .x26).toNat + 24 := toNat_add_ofNat (by omega)
  have w32 : (R .x26 + 32#64).toNat = (R .x26).toNat + 32 := toNat_add_ofNat (by omega)
  have v8 : (R .x19 + 8#64).toNat = (R .x19).toNat + 8 := toNat_add_ofNat (by omega)
  have v16 : (R .x19 + 16#64).toNat = (R .x19).toNat + 16 := toNat_add_ofNat (by omega)
  have v24 : (R .x19 + 24#64).toNat = (R .x19).toNat + 24 := toNat_add_ofNat (by omega)
  have v32 : (R .x19 + 32#64).toNat = (R .x19).toNat + 32 := toNat_add_ofNat (by omega)
  have e19 : (R .x19 + 40#64).toNat = T.toNat + 40 * (t + 1) := by rw [toNat_add_ofNat (by omega)]; omega
  have e26 : (R .x26 + 40#64).toNat = (vecPtr m a).toNat + 40 * (t + 1) := by
    rw [toNat_add_ofNat (by omega)]; omega
  have e20 : (R .x20 + 18446744073709551576#64).toNat = 40 * (q - 1) := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hback := back hp hL hk hA (t := t + 1) (q := q - 1) hjk hmH hFL40 h66 h124
  have h18 := hR.1.2.2.2
  clear hV hdone hterms
  rv_introT hR
  rv_symT hp stop [168] with [hL]
  exact hback _ _ rfl ⟨⟨rfl, rfl, rfl, h18⟩, h22, h21, h25, h23, e20, h27, s160'.trans s160, s152'.trans s152, hHT,
    by rw [n7]; exact hT2, hT8, hd7, m7, by omega, e26, e19, ht7⟩

set_option rv_sym.heap true in
/-- **The inner loop**, from its head to the join. -/
theorem inner {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hnC : 160 + needC ≤ need) (hcl : CloneSpecT env 8 p L.clone.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) {a T : Word} {H j k : Nat}
    (hjk : j + k + 1 = cnt regs) (hmH : (env.next m).toNat ≤ H) (hFa : FormT env m a)
    (hag : ∀ b : Word, (vecPtr m a).toNat ≤ b.toNat → b.toNat < (vecPtr m a).toNat + 40 * (vecLen m a).toNat →
      ¬ SlotOut regs m b)
    (h66 : 0 < k → ∀ R M, OInv env m top ret regs (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩) :
    ∀ q R M, IInv env m top ret regs H j a T q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 124, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (IInv env m top ret regs H j a T) fun q R M hI ih => ?_
  have hlay := env.layout
  have hJ := join hp hL hk hA h66 (H := H) (j := j) (k := k)
  have hFL40 : (vecLen m a).toNat * 40 < 2 ^ 63 := by
    have := (vecT_buf hFa.1).2; have := Nat.mul_le_mul_right 40 this.1; omega
  obtain ⟨hstk, hW, h16, -⟩ := id hA
  obtain ⟨t, hR, h22, h21, h25, h23, h20, h27, s160, s152, hHT, hT2, hT8, hdone, hM, htq, h26, h19, hterms⟩ := id hI
  clear hI
  have := hW.nextAddr_ge
  have h18 := hR.2.2.2
  rcases Nat.eq_zero_or_pos q with hq | hq
  · -- no term left: to the join
    clear hFa
    have hx : R .x20 = 0#64 := BitVec.eq_of_toNat_eq (by rw [h20, hq]; rfl)
    have hfl : t = (vecLen m a).toNat := by omega
    have hR' := And.intro hR hx
    rv_introT hR'
    rv_symT hp stop [186] with [hL]
    refine hJ _ _ ⟨rfl, rfl, rfl, h18, ?_, ?_⟩ h22 h21 hjk ?_ (.inr ⟨rfl, ?_, ?_, ?_, ?_⟩) hmH (by omega) hdone hM
    · simp only [Tactic.rf]; exact s152
    · simp only [Tactic.rf]; exact s160
    · simp only [Tactic.rf]; rw [h25]; exact hFL40
    · simp only [Tactic.rf]; rw [h23]; exact hHT
    · simp only [Tactic.rf]; rw [h23, h25]; exact hT2
    · simp only [Tactic.rf]; rw [h23]; exact hT8
    · simp only [Tactic.rf]; rw [h23, h25, ← hfl]; exact hterms
  · have hFL : 0 < (vecLen m a).toNat := by omega
    obtain ⟨hP1, hP2, hP8⟩ := hFa.foot.resolve_left (by omega)
    have hafter := after hp hL hk hA (T := T) (t := t) (q := q) hjk hmH hFL40 hP1 hP2 hP8 h66
      (fun R' M' h => ih (q - 1) R' M' (by omega) h)
    have hx26 : R .x26 = vecPtr m a + BitVec.ofNat 64 (40 * t) :=
      BitVec.eq_of_toNat_eq (by rw [h26, toNat_add_ofNat (by omega)])
    have hnm := hM.2.1.1
    have hnM := hM.2.1.2.1
    have hW1 := hW.heapEnd_le
    have hSt : env.Static M := hM.2.2.1
    have hcM : M.code = m.code := hM.2.2.2
    have h176 : 176 ≤ top.toNat := by omega
    obtain ⟨b1, b2, b3, b4⟩ := hA.buf (by omega)
    have w8 : (R .x26 + 8#64).toNat = (R .x26).toNat + 8 := toNat_add_ofNat (by omega)
    have w16 : (R .x26 + 16#64).toNat = (R .x26).toNat + 16 := toNat_add_ofNat (by omega)
    have ag : ∀ b : Word, (vecPtr m a).toNat ≤ b.toNat → b.toNat < (vecPtr m a).toNat + 40 * (vecLen m a).toNat →
        M.getMem b = m.getMem b := fun b h1 h2 =>
      keepF hM.2.1 (by omega) (.inl (by omega)) (hag b h1 h2)
    have hBt : BufT env M (M.getMem (R .x26 + 16#64)) (M.getMem (R .x26 + 8#64)) 8 := by
      have hv := (vecT_buf (hFa.2 t (by omega))).1
      rw [← hx26, vecLen_eq, vecPtr_eq] at hv
      rw [ag _ (by omega) (by omega), ag _ (by omega) (by omega)]
      exact hv.mono hnm
    clear hFa ag hag
    rv_introT hR
    rv_symT hp stop [138, 186] with [hL] using [hcl]
    · exact absurd (congrArg BitVec.toNat hc) (by rw [h20]; simp only [BitVec.toNat_ofNat]; omega)
    · -- after the clone
      have e144 := es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
      have e160 := es (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
      have e152 := es (top := top) (c := 18446744073709551464#64) (k := 152) rfl (by omega)
      obtain ⟨hM1, hn1, hk1⟩ := call_keep hstk h176 hM hret1_14 hret1_15 hret1_24 (fun b hb => by
        obtain ⟨h1, h2⟩ := hb
        change (top + 18446744073709551472#64).toNat ≤ b.toNat at h1
        change b.toNat < (top + 18446744073709551472#64).toNat + 24 at h2
        omega) keep1_2
      refine hafter _ _ ⟨⟨rfl, rfl, rfl, h18⟩, rfl⟩ h22 h21 h25 h23 h20 h27 h26 h19 htq hq ?_ ?_ hHT (by omega) hT8
        ?_ hM1 ?_ ?_
      · rw [hk1 _ (.inr (by omega)) (.inl (by omega))]; exact s160
      · rw [hk1 _ (.inr (by omega)) (.inl (by omega))]; exact s152
      · exact DoneT.keep hdone (by omega) hn1 fun b hb => hk1 b (.inl (by omega)) (.inl (by omega))
      · exact TermsT.keep hterms (by omega) hn1 fun b h1 h2 => hk1 b (.inl (by omega)) (.inl (by omega))
      · exact ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩

/-! ## The outer loop: one `Form` cloned -/

/-- **The source's `Form` `j`**: a `Form` at entry, its header below `NEXT` or at or above the stack top, its header
    and its terms' block apart from the new `Form`s' slots. -/
theorem Args.src {env : Env} {m : MachineState} {top : Word} {regs : Reg → Word} (hA : Args env m top regs) {j : Nat}
    (hj : j < cnt regs) :
    FormT env m (regs .x11 + BitVec.ofNat 64 (24 * j)) ∧
      (regs .x11 + BitVec.ofNat 64 (24 * j)).toNat = (regs .x11).toNat + 24 * j ∧
      ((regs .x11).toNat + 24 * j + 24 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x11).toNat + 24 * j) ∧
      (∀ b : Word, (regs .x11).toNat + 24 * j ≤ b.toNat → b.toNat < (regs .x11).toNat + 24 * j + 24 →
        ¬ SlotOut regs m b) ∧
      (∀ b : Word, (vecPtr m (regs .x11 + BitVec.ofNat 64 (24 * j))).toNat ≤ b.toNat →
        b.toNat < (vecPtr m (regs .x11 + BitVec.ofNat 64 (24 * j))).toNat +
          40 * (vecLen m (regs .x11 + BitVec.ofNat 64 (24 * j))).toNat → ¬ SlotOut regs m b) := by
  have hlay := env.layout
  obtain ⟨hstk, hW, -, h2, -, -, -, -, h11, -, -, hsrc, hF, hTA⟩ := id hA
  obtain ⟨hoff, hnx, hsp⟩ := hsrc.resolve_left (by omega)
  have hFj := hF j hj
  have hw := hFj.1.1
  unfold InWin at hw
  simp only [Layouts.Vec.byteSize] at hw
  have hlt : (regs .x11).toNat + 24 * cnt regs ≤ (regs .x12).toNat := by unfold cnt; omega
  have := (regs .x12).isLt
  have e : (regs .x11 + BitVec.ofNat 64 (24 * j)).toNat = (regs .x11).toNat + 24 * j :=
    toNat_add_ofNat (by omega)
  rw [e] at hw
  unfold OffStack at hoff
  rw [h2] at hoff
  have hbelow : (regs .x11).toNat + 24 * j + 24 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x11).toNat + 24 * j := by
    rcases hw with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;> rcases hnx with h4 | h4 <;> rcases hoff with h5 | h5 <;> omega
  refine ⟨hFj, e, hbelow, fun b h1 h3 hs => ?_, fun b h1 h3 hs => ?_⟩
  · obtain ⟨s1, s2⟩ := hs
    unfold spareLo spareHi at *
    rcases hsp with h | h
    · omega
    · have := hA.buf (by omega)
      omega
  · obtain ⟨s1, s2⟩ := hs
    have hroom := (hA.buf (by omega)).2.2.2
    rcases hTA j hj with h0 | h4 | h4
    · omega
    · omega
    · unfold spareLo spareHi at *; omega

set_option rv_sym.heap true in
/-- **The outer loop**, from its head to the return. -/
theorem outer {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needC needH : Nat} (hnA : 160 + needA ≤ need) (hnC : 160 + needC ≤ need)
    (hnH : 160 + needH ≤ need)
    (hal : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hcl : CloneSpecT env 8 p L.clone.idx needC) (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) :
    ∀ k R M, OInv env m top ret regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env m top ret regs) fun k R M hI ih => ?_
  have hlay := env.layout
  have h66 : 0 < k → ∀ R M, OInv env m top ret regs (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩ := fun hk0 R' M' h => ih (k - 1) R' M'
    (by omega) h
  obtain ⟨hR, j, hjk, h22, h21, hdone, hM⟩ := hI
  obtain ⟨hstk, hW, h16, -⟩ := id hA
  obtain ⟨hFa, ea, hbel, hhdr, hag⟩ := hA.src (j := j) (by omega)
  obtain ⟨b1, b2, b3, b4⟩ := hA.buf (by omega)
  have := hW.nextAddr_ge
  have h176 : 176 ≤ top.toNat := by omega
  have eS : (R .x22 <<< 4 + R .x22 <<< 3).toNat = 24 * j := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq, h22]
    omega
  have ha : regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) = regs .x11 + BitVec.ofNat 64 (24 * j) := by
    rw [BitVec.eq_of_toNat_eq (x := R .x22 <<< 4 + R .x22 <<< 3) (y := BitVec.ofNat 64 (24 * j)) (by
      rw [eS, BitVec.toNat_ofNat]; omega)]
  have hFL40 : (vecLen m (regs .x11 + BitVec.ofNat 64 (24 * j))).toNat * 40 < 2 ^ 63 := by
    have := (vecT_buf hFa.1).2; have := Nat.mul_le_mul_right 40 this.1; omega
  have hlt := vecT_lt hFa.1
  have hnm := hM.2.1.1
  have hnM := hM.2.1.2.1
  have hW1 := hW.heapEnd_le
  have hSt : env.Static M := hM.2.2.1
  have hcM : M.code = m.code := hM.2.2.2
  have w8 : (regs .x11 + BitVec.ofNat 64 (24 * j) + 8#64).toNat = (regs .x11).toNat + 24 * j + 8 := by
    rw [toNat_add_ofNat (by omega), ea]
  have w16 : (regs .x11 + BitVec.ofNat 64 (24 * j) + 16#64).toNat = (regs .x11).toNat + 24 * j + 16 := by
    rw [toNat_add_ofNat (by omega), ea]
  have ag8 : M.getMem (regs .x11 + BitVec.ofNat 64 (24 * j) + 8#64) =
      vecPtr m (regs .x11 + BitVec.ofNat 64 (24 * j)) :=
    keepF hM.2.1 (by omega) (by rw [w8]; omega) (hhdr _ (by omega) (by omega))
  have ag16 : M.getMem (regs .x11 + BitVec.ofNat 64 (24 * j) + 16#64) =
      vecLen m (regs .x11 + BitVec.ofNat 64 (24 * j)) :=
    keepF hM.2.1 (by omega) (by rw [w16]; omega) (hhdr _ (by omega) (by omega))
  have hin := fun T => inner hp hL hnC hcl hk hstop hneed hA (a := regs .x11 + BitVec.ofNat 64 (24 * j)) (T := T)
    (H := (env.next M).toNat) hjk hnm hFa hag h66
  have hJ := join hp hL hk hA h66 (H := (env.next M).toNat) (j := j) (k := k)
  rw [← ha] at ag8 ag16 hFL40
  have hFLn : (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat * 40 < 2 ^ 63 := by
    rw [ag16]; exact hFL40
  have s40 : (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64) <<< 5 +
      M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64) <<< 3).toNat =
      40 * (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega
  have sh : M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64) <<< 3 >>> 3 =
      M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have e160 := es (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have h18 := hR.2.2.2.1
  rv_introT hR
  rv_symT hp stop [124, 186] with [hL] using [hal, hhe]
  · -- no terms, no block
    have hF0 : (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat = 0 := by
      have := congrArg BitVec.toNat hc; rw [s40] at this; simp only [BitVec.toNat_ofNat] at this; omega
    clear hc
    exact hJ _ _ ⟨rfl, rfl, rfl, h18, rfl, rfl⟩ h22 h21 hjk hFLn (.inl ⟨rfl, hF0⟩) hnm (Nat.le_refl _) hdone hM
  · -- after `alloc`, no terms
    have hF0 : (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat = 0 := by rw [hc]; rfl
    clear hc
    obtain ⟨hM2, hn2, hk2⟩ := call_keep hstk h176 hM hret2_14 hret2_15 hret2_19 (fun b hb => hb.elim)
      (fun a h _ => keep2_2 a h)
    exact hJ _ _ ⟨rfl, rfl, rfl, h18, rfl, rfl⟩ h22 h21 hjk hFLn (.inl ⟨rfl, hF0⟩) hnm hn2
      (DoneT.keep hdone (by omega) hn2 fun b hb => hk2 b (.inl (by omega)) (.inl (by omega))) hM2
  · -- `min(n, n - 1)` is `n`: not reached
    have hF1 : (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat ≠ 0 :=
      fun h => hc_4 (BitVec.eq_of_toNat_eq h)
    rw [sh, BitVec.lt_def, BitVec.toNat_add] at hc
    simp only [BitVec.toNat_ofNat] at hc
    omega
  · -- into the inner loop
    have hF1 : (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat ≠ 0 :=
      fun h => hc_4 (BitVec.eq_of_toNat_eq h)
    clear hc
    have hLa : (vecLen m (regs .x11 + BitVec.ofNat 64 (24 * j))).toNat ≠ 0 := by
      have := ag16; rw [ha] at this; rw [← this, ← ha]; exact hF1
    obtain ⟨-, hP2, -⟩ := hFa.foot.resolve_left hLa
    rw [← ha, ← ag8, ← ag16] at hP2
    have e1 : (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64) + 18446744073709551615#64).toNat =
        (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat - 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    have e27 : (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 8#64) +
        ((M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64) + 18446744073709551615#64) <<< 5 +
        (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64) + 18446744073709551615#64) <<< 3) +
        40#64).toNat =
        (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 8#64)).toNat +
          40 * (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq, Nat.shiftLeft_eq, e1]
      simp only [BitVec.toNat_ofNat]
      have : 2 ^ 5 * ((M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat - 1) +
        2 ^ 3 * ((M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat - 1) + 40 =
        40 * (M.getMem (regs .x11 + (R .x22 <<< 4 + R .x22 <<< 3) + 16#64)).toNat := by omega
      omega
    obtain ⟨hM2, hn2, hk2⟩ := call_keep hstk h176 hM hret2_14 hret2_15 hret2_19 (fun b hb => hb.elim)
      (fun a h _ => keep2_2 a h)
    have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
    have e152 := es (top := top) (c := 18446744073709551464#64) (k := 152) rfl (by omega)
    obtain ⟨m3, n3, k3⟩ := frame_store (a := top + 18446744073709551456#64) (v := 230584300921369395#64) hstk h176
      hM2 (by omega) (by omega)
    obtain ⟨m4, n4, k4⟩ := frame_store (a := top + 18446744073709551464#64) (v := vecPtr m (regs .x10)) hstk h176
      m3 (by omega) (by omega)
    have hN : env.next ((m2.setMem (top + 18446744073709551456#64) 230584300921369395#64).setMem
        (top + 18446744073709551464#64) (vecPtr m (regs .x10))) = env.next m2 := by rw [n4, n3]
    rw [s40] at hret2_18
    refine hin (r2 .x10) (vecLen m (regs .x11 + BitVec.ofNat 64 (24 * j))).toNat _ _ ⟨0, ⟨rfl, rfl, rfl, h18⟩,
      h22, h21, by rw [← ha]; exact ag16, rfl, by rw [← ha, ← ag16]; exact s40, ?_, ?_, MachineState.getMem_setMem_eq,
      hret2_16, by rw [hN, ← ha, ← ag16]; omega, hret2_17, ?_, m4, by omega, ?_, by simp only [Tactic.rf]; omega,
      fun t ht => absurd ht (Nat.not_lt_zero _)⟩
    · simp only [Tactic.rf]; rw [← ha, ← ag8, ← ag16]; exact e27
    · rw [k4 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
    · refine DoneT.keep hdone (by omega) (by rw [hN]; exact hn2) fun b hb => ?_
      rw [k4 _ (ne _ _ (by omega)), k3 _ (ne _ _ (by omega))]
      exact hk2 b (.inl (by omega)) (.inl (by omega))
    · simp only [Tactic.rf]; rw [← ha, ← ag8]; omega

/-! ## The entry -/

/-- The source's count, as the code computes it: `((a2 - a1) >> 3) * (3⁻¹ mod 2^64)`. -/
theorem cnt_toNat {regs : Reg → Word} (h1 : (regs .x11).toNat ≤ (regs .x12).toNat)
    (h2 : ((regs .x12).toNat - (regs .x11).toNat) % 24 = 0) :
    ((regs .x12 - regs .x11) >>> 3 * 12297829382473034411#64).toNat = cnt regs := by
  have e : (regs .x12 - regs .x11).toNat = (regs .x12).toNat - (regs .x11).toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.2 h1)
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e]
  have := (regs .x12).isLt
  simp only [BitVec.toNat_ofNat]
  unfold cnt
  omega

/-- A word off the frame is the entry's after the prologue. -/
theorem saved_get {m : MachineState} {top ret b : Word} {regs : Reg → Word} (h176 : 176 ≤ top.toNat)
    (hb : b.toNat + 8 ≤ top.toNat - 104 ∨ top.toNat ≤ b.toNat) : (saved m top ret regs).getMem b = m.getMem b := by
  have hne : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 104 → b ≠ top + c := fun c k hc h0 hk he => by
    have := congrArg BitVec.toNat he
    rw [es hc (by omega)] at this
    omega
  simp only [saved]
  rw [MachineState.getMem_setMem_ne (hne _ 104 rfl (by omega) le_rfl),
    MachineState.getMem_setMem_ne (hne _ 96 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 88 rfl (by omega) (by omega)),
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
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (h176 : 176 ≤ top.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hS : env.Static m) :
    MemOk env m top ret regs Tactic.F (saved m top ret regs) := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 160 → (top + c).toNat = top.toNat - k :=
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
  have e12 := g 18446744073709551520#64 96 rfl (by omega)
  have e13 := g 18446744073709551512#64 104 rfl (by omega)
  refine ⟨?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13] at h'; omega)])
  · simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  · simp only [saved]
    repeat (first | refine Env.static_setMem_stack ?_ (by omega) | exact hS)

/-- **After `reserve`**, which had room: `MemOk` with the new `Form`s' slots as `out` (its writes, to the header's
    capacity and pointer, keep their values), and every word below `NEXT` at entry or at or above the stack top the
    entry's. -/
theorem after_reserve {env : Env} {m m1 : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hA : Args env m top regs) (h176 : 176 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m)
    (hF1 : env.Frame (top + 18446744073709551456#64) out (saved m top ret regs) m1) (hS1 : env.Static m1)
    (hc1 : m1.code = (saved m top ret regs).code)
    (hout : ∀ b, out b → b = rvCapAt (regs .x10) ∨ b = rvPtrAt (regs .x10))
    (hcap : m1.getMem (regs .x10) = (saved m top ret regs).getMem (regs .x10))
    (hptr : m1.getMem (regs .x10 + 8#64) = (saved m top ret regs).getMem (regs .x10 + 8#64)) :
    MemOk env m top ret regs (SlotOut regs m) m1 ∧
      ∀ b : Word, (b.toNat < (env.next m).toNat ∨ top.toNat ≤ b.toNat) → m1.getMem b = m.getMem b := by
  have hlay := env.layout
  obtain ⟨hstk, hW, -⟩ := id hA
  obtain ⟨hhd1, hhd2⟩ := hA.hdr
  obtain ⟨hsl, hF0, -, hc0⟩ := saved_ok (ret := ret) (regs := regs) hstk h176 hnx hS
  have e160 := es (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have hn1 := hF1.1
  have hn0 := hF0.1
  have hn2 := hF1.2.1
  have hW1 := hW.heapEnd_le
  have := hW.nextAddr_ge
  have hgo : ∀ b, out b → m1.getMem b = m.getMem b := fun b hb => by
    rcases hout b hb with rfl | rfl
    · rw [rvCapAt_eq, hcap, saved_get h176 (.inr hhd1)]
    · rw [rvPtrAt_eq, hptr, saved_get h176 (.inr (by rw [toNat_add_ofNat (by omega)]; omega))]
  have hk' : ∀ a : Word, ¬ (env.stackLimit.toNat ≤ a.toNat ∧ a.toNat < top.toNat) →
      ¬ ((env.next m).toNat ≤ a.toNat ∧ a.toNat < (env.next m1).toNat) → a ≠ env.nextAddr →
      m1.getMem a = m.getMem a := fun a h1 h2 h3 => by
    by_cases ho : out a
    · exact hgo a ho
    · have e1 : m1.getMem a = (saved m top ret regs).getMem a := hF1.2.2 a fun hw => by
        rcases hw with hw | hw | hw | hw
        · exact h1 ⟨hw.1, by have := hw.2; rw [e160] at this; omega⟩
        · exact h2 ⟨by omega, hw.2⟩
        · exact h3 hw
        · exact ho hw
      rw [e1]
      exact hF0.2.2 a fun hw => by
        rcases hw with hw | hw | hw | hw
        · exact h1 hw
        · exact h2 ⟨hw.1, by omega⟩
        · exact h3 hw
        · exact hw
  refine ⟨⟨slots_keep h176 (fun b h1 h2 => ?_) hsl, ⟨by omega, hF1.2.1, fun a ha => hk' a
    (fun h => ha (.inl h)) (fun h => ha (.inr (.inl h))) (fun h => ha (.inr (.inr (.inl h))))⟩, hS1, hc1.trans hc0⟩,
    fun b hb => hk' b (by omega) (by omega) fun e => by rw [e] at hb; omega⟩
  exact hF1.2.2 b fun hw => by
    rcases hw with hw | hw | hw | hw
    · have := hw.2; rw [e160] at this; omega
    · have := hF1.2.1; omega
    · rw [hw] at h1; omega
    · rcases hout b hw with rfl | rfl
      · rw [rvCapAt_eq] at h2; omega
      · rw [rvPtrAt_eq, toNat_add_ofNat (by omega)] at h2; omega

set_option rv_sym.heap true in
/-- **`Vec<Form>::spec_extend` from a slice is total**, with 160 bytes of stack beyond its callees', given its
    bound's word in the static data. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hd : DataRef.InData env [(L.d_c8_51ab739d, d_c8_51ab739d_words)])
    {need needR needA needC needH : Nat} (hnR : 160 + needR ≤ need) (hnA : 160 + needA ≤ need)
    (hnC : 160 + needC ≤ need) (hnH : 160 + needH ≤ need)
    (hres : ReserveSpecT env 8 24 p L.reserve.idx needR) (hal : AllocSpecT env p L.alloc.idx needA)
    (hcl : CloneSpecT env 8 p L.clone.idx needC) (hhe : Aborts env p L.handleError.idx needH) :
    SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hw1 := hd.words (List.mem_cons_self ..)
  rv_autoT hp stop [66, 206] with [hL, hw1] using [hres]
  all_goals
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 160 ≤ top.toNat := by omega
    have h176 : 176 ≤ top.toNat := by have := hpre_23.nextAddr_ge; omega
    have hA : Args env m top regs := ⟨hlim, hpre_23, hpre_22, hpre_2, ⟨hpre_6, ⟨hpre_7, hpre_8, hpre_9, hpre_10⟩,
      hpre_11⟩, ⟨hpre_12, hpre_13⟩, hpre_14, hpre_15, hpre_16, hpre_17, hpre_18, hpre_19, hpre_20, hpre_21⟩
    have hx8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
    have hx16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
    have hcap0 : (saved m top ret regs).getMem (regs .x10) = m.getMem (regs .x10) :=
      saved_get h176 (.inr (by rw [← hpre_2]; exact hpre_12))
    have hptr0 : (saved m top ret regs).getMem (regs .x10 + 8#64) = m.getMem (regs .x10 + 8#64) :=
      saved_get h176 (.inr (by rw [← hpre_2, hx8]; omega))
    have hlen0 : (saved m top ret regs).getMem (regs .x10 + 16#64) = m.getMem (regs .x10 + 16#64) :=
      saved_get h176 (.inr (by rw [← hpre_2, hx16]; omega))
    have hSn : (saved m top ret regs).getMem env.nextAddr = m.getMem env.nextAddr :=
      saved_get h176 (.inl (by omega))
    simp only [saved] at hcap0 hptr0 hlen0 hSn
  -- `reserve`'s precondition, read through the prologue's stores
  all_goals try
    simp only [rvCapAt_eq, rvPtrAt_eq, hcap0, hptr0, Env.Live, Env.next, hSn] at hpre_9 hpre_10 hpre_11 ⊢
    first
    | exact hpre_9
    | exact hpre_10
    | exact hpre_9.imp id fun h => h.2.1
    | (rwa [vecLen_eq, vecCap_eq] at hpre_11)
  all_goals try exact (data_ok hpre_23 hd (List.mem_cons_self ..) (by decide)).1
  all_goals try exact (data_ok hpre_23 hd (List.mem_cons_self ..) (by decide)).2
  -- after `reserve`
  all_goals
    have hn : ((regs .x12 - regs .x11) >>> 3 * 12297829382473034411#64).toNat = cnt regs := cnt_toNat hpre_16 hpre_17
    have h18 := hpre_18
    rw [vecCap_eq, vecLen_eq] at h18
    have hroom := hret1_17 (by
      rw [hn, vecCap_eq, vecLen_eq, hcap0, hlen0]
      omega)
    have hcap : m1.getMem (regs .x10) = (saved m top ret regs).getMem (regs .x10) := by
      have := hroom.1; rwa [vecCap_eq, vecCap_eq] at this
    have hptr : m1.getMem (regs .x10 + 8#64) = (saved m top ret regs).getMem (regs .x10 + 8#64) := hroom.2
    obtain ⟨hM1, hk1⟩ := after_reserve hA h176 hpre_5 hpre_4 hret1_14 hret1_15 hret1_25 (fun b hb => hb) hcap hptr
    have hl1 : m1.getMem (regs .x10 + 16#64) = vecLen m (regs .x10) := hk1 _ (.inr (by rw [hx16, ← hpre_2]; omega))
    have hp1 : m1.getMem (regs .x10 + 8#64) = vecPtr m (regs .x10) := hk1 _ (.inr (by rw [hx8, ← hpre_2]; omega))
  · -- `a1 = a2`: no `Form`s
    have hn0 : cnt regs = 0 := by unfold cnt; rw [hc]; simp
    exact exit hp hL hk hA _ _ ⟨rfl, rfl⟩ (by simp only [Tactic.rf]; rw [hl1, hn0]; rfl) hM1
      fun _ h => absurd h (by omega)
  · -- into the outer loop
    have hn0 : 0 < cnt regs := by
      have : (regs .x12).toNat ≠ (regs .x11).toNat := fun h => hc (BitVec.eq_of_toNat_eq h)
      unfold cnt; omega
    exact outer hp hL hnA hnC hnH hal' hcl hhe hk hstop hpre_3 hA (cnt regs - 1) _ _
      ⟨⟨rfl, rfl, rfl, hn, hp1, rfl⟩, 0, by omega, rfl, by simp only [Tactic.rf]; rw [hl1]; rfl,
        fun _ h => absurd h (by omega), hM1⟩

end Rv64mc.Proof.Layout.SpecExtendFormT

/-- info: 'Rv64mc.Proof.Layout.SpecExtendFormT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.SpecExtendFormT.total
