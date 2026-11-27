/-
  Rv64mc.Proof.Layout.FromElemVecFormT

  `<Vec<Form> as SpecFromElem>::from_elem` (`vec![v; n]`: `sret` in `a0`, the element `Vec<Form>`'s header at `a1`,
  `n` in `a2`) is total: for `n = 0` it drops the element and returns the empty vector; otherwise it allocates the
  result's block (`alloc(24 n)`), stores `n - 1` clones of the element (`<Vec<Form> as Clone>::clone`, through
  `CloneFormsFreshT`'s contract) and moves the element into the last slot. Its result is a vector of `n` `Vec<Form>`s
  (`VecFormT`: each a vector of `Form`s, `FormReprT.FormsT`), its buffer fresh unless empty; the elements' buffers
  apart from it and from each other, and each element's `Form`s of capacity `0` if the element's are (`ElemsT`), what
  a caller writing into one element's `Form`s (`verify_bus_balance` through `add_scaled`) needs to keep the others;
  the run ends with the guest's abort (`AbortStop`) where `alloc`, `clone` or `handle_error` does. A safety-only
  contract (class D).

  The precondition: the result's slot in the caller's frame (at or above the stack pointer, so apart from every heap
  block the result's elements use), in a window and 8-byte aligned; the element a `Vec<Form>` its caller owns; `24 n`
  below `2^63` (the code does not check it). The clones' `Form`s must lie in blocks allocated by each clone
  (`CloneFormsFreshT.FreshTermsT`): the code stores each clone's header into the result's block, allocated before,
  and `FormsT` reads the `Form`s' terms' blocks.

  The body is cut at the loop's head (instruction 60, measure the clones left, `LInv`), after the clone (70,
  `after`), the move (86), the result's header (114, `fin`) and the epilogue (120, `exit`). The clones stored so
  far (`DoneV`) lie, buffers and terms' blocks, between the result's block's end and `NEXT` (`FootV`), so the later
  stores into the block and the later clones keep them (`vecForm_keep`); each clone's buffer is allocated after the
  earlier ones', so their buffers are apart (`BufApart`), and the moved element's lies below the result's block. A
  clone's `Form`s have its source's lengths as capacities (`CloneFormsFreshT.CapsT`), `0` where the element's
  `Form`s have capacity `0`.

  ## Main definitions

  * `VecFormT`, `EmptyFormsT`, `BufApart`, `ElemsT`, `PreT`, `PostT`, `SpecT`, `Slots`, `MemOk`, `FootV`, `DoneV`,
    `LInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.CloneFormsFreshT
import Rv64mc.Proof.Layout.PairT
import Rv64mc.Proof.Runtime.DropT
import Rv64mc.Gen.Tmpl.Alloc.Vec.SpecFromElem.VecForm.AsSpecFromElem.FromElemGlobal

namespace Rv64mc.Proof.Layout.FromElemVecFormT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.DropT (DropSpecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Proof.Layout.PairT (Apart)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Alloc.Vec.SpecFromElem.VecForm.AsSpecFromElem.FromElemGlobal (Link tmpl)

/-- **The `Vec<Form>` at `a`**: a vector of 24-byte `Form` headers, each a `Form`. -/
def VecFormT (env : Env) (m : MachineState) (a : Word) : Prop :=
  VecT env m a 24 ∧ FormsT env m (vecPtr m a) (vecLen m a).toNat

/-- **The `Vec<Form>` at `a` holds only empty `Form`s**: each of capacity `0`. -/
def EmptyFormsT (M : MachineState) (a : Word) : Prop :=
  ∀ k, k < (vecLen M a).toNat → vecCap M (vecPtr M a + BitVec.ofNat 64 (24 * k)) = 0#64

/-- **The buffers of the `Vec<Form>`s at `a` and `b`** (their `Form`s' headers), each unless empty, apart. -/
def BufApart (M : MachineState) (a b : Word) : Prop :=
  (vecLen M a).toNat = 0 ∨ (vecLen M b).toNat = 0 ∨
    Apart (vecPtr M a) (24 * (vecLen M a).toNat) (vecPtr M b) (24 * (vecLen M b).toNat)

/-- **`n` `Vec<Form>`s from `P`**: each a `Vec<Form>` whose buffer (unless empty) lies apart from `[P, P + 24 n)` and
    from the others', each holding only empty `Form`s if `E`. -/
def ElemsT (env : Env) (E : Prop) (M : MachineState) (P : Word) (n : Nat) : Prop :=
  (∀ i, i < n → VecFormT env M (P + BitVec.ofNat 64 (24 * i)) ∧
    ((vecLen M (P + BitVec.ofNat 64 (24 * i))).toNat = 0 ∨
      Apart (vecPtr M (P + BitVec.ofNat 64 (24 * i))) (24 * (vecLen M (P + BitVec.ofNat 64 (24 * i))).toNat) P
        (24 * n))) ∧
  (∀ i i', i < i' → i' < n → BufApart M (P + BitVec.ofNat 64 (24 * i)) (P + BitVec.ofNat 64 (24 * i'))) ∧
  (E → ∀ i, i < n → EmptyFormsT M (P + BitVec.ofNat 64 (24 * i)))

/-- The total precondition: the result's slot in the caller's frame (at or above the stack pointer), in a window
    and 8-byte aligned; the element (`a1`) a `Vec<Form>` its caller owns; the count (`a2`) with `24 n` below
    `2^63`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ (regs .x2).toNat ≤ (regs .x10).toNat ∧ InWin env (regs .x10) 24 ∧
    (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x11) 24 ∧ VecFormT env m (regs .x11) ∧
    (regs .x12).toNat * 24 < 2 ^ 63

/-- The total postcondition: the result a vector of `n` `Vec<Form>`s, its buffer fresh unless empty; their buffers
    apart from it and from each other, and each holding only empty `Form`s if the element does (`ElemsT`). -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 24 ∧ vecLen m' (regs .x10) = regs .x12 ∧
    ((regs .x12).toNat = 0 ∨ env.Fresh m m' (vecPtr m' (regs .x10)) ((regs .x12).toNat * 24)) ∧
    ElemsT env (EmptyFormsT m (regs .x11)) m' (vecPtr m' (regs .x10)) (regs .x12).toNat

/-- **The total contract of `<Vec<Form> as SpecFromElem>::from_elem`** (`vec![v; n]`). -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

/-! ## The frame -/

/-- The prologue's nine saved words in `M`, at `top - 8` down to `top - 72`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23

/-- What every part keeps of memory: the slots, the frame with `out`, the static data, the code. -/
def MemOk (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (out : Word → Prop)
    (M : MachineState) : Prop :=
  Slots M top ret regs ∧ env.Frame top out m M ∧ env.Static M ∧ M.code = m.code

theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 96 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 72 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 72 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := CloneFormsT.es (top := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hsl
  exact ⟨(g _ 8 rfl (by omega) (by omega)).trans s1, (g _ 16 rfl (by omega) (by omega)).trans s2,
    (g _ 24 rfl (by omega) (by omega)).trans s3, (g _ 32 rfl (by omega) (by omega)).trans s4,
    (g _ 40 rfl (by omega) (by omega)).trans s5, (g _ 48 rfl (by omega) (by omega)).trans s6,
    (g _ 56 rfl (by omega) (by omega)).trans s7, (g _ 64 rfl (by omega) (by omega)).trans s8,
    (g _ 72 rfl (by omega) (by omega)).trans s9⟩

/-- **A store into a block allocated since the entry**: `MemOk`, `NEXT` and every word apart from it kept. -/
theorem heap_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hM : MemOk env m top ret regs out M)
    (ha1 : (env.next m).toNat ≤ a.toNat) (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    MemOk env m top ret regs out (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ b : Word, b ≠ a → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  exact ⟨⟨slots_keep (by omega) (fun b h1 _ => MachineState.getMem_setMem_ne fun e => by rw [e] at h1; omega) hsl,
    Tactic.frame_fresh hF rfl ha1 (by omega), Tactic.static_store hS (.inl (by omega)),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne, fun b hb => MachineState.getMem_setMem_ne hb⟩

/-- **One store into the frame's `out`**, a word at or above the stack pointer and in a window. -/
theorem out_store {env : Env} {m M : MachineState} {top ret b v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hb : SretVecOut regs m b) (hwin : InWin env b 8)
    (htop : top.toNat ≤ b.toNat)
    (hM : MemOk env m top ret regs (SretVecOut regs m) M) :
    MemOk env m top ret regs (SretVecOut regs m) (M.setMem b v) ∧ env.next (M.setMem b v) = env.next M := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hn : b ≠ env.nextAddr := fun e => by rw [e] at hwin; unfold InWin at hwin; omega
  exact ⟨⟨slots_keep (by omega) (fun a h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_out hF hb hn, Tactic.static_store hS (by unfold InWin at hwin; omega),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hn⟩

/-- **A `Vec<Form>` below `NEXT` is kept** by a memory agreeing below `NEXT`, `NEXT` no lower. -/
theorem VecFormT.keep_below {env : Env} {M M' : MachineState} {a : Word} (h : VecFormT env M a)
    (ha : a.toNat + 24 ≤ (env.next M).toNat) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ b : Word, b.toNat < (env.next M).toNat → M'.getMem b = M.getMem b) : VecFormT env M' a := by
  have hlt := vecT_lt h.1
  have ep : vecPtr M' a = vecPtr M a := by
    rw [vecPtr_eq, vecPtr_eq]; exact hk _ (by rw [toNat_add_ofNat (by omega)]; omega)
  have el : vecLen M' a = vecLen M a := by
    rw [vecLen_eq, vecLen_eq]; exact hk _ (by rw [toNat_add_ofNat (by omega)]; omega)
  refine ⟨vecT_keep h.1 hn fun b _ h2 => hk b (by omega), ?_⟩
  rw [ep, el]
  refine FormsT.keep_below h.2 ?_ hn hk
  rcases (vecT_buf h.1).1 with h0 | ⟨-, h2, -⟩
  · exact .inl h0
  · unfold Env.Live at h2; exact .inr (by rw [Nat.mul_comm]; exact h2)

/-- A vector's header kept by a memory agreeing on its 24 bytes. -/
theorem hdr_keep {M M' : MachineState} {a : Word} (hlt : a.toNat + 24 < 2 ^ 64)
    (hk : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 24 → M'.getMem b = M.getMem b) :
    vecPtr M' a = vecPtr M a ∧ vecLen M' a = vecLen M a := by
  refine ⟨?_, ?_⟩
  · rw [vecPtr_eq, vecPtr_eq]
    exact hk _ (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)
  · rw [vecLen_eq, vecLen_eq]
    exact hk _ (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)

/-- **Empty `Form`s are kept** where the header's pointer and length and the `Form`s' capacities are. -/
theorem EmptyFormsT.keep {M M' : MachineState} {a a' : Word} (h : EmptyFormsT M a)
    (ep : vecPtr M' a' = vecPtr M a) (el : vecLen M' a' = vecLen M a)
    (hb : ∀ k, k < (vecLen M a).toNat →
      M'.getMem (vecPtr M a + BitVec.ofNat 64 (24 * k)) = M.getMem (vecPtr M a + BitVec.ofNat 64 (24 * k))) :
    EmptyFormsT M' a' := fun k hk => by
  rw [el] at hk
  rw [ep, vecCap_eq, hb k hk, ← vecCap_eq]
  exact h k hk

/-- A word of a vector's buffer of 24-byte elements, as a number. -/
theorem buf_word {env : Env} {M : MachineState} {a : Word} {k : Nat} (h : VecT env M a 24)
    (hk : k < (vecLen M a).toNat) :
    (vecPtr M a + BitVec.ofNat 64 (24 * k)).toNat = (vecPtr M a).toNat + 24 * k ∧
      (vecPtr M a).toNat + 24 * (vecLen M a).toNat ≤ (env.next M).toNat := by
  have hnx := (env.next M).isLt
  rcases (vecT_buf h).1 with h0 | ⟨-, h3, -⟩
  · omega
  · unfold Env.Live at h3
    exact ⟨toNat_add_ofNat (by omega), by omega⟩

/-- **`ElemsT` below `NEXT` is kept** by a memory agreeing below `NEXT`, `NEXT` no lower. -/
theorem ElemsT.keep_below {env : Env} {E : Prop} {M M' : MachineState} {P : Word} {n : Nat}
    (h : ElemsT env E M P n) (hP : P.toNat + 24 * n ≤ (env.next M).toNat)
    (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ b : Word, b.toNat < (env.next M).toNat → M'.getMem b = M.getMem b) : ElemsT env E M' P n := by
  obtain ⟨h1, h2, h3⟩ := h
  have hnx := (env.next M).isLt
  have e : ∀ i, i < n → (P + BitVec.ofNat 64 (24 * i)).toNat = P.toNat + 24 * i := fun i hi =>
    toNat_add_ofNat (by omega)
  have hh : ∀ i, i < n → vecPtr M' (P + BitVec.ofNat 64 (24 * i)) = vecPtr M (P + BitVec.ofNat 64 (24 * i)) ∧
      vecLen M' (P + BitVec.ofNat 64 (24 * i)) = vecLen M (P + BitVec.ofNat 64 (24 * i)) := fun i hi =>
    hdr_keep (by rw [e i hi]; omega) fun b c1 c2 => hk b (by rw [e i hi] at c2; omega)
  refine ⟨fun i hi => ?_, fun i i' hii hi' => ?_, fun hE i hi => ?_⟩
  · rw [(hh i hi).1, (hh i hi).2]
    exact ⟨VecFormT.keep_below (h1 i hi).1 (by rw [e i hi]; omega) hn hk, (h1 i hi).2⟩
  · have := h2 i i' hii hi'
    unfold BufApart at this ⊢
    rwa [(hh i (by omega)).1, (hh i (by omega)).2, (hh i' hi').1, (hh i' hi').2]
  · refine EmptyFormsT.keep (h3 hE i hi) (hh i hi).1 (hh i hi).2 fun k hk' => hk _ ?_
    have := buf_word (h1 i hi).1.1 hk'
    omega

/-- The result's header `(c, P, n)` before it is stored: none, or `n` `Vec<Form>`s in a block allocated since the
    entry. -/
def Res (env : Env) (E : Prop) (m M : MachineState) (n c P : Word) : Prop :=
  (n.toNat = 0 ∧ c = 0#64 ∧ P = 8#64) ∨
    (c = n ∧ 0 < n.toNat ∧ (env.next m).toNat ≤ P.toNat ∧ P.toNat + 24 * n.toNat ≤ (env.next M).toNat ∧
      P.toNat % 8 = 0 ∧ ElemsT env E M P n.toNat)

/-- **The result's three stores** at `sret`: `MemOk` with `out` the result's header, and the postcondition. -/
theorem fin_mem {env : Env} {m M : MachineState} {top ret c P : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hW : Windows env top m) (hpre : PreT env regs m)
    (h2 : regs .x2 = top) (hM : MemOk env m top ret regs Tactic.F M)
    (hD : Res env (EmptyFormsT m (regs .x11)) m M (regs .x12) c P) :
    MemOk env m top ret regs (SretVecOut regs m)
        (((M.setMem (regs .x10) c).setMem (regs .x10 + 8#64) P).setMem (regs .x10 + 16#64) (regs .x12)) ∧
      ∀ r, PostT env regs m r
        (((M.setMem (regs .x10) c).setMem (regs .x10 + 8#64) P).setMem (regs .x10 + 16#64) (regs .x12)) := by
  obtain ⟨hown, htop, hwin, hal, -, -, hn24⟩ := hpre
  rw [h2] at htop
  have hlay := env.layout
  have hge := hW.next_ge
  have hW1 := hW.heapEnd_le
  have h24 : (regs .x10).toNat + 24 < 2 ^ 64 := hown.2
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hout : ∀ k : Nat, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → SretVecOut regs m b :=
    fun k hk b hb => by show InRange (regs .x10) Layouts.Vec.byteSize b; unfold InRange Layouts.Vec.byteSize; omega
  have hw : ∀ k : Nat, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → InWin env b 8 :=
    fun k hk b hb => Runtime.MemsetT.InWin.sub hwin (by omega) (by omega)
  have hM' : MemOk env m top ret regs (SretVecOut regs m) M := ⟨hM.1, Tactic.frame_weaken hM.2.1, hM.2.2⟩
  obtain ⟨m1, n1⟩ := out_store (v := c) hlim (hout 0 (by omega) _ rfl) (hw 0 (by omega) _ rfl) htop hM'
  obtain ⟨m2, n2⟩ := out_store (v := P) hlim (hout 8 (by omega) _ e8) (hw 8 (by omega) _ e8) (by omega) m1
  obtain ⟨m3, n3⟩ := out_store (v := regs .x12) hlim (hout 16 (by omega) _ e16) (hw 16 (by omega) _ e16)
    (by omega) m2
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hN : env.next (((M.setMem (regs .x10) c).setMem (regs .x10 + 8#64) P).setMem (regs .x10 + 16#64)
      (regs .x12)) = env.next M := by rw [n3, n2, n1]
  have r0 : (((M.setMem (regs .x10) c).setMem (regs .x10 + 8#64) P).setMem (regs .x10 + 16#64)
      (regs .x12)).getMem (regs .x10) = c := by
    rw [MachineState.getMem_setMem_ne (ne (regs .x10) (regs .x10 + 16#64) (by omega)),
      MachineState.getMem_setMem_ne (ne (regs .x10) (regs .x10 + 8#64) (by omega)), MachineState.getMem_setMem_eq]
  have r8 : (((M.setMem (regs .x10) c).setMem (regs .x10 + 8#64) P).setMem (regs .x10 + 16#64)
      (regs .x12)).getMem (regs .x10 + 8#64) = P := by
    rw [MachineState.getMem_setMem_ne (ne (regs .x10 + 8#64) (regs .x10 + 16#64) (by omega)),
      MachineState.getMem_setMem_eq]
  have r16 : (((M.setMem (regs .x10) c).setMem (regs .x10 + 8#64) P).setMem (regs .x10 + 16#64)
      (regs .x12)).getMem (regs .x10 + 16#64) = regs .x12 := MachineState.getMem_setMem_eq
  have hk : ∀ b : Word, b.toNat < (env.next M).toNat → (((M.setMem (regs .x10) c).setMem (regs .x10 + 8#64) P).setMem
      (regs .x10 + 16#64) (regs .x12)).getMem b = M.getMem b := fun b hb => by
    rw [MachineState.getMem_setMem_ne (ne b _ (by omega)), MachineState.getMem_setMem_ne (ne b _ (by omega)),
      MachineState.getMem_setMem_ne (ne b _ (by omega))]
  refine ⟨m3, fun r => ⟨⟨hwin, ⟨Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _)
    (by simp only [Layouts.RawVecInner.byteSize]; omega), hal, ?_, ?_⟩, ?_⟩, by rw [vecLen_eq, r16], ?_, ?_⟩⟩
  · rw [rvCapAt_eq, rvPtrAt_eq, r0, r8]
    rcases hD with ⟨h0, rfl, -⟩ | ⟨rfl, -, h1, h2, h3, -⟩
    · exact .inl rfl
    · exact .inr ⟨by omega, by unfold Env.Live; rw [hN]; omega, h3⟩
  · rw [rvCapAt_eq, r0]
    rcases hD with ⟨h0, rfl, -⟩ | ⟨rfl, -⟩
    · simp
    · exact hn24
  · rw [vecLen_eq, vecCap_eq, r0, r16]
    rcases hD with ⟨h0, rfl, -⟩ | ⟨rfl, -⟩ <;> simp_all
  · rw [vecPtr_eq, r8]
    rcases hD with ⟨h0, -⟩ | ⟨-, -, h1, h2, -⟩
    · exact .inl h0
    · exact .inr ⟨h1, by rw [hN]; omega⟩
  · rw [vecPtr_eq, r8]
    rcases hD with ⟨h0, -⟩ | ⟨-, -, h1, h2, h3, hV⟩
    · exact ⟨fun i hi => by omega, fun i i' _ hi => by omega, fun _ i hi => by omega⟩
    exact ElemsT.keep_below hV h2 (by rw [hN]) hk

/-! ## The clones stored so far -/

/-- **The `Vec<Form>` at `a` lies in `[lo, H)`**: its buffer and its `Form`s' terms' blocks, each unless empty. -/
def FootV (M : MachineState) (a : Word) (lo H : Nat) : Prop :=
  ((vecLen M a).toNat = 0 ∨ (lo ≤ (vecPtr M a).toNat ∧ (vecPtr M a).toNat + 24 * (vecLen M a).toNat ≤ H)) ∧
    ∀ k, k < (vecLen M a).toNat →
      (vecLen M (vecPtr M a + BitVec.ofNat 64 (24 * k))).toNat = 0 ∨
        (lo ≤ (vecPtr M (vecPtr M a + BitVec.ofNat 64 (24 * k))).toNat ∧
          (vecPtr M (vecPtr M a + BitVec.ofNat 64 (24 * k))).toNat +
            40 * (vecLen M (vecPtr M a + BitVec.ofNat 64 (24 * k))).toNat ≤ H)

/-- **A `Vec<Form>` lying in `[lo, H)` is kept** by a memory agreeing on its header and on `[lo, H)`, `NEXT` no
    lower. -/
theorem vecForm_keep {env : Env} {M M' : MachineState} {a : Word} {lo H : Nat} (h : VecFormT env M a)
    (hf : FootV M a lo H) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hka : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 24 → M'.getMem b = M.getMem b)
    (hkr : ∀ b : Word, lo ≤ b.toNat → b.toNat < H → M'.getMem b = M.getMem b) :
    VecFormT env M' a ∧ FootV M' a lo H := by
  have hlt := vecT_lt h.1
  have ep : vecPtr M' a = vecPtr M a := by
    rw [vecPtr_eq, vecPtr_eq]; exact hka _ (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega)
  have el : vecLen M' a = vecLen M a := by
    rw [vecLen_eq, vecLen_eq]; exact hka _ (by rw [toNat_add_ofNat (by omega)]; omega)
      (by rw [toNat_add_ofNat (by omega)]; omega)
  have hb := (vecT_buf h.1).1
  have hlay := env.layout
  have := env.heapEnd.isLt
  have hnx : (env.next M).toNat < 2 ^ 64 := (env.next M).isLt
  -- each `Form`'s header in the buffer, and its terms' block, kept
  have hform : ∀ k, k < (vecLen M a).toNat →
      vecPtr M' (vecPtr M a + BitVec.ofNat 64 (24 * k)) = vecPtr M (vecPtr M a + BitVec.ofNat 64 (24 * k)) ∧
      vecLen M' (vecPtr M a + BitVec.ofNat 64 (24 * k)) = vecLen M (vecPtr M a + BitVec.ofNat 64 (24 * k)) ∧
      FormT env M' (vecPtr M a + BitVec.ofNat 64 (24 * k)) := fun k hk => by
    rcases hf.1 with h0 | ⟨h1, h2⟩
    · omega
    rcases hb with h0 | ⟨-, h3, -⟩
    · omega
    unfold Env.Live at h3
    have ek : (vecPtr M a + BitVec.ofNat 64 (24 * k)).toNat = (vecPtr M a).toNat + 24 * k :=
      toNat_add_ofNat (by omega)
    have hF := h.2 k hk
    have hft := hf.2 k hk
    generalize vecPtr M a + BitVec.ofNat 64 (24 * k) = f at ek hF hft ⊢
    have hkh : ∀ b : Word, f.toNat ≤ b.toNat → b.toNat < f.toNat + 24 → M'.getMem b = M.getMem b :=
      fun b b1 b2 => hkr b (by omega) (by omega)
    have hlt' := vecT_lt hF.1
    have f8 : (f + 8#64).toNat = f.toNat + 8 := toNat_add_ofNat (by omega)
    have f16 : (f + 16#64).toNat = f.toNat + 16 := toNat_add_ofNat (by omega)
    refine ⟨?_, ?_, hF.keep hn hkh fun b b1 b2 => ?_⟩
    · rw [vecPtr_eq, vecPtr_eq]; exact hkh _ (by omega) (by omega)
    · rw [vecLen_eq, vecLen_eq]; exact hkh _ (by omega) (by omega)
    · rcases hft with h0 | ⟨h4, h5⟩
      · omega
      · exact hkr b (by omega) (by omega)
  refine ⟨⟨vecT_keep h.1 hn hka, ?_⟩, ?_, ?_⟩
  · rw [ep, el]; exact fun k hk => (hform k hk).2.2
  · rw [ep, el]; exact hf.1
  · rw [ep, el]
    intro k hk
    rw [(hform k hk).1, (hform k hk).2.1]
    exact hf.2 k hk

/-- **The first `j` of the `n` results** from `D`, each a `Vec<Form>` lying between the result's block's end and
    `H`, their buffers apart, each holding only empty `Form`s if `E`. -/
def DoneV (env : Env) (E : Prop) (M : MachineState) (D : Word) (n j H : Nat) : Prop :=
  (∀ i, i < j → VecFormT env M (D + BitVec.ofNat 64 (24 * i)) ∧
    FootV M (D + BitVec.ofNat 64 (24 * i)) (D.toNat + 24 * n) H) ∧
  (∀ i i', i < i' → i' < j → BufApart M (D + BitVec.ofNat 64 (24 * i)) (D + BitVec.ofNat 64 (24 * i'))) ∧
  (E → ∀ i, i < j → EmptyFormsT M (D + BitVec.ofNat 64 (24 * i)))

/-- **`DoneV` is kept** by a memory agreeing on the first `j` headers and on `[D + 24 n, H)`, `NEXT` no lower. -/
theorem DoneV.keep {env : Env} {E : Prop} {M M' : MachineState} {D : Word} {n j H : Nat}
    (h : DoneV env E M D n j H)
    (hD : D.toNat + 24 * n < 2 ^ 64) (hj : j ≤ n) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ b : Word, (D.toNat ≤ b.toNat ∧ b.toNat < D.toNat + 24 * j) ∨ (D.toNat + 24 * n ≤ b.toNat ∧ b.toNat < H) →
      M'.getMem b = M.getMem b) : DoneV env E M' D n j H := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : ∀ i, i < j → (D + BitVec.ofNat 64 (24 * i)).toNat = D.toNat + 24 * i := fun i hi =>
    toNat_add_ofNat (by omega)
  have hh : ∀ i, i < j → vecPtr M' (D + BitVec.ofNat 64 (24 * i)) = vecPtr M (D + BitVec.ofNat 64 (24 * i)) ∧
      vecLen M' (D + BitVec.ofNat 64 (24 * i)) = vecLen M (D + BitVec.ofNat 64 (24 * i)) := fun i hi =>
    hdr_keep (by rw [e i hi]; omega) fun b c1 c2 => hk b (.inl ⟨by rw [e i hi] at c1; omega, by
      rw [e i hi] at c2; omega⟩)
  refine ⟨fun i hi => ?_, fun i i' hii hi' => ?_, fun hE i hi => ?_⟩
  · obtain ⟨hV, hf⟩ := h1 i hi
    exact vecForm_keep hV hf hn (fun b c1 c2 => hk b (.inl ⟨by rw [e i hi] at c1; omega, by
      rw [e i hi] at c2; omega⟩)) fun b c1 c2 => hk b (.inr ⟨c1, c2⟩)
  · have := h2 i i' hii hi'
    unfold BufApart at this ⊢
    rwa [(hh i (by omega)).1, (hh i (by omega)).2, (hh i' hi').1, (hh i' hi').2]
  · refine EmptyFormsT.keep (h3 hE i hi) (hh i hi).1 (hh i hi).2 fun k hk' => hk _ (.inr ?_)
    have hw := buf_word (h1 i hi).1.1 hk'
    rcases (h1 i hi).2.1 with h0 | ⟨f1, f2⟩
    · omega
    · omega

/-- `DoneV`'s bound only grows. -/
theorem DoneV.mono {env : Env} {E : Prop} {M : MachineState} {D : Word} {n j H H' : Nat}
    (h : DoneV env E M D n j H) (hH : H ≤ H') : DoneV env E M D n j H' :=
  ⟨fun i hi => ⟨(h.1 i hi).1, (h.1 i hi).2.1.imp id (fun ⟨a, b⟩ => ⟨a, by omega⟩),
    fun k hk => ((h.1 i hi).2.2 k hk).imp id fun ⟨a, b⟩ => ⟨a, by omega⟩⟩, h.2⟩

/-- The result's block `D` of `n` `Vec<Form>`s: allocated since the entry, 8-byte aligned. -/
def Blk (env : Env) (m : MachineState) (D : Word) (n : Nat) (M : MachineState) : Prop :=
  (env.next m).toNat ≤ D.toNat ∧ D.toNat + 24 * n ≤ (env.next M).toNat ∧ D.toNat % 8 = 0

/-- **The element's header moved** to the last slot `A = D + 24 (n - 1)`: `MemOk`, and the result's header
    `(n, D, n)` with its `n` `Vec<Form>`s. -/
theorem move_mem {env : Env} {m M : MachineState} {top ret A D : Word} {regs : Reg → Word} {H : Nat}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hW : Windows env top m) (hpre : PreT env regs m)
    (h2 : regs .x2 = top) (hM : MemOk env m top ret regs Tactic.F M) (hB : Blk env m D (regs .x12).toNat M)
    (hn : 0 < (regs .x12).toNat) (hA : A.toNat = D.toNat + 24 * ((regs .x12).toNat - 1))
    (hdone : DoneV env (EmptyFormsT m (regs .x11)) M D (regs .x12).toNat ((regs .x12).toNat - 1) H) :
    MemOk env m top ret regs Tactic.F (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64)
        (M.getMem (regs .x11 + 8#64))).setMem (A + 16#64) (M.getMem (regs .x11 + 16#64))) ∧
      Res env (EmptyFormsT m (regs .x11)) m
        (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64) (M.getMem (regs .x11 + 8#64))).setMem
        (A + 16#64) (M.getMem (regs .x11 + 16#64))) (regs .x12) (regs .x12) D := by
  obtain ⟨-, -, -, -, hown1, hV, -⟩ := hpre
  rw [h2] at hown1
  obtain ⟨b1, b2, b3⟩ := hB
  have hlay := env.layout
  have hge := hW.next_ge
  have hW1 := hW.heapEnd_le
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hnx : (env.next m).toNat ≤ env.heapEnd.toNat := by omega
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  obtain ⟨m1, n1, k1⟩ := heap_store (a := A) (v := M.getMem (regs .x11)) hlim hM (by omega) (by omega)
  obtain ⟨m2, n2, k2⟩ := heap_store (a := A + 8#64) (v := M.getMem (regs .x11 + 8#64)) hlim m1 (by omega)
    (by rw [n1]; omega)
  obtain ⟨m3, n3, k3⟩ := heap_store (a := A + 16#64) (v := M.getMem (regs .x11 + 16#64)) hlim m2 (by omega)
    (by rw [n2, n1]; omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hN : env.next (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64) (M.getMem (regs .x11 + 8#64))).setMem
      (A + 16#64) (M.getMem (regs .x11 + 16#64))) = env.next M := by rw [n3, n2, n1]
  have hk : ∀ b : Word, (b.toNat < A.toNat ∨ A.toNat + 24 ≤ b.toNat) →
      (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64) (M.getMem (regs .x11 + 8#64))).setMem
        (A + 16#64) (M.getMem (regs .x11 + 16#64))).getMem b = M.getMem b := fun b hb => by
    rw [k3 b (ne _ _ (by omega)), k2 b (ne _ _ (by omega)), k1 b (ne _ _ (by omega))]
  -- the element's words and everything below `NEXT` at the entry: as at the entry
  have h24 : (regs .x11).toNat + 24 < 2 ^ 64 := hown1.2
  have hsep : ∀ b : Word, (regs .x11).toNat ≤ b.toNat → b.toNat < (regs .x11).toNat + 24 →
      b.toNat < A.toNat ∨ A.toNat + 24 ≤ b.toNat := fun b c1 c2 => by rcases hown1.1 with h | h <;> omega
  have hel : ∀ b : Word, (regs .x11).toNat ≤ b.toNat → b.toNat < (regs .x11).toNat + 24 →
      M.getMem b = m.getMem b := fun b c1 c2 =>
    Runtime.ReserveT.getMem_owned hM.2.1 hown1 hnx (by omega) ⟨c1, c2⟩ id
  have hbelow : ∀ b : Word, b.toNat < (env.next m).toNat →
      (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64) (M.getMem (regs .x11 + 8#64))).setMem
        (A + 16#64) (M.getMem (regs .x11 + 16#64))).getMem b = m.getMem b := fun b hb => by
    rw [hk b (.inl (by omega))]; exact hM.2.1.getMem_below_next hnx hb id
  have x8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
  have x16 : (regs .x11 + 16#64).toNat = (regs .x11).toNat + 16 := toNat_add_ofNat (by omega)
  have r8 : (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64) (M.getMem (regs .x11 + 8#64))).setMem
      (A + 16#64) (M.getMem (regs .x11 + 16#64))).getMem (A + 8#64) = m.getMem (regs .x11 + 8#64) := by
    rw [MachineState.getMem_setMem_ne (ne (A + 8#64) (A + 16#64) (by omega)), MachineState.getMem_setMem_eq,
      hel _ (by omega) (by omega)]
  have r16 : (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64) (M.getMem (regs .x11 + 8#64))).setMem
      (A + 16#64) (M.getMem (regs .x11 + 16#64))).getMem (A + 16#64) = m.getMem (regs .x11 + 16#64) := by
    rw [MachineState.getMem_setMem_eq, hel _ (by omega) (by omega)]
  have hq : (vecLen m (regs .x11)).toNat = 0 ∨
      (vecPtr m (regs .x11)).toNat + 24 * (vecLen m (regs .x11)).toNat ≤ (env.next m).toNat := by
    rcases (vecT_buf hV.1).1 with h0 | ⟨-, h3, -⟩
    · exact .inl h0
    · unfold Env.Live at h3; exact .inr (by rw [Nat.mul_comm]; exact h3)
  have hlast : VecFormT env (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64)
      (M.getMem (regs .x11 + 8#64))).setMem (A + 16#64) (M.getMem (regs .x11 + 16#64))) A := by
    have r0 : (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64) (M.getMem (regs .x11 + 8#64))).setMem
        (A + 16#64) (M.getMem (regs .x11 + 16#64))).getMem A = m.getMem (regs .x11) := by
      rw [MachineState.getMem_setMem_ne (ne A (A + 16#64) (by omega)),
        MachineState.getMem_setMem_ne (ne A (A + 8#64) (by omega)), MachineState.getMem_setMem_eq,
        hel _ (by omega) (by omega)]
    refine ⟨CloneFormsT.vecT_copy hV.1 (.inl ⟨by omega, by omega⟩) (by omega) (by rw [hN]; omega) r0 r8 r16, ?_⟩
    rw [vecPtr_eq, vecLen_eq, r8, r16]
    exact FormsT.keep_below hV.2 hq (by rw [hN]; omega) hbelow
  have epA : vecPtr (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64) (M.getMem (regs .x11 + 8#64))).setMem
      (A + 16#64) (M.getMem (regs .x11 + 16#64))) A = vecPtr m (regs .x11) := by rw [vecPtr_eq, vecPtr_eq, r8]
  have elA : vecLen (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64) (M.getMem (regs .x11 + 8#64))).setMem
      (A + 16#64) (M.getMem (regs .x11 + 16#64))) A = vecLen m (regs .x11) := by rw [vecLen_eq, vecLen_eq, r16]
  have hold := DoneV.keep (M' := (((M.setMem A (M.getMem (regs .x11))).setMem (A + 8#64)
    (M.getMem (regs .x11 + 8#64))).setMem (A + 16#64) (M.getMem (regs .x11 + 16#64)))) hdone (by omega) (by omega)
    (by rw [hN]) fun b hb => hk b (by omega)
  have hlastI : ∀ i, (regs .x12).toNat - 1 ≤ i → i < (regs .x12).toNat → D + BitVec.ofNat 64 (24 * i) = A :=
    fun i h1 h2 => BitVec.eq_of_toNat_eq (by rw [toNat_add_ofNat (by omega)]; omega)
  refine ⟨m3, .inr ⟨rfl, hn, b1, by rw [hN]; exact b2, b3, fun i hi => ?_, fun i i' hii hi' => ?_, fun hE i hi => ?_⟩⟩
  · rcases Nat.lt_or_ge i ((regs .x12).toNat - 1) with hi' | hi'
    · obtain ⟨hV', hf⟩ := hold.1 i hi'
      refine ⟨hV', ?_⟩
      rcases hf.1 with h0 | ⟨f1, -⟩
      · exact .inl h0
      · exact .inr (Or.inr f1)
    · rw [hlastI i hi' hi, epA, elA]
      refine ⟨hlast, ?_⟩
      rcases hq with h0 | h0
      · exact .inl h0
      · exact .inr (Or.inl (by omega))
  · rcases Nat.lt_or_ge i' ((regs .x12).toNat - 1) with hi'' | hi''
    · exact hold.2.1 i i' hii hi''
    · rw [hlastI i' hi'' hi']
      obtain ⟨-, hf⟩ := hold.1 i (by omega)
      unfold BufApart
      rw [epA, elA]
      rcases hf.1 with h0 | ⟨f1, -⟩
      · exact .inl h0
      rcases hq with h0 | h0
      · exact .inr (.inl h0)
      · exact .inr (.inr (Or.inr (by omega)))
  · rcases Nat.lt_or_ge i ((regs .x12).toNat - 1) with hi' | hi'
    · exact hold.2.2 hE i hi'
    · rw [hlastI i hi' hi]
      refine EmptyFormsT.keep hE epA elA fun k hk' => hbelow _ ?_
      have := buf_word hV.1 hk'
      omega

/-- **One clone stored**: after the clone's call (writing at most its slot at the stack pointer, `top - 96`) and
    the three stores of its header at `A = D + 24 j`, `MemOk`, the block and `j + 1` results kept. -/
theorem step_mem {env : Env} {E : Prop} {m M M1 : MachineState} {top ret A D : Word} {regs : Reg → Word}
    {out : Word → Prop} {n j : Nat} (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hge : 0x10000000 ≤ (env.next m).toNat)
    (hM : MemOk env m top ret regs Tactic.F M) (hB : Blk env m D n M) (hj : j < n)
    (hA : A.toNat = D.toNat + 24 * j) (hdone : DoneV env E M D n j (env.next M).toNat)
    (hF1 : env.Frame (top + 18446744073709551520#64) out M M1) (hS1 : env.Static M1) (hc1 : M1.code = M.code)
    (hout : ∀ b, out b → top.toNat - 96 ≤ b.toNat ∧ b.toNat < top.toNat - 72)
    (hV : VecT env M1 (top + 18446744073709551520#64) 24)
    (hfr : (vecLen M1 (top + 18446744073709551520#64)).toNat = 0 ∨
      env.Fresh M M1 (vecPtr M1 (top + 18446744073709551520#64))
        ((vecLen M1 (top + 18446744073709551520#64)).toNat * 24))
    (hFs : FormsT env M1 (vecPtr M1 (top + 18446744073709551520#64))
      (vecLen M1 (top + 18446744073709551520#64)).toNat)
    (hFt : CloneFormsFreshT.FreshTermsT env M M1 (vecPtr M1 (top + 18446744073709551520#64))
      (vecLen M1 (top + 18446744073709551520#64)).toNat)
    (hEc : E → EmptyFormsT M1 (top + 18446744073709551520#64)) :
    let M2 := ((M1.setMem A (M1.getMem (top + 18446744073709551520#64))).setMem (A + 8#64)
      (M1.getMem (top + 18446744073709551528#64))).setMem (A + 16#64) (M1.getMem (top + 18446744073709551536#64))
    MemOk env m top ret regs Tactic.F M2 ∧ Blk env m D n M2 ∧ DoneV env E M2 D n (j + 1) (env.next M2).toNat := by
  intro M2
  have hlay := env.layout
  obtain ⟨b1, b2, b3⟩ := hB
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  have hnM := hF0.2.1
  have e96 := CloneFormsT.es (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have e88 := CloneFormsT.es (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have e80 := CloneFormsT.es (top := top) (c := 18446744073709551536#64) (k := 80) rfl (by omega)
  have hn1 := hF1.1
  have hk1 : ∀ a : Word, (a.toNat < (env.next M).toNat ∨ top.toNat - 96 ≤ a.toNat) →
      (a.toNat < top.toNat - 96 ∨ top.toNat - 72 ≤ a.toNat) → M1.getMem a = M.getMem a := fun a h1 h2 =>
    hF1.2.2 a fun hw => by
      rcases hw with hw | hw | hw | hw
      · rw [e96] at hw; omega
      · have := hw.1; have := hF1.2.1; omega
      · rw [hw] at h1; have := hF0.2.1; rcases h1 with h1 | h1 <;> omega
      · have := hout a hw; omega
  have hM1 : MemOk env m top ret regs Tactic.F M1 :=
    ⟨slots_keep (by omega) (fun a h1 _ => hk1 a (.inr (by omega)) (.inr (by omega))) hsl,
      hF0.trans hF1 (by rw [e96]; omega) fun b hb => Or.inl (by have := hout b hb; omega), hS1, hc1.trans hc0⟩
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  obtain ⟨m1, n1, k1⟩ := heap_store (a := A) (v := M1.getMem (top + 18446744073709551520#64)) hlim hM1 (by omega)
    (by omega)
  obtain ⟨m2, n2, k2⟩ := heap_store (a := A + 8#64) (v := M1.getMem (top + 18446744073709551528#64)) hlim m1
    (by omega) (by rw [n1]; omega)
  obtain ⟨m3, n3, k3⟩ := heap_store (a := A + 16#64) (v := M1.getMem (top + 18446744073709551536#64)) hlim m2
    (by omega) (by rw [n2, n1]; omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hN : env.next M2 = env.next M1 := by rw [n3, n2, n1]
  have hk : ∀ b : Word, (b.toNat < A.toNat ∨ A.toNat + 24 ≤ b.toNat) → M2.getMem b = M1.getMem b := fun b hb => by
    rw [k3 b (ne _ _ (by omega)), k2 b (ne _ _ (by omega)), k1 b (ne _ _ (by omega))]
  -- the new result, first at the clone's slot
  have hlo : D.toNat + 24 * n ≤ (env.next M).toNat := b2
  have hfoot : FootV M1 (top + 18446744073709551520#64) (D.toNat + 24 * n) (env.next M1).toNat := by
    refine ⟨?_, fun k hk => ?_⟩
    · rcases hfr with h0 | ⟨h1, h2⟩
      · exact .inl h0
      · exact .inr ⟨by omega, by omega⟩
    · rcases hFt k hk with h0 | ⟨h1, h2⟩
      · exact .inl h0
      · exact .inr ⟨by omega, h2⟩
  have hs1 := vecForm_keep (M' := M2) ⟨hV, hFs⟩ hfoot (by rw [hN])
    (fun b c1 c2 => hk b (.inr (by rw [e96] at c1; omega))) fun b c1 c2 => hk b (.inr (by omega))
  have s0 : M2.getMem A = M1.getMem (top + 18446744073709551520#64) := by
    rw [MachineState.getMem_setMem_ne (ne A (A + 16#64) (by omega)),
      MachineState.getMem_setMem_ne (ne A (A + 8#64) (by omega)), MachineState.getMem_setMem_eq]
  have a8 : top + 18446744073709551520#64 + 8#64 = top + 18446744073709551528#64 := by
    rw [BitVec.add_assoc]; rfl
  have a16 : top + 18446744073709551520#64 + 16#64 = top + 18446744073709551536#64 := by
    rw [BitVec.add_assoc]; rfl
  have s8 : M2.getMem (A + 8#64) = M1.getMem (top + 18446744073709551520#64 + 8#64) := by
    rw [MachineState.getMem_setMem_ne (ne (A + 8#64) (A + 16#64) (by omega)), MachineState.getMem_setMem_eq, a8]
  have s16 : M2.getMem (A + 16#64) = M1.getMem (top + 18446744073709551520#64 + 16#64) := by
    rw [MachineState.getMem_setMem_eq, a16]
  have ep : vecPtr M2 A = vecPtr M2 (top + 18446744073709551520#64) := by
    rw [vecPtr_eq, vecPtr_eq, s8, hk _ (.inr (by rw [toNat_add_ofNat (by omega), e96]; omega))]
  have el : vecLen M2 A = vecLen M2 (top + 18446744073709551520#64) := by
    rw [vecLen_eq, vecLen_eq, s16, hk _ (.inr (by rw [toNat_add_ofNat (by omega), e96]; omega))]
  have hnew : VecFormT env M2 A ∧ FootV M2 A (D.toNat + 24 * n) (env.next M1).toNat := by
    refine ⟨⟨CloneFormsT.vecT_copy hV (.inl ⟨by omega, by omega⟩) (by omega) (by rw [hN]) s0 s8 s16, ?_⟩, ?_⟩
    · rw [ep, el]; exact hs1.1.2
    · unfold FootV; rw [ep, el]; exact hs1.2
  -- the earlier results
  have hold1 := DoneV.keep (M' := M1) hdone (by omega) (by omega) hn1 fun b hb => hk1 b (.inl (by omega))
    (.inl (by rcases hb with hb | hb <;> omega))
  have hold2 := DoneV.keep (M' := M2) hold1 (by omega) (by omega) (by rw [hN]) fun b hb => hk b (by omega)
  -- the clone's header, buffer and `Form`s' capacities, read at `A` in `M2`
  have q8 : M2.getMem (top + 18446744073709551520#64 + 8#64) = M1.getMem (top + 18446744073709551520#64 + 8#64) :=
    hk _ (.inr (by rw [toNat_add_ofNat (by omega), e96]; omega))
  have q16 : M2.getMem (top + 18446744073709551520#64 + 16#64) = M1.getMem (top + 18446744073709551520#64 + 16#64) :=
    hk _ (.inr (by rw [toNat_add_ofNat (by omega), e96]; omega))
  have epA : vecPtr M2 A = vecPtr M1 (top + 18446744073709551520#64) := by rw [ep, vecPtr_eq, vecPtr_eq, q8]
  have elA : vecLen M2 A = vecLen M1 (top + 18446744073709551520#64) := by rw [el, vecLen_eq, vecLen_eq, q16]
  have hAi : ∀ i, i = j → D + BitVec.ofNat 64 (24 * i) = A := fun i hi =>
    BitVec.eq_of_toNat_eq (by rw [toNat_add_ofNat (by omega)]; omega)
  refine ⟨m3, ⟨b1, by rw [hN]; omega, b3⟩, ⟨fun i hi => ?_, fun i i' hii hi' => ?_, fun hE i hi => ?_⟩⟩
  · rw [hN]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact (hold2.mono hn1).1 i hi
    · rw [hAi i hi]; exact hnew
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | hi'
    · exact hold2.2.1 i i' hii hi'
    · rw [hAi i' hi']
      obtain ⟨-, hf⟩ := hold2.1 i (by omega)
      unfold BufApart
      rw [epA, elA]
      rcases hf.1 with h0 | ⟨-, f2⟩
      · exact .inl h0
      rcases hfr with h0 | ⟨f3, -⟩
      · exact .inr (.inl h0)
      · exact .inr (.inr (Or.inl (by omega)))
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact hold2.2.2 hE i hi
    · rw [hAi i hi]
      refine EmptyFormsT.keep (hEc hE) epA elA fun k hk' => hk _ (.inr ?_)
      rcases hfr with h0 | ⟨f3, -⟩
      · omega
      have := buf_word hV hk'
      omega

/-! ## The return -/

/-- The registers the code never writes, kept for the caller. -/
def Kept (regs R : Reg → Word) : Prop :=
  R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

set_option rv_sym.heap true in
/-- **The return**, from instruction 120: the saved registers reloaded. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (R : Reg → Word) (M : MachineState) (hR : R .x2 = top + 18446744073709551520#64) (hK : Kept regs R)
    (hM : MemOk env m top ret regs (SretVecOut regs m) M) (hPost : ∀ r, PostT env regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 120, ret, top⟩ :: rest, R, M⟩ := by
  obtain ⟨⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩, hF, hS, hc⟩ := hM
  obtain ⟨k24, k25, k26, k27⟩ := hK
  rv_introT hR
  rv_symT hp with [_hL]
  exact ⟨⟨rfl, t2, t3, t4, t5, t6, t7, t8, t9, k24, k25, k26, k27⟩, hF, hS, hPost _⟩

/-- The registers at the result's stores (instruction 114). -/
def XRegs (top c P : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x10 = c ∧ R .x18 = P ∧
    Kept regs R

set_option rv_sym.heap true in
/-- **The result's header**, from instruction 114: `(c, P, n)` stored at `sret`, then the return. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hpre : PreT env regs m) (h2 : regs .x2 = top) :
    ∀ c P R M, XRegs top c P regs R → MemOk env m top ret regs Tactic.F M →
      Res env (EmptyFormsT m (regs .x11)) m M (regs .x12) c P →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩ := by
  intro c P R M ⟨r2, r8, r9, r10, r18, hK⟩ hM hD
  obtain ⟨hMf, hPost⟩ := fin_mem hlim hW hpre h2 hM hD
  have hcM : M.code = m.code := hM.2.2.2
  have hex := exit hp hL hk hlim hW h16
  obtain ⟨hown, htop, hwin, hal, -⟩ := hpre
  have h24 : (regs .x10).toNat + 24 < 2 ^ 64 := hown.2
  have hW1 := hW.heapEnd_le
  have hW2 := hW.top_le
  have hlay := env.layout
  have hW3 := hW.nextAddr_ge
  have w0 : inWindow (regs .x10) 8 = true := (hwin.dword (x := regs .x10) (o := 0) hW hal rfl (by omega) rfl).1
  have w8 := hwin.dword_add (x := regs .x10) (o := 0) (k := 8) hW hal rfl (by omega) rfl
  have w16 := hwin.dword_add (x := regs .x10) (o := 0) (k := 16) hW hal rfl (by omega) rfl
  have hR := And.intro r2 (And.intro r8 (And.intro r9 (And.intro r10 r18)))
  rv_introT hR
  rv_symT hp stop [120] with [hL]
  exact hex _ _ rfl hK hMf hPost

/-- The registers every part from the allocation on keeps: the stack pointer, the count, `sret`, the block, the
    element. -/
def JRegs (top D : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x18 = D ∧
    R .x19 = regs .x11 ∧ Kept regs R

set_option rv_sym.heap true in
/-- **The move**, from instruction 86: the element's header into the last slot, then the result's header. -/
theorem move {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hpre : PreT env regs m) (h2 : regs .x2 = top) :
    ∀ D H R M, JRegs top D regs R → (R .x23).toNat = D.toNat + 24 * ((regs .x12).toNat - 1) →
      0 < (regs .x12).toNat → MemOk env m top ret regs Tactic.F M → Blk env m D (regs .x12).toNat M →
      DoneV env (EmptyFormsT m (regs .x11)) M D (regs .x12).toNat ((regs .x12).toNat - 1) H →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 86, ret, top⟩ :: rest, R, M⟩ := by
  intro D H R M ⟨r2, r8, r9, r18, r19, hK⟩ h23 hn hM hB hdone
  have hfin := fin hp hL hk hlim hW h16 hpre h2
  obtain ⟨hM3, hres⟩ := move_mem hlim hW hpre h2 hM hB hn h23 hdone
  have hcM : M.code = m.code := hM.2.2.2
  obtain ⟨-, -, -, -, hown1, hV, -⟩ := hpre
  obtain ⟨b1, b2, b3⟩ := hB
  have h24 : (regs .x11).toNat + 24 < 2 ^ 64 := hown1.2
  have hv := hV.1
  have hlay := env.layout
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnM := hM.2.1.2.1
  clear hdone hV
  have hR := And.intro r2 (And.intro r8 (And.intro r9 (And.intro r18 r19)))
  rv_introT hR
  rv_symT hp stop [114] with [hL]
  exact hfin _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, hK⟩ hM3 hres

/-- The loop's head (instruction 60) with `k + 1` clones left, the next at `D + 24 j`. -/
def LInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  JRegs top D regs R ∧ R .x20 = m.getMem (regs .x11 + 8#64) ∧ R .x21 = m.getMem (regs .x11 + 16#64) ∧
    (R .x22).toNat = D.toNat + 24 * ((regs .x12).toNat - 1) ∧
    ∃ j, j + k + 1 = (regs .x12).toNat - 1 ∧ (R .x23).toNat = D.toNat + 24 * j ∧
      MemOk env m top ret regs Tactic.F M ∧ Blk env m D (regs .x12).toNat M ∧
      DoneV env (EmptyFormsT m (regs .x11)) M D (regs .x12).toNat j (env.next M).toNat

set_option rv_sym.heap true in
/-- **After the clone** (instruction 70): its header stored at `D + 24 j`, then the next clone (60) or the move
    (86). -/
theorem after {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hW : Windows env top m)
    (h16 : top.toNat % 16 = 0) {D : Word} {k j : Nat}
    (h60 : 0 < k → ∀ R M, LInv env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 60, ret, top⟩ :: rest, R, M⟩)
    (h86 : ∀ D H R M, JRegs top D regs R → (R .x23).toNat = D.toNat + 24 * ((regs .x12).toNat - 1) →
      0 < (regs .x12).toNat → MemOk env m top ret regs Tactic.F M → Blk env m D (regs .x12).toNat M →
      DoneV env (EmptyFormsT m (regs .x11)) M D (regs .x12).toNat ((regs .x12).toNat - 1) H →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 86, ret, top⟩ :: rest, R, M⟩)
    (R : Reg → Word) (M M1 : MachineState) {out : Word → Prop} (hR : JRegs top D regs R)
    (r20 : R .x20 = m.getMem (regs .x11 + 8#64)) (r21 : R .x21 = m.getMem (regs .x11 + 16#64))
    (h22 : (R .x22).toNat = D.toNat + 24 * ((regs .x12).toNat - 1)) (hjk : j + k + 1 = (regs .x12).toNat - 1)
    (h23 : (R .x23).toNat = D.toNat + 24 * j) (hM : MemOk env m top ret regs Tactic.F M)
    (hB : Blk env m D (regs .x12).toNat M)
    (hdone : DoneV env (EmptyFormsT m (regs .x11)) M D (regs .x12).toNat j (env.next M).toNat)
    (hF1 : env.Frame (top + 18446744073709551520#64) out M M1) (hS1 : env.Static M1) (hc1 : M1.code = M.code)
    (hout : ∀ b, out b → top.toNat - 96 ≤ b.toNat ∧ b.toNat < top.toNat - 72)
    (hV : VecT env M1 (top + 18446744073709551520#64) 24)
    (hfr : (vecLen M1 (top + 18446744073709551520#64)).toNat = 0 ∨
      env.Fresh M M1 (vecPtr M1 (top + 18446744073709551520#64))
        ((vecLen M1 (top + 18446744073709551520#64)).toNat * 24))
    (hFs : FormsT env M1 (vecPtr M1 (top + 18446744073709551520#64))
      (vecLen M1 (top + 18446744073709551520#64)).toNat)
    (hFt : CloneFormsFreshT.FreshTermsT env M M1 (vecPtr M1 (top + 18446744073709551520#64))
      (vecLen M1 (top + 18446744073709551520#64)).toNat)
    (hEc : EmptyFormsT m (regs .x11) → EmptyFormsT M1 (top + 18446744073709551520#64)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 70, ret, top⟩ :: rest, R, M1⟩ := by
  have hlay := env.layout
  have hge := hW.next_ge
  have hW1 := hW.heapEnd_le
  obtain ⟨b1, b2, b3⟩ := id hB
  have hnM := hM.2.1.2.1
  have hn1 := hF1.1
  have hnM1 := hF1.2.1
  have hcM : M1.code = m.code := hc1.trans hM.2.2.2
  obtain ⟨hM2, hB2, hD2⟩ := step_mem hlim hge hM hB (j := j) (by omega) h23 hdone hF1 hS1 hc1 hout hV hfr hFs hFt
    hEc
  have hw23 : ∀ c : Nat, c ≤ 16 → c % 8 = 0 → inWindow (R .x23 + BitVec.ofNat 64 c) 8 = true ∧
      (R .x23 + BitVec.ofNat 64 c).toNat % 8 = 0 := fun c hc hc8 => by
    rw [inWindow_iff, toNat_add_ofNat (by omega)]; exact ⟨by omega, by omega⟩
  have w8 := hw23 8 (by omega) rfl
  have w16 := hw23 16 (by omega) rfl
  have a80 : (top + 18446744073709551536#64).toNat % 8 = 0 := by
    rw [CloneFormsT.es (k := 80) rfl (by omega)]; omega
  have a88 : (top + 18446744073709551528#64).toNat % 8 = 0 := by
    rw [CloneFormsT.es (k := 88) rfl (by omega)]; omega
  have e23 : (R .x23 + 24#64).toNat = D.toNat + 24 * (j + 1) := by rw [toNat_add_ofNat (by omega)]; omega
  obtain ⟨r2, r8, r9, r18, r19, hK⟩ := hR
  have hR' := And.intro r2 (And.intro r8 (And.intro r9 (And.intro r18 (And.intro r19 (And.intro r20 r21)))))
  clear hdone hFs hFt hfr hV hF1 hM hEc
  rv_introT hR'
  rv_symT hp stop [60, 86] with [_hL]
  · -- another clone
    have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [e23, h22]; omega))
    clear hc
    exact h60 (by omega) _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, hK⟩, rfl, rfl, h22, j + 1, by omega, e23, hM2, hB2, hD2⟩
  · -- the last clone stored: the move
    have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [e23, h22] at this; omega
    clear hc
    have hj : j + 1 = (regs .x12).toNat - 1 := by omega
    rw [hj] at hD2
    exact h86 D _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, hK⟩ (by simp only [Tactic.rf]; rw [e23, hj]) (by omega) hM2 hB2 hD2

set_option rv_sym.heap true in
/-- **The loop**, from its head: a clone of the element stored at `D + 24 j`, then the next or the move. -/
theorem loop {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hnC : 96 + needC ≤ need)
    (hcl : CloneFormsFreshT.SpecT env p L.clone.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hpre : PreT env regs m) (h2 : regs .x2 = top) {D : Word} :
    ∀ k R M, LInv env m top ret regs D k R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 60, ret, top⟩ :: rest, R, M⟩ := by
  have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
  have hmove := move hp hL hk hlim hW h16 hpre h2
  refine Total.loop (I := rvIsa) (LInv env m top ret regs D) fun k R M hI ih => ?_
  obtain ⟨⟨r2, r8, r9, r18, r19, hK⟩, r20, r21, h22, j, hjk, h23, hM, hB, hdone⟩ := hI
  have haft := after hp hL hlim hW h16 (D := D) (k := k) (j := j)
    (fun hk0 R' M' h => ih (k - 1) R' M' (by omega) h) hmove
  have hlay := env.layout
  have hge := hW.next_ge
  have hW1 := hW.heapEnd_le
  have hnm := hM.2.1.1
  have hnM := hM.2.1.2.1
  have hnx : (env.next m).toNat ≤ env.heapEnd.toNat := by omega
  obtain ⟨-, -, -, -, hown1, hV, hn24⟩ := id hpre
  rw [h2] at hown1
  have hcM : M.code = m.code := hM.2.2.2
  have hSM : env.Static M := hM.2.2.1
  have hBt : BufT env M (m.getMem (regs .x11 + 16#64)) (m.getMem (regs .x11 + 8#64)) 24 :=
    (vecT_buf hV.1).1.mono hnm
  have hFt : FormsT env M (m.getMem (regs .x11 + 8#64)) (m.getMem (regs .x11 + 16#64)).toNat := by
    refine FormsT.keep_below hV.2 ?_ hnm fun b hb => hM.2.1.getMem_below_next hnx hb id
    rcases (vecT_buf hV.1).1 with h0 | ⟨-, h3, -⟩
    · exact .inl h0
    · unfold Env.Live at h3; exact .inr (by rw [Nat.mul_comm]; exact h3)
  have e96 := CloneFormsT.es (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  -- the element's `Form`s, if of capacity `0`, of length `0`
  have hEsrc : EmptyFormsT m (regs .x11) → ∀ k, k < (vecLen m (regs .x11)).toNat →
      vecLen M (vecPtr m (regs .x11) + BitVec.ofNat 64 (24 * k)) = 0#64 := fun hE k hk => by
    have hw := buf_word hV.1 hk
    have hF := hV.2 k hk
    have hle := (vecT_buf hF.1).2.1
    rw [hE k hk] at hle
    rw [vecLen_eq, hM.2.1.getMem_below_next hnx (by rw [toNat_add_ofNat (by omega)]; omega) id, ← vecLen_eq]
    exact BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat] at hle ⊢; omega)
  have hdone' : True → DoneV env (EmptyFormsT m (regs .x11)) M D (regs .x12).toNat j (env.next M).toNat :=
    fun _ => hdone
  have hM' : True → MemOk env m top ret regs Tactic.F M := fun _ => hM
  have hB' : True → Blk env m D (regs .x12).toNat M := fun _ => hB
  have hR := And.intro r2 (And.intro r8 (And.intro r9 (And.intro r18 (And.intro r19 (And.intro r20 r21)))))
  clear hdone hV hM hB
  rv_introT hR
  rv_symT hp stop [70] with [hL] using [hcl]
  all_goals try exact hFt
  exact haft _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, hK⟩ rfl rfl h22 hjk h23 (hM' trivial) (hB' trivial) (hdone' trivial)
    hret1_14 hret1_15 hret1_27 (fun b hb => by
      have h' : InRange (top + 18446744073709551520#64) 24 b := hb
      unfold InRange at h'; rw [e96] at h'; omega)
    ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩ (by rw [hret1_22]; exact hret1_23)
    (by rw [hret1_22]; exact hret1_24) (by rw [hret1_22]; exact hret1_25)
    fun hE k hk => by rw [hret1_22] at hk; rw [(hret1_26 k hk).1]; exact hEsrc hE k hk

/-! ## The entry -/

/-- The prologue's nine saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)

/-- **After the prologue and a call writing nothing of the caller's** (`alloc`, the drop): `MemOk`. -/
theorem call_ok {env : Env} {m m1 : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hF : env.Frame (top + 18446744073709551520#64) Tactic.F (saved m top ret regs) m1)
    (hS1 : env.Static m1) (hc : m1.code = (saved m top ret regs).code)
    (hk : ∀ a, top + 18446744073709551520#64 ≤ a → m1.getMem a = (saved m top ret regs).getMem a) :
    MemOk env m top ret regs Tactic.F m1 := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 96 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => CloneFormsT.es hc (by omega)
  have e1 := g 18446744073709551608#64 8 rfl (by omega)
  have e2 := g 18446744073709551600#64 16 rfl (by omega)
  have e3 := g 18446744073709551592#64 24 rfl (by omega)
  have e4 := g 18446744073709551584#64 32 rfl (by omega)
  have e5 := g 18446744073709551576#64 40 rfl (by omega)
  have e6 := g 18446744073709551568#64 48 rfl (by omega)
  have e7 := g 18446744073709551560#64 56 rfl (by omega)
  have e8 := g 18446744073709551552#64 64 rfl (by omega)
  have e9 := g 18446744073709551544#64 72 rfl (by omega)
  have e96 := g 18446744073709551520#64 96 rfl (by omega)
  have hsl : Slots (saved m top ret regs) top ret regs := by
    simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9] at h'; omega)])
  have hF0 : env.Frame top Tactic.F m (saved m top ret regs) := by
    simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  refine ⟨slots_keep (by omega) (fun a h1 _ => hk a (by rw [BitVec.le_def, e96]; omega)) hsl,
    Tactic.frame_call hF0 hF (by omega), hS1, ?_⟩
  rw [hc]; simp only [saved, MachineState.code_setMem]

set_option rv_sym.heap true in
/-- **`<Vec<Form> as SpecFromElem>::from_elem` is total**, with 96 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needC needD needH : Nat} (hnA : 96 + needA ≤ need) (hnC : 96 + needC ≤ need)
    (hnD : 96 + needD ≤ need) (hnH : 96 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcl : CloneFormsFreshT.SpecT env p L.clone.idx needC)
    (hdr : DropSpecT env p L.dropGlueVecForm.idx needD) (hhe : Aborts env p L.handleError.idx needH) :
    SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [60, 86, 114] with [hL] using [hal', hdr, hhe]
  all_goals
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
    have hpre : PreT env regs m := ⟨⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, hpre_10, ⟨hpre_11, hpre_12⟩,
      ⟨⟨hpre_13, ⟨hpre_14, hpre_15, hpre_16, hpre_17⟩, hpre_18⟩, hpre_19⟩, hpre_20⟩
    have s24 : (regs .x12 <<< 4 + regs .x12 <<< 3).toNat = 24 * (regs .x12).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      omega
  · -- no elements: the element dropped, the empty vector
    have hM1 := call_ok hlim hpre_5 hret1_14 hret1_15 hret1_16 keep1_1
    exact fin hp hL hk hlim hpre_22 hpre_21 hpre hpre_2 0#64 8#64 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hM1
      (.inl ⟨by rw [hc]; rfl, rfl, rfl⟩)
  · rw [s24]; omega
  · -- one element: the move
    have hM2 := call_ok hlim hpre_5 hret2_14 hret2_15 hret2_19 keep2_1
    have hn1 : (regs .x12).toNat = 1 := by rw [hc]; rfl
    rw [s24] at hret2_18
    exact move hp hL hk hlim hpre_22 hpre_21 hpre hpre_2 (r2 .x10) 0 _ m2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (by simp only [Tactic.rf]; omega) (by omega) hM2 ⟨hret2_16, by omega, hret2_17⟩
      ⟨fun _ h => absurd h (by omega), fun _ _ _ h => absurd h (by omega), fun _ _ h => absurd h (by omega)⟩
  · -- into the loop
    have hM2 := call_ok hlim hpre_5 hret2_14 hret2_15 hret2_19 keep2_1
    have hn0 : (regs .x12).toNat ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq h)
    have hn1 : (regs .x12).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq h)
    rw [s24] at hret2_18
    refine loop hp hL hnC hcl hk hstop hpre_3 hpre_22 hpre_21 hpre hpre_2 (D := r2 .x10) ((regs .x12).toNat - 2) _ _
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_, 0, by omega, by simp only [Tactic.rf]; omega,
        hM2, ⟨hret2_16, by omega, hret2_17⟩,
        ⟨fun _ h => absurd h (by omega), fun _ _ _ h => absurd h (by omega), fun _ _ h => absurd h (by omega)⟩⟩
    simp only [Tactic.rf]
    rw [BitVec.toNat_add, BitVec.toNat_add, s24]
    simp only [BitVec.toNat_ofNat]
    omega

end Rv64mc.Proof.Layout.FromElemVecFormT

/-- info: 'Rv64mc.Proof.Layout.FromElemVecFormT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.FromElemVecFormT.total
