/-
  Rv64mc.Proof.Layout.CloneFormsT

  `<Vec<Form> as Clone>::clone` is total: called with the result's slot (`a0`) and the source's buffer and length
  (`a1`, `a2`), it checks the length against `isize::MAX / 24` (a word of the static data), allocates the result's
  block, and clones each `Form` in turn: it checks the `Form`'s length against `isize::MAX / 40` (another word),
  allocates its terms' block, and for each term clones the monomial (`Vec<usize>::clone`) and copies the
  coefficient's two words. Its result is a vector of the source's length (`CloneT.ClonePostT`: `VecT`, its buffer
  fresh unless empty) whose elements are `Form`s (`FormReprT.FormsT`); the run ends with the guest's abort
  (`AbortStop`) where `alloc` or `handle_error` does. A safety-only contract (the function is class D: no spec); it
  does not state the terms' values.

  The precondition: the result's slot a caller's (`SretPre`), in a window and 8-byte aligned; the source the elements
  of a vector's buffer (`BufT`, the length for the capacity), each a `Form` (`FormsT`). The two bounds' words are
  read in the static data (`DataRef.InData`, an environment fact); their values do not matter for safety, every
  size being bounded by the source's blocks below `NEXT`.

  The body is cut at the outer loop's head (instruction 78, measure the `Form`s left), the inner loop's head (130,
  measure the terms left), the join where a cloned `Form`'s header is stored (194) and the return (226). Every part
  keeps `MemOk` (the thirteen slots, the frame, the static data, the code). The `Form`s cloned so far (`DoneT`) have
  their terms' blocks between the result's block and a bound `H`, the `NEXT` at the head of the pass, so the pass's
  stores and calls, all at or above `H` or on the stack, keep them.

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`, `Slots`, `MemOk`, `DoneT`, `OInv`, `IInv`, `JInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.FormReprT
import Rv64mc.Proof.Runtime.CloneT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.FromElemT
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecForm.AsClone.Clone

namespace Rv64mc.Proof.Layout.CloneFormsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT CloneSpecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Gen.Alloc.Vec.VecForm.AsClone.Clone (Link tmpl d_c8_d6dfd6bc_words d_c8_51ab739d_words)

/-- The total precondition: the result's slot a caller's, in a window and 8-byte aligned; the source (`a1`, `a2`)
    the elements of a vector's buffer, each a `Form`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (regs .x12) (regs .x11) 24 ∧ FormsT env m (regs .x11) (regs .x12).toNat

/-- The total postcondition: the result a vector's of the source's length, its buffer fresh unless empty, its
    elements `Form`s. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  ClonePostT env 24 regs m r' m' ∧ FormsT env m' (vecPtr m' (regs .x10)) (regs .x12).toNat

/-- **The total contract of `<Vec<Form> as Clone>::clone`**. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

/-! ## The frame -/

/-- The prologue's thirteen saved words in `M`, at `top - 8` down to `top - 104`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26 ∧
    M.getMem (top + 18446744073709551512#64) = regs .x27

/-- What every part keeps of memory: the slots, the frame with `out`, the static data, the code. -/
def MemOk (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (out : Word → Prop)
    (M : MachineState) : Prop :=
  Slots M top ret regs ∧ env.Frame top out m M ∧ env.Static M ∧ M.code = m.code

/-- `top + c` as a number, for `c` the word of `-k`, `k` at most the frame's `176`. -/
theorem es {top c : Word} {k : Nat} (hc : c.toNat + k = 2 ^ 64) (hk : k ≤ top.toNat) :
    (top + c).toNat = top.toNat - k :=
  Runtime.CloneT.toNat_add_neg hc hk

theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 176 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 104 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 104 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := es (top := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := hsl
  exact ⟨(g _ 8 rfl (by omega) (by omega)).trans s1, (g _ 16 rfl (by omega) (by omega)).trans s2,
    (g _ 24 rfl (by omega) (by omega)).trans s3, (g _ 32 rfl (by omega) (by omega)).trans s4,
    (g _ 40 rfl (by omega) (by omega)).trans s5, (g _ 48 rfl (by omega) (by omega)).trans s6,
    (g _ 56 rfl (by omega) (by omega)).trans s7, (g _ 64 rfl (by omega) (by omega)).trans s8,
    (g _ 72 rfl (by omega) (by omega)).trans s9, (g _ 80 rfl (by omega) (by omega)).trans s10,
    (g _ 88 rfl (by omega) (by omega)).trans s11, (g _ 96 rfl (by omega) (by omega)).trans s12,
    (g _ 104 rfl (by omega) (by omega)).trans s13⟩

/-- **A store into a block allocated since the entry**: `MemOk`, `NEXT` and every word apart from it kept. -/
theorem heap_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hM : MemOk env m top ret regs out M)
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

/-- **A store into the frame below the slots** (`top - 176` to `top - 104`): `MemOk`, `NEXT` and every other word
    kept. -/
theorem frame_store {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hM : MemOk env m top ret regs out M)
    (ha1 : top.toNat - 176 ≤ a.toNat) (ha2 : a.toNat + 8 ≤ top.toNat - 104) :
    MemOk env m top ret regs out (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M ∧
      ∀ b : Word, b ≠ a → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  exact ⟨⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_slot hF (by omega) (by omega), Env.static_setMem_stack hS (by omega),
    by rw [MachineState.code_setMem, hc]⟩, Env.next_setMem_stack (by omega),
    fun b hb => MachineState.getMem_setMem_ne hb⟩

/-- **One store into the frame's `out`**, a word apart from the slots and in a window. -/
theorem out_store {env : Env} {m M : MachineState} {top ret b v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hb : SretVecOut regs m b) (hwin : InWin env b 8)
    (hsep : b.toNat + 8 ≤ top.toNat - 104 ∨ top.toNat ≤ b.toNat) (hM : MemOk env m top ret regs (SretVecOut regs m) M) :
    MemOk env m top ret regs (SretVecOut regs m) (M.setMem b v) ∧ env.next (M.setMem b v) = env.next M := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hn : b ≠ env.nextAddr := fun e => by rw [e] at hwin; unfold InWin at hwin; omega
  exact ⟨⟨slots_keep (by omega) (fun a h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_out hF hb hn, Tactic.static_store hS (by unfold InWin at hwin; omega),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hn⟩

/-! ## The `Form`s cloned so far -/

/-- **The first `j` of the result's `n` `Form`s** from `D`, each a `Form` whose terms' block lies between the
    result's block's end and `H`. -/
def DoneT (env : Env) (M : MachineState) (D : Word) (n j H : Nat) : Prop :=
  ∀ i, i < j → FormT env M (D + BitVec.ofNat 64 (24 * i)) ∧
    ((vecLen M (D + BitVec.ofNat 64 (24 * i))).toNat = 0 ∨
      (D.toNat + 24 * n ≤ (vecPtr M (D + BitVec.ofNat 64 (24 * i))).toNat ∧
        (vecPtr M (D + BitVec.ofNat 64 (24 * i))).toNat + 40 * (vecLen M (D + BitVec.ofNat 64 (24 * i))).toNat ≤ H))

/-- **`DoneT` is kept** by a memory agreeing on the first `j` headers and on `[D + 24 n, H)`, `NEXT` no lower. -/
theorem DoneT.keep {env : Env} {M M' : MachineState} {D : Word} {n j H : Nat} (h : DoneT env M D n j H)
    (hD : D.toNat + 24 * n < 2 ^ 64) (hj : j ≤ n) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ b : Word, (D.toNat ≤ b.toNat ∧ b.toNat < D.toNat + 24 * j) ∨ (D.toNat + 24 * n ≤ b.toNat ∧ b.toNat < H) →
      M'.getMem b = M.getMem b) : DoneT env M' D n j H := by
  intro i hi
  obtain ⟨hF, hfoot⟩ := h i hi
  have e : (D + BitVec.ofNat 64 (24 * i)).toNat = D.toNat + 24 * i := toNat_add_ofNat (by omega)
  have hk1 : ∀ b : Word, (D + BitVec.ofNat 64 (24 * i)).toNat ≤ b.toNat →
      b.toNat < (D + BitVec.ofNat 64 (24 * i)).toNat + 24 → M'.getMem b = M.getMem b :=
    fun b h1 h2 => hk b (.inl ⟨by omega, by omega⟩)
  have hlt := vecT_lt hF.1
  have e8 : (D + BitVec.ofNat 64 (24 * i) + 8#64).toNat = (D + BitVec.ofNat 64 (24 * i)).toNat + 8 :=
    toNat_add_ofNat (by omega)
  have e16 : (D + BitVec.ofNat 64 (24 * i) + 16#64).toNat = (D + BitVec.ofNat 64 (24 * i)).toNat + 16 :=
    toNat_add_ofNat (by omega)
  have ep : vecPtr M' (D + BitVec.ofNat 64 (24 * i)) = vecPtr M (D + BitVec.ofNat 64 (24 * i)) := by
    rw [vecPtr_eq, vecPtr_eq]; exact hk1 _ (by rw [e8]; omega) (by rw [e8]; omega)
  have el : vecLen M' (D + BitVec.ofNat 64 (24 * i)) = vecLen M (D + BitVec.ofNat 64 (24 * i)) := by
    rw [vecLen_eq, vecLen_eq]; exact hk1 _ (by rw [e16]; omega) (by rw [e16]; omega)
  refine ⟨hF.keep hn hk1 fun b h1 h2 => hk b (.inr ?_), by rw [ep, el]; exact hfoot⟩
  rcases hfoot with h0 | ⟨h3, h4⟩
  · omega
  · omega

/-- **The result's block** `D` of `n` `Form`s: allocated since the entry, 8-byte aligned. -/
def Blk (env : Env) (m : MachineState) (D : Word) (n : Nat) (M : MachineState) : Prop :=
  (env.next m).toNat ≤ D.toNat ∧ D.toNat + 24 * n ≤ (env.next M).toNat ∧ D.toNat % 8 = 0

/-! ## The return -/

/-- The facts of the precondition every part reads. -/
def Args (env : Env) (m : MachineState) (top : Word) (regs : Reg → Word) : Prop :=
  env.stackLimit.toNat + 176 ≤ top.toNat ∧ Windows env top m ∧ top.toNat % 16 = 0 ∧
    env.Owned m top (regs .x10) 24 ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (regs .x12) (regs .x11) 24 ∧ FormsT env m (regs .x11) (regs .x12).toNat

/-- **The result's three stores** at `sret`: `MemOk` and `NEXT` kept, the three words read back, every word apart
    from them kept. -/
theorem hdr3 {env : Env} {m M : MachineState} {top ret v0 v1 v2 : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hown : env.Owned m top (regs .x10) 24)
    (hwin : InWin env (regs .x10) 24) (hM : MemOk env m top ret regs (SretVecOut regs m) M) :
    MemOk env m top ret regs (SretVecOut regs m)
        (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2) ∧
      env.next (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2) =
        env.next M ∧
      (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2).getMem (regs .x10) =
        v0 ∧
      (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2).getMem
        (regs .x10 + 8#64) = v1 ∧
      (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2).getMem
        (regs .x10 + 16#64) = v2 ∧
      ∀ b : Word, (b.toNat < (regs .x10).toNat ∨ (regs .x10).toNat + 24 ≤ b.toNat) →
        (((M.setMem (regs .x10) v0).setMem (regs .x10 + 8#64) v1).setMem (regs .x10 + 16#64) v2).getMem b =
          M.getMem b := by
  have hlay := env.layout
  have h24 := hown.2
  have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hsep : ∀ k, k ≤ 16 → (regs .x10).toNat + k + 8 ≤ top.toNat - 104 ∨ top.toNat ≤ (regs .x10).toNat + k :=
    fun k hk => by have := hM.2.1.2.1; have := hM.2.1.1; rcases hown.1 with h1 | h1 <;> omega
  have hout : ∀ k : Nat, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → SretVecOut regs m b :=
    fun k hk b hb => by show InRange (regs .x10) Layouts.Vec.byteSize b; unfold InRange Layouts.Vec.byteSize; omega
  have hw : ∀ k : Nat, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → InWin env b 8 :=
    fun k hk b hb => Runtime.MemsetT.InWin.sub hwin (by omega) (by omega)
  obtain ⟨m1, n1⟩ := out_store (v := v0) hlim (hout 0 (by omega) _ rfl) (hw 0 (by omega) _ rfl) (hsep 0 (by omega)) hM
  obtain ⟨m2, n2⟩ := out_store (v := v1) hlim (hout 8 (by omega) _ e8) (hw 8 (by omega) _ e8)
    (by rw [e8]; exact hsep 8 (by omega)) m1
  obtain ⟨m3, n3⟩ := out_store (v := v2) hlim (hout 16 (by omega) _ e16) (hw 16 (by omega) _ e16)
    (by rw [e16]; exact hsep 16 (by omega)) m2
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  refine ⟨m3, by rw [n3, n2, n1], ?_, ?_, MachineState.getMem_setMem_eq, fun b hb => ?_⟩
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega))]

/-- **The result from its header's words**: capacity and length `n`, the buffer `D` of `n` `Form`s fresh since `m`
    unless `n = 0`. -/
theorem post_ok {env : Env} {regs : Reg → Word} {m M : MachineState} {D : Word}
    (hwin : InWin env (regs .x10) 24) (hal : (regs .x10).toNat % 8 = 0)
    (h0 : M.getMem (regs .x10) = regs .x12) (h8 : M.getMem (regs .x10 + 8#64) = D)
    (h16 : M.getMem (regs .x10 + 16#64) = regs .x12)
    (hD : (regs .x12).toNat = 0 ∨ (0x10000000 ≤ D.toNat ∧ (env.next m).toNat ≤ D.toNat ∧
      D.toNat + (regs .x12).toNat * 24 ≤ (env.next M).toNat ∧ D.toNat % 8 = 0))
    (hn : (regs .x12).toNat * 24 < 2 ^ 63) {r : Reg → Word} : ClonePostT env 24 regs m r M := by
  have hc : rvCapAt (regs .x10) = regs .x10 := rvCapAt_eq _
  have hp : rvPtrAt (regs .x10) = regs .x10 + 8#64 := rfl
  refine ⟨⟨hwin, ⟨Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega),
    hal, ?_, by rw [hc, h0]; exact hn⟩, by rw [vecLen_eq, vecCap_eq, h0, h16]⟩, by rw [vecLen_eq, h16], ?_⟩
  · rw [hc, hp, h0, h8]
    rcases hD with h | ⟨h1, -, h3, h4⟩
    · exact .inl h
    · exact .inr ⟨h1, by unfold Env.Live; omega, h4⟩
  · rw [vecPtr_eq, h8]
    rcases hD with h | ⟨-, h2, h3, -⟩
    · exact .inl h
    · exact .inr ⟨h2, by omega⟩

/-- The registers the return reads: the stack pointer, `sret`, the length, the result's block. -/
def XRegs (top D : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551440#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x10 = regs .x12 ∧ R .x18 = D

set_option rv_sym.heap true in
/-- **The return**, from instruction 226: the header `(n, D, n)` stored at `sret`, the saved registers. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) :
    ∀ D R M, XRegs top D regs R → MemOk env m top ret regs Tactic.F M →
      ((regs .x12).toNat = 0 ∨ (Blk env m D (regs .x12).toNat M ∧
        ∃ H, DoneT env M D (regs .x12).toNat (regs .x12).toNat H ∧ H ≤ (env.next M).toNat)) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 226, ret, top⟩ :: rest, R, M⟩ := by
  intro D R M hR hM hD
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hown, hwin, hal, hB, -⟩ := hA
  obtain ⟨hsl0, hF0, hS0, hc0⟩ := hM
  have hM' : MemOk env m top ret regs (SretVecOut regs m) M := ⟨hsl0, Tactic.frame_weaken hF0, hS0, hc0⟩
  obtain ⟨hM3, hn3, r0, r8, r16, rk⟩ := hdr3 (v0 := regs .x12) (v1 := D) (v2 := regs .x12) hstk hown hwin hM'
  have hge := hW.next_ge
  have hnm := hF0.1
  have hnM := hF0.2.1
  have hW1 := hW.heapEnd_le
  have hsmall : (regs .x12).toNat * 24 ≤ 0x78000000 := by
    rcases hB with h | ⟨-, h2, -⟩
    · rw [h]; omega
    · unfold Env.Live at h2; omega
  have hPost : ∀ r, PostT env regs m r
      (((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) D).setMem (regs .x10 + 16#64) (regs .x12)) := by
    intro r
    refine ⟨post_ok hwin hal r0 r8 r16 ?_ (by omega), ?_⟩
    · rcases hD with h | ⟨⟨b1, b2, b3⟩, -⟩
      · exact .inl h
      · exact .inr ⟨by omega, b1, by rw [hn3]; omega, b3⟩
    · rw [vecPtr_eq, r8]
      intro j hj
      rcases hD with h | ⟨⟨b1, b2, b3⟩, H, hdone, hH⟩
      · omega
      have hd2 := DoneT.keep (M' := ((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) D).setMem
        (regs .x10 + 16#64) (regs .x12)) hdone (by omega) (Nat.le_refl _) (by rw [hn3]) fun b hb => rk b (by
          have := hown.2
          rcases hown.1 with h1 | h1 <;> rcases hb with h2 | h2 <;> omega)
      exact (hd2 j hj).1
  obtain ⟨-, hF3, hS3, hc3⟩ := hM3
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13⟩ := hsl0
  have h24 := hown.2
  have := hW.nextAddr_ge
  have hw : ∀ k : Nat, k ≤ 16 → inWindow (regs .x10 + BitVec.ofNat 64 k) 8 = true := fun k hk => by
    have e : (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k := toNat_add_ofNat (by omega)
    rw [inWindow_iff, e]; unfold InWin at hwin; omega
  have w0 : inWindow (regs .x10) 8 = true := by simpa using hw 0 (by omega)
  have w8 := hw 8 (by omega)
  have w16 := hw 16 (by omega)
  rv_introT hR
  rv_symT hp with [_hL]
  all_goals try first | exact (hPost (fun _ => 0#64)).1.1.2.1.2.2.1 | exact (hPost (fun _ => 0#64)).1.1.2.1.2.2.2
  · have h := (hPost (fun _ => 0#64)).1.2.2
    rwa [vecPtr_eq, r8] at h
  · have h := (hPost (fun _ => 0#64)).2
    rwa [vecPtr_eq, r8] at h

/-! ## The join: a cloned `Form`'s header stored -/

/-- **A new `Form`'s header** `(c, P, L)` at `a`: no terms (capacity `0`), or `L` terms in a block `P` below `NEXT`. -/
theorem new_form {env : Env} {M : MachineState} {a c P L : Word} (hw : InWin env a 24) (hal : a.toNat % 8 = 0)
    (h0 : M.getMem a = c) (h8 : M.getMem (a + 8#64) = P) (h16 : M.getMem (a + 16#64) = L)
    (hL : L.toNat * 40 < 2 ^ 63)
    (hn : (c.toNat = 0 ∧ L.toNat = 0) ∨ (c = L ∧ 0x10000000 ≤ P.toNat ∧ P.toNat + 40 * L.toNat ≤ (env.next M).toNat ∧
      P.toNat % 8 = 0 ∧ TermsT env M P L.toNat)) : FormT env M a := by
  have hv : VecT env M a 40 := by
    refine ⟨hw, ⟨Runtime.MemsetT.InWin.sub hw (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega),
      hal, ?_, ?_⟩, ?_⟩
    · rw [rvCapAt_eq, rvPtrAt_eq, h0, h8]
      rcases hn with ⟨h1, -⟩ | ⟨rfl, h2, h3, h4, -⟩
      · exact .inl h1
      · exact .inr ⟨h2, by unfold Env.Live; omega, h4⟩
    · rw [rvCapAt_eq, h0]
      rcases hn with ⟨h1, -⟩ | ⟨rfl, -⟩
      · rw [h1]; omega
      · exact hL
    · rw [vecLen_eq, vecCap_eq, h0, h16]
      rcases hn with ⟨h1, h2⟩ | ⟨rfl, -⟩ <;> omega
  refine ⟨hv, ?_⟩
  rw [vecPtr_eq, vecLen_eq, h8, h16]
  rcases hn with ⟨-, h2⟩ | ⟨-, -, -, -, h5⟩
  · intro t ht; omega
  · exact h5

/-- **Terms are kept** by a memory agreeing on their block, `NEXT` no lower. -/
theorem TermsT.keep {env : Env} {M M' : MachineState} {P : Word} {L : Nat} (h : TermsT env M P L)
    (hP : P.toNat + 40 * L < 2 ^ 64) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ b : Word, P.toNat ≤ b.toNat → b.toNat < P.toNat + 40 * L → M'.getMem b = M.getMem b) :
    TermsT env M' P L := by
  intro t ht
  have et : (P + BitVec.ofNat 64 (40 * t)).toNat = P.toNat + 40 * t := toNat_add_ofNat (by omega)
  refine vecT_keep (h t ht) hn fun b h1 h2 => hk b (by omega) ?_
  rw [et] at h2
  have : 40 * t + 40 ≤ 40 * L := by omega
  omega

/-- `DoneT`'s bound only grows. -/
theorem DoneT.mono {env : Env} {M : MachineState} {D : Word} {n j H H' : Nat} (h : DoneT env M D n j H)
    (hH : H ≤ H') : DoneT env M D n j H' := fun i hi =>
  ⟨(h i hi).1, (h i hi).2.imp id fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩

/-- **The join's three stores** at `A = D + 24 j`, the header `(c, P, L)` of a new `Form` with its terms' block
    between `H` and `NEXT`: `MemOk` and `NEXT` kept, `j + 1` `Form`s cloned. -/
theorem join_mem {env : Env} {m M : MachineState} {top ret A D c P L : Word} {regs : Reg → Word} {n j H : Nat}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hge : 0x10000000 ≤ (env.next m).toNat)
    (hM : MemOk env m top ret regs Tactic.F M) (hB : Blk env m D n M) (hA : A = D + BitVec.ofNat 64 (24 * j))
    (hj : j < n) (hDH : D.toNat + 24 * n ≤ H) (hH : H ≤ (env.next M).toNat) (hdone : DoneT env M D n j H)
    (hL : L.toNat * 40 < 2 ^ 63)
    (hnew : (c.toNat = 0 ∧ L.toNat = 0) ∨ (c = L ∧ H ≤ P.toNat ∧ P.toNat + 40 * L.toNat ≤ (env.next M).toNat ∧
      P.toNat % 8 = 0 ∧ TermsT env M P L.toNat)) :
    MemOk env m top ret regs Tactic.F (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L) ∧
      env.next (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L) = env.next M ∧
      DoneT env (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L) D n (j + 1)
        (env.next (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L)).toNat := by
  have hlay := env.layout
  obtain ⟨b1, b2, b3⟩ := hB
  have hnM := hM.2.1.2.1
  have eA : A.toNat = D.toNat + 24 * j := by rw [hA]; exact toNat_add_ofNat (by omega)
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  obtain ⟨m1, n1, k1⟩ := heap_store (a := A) (v := c) hlim hM (by omega) (by omega)
  obtain ⟨m2, n2, k2⟩ := heap_store (a := A + 8#64) (v := P) hlim m1 (by omega) (by rw [n1]; omega)
  obtain ⟨m3, n3, k3⟩ := heap_store (a := A + 16#64) (v := L) hlim m2 (by omega) (by rw [n2, n1]; omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hk : ∀ b : Word, (b.toNat < A.toNat ∨ A.toNat + 24 ≤ b.toNat) →
      (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L).getMem b = M.getMem b := fun b hb => by
    rw [k3 b (ne _ _ (by omega)), k2 b (ne _ _ (by omega)), k1 b (ne _ _ (by omega))]
  have hN : env.next (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L) = env.next M := by
    rw [n3, n2, n1]
  have r0 : (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L).getMem A = c := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L).getMem (A + 8#64) = P := by
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r16 : (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L).getMem (A + 16#64) = L :=
    MachineState.getMem_setMem_eq
  have hold := (DoneT.keep hdone (by omega) (by omega) (by rw [hN]) fun b hb => hk b (by omega)).mono
    (H' := (env.next M).toNat) hH
  have hF : FormT env (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L) A := by
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
  · rw [hi, ← hA]
    refine ⟨hF, ?_⟩
    rw [vecLen_eq, vecPtr_eq, r8, r16]
    rcases hnew with ⟨-, h⟩ | ⟨-, h2, h3, -, -⟩
    · exact .inl h
    · exact .inr ⟨by omega, h3⟩

/-- The registers every part keeps: the stack pointer, the length, `sret`, the result's block. -/
def JRegs (top D : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551440#64 ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x18 = D

/-- The outer loop's head (instruction 78) with `k + 1` `Form`s left, from `Form` `j` (`x19`, `x24`). -/
def OInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  JRegs top D regs R ∧ (R .x23).toNat = (regs .x11).toNat + 24 * (regs .x12).toNat ∧
    ∃ j, j + k + 1 = (regs .x12).toNat ∧ (R .x19).toNat = (regs .x11).toNat + 24 * j ∧ (R .x24).toNat = j ∧
      (R .x25).toNat = k + 1 ∧ Blk env m D (regs .x12).toNat M ∧
      DoneT env M D (regs .x12).toNat j (env.next M).toNat ∧ MemOk env m top ret regs Tactic.F M

set_option rv_sym.heap true in
/-- **The join**, from instruction 194: `Form` `j`'s header stored at `D + 24 j`, then the next `Form` (78) or the
    return. -/
theorem join {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {D : Word} {H j k : Nat}
    (h78 : 0 < k → ∀ R M, OInv env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, JRegs top D regs R → (R .x19).toNat = (regs .x11).toNat + 24 * j → (R .x24).toNat = j →
      (R .x25).toNat = k + 1 → j + k + 1 = (regs .x12).toNat →
      (R .x23).toNat = (regs .x11).toNat + 24 * (regs .x12).toNat → (R .x26).toNat * 40 < 2 ^ 63 →
      ((R .x13).toNat = 0 ∧ (R .x26).toNat = 0 ∨ R .x13 = R .x26 ∧ H ≤ (R .x10).toNat ∧
        (R .x10).toNat + 40 * (R .x26).toNat ≤ (env.next M).toNat ∧ (R .x10).toNat % 8 = 0 ∧
        TermsT env M (R .x10) (R .x26).toNat) →
      Blk env m D (regs .x12).toNat M → D.toNat + 24 * (regs .x12).toNat ≤ H → H ≤ (env.next M).toNat →
      DoneT env M D (regs .x12).toNat j H → MemOk env m top ret regs Tactic.F M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 194, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR h19 h24 h25 hjk h23 hL40 hnew hB hDH hH hdone hM
  have hlay := env.layout
  have hex := exit hp hL hk hA
  obtain ⟨hstk, hW, h16, hown, hwin, hal, hsrc, hforms⟩ := id hA
  obtain ⟨b1, b2, b3⟩ := id hB
  have hge := hW.next_ge
  have hnM := hM.2.1.2.1
  have hW1 := hW.heapEnd_le
  have hsrc' : (regs .x11).toNat + 24 * (regs .x12).toNat ≤ (env.next m).toNat := by
    rcases hsrc with h | ⟨-, h2, -⟩
    · omega
    · unfold Env.Live at h2; omega
  have eS : (R .x24 <<< 4 + R .x24 <<< 3).toNat = 24 * j := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq, h24]
    omega
  have eA : (D + (R .x24 <<< 4 + R .x24 <<< 3)).toNat = D.toNat + 24 * j := by
    rw [BitVec.toNat_add, eS]; omega
  have hAw : D + (R .x24 <<< 4 + R .x24 <<< 3) = D + BitVec.ofNat 64 (24 * j) :=
    BitVec.eq_of_toNat_eq (by rw [eA, toNat_add_ofNat (by omega)])
  have e8 : (D + (R .x24 <<< 4 + R .x24 <<< 3) + 8#64).toNat = D.toNat + 24 * j + 8 := by
    rw [toNat_add_ofNat (by omega), eA]
  have e16 : (D + (R .x24 <<< 4 + R .x24 <<< 3) + 16#64).toNat = D.toNat + 24 * j + 16 := by
    rw [toNat_add_ofNat (by omega), eA]
  obtain ⟨m3, n3, d3⟩ := join_mem (A := D + (R .x24 <<< 4 + R .x24 <<< 3)) (c := R .x13) (P := R .x10) (L := R .x26)
    hstk hge hM hB hAw (by omega) hDH hH hdone hL40 hnew
  have e19 : (R .x19 + 24#64).toNat = (regs .x11).toNat + 24 * (j + 1) := by
    rw [toNat_add_ofNat (by omega)]; omega
  have e24 : (R .x24 + 1#64).toNat = j + 1 := by rw [toNat_add_ofNat (by omega)]; omega
  have e25 : (R .x25 + 18446744073709551615#64).toNat = k := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hcM : M.code = m.code := hM.2.2.2
  rv_introT hR
  rv_symT hp stop [78, 226] with [hL]
  · have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [e25, h]; rfl)) hc
      · exact h
    clear hc
    exact h78 hk0 _ _ ⟨⟨rfl, rfl, rfl, rfl⟩, h23, j + 1, by omega, e19, e24,
      by show (R .x25 + 18446744073709551615#64).toNat = k - 1 + 1; omega,
      ⟨b1, by rw [n3]; exact b2, b3⟩, d3, m3⟩
  · have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [e25] at this; exact this
    clear hc
    have hj1 : j + 1 = (regs .x12).toNat := by omega
    rw [hj1] at d3
    exact hex D _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ m3 (.inr ⟨⟨b1, by rw [n3]; exact b2, b3⟩, _, d3, Nat.le_refl _⟩)

/-! ## The inner loop's memory -/

/-- **A vector's header copied** to `A`, in a window and aligned, `NEXT` no lower. -/
theorem vecT_copy {env : Env} {M M' : MachineState} {s A : Word} {sz : Nat} (h : VecT env M s sz)
    (hw : InWin env A 24) (hal : A.toNat % 8 = 0) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (h0 : M'.getMem A = M.getMem s) (h8 : M'.getMem (A + 8#64) = M.getMem (s + 8#64))
    (h16 : M'.getMem (A + 16#64) = M.getMem (s + 16#64)) : VecT env M' A sz := by
  obtain ⟨-, ⟨-, -, h3, h4⟩, h5⟩ := h
  rw [rvCapAt_eq, rvPtrAt_eq] at h3
  rw [rvCapAt_eq] at h4
  rw [vecLen_eq, vecCap_eq] at h5
  refine ⟨hw, ⟨Runtime.MemsetT.InWin.sub hw (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega),
    hal, ?_, ?_⟩, ?_⟩
  · rw [rvCapAt_eq, rvPtrAt_eq, h0, h8]; exact h3.mono hn
  · rw [rvCapAt_eq, h0]; exact h4
  · rw [vecLen_eq, vecCap_eq, h0, h16]; exact h5

/-- **A call writing at most the clone's slot** (`top - 144` to `top - 120`): `MemOk` kept, every word apart from
    the slot below `NEXT` before the call or at or above the stack pointer kept. -/
theorem call_keep {env : Env} {m M M' : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hM : MemOk env m top ret regs Tactic.F M)
    (hF : env.Frame (top + 18446744073709551440#64) out M M') (hSt : env.Static M') (hc : M'.code = M.code)
    (hout : ∀ b, out b → top.toNat - 144 ≤ b.toNat ∧ b.toNat < top.toNat - 120)
    (hkeep : ∀ a : Word, a.toNat < (env.next M).toNat ∨ (top + 18446744073709551440#64).toNat ≤ a.toNat → ¬ out a →
      M'.getMem a = M.getMem a) :
    MemOk env m top ret regs Tactic.F M' ∧ (env.next M).toNat ≤ (env.next M').toNat ∧
      ∀ a : Word, (a.toNat < (env.next M).toNat ∨ top.toNat - 176 ≤ a.toNat) →
        (a.toNat < top.toNat - 144 ∨ top.toNat - 120 ≤ a.toNat) → M'.getMem a = M.getMem a := by
  have hlay := env.layout
  obtain ⟨hsl, hF0, -, hc0⟩ := hM
  have e176 := es (top := top) (c := 18446744073709551440#64) (k := 176) rfl (by omega)
  have hk : ∀ a : Word, (a.toNat < (env.next M).toNat ∨ top.toNat - 176 ≤ a.toNat) →
      (a.toNat < top.toNat - 144 ∨ top.toNat - 120 ≤ a.toNat) → M'.getMem a = M.getMem a := fun a h1 h2 =>
    hkeep a (by rw [e176]; exact h1) fun ho => by have := hout a ho; omega
  refine ⟨⟨slots_keep (by omega) (fun a h1 _ => hk a (.inr (by omega)) (.inr (by omega))) hsl,
    hF0.trans hF (by rw [e176]; omega) fun b hb => Or.inl (by have := hout b hb; omega), hSt, hc.trans hc0⟩,
    hF.1, hk⟩

/-- **The term's seven stores**: the clone's three words and the coefficient's two at `A = T + 40 t`, after two
    stores into the frame at `top - 120` and `top - 112`: `MemOk`, `NEXT`, the slots at `top - 168` and `top - 160`,
    `DoneT` kept, `t + 1` terms. -/
theorem term_mem {env : Env} {m M : MachineState} {top ret A T D u1 u2 e0 e1 : Word} {regs : Reg → Word}
    {n j t FL H : Nat} (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hge : 0x10000000 ≤ (env.next m).toNat)
    (hM : MemOk env m top ret regs Tactic.F M)
    (hV : VecT env M (top + 18446744073709551472#64) 8) (hA : A.toNat = T.toNat + 40 * t) (ht : t < FL)
    (hTm : (env.next m).toNat ≤ T.toNat) (hHT : H ≤ T.toNat) (hT2 : T.toNat + 40 * FL ≤ (env.next M).toNat)
    (hT8 : T.toNat % 8 = 0) (hterms : TermsT env M T t) (hdone : DoneT env M D n j H)
    (hD : D.toNat + 24 * n ≤ H) (hj : j ≤ n) :
    let M7 := (((((((M.setMem (top + 18446744073709551496#64) u1).setMem (top + 18446744073709551504#64) u2).setMem A
      (M.getMem (top + 18446744073709551472#64))).setMem (A + 8#64) (M.getMem (top + 18446744073709551480#64))).setMem
      (A + 16#64) (M.getMem (top + 18446744073709551488#64))).setMem (A + 24#64) e0).setMem (A + 32#64) e1)
    MemOk env m top ret regs Tactic.F M7 ∧ env.next M7 = env.next M ∧
      M7.getMem (top + 18446744073709551448#64) = M.getMem (top + 18446744073709551448#64) ∧
      M7.getMem (top + 18446744073709551456#64) = M.getMem (top + 18446744073709551456#64) ∧
      TermsT env M7 T (t + 1) ∧ DoneT env M7 D n j H := by
  intro M7
  have hlay := env.layout
  have hnM := hM.2.1.2.1
  have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 176 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => es hc (by omega)
  have e120 := e 18446744073709551496#64 120 rfl (by omega)
  have e112 := e 18446744073709551504#64 112 rfl (by omega)
  have e144 := e 18446744073709551472#64 144 rfl (by omega)
  have e136 := e 18446744073709551480#64 136 rfl (by omega)
  have e128 := e 18446744073709551488#64 128 rfl (by omega)
  have e168 := e 18446744073709551448#64 168 rfl (by omega)
  have e160 := e 18446744073709551456#64 160 rfl (by omega)
  have hs144 : (top + 18446744073709551472#64 + 8#64) = top + 18446744073709551480#64 := by
    rw [BitVec.add_assoc]; rfl
  have hs128 : (top + 18446744073709551472#64 + 16#64) = top + 18446744073709551488#64 := by
    rw [BitVec.add_assoc]; rfl
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  have e24 : (A + 24#64).toNat = A.toNat + 24 := toNat_add_ofNat (by omega)
  have e32 : (A + 32#64).toNat = A.toNat + 32 := toNat_add_ofNat (by omega)
  obtain ⟨m1, n1, k1⟩ := frame_store (a := top + 18446744073709551496#64) (v := u1) hlim hM (by omega) (by omega)
  obtain ⟨m2, n2, k2⟩ := frame_store (a := top + 18446744073709551504#64) (v := u2) hlim m1 (by omega) (by omega)
  obtain ⟨m3, n3, k3⟩ := heap_store (a := A) (v := M.getMem (top + 18446744073709551472#64)) hlim m2 (by omega)
    (by rw [n2, n1]; omega)
  obtain ⟨m4, n4, k4⟩ := heap_store (a := A + 8#64) (v := M.getMem (top + 18446744073709551480#64)) hlim m3
    (by omega) (by rw [n3, n2, n1]; omega)
  obtain ⟨m5, n5, k5⟩ := heap_store (a := A + 16#64) (v := M.getMem (top + 18446744073709551488#64)) hlim m4
    (by omega) (by rw [n4, n3, n2, n1]; omega)
  obtain ⟨m6, n6, k6⟩ := heap_store (a := A + 24#64) (v := e0) hlim m5 (by omega) (by rw [n5, n4, n3, n2, n1]; omega)
  obtain ⟨m7, n7, k7⟩ := heap_store (a := A + 32#64) (v := e1) hlim m6 (by omega)
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
    DoneT.keep hdone (by omega) hj (by rw [hN]) fun b hb => hk b (by omega) (by omega) (by omega)⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | hs
  · have hT := hterms s hs
    refine vecT_keep hT (by rw [hN]) fun b h1 h2 => ?_
    rw [toNat_add_ofNat (by omega)] at h1 h2
    exact hk b (by omega) (by omega) (by omega)
  · have eA : T + BitVec.ofNat 64 (40 * s) = A := BitVec.eq_of_toNat_eq (by rw [toNat_add_ofNat (by omega)]; omega)
    rw [eA]; exact hvA

/-! ## The inner loop: one term cloned -/

/-- The inner loop's head (instruction 130) with `q` terms left of `Form` `j` at `a` in the source, its clone's terms'
    block `T` in the slot at `top - 168`. -/
def IInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : Word) (H j k : Nat) (a T : Word)
    (q : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  JRegs top D regs R ∧ R .x19 = a ∧ (R .x24).toNat = j ∧ (R .x25).toNat = k + 1 ∧ R .x26 = vecLen m a ∧
    (R .x21).toNat = 40 * q ∧ (R .x22).toNat = (vecPtr m a).toNat + 40 * (vecLen m a).toNat ∧
    M.getMem (top + 18446744073709551448#64) = T ∧
    (M.getMem (top + 18446744073709551456#64)).toNat = (regs .x11).toNat + 24 * (regs .x12).toNat ∧
    H ≤ T.toNat ∧ T.toNat + 40 * (vecLen m a).toNat ≤ (env.next M).toNat ∧ T.toNat % 8 = 0 ∧
    Blk env m D (regs .x12).toNat M ∧ DoneT env M D (regs .x12).toNat j H ∧ MemOk env m top ret regs Tactic.F M ∧
    ∃ t, t + q = (vecLen m a).toNat ∧ (R .x27).toNat = (vecPtr m a).toNat + 40 * t ∧
      (R .x20).toNat = T.toNat + 40 * t ∧ TermsT env M T t

/-- The inner loop's registers and memory at its back edge (instruction 174) or head, `t` terms done and `q` left. -/
def TInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : Word) (H j k : Nat) (a T : Word)
    (t q : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  JRegs top D regs R ∧ R .x19 = a ∧ (R .x24).toNat = j ∧ (R .x25).toNat = k + 1 ∧ R .x26 = vecLen m a ∧
    (R .x21).toNat = 40 * q ∧ (R .x22).toNat = (vecPtr m a).toNat + 40 * (vecLen m a).toNat ∧
    M.getMem (top + 18446744073709551448#64) = T ∧
    (M.getMem (top + 18446744073709551456#64)).toNat = (regs .x11).toNat + 24 * (regs .x12).toNat ∧
    H ≤ T.toNat ∧ T.toNat + 40 * (vecLen m a).toNat ≤ (env.next M).toNat ∧ T.toNat % 8 = 0 ∧
    Blk env m D (regs .x12).toNat M ∧ DoneT env M D (regs .x12).toNat j H ∧ MemOk env m top ret regs Tactic.F M ∧
    t + q = (vecLen m a).toNat ∧ (R .x27).toNat = (vecPtr m a).toNat + 40 * t ∧
    (R .x20).toNat = T.toNat + 40 * t ∧ TermsT env M T t

set_option rv_sym.heap true in
/-- **The inner loop's back edge** (instruction 174, `x23` the next term): the head again (130), or the join once
    the last term is done. -/
theorem back {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {D a T : Word} {H j k t q : Nat}
    (ha : a.toNat = (regs .x11).toNat + 24 * j) (hjk : j + k + 1 = (regs .x12).toNat)
    (hDH : D.toNat + 24 * (regs .x12).toNat ≤ H) (hFL40 : (vecLen m a).toNat * 40 < 2 ^ 63)
    (h78 : 0 < k → ∀ R M, OInv env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩)
    (h130 : ∀ R M, IInv env m top ret regs D H j k a T q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, R .x23 = R .x27 → TInv env m top ret regs D H j k a T t q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 174, ret, top⟩ :: rest, R, M⟩ := by
  intro R M h23 hI
  have hJ := join hp hL hk hA h78 (H := H) (j := j)
  obtain ⟨hR, h19, h24, h25, h26, h21, h22, sT, s23, hHT, hT2, hT8, hB, hdone, hM, htq, h27, h20, hterms⟩ := hI
  obtain ⟨hstk, hW, h16, -⟩ := hA
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hR' := And.intro hR h23
  rv_introT hR'
  rv_symT hp stop [130, 176] with [hL]
  · -- more terms: `x27 ≠ x22`
    have hq0 : q ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h27, h22]; omega))
    clear hc
    exact h130 _ _ ⟨⟨rfl, rfl, rfl, rfl⟩, h19, h24, h25, h26, h21, h22, sT, s23, hHT, hT2, hT8, hB, hdone, hM, t,
      htq, h27, h20, hterms⟩
  · have hq0 : q = 0 := by have := congrArg BitVec.toNat hc; rw [h27, h22] at this; omega
    clear hc
    have hfl : t = (vecLen m a).toNat := by omega
    rv_symT hp stop [194] with [hL]
    refine hJ _ _ ⟨rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ hjk ?_ ?_ (.inr ⟨?_, ?_, ?_, ?_, ?_⟩) hB hDH (by omega) hdone hM
    · simp only [Tactic.rf]; rw [h19]; exact ha
    · simpa only [Tactic.rf] using h24
    · simpa only [Tactic.rf] using h25
    · simpa only [Tactic.rf] using s23
    · simp only [Tactic.rf]; rw [h26]; exact hFL40
    · simp only [Tactic.rf]
    · simp only [Tactic.rf]; rw [sT]; exact hHT
    · simp only [Tactic.rf]; rw [sT, h26]; exact hT2
    · simp only [Tactic.rf]; rw [sT]; exact hT8
    · simp only [Tactic.rf]; rw [sT, h26, ← hfl]; exact hterms

set_option rv_sym.heap true in
/-- **After the monomial's clone** (instruction 144): the term stored at `T + 40 t`, then the next term (130) or
    the join. -/
theorem after {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {D a T : Word} {H j k t q : Nat}
    (ha : a.toNat = (regs .x11).toNat + 24 * j) (hjk : j + k + 1 = (regs .x12).toNat)
    (hDH : D.toNat + 24 * (regs .x12).toNat ≤ H) (hFL40 : (vecLen m a).toNat * 40 < 2 ^ 63)
    (hP1 : 0x10000000 ≤ (vecPtr m a).toNat)
    (hP2 : (vecPtr m a).toNat + 40 * (vecLen m a).toNat ≤ (env.next m).toNat)
    (hP8 : (vecPtr m a).toNat % 8 = 0)
    (h78 : 0 < k → ∀ R M, OInv env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩)
    (h130 : ∀ R M, IInv env m top ret regs D H j k a T (q - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, (JRegs top D regs R ∧ R .x23 = R .x27 + 40#64) → R .x19 = a → (R .x24).toNat = j →
      (R .x25).toNat = k + 1 → R .x26 = vecLen m a → (R .x21).toNat = 40 * q →
      (R .x22).toNat = (vecPtr m a).toNat + 40 * (vecLen m a).toNat → (R .x27).toNat = (vecPtr m a).toNat + 40 * t →
      (R .x20).toNat = T.toNat + 40 * t → t + q = (vecLen m a).toNat → 0 < q →
      M.getMem (top + 18446744073709551448#64) = T →
      (M.getMem (top + 18446744073709551456#64)).toNat = (regs .x11).toNat + 24 * (regs .x12).toNat →
      H ≤ T.toNat → T.toNat + 40 * (vecLen m a).toNat ≤ (env.next M).toNat → T.toNat % 8 = 0 →
      Blk env m D (regs .x12).toNat M → DoneT env M D (regs .x12).toNat j H → MemOk env m top ret regs Tactic.F M →
      TermsT env M T t → VecT env M (top + 18446744073709551472#64) 8 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 144, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR h19 h24 h25 h26 h21 h22 h27 h20 htq hq sT s23 hHT hT2 hT8 hB hdone hM hterms hV
  have hlay := env.layout
  have hJ := join hp hL hk hA h78 (H := H) (j := j)
  obtain ⟨hstk, hW, h16, -, -, -, -, -⟩ := id hA
  obtain ⟨b1, b2, b3⟩ := id hB
  have hge := hW.next_ge
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hW1 := hW.heapEnd_le
  have hcM : M.code = m.code := hM.2.2.2
  have hTm : (env.next m).toNat ≤ T.toNat := by omega
  obtain ⟨m7, n7, sT7, s237, ht7, hd7⟩ := term_mem (A := R .x20) (u1 := M.getMem (R .x27 + 24#64))
    (u2 := M.getMem (R .x27 + 32#64)) (e0 := M.getMem (R .x27 + 24#64)) (e1 := M.getMem (R .x27 + 32#64)) hstk hge hM
    hV h20 (by omega : t < (vecLen m a).toNat) hTm hHT hT2 hT8 hterms hdone hDH (by omega)
  have w24 : (R .x27 + 24#64).toNat = (R .x27).toNat + 24 := toNat_add_ofNat (by omega)
  have w32 : (R .x27 + 32#64).toNat = (R .x27).toNat + 32 := toNat_add_ofNat (by omega)
  have v8 : (R .x20 + 8#64).toNat = (R .x20).toNat + 8 := toNat_add_ofNat (by omega)
  have v16 : (R .x20 + 16#64).toNat = (R .x20).toNat + 16 := toNat_add_ofNat (by omega)
  have v24 : (R .x20 + 24#64).toNat = (R .x20).toNat + 24 := toNat_add_ofNat (by omega)
  have v32 : (R .x20 + 32#64).toNat = (R .x20).toNat + 32 := toNat_add_ofNat (by omega)
  have e20 : (R .x20 + 40#64).toNat = T.toNat + 40 * (t + 1) := by rw [toNat_add_ofNat (by omega)]; omega
  have e27 : (R .x27 + 40#64).toNat = (vecPtr m a).toNat + 40 * (t + 1) := by rw [toNat_add_ofNat (by omega)]; omega
  have e21 : (R .x21 + 18446744073709551576#64).toNat = 40 * (q - 1) := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hback := back hp hL hk hA (t := t + 1) (q := q - 1) ha hjk hDH hFL40 h78 h130
  clear hA hV hdone hterms
  rv_introT hR
  rv_symT hp stop [174] with [hL]
  exact hback _ _ rfl ⟨⟨rfl, rfl, rfl, rfl⟩, h19, h24, h25, h26, e21, h22, sT7.trans sT, by rw [s237]; exact s23, hHT,
    by rw [n7]; exact hT2, hT8, ⟨b1, by rw [n7]; exact b2, b3⟩, hd7, m7, by omega, e27, e20, ht7⟩

set_option rv_sym.heap true in
/-- **The inner loop**, from its head to the join. -/
theorem inner {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hnC : 176 + needC ≤ need) (hcl : CloneSpecT env 8 p L.clone.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) {D a T : Word} {H j k : Nat}
    (ha : a.toNat = (regs .x11).toNat + 24 * j) (hjk : j + k + 1 = (regs .x12).toNat) (hFa : FormT env m a)
    (hDH : D.toNat + 24 * (regs .x12).toNat ≤ H)
    (h78 : 0 < k → ∀ R M, OInv env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩) :
    ∀ q R M, IInv env m top ret regs D H j k a T q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (IInv env m top ret regs D H j k a T) fun q R M hI ih => ?_
  have hlay := env.layout
  have hJ := join hp hL hk hA h78 (H := H) (j := j)
  have hFL40 : (vecLen m a).toNat * 40 < 2 ^ 63 := by
    have := (vecT_buf hFa.1).2; have := Nat.mul_le_mul_right 40 this.1; omega
  obtain ⟨hstk, hW, h16, -, -, -, -, -⟩ := id hA
  obtain ⟨hR, h19, h24, h25, h26, h21, h22, sT, s23, hHT, hT2, hT8, hB, hdone, hM, t, htq, h27, h20, hterms⟩ := id hI
  clear hI
  have := hW.nextAddr_ge
  rcases Nat.eq_zero_or_pos q with hq | hq
  · -- no term left: to the join
    clear hA hFa
    have hx : R .x21 = 0#64 := BitVec.eq_of_toNat_eq (by rw [h21, hq]; rfl)
    have hfl : t = (vecLen m a).toNat := by omega
    have hR' := And.intro hR hx
    rv_introT hR'
    rv_symT hp stop [194] with [hL]
    refine hJ _ _ ⟨rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ hjk ?_ ?_ (.inr ⟨?_, ?_, ?_, ?_, ?_⟩) hB hDH (by omega) hdone hM
    · simp only [Tactic.rf]; rw [h19]; exact ha
    · simpa only [Tactic.rf] using h24
    · simpa only [Tactic.rf] using h25
    · simpa only [Tactic.rf] using s23
    · simp only [Tactic.rf]; rw [h26]; exact hFL40
    · simp only [Tactic.rf]
    · simp only [Tactic.rf]; rw [sT]; exact hHT
    · simp only [Tactic.rf]; rw [sT, h26]; exact hT2
    · simp only [Tactic.rf]; rw [sT]; exact hT8
    · simp only [Tactic.rf]; rw [sT, h26, ← hfl]; exact hterms
  · have hFL : 0 < (vecLen m a).toNat := by omega
    obtain ⟨hP1, hP2, hP8⟩ := hFa.foot.resolve_left (by omega)
    have hafter := after hp hL hk hA (T := T) (t := t) (q := q) ha hjk hDH hFL40 hP1 hP2 hP8 h78
      (fun R' M' h => ih (q - 1) R' M' (by omega) h)
    have hx27 : R .x27 = vecPtr m a + BitVec.ofNat 64 (40 * t) :=
      BitVec.eq_of_toNat_eq (by rw [h27, toNat_add_ofNat (by omega)])
    have hnm := hM.2.1.1
    have hnM := hM.2.1.2.1
    have hW1 := hW.heapEnd_le
    have hSt : env.Static M := hM.2.2.1
    have hcM : M.code = m.code := hM.2.2.2
    have w8 : (R .x27 + 8#64).toNat = (R .x27).toNat + 8 := toNat_add_ofNat (by omega)
    have w16 : (R .x27 + 16#64).toNat = (R .x27).toNat + 16 := toNat_add_ofNat (by omega)
    have ag : ∀ b : Word, b.toNat < (env.next m).toNat → M.getMem b = m.getMem b := fun b hb =>
      hM.2.1.getMem_below_next (by omega) hb id
    have hBt : BufT env M (M.getMem (R .x27 + 16#64)) (M.getMem (R .x27 + 8#64)) 8 := by
      have hv := (vecT_buf (hFa.2 t (by omega))).1
      rw [← hx27, vecLen_eq, vecPtr_eq] at hv
      rw [ag _ (by omega), ag _ (by omega)]
      exact hv.mono hnm
    obtain ⟨b1, b2, b3⟩ := hB
    clear hA hFa ag
    rv_introT hR
    rv_symT hp stop [144, 194] with [hL] using [hcl]
    · exact absurd (congrArg BitVec.toNat hc) (by rw [h21]; simp only [BitVec.toNat_ofNat]; omega)
    · -- after the clone
      have e144 := es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
      have e168 := es (top := top) (c := 18446744073709551448#64) (k := 168) rfl (by omega)
      have e160 := es (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
      obtain ⟨hM1, hn1, hk1⟩ := call_keep hstk hM hret1_14 hret1_15 hret1_24 (fun b hb => by
        obtain ⟨h1, h2⟩ := hb
        change (top + 18446744073709551472#64).toNat ≤ b.toNat at h1
        change b.toNat < (top + 18446744073709551472#64).toNat + 24 at h2
        omega) keep1_2
      refine hafter _ _ ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ h19 h24 h25 h26 h21 h22 h27 h20 htq hq ?_ ?_ hHT (by omega) hT8
        ⟨b1, by omega, b3⟩ ?_ hM1 ?_ ?_
      · rw [hk1 _ (.inr (by omega)) (.inl (by omega))]; exact sT
      · rw [hk1 _ (.inr (by omega)) (.inl (by omega))]; exact s23
      · exact DoneT.keep hdone (by omega) (by omega) hn1 fun b hb => hk1 b (.inl (by omega)) (.inl (by omega))
      · exact TermsT.keep hterms (by omega) hn1 fun b h1 h2 => hk1 b (.inl (by omega)) (.inl (by omega))
      · exact ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩

/-! ## The outer loop: one `Form` cloned -/

set_option rv_sym.heap true in
/-- **The outer loop**, from its head to the return. -/
theorem outer {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needC needH : Nat} (hnA : 176 + needA ≤ need) (hnC : 176 + needC ≤ need)
    (hnH : 176 + needH ≤ need)
    (hal : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hcl : CloneSpecT env 8 p L.clone.idx needC) (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) {D : Word} :
    ∀ k R M, OInv env m top ret regs D k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env m top ret regs D) fun k R M hI ih => ?_
  have hlay := env.layout
  have h78 : 0 < k → ∀ R M, OInv env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := fun hk0 R' M' h => ih (k - 1) R' M'
    (by omega) h
  obtain ⟨hR, h23, j, hjk, h19, h24, h25, hB, hdone, hM⟩ := hI
  obtain ⟨hstk, hW, h16, -, -, -, hsrc, hforms⟩ := id hA
  have hsrc' : (regs .x11).toNat + 24 * (regs .x12).toNat ≤ (env.next m).toNat := by
    rcases hsrc with h | ⟨-, h2, -⟩
    · omega
    · unfold Env.Live at h2; omega
  have ha : R .x19 = regs .x11 + BitVec.ofNat 64 (24 * j) :=
    BitVec.eq_of_toNat_eq (by rw [h19, toNat_add_ofNat (by omega)])
  have hFa : FormT env m (R .x19) := ha ▸ hforms j (by omega)
  have hFL40 : (vecLen m (R .x19)).toNat * 40 < 2 ^ 63 := by
    have := (vecT_buf hFa.1).2; have := Nat.mul_le_mul_right 40 this.1; omega
  have hlt := vecT_lt hFa.1
  have hnm := hM.2.1.1
  have hnM := hM.2.1.2.1
  have hW1 := hW.heapEnd_le
  have := hW.nextAddr_ge
  have hSt : env.Static M := hM.2.2.1
  have hcM : M.code = m.code := hM.2.2.2
  have ag8 : M.getMem (R .x19 + 8#64) = vecPtr m (R .x19) :=
    hM.2.1.getMem_below_next (by omega) (by rw [toNat_add_ofNat (by omega)]; omega) id
  have ag16 : M.getMem (R .x19 + 16#64) = vecLen m (R .x19) :=
    hM.2.1.getMem_below_next (by omega) (by rw [toNat_add_ofNat (by omega)]; omega) id
  have w8 : (R .x19 + 8#64).toNat = (R .x19).toNat + 8 := toNat_add_ofNat (by omega)
  have w16 : (R .x19 + 16#64).toNat = (R .x19).toNat + 16 := toNat_add_ofNat (by omega)
  clear hsrc hforms
  have hJ := join hp hL hk hA h78 (H := (env.next M).toNat) (j := j)
  have hin := fun T => inner hp hL hnC hcl hk hstop hneed hA (a := R .x19) (T := T) (H := (env.next M).toNat) h19 hjk
    hFa (by have := hB.2.1; omega) h78
  obtain ⟨b1, b2, b3⟩ := id hB
  have hFLn : (M.getMem (R .x19 + 16#64)).toNat * 40 < 2 ^ 63 := by rw [ag16]; exact hFL40
  have s40 : (M.getMem (R .x19 + 16#64) <<< 5 + M.getMem (R .x19 + 16#64) <<< 3).toNat =
      40 * (M.getMem (R .x19 + 16#64)).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega
  have sh : M.getMem (R .x19 + 16#64) <<< 3 >>> 3 = M.getMem (R .x19 + 16#64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have e176 := es (top := top) (c := 18446744073709551440#64) (k := 176) rfl (by omega)
  rv_introT hR
  rv_symT hp stop [130, 194, 218] with [hL] using [hal, hhe]
  · -- `x19 = x23`: not reached, `j < n`
    exact absurd (congrArg BitVec.toNat hc) (by rw [h19, h23]; omega)
  · -- no terms, no block
    have hF0 : (M.getMem (R .x19 + 16#64)).toNat = 0 := by
      have := congrArg BitVec.toNat hc; rw [s40] at this; simp only [BitVec.toNat_ofNat] at this; omega
    clear hc
    exact hJ _ _ ⟨rfl, rfl, rfl, rfl⟩ h19 h24 h25 hjk h23 hFLn (.inl ⟨rfl, hF0⟩) hB b2 (Nat.le_refl _) hdone hM
  · -- after `alloc`, no terms
    have hF0 : (M.getMem (R .x19 + 16#64)).toNat = 0 := by rw [hc]; rfl
    clear hc
    obtain ⟨hM2, hn2, hk2⟩ := call_keep hstk hM hret2_14 hret2_15 hret2_19 (fun b hb => hb.elim)
      (fun a h _ => keep2_2 a h)
    exact hJ _ _ ⟨rfl, rfl, rfl, rfl⟩ h19 h24 h25 hjk h23 hFLn (.inl ⟨rfl, hF0⟩) ⟨b1, by omega, b3⟩ b2 hn2
      (DoneT.keep hdone (by omega) (by omega) hn2 fun b hb => hk2 b (.inl (by omega)) (.inl (by omega))) hM2
  · -- `min(n, n - 1)` is `n`: not reached
    have hF1 : (M.getMem (R .x19 + 16#64)).toNat ≠ 0 := fun h => hc_5 (BitVec.eq_of_toNat_eq h)
    rw [sh, BitVec.lt_def, BitVec.toNat_add] at hc
    simp only [BitVec.toNat_ofNat] at hc
    omega
  · -- into the inner loop
    have hF1 : (M.getMem (R .x19 + 16#64)).toNat ≠ 0 := fun h => hc_5 (BitVec.eq_of_toNat_eq h)
    clear hc
    obtain ⟨-, hP2, -⟩ := hFa.foot.resolve_left (by rw [← ag16]; exact hF1)
    rw [← ag8, ← ag16] at hP2
    have e1 : (M.getMem (R .x19 + 16#64) + 18446744073709551615#64).toNat = (M.getMem (R .x19 + 16#64)).toNat - 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    have e22 : (M.getMem (R .x19 + 8#64) + ((M.getMem (R .x19 + 16#64) + 18446744073709551615#64) <<< 5 +
        (M.getMem (R .x19 + 16#64) + 18446744073709551615#64) <<< 3) + 40#64).toNat =
        (M.getMem (R .x19 + 8#64)).toNat + 40 * (M.getMem (R .x19 + 16#64)).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq, Nat.shiftLeft_eq, e1]
      simp only [BitVec.toNat_ofNat]
      have : 2 ^ 5 * ((M.getMem (R .x19 + 16#64)).toNat - 1) + 2 ^ 3 * ((M.getMem (R .x19 + 16#64)).toNat - 1) + 40 =
        40 * (M.getMem (R .x19 + 16#64)).toNat := by omega
      omega
    obtain ⟨hM2, hn2, hk2⟩ := call_keep hstk hM hret2_14 hret2_15 hret2_19 (fun b hb => hb.elim)
      (fun a h _ => keep2_2 a h)
    have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
    have e168 := es (top := top) (c := 18446744073709551448#64) (k := 168) rfl (by omega)
    have e160 := es (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
    have e152 := es (top := top) (c := 18446744073709551464#64) (k := 152) rfl (by omega)
    obtain ⟨m3, n3, k3⟩ := frame_store (a := top + 18446744073709551456#64) (v := R .x23) hstk hM2 (by omega)
      (by omega)
    obtain ⟨m4, n4, k4⟩ := frame_store (a := top + 18446744073709551464#64) (v := R .x22) hstk m3 (by omega)
      (by omega)
    obtain ⟨m5, n5, k5⟩ := frame_store (a := top + 18446744073709551448#64) (v := r2 .x10) hstk m4 (by omega)
      (by omega)
    have hN : env.next (((m2.setMem (top + 18446744073709551456#64) (R .x23)).setMem (top + 18446744073709551464#64)
        (R .x22)).setMem (top + 18446744073709551448#64) (r2 .x10)) = env.next m2 := by rw [n5, n4, n3]
    refine hin (r2 .x10) (vecLen m (R .x19)).toNat _ _ ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, h24, h25, ag16,
      by rw [← ag16]; exact s40, by rw [← ag8, ← ag16]; exact e22, MachineState.getMem_setMem_eq, ?_, hret2_16,
      by rw [hN, ← ag16]; rw [s40] at hret2_18; omega, hret2_17, ⟨b1, by rw [hN]; omega, b3⟩, ?_, m5, 0, by omega,
      by simp only [Tactic.rf]; rw [← ag8]; omega, by simp only [Tactic.rf]; omega,
      fun t ht => absurd ht (Nat.not_lt_zero _)⟩
    · rw [k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]; exact h23
    · refine DoneT.keep hdone (by omega) (by omega) (by rw [hN]; exact hn2) fun b hb => ?_
      rw [k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), k3 _ (ne _ _ (by omega))]
      exact hk2 b (.inl (by omega)) (.inl (by omega))

/-! ## The entry -/

/-- The prologue's thirteen saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)).setMem (top + 18446744073709551536#64) (regs .x24)).setMem
    (top + 18446744073709551528#64) (regs .x25)).setMem (top + 18446744073709551520#64) (regs .x26)).setMem
    (top + 18446744073709551512#64) (regs .x27)

/-- The prologue's stores: `MemOk` at the entry's frame. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) : MemOk env m top ret regs Tactic.F (saved m top ret regs) := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 176 → (top + c).toNat = top.toNat - k :=
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

/-- A word of a static data table of `ts` is in a window and aligned. -/
theorem data_ok {env : Env} {top : Word} {m : MachineState} {ts : List (DataRef × List Word)} {d : DataRef}
    {ws : List Word} (hW : Windows env top m) (hd : DataRef.InData env ts) (hm : (d, ws) ∈ ts) (hk : 0 < ws.length) :
    inWindow (d.hi + d.lo) 8 = true ∧ (d.hi + d.lo).toNat % 8 = 0 := by
  simpa using hW.data_ok _ (hd _ hm 0 hk)

set_option rv_sym.heap true in
/-- **`<Vec<Form> as Clone>::clone` is total**, with 176 bytes of stack beyond its callees', given its two bounds'
    words in the static data. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hd : DataRef.InData env [(L.d_c8_d6dfd6bc, d_c8_d6dfd6bc_words), (L.d_c8_51ab739d, d_c8_51ab739d_words)])
    {need needA needC needH : Nat} (hnA : 176 + needA ≤ need) (hnC : 176 + needC ≤ need) (hnH : 176 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcl : CloneSpecT env 8 p L.clone.idx needC)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hw1 := hd.words (List.mem_cons_self ..)
  have hw2 := hd.words (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  rv_autoT hp stop [78, 226] with [hL, hw1, hw2] using [hal', hhe]
  all_goals
    have hlay := env.layout
    rw [hpre_2] at hpre_6
    have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
    have hM0 := saved_ok (ret := ret) (regs := regs) hlim hpre_5 hpre_4
    simp only [saved] at hM0
    have hA : Args env m top regs := ⟨hlim, hpre_13, hpre_12, ⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, hpre_10, hpre_11⟩
    have hW1 := hpre_13.heapEnd_le
    have hsm : (regs .x12).toNat = 0 ∨ (regs .x11).toNat + 24 * (regs .x12).toNat ≤ 0x78000000 := by
      rcases hpre_10 with h | ⟨-, h2, -⟩
      · exact .inl h
      · unfold Env.Live at h2; exact .inr (by omega)
    have hsm' : 24 * (regs .x12).toNat ≤ 0x78000000 := by rcases hsm with h | h <;> omega
    have s24 : (regs .x12 <<< 4 + regs .x12 <<< 3).toNat = 24 * (regs .x12).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      omega
  · exact (data_ok hpre_13 hd (List.mem_cons_self ..) (by decide)).1
  · exact (data_ok hpre_13 hd (List.mem_cons_self ..) (by decide)).2
  · -- no `Form`s: the empty vector
    have hn0 : regs .x12 = 0#64 := BitVec.eq_of_toNat_eq (by
      have := congrArg BitVec.toNat hc; rw [s24] at this; simp only [BitVec.toNat_ofNat] at this ⊢; omega)
    clear hc
    exact exit hp hL hk hA (D := 8#64) _ _ ⟨rfl, rfl, rfl, by simp only [Tactic.rf]; exact hn0.symm, rfl⟩ hM0
      (.inl (by rw [hn0]; rfl))
  · rw [s24]; omega
  · -- `n = 0` after `alloc`: not reached, the empty vector all the same
    obtain ⟨hM1, -, -⟩ := call_keep hlim hM0 hret1_14 hret1_15 hret1_19 (fun b hb => hb.elim)
      (fun a h _ => keep1_2 a h)
    exact exit hp hL hk hA (D := r1 .x10) _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hM1 (.inl (by rw [hc]; rfl))
  · exact (data_ok hpre_13 hd (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by decide)).1
  · exact (data_ok hpre_13 hd (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by decide)).2
  · -- into the outer loop
    have hn0 : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    clear hc
    replace hsm := hsm.resolve_left hn0
    obtain ⟨hM1, hn1, -⟩ := call_keep hlim hM0 hret1_14 hret1_15 hret1_19 (fun b hb => hb.elim)
      (fun a h _ => keep1_2 a h)
    have hnm := hM0.2.1.1
    rw [s24] at hret1_18
    exact outer hp hL hnA hnC hnH hal' hcl hhe hk hstop hpre_3 hA ((regs .x12).toNat - 1) _ _
      ⟨⟨rfl, rfl, rfl, rfl⟩, by simp only [Tactic.rf]; rw [BitVec.toNat_add, s24]; omega, 0, by omega,
        by simp only [Tactic.rf]; omega, rfl, by simp only [Tactic.rf]; omega,
        ⟨by simp only [Tactic.rf]; omega, by simp only [Tactic.rf]; omega, hret1_17⟩,
        fun _ h => absurd h (Nat.not_lt_zero _), hM1⟩

end Rv64mc.Proof.Layout.CloneFormsT

/-- info: 'Rv64mc.Proof.Layout.CloneFormsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.CloneFormsT.total
