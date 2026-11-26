/-
  Rv64mc.Proof.Bytecode.CountingSortUsizeT

  `counting_sort::<usize, block_members::{closure#0}>(items, keys, key)` is total: called with the result's slot
  (`a0`), the items (`a1`, `a2`), `keys` (`a3`) and the closure's members (`a4`, `a5`, 32-byte elements whose length
  word at `+ 24` is the key), it returns a vector of the items' length (`CloneT.ClonePostT`: `VecT`, its buffer fresh
  unless empty), or the run ends with the guest's abort (`AbortStop`) where `try_allocate_in`, `alloc`, a bounds
  check or `handle_error` does. A safety-only contract: the partial `CountingSortUsize.spec` (the sorted items, a
  partial proof in progress) is not combined with it.

  Every item, key and count is checked against a bound by the code before it indexes (`members[item]`,
  `starts[key + 1]`, `starts[key]`, `sorted[starts[key]]`), so no access depends on what the `starts` block holds:
  the precondition asks the two slices in windows (`BufT`, a block allocated before), `keys` at least `1` (the
  compiled prefix-sum loop runs once before its test) and below `2 ^ 59`, and the result's slot a caller's, in a
  window and aligned.

  The body is cut at the three loops' heads (instructions 66, 102, 142), at 114 (after the prefix sums) and at the
  return (190); every part keeps `Common` (the arguments' registers, the `starts` block fresh, the slots, the frame).

  ## Main definitions

  * `PreT`, `SpecT`, `Slots`, `Common`, `LInv1`, `LInv2`, `LInv3`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.TryAllocateInT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.CloneT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Gen.Tmpl.Verifier.Bytecode.CountingSortUsizeBlockMembersClosure0

namespace Rv64mc.Proof.Bytecode.CountingSortUsizeT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.TryAllocateInT (TryAllocSpecT)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT)
open Rv64mc.Gen.Verifier.Bytecode.CountingSortUsizeBlockMembersClosure0 (Link tmpl)

/-- The total precondition: the result's slot a caller's, in a window and 8-byte aligned; the items (`a1`, `a2`) and
    the members (`a4`, `a5`, 32-byte elements) slices of blocks allocated before (`BufT`, for their lengths); `keys`
    (`a3`) at least `1` and below `2 ^ 59`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (regs .x12) (regs .x11) 8 ∧ 1 ≤ (regs .x13).toNat ∧ (regs .x13).toNat < 2 ^ 59 ∧
    BufT env m (regs .x15) (regs .x14) 32

/-- **The total contract of this `counting_sort`**: the result a vector's of the items' length, its buffer fresh
    unless empty. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (ClonePostT env 8) SretVecOut AbortStop

/-- The prologue's eleven saved words in `M`, at `top - 8` down to `top - 88`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25

/-- What every part keeps: the arguments in the saved registers, the `starts` block `S` of `keys + 1` words fresh
    since the entry, the slots, the frame. -/
def Common (env : Env) (m : MachineState) (top ret S : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x15 ∧ R .x9 = regs .x13 + 1#64 ∧ R .x18 = regs .x12 ∧
    R .x19 = regs .x14 ∧ R .x20 = regs .x13 ∧ R .x23 = regs .x10 ∧ R .x25 = S ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27 ∧
    (env.next m).toNat ≤ S.toNat ∧ S.toNat + 8 * ((regs .x13).toNat + 1) ≤ (env.next M).toNat ∧ S.toNat % 8 = 0 ∧
    Slots M top ret regs ∧ env.Frame top (SretVecOut regs m) m M ∧ env.Static M ∧ M.code = m.code

/-- The counting loop's head (instruction 66) with `k + 1` items left: `x12` at item `j`, `x11` the bytes left. -/
def LInv1 (env : Env) (m : MachineState) (top ret S : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Common env m top ret S regs R M ∧ R .x21 = regs .x11 ∧ R .x22 = regs .x12 <<< 3 ∧ R .x24 = regs .x24 ∧
    ∃ j, j + k + 1 = (regs .x12).toNat ∧ (R .x12).toNat = (regs .x11).toNat + 8 * j ∧ (R .x11).toNat = 8 * (k + 1)

/-- The facts of the precondition the loops read: the items and members slices in the heap, `keys`' bounds. -/
def Args (env : Env) (m : MachineState) (regs : Reg → Word) : Prop :=
  BufT env m (regs .x12) (regs .x11) 8 ∧ 1 ≤ (regs .x13).toNat ∧ (regs .x13).toNat < 2 ^ 59 ∧
    BufT env m (regs .x15) (regs .x14) 32

/-- Member `X` of a slice of 32-byte elements below its length: its length word in a window, aligned. -/
theorem member_ok {env : Env} {m : MachineState} {len P X : Word} (hB : BufT env m len P 32)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hend : env.heapEnd.toNat ≤ 0x78000000) (hX : X < len) :
    inWindow (P + X <<< 5 + 24#64) 8 = true ∧ (P + X <<< 5 + 24#64).toNat % 8 = 0 := by
  have hX' := BitVec.lt_def.1 hX
  rcases hB with h0 | ⟨h1, h2, h3⟩
  · omega
  unfold Env.Live at h2
  have hs : (X <<< 5).toNat = 32 * X.toNat := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e : (P + X <<< 5 + 24#64).toNat = P.toNat + 32 * X.toNat + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hs]; simp only [BitVec.toNat_ofNat]; omega
  rw [inWindow_iff, e]
  omega

/-- Word `K` of a block `P` of `c` words below `NEXT`, `K` below `c`: in a window, aligned, at `P + 8 K`. -/
theorem word_ok {env : Env} {M : MachineState} {P K : Word} {c : Nat} (hP1 : 0x10000000 ≤ P.toNat)
    (hP2 : P.toNat + 8 * c ≤ (env.next M).toNat) (hP8 : P.toNat % 8 = 0)
    (hnx : (env.next M).toNat ≤ env.heapEnd.toNat) (hend : env.heapEnd.toNat ≤ 0x78000000) (hK : K.toNat < c) :
    inWindow (P + K <<< 3) 8 = true ∧ (P + K <<< 3).toNat % 8 = 0 ∧ (P + K <<< 3).toNat = P.toNat + 8 * K.toNat := by
  have hs : (K <<< 3).toNat = 8 * K.toNat := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e : (P + K <<< 3).toNat = P.toNat + 8 * K.toNat := by rw [BitVec.toNat_add, hs]; omega
  rw [inWindow_iff, e]
  omega

/-- Word `K` of the `starts` block `S` of `keys + 1` words, `K` at most `keys`: in a window, aligned. -/
theorem start_ok {env : Env} {M : MachineState} {S K keys : Word} (hS1 : 0x10000000 ≤ S.toNat)
    (hS2 : S.toNat + 8 * (keys.toNat + 1) ≤ (env.next M).toNat) (hS8 : S.toNat % 8 = 0)
    (hnx : (env.next M).toNat ≤ env.heapEnd.toNat) (hend : env.heapEnd.toNat ≤ 0x78000000) (hK : K.toNat ≤ keys.toNat) :
    inWindow (S + K <<< 3) 8 = true ∧ (S + K <<< 3).toNat % 8 = 0 ∧ (S + K <<< 3).toNat = S.toNat + 8 * K.toNat := by
  have hs : (K <<< 3).toNat = 8 * K.toNat := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e : (S + K <<< 3).toNat = S.toNat + 8 * K.toNat := by rw [BitVec.toNat_add, hs]; omega
  rw [inWindow_iff, e]
  omega

/-- `lens + 1` below `keys + 1`, as numbers. -/
theorem succ_toNat {a b : Word} (h : a < b) : (a + 1#64).toNat = a.toNat + 1 :=
  toNat_add_ofNat (by have := BitVec.lt_def.1 h; have := b.isLt; omega)

/-- One store into a block allocated since the entry keeps what every part states of memory. -/
theorem store_ok {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hF : env.Frame top out m M) (hS : env.Static M)
    (hc : M.code = m.code) (hsl : Slots M top ret regs) (ha1 : (env.next m).toNat ≤ a.toNat)
    (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    Slots (M.setMem a v) top ret regs ∧ env.Frame top out m (M.setMem a v) ∧ env.Static (M.setMem a v) ∧
      (M.setMem a v).code = m.code ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hnM := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  have e : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 112 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 112 → (M.setMem a v).getMem (top + c) = M.getMem (top + c) :=
    fun c k hc hk => MachineState.getMem_setMem_ne fun h => by
      have := congrArg BitVec.toNat h; rw [e c k hc hk] at this; omega
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hsl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Tactic.frame_fresh hF rfl ha1 (by omega),
    Tactic.static_store hS (.inl (by omega)), by rw [MachineState.code_setMem, hc], Tactic.next_setMem hne⟩
  · rw [g _ 8 rfl (by omega)]; exact s1
  · rw [g _ 16 rfl (by omega)]; exact s2
  · rw [g _ 24 rfl (by omega)]; exact s3
  · rw [g _ 32 rfl (by omega)]; exact s4
  · rw [g _ 40 rfl (by omega)]; exact s5
  · rw [g _ 48 rfl (by omega)]; exact s6
  · rw [g _ 56 rfl (by omega)]; exact s7
  · rw [g _ 64 rfl (by omega)]; exact s8
  · rw [g _ 72 rfl (by omega)]; exact s9
  · rw [g _ 80 rfl (by omega)]; exact s10
  · rw [g _ 88 rfl (by omega)]; exact s11

/-- The prefix sums' head (instruction 102) with `k + 1` words left: `x10` at word `j + 1` of `starts`, `x11` past its
    end. -/
def LInv2 (env : Env) (m : MachineState) (top ret S : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Common env m top ret S regs R M ∧ R .x21 = regs .x11 ∧ R .x22 = regs .x12 <<< 3 ∧ R .x24 = regs .x24 ∧
    R .x11 = S + 8#64 + regs .x13 <<< 3 ∧
    ∃ j, j + k + 1 = (regs .x13).toNat ∧ (R .x10).toNat = S.toNat + 8 + 8 * j

theorem rvCapAt_eq (a : Word) : rvCapAt a = a := by
  simp only [rvCapAt, Layouts.RawVecInner.cap]; exact BitVec.add_zero a

theorem vecCap_eq (m : MachineState) (a : Word) : vecCap m a = m.getMem a := by
  simp only [vecCap, Layouts.Vec.cap]; exact congrArg _ (BitVec.add_zero a)

/-- **The result from its header's words**: capacity and length `n`, the buffer `P` of `n` words fresh since `m`
    unless `n = 0`. -/
theorem post_ok {env : Env} {regs : Reg → Word} {m M : MachineState} {P : Word}
    (hwin : InWin env (regs .x10) 24) (hal : (regs .x10).toNat % 8 = 0)
    (h0 : M.getMem (regs .x10) = regs .x12) (h8 : M.getMem (regs .x10 + 8#64) = P)
    (h16 : M.getMem (regs .x10 + 16#64) = regs .x12)
    (hP : (regs .x12).toNat = 0 ∨ (0x10000000 ≤ P.toNat ∧ (env.next m).toNat ≤ P.toNat ∧
      P.toNat + (regs .x12).toNat * 8 ≤ (env.next M).toNat ∧ P.toNat % 8 = 0))
    (hn : (regs .x12).toNat * 8 < 2 ^ 63) {r : Reg → Word} : ClonePostT env 8 regs m r M := by
  have hc : rvCapAt (regs .x10) = regs .x10 := rvCapAt_eq _
  have hp : rvPtrAt (regs .x10) = regs .x10 + 8#64 := rfl
  refine ⟨⟨hwin, ⟨Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega), hal,
    ?_, by rw [hc, h0]; exact hn⟩, by rw [show vecLen M (regs .x10) = M.getMem (regs .x10 + 16#64) from rfl, vecCap_eq, h0, h16]⟩,
    by rw [show vecLen M (regs .x10) = M.getMem (regs .x10 + 16#64) from rfl, h16], ?_⟩
  · rw [hc, hp, h0, h8]
    rcases hP with h | ⟨h1, -, h3, h4⟩
    · exact .inl h
    · exact .inr ⟨h1, by unfold Env.Live; omega, h4⟩
  · rw [show vecPtr M (regs .x10) = M.getMem (regs .x10 + 8#64) from rfl, h8]
    rcases hP with h | ⟨-, h2, h3, -⟩
    · exact .inl h
    · exact .inr ⟨h2, by omega⟩

/-- A store into a block allocated since `m` keeps the result's header, a caller's 24 bytes. -/
theorem hdr_keep {env : Env} {m M : MachineState} {top a h : Word} (hown : env.Owned m top h 24)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hnx : (env.next M).toNat ≤ env.heapEnd.toNat)
    (ha1 : (env.next m).toNat ≤ a.toNat) (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    ∀ v, ∀ k : Nat, k ≤ 16 → (M.setMem a v).getMem (h + BitVec.ofNat 64 k) = M.getMem (h + BitVec.ofNat 64 k) := by
  intro v k hk
  have hlay := env.layout
  have e : (h + BitVec.ofNat 64 k).toNat = h.toNat + k := toNat_add_ofNat (by have := hown.2; omega)
  refine MachineState.getMem_setMem_ne fun he => ?_
  have := congrArg BitVec.toNat he
  rcases hown.1 with h1 | h1 <;> omega

/-- `hdr_keep` at the header's first word. -/
theorem hdr_keep0 {env : Env} {m M : MachineState} {top a h : Word} (hown : env.Owned m top h 24)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hnx : (env.next M).toNat ≤ env.heapEnd.toNat)
    (ha1 : (env.next m).toNat ≤ a.toNat) (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    ∀ v, (M.setMem a v).getMem h = M.getMem h := fun v => by
  simpa using hdr_keep hown hlim hnx ha1 ha2 v 0 (by omega)

set_option rv_sym.heap true in
/-- **The return**, from instruction 190, the result's header written. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top S : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 8) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0) :
    ∀ R M, Common env m top ret S regs R M → (∀ r, ClonePostT env 8 regs m r M) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 190, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hPost
  have hlay := env.layout
  rv_introT hI
  rv_symT hp with [_hL]
  exact ⟨⟨rfl, hI_15, hI_16, hI_17, hI_18, hI_19, hI_20, hI_21, hI_22, hI_23, hI_24, rfl, rfl⟩, hI_25, hI_26, hPost _⟩

/-- The placing loop's head (instruction 142) with `k + 1` items left: `x21` at item `j`, `x22` the bytes left; the
    sorted copy `P` of `n` words fresh since the entry, the result's header naming it with length `n`. -/
def LInv3 (env : Env) (m : MachineState) (top ret S P : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Common env m top ret S regs R M ∧ R .x24 = P ∧
    (env.next m).toNat ≤ P.toNat ∧ P.toNat + 8 * (regs .x12).toNat ≤ (env.next M).toNat ∧ P.toNat % 8 = 0 ∧
    M.getMem (regs .x10) = regs .x12 ∧ M.getMem (regs .x10 + 8#64) = P ∧ M.getMem (regs .x10 + 16#64) = regs .x12 ∧
    ∃ j, j + k + 1 = (regs .x12).toNat ∧ (R .x21).toNat = (regs .x11).toNat + 8 * j ∧
      (R .x22).toNat = 8 * (k + 1)

set_option rv_sym.heap true in
/-- **The placing loop**, from its head to the return. -/
theorem loop3 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needP : Nat} (hn : 112 ≤ need) (hnP : 112 + needP ≤ need)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top S P : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 8) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hA : Args env m regs) (hn0 : (regs .x12).toNat ≠ 0)
    (hown : env.Owned m top (regs .x10) 24) (hwin : InWin env (regs .x10) 24)
    (hal : (regs .x10).toNat % 8 = 0) :
    ∀ k R M, LInv3 env m top ret S P regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 142, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv3 env m top ret S P regs) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨hB1, hk1, hk59, hB2⟩ := hA
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hS1, hS2, hS8, hsl, hF, hSt, hcode⟩, -, hP1, hP2, hP8, hh0, hh8, hh16, j, hj,
    hx21, hx22⟩ := id hI
  have hnM := hF.2.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hF.1
  have hS1' : 0x10000000 ≤ S.toNat := by omega
  have hP1' : 0x10000000 ≤ P.toNat := by omega
  have hB1' : 0x10000000 ≤ (regs .x11).toNat ∧ (regs .x11).toNat + 8 * (regs .x12).toNat ≤ (env.next m).toNat ∧
      (regs .x11).toNat % 8 = 0 := by
    rcases hB1 with h | ⟨h1, h2, h3⟩
    · exact absurd h hn0
    · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
  rv_introT hI
  rv_symT hp stop [142, 190] with [hL] using [hpb]
  · exact (member_ok hB2 hnx hW1 hc).1
  · exact (member_ok hB2 hnx hW1 hc).2
  · exact (word_ok (c := (regs .x13).toNat + 1) hS1' hS2 hS8 hnM hW1 (by have := BitVec.le_def.1 hc; omega)).1
  · exact (word_ok (c := (regs .x13).toNat + 1) hS1' hS2 hS8 hnM hW1 (by have := BitVec.le_def.1 hc; omega)).2.1
  · exact (word_ok hP1' hP2 hP8 hnM hW1 (BitVec.lt_def.1 hc)).1
  · exact (word_ok hP1' hP2 hP8 hnM hW1 (BitVec.lt_def.1 hc)).2.1
  all_goals
    have hl := BitVec.le_def.1 hc_2
    have eS := (word_ok (c := (regs .x13).toNat + 1) (K := MachineState.getMem M (regs .x14 +
      MachineState.getMem M (R .x21) <<< 5 + 24#64)) hS1' hS2 hS8 hnM hW1 (by omega)).2.2
  · exact (word_ok (c := (regs .x13).toNat + 1) hS1' hS2 hS8 hnM hW1 (by omega)).1
  · exact (word_ok (c := (regs .x13).toNat + 1) hS1' hS2 hS8 hnM hW1 (by omega)).2.1
  · exact (word_ok (c := (regs .x13).toNat + 1) hS1' hS2 hS8 hnM hW1 (by omega)).1
  · exact (word_ok (c := (regs .x13).toNat + 1) hS1' hS2 hS8 hnM hW1 (by omega)).2.1
  all_goals
    have hx := BitVec.lt_def.1 hc_3
    have eP := (word_ok hP1' hP2 hP8 hnM hW1 hx).2.2
    obtain ⟨m1, m2, m3, m4, m5⟩ := store_ok (v := MachineState.getMem M (R .x21)) (by omega) hF hSt hcode hsl
      (by rw [eP]; omega) (by rw [eP]; omega)
    have k1 := hdr_keep hown (by omega) hnM (by rw [eP]; omega) (by rw [eP]; omega)
    have nS := fun v => store_ok (v := v) (by omega) m2 m3 m4 m1 (by rw [eS]; omega) (by rw [eS, m5]; omega)
    have k2 := hdr_keep hown (by omega) (by rw [m5]; exact hnM) (by rw [eS]; omega) (by rw [eS, m5]; omega)
    have k10 := hdr_keep0 hown (by omega) hnM (by rw [eP]; omega) (by rw [eP]; omega)
    have k20 := hdr_keep0 hown (by omega) (by rw [m5]; exact hnM) (by rw [eS]; omega) (by rw [eS, m5]; omega)
    have h8 := Runtime.CloneT.toNat_add_neg (t := R .x22) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h8]; simp; omega))
    refine ih (k - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1,
      by rw [(nS _).2.2.2.2, m5]; exact hS2, hS8, (nS _).1, (nS _).2.1, (nS _).2.2.1, (nS _).2.2.2.1⟩, rfl, hP1,
      by rw [(nS _).2.2.2.2, m5]; exact hP2, hP8, ?_, ?_, ?_, j + 1, by omega, ?_, ?_⟩
    · rw [k20, k10]; exact hh0
    · rw [k2 _ 8 (by omega), k1 _ 8 (by omega)]; exact hh8
    · rw [k2 _ 16 (by omega), k1 _ 16 (by omega)]; exact hh16
    · simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]; omega
    · simp only [Tactic.rf]; rw [h8]; omega
  · -- past the last item
    have hn8 : (regs .x12).toNat * 8 < 2 ^ 63 := by omega
    refine exit hp hL hk (by omega) hW h16 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1,
      by rw [(nS _).2.2.2.2, m5]; exact hS2, hS8, (nS _).1, (nS _).2.1, (nS _).2.2.1, (nS _).2.2.2.1⟩
      fun r => post_ok hwin hal ?_ ?_ ?_ (.inr ⟨hP1', hP1, by rw [(nS _).2.2.2.2, m5]; omega, hP8⟩) hn8
    · rw [k20, k10]; exact hh0
    · rw [k2 _ 8 (by omega), k1 _ 8 (by omega)]; exact hh8
    · rw [k2 _ 16 (by omega), k1 _ 16 (by omega)]; exact hh16

/-- **The header's three stores** at `h`, a caller's 24 bytes in a window, all in the frame's `out`: the slots, the
    frame, `env.Static`, the code and `NEXT` kept, the three words read back. -/
theorem hdr3 {env : Env} {m M : MachineState} {top ret h v0 v1 v2 : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hown : env.Owned m top h 24) (hwin : InWin env h 24)
    (hout : ∀ b, InRange h 24 b → out b) (hF : env.Frame top out m M) (hS : env.Static M) (hc : M.code = m.code)
    (hsl : Slots M top ret regs) :
    Slots (((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2) top ret regs ∧
      env.Frame top out m (((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2) ∧
      env.Static (((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2) ∧
      (((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).code = m.code ∧
      env.next (((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2) = env.next M ∧
      (((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).getMem h = v0 ∧
      (((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).getMem (h + 8#64) = v1 ∧
      (((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).getMem (h + 16#64) = v2 := by
  have hlay := env.layout
  have hnM := hF.2.1
  have hnm := hF.1
  have h24 := hown.2
  have e8 : (h + 8#64).toNat = h.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (h + 16#64).toNat = h.toNat + 16 := toNat_add_ofNat (by omega)
  have hn : ∀ b : Word, h.toNat ≤ b.toNat → b.toNat < h.toNat + 24 → b ≠ env.nextAddr := fun b h1 h2 e => by
    rw [e] at h1 h2; unfold InWin at hwin; omega
  have hst : ∀ b : Word, h.toNat ≤ b.toNat → b.toNat < h.toNat + 24 →
      b.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ b.toNat := fun b h1 h2 => by
    unfold InWin at hwin; omega
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 112 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e1 := es 18446744073709551608#64 8 rfl (by omega)
  have e2 := es 18446744073709551600#64 16 rfl (by omega)
  have e3 := es 18446744073709551592#64 24 rfl (by omega)
  have e4 := es 18446744073709551584#64 32 rfl (by omega)
  have e5 := es 18446744073709551576#64 40 rfl (by omega)
  have e6 := es 18446744073709551568#64 48 rfl (by omega)
  have e7 := es 18446744073709551560#64 56 rfl (by omega)
  have e8' := es 18446744073709551552#64 64 rfl (by omega)
  have e9 := es 18446744073709551544#64 72 rfl (by omega)
  have e10 := es 18446744073709551536#64 80 rfl (by omega)
  have e11 := es 18446744073709551528#64 88 rfl (by omega)
  have hsep : h.toNat + 24 ≤ top.toNat - 88 ∨ top.toNat ≤ h.toNat := by rcases hown.1 with h1 | h1 <;> omega
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  refine ⟨?_, ?_, ?_, by simp only [MachineState.code_setMem, hc], ?_, ?_, ?_, MachineState.getMem_setMem_eq⟩
  · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hsl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat rw [MachineState.getMem_setMem_ne (fun e => by
        have h' := congrArg BitVec.toNat e
        simp only [e8, e16, e1, e2, e3, e4, e5, e6, e7, e8', e9, e10, e11] at h'; omega)]
    exacts [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · refine Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF (hout _ ⟨le_refl _, by omega⟩)
      (hn _ (le_refl _) (by omega))) (hout _ ⟨by omega, by omega⟩) (hn _ (by omega) (by omega)))
      (hout _ ⟨by omega, by omega⟩) (hn _ (by omega) (by omega))
  · exact Tactic.static_store (Tactic.static_store (Tactic.static_store hS (hst _ (le_refl _) (by omega)))
      (hst _ (by omega) (by omega))) (hst _ (by omega) (by omega))
  · rw [Tactic.next_setMem (hn _ (by omega) (by omega)), Tactic.next_setMem (hn _ (by omega) (by omega)),
      Tactic.next_setMem (hn _ (le_refl _) (by omega))]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]

/-- The slots kept by a memory that agrees from `top - 88` up to `top`. -/
theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 112 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 88 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 88 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := Runtime.CloneT.toNat_add_neg (t := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hsl
  exact ⟨(es _ 8 rfl (by omega) (by omega)).trans s1, (es _ 16 rfl (by omega) (by omega)).trans s2,
    (es _ 24 rfl (by omega) (by omega)).trans s3, (es _ 32 rfl (by omega) (by omega)).trans s4,
    (es _ 40 rfl (by omega) (by omega)).trans s5, (es _ 48 rfl (by omega) (by omega)).trans s6,
    (es _ 56 rfl (by omega) (by omega)).trans s7, (es _ 64 rfl (by omega) (by omega)).trans s8,
    (es _ 72 rfl (by omega) (by omega)).trans s9, (es _ 80 rfl (by omega) (by omega)).trans s10,
    (es _ 88 rfl (by omega) (by omega)).trans s11⟩

/-- **One store into the frame's `out`**, a word apart from the slots and in a window: the slots, the frame,
    `env.Static`, the code and `NEXT` kept. -/
theorem out_store {env : Env} {m M : MachineState} {top ret b v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hb : out b) (hwin : InWin env b 8)
    (hsep : b.toNat + 8 ≤ top.toNat - 88 ∨ top.toNat ≤ b.toNat) (hF : env.Frame top out m M) (hS : env.Static M)
    (hc : M.code = m.code) (hsl : Slots M top ret regs) :
    Slots (M.setMem b v) top ret regs ∧ env.Frame top out m (M.setMem b v) ∧ env.Static (M.setMem b v) ∧
      (M.setMem b v).code = m.code ∧ env.next (M.setMem b v) = env.next M := by
  have hlay := env.layout
  have hn : b ≠ env.nextAddr := fun e => by rw [e] at hwin; unfold InWin at hwin; omega
  refine ⟨slots_keep (by omega) (fun a h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_out hF hb hn, Tactic.static_store hS (by unfold InWin at hwin; omega),
    by rw [MachineState.code_setMem, hc], Tactic.next_setMem hn⟩

/-- A word `memcpy` may write, to `P` aligned, lies in `[P, P + n)`. -/
theorem copyOut_in {R : Reg → Word} {M : MachineState} {b P : Word} {n : Nat} (hR10 : R .x10 = P)
    (hR12 : (R .x12).toNat = n) (hP8 : P.toNat % 8 = 0) (hb : CopyOut R M b) : P.toNat ≤ b.toNat ∧ b.toNat < P.toNat + n := by
  unfold CopyOut DwordsOf InRange at hb
  rw [toNat_alignToDword, hR10, hR12] at hb
  omega

set_option rv_sym.heap true in
/-- **From instruction 114**: the sorted copy (`alloc`, `memcpy`) and the result's header, then the placing loop; or,
    with no items, the empty result. -/
theorem tail {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needM needP needH : Nat} (hn : 112 ≤ need) (hnA : 112 + needA ≤ need)
    (hnC : 112 + needM ≤ need) (hnP : 112 + needP ≤ need) (hnH : 112 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP) (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top S : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 8) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hA : Args env m regs)
    (hown : env.Owned m top (regs .x10) 24) (hwin : InWin env (regs .x10) 24) (hal8 : (regs .x10).toNat % 8 = 0) :
    ∀ R M, (Common env m top ret S regs R M ∧ R .x21 = regs .x11 ∧ R .x22 = regs .x12 <<< 3 ∧ R .x24 = regs .x24) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hS1, hS2, hS8, hsl, hF, hSt, hcode⟩, -⟩ := id hI
  obtain ⟨hB1, hk1, hk59, hB2⟩ := id hA
  have hnM := hF.2.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hF.1
  have t112 : (top + 18446744073709551504#64).toNat = top.toNat - 112 :=
    Runtime.CloneT.toNat_add_neg (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have hsep : (regs .x10).toNat + 24 ≤ top.toNat - 88 ∨ top.toNat ≤ (regs .x10).toNat := by
    rcases hown.1 with h1 | h1 <;> omega
  have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by have := hown.2; omega)
  have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by have := hown.2; omega)
  have hs : (regs .x12 <<< 3).toNat = 8 * (regs .x12).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rcases hB1 with h | ⟨-, h2, -⟩
    · rw [h]
    · unfold Env.Live at h2; omega
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hlay := env.layout
  rv_introT hI
  rv_symT hp stop [142, 190] with [hL] using [hal', hcp, hpb, hhe]
  · -- no items: the empty result
    have hn0 : (regs .x12).toNat = 0 := by rw [hc]; rfl
    obtain ⟨s1, f1, st1, c1, nx1, r0, r8, r16⟩ := hdr3 (v0 := 0#64) (v1 := 8#64) (v2 := 0#64) (by omega) hown hwin
      (fun b hb => hb) hI_25 hI_26 hI_27 ⟨hI_14, hI_15, hI_16, hI_17, hI_18, hI_19, hI_20, hI_21, hI_22, hI_23, hI_24⟩
    exact exit hp hL hk (by omega) hW h16 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hI_11,
      by rw [nx1]; exact hI_12, hI_13, s1, f1, st1, c1⟩ fun r =>
      post_ok hwin hal8 (by rw [r0, hc]) r8 (by rw [r16, hc]) (.inl hn0) (by omega)
  all_goals
    have hn0 : (regs .x12).toNat ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq h)
    obtain ⟨a1, a2, a3⟩ : 0x10000000 ≤ (regs .x11).toNat ∧
        (regs .x11).toNat + 8 * (regs .x12).toNat ≤ (env.next m).toNat ∧ (regs .x11).toNat % 8 = 0 := by
      rcases hB1 with h | ⟨h1, h2, h3⟩
      · exact absurd h hn0
      · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
    have hn1 := hret1_14.1
    have hn2 := hret1_14.2.1
  · -- `memcpy`'s ranges
    rw [hs]
    refine .inr ⟨.inl ⟨by omega, by omega⟩, .inl (by omega), ?_, .inl (by omega)⟩
    rw [inWindow_iff]; omega
  · -- the placing loop from its first item
    have hF1 : env.Frame top (SretVecOut regs m) m m1 := Tactic.frame_callF hI_25 hret1_14 (by rw [t112]; omega)
    have hsl1 : Slots m1 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep1_1 a (BitVec.le_def.2 (by rw [t112]; omega)))
      ⟨hI_14, hI_15, hI_16, hI_17, hI_18, hI_19, hI_20, hI_21, hI_22, hI_23, hI_24⟩
    obtain ⟨s2, f2, st2, c2, nx2, r0, r8, r16⟩ := hdr3 (v0 := regs .x12) (v1 := r1 .x10) (v2 := 0#64) (by omega)
      hown hwin (fun b hb => hb) hF1 hret1_15 (hret1_19.trans hI_27) hsl1
    have hcout : ∀ b, CopyOut (updReg (Tactic.rf (r1 .x0) L.s2.hi (top + 18446744073709551504#64) (r1 .x3) (r1 .x4)
        (r1 .x5) (r1 .x6) (r1 .x7) (regs .x15) (regs .x13 + 1#64) (r1 .x10) (regs .x11) (regs .x12 <<< 3) (r1 .x13)
        (r1 .x14) (r1 .x15) (r1 .x16) (r1 .x17) (regs .x12) (regs .x14) (regs .x13) (regs .x11) (regs .x12 <<< 3)
        (regs .x10) (r1 .x10) S (regs .x26) (regs .x27) (r1 .x28) (r1 .x29) (r1 .x30) (r1 .x31)) .x1
        (L.base + 280#64)) (((m1.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) (r1 .x10)).setMem
        (regs .x10 + 16#64) 0#64) b →
        (r1 .x10).toNat ≤ b.toNat ∧ b.toNat < (r1 .x10).toNat + 8 * (regs .x12).toNat :=
      fun b hb => copyOut_in (by exact rfl) (by exact hs) hret1_17 hb
    have hn3 := hret3_14.1
    rw [nx2] at hn3
    have hF3 : env.Frame top (SretVecOut regs m) m m3 := f2.trans hret3_14 (by rw [t112]; omega) fun b hb =>
      Or.inr (Or.inl ⟨by have := hcout b hb; omega, by have := hcout b hb; omega⟩)
    have hsl3 : Slots m3 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep3_1 a (BitVec.le_def.2 (by rw [t112]; omega)) fun hb => by
        have := hcout a hb; omega) s2
    have hk3 : ∀ a : Word, ((regs .x10).toNat ≤ a.toNat ∧ a.toNat < (regs .x10).toNat + 24) →
        MachineState.getMem m3 a = _ := fun a ha => keep3_2 a
      (by rw [nx2]; rcases hown.1 with h | h <;> [exact .inl (by omega); exact .inr (by rw [t112]; omega)])
      fun hb => by have := hcout a hb; rcases hown.1 with h | h <;> omega
    obtain ⟨s4, f4, st4, c4, nx4⟩ := out_store (v := regs .x12) (b := regs .x10 + 16#64) (by omega)
      ⟨by omega, by simp only [Layouts.Vec.byteSize]; omega⟩ (Runtime.MemsetT.InWin.sub hwin (by omega) (by omega))
      (by omega) hF3 hret3_15
      (by rw [hret3_19, c2]) hsl3
    have q0 : MachineState.getMem (MachineState.setMem m3 (regs .x10 + 16#64) (regs .x12)) (regs .x10) = regs .x12 := by
      rw [MachineState.getMem_setMem_ne (fun e => by have := congrArg BitVec.toNat e; omega), hk3 _ ⟨by omega, by omega⟩,
        r0]
    have q8 : MachineState.getMem (MachineState.setMem m3 (regs .x10 + 16#64) (regs .x12)) (regs .x10 + 8#64) =
        r1 .x10 := by
      rw [MachineState.getMem_setMem_ne (fun e => by have := congrArg BitVec.toNat e; omega),
        hk3 _ ⟨by omega, by omega⟩, r8]
    refine loop3 (S := S) (P := r1 .x10) hp hL hn hnP hpb hk hstop hstk hnx hW h16 hA hn0 hown hwin hal8
      ((regs .x12).toNat - 1) _ _
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hI_11, by rw [nx4]; omega, hI_13, s4, f4, st4, c4⟩, rfl,
        by omega, by rw [nx4]; omega, hret1_17, q0, q8, MachineState.getMem_setMem_eq, 0, by omega, by rfl, ?_⟩
    simp only [Tactic.rf]; rw [hs]; omega

set_option rv_sym.heap true in
/-- **The prefix sums**, from their head to instruction 114. -/
theorem loop2 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {need : Nat} (hn : 112 ≤ need)
    {Q : State rvIsa → Prop} {ret top S : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (_hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (hk59 : (regs .x13).toNat < 2 ^ 59)
    (hk3 : ∀ R M, (Common env m top ret S regs R M ∧ R .x21 = regs .x11 ∧ R .x22 = regs .x12 <<< 3 ∧
      R .x24 = regs .x24) → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv2 env m top ret S regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 102, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv2 env m top ret S regs) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hS1, hS2, hS8, hsl, hF, hSt, hcode⟩, -, -, -, -, j, hj, hx10⟩ := id hI
  have hnM := hF.2.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hS1' : 0x10000000 ≤ S.toNat := by omega
  have e8 : (R .x10 + 18446744073709551608#64).toNat = (R .x10).toNat - 8 :=
    Runtime.CloneT.toNat_add_neg (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have e10 : (R .x10 + 8#64).toNat = (R .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have hs : (regs .x13 <<< 3).toNat = 8 * (regs .x13).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e11 : (S + 8#64 + regs .x13 <<< 3).toNat = S.toNat + 8 + 8 * (regs .x13).toNat := by
    rw [BitVec.toNat_add, toNat_add_ofNat (by omega), hs]; omega
  obtain ⟨m1, m2, m3, m4, m5⟩ := store_ok (a := R .x10) (v := MachineState.getMem M (R .x10) +
    MachineState.getMem M (R .x10 + 18446744073709551608#64)) (by omega) hF hSt hcode hsl (by omega) (by omega)
  rv_introT hI
  rv_symT hp stop [102, 114] with [_hL]
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [e10, e11]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1, by rw [m5]; exact hS2, hS8,
      m1, m2, m3, m4⟩, rfl, rfl, rfl, rfl, j + 1, by omega, ?_⟩
    simp only [Tactic.rf]; rw [e10]; omega
  · -- past the last word
    exact hk3 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1, by rw [m5]; exact hS2, hS8, m1, m2, m3, m4⟩,
      rfl, rfl, rfl⟩

set_option rv_sym.heap true in
/-- **The counting loop**, from its head to the prefix sums' head (instruction 102). -/
theorem loop1 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needP : Nat} (hn : 112 ≤ need) (hnP : 112 + needP ≤ need)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top S : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hA : Args env m regs) (hn0 : (regs .x12).toNat ≠ 0)
    (hk2 : ∀ R M, LInv2 env m top ret S regs ((regs .x13).toNat - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 102, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv1 env m top ret S regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv1 env m top ret S regs) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨hB1, hk1, hk59, hB2⟩ := hA
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hS1, hS2, hS8, -, hF, -, -⟩, -, -, -, j, hj, hx12, hx11⟩ := id hI
  have hnM := hF.2.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hF.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hsl, -, hSt, hcode⟩ := hI.1
  have hB1' : 0x10000000 ≤ (regs .x11).toNat ∧ (regs .x11).toNat + 8 * (regs .x12).toNat ≤ (env.next m).toNat ∧
      (regs .x11).toNat % 8 = 0 := by
    rcases hB1 with h | ⟨h1, h2, h3⟩
    · exact absurd h hn0
    · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
  have hS1' : 0x10000000 ≤ S.toNat := by omega
  rv_introT hI
  rv_symT hp stop [66, 102] with [hL] using [hpb]
  · exact (member_ok hB2 hnx hW1 hc).1
  · exact (member_ok hB2 hnx hW1 hc).2
  · refine (start_ok hS1' hS2 hS8 hnM hW1 ?_).1
    rw [succ_toNat hc]; have := BitVec.lt_def.1 hc; omega
  · refine (start_ok hS1' hS2 hS8 hnM hW1 ?_).2.1
    rw [succ_toNat hc]; have := BitVec.lt_def.1 hc; omega
  · refine (start_ok hS1' hS2 hS8 hnM hW1 ?_).1
    rw [succ_toNat hc]; have := BitVec.lt_def.1 hc; omega
  · refine (start_ok hS1' hS2 hS8 hnM hW1 ?_).2.1
    rw [succ_toNat hc]; have := BitVec.lt_def.1 hc; omega
  all_goals
    have hK := BitVec.lt_def.1 hc_2
    have e1 := (start_ok hS1' hS2 hS8 hnM hW1 (K := MachineState.getMem M (regs .x14 +
      MachineState.getMem M (R .x12) <<< 5 + 24#64) + 1#64) (by rw [succ_toNat hc_2]; omega)).2.2
    rw [succ_toNat hc_2] at e1
    obtain ⟨m1, m2, m3, m4, m5⟩ := store_ok (v := MachineState.getMem M (S + (MachineState.getMem M (regs .x14 +
      MachineState.getMem M (R .x12) <<< 5 + 24#64) + 1#64) <<< 3) + 1#64) (by omega) hF hSt hcode hsl
      (by rw [e1]; omega) (by rw [e1]; omega)
    have h8 := Runtime.CloneT.toNat_add_neg (t := R .x11) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h8]; simp; omega))
    refine ih (k - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1, by rw [m5]; exact hS2, hS8,
      m1, m2, m3, m4⟩, rfl, rfl, rfl, j + 1, by omega, ?_, ?_⟩
    · simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]; omega
    · simp only [Tactic.rf]; rw [h8]; omega
  · -- past the last item
    exact hk2 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1, by rw [m5]; exact hS2, hS8, m1, m2, m3, m4⟩,
      rfl, rfl, rfl, rfl, 0, by omega, by simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]⟩

/-- The prologue's eleven saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)).setMem (top + 18446744073709551536#64) (regs .x24)).setMem
    (top + 18446744073709551528#64) (regs .x25)

/-- The prologue's stores: in the frame, `env.Static`, `NEXT` and the code kept, the slots holding the saved
    words. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) :
    env.Frame top out m (saved m top ret regs) ∧ env.Static (saved m top ret regs) ∧
      env.next (saved m top ret regs) = env.next m ∧ Slots (saved m top ret regs) top ret regs ∧
      (saved m top ret regs).code = m.code := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 112 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e1 := es 18446744073709551608#64 8 rfl (by omega)
  have e2 := es 18446744073709551600#64 16 rfl (by omega)
  have e3 := es 18446744073709551592#64 24 rfl (by omega)
  have e4 := es 18446744073709551584#64 32 rfl (by omega)
  have e5 := es 18446744073709551576#64 40 rfl (by omega)
  have e6 := es 18446744073709551568#64 48 rfl (by omega)
  have e7 := es 18446744073709551560#64 56 rfl (by omega)
  have e8 := es 18446744073709551552#64 64 rfl (by omega)
  have e9 := es 18446744073709551544#64 72 rfl (by omega)
  have e10 := es 18446744073709551536#64 80 rfl (by omega)
  have e11 := es 18446744073709551528#64 88 rfl (by omega)
  refine ⟨?_, ?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved]
    repeat (first | exact Env.Frame.refl hnx | refine Tactic.frame_slot ?_ (by omega) (by omega))
  · simp only [saved]
    repeat (first | exact hS | refine Env.static_setMem_stack ?_ (by omega))
  · simp only [saved]
    repeat rw [Env.next_setMem_stack (by omega)]
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at h'; omega)])

theorem ptr_slot (top : Word) : taPtrAt (top + 18446744073709551504#64) = top + 18446744073709551520#64 := by
  unfold taPtrAt; rw [BitVec.add_assoc]; rfl

set_option rv_sym.heap true in
/-- **This `counting_sort` is total**, with 112 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needT needA needM needP needH : Nat} (hnT : 112 + needT ≤ need) (hnA : 112 + needA ≤ need)
    (hnC : 112 + needM ≤ need) (hnP : 112 + needP ≤ need) (hnH : 112 + needH ≤ need)
    (hta : TryAllocSpecT env p L.tryAllocateInInVerifier.idx needT) (hal : AllocSpecT env p L.alloc.idx needA)
    (hcp : MemcpySpecT env p L.memcpy.idx needM) (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  rv_autoT hp stop [66, 102] with [hL] using [hta, hhe]
  all_goals
    have hlay := env.layout
    rw [hpre_2] at hpre_6
    have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
    obtain ⟨hF0, hS0, hn0, hsl0, hc0⟩ := saved_ok (out := SretVecOut regs m) (ret := ret) (regs := regs) hlim hpre_5
      hpre_4
    simp only [saved] at hF0 hS0 hn0 hsl0 hc0
    have t112 : (top + 18446744073709551504#64).toNat = top.toNat - 112 :=
      Runtime.CloneT.toNat_add_neg (c := 18446744073709551504#64) (k := 112) rfl (by omega)
    have hF1 := hF0.trans hret1_14 (by rw [t112]; omega) fun b hb => Or.inl (by
      unfold TryAllocOut InRange at hb; rw [show ((updReg (Tactic.rf (regs .x0) L.s0.hi (top + 18446744073709551504#64)
        (regs .x3) (regs .x4) (regs .x5) (regs .x6) (regs .x7) (regs .x15) (regs .x13 + 1#64)
        (top + 18446744073709551504#64) (regs .x13 + 1#64) (1#64) (8#64) (8#64) (regs .x15) (regs .x16) (regs .x17)
        (regs .x12) (regs .x14) (regs .x13) (regs .x11) (regs .x22) (regs .x10) (regs .x24) (regs .x25) (regs .x26)
        (regs .x27) (regs .x28) (regs .x29) (regs .x30) (regs .x31)) .x1 (L.base + 104#64)) .x10) =
        top + 18446744073709551504#64 from rfl, t112] at hb
      unfold tryAllocBytes at hb; omega)
    have hsl1 : Slots m1 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep1_1 a (BitVec.le_def.2 (by rw [t112]; omega)) fun hb => by
        unfold TryAllocOut InRange at hb; unfold tryAllocBytes at hb
        have : (updReg (Tactic.rf (regs .x0) L.s0.hi (top + 18446744073709551504#64)
          (regs .x3) (regs .x4) (regs .x5) (regs .x6) (regs .x7) (regs .x15) (regs .x13 + 1#64)
          (top + 18446744073709551504#64) (regs .x13 + 1#64) (1#64) (8#64) (8#64) (regs .x15) (regs .x16) (regs .x17)
          (regs .x12) (regs .x14) (regs .x13) (regs .x11) (regs .x22) (regs .x10) (regs .x24) (regs .x25) (regs .x26)
          (regs .x27) (regs .x28) (regs .x29) (regs .x30) (regs .x31)) .x1 (L.base + 104#64)) .x10 =
          top + 18446744073709551504#64 := rfl
        rw [this, t112] at hb; omega) hsl0
    have hk1 : (regs .x13 + 1#64).toNat = (regs .x13).toNat + 1 := toNat_add_ofNat (by omega)
    obtain ⟨-, hok⟩ := hret1_16 hc_1
    rw [hk1, show (8#64 : Word).toNat = 8 from rfl, ptr_slot] at hok
    obtain ⟨-, -, hfr, hS8⟩ := hok.resolve_left (by omega)
    unfold Env.Fresh at hfr
    rw [hn0] at hfr
    have hA : Args env m regs := ⟨hpre_10, hpre_11, hpre_12, hpre_13⟩
    have hown : env.Owned m top (regs .x10) 24 := ⟨hpre_6, hpre_7⟩
    have hfin := tail (S := m1.getMem (top + 18446744073709551520#64)) hp hL (by omega) hnA hnC hnP hnH hal hcp hpb hhe
      hk hstop hpre_3 hpre_5 hpre_15 hpre_14 hA hown hpre_8 hpre_9
    have h2 := loop2 hp hL (by omega) hpre_3 hpre_5 hpre_15 hpre_12 hfin
    have hge := hpre_15.next_ge
    have hS2 : (m1.getMem (top + 18446744073709551520#64)).toNat + 8 * ((regs .x13).toNat + 1) ≤
        (env.next m1).toNat := by omega
    have hc1 := hret1_18.trans hc0
  · -- no items: the prefix sums
    exact h2 ((regs .x13).toNat - 1) _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfr.1, hS2, hS8, hsl1, hF1, hret1_15, hc1⟩,
      rfl, rfl, rfl, rfl, 0, by omega, by simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]⟩
  · -- the counting loop from its first item
    have hn0' : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    have hB := hpre_10.resolve_left hn0'
    unfold Env.Live at hB
    have hs : (regs .x12 <<< 3).toNat = 8 * (regs .x12).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    exact loop1 hp hL (by omega) hnP hpb hstop hpre_3 hpre_5 hpre_15 hpre_14 hA hn0' (h2 _) ((regs .x12).toNat - 1) _ _
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfr.1, hS2, hS8, hsl1, hF1, hret1_15, hc1⟩, rfl, rfl, rfl,
        0, by omega, by simp only [Tactic.rf]; omega, by simp only [Tactic.rf]; rw [hs]; omega⟩

end Rv64mc.Proof.Bytecode.CountingSortUsizeT

/-- info: 'Rv64mc.Proof.Bytecode.CountingSortUsizeT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Bytecode.CountingSortUsizeT.total
