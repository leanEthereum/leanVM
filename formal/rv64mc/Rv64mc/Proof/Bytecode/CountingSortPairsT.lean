/-
  Rv64mc.Proof.Bytecode.CountingSortPairsT

  `counting_sort::<(u64, u16), group_by_word::{closure#2}>(items, 256, key)` is total: called with the result's slot
  (`a0`), the items (`a1`, `a2`, 16-byte `(u64, u16)` pairs) and the byte the key reads (`a3`), it returns a vector of
  the items' length (`CloneT.ClonePostT`: `VecT`, its buffer fresh unless empty), or the run ends with the guest's
  abort (`AbortStop`) where `alloc`, the bounds check or `handle_error` does. A safety-only contract (no partial
  spec).

  The `starts` block is `alloc`'s 257 words, zeroed by `memset`; the key is a byte (`byte_le`), so `starts[key + 1]`
  and `starts[key]` lie in it without a check, and the count `starts[key]` is checked against the length before
  `sorted[starts[key]]` is written. So no access depends on what the block holds, and `memset`'s safety-only contract
  (`MemsetSafeT`) is enough. The precondition asks the items' slice in a window (`BufT`) and the result's slot a
  caller's, in a window and aligned; `a3` is unconstrained.

  The body is cut as `CountingSortUsizeT`'s: at the three loops' heads (instructions 62, 88, 130), at 100 (after the
  prefix sums) and at the return (174).

  ## Main definitions

  * `PreT`, `SpecT`, `Slots`, `Common`, `LInv1`, `LInv2`, `LInv3`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Bytecode.CountingSortUsizeT
import Rv64mc.Gen.Tmpl.Verifier.Bytecode.CountingSortTU64U16EGroupByWordClosure2

namespace Rv64mc.Proof.Bytecode.CountingSortPairsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin MemsetSafeT)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT)
open Rv64mc.Proof.Bytecode.CountingSortUsizeT (word_ok hdr_keep hdr_keep0)
open Rv64mc.Proof.Runtime.VecHdrT (copyOut_in post_ok)
open Rv64mc.Gen.Verifier.Bytecode.CountingSortTU64U16EGroupByWordClosure2 (Link tmpl)

/-- The total precondition: the result's slot a caller's, in a window and 8-byte aligned; the items (`a1`, `a2`,
    16-byte elements) a slice of a block allocated before (`BufT`). -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ BufT env m (regs .x12) (regs .x11) 16

/-- **The total contract of this `counting_sort`**: the result a vector of the items' length, its buffer fresh
    unless empty. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (ClonePostT env 16) SretVecOut AbortStop

/-- The prologue's nine saved words in `M`, at `top - 8` down to `top - 72`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23

/-- What every part after `memset` keeps: the arguments in the saved registers, the `starts` block `S` of `257`
    words fresh since the entry, the slots, the frame. -/
def Common (env : Env) (m : MachineState) (top ret S : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x8 = regs .x12 ∧ R .x18 = S ∧ R .x19 = regs .x10 ∧
    R .x20 = regs .x12 <<< 4 ∧ R .x22 = regs .x11 + regs .x12 <<< 4 ∧ R .x23 = regs .x13 <<< 61 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    (env.next m).toNat ≤ S.toNat ∧ S.toNat + 2056 ≤ (env.next M).toNat ∧ S.toNat % 8 = 0 ∧
    Slots M top ret regs ∧ env.Frame top (SretVecOut regs m) m M ∧ env.Static M ∧ M.code = m.code

/-- A byte's index, at most `255`. -/
theorem byte_le (x : Word) : (x &&& 255#64).toNat ≤ 255 := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right.trans (by decide)

/-- Word `K + 1` of the `starts` block, `K` a byte: in a window, aligned. -/
theorem start1_ok {env : Env} {M : MachineState} {S K : Word} (hS1 : 0x10000000 ≤ S.toNat)
    (hS2 : S.toNat + 2056 ≤ (env.next M).toNat) (hS8 : S.toNat % 8 = 0)
    (hnx : (env.next M).toNat ≤ env.heapEnd.toNat) (hend : env.heapEnd.toNat ≤ 0x78000000) (hK : K.toNat ≤ 255) :
    inWindow (S + K <<< 3 + 8#64) 8 = true ∧ (S + K <<< 3 + 8#64).toNat % 8 = 0 ∧
      (S + K <<< 3 + 8#64).toNat = S.toNat + 8 * K.toNat + 8 := by
  have hs : (K <<< 3).toNat = 8 * K.toNat := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e : (S + K <<< 3 + 8#64).toNat = S.toNat + 8 * K.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hs]; simp only [BitVec.toNat_ofNat]; omega
  rw [inWindow_iff, e]
  omega

/-- `top - k` for the frame's offsets. -/
theorem off {top c : Word} {k : Nat} (hc : c.toNat + k = 2 ^ 64) (hk : k ≤ top.toNat) : (top + c).toNat = top.toNat - k :=
  Runtime.CloneT.toNat_add_neg hc hk

/-- The slots kept by a memory that agrees from `top - 72` up to `top`. -/
theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 80 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 72 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 72 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := off (top := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hsl
  exact ⟨(es _ 8 rfl (by omega) (by omega)).trans s1, (es _ 16 rfl (by omega) (by omega)).trans s2,
    (es _ 24 rfl (by omega) (by omega)).trans s3, (es _ 32 rfl (by omega) (by omega)).trans s4,
    (es _ 40 rfl (by omega) (by omega)).trans s5, (es _ 48 rfl (by omega) (by omega)).trans s6,
    (es _ 56 rfl (by omega) (by omega)).trans s7, (es _ 64 rfl (by omega) (by omega)).trans s8,
    (es _ 72 rfl (by omega) (by omega)).trans s9⟩

/-- One doubleword store into a block allocated since the entry: the slots, the frame, `env.Static`, the code and
    `NEXT` kept. -/
theorem store8 {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hF : env.Frame top out m M) (hS : env.Static M)
    (hc : M.code = m.code) (hsl : Slots M top ret regs) (ha1 : (env.next m).toNat ≤ a.toNat)
    (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    Slots (M.setMem a v) top ret regs ∧ env.Frame top out m (M.setMem a v) ∧ env.Static (M.setMem a v) ∧
      (M.setMem a v).code = m.code ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  have hnM := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  exact ⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1; omega) hsl,
    Tactic.frame_fresh hF rfl ha1 (by omega), Tactic.static_store hS (.inl (by omega)),
    by rw [MachineState.code_setMem, hc], Tactic.next_setMem hne⟩

/-- **One store into the frame's `out`**, a word apart from the slots and in a window. -/
theorem out_store {env : Env} {m M : MachineState} {top ret b v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hb : out b) (hwin : InWin env b 8)
    (hsep : b.toNat + 8 ≤ top.toNat - 72 ∨ top.toNat ≤ b.toNat) (hF : env.Frame top out m M) (hS : env.Static M)
    (hc : M.code = m.code) (hsl : Slots M top ret regs) :
    Slots (M.setMem b v) top ret regs ∧ env.Frame top out m (M.setMem b v) ∧ env.Static (M.setMem b v) ∧
      (M.setMem b v).code = m.code ∧ env.next (M.setMem b v) = env.next M := by
  have hlay := env.layout
  have hn : b ≠ env.nextAddr := fun e => by rw [e] at hwin; unfold InWin at hwin; omega
  refine ⟨slots_keep (by omega) (fun a h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_out hF hb hn, Tactic.static_store hS (by unfold InWin at hwin; omega),
    by rw [MachineState.code_setMem, hc], Tactic.next_setMem hn⟩

/-- The prologue's nine saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)

/-- The prologue's stores: in the frame, `env.Static`, `NEXT` and the code kept, the slots holding the saved
    words. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) :
    env.Frame top out m (saved m top ret regs) ∧ env.Static (saved m top ret regs) ∧
      env.next (saved m top ret regs) = env.next m ∧ Slots (saved m top ret regs) top ret regs ∧
      (saved m top ret regs).code = m.code := by
  have e1 := off (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have e2 := off (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
  have e3 := off (top := top) (c := 18446744073709551592#64) (k := 24) rfl (by omega)
  have e4 := off (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
  have e5 := off (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have e6 := off (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  have e7 := off (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  have e8 := off (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have e9 := off (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  refine ⟨?_, ?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved]
    repeat (first | exact Env.Frame.refl hnx | refine Tactic.frame_slot ?_ (by omega) (by omega))
  · simp only [saved]
    repeat (first | exact hS | refine Env.static_setMem_stack ?_ (by omega))
  · simp only [saved]
    repeat rw [Env.next_setMem_stack (by omega)]
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9] at h'; omega)])

set_option rv_sym.heap true in
/-- **The return**, from instruction 174, the result's header written. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top S : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 16) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + 80 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0) :
    ∀ R M, Common env m top ret S regs R M → (∀ r, ClonePostT env 16 regs m r M) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 174, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hPost
  have hlay := env.layout
  rv_introT hI
  rv_symT hp with [_hL]
  exact ⟨⟨rfl, hI_16, hI_17, hI_18, hI_19, hI_20, hI_21, hI_22, hI_23, rfl, rfl, rfl, rfl⟩, hI_24, hI_25, hPost _⟩

/-- **The header's three stores** at `h`, a caller's 24 bytes in a window, all in the frame's `out`: the slots, the
    frame, `env.Static`, the code and `NEXT` kept, the three words read back. -/
theorem hdr3 {env : Env} {m M : MachineState} {top ret h v0 v1 v2 : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hown : env.Owned m top h 24) (hwin : InWin env h 24)
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
  have hsep : ∀ k, k ≤ 16 → h.toNat + k + 8 ≤ top.toNat - 72 ∨ top.toNat ≤ h.toNat + k :=
    fun k hk => by rcases hown.1 with h1 | h1 <;> omega
  have ho : ∀ k : Nat, k ≤ 16 → ∀ b : Word, b.toNat = h.toNat + k → out b :=
    fun k hk b hb => hout _ ⟨by omega, by omega⟩
  have hw : ∀ k : Nat, k ≤ 16 → ∀ b : Word, b.toNat = h.toNat + k → InWin env b 8 :=
    fun k hk b hb => Runtime.MemsetT.InWin.sub hwin (by omega) (by omega)
  obtain ⟨s1, f1, t1, c1, n1⟩ :=
    out_store (v := v0) hlim (ho 0 (by omega) _ rfl) (hw 0 (by omega) _ rfl) (hsep 0 (by omega)) hF hS hc hsl
  obtain ⟨s2, f2, t2, c2, n2⟩ := out_store (v := v1) hlim (ho 8 (by omega) _ e8) (hw 8 (by omega) _ e8)
    (by rw [e8]; exact hsep 8 (by omega)) f1 t1 c1 s1
  obtain ⟨s3, f3, t3, c3, n3⟩ := out_store (v := v2) hlim (ho 16 (by omega) _ e16) (hw 16 (by omega) _ e16)
    (by rw [e16]; exact hsep 16 (by omega)) f2 t2 c2 s2
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  refine ⟨s3, f3, t3, c3, by rw [n3, n2, n1], ?_, ?_, MachineState.getMem_setMem_eq⟩
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]

/-- The counting loop's head (instruction 62) with `k + 1` items left: `x11` at item `j`. -/
def LInv1 (env : Env) (m : MachineState) (top ret S : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Common env m top ret S regs R M ∧ R .x9 = regs .x11 ∧ R .x21 = regs .x13 ∧
    R .x10 = (regs .x13 <<< 61) >>> 58 ∧
    ∃ j, j + k + 1 = (regs .x12).toNat ∧ (R .x11).toNat = (regs .x11).toNat + 16 * j

/-- The prefix sums' head (instruction 88) with `k + 1` words left. -/
def LInv2 (env : Env) (m : MachineState) (top ret S : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Common env m top ret S regs R M ∧ R .x9 = regs .x11 ∧ R .x21 = regs .x13 ∧ R .x11 = S + 2056#64 ∧
    ∃ j, j + k + 1 = 256 ∧ (R .x10).toNat = S.toNat + 8 + 8 * j

/-- The items' slice in the heap, when it has any. -/
def Items (env : Env) (m : MachineState) (regs : Reg → Word) : Prop :=
  0x10000000 ≤ (regs .x11).toNat ∧ (regs .x11).toNat + 16 * (regs .x12).toNat ≤ (env.next m).toNat ∧
    (regs .x11).toNat % 8 = 0

set_option rv_sym.heap true in
/-- **The prefix sums**, from their head to instruction 100. -/
theorem loop2 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {need : Nat} (hn : 80 ≤ need)
    {Q : State rvIsa → Prop} {ret top S : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m)
    (hk3 : ∀ R M, (Common env m top ret S regs R M ∧ R .x9 = regs .x11 ∧ R .x21 = regs .x13) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 100, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv2 env m top ret S regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 88, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv2 env m top ret S regs) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hS1, hS2, hS8, hsl, hF, hSt, hcode⟩, -, -, -, j, hj, hx10⟩ := id hI
  have hnM := hF.2.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have e8 : (R .x10 + 18446744073709551608#64).toNat = (R .x10).toNat - 8 :=
    Runtime.CloneT.toNat_add_neg (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have e10 : (R .x10 + 8#64).toNat = (R .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have e11 : (S + 2056#64).toNat = S.toNat + 2056 := toNat_add_ofNat (by omega)
  obtain ⟨m1, m2, m3, m4, m5⟩ := store8 (a := R .x10) (v := MachineState.getMem M (R .x10) +
    MachineState.getMem M (R .x10 + 18446744073709551608#64)) (by omega) hF hSt hcode hsl (by omega) (by omega)
  rv_introT hI
  rv_symT hp stop [88, 100] with [_hL]
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [e10, e11]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1,
      by rw [m5]; exact hS2, hS8, m1, m2, m3, m4⟩, rfl, rfl, rfl, j + 1, by omega, ?_⟩
    simp only [Tactic.rf]; rw [e10]; omega
  · exact hk3 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1, by rw [m5]; exact hS2, hS8, m1, m2, m3,
      m4⟩, rfl, rfl⟩

set_option rv_sym.heap true in
/-- **The counting loop**, from its head to the prefix sums' head. -/
theorem loop1 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {need : Nat} (hn : 80 ≤ need)
    {Q : State rvIsa → Prop} {ret top S : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (_hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (hI0 : Items env m regs)
    (hk2 : ∀ R M, LInv2 env m top ret S regs 255 R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 88, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv1 env m top ret S regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 62, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv1 env m top ret S regs) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hS1, hS2, hS8, hsl, hF, hSt, hcode⟩, -, -, -, j, hj, hx11⟩ := id hI
  obtain ⟨a1, a2, a3⟩ := hI0
  have hnM := hF.2.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hF.1
  have hS1' : 0x10000000 ≤ S.toNat := by omega
  have hs : (regs .x12 <<< 4).toNat = 16 * (regs .x12).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e22 : (regs .x11 + regs .x12 <<< 4).toNat = (regs .x11).toNat + 16 * (regs .x12).toNat := by
    rw [BitVec.toNat_add, hs]; omega
  have e16 : (R .x11 + 16#64).toNat = (R .x11).toNat + 16 := toNat_add_ofNat (by omega)
  rv_introT hI
  rv_symT hp stop [62, 88] with [_hL]
  · exact (start1_ok hS1' hS2 hS8 hnM hW1 (byte_le _)).1
  · exact (start1_ok hS1' hS2 hS8 hnM hW1 (byte_le _)).2.1
  · exact (start1_ok hS1' hS2 hS8 hnM hW1 (byte_le _)).1
  · exact (start1_ok hS1' hS2 hS8 hnM hW1 (byte_le _)).2.1
  all_goals
    have hK := byte_le (MachineState.getMem M (R .x11) >>> (regs .x13 <<< 61 >>> 58 &&& 63#64).toNat)
    have eA := (start1_ok hS1' hS2 hS8 hnM hW1 hK).2.2
    obtain ⟨m1, m2, m3, m4, m5⟩ := store8 (v := MachineState.getMem M (S + (MachineState.getMem M (R .x11) >>>
      (regs .x13 <<< 61 >>> 58 &&& 63#64).toNat &&& 255#64) <<< 3 + 8#64) + 1#64) (by omega) hF hSt hcode hsl
      (by rw [eA]; omega) (by rw [eA]; omega)
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [e16, e22]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1,
      by rw [m5]; exact hS2, hS8, m1, m2, m3, m4⟩, rfl, rfl, rfl, j + 1, by omega, ?_⟩
    simp only [Tactic.rf]; rw [e16]; omega
  · exact hk2 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1, by rw [m5]; exact hS2, hS8, m1, m2, m3,
      m4⟩, rfl, rfl, rfl, 0, by omega, by simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]⟩

/-- Element `c` of a block `P` of `n` 16-byte elements below `NEXT`, `c` below `n`: its doubleword and its halfword
    at `+ 8` in a window, aligned. -/
theorem elt16_ok {env : Env} {M : MachineState} {P c : Word} {n : Nat} (hP1 : 0x10000000 ≤ P.toNat)
    (hP2 : P.toNat + 16 * n ≤ (env.next M).toNat) (hP8 : P.toNat % 8 = 0)
    (hnx : (env.next M).toNat ≤ env.heapEnd.toNat) (hend : env.heapEnd.toNat ≤ 0x78000000) (hc : c.toNat < n) :
    inWindow (P + c <<< 4) 8 = true ∧ (P + c <<< 4).toNat % 8 = 0 ∧ (P + c <<< 4).toNat = P.toNat + 16 * c.toNat ∧
      inWindow (P + c <<< 4 + 8#64) 2 = true ∧ (P + c <<< 4 + 8#64).toNat % 8 = 0 ∧
      (P + c <<< 4 + 8#64).toNat = P.toNat + 16 * c.toNat + 8 := by
  have hs : (c <<< 4).toNat = 16 * c.toNat := by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e : (P + c <<< 4).toNat = P.toNat + 16 * c.toNat := by rw [BitVec.toNat_add, hs]; omega
  have e8 : (P + c <<< 4 + 8#64).toNat = P.toNat + 16 * c.toNat + 8 := by rw [toNat_add_ofNat (by omega), e]
  rw [inWindow_iff, inWindow_iff, e, e8]
  omega

/-- A halfword store at a doubleword-aligned address is a doubleword store there. -/
theorem setHalfword_eq {M : MachineState} {b : Word} {h : BitVec 16} (hb8 : b.toNat % 8 = 0) :
    M.setHalfword b h = M.setMem b (replaceHalfword (M.getMem b) (byteOffset b / 2) h) := by
  have : alignToDword b = b := BitVec.eq_of_toNat_eq (by rw [toNat_alignToDword]; omega)
  simp only [MachineState.setHalfword, this]

/-- The placing loop's head (instruction 130) with `k + 1` items left: `x9` at item `j`; the sorted copy `P` of `n`
    elements fresh since the entry, the result's header naming it with length `n`. -/
def LInv3 (env : Env) (m : MachineState) (top ret S P : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Common env m top ret S regs R M ∧ R .x21 = P ∧ R .x11 = (regs .x13 <<< 61) >>> 58 ∧
    (env.next m).toNat ≤ P.toNat ∧ P.toNat + 16 * (regs .x12).toNat ≤ (env.next M).toNat ∧ P.toNat % 8 = 0 ∧
    M.getMem (regs .x10) = regs .x12 ∧ M.getMem (regs .x10 + 8#64) = P ∧ M.getMem (regs .x10 + 16#64) = regs .x12 ∧
    ∃ j, j + k + 1 = (regs .x12).toNat ∧ (R .x9).toNat = (regs .x11).toNat + 16 * j

set_option rv_sym.heap true in
/-- **The placing loop**, from its head to the return. -/
theorem loop3 {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needP : Nat} (hn : 80 ≤ need) (hnP : 80 + needP ≤ need)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top S P : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 16) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hI0 : Items env m regs)
    (hown : env.Owned m top (regs .x10) 24) (hwin : InWin env (regs .x10) 24)
    (hal : (regs .x10).toNat % 8 = 0) :
    ∀ k R M, LInv3 env m top ret S P regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv3 env m top ret S P regs) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hS1, hS2, hS8, hsl, hF, hSt, hcode⟩, -, -, hP1, hP2, hP8, hh0, hh8, hh16,
    j, hj, hx9⟩ := id hI
  obtain ⟨a1, a2, a3⟩ := hI0
  have hnM := hF.2.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hF.1
  have hS1' : 0x10000000 ≤ S.toNat := by omega
  have hP1' : 0x10000000 ≤ P.toNat := by omega
  have hK := byte_le (MachineState.getMem M (R .x9) >>> (regs .x13 <<< 61 >>> 58 &&& 63#64).toNat)
  have hK' : (MachineState.getMem M (R .x9) >>> (regs .x13 <<< 61 >>> 58 &&& 63#64).toNat &&& 255#64).toNat < 257 := by
    omega
  have eS := (word_ok (c := 257) hS1' (by omega) hS8 hnM hW1 hK').2.2
  rv_introT hI
  rv_symT hp stop [130, 174] with [hL] using [hpb]
  · exact (elt16_ok hP1' hP2 hP8 hnM hW1 (BitVec.lt_def.1 hc)).1
  · exact (elt16_ok hP1' hP2 hP8 hnM hW1 (BitVec.lt_def.1 hc)).2.1
  · exact (elt16_ok hP1' hP2 hP8 hnM hW1 (BitVec.lt_def.1 hc)).2.2.2.1
  · have := (elt16_ok hP1' hP2 hP8 hnM hW1 (BitVec.lt_def.1 hc)).2.2.2.2.1; omega
  all_goals
    have hC := BitVec.lt_def.1 hc_1
    obtain ⟨-, -, eA, -, hA8, eA8⟩ := elt16_ok hP1' hP2 hP8 hnM hW1 hC
    rw [setHalfword_eq hA8]
    obtain ⟨m1, m2, m3, m4, m5⟩ := store8 (a := P + MachineState.getMem M (S + (MachineState.getMem M (R .x9) >>>
      (regs .x13 <<< 61 >>> 58 &&& 63#64).toNat &&& 255#64) <<< 3) <<< 4) (v := MachineState.getMem M (R .x9))
      (by omega) hF hSt hcode hsl (by rw [eA]; omega) (by rw [eA]; omega)
    have nH := fun v => store8 (v := v) (by omega) m2 m3 m4 m1 (by rw [eA8]; omega) (by rw [eA8, m5]; omega)
    have k1 := hdr_keep hown (by omega) hnM (by rw [eA]; omega) (by rw [eA]; omega)
    have k10 := hdr_keep0 hown (by omega) hnM (by rw [eA]; omega) (by rw [eA]; omega)
    have k2 := hdr_keep hown (by omega) (by rw [m5]; exact hnM) (by rw [eA8]; omega) (by rw [eA8, m5]; omega)
    have k20 := hdr_keep0 hown (by omega) (by rw [m5]; exact hnM) (by rw [eA8]; omega) (by rw [eA8, m5]; omega)
    have nX := fun v w => store8 (v := w) (by omega) (nH v).2.1 (nH v).2.2.1 (nH v).2.2.2.1 (nH v).1
      (by rw [eS]; omega) (by rw [eS, (nH v).2.2.2.2, m5]; omega)
    have k3 := fun v => hdr_keep (M := (M.setMem (P + MachineState.getMem M (S + (MachineState.getMem M (R .x9) >>>
      (regs .x13 <<< 61 >>> 58 &&& 63#64).toNat &&& 255#64) <<< 3) <<< 4) (MachineState.getMem M (R .x9))).setMem
      (P + MachineState.getMem M (S + (MachineState.getMem M (R .x9) >>> (regs .x13 <<< 61 >>> 58 &&& 63#64).toNat
      &&& 255#64) <<< 3) <<< 4 + 8#64) v) hown (by omega) (by rw [(nH v).2.2.2.2, m5]; exact hnM) (by rw [eS]; omega)
      (by rw [eS, (nH v).2.2.2.2, m5]; omega)
    have k30 := fun v => hdr_keep0 (M := (M.setMem (P + MachineState.getMem M (S + (MachineState.getMem M (R .x9) >>>
      (regs .x13 <<< 61 >>> 58 &&& 63#64).toNat &&& 255#64) <<< 3) <<< 4) (MachineState.getMem M (R .x9))).setMem
      (P + MachineState.getMem M (S + (MachineState.getMem M (R .x9) >>> (regs .x13 <<< 61 >>> 58 &&& 63#64).toNat
      &&& 255#64) <<< 3) <<< 4 + 8#64) v) hown (by omega) (by rw [(nH v).2.2.2.2, m5]; exact hnM) (by rw [eS]; omega)
      (by rw [eS, (nH v).2.2.2.2, m5]; omega)
    have e9 : (R .x9 + 16#64).toNat = (R .x9).toNat + 16 := toNat_add_ofNat (by omega)
    have hs : (regs .x12 <<< 4).toNat = 16 * (regs .x12).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have e22 : (regs .x11 + regs .x12 <<< 4).toNat = (regs .x11).toNat + 16 * (regs .x12).toNat := by
      rw [BitVec.toNat_add, hs]; omega
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [e9, e22]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1,
      by rw [(nX _ _).2.2.2.2, (nH _).2.2.2.2, m5]; exact hS2, hS8, (nX _ _).1, (nX _ _).2.1, (nX _ _).2.2.1,
      (nX _ _).2.2.2.1⟩, rfl, rfl, hP1, by rw [(nX _ _).2.2.2.2, (nH _).2.2.2.2, m5]; exact hP2, hP8, ?_, ?_, ?_,
      j + 1, by omega, ?_⟩
    · rw [k30, k20, k10]; exact hh0
    · rw [k3 _ _ 8 (by omega), k2 _ 8 (by omega), k1 _ 8 (by omega)]; exact hh8
    · rw [k3 _ _ 16 (by omega), k2 _ 16 (by omega), k1 _ 16 (by omega)]; exact hh16
    · simp only [Tactic.rf]; rw [e9]; omega
  · -- past the last item
    have hn8 : (regs .x12).toNat * 16 < 2 ^ 63 := by omega
    refine exit hp hL hk (by omega) hW h16 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hS1,
      by rw [(nX _ _).2.2.2.2, (nH _).2.2.2.2, m5]; exact hS2, hS8, (nX _ _).1, (nX _ _).2.1, (nX _ _).2.2.1,
      (nX _ _).2.2.2.1⟩ fun r => post_ok hwin hal ?_ ?_ ?_
      (.inr ⟨hP1', hP1, by rw [(nX _ _).2.2.2.2, (nH _).2.2.2.2, m5]; omega, hP8⟩) hn8
    · rw [k30, k20, k10]; exact hh0
    · rw [k3 _ _ 8 (by omega), k2 _ 8 (by omega), k1 _ 8 (by omega)]; exact hh8
    · rw [k3 _ _ 16 (by omega), k2 _ 16 (by omega), k1 _ 16 (by omega)]; exact hh16

set_option rv_sym.heap true in
/-- **From instruction 100**: the sorted copy (`alloc`, `memcpy`) and the result's header, then the placing loop; or,
    with no items, the empty result. -/
theorem tail {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needM needP needH : Nat} (hn : 80 ≤ need) (hnA : 80 + needA ≤ need)
    (hnC : 80 + needM ≤ need) (hnP : 80 + needP ≤ need) (hnH : 80 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP) (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top S : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 16) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hB : BufT env m (regs .x12) (regs .x11) 16)
    (hown : env.Owned m top (regs .x10) 24) (hwin : InWin env (regs .x10) 24) (hal8 : (regs .x10).toNat % 8 = 0) :
    ∀ R M, (Common env m top ret S regs R M ∧ R .x9 = regs .x11 ∧ R .x21 = regs .x13) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 100, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hS1, hS2, hS8, hsl, hF, hSt, hcode⟩, -⟩ := id hI
  have hnM := hF.2.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  have hnm := hF.1
  have t80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := off rfl (by omega)
  have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by have := hown.2; omega)
  have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by have := hown.2; omega)
  have hs : (regs .x12 <<< 4).toNat = 16 * (regs .x12).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rcases hB with h | ⟨-, h2, -⟩
    · rw [h]
    · unfold Env.Live at h2; omega
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_introT hI
  rv_symT hp stop [130, 174] with [hL] using [hal', hcp, hpb, hhe]
  · -- no items: the empty result
    have hn0 : (regs .x12).toNat = 0 := by rw [hc]; rfl
    obtain ⟨s1, f1, st1, c1, nx1, r0, r8, r16⟩ := hdr3 (v0 := 0#64) (v1 := 8#64) (v2 := 0#64) (by omega) hown hwin
      (fun b hb => hb) hI_24 hI_25 hI_26 ⟨hI_15, hI_16, hI_17, hI_18, hI_19, hI_20, hI_21, hI_22, hI_23⟩
    exact exit hp hL hk (by omega) hW h16 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hI_12,
      by rw [nx1]; exact hI_13, hI_14, s1, f1, st1, c1⟩ fun r =>
      post_ok hwin hal8 (by rw [r0, hc]) r8 (by rw [r16, hc]) (.inl hn0) (by omega)
  all_goals
    have hn0 : (regs .x12).toNat ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq h)
    obtain ⟨a1, a2, a3⟩ : 0x10000000 ≤ (regs .x11).toNat ∧
        (regs .x11).toNat + (regs .x12).toNat * 16 ≤ (env.next m).toNat ∧ (regs .x11).toNat % 8 = 0 := by
      rcases hB with h | ⟨h1, h2, h3⟩
      · exact absurd h hn0
      · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
    have hn1 := hret1_14.1
    have hn2 := hret1_14.2.1
  · -- `memcpy`'s ranges
    rw [hs]
    refine .inr ⟨.inl ⟨by omega, by omega⟩, .inl (by omega), ?_, .inl (by omega)⟩
    rw [inWindow_iff]; omega
  · -- the placing loop from its first item
    have hF1 : env.Frame top (SretVecOut regs m) m m1 := Tactic.frame_callF hI_24 hret1_14 (by rw [t80]; omega)
    have hsl1 : Slots m1 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep1_1 a (BitVec.le_def.2 (by rw [t80]; omega)))
      ⟨hI_15, hI_16, hI_17, hI_18, hI_19, hI_20, hI_21, hI_22, hI_23⟩
    obtain ⟨s2, f2, st2, c2, nx2, r0, r8, r16⟩ := hdr3 (v0 := regs .x12) (v1 := r1 .x10) (v2 := 0#64) (by omega)
      hown hwin (fun b hb => hb) hF1 hret1_15 (hret1_19.trans hI_26) hsl1
    have hcout : ∀ b, CopyOut (updReg (Tactic.rf (r1 .x0) L.s3.hi (top + 18446744073709551536#64) (r1 .x3) (r1 .x4)
        (r1 .x5) (r1 .x6) (r1 .x7) (regs .x12) (regs .x11) (r1 .x10) (regs .x11) (regs .x12 <<< 4) (r1 .x13)
        (r1 .x14) (r1 .x15) (r1 .x16) (r1 .x17) S (regs .x10) (regs .x12 <<< 4) (r1 .x10)
        (regs .x11 + regs .x12 <<< 4) (regs .x13 <<< 61) (regs .x24) (regs .x25) (regs .x26) (regs .x27) (r1 .x28)
        (r1 .x29) (r1 .x30) (r1 .x31)) .x1 (L.base + 252#64))
        (((m1.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) (r1 .x10)).setMem (regs .x10 + 16#64) 0#64) b →
        (r1 .x10).toNat ≤ b.toNat ∧ b.toNat < (r1 .x10).toNat + 16 * (regs .x12).toNat :=
      fun b hb => copyOut_in (by exact rfl) (by exact hs) hret1_17 hb
    have hn3 := hret3_14.1
    rw [nx2] at hn3
    have hF3 : env.Frame top (SretVecOut regs m) m m3 := f2.trans hret3_14 (by rw [t80]; omega) fun b hb =>
      Or.inr (Or.inl ⟨by have := hcout b hb; omega, by have := hcout b hb; omega⟩)
    have hsl3 : Slots m3 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep3_1 a (BitVec.le_def.2 (by rw [t80]; omega)) fun hb => by
        have := hcout a hb; omega) s2
    have hk3 : ∀ a : Word, ((regs .x10).toNat ≤ a.toNat ∧ a.toNat < (regs .x10).toNat + 24) →
        MachineState.getMem m3 a = _ := fun a ha => keep3_2 a
      (by rw [nx2]; rcases hown.1 with h | h <;> [exact .inl (by omega); exact .inr (by rw [t80]; omega)])
      fun hb => by have := hcout a hb; rcases hown.1 with h | h <;> omega
    obtain ⟨s4, f4, st4, c4, nx4⟩ := out_store (v := regs .x12) (b := regs .x10 + 16#64) (by omega)
      ⟨by omega, by simp only [Layouts.Vec.byteSize]; omega⟩ (Runtime.MemsetT.InWin.sub hwin (by omega) (by omega))
      (by rcases hown.1 with h | h <;> omega) hF3 hret3_15 (by rw [hret3_19, c2]) hsl3
    have q0 : MachineState.getMem (MachineState.setMem m3 (regs .x10 + 16#64) (regs .x12)) (regs .x10) = regs .x12 := by
      rw [MachineState.getMem_setMem_ne (fun e => by have := congrArg BitVec.toNat e; omega), hk3 _ ⟨by omega, by omega⟩,
        r0]
    have q8 : MachineState.getMem (MachineState.setMem m3 (regs .x10 + 16#64) (regs .x12)) (regs .x10 + 8#64) =
        r1 .x10 := by
      rw [MachineState.getMem_setMem_ne (fun e => by have := congrArg BitVec.toNat e; omega),
        hk3 _ ⟨by omega, by omega⟩, r8]
    refine loop3 (S := S) (P := r1 .x10) hp hL hn hnP hpb hk hstop hstk hnx hW h16 ⟨a1, by omega, a3⟩ hown hwin hal8
      ((regs .x12).toNat - 1) _ _
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hI_12, by rw [nx4]; omega, hI_14, s4, f4, st4, c4⟩, rfl,
        rfl, by omega, by rw [nx4]; omega, hret1_17, q0, q8, MachineState.getMem_setMem_eq, 0, by omega, by simp only [Tactic.rf]; omega⟩

set_option rv_sym.heap true in
/-- **This `counting_sort` is total**, with 80 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needS needM needP needH : Nat} (hnA : 80 + needA ≤ need) (hnS : 80 + needS ≤ need)
    (hnC : 80 + needM ≤ need) (hnP : 80 + needP ≤ need) (hnH : 80 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hms : MemsetSafeT env p L.memset.idx needS)
    (hcp : MemcpySpecT env p L.memcpy.idx needM) (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [62, 88] with [hL] using [hal', hms, hhe]
  all_goals
    have hlay := env.layout
    rw [hpre_2] at hpre_6
    have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
    obtain ⟨hF0, hS0, hn0, hsl0, hc0⟩ := saved_ok (out := SretVecOut regs m) (ret := ret) (regs := regs) hlim hpre_5
      hpre_4
    simp only [saved] at hF0 hS0 hn0 hsl0 hc0
    have t80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := off rfl (by omega)
    have h2056 : (2056#64 : Word).toNat = 2056 := rfl
    rw [h2056] at hret1_18
    have hW1 := hpre_12.heapEnd_le
    have hge := hpre_12.next_ge
    have hn1 := hret1_14.1
    have hn2 := hret1_14.2.1
    have hF1 := Tactic.frame_callF hF0 hret1_14 (by rw [t80]; omega)
    have hsl1 : Slots m1 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep1_1 a (BitVec.le_def.2 (by rw [t80]; omega))) hsl0
    have hcout : ∀ b, CopyOut (updReg (Tactic.rf (r1 .x0) L.s1.hi (top + 18446744073709551536#64) (r1 .x3) (r1 .x4)
        (r1 .x5) (r1 .x6) (r1 .x7) (regs .x12) (regs .x11) (r1 .x10) (0#64) (2056#64) (r1 .x13) (r1 .x14) (r1 .x15)
        (r1 .x16) (r1 .x17) (r1 .x10) (regs .x10) (2056#64) (regs .x13) (regs .x22) (regs .x23) (regs .x24)
        (regs .x25) (regs .x26) (regs .x27) (r1 .x28) (r1 .x29) (r1 .x30) (r1 .x31)) .x1 (L.base + 100#64)) m1 b →
        (r1 .x10).toNat ≤ b.toNat ∧ b.toNat < (r1 .x10).toNat + 2056 :=
      fun b hb => copyOut_in (by exact rfl) (by exact h2056) hret1_17 hb
    have hn3 := hret3_14.1
    have hF3 := hF1.trans hret3_14 (by rw [t80]; omega) fun b hb =>
      Or.inr (Or.inl ⟨by have := hcout b hb; omega, by have := hcout b hb; omega⟩)
    have hsl3 : Slots m3 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep3_1 a (BitVec.le_def.2 (by rw [t80]; omega)) fun hb => by
        have := hcout a hb; omega) hsl1
    have hc3 := hret3_17.trans (hret1_19.trans hc0)
    have hB : BufT env m (regs .x12) (regs .x11) 16 := hpre_10
    have hown : env.Owned m top (regs .x10) 24 := ⟨hpre_6, hpre_7⟩
    have hfin := tail (S := r1 .x10) hp hL (by omega) hnA hnC hnP hnH hal hcp hpb hhe hk hstop hpre_3 hpre_5 hpre_12
      hpre_11 hB hown hpre_8 hpre_9
    have h2 := loop2 hp hL (by omega) hpre_3 hpre_12 hfin
    have hS2 : (r1 .x10).toNat + 2056 ≤ (env.next m3).toNat := by omega
  · -- no items: the prefix sums
    exact h2 255 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hret1_16, hS2, hret1_17, hsl3, hF3,
      hret3_15, hc3⟩, rfl, rfl, rfl, 0, rfl, by simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]⟩
  · -- the counting loop from its first item
    have hn0' : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    have hB' := hB.resolve_left hn0'
    unfold Env.Live at hB'
    exact loop1 hp hL (by omega) hpre_3 hpre_5 hpre_12 ⟨hB'.1, by omega, hB'.2.2⟩ (h2 255) ((regs .x12).toNat - 1) _ _
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hret1_16, hS2, hret1_17, hsl3, hF3, hret3_15, hc3⟩, rfl,
        rfl, rfl, 0, by omega, by simp only [Tactic.rf]; omega⟩

end Rv64mc.Proof.Bytecode.CountingSortPairsT

/-- info: 'Rv64mc.Proof.Bytecode.CountingSortPairsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Bytecode.CountingSortPairsT.total
