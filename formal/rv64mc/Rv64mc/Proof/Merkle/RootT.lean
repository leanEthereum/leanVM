/-
  Rv64mc.Proof.Merkle.RootT

  `MerklePath::root` is total (`specT`): from the digest's slot (`out`, `a0`) owned by the caller and in a window,
  and the path (`a1`) owned, in a window and 8-byte aligned, its leaf's `K` words and its siblings' digests, unless
  there are none, allocated before (`Live`) and in windows, it returns, writing at most the slot's doublewords besides
  its stack and the leaf's byte buffer (`DigestOut`), or ends the run with `a0 = 2` (the allocator out of heap, in
  `hash_leaf`). Safety only: the digest is `keccak_hash`'s, whose functional contract is not total. One loop, over
  the siblings, by `Total.loop` with the siblings left as the measure.

  ## Main definitions

  * `PreT`, `specT`, `ExitInv`, `LInv`

  ## Main results

  * `slot_facts`, `slot_read`, `cnt_eq`, `exit_ok`, `loop`, `total`
-/

import Rv64mc.Proof.Merkle.HashLeafT
import Rv64mc.Proof.Merkle.HashPairT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Tactic.SymT
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Gen.Tmpl.Verifier.Merkle.MerklePath.Root

namespace Rv64mc.Proof.Merkle.RootT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Merkle.MerklePath.Root (Link tmpl)

/-- The total precondition: the slot owned and in a window; the path (`MerklePath`, 56 bytes) owned, in a window and
    8-byte aligned; its leaf's words (the vector at offset `0`) and its siblings' digests (the vector at `24`), unless
    there are none, allocated before and in windows. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Digest.byteSize ∧ InWin env (regs .x10) Layouts.Digest.byteSize ∧
  env.Owned m (regs .x2) (regs .x11) Layouts.MerklePath.byteSize ∧
    InWin env (regs .x11) Layouts.MerklePath.byteSize ∧ (regs .x11).toNat % 8 = 0 ∧
  ((m.getMem (regs .x11 + 16#64)).toNat = 0 ∨
    (env.Live m (m.getMem (regs .x11 + 8#64)) (8 * (m.getMem (regs .x11 + 16#64)).toNat) ∧
      InWin env (m.getMem (regs .x11 + 8#64)) (8 * (m.getMem (regs .x11 + 16#64)).toNat))) ∧
  ((m.getMem (regs .x11 + 40#64)).toNat = 0 ∨
    (env.Live m (m.getMem (regs .x11 + 32#64)) (32 * (m.getMem (regs .x11 + 40#64)).toNat) ∧
      InWin env (m.getMem (regs .x11 + 32#64)) (32 * (m.getMem (regs .x11 + 40#64)).toNat)))

/-- **The total contract of `MerklePath::root`**: it returns, writing at most the slot's doublewords, or ends the run
    with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) (fun regs _ => Spec.Hash.DigestOut (regs .x10))
    (Stop := AbortStop)

/-- The state at the copy of the digest to the slot (instruction 131): the stack pointer, the slot, the frame, the
    code, the static data, the saved registers' slots. -/
def ExitInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x10 ∧
    env.Frame top (Spec.Hash.DigestOut (regs .x10)) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27

set_option rv_sym.heap true in
/-- From the copy of the digest to the slot: `memcpy`, the return. -/
theorem exit_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hnC : 112 + needC ≤ need)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC) {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun regs _ => Spec.Hash.DigestOut (regs .x10)) ret top
      regs m r' m' → rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (ho : env.Owned m top (regs .x10) Layouts.Digest.byteSize) (hw : InWin env (regs .x10) Layouts.Digest.byteSize) :
    ∀ R M, ExitInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 262, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have := hW.top_le
  unfold InWin at hw
  rv_introT hinv
  rv_symT hp with [hL, (by omega : env.stackLimit.toNat + 112 ≤ top.toNat)] using [hcp]
  have hsp : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have := env.layout
  have := ho.1
  simp only [show (32#64).toNat = 32 from rfl, OffStack, hsp]
  simp only [Layouts.Digest.byteSize] at hw this
  exact Or.inr ⟨hw, by omega, hW.stack (by rw [hsp]; omega) (by rw [hsp]; omega), Or.inr (Nat.le_refl _)⟩

theorem cur_step (q : Word) (j : Nat) :
    q + BitVec.ofNat 64 (32 * j) + 32#64 = q + BitVec.ofNat 64 (32 * (j + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * j + 32 = 32 * (j + 1) by omega]

/-- The siblings' count as the code computes it from their length `s`, `((s << 5) - 32) >> 5 + 1`. -/
theorem cnt_eq {s : Word} (h0 : s.toNat ≠ 0) (h : 32 * s.toNat < 18446744073709551616) :
    (s <<< 5 + 18446744073709551584#64) >>> 5 + 1#64 = BitVec.ofNat 64 s.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 5 = 32 from rfl, show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
  omega

/-- A range in a window has fewer than `2^32` bytes. -/
theorem le_of_inWin {env : Env} {top q : Word} {n : Nat} {m : MachineState} (hW : Windows env top m)
    (h : InWin env q n) : n ≤ 0xc0000000 := by
  have := hW.heapEnd_le
  unfold InWin at h
  omega

theorem cnt_step (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) :=
  (BitVec.ofNat_add j 1).symm

/-- A word of the frame read after a call that keeps it and four stores at other offsets of the stack pointer. -/
theorem slot_read {top c d0 d1 d2 d3 v0 v1 v2 v3 : Word} {M m1 : MachineState} {P : Word → Prop}
    (hkeep : ∀ a, top + 18446744073709551504#64 ≤ a → ¬ P a → m1.getMem a = M.getMem a)
    (h0 : c ≠ d0) (h1 : c ≠ d1) (h2 : c ≠ d2) (h3 : c ≠ d3) (hle : top + 18446744073709551504#64 ≤ top + c)
    (hno : ¬ P (top + c)) :
    ((((m1.setMem (top + d0) v0).setMem (top + d1) v1).setMem (top + d2) v2).setMem (top + d3) v3).getMem
      (top + c) = M.getMem (top + c) := by
  rw [Transcript.getMem_setMem_off h3, Transcript.getMem_setMem_off h2, Transcript.getMem_setMem_off h1,
    Transcript.getMem_setMem_off h0]
  exact hkeep _ hle hno

/-- A saved register's slot (`c`, `k` bytes below the stack top) is at or above the stack pointer and misses a digest
    at `e`, `d` bytes below the stack top, that ends at or below it (`hash_leaf`'s at `sp`, `hash_pair`'s at
    `sp + 32`). -/
theorem slot_facts {top c e : Word} {k d : Nat} (hc : c.toNat + k = 18446744073709551616)
    (he : e.toNat + d = 18446744073709551616) (ht : 112 ≤ top.toNat) (hk8 : 8 ≤ k) (hkd : k + 32 ≤ d)
    (hd : d ≤ 112) (hd8 : d % 8 = 0) (hal : top.toNat % 16 = 0) :
    top + 18446744073709551504#64 ≤ top + c ∧ ¬ Spec.Hash.DigestOut (top + e) (top + c) := by
  have h1 : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h2 : (top + e).toNat = top.toNat - d := by
    rw [BitVec.toNat_add]; omega
  have h3 : (top + c).toNat = top.toNat - k := by
    rw [BitVec.toNat_add]; omega
  refine ⟨BitVec.le_def.2 (by rw [h1, h3]; omega), ?_⟩
  simp only [Spec.Hash.DigestOut, DwordsOf, InRange, toNat_alignToDword, Layouts.Digest.byteSize, h2, h3]
  omega

set_option hygiene false in
/-- A saved register's slot after `hash_leaf` (call 1; its `out` is the digest at `sp`), read through the prologue's
    stores. -/
local macro "slot_l" k:num c:term:max : tactic => `(tactic| (
  rw [keep1_1 _ (slot_facts (c := $c) (e := 18446744073709551504#64) (k := $k) (d := 112) (by decide) (by decide)
      h112 (by decide) (by decide) (by decide) (by decide) hpre_15).1
    (slot_facts (c := $c) (e := 18446744073709551504#64) (k := $k) (d := 112) (by decide) (by decide) h112
      (by decide) (by decide) (by decide) (by decide) hpre_15).2]
  simp (disch := decide) only [Transcript.getMem_setMem_off, MachineState.getMem_setMem_eq]))

set_option hygiene false in
/-- A saved register's slot after `hash_pair` (call 1; its `out` is the digest at `sp + 32`) and the four stores of
    the digest's words. -/
local macro "slot_p" k:num c:term:max h:ident : tactic => `(tactic| (
  exact (slot_read keep1_1 (by decide) (by decide) (by decide) (by decide)
    (slot_facts (c := $c) (e := 18446744073709551536#64) (k := $k) (d := 80) (by decide) (by decide) h112
      (by decide) (by decide) (by decide) (by decide) hal).1
    (slot_facts (c := $c) (e := 18446744073709551536#64) (k := $k) (d := 80) (by decide) (by decide) h112
      (by decide) (by decide) (by decide) (by decide) hal).2).trans $h))

set_option hygiene false in
/-- The three goals one pass leaves: the sibling's window for `hash_pair`, the copy (instruction 131), the head. -/
local macro "pass_tail" : tactic => `(tactic| (
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    first
      | exact (Runtime.MemsetT.InWin.sub hqw (by rw [hj]; omega)
          (by rw [hj]; simp only [Layouts.Digest.byteSize]; omega)).inWindow hW
      | exact hW.stack (by rw [hsp]; omega) (by rw [hsp]; simp only [Layouts.Digest.byteSize]; omega)
  · refine exit_ok env p i L hp hL hnC hcp hk hstk hal hW hnx ho hw _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_6 => slot_p 8 18446744073709551608#64 hI_10
    case refine_7 => slot_p 16 18446744073709551600#64 hI_11
    case refine_8 => slot_p 24 18446744073709551592#64 hI_12
    case refine_9 => slot_p 32 18446744073709551584#64 hI_13
    case refine_10 => slot_p 40 18446744073709551576#64 hI_14
    case refine_11 => slot_p 48 18446744073709551568#64 hI_15
    all_goals rv_closeT
  · have hk0 : k ≠ 0 := by
      intro h0
      apply hc
      rw [cnt_step, show n - (k + 1) + 1 = n by omega]
    refine ih (k - 1) _ _ (by omega) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    case refine_3 => rw [cur_step, show n - (k - 1 + 1) = n - (k + 1) + 1 by omega]
    case refine_4 => rw [cnt_step, show n - (k - 1 + 1) = n - (k + 1) + 1 by omega]
    case refine_6 => omega
    case refine_10 => slot_p 8 18446744073709551608#64 hI_10
    case refine_11 => slot_p 16 18446744073709551600#64 hI_11
    case refine_12 => slot_p 24 18446744073709551592#64 hI_12
    case refine_13 => slot_p 32 18446744073709551584#64 hI_13
    case refine_14 => slot_p 40 18446744073709551576#64 hI_14
    case refine_15 => slot_p 48 18446744073709551568#64 hI_15
    all_goals rv_closeT))

/-- The loop's head (instruction 124) with `k + 1` of the `n` siblings at `q` left: the cursor and the count, the
    frame, the code, the static data, the saved registers' slots. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (n k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x10 ∧
    R .x9 = q + BitVec.ofNat 64 (32 * (n - (k + 1))) ∧ R .x19 = BitVec.ofNat 64 (n - (k + 1)) ∧
    R .x20 = BitVec.ofNat 64 n ∧ k + 1 ≤ n ∧
    env.Frame top (Spec.Hash.DigestOut (regs .x10)) m M ∧ M.code = m.code ∧ env.Static M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27

/- Both paths of a pass (the sibling on either side), each through `hash_pair` and the digest's 32 byte loads, in one
   run: the default heartbeats do not cover it. -/
set_option maxHeartbeats 800000 in
set_option rv_sym.heap true in
/-- **The loop**, from its head: one sibling hashed in, then back to the head or to the copy. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needP needC : Nat} (hnP : 112 + needP ≤ need) (hnC : 112 + needC ≤ need)
    (hhp : HashPairT.specT env p L.hashPair.idx needP)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC) {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun regs _ => Spec.Hash.DigestOut (regs .x10)) ret top
      regs m r' m' → rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (ho : env.Owned m top (regs .x10) Layouts.Digest.byteSize) (hw : InWin env (regs .x10) Layouts.Digest.byteSize)
    {q : Word} {n : Nat} (hqn : q.toNat + 32 * n ≤ (env.next m).toNat) (hqw : InWin env q (32 * n)) :
    ∀ k R M, LInv env ret top regs m q n k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 248, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m q n) fun k R M hI ih => ?_
  obtain ⟨-, -, -, -, -, hkn, hF, -⟩ := id hI
  have hlay := env.layout
  have := hW.top_le
  have hqlt := hqw.lt
  have hj : (q + BitVec.ofNat 64 (32 * (n - (k + 1)))).toNat = q.toNat + 32 * (n - (k + 1)) :=
    toNat_add_ofNat (by omega)
  have hFn := hF.1
  have hsp : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h112 : 112 ≤ top.toNat := by omega
  rv_introT hI
  rv_symT hp stop [248, 262] with [hL, (by omega : env.stackLimit.toNat + 112 ≤ top.toNat)] using [hhp]
  · -- the sibling on the left
    rv_symT hp stop [248, 262] with [hL, (by omega : env.stackLimit.toNat + 112 ≤ top.toNat)] using [hhp]
    rv_symT hp stop [248, 262] with [hL, (by omega : env.stackLimit.toNat + 112 ≤ top.toNat)] using [hhp]
    pass_tail
  · -- the sibling on the right
    rv_symT hp stop [248, 262] with [hL, (by omega : env.stackLimit.toNat + 112 ≤ top.toNat)] using [hhp]
    pass_tail

set_option rv_sym.heap true in
/-- **`MerklePath::root` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needL needP needC : Nat} (hnL : 112 + needL ≤ need) (hnP : 112 + needP ≤ need)
    (hnC : 112 + needC ≤ need)
    (hhl : HashLeafT.specT env p L.hashLeaf.idx needL) (hhp : HashPairT.specT env p L.hashPair.idx needP)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needC) : specT env p i need := by
  rv_autoT hp stop [262, 248] with [hL] using [hhl, hhp, hcp]
  -- `omega` here would split the precondition's disjunctions: the bound by terms.
  all_goals have h112 : 112 ≤ top.toNat :=
    Nat.le_trans (Nat.le_add_right 112 needC) (Nat.le_trans hnC (Nat.le_trans (Nat.le_add_left need _) hpre_3))
  all_goals have ho : env.Owned m top (regs .x10) Layouts.Digest.byteSize := ⟨hpre_2 ▸ hpre_6, hpre_7⟩
  · -- no siblings
    refine exit_ok env p i L hp hL hnC hcp hk hpre_3 hpre_15 hpre_16 hpre_5 ho hpre_8 _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals clear hpre_6 hpre_8 hpre_9 hpre_11 hpre_13 hpre_14
    all_goals try simp only [Tactic.rf]
    case refine_6 => slot_l 8 18446744073709551608#64
    case refine_7 => slot_l 16 18446744073709551600#64
    case refine_8 => slot_l 24 18446744073709551592#64
    case refine_9 => slot_l 32 18446744073709551584#64
    case refine_10 => slot_l 40 18446744073709551576#64
    case refine_11 => slot_l 48 18446744073709551568#64
    all_goals rv_closeT
  · -- into the loop
    have hn0 : (m.getMem (regs .x11 + 40#64)).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hlv, hwn⟩ := hpre_14.resolve_left hn0
    have h32 := le_of_inWin hpre_16 hwn
    refine loop env p i L hp hL hnP hnC hhp hcp hk hpre_3 hpre_15 hpre_16 hpre_5 ho hpre_8 hlv hwn
      ((m.getMem (regs .x11 + 40#64)).toNat - 1) _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals clear hpre_6 hpre_8 hpre_9 hpre_11 hpre_13 hpre_14 hwn
    all_goals try simp only [Tactic.rf]
    case refine_3 =>
      rw [show (m.getMem (regs .x11 + 40#64)).toNat - ((m.getMem (regs .x11 + 40#64)).toNat - 1 + 1) = 0 by omega]
      simp
    case refine_4 =>
      rw [show (m.getMem (regs .x11 + 40#64)).toNat - ((m.getMem (regs .x11 + 40#64)).toNat - 1 + 1) = 0 by omega]
    case refine_5 => exact cnt_eq hn0 (by omega)
    case refine_6 => omega
    case refine_10 => slot_l 8 18446744073709551608#64
    case refine_11 => slot_l 16 18446744073709551600#64
    case refine_12 => slot_l 24 18446744073709551592#64
    case refine_13 => slot_l 32 18446744073709551584#64
    case refine_14 => slot_l 40 18446744073709551576#64
    case refine_15 => slot_l 48 18446744073709551568#64
    all_goals rv_closeT

end Rv64mc.Proof.Merkle.RootT

/-- info: 'Rv64mc.Proof.Merkle.RootT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Merkle.RootT.total
