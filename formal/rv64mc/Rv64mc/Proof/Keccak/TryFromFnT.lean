/-
  Rv64mc.Proof.Keccak.TryFromFnT

  `core::array::try_from_fn` building `verify_layer`'s 25 lane weights (`std::array::from_fn(|lane| ...)` over
  `eq_lane`, a slice of `E` at `(a1, a2)`, and `beta` in `(a3, a4)`) is total: for each lane it checks the lane and
  the two shifted lanes against the slice's length (else `panic_bounds_check`), reads the three elements, multiplies
  twice by `beta` (`E::mul`) and stores the weight into an array in its frame; then it copies the 400 bytes to
  `sret` (`memcpy`). The run ends with the guest's abort (`AbortStop`) where a bounds check does. Safety only: it
  does not state the weights, and the shifted lanes' indices (computed by a multiply-high by a static data word) are
  read only through the code's own checks.

  The precondition: `sret` a caller's 400 bytes in a window, 8-byte aligned; the slice, unless empty, in a window
  and 8-byte aligned (a heap vector's buffer or a caller's stack array). At the image's one call site
  (`verify_layer`) `sret` is its frame's array at `sp + 0xa0` and the slice a vector's buffer (`SliceT.of_buf`).

  The proof: `rv_autoT` to the loop's head (instruction 50), `loop` (`Total.loop`, the lanes left as the measure,
  `LInv`), which also runs the copy and the return.

  ## Main definitions

  * `SliceT`, `PreT`, `OutT`, `SpecT`, `LInv`

  ## Main results

  * `total`, `SliceT.of_buf`
-/

import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.FromElemT
import Rv64mc.Proof.Runtime.VecReprT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Core.AbortStop
import Rv64mc.Gen.Tmpl.Core.Array.TryFromFnNeverShortCircuHc949fc7d

namespace Rv64mc.Proof.Keccak.TryFromFnT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.FromElemT (keep_store data0)
open Rv64mc.Gen.Core.Array.TryFromFnNeverShortCircuHc949fc7d (Link tmpl d_c8_e5d50e4a_words)

/-- A slice of `n` elements of `E` at `q`: none, or in a window and 8-byte aligned. -/
def SliceT (env : Env) (q : Word) (n : Nat) : Prop :=
  n = 0 ∨ (InWin env q (16 * n) ∧ q.toNat % 8 = 0)

/-- A vector's buffer holds a slice of its length. -/
theorem SliceT.of_buf {env : Env} {m : MachineState} {c q : Word} {n : Nat} (hb : BufT env m c q 16)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hn : n ≤ c.toNat) : SliceT env q n := by
  rcases hb with h0 | ⟨hge, hl, hal⟩
  · exact .inl (by omega)
  · unfold Env.Live at hl
    exact .inr ⟨.inl ⟨hge, by omega⟩, hal⟩

/-- The total precondition: `sret` a caller's 400 bytes, in a window, 8-byte aligned; the slice `(a1, a2)`
    `SliceT`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) 400 ∧ InWin env (regs .x10) 400 ∧ (regs .x10).toNat % 8 = 0 ∧
    SliceT env (regs .x11) (regs .x12).toNat

/-- What `try_from_fn` writes besides its stack: the array at `sret`. -/
def OutT (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) 400 b

/-- **The total contract of `try_from_fn` for `verify_layer`'s lane weights**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) OutT AbortStop

/-- The prologue's thirteen saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)).setMem (top + 18446744073709551536#64) (regs .x24)).setMem
    (top + 18446744073709551528#64) (regs .x25)).setMem (top + 18446744073709551520#64) (regs .x26)).setMem
    (top + 18446744073709551512#64) (regs .x27)

/-- The loop's head with `k + 1` lanes left: the lane `x22` below the slice's length or at it, the cursor `x25` 8
    bytes into the slice's element `x22` (when there is one), the array's cursor `x24` 8 bytes into the frame's
    element `x22`; the frame's four argument slots and its saved words kept. -/
def LInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551072#64 ∧ R .x8 = regs .x12 ∧
    (R .x22).toNat + (k + 1) = 25 ∧ (R .x22).toNat ≤ (regs .x12).toNat ∧
    (R .x24).toNat = top.toNat - 496 + 16 * (R .x22).toNat ∧
    ((R .x22).toNat < (regs .x12).toNat → (R .x25).toNat = (regs .x11).toNat + 8 + 16 * (R .x22).toNat) ∧
    M.getMem (top + 18446744073709551080#64) = regs .x10 ∧ M.getMem (top + 18446744073709551088#64) = regs .x11 ∧
    M.getMem (top + 18446744073709551096#64) = regs .x13 ∧ M.getMem (top + 18446744073709551104#64) = regs .x14 ∧
    (∀ a, top + 18446744073709551512#64 ≤ a → M.getMem a = (saved m top ret regs).getMem a) ∧
    env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

/-- Element `j` of a slice of `n > j` elements, as the code addresses it, in a window and aligned. -/
theorem elem_ok {env : Env} {top : Word} {m : MachineState} {q j : Word} {n : Nat} (hW : Windows env top m)
    (hs : SliceT env q n) (hj : j.toNat < n) :
    (inWindow (q + j <<< 4) 8 = true ∧ (q + j <<< 4).toNat % 8 = 0) ∧
      (inWindow (q + j <<< 4 + 8#64) 8 = true ∧ (q + j <<< 4 + 8#64).toNat % 8 = 0) := by
  rcases hs with h0 | ⟨hw, hal⟩
  · omega
  have hlt := hw.lt
  have hx : (q + j <<< 4).toNat = q.toNat + 16 * j.toNat := by
    rw [Runtime.WinT.elem_toNat (by omega)]; rfl
  refine ⟨hw.dword hW hal hx (by omega) (by omega), hw.dword hW hal (o := 16 * j.toNat + 8) ?_ (by omega)
    (by omega)⟩
  rw [toNat_add_ofNat (by omega), hx]; omega

/-- The slice's element at the cursor `x`, 8 bytes into element `j < n`, in a window and aligned. -/
theorem cur_ok {env : Env} {top : Word} {m : MachineState} {q x : Word} {j n : Nat} (hW : Windows env top m)
    (hs : SliceT env q n) (hj : j < n) (hx : x.toNat = q.toNat + 8 + 16 * j) :
    (inWindow (x + 18446744073709551608#64) 8 = true ∧ (x + 18446744073709551608#64).toNat % 8 = 0) ∧
      (inWindow x 8 = true ∧ x.toNat % 8 = 0) := by
  rcases hs with h0 | ⟨hw, hal⟩
  · omega
  have hlt := hw.lt
  have hx8 : (x + 18446744073709551608#64).toNat = q.toNat + 16 * j := by
    rw [Runtime.CloneT.toNat_add_neg (k := 8) rfl (by omega)]; omega
  exact ⟨hw.dword hW hal (o := 16 * j) hx8 (by omega) (by omega),
    hw.dword hW hal (o := 16 * j + 8) (by omega) (by omega) (by omega)⟩

/-- The two stores of a lane's weight, at the cursor `x` and 8 bytes below, keep every other word. -/
theorem get_store2 {N : MachineState} {x a v w : Word} (h8 : 8 ≤ x.toNat) (h1 : a.toNat ≠ x.toNat)
    (h2 : a.toNat ≠ x.toNat - 8) :
    ((N.setMem (x + 18446744073709551608#64) v).setMem x w).getMem a = N.getMem a := by
  rw [MachineState.getMem_setMem_ne (fun e => h1 (by rw [e])),
    MachineState.getMem_setMem_ne (fun e => h2 (by rw [e, Runtime.CloneT.toNat_add_neg (k := 8) rfl h8]))]

/-- **One lane's frame**: two calls from the frame's stack pointer and the weight's two stores into the array keep
    the frame (writing nothing a caller sees) and the saved words. -/
theorem step_ok {env : Env} {m M m1 m2 S : MachineState} {top x v w : Word} {j : Nat}
    (hstk : env.stackLimit.toNat + 544 ≤ top.toNat) (hx : x.toNat = top.toNat - 496 + 16 * j) (hj : j < 25)
    (hF : env.Frame top Tactic.F m M) (h1 : env.Frame (top + 18446744073709551072#64) Tactic.F M m1)
    (h2 : env.Frame (top + 18446744073709551072#64) Tactic.F m1 m2)
    (k1 : ∀ a, top + 18446744073709551072#64 ≤ a → m1.getMem a = M.getMem a)
    (k2 : ∀ a, top + 18446744073709551072#64 ≤ a → m2.getMem a = m1.getMem a)
    (hK : ∀ a, top + 18446744073709551512#64 ≤ a → M.getMem a = S.getMem a) :
    env.Frame top Tactic.F m ((m2.setMem (x + 18446744073709551608#64) v).setMem x w) ∧
      ∀ a, top + 18446744073709551512#64 ≤ a →
        ((m2.setMem (x + 18446744073709551608#64) v).setMem x w).getMem a = S.getMem a := by
  have s544 : (top + 18446744073709551072#64).toNat = top.toNat - 544 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have s104 : (top + 18446744073709551512#64).toNat = top.toNat - 104 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have h8 : (x + 18446744073709551608#64).toNat = x.toNat - 8 := Runtime.CloneT.toNat_add_neg (k := 8) rfl (by omega)
  refine ⟨Tactic.frame_store (Tactic.frame_store (Tactic.frame_call (Tactic.frame_call hF h1 (by omega)) h2
    (by omega)) (by omega) (by omega)) (by omega) (by omega), fun a ha => ?_⟩
  have hat := BitVec.le_def.1 ha
  rw [s104] at hat
  have hle : top + 18446744073709551072#64 ≤ a := BitVec.le_def.2 (by rw [s544]; omega)
  rw [get_store2 (by omega) (by omega) (by omega), k2 a hle, k1 a hle, hK a ha]

/-- The state at instruction 164, past the last lane: the frame's `sret` slot and saved words kept. -/
def TInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551072#64 ∧ M.getMem (top + 18446744073709551080#64) = regs .x10 ∧
    (∀ a, top + 18446744073709551512#64 ≤ a → M.getMem a = (saved m top ret regs).getMem a) ∧
    env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option rv_sym.heap true in
/-- **The copy to `sret` and the return**, from instruction 164. -/
theorem tail {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hn : 544 ≤ need) (hnC : 544 + needC ≤ need)
    (hcp : MemcpySpecT env p L.memcpy.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) 400) (hwin : InWin env (regs .x10) 400) (hal : (regs .x10).toNat % 8 = 0)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) :
    ∀ R M, TInv env m top ret regs R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 164, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hlay := env.layout
  obtain ⟨-, h80, -, hF, -, -⟩ := id hI
  rv_introT hI
  simp only [saved] at hI_3
  rv_symT hp with [hL, (by decide : (400#64).toNat = 400)] using [hcp]
  rw [h80]
  have hsp : (top + 18446744073709551072#64).toNat = top.toNat - 544 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have h112 : (top + 18446744073709551112#64).toNat = top.toNat - 504 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have := hW.top_le
  have := hW.nextAddr_ge
  have := hown.1
  unfold InWin at hwin
  simp only [OffStack, inWindow_iff, hsp, h112, show (400#64).toNat = 400 from rfl]
  refine Or.inr ⟨by omega, by omega, by omega, by omega⟩

/-- The state at instruction 98, past the three bounds checks: `LInv`'s, the lane below the slice's length and the
    two shifted lanes `x10`, `x11` too. -/
def BInv (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551072#64 ∧ R .x8 = regs .x12 ∧
    (R .x22).toNat + (k + 1) = 25 ∧ (R .x22).toNat < (regs .x12).toNat ∧
    (R .x24).toNat = top.toNat - 496 + 16 * (R .x22).toNat ∧
    (R .x25).toNat = (regs .x11).toNat + 8 + 16 * (R .x22).toNat ∧
    (R .x10).toNat < (regs .x12).toNat ∧ (R .x11).toNat < (regs .x12).toNat ∧
    M.getMem (top + 18446744073709551080#64) = regs .x10 ∧ M.getMem (top + 18446744073709551088#64) = regs .x11 ∧
    M.getMem (top + 18446744073709551096#64) = regs .x13 ∧ M.getMem (top + 18446744073709551104#64) = regs .x14 ∧
    (∀ a, top + 18446744073709551512#64 ≤ a → M.getMem a = (saved m top ret regs).getMem a) ∧
    env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

set_option maxHeartbeats 400000 in
set_option rv_sym.heap true in
/-- **The loads, products and stores of one lane**, from instruction 98; back to the head with a lane fewer, or past
    the last the copy and the return. -/
theorem body {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needC : Nat} (hn : 544 ≤ need) (hnM : 544 + needM ≤ need) (hnC : 544 + needC ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hcp : MemcpySpecT env p L.memcpy.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) 400) (hwin : InWin env (regs .x10) 400) (hal : (regs .x10).toNat % 8 = 0)
    (hsl : SliceT env (regs .x11) (regs .x12).toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    {k : Nat} (ih : ∀ R M, 0 < k → LInv env m top ret regs (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 50, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, BInv env m top ret regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 98, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hlay := env.layout
  obtain ⟨-, -, hk1, hlt, hx24, hx25, hj1, hj2, -, -, -, -, -, hF, -, -⟩ := id hI
  have hc1 := cur_ok hW hsl hlt hx25
  rv_introT hI
  simp only [saved] at hI_13
  rv_symT hp stop [50, 164] with [hL] using [hmul]
  · rw [hI_10]; exact (elem_ok hW hsl hj1).1.1
  · rw [hI_10]; exact (elem_ok hW hsl hj1).1.2
  · rw [hI_10]; exact (elem_ok hW hsl hj1).2.1
  · rw [hI_10]; exact (elem_ok hW hsl hj1).2.2
  · rw [hI_10]; exact (elem_ok hW hsl hj2).1.1
  · rw [hI_10]; exact (elem_ok hW hsl hj2).1.2
  · rw [hI_10]; exact (elem_ok hW hsl hj2).2.1
  · rw [hI_10]; exact (elem_ok hW hsl hj2).2.2
  · have hi1 : (R .x22 + 1#64).toNat = (R .x22).toNat + 1 := toNat_add_ofNat (by omega)
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by
      rw [hi1]; subst h0; simp only [BitVec.toNat_ofNat]; omega))
    clear hc
    refine ih _ _ hk0 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    all_goals try rv_closeT
    · exact (step_ok (by omega) hI_5 (by omega) hI_14 hret1_14 hret2_14 keep1_1 keep2_1 hI_13).2
    · exact (step_ok (by omega) hI_5 (by omega) hI_14 hret1_14 hret2_14 keep1_1 keep2_1 hI_13).1
  · refine tail hp hL hn hnC hcp hk hstk hnx hown hwin hal hW h16 _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    all_goals try rv_closeT
    · exact (step_ok (by omega) hI_5 (by omega) hI_14 hret1_14 hret2_14 keep1_1 keep2_1 hI_13).2
    · exact (step_ok (by omega) hI_5 (by omega) hI_14 hret1_14 hret2_14 keep1_1 keep2_1 hI_13).1

set_option rv_sym.heap true in
/-- **The loop**, from its head; past the last lane the array is copied to `sret` and the function returns. -/
theorem loop {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needM needP needC : Nat} (hn : 544 ≤ need) (hnM : 544 + needM ≤ need)
    (hnP : 544 + needP ≤ need) (hnC : 544 + needC ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    (hcp : MemcpySpecT env p L.memcpy.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) 400) (hwin : InWin env (regs .x10) 400) (hal : (regs .x10).toNat % 8 = 0)
    (hsl : SliceT env (regs .x11) (regs .x12).toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0) :
    ∀ k R M, LInv env m top ret regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 50, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env m top ret regs) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, hk1, hle, hx24, hx25, -, -, -, -, hK, hF, hS, hcode⟩ := id hI
  rv_introT hI
  simp only [saved] at hI_11
  rv_symT hp stop [98] with [hL] using [hpb]
  all_goals
    have hlt : (R .x22).toNat < (regs .x12).toNat :=
      Nat.lt_of_le_of_ne hle fun h => hc_1 (BitVec.eq_of_toNat_eq h.symm)
    refine body hp hL hn hnM hnC hmul hcp hk hstk hnx hown hwin hal hsl hW h16
      (fun R' M' hk0 hI' => ih (k - 1) R' M' (by omega) hI') _ _
      ⟨?_, ?_, ?_, hlt, ?_, hx25 hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    all_goals rv_closeT

set_option rv_sym.heap true in
/-- **`try_from_fn` for `verify_layer`'s lane weights is total**, with its 544-byte frame beyond its callees'
    stack. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hdata : DataRef.InData env [(L.d_c8_e5d50e4a, d_c8_e5d50e4a_words)])
    {need needM needP needC : Nat} (hnM : 544 + needM ≤ need) (hnP : 544 + needP ≤ need)
    (hnC : 544 + needC ≤ need) (hmul : Field.EMulT.specT env p L.mul.idx needM)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP) (hcp : MemcpySpecT env p L.memcpy.idx needC) :
    SpecT env p i need := by
  have hw := hdata.words (List.mem_singleton_self _)
  rv_autoT hp stop [50] with [hL, hw] using [hmul, hpb, hcp]
  · exact (data0 hpre_12 hdata Nat.one_pos).1
  · exact (data0 hpre_12 hdata Nat.one_pos).2
  refine loop hp hL (by omega) hnM hnP hnC hmul hpb hcp hk hstop hpre_3 hpre_5
    ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩ hpre_8 hpre_9 hpre_10 hpre_12 hpre_11 24 _ _
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [Tactic.rf]
  all_goals try rv_closeT
  · rw [Multilinear.slot_toNat (k := 496) (by decide) (by omega) (by decide), BitVec.toNat_ofNat]; omega
  · intro a ha
    have hat := BitVec.le_def.1 ha
    rw [Multilinear.slot_toNat (k := 104) (by decide) (by omega) (by decide)] at hat
    have hne : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 104 < k → k ≤ 544 → a ≠ top + c :=
      fun c k hc hk1 hk2 e => by rw [e, Runtime.CloneT.toNat_add_neg hc (by omega)] at hat; omega
    rw [MachineState.getMem_setMem_ne (hne _ 528 rfl (by omega) (by omega)),
      MachineState.getMem_setMem_ne (hne _ 536 rfl (by omega) (by omega)),
      MachineState.getMem_setMem_ne (hne _ 520 rfl (by omega) (by omega)),
      MachineState.getMem_setMem_ne (hne _ 512 rfl (by omega) (by omega))]
    rfl

end Rv64mc.Proof.Keccak.TryFromFnT

/-- info: 'Rv64mc.Proof.Keccak.TryFromFnT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Keccak.TryFromFnT.total
