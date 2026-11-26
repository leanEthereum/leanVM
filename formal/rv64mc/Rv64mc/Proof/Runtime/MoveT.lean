/-
  Rv64mc.Proof.Runtime.MoveT

  What the total proof of `compiler_builtins`' `memmove` (`MemmoveT.MemmoveSpecT`) shares between its forward and
  backward copies. `memmove` saves `s0` at `sp + 8` and keeps its scratch doubleword at `sp + 0` (`memcpy` at
  `sp + 8`), so the registers its body keeps leave `s0` out (`Regs`) and its invariants carry the saved word: `FInv`,
  `CopyT.Inv` with the first `j` bytes copied, and `BInv`, the bytes from `j` on copied (`InvB`).

  The forward copy, taken when `dst - src` (wrapping) is at least `n`, reads each source byte at or after the ones
  copied (`FxF.src`); the backward copy, from the end, each one before them (`FxB.src`). A store into the scratch
  doubleword keeps both invariants (`slot_copy16`).

  ## Main definitions

  * `Regs`, `Fx`, `FxF`, `FxB`, `FInv`, `InvB`, `BInv`, `Cont`

  ## Main results

  * `FInv.byte`, `FInv.word`, `FInv.slot`, `BInv.byte`, `BInv.word`, `BInv.slot`, `slot_copy16`, `ret_ok`
-/

import Rv64mc.Proof.Runtime.CopyT
import Rv64mc.Proof.Runtime.MemmoveT
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.CompilerBuiltins.Mem.Memmove

namespace Rv64mc.Proof.Runtime.MoveT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime.CopyT
open Rv64mc.Proof.Runtime.MemsetT (InWin Kept)
open Rv64mc.Gen.CompilerBuiltins.Mem.Memmove (Link tmpl)

/-- The registers the body keeps: the return address, the stack pointer 16 below `top`, the saved registers but `s0`
    and `dst`. -/
def Regs (ret top : Word) (regs r : Reg → Word) : Prop :=
  r .x1 = ret ∧ r .x2 = top + 0xfffffffffffffff0#64 ∧
    AbiRegs (top + 0xfffffffffffffff0#64) regs (updReg r .x8 (regs .x8)) ∧ r .x10 = regs .x10

theorem Regs.upd {ret top : Word} {regs r : Reg → Word} (h : Regs ret top regs r) {d : Reg}
    (hd : d ∈ [.x5, .x6, .x7, .x8, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29, .x30, .x31]) (v : Word) :
    Regs ret top regs (updReg r d v) := by
  obtain ⟨h1, h2, ha, h10⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  have hne : d ≠ .x1 ∧ d ≠ .x2 ∧ d ≠ .x10 := by
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  refine ⟨by simp [updReg_apply, Ne.symm hne.1, h1], by simp [updReg_apply, Ne.symm hne.2.1, h2], ?_,
    by simp [updReg_apply, Ne.symm hne.2.2, h10]⟩
  by_cases h8 : d = .x8
  · subst h8
    have : updReg (updReg r .x8 v) .x8 (regs .x8) = updReg r .x8 (regs .x8) := by
      funext x; simp only [updReg_apply]; split <;> rfl
    rwa [this]
  · have : updReg (updReg r d v) .x8 (regs .x8) = updReg (updReg r .x8 (regs .x8)) d v := by
      funext x; simp only [updReg_apply]
      by_cases hx8 : x = .x8 <;> by_cases hxd : x = d <;> simp_all
    rw [this]
    refine (AbiRegs.updReg_iff ?_).2 ha
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl h8 | decide

/-- What the entry gives every part of the body: `n` bytes, the windows, the stack slots. -/
structure Fx (env : Env) (top dst src : Word) (n : Nat) (m : MachineState) : Prop where
  win : Windows env top m
  room : env.stackLimit.toNat + 16 ≤ top.toNat
  al : top.toNat % 16 = 0
  dwin : InWin env dst n
  doff : OffStack env top dst n
  swin : inWindow src n = true
  soff : OffStack env top src n

/-- The forward copy's ranges: no destination byte is a source byte at or after it. -/
structure FxF (env : Env) (top dst src : Word) (n : Nat) (m : MachineState) : Prop extends Fx env top dst src n m where
  disj : ∀ k k', k ≤ k' → k' < n → dst.toNat + k ≠ src.toNat + k'

/-- The backward copy's ranges: no destination byte is a source byte before it. -/
structure FxB (env : Env) (top dst src : Word) (n : Nat) (m : MachineState) : Prop extends Fx env top dst src n m where
  disj : ∀ k k', k' < k → k < n → dst.toNat + k ≠ src.toNat + k'

variable {env : Env}

theorem toNat_top8 {top : Word} (h : 8 ≤ top.toNat) : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

/-- A store aligned for its width apart from the doubleword at `top - 8` keeps it. -/
theorem getMem_saved {top x v : Word} {w : Width} {M : MachineState} (htop : top.toNat % 8 = 0)
    (h16 : 16 ≤ top.toNat) (hal : x.toNat % w.bytes = 0)
    (hx : x.toNat + w.bytes ≤ top.toNat - 8 ∨ top.toNat ≤ x.toNat) :
    (Tactic.storeMem w M x v).getMem (top + 0xfffffffffffffff8#64) = M.getMem (top + 0xfffffffffffffff8#64) := by
  obtain ⟨v', hv⟩ := storeMem_eq_setMem w M v hal
  have hw : 0 < w.bytes ∧ w.bytes ≤ 8 := by cases w <;> decide
  rw [hv, MachineState.getMem_setMem_ne]
  intro h
  have := congrArg BitVec.toNat h
  rw [toNat_alignToDword, toNat_top8 (by omega)] at this
  omega

theorem toNat_dec {a : Word} (h : 0 < a.toNat) : (a + 0xffffffffffffffff#64).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

theorem extractByte_zext_getByte (M : MachineState) (x : Word) :
    extractByte ((M.getByte x).zeroExtend 64) 0 = bat M x.toNat := by
  rw [bat, ofNat_toNat']
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [extractByte, hi]

/-! ## The forward copy -/

/-- `CopyT.Inv`, `s0` saved at `top - 8`. -/
def FInv (env : Env) (top dst src : Word) (n : Nat) (s0 : Word) (m M : MachineState) (j : Nat) : Prop :=
  Inv env top dst src n m M j ∧ M.getMem (top + 0xfffffffffffffff8#64) = s0

theorem Fx.dn {top dst src : Word} {n : Nat} {m : MachineState} (F : Fx env top dst src n m) :
    dst.toNat + n < 2 ^ 64 := by
  have := env.heapEnd.isLt; have := F.dwin; unfold InWin at this; omega

theorem Fx.dtop {top dst src : Word} {n : Nat} {m : MachineState} (F : Fx env top dst src n m) {x : Nat}
    (h1 : dst.toNat ≤ x) (h2 : x < dst.toNat + n) : x + 1 ≤ top.toNat - 8 ∨ top.toNat ≤ x := by
  have h := F.doff; have := F.room; unfold OffStack at h; omega

theorem FInv.byte {top dst src x v s0 : Word} {n j : Nat} {m M : MachineState} (h : FInv env top dst src n s0 m M j)
    (F : Fx env top dst src n m) (hx : x.toNat = dst.toNat + j) (hjn : j < n)
    (hv : extractByte v 0 = bat m (src.toNat + j)) :
    FInv env top dst src n s0 m (Tactic.storeMem .b1 M x v) (j + 1) := by
  have := F.room; have := F.al
  refine ⟨h.1.byte F.dwin hx hjn hv, ?_⟩
  rw [getMem_saved (by omega) (by omega) (Nat.mod_one _) (F.dtop (x := x.toNat) (by omega) (by omega))]
  exact h.2

theorem FInv.word {top dst src x v s0 : Word} {n j : Nat} {m M : MachineState} (h : FInv env top dst src n s0 m M j)
    (F : Fx env top dst src n m) (hx : x.toNat = dst.toNat + j) (hal : x.toNat % 8 = 0) (hjn : j + 8 ≤ n)
    (hv : ∀ t, t < 8 → extractByte v t = bat m (src.toNat + j + t)) :
    FInv env top dst src n s0 m (Tactic.storeMem .b8 M x v) (j + 8) := by
  have := F.room; have := F.al; have := F.doff; unfold OffStack at this
  refine ⟨h.1.word F.dwin hx hal hjn hv, ?_⟩
  rw [getMem_saved (w := .b8) (by omega) (by omega) hal (by show _ + 8 ≤ _ ∨ _; omega)]
  exact h.2

/-- A store into the scratch doubleword keeps `FInv`. -/
theorem FInv.slot {top dst src x v s0 : Word} {n j : Nat} {w : Width} {m M : MachineState}
    (h : FInv env top dst src n s0 m M j) (F : Fx env top dst src n m) (hj : j ≤ n)
    (hx1 : top.toNat - 16 ≤ x.toNat) (hx2 : x.toNat + w.bytes ≤ top.toNat - 8) (hal : x.toNat % w.bytes = 0) :
    FInv env top dst src n s0 m (Tactic.storeMem w M x v) j := by
  have := F.room; have := F.al
  refine ⟨h.1.slot F.doff hj F.dn F.room (by omega) hx1 (by omega) hal, ?_⟩
  rw [getMem_saved (by omega) (by omega) hal (.inl hx2)]
  exact h.2

/-- **The start**: nothing copied, `s0` saved at `top - 8`. -/
theorem FInv.start {top dst src s0 : Word} {n : Nat} {m : MachineState} (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hroom : env.stackLimit.toNat + 16 ≤ top.toNat)
    (hal : top.toNat % 16 = 0) :
    FInv env top dst src n s0 m (Tactic.storeMem .b8 m (top + 0xfffffffffffffff8#64) s0) 0 := by
  have h8 := toNat_top8 (top := top) (by omega)
  have hb8 : Width.b8.bytes = 8 := rfl
  have htl := top.isLt
  refine ⟨⟨Kept.slot ⟨Env.Frame.refl hnx, hst, rfl⟩ hroom (by omega) (by omega) (by rw [h8, hb8]; omega)
    (by omega), fun _ h => absurd h (Nat.not_lt_zero _), fun b hb _ hs => ?_⟩, ?_⟩
  · rw [bat_storeMem (by rw [h8, hb8]; omega) hb, ite_eq_right (by rw [h8, hb8]; omega)]
  · exact MachineState.getMem_setMem_eq

/-- A source byte at or after the copied ones reads as at entry while the forward copy runs. -/
theorem FxF.src {top dst src s0 : Word} {n j a : Nat} {m M : MachineState} (F : FxF env top dst src n m)
    (hI : FInv env top dst src n s0 m M j) (hj : j ≤ n) (ha : src.toNat + j ≤ a) (hn : a < src.toNat + n) :
    bat M a = bat m a := by
  have hsw := inWindow_iff.1 F.swin
  have hs := F.soff
  unfold OffStack at hs
  have := hI.1.src (k := a - src.toNat) (by omega)
    (fun ⟨h1, h2⟩ => F.disj (a - dst.toNat) (a - src.toNat) (by omega) (by omega) (by omega)) (by omega)
  rwa [Nat.add_sub_cancel' (by omega : src.toNat ≤ a)] at this

/-! ## The backward copy -/

/-- **The backward copy so far**: the bytes from `j` on of `[src, src + n)` copied to `[dst, dst + n)`, every byte
    outside the copied ones and apart from the stack below `top` kept, and `Kept`. -/
def InvB (env : Env) (top dst src : Word) (n : Nat) (m M : MachineState) (j : Nat) : Prop :=
  Kept env top dst n m M ∧ (∀ k, j ≤ k → k < n → bat M (dst.toNat + k) = bat m (src.toNat + k)) ∧
    ∀ b, b < 2 ^ 64 → ¬ (dst.toNat + j ≤ b ∧ b < dst.toNat + n) → (b < env.stackLimit.toNat ∨ top.toNat ≤ b) →
      bat M b = bat m b

/-- `InvB`, `s0` saved at `top - 8`. -/
def BInv (env : Env) (top dst src : Word) (n : Nat) (s0 : Word) (m M : MachineState) (j : Nat) : Prop :=
  InvB env top dst src n m M j ∧ M.getMem (top + 0xfffffffffffffff8#64) = s0

/-- Nothing copied, forward or backward. -/
theorem FInv.toB {top dst src s0 : Word} {n : Nat} {m M : MachineState} (h : FInv env top dst src n s0 m M 0) :
    BInv env top dst src n s0 m M n :=
  ⟨⟨h.1.1, fun _ h1 h2 => absurd h2 (by omega), fun b hb _ hs => h.1.2.2 b hb (by omega) hs⟩, h.2⟩

/-- Everything copied, backward or forward. -/
theorem BInv.toF {top dst src s0 : Word} {n : Nat} {m M : MachineState} (h : BInv env top dst src n s0 m M 0) :
    FInv env top dst src n s0 m M n :=
  ⟨⟨h.1.1, fun k hk => by simpa using h.1.2.1 k (Nat.zero_le _) hk,
    fun b hb hn hs => h.1.2.2 b hb (by simpa using hn) hs⟩,
    h.2⟩

theorem BInv.byte {top dst src x v s0 : Word} {n j : Nat} {m M : MachineState}
    (h : BInv env top dst src n s0 m M (j + 1)) (F : Fx env top dst src n m) (hx : x.toNat = dst.toNat + j)
    (hjn : j < n) (hv : extractByte v 0 = bat m (src.toNat + j)) :
    BInv env top dst src n s0 m (Tactic.storeMem .b1 M x v) j := by
  have := F.room; have := F.al
  have h1 : x.toNat % Width.b1.bytes = 0 := Nat.mod_one _
  have hwb : Width.b1.bytes = 1 := rfl
  have hdn := F.dn
  refine ⟨⟨Kept.setByte h.1.1 F.dwin (by omega) (by omega) _, fun k hk1 hk => ?_, fun b hb hn hs => ?_⟩, ?_⟩
  · rw [bat_storeMem h1 (by omega)]
    by_cases hkj : k = j
    · rw [ite_eq_left (by omega), show dst.toNat + k - x.toNat = 0 by omega, hv, hkj]
    · rw [ite_eq_right (by omega)]; exact h.1.2.1 k (by omega) hk
  · rw [bat_storeMem h1 hb, ite_eq_right (by omega)]
    exact h.1.2.2 b hb (by omega) hs
  · rw [show Tactic.storeMem .b1 M x v = Tactic.storeMem .b1 M x v from rfl,
      getMem_saved (by omega) (by omega) (Nat.mod_one _) (F.dtop (x := x.toNat) (by omega) (by omega))]
    exact h.2

theorem BInv.word {top dst src x v s0 : Word} {n j : Nat} {m M : MachineState}
    (h : BInv env top dst src n s0 m M (j + 8)) (F : Fx env top dst src n m) (hx : x.toNat = dst.toNat + j)
    (hal : x.toNat % 8 = 0) (hjn : j + 8 ≤ n) (hv : ∀ t, t < 8 → extractByte v t = bat m (src.toNat + j + t)) :
    BInv env top dst src n s0 m (Tactic.storeMem .b8 M x v) j := by
  have := F.room; have := F.al; have := F.doff; unfold OffStack at this
  have h1 : x.toNat % Width.b8.bytes = 0 := hal
  have hwb : Width.b8.bytes = 8 := rfl
  have hdn := F.dn
  refine ⟨⟨Kept.setMem h.1.1 F.dwin hal (by omega) (by omega) _, fun k hk1 hk => ?_, fun b hb hn hs => ?_⟩, ?_⟩
  · rw [bat_storeMem h1 (by omega)]
    by_cases hkj : k < j + 8
    · rw [ite_eq_left (by omega), hv _ (by omega)]; congr 1; omega
    · rw [ite_eq_right (by omega)]; exact h.1.2.1 k (by omega) hk
  · rw [bat_storeMem h1 hb, ite_eq_right (by omega)]
    exact h.1.2.2 b hb (by omega) hs
  · rw [getMem_saved (w := .b8) (by omega) (by omega) hal (by show _ + 8 ≤ _ ∨ _; omega)]
    exact h.2

/-- A store into the scratch doubleword keeps `BInv`. -/
theorem BInv.slot {top dst src x v s0 : Word} {n j : Nat} {w : Width} {m M : MachineState}
    (h : BInv env top dst src n s0 m M j) (F : Fx env top dst src n m)
    (hx1 : top.toNat - 16 ≤ x.toNat) (hx2 : x.toNat + w.bytes ≤ top.toNat - 8) (hal : x.toNat % w.bytes = 0) :
    BInv env top dst src n s0 m (Tactic.storeMem w M x v) j := by
  have := F.room; have := F.al; have hdoff := F.doff; unfold OffStack at hdoff
  have htl := top.isLt
  refine ⟨⟨Kept.slot h.1.1 F.room hx1 (by omega) hal (by omega), fun k hk1 hk => ?_, fun b hb h1 h2 => ?_⟩, ?_⟩
  · rw [bat_storeMem hal (by have := F.dn; omega), ite_eq_right (by omega)]
    exact h.1.2.1 k hk1 hk
  · rw [bat_storeMem hal hb, ite_eq_right (by omega)]
    exact h.1.2.2 b hb h1 h2
  · rw [getMem_saved (by omega) (by omega) hal (.inl hx2)]
    exact h.2

/-- A source byte before the copied ones reads as at entry while the backward copy runs. -/
theorem FxB.src {top dst src s0 : Word} {n j a : Nat} {m M : MachineState} (F : FxB env top dst src n m)
    (hI : BInv env top dst src n s0 m M j) (hj : j ≤ n) (ha : src.toNat ≤ a) (hn : a < src.toNat + j) :
    bat M a = bat m a := by
  have hsw := inWindow_iff.1 F.swin
  have hs := F.soff
  unfold OffStack at hs
  exact hI.1.2.2 a (by omega)
    (fun ⟨h1, h2⟩ => F.disj (a - dst.toNat) (a - src.toNat) (by omega) (by omega) (by omega)) (by omega)

/-! ## The scratch doubleword -/

/-- **A narrow copy into the scratch doubleword**: `w` bytes of the source at `i` into byte `i` of the doubleword at
    `top - 16`, bytes `lo` to `i` already copied, keeps any invariant that such stores keep and copies bytes `lo` to
    `i + w`. -/
theorem slot_copy16 {P : MachineState → Prop} {top X v : Word} {lo i B : Nat} {w : Width} {m M : MachineState}
    (hP : ∀ M', P M' → P (Tactic.storeMem w M' X v)) (hI : P M) (htop : 16 ≤ top.toNat)
    (hS : ∀ t, lo ≤ t → t < i → bat M (top.toNat - 16 + t) = bat m (B + t)) (hX : X.toNat = top.toNat - 16 + i)
    (hal : X.toNat % w.bytes = 0) (hiw : i + w.bytes ≤ 8)
    (hv : ∀ u, u < w.bytes → extractByte v u = bat m (B + i + u)) :
    P (Tactic.storeMem w M X v) ∧
      ∀ t, lo ≤ t → t < i + w.bytes → bat (Tactic.storeMem w M X v) (top.toNat - 16 + t) = bat m (B + t) := by
  have htl := top.isLt
  refine ⟨hP M hI, fun t ht0 ht => ?_⟩
  rw [bat_storeMem hal (by omega)]
  by_cases hti : i ≤ t
  · rw [ite_eq_left (by omega), hv _ (by omega)]; congr 1; omega
  · rw [ite_eq_right (by omega)]; exact hS t ht0 (by omega)

/-! ## The return -/

variable {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {Q : State rvIsa → Prop} {ret top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState}

/-- The continuation a part of the body is proved against: the contract's, at the return. -/
abbrev Cont (env : Env) (p : Lprog (Op Reg) Reg) (Q : State rvIsa → Prop) (ret top : Word) (rest : List Frame)
    (regs : Reg → Word) (m : MachineState) : Prop :=
  ∀ r' m', HoldsT.post env (CopyPostT env) CopyOut ret top regs m r' m' →
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩

theorem ofNat_add_toNat (a : Word) (k : Nat) : BitVec.ofNat 64 (a.toNat + k) = a + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-- The return, with every byte copied: `s0` restored from its slot. -/
theorem ret_ok' (hp : p[i]? = some (tmpl L)) (hW : Windows env top m)
    (hroom : env.stackLimit.toNat + 16 ≤ top.toNat) (hal : top.toNat % 16 = 0)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top)
    {r : Reg → Word} {M : MachineState} (hR : Regs ret top regs r)
    (hI : FInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (regs .x12).toNat) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 450, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h1, hx2, ha, h10⟩ := hR
  have h8 : r .x2 + 8#64 = top + 0xfffffffffffffff8#64 := by
    rw [hx2, BitVec.add_assoc]; rfl
  have hx2' : r .x2 + 16#64 = top := by
    rw [hx2, BitVec.add_assoc, show (0xfffffffffffffff0#64 + 16#64 : Word) = 0#64 by decide, BitVec.add_zero]
  rv_symT hp with [h1, hx2]
  rw [h8, hI.2, hx2']
  refine hk _ _ ⟨⟨?_, hI.1.1.1, hI.1.1.2.1, by simpa [updReg_apply] using h10, fun k hk' => ?_, fun b hb hs => ?_⟩,
    hI.1.1.2.2⟩
  · unfold AbiRegs at ha ⊢
    simp only [updReg_apply, reduceCtorEq, ↓reduceIte] at ha ⊢
    exact ⟨trivial, ha.2⟩
  · have := hI.1.2.1 k hk'
    simpa only [bat, ofNat_add_toNat] using this
  · have := hI.1.2.2 b.toNat b.isLt (by unfold InRange at hb; omega) (by unfold OffStack at hs; rw [hsp] at hs; omega)
    simpa only [bat, ofNat_toNat'] using this

/-- `ret_ok'` with the windows from `Fx`. -/
theorem ret_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top)
    {r : Reg → Word} {M : MachineState} (hR : Regs ret top regs r)
    (hI : FInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (regs .x12).toNat) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 450, ret, top⟩ :: rest, r, M⟩ :=
  ret_ok' hp F.win F.room F.al hk hsp hR hI

end Rv64mc.Proof.Runtime.MoveT
