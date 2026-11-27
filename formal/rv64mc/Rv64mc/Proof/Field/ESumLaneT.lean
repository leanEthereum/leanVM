/-
  Rv64mc.Proof.Field.ESumLaneT

  `E::sum` over `claim.weights.chunks(64).zip(&eq_lane).map(|(lane, &e)| e * dot(&eq_z, lane))` (`verify_layer`'s
  bit-position sum, index 27) is total (`SumSafeT`): passed the iterator by reference (the chunks' slice `v` and
  size `c`, the `eq_lane` slice's pointer, the zip's index and length, the closure's reference to `eq_z`'s header),
  it returns, writing nothing of its caller's, or ends the run with `a0 = 2` where `dot` does (slices of different
  lengths). The precondition (`SumPreT`): the iterator's eight words 8-byte aligned, in a window and the caller's
  (`Owned`), the zip's index `0` (as `verify_layer` builds it); unless the zip is empty, its `n` pairs fit (`c (n - 1)`
  below `v`'s length, so every chunk is nonempty), `v` and `eq_lane`'s first `n` elements in windows, 8-byte aligned,
  `v` the caller's; `eq_z`'s header 8-byte aligned, in a window and the caller's, `eq_z` the caller's and, unless
  empty, in a window and 8-byte aligned. The sum is not stated: no caller's safety reads it.

  `dot` is stepped through `DotOwnT`'s contract at the elements its slices hold, of either length (`dotAny`: as
  `DotSafeT.dotSafe`, without its equal lengths), `E::mul` through its total contract with its postcondition dropped
  (`KInvT.dropPost`). The loop is `Total.loop` with the pairs left as the measure; the thirteen saved registers' slots
  are `SavedT.MemOk`.

  ## Main definitions

  * `PreD`, `SumPreT`, `SumSafeT`, `Mem`, `LInv`

  ## Main results

  * `dotAny`, `owned_mono`, `call_back`, `loop_ok`, `total`
-/

import Rv64mc.Proof.Field.ESumFormT
import Rv64mc.Proof.Field.KInvT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Multilinear.DotSafeT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Core.AbortStop
import Rv64mc.Gen.Tmpl.Verifier.Field.E.SumMapZipChunksEIterEVerifyLayerClosure3

namespace Rv64mc.Proof.Field.ESumLaneT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Field.KInvT (dropPost)
open Rv64mc.Proof.Field.ESumFormT (kept)
open Rv64mc.Proof.Multilinear.DotSafeT (elemsAt elemsAt_length sliceArgs_elemsAt)
open Rv64mc.Gen.Verifier.Field.E.SumMapZipChunksEIterEVerifyLayerClosure3 (Link tmpl)

/-- `dot`'s slices without their elements, of any lengths: each owned by the caller and, unless empty, in a window
    and 8-byte aligned. -/
def PreD (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) (16 * (regs .x11).toNat) ∧
    env.Owned m (regs .x2) (regs .x12) (16 * (regs .x13).toNat) ∧
    ((regs .x11).toNat = 0 ∨ InWin env (regs .x10) (16 * (regs .x11).toNat) ∧ (regs .x10).toNat % 8 = 0) ∧
    ((regs .x13).toNat = 0 ∨ InWin env (regs .x12) (16 * (regs .x13).toNat) ∧ (regs .x12).toNat % 8 = 0)

/-- **`dot`'s safety at slices of any lengths**: `DotOwnT.specT` at the elements its slices hold. -/
theorem dotAny {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : DotOwnT.specT env p i need) :
    HoldsT env p i need (PreD env) (fun _ _ _ _ => True) (Stop := AbortStop) :=
  fun Q ret top rest regs m ⟨⟨he, hs, hst, hn, ⟨hox, hoy, hwx, hwy⟩, hal⟩, hW⟩ hstop hk =>
    h (elemsAt m (regs .x10) (regs .x11).toNat) (elemsAt m (regs .x12) (regs .x13).toNat) Q ret top rest regs m
      ⟨⟨he, hs, hst, hn, ⟨sliceArgs_elemsAt hox.2, sliceArgs_elemsAt hoy.2,
        by simpa [elemsAt_length, Layouts.E.byteSize] using hox,
        by simpa [elemsAt_length, Layouts.E.byteSize] using hoy,
        by rw [elemsAt_length]; exact hwx, by rw [elemsAt_length]; exact hwy⟩, hal⟩, hW⟩ hstop
      fun r' m' ⟨⟨ha', hf, hs', _⟩, hc⟩ => hk r' m' ⟨⟨ha', hf, hs', trivial⟩, hc⟩

/-- The zip at `q`: unless its length `n` (`+ 48`) is `0`, the chunks' size (`+ 16`) times `n - 1` below `v`'s
    length (`+ 8`), `v` (`+ 0`) in a window, 8-byte aligned and the caller's (`Owned` at `top`), `eq_lane`'s first
    `n` elements (`+ 24`) in a window and 8-byte aligned. -/
def ZipW (env : Env) (m : MachineState) (top q : Word) : Prop :=
  (m.getMem (q + 48#64)).toNat = 0 ∨
    (m.getMem (q + 16#64)).toNat * ((m.getMem (q + 48#64)).toNat - 1) < (m.getMem (q + 8#64)).toNat ∧
      InWin env (m.getMem q) (16 * (m.getMem (q + 8#64)).toNat) ∧ (m.getMem q).toNat % 8 = 0 ∧
      env.Owned m top (m.getMem q) (16 * (m.getMem (q + 8#64)).toNat) ∧
      InWin env (m.getMem (q + 24#64)) (16 * (m.getMem (q + 48#64)).toNat) ∧ (m.getMem (q + 24#64)).toNat % 8 = 0

/-- The `Vec<E>` whose header is at `h`: its elements the caller's and, unless none, in a window and 8-byte
    aligned. -/
def VecW (env : Env) (m : MachineState) (top h : Word) : Prop :=
  env.Owned m top (m.getMem (h + 8#64)) (16 * (m.getMem (h + 16#64)).toNat) ∧
    ((m.getMem (h + 16#64)).toNat = 0 ∨
      InWin env (m.getMem (h + 8#64)) (16 * (m.getMem (h + 16#64)).toNat) ∧ (m.getMem (h + 8#64)).toNat % 8 = 0)

/-- The total precondition: the iterator at `x10` (`64` bytes) 8-byte aligned, in a window and the caller's; the
    zip's index (`+ 40`) `0`, the zip `ZipW`; `eq_z`'s header (`+ 56`) 8-byte aligned, in a window and the caller's,
    `eq_z` a `VecW`. -/
def SumPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ InWin env (regs .x10) 64 ∧ env.Owned m (regs .x2) (regs .x10) 64 ∧
    m.getMem (regs .x10 + 40#64) = 0#64 ∧ ZipW env m (regs .x2) (regs .x10) ∧
    (m.getMem (regs .x10 + 56#64)).toNat % 8 = 0 ∧ InWin env (m.getMem (regs .x10 + 56#64)) 24 ∧
    env.Owned m (regs .x2) (m.getMem (regs .x10 + 56#64)) 24 ∧ VecW env m (regs .x2) (m.getMem (regs .x10 + 56#64))

/-- **The total contract**: it returns, writing nothing of its caller's, or ends the run with `a0 = 2`. It does not
    state the sum. -/
def SumSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (SumPreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

/-- What the loop keeps of memory: `SavedT.MemOk` with the thirteen saved registers' slots, from `top - 8` (the
    return address) down to `top - 104` (`s11`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (fun _ => False)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64, 18446744073709551528#64, 18446744073709551520#64,
      18446744073709551512#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20, regs .x21, regs .x22, regs .x23, regs .x24,
      regs .x25, regs .x26, regs .x27] m M

/-- The saved slots lie in the `104` bytes below `top`. -/
theorem slots : SlotsIn 104
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64, 18446744073709551528#64, 18446744073709551520#64,
      18446744073709551512#64] :=
  slots_le

/-- **`Mem` across a callee** writing nothing of the caller's, from the stack pointer `top - 112`. -/
theorem call_back {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState}
    (hf : env.Frame (top + 18446744073709551504#64) (fun _ => False) M X)
    (hk : ∀ a : Word, top + 18446744073709551504#64 ≤ a → X.getMem a = M.getMem a) (hc : X.code = M.code)
    (hs : env.Static X) (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hM : Mem env ret top regs m M) :
    Mem env ret top regs m X :=
  (hM.call_below slots (by omega) hlim (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hf hk hc hs).1

/-- A range the caller owned at the entry it still owns, from a lower stack pointer and `NEXT` not lowered. -/
theorem owned_mono {env : Env} {m M : MachineState} {top sp a : Word} {n : Nat} (h : env.Owned m top a n)
    (hn : (env.next m).toNat ≤ (env.next M).toNat) (hsp : sp.toNat ≤ top.toNat) : env.Owned M sp a n :=
  ⟨h.1.imp (fun h => by omega) fun h => by omega, h.2⟩

/-- The loop's head (instruction 75), `k` of the `n` pairs left (`j = n - k` done): the stack pointer, `eq_z` at
    `x18`, `x19`, the chunks' size `x23` and stride `x27`, the pairs left `x24`, the chunk's pointer `x20` and `v`'s
    elements from it `x26`, `eq_lane`'s cursor `x25` (`8` past the next element), `Mem`. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (vp bp c zp zl : Word) (vl n k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x18 = zp ∧ R .x19 = zl ∧ R .x23 = c ∧ R .x27 = c <<< 4 ∧
    (R .x24).toNat = k ∧ 1 ≤ k ∧ k ≤ n ∧ (R .x20).toNat = vp.toNat + 16 * (c.toNat * (n - k)) ∧
    (R .x26).toNat = vl - c.toNat * (n - k) ∧ (R .x25).toNat = bp.toNat + 16 * (n - k) + 8 ∧
    Mem env ret top regs m M

set_option rv_sym.heap true in
/-- **The return** (instruction 19): the saved registers restored from their slots. -/
theorem ret_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m) :
    ∀ R M, R .x2 = top + 18446744073709551504#64 → Mem env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 38, ret, top⟩ :: rest, R, M⟩ := by
  intro R M h2 hM
  have hI : R .x2 = top + 18446744073709551504#64 ∧ Mem env ret top regs m M := ⟨h2, hM⟩
  rv_introT hI
  rv_symT hp with [hlim]

set_option rv_sym.heap true in
/-- **The loop**, from its head: the chunk's length (`min` of `v`'s elements left and the size), the next `eq_lane`
    element, `dot(eq_z, chunk)` and the product, then back to the head (one pair fewer) or the return. -/
theorem loop_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needD needU : Nat} (hnD : 112 + needD ≤ need) (hnU : 112 + needU ≤ need)
    (hdot : DotOwnT.specT env p L.dot.idx needD) (hmul : Field.EMulT.specT env p L.mul.idx needU)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {vp bp c zp zl : Word} {vl n : Nat} (hcn : c.toNat * (n - 1) < vl) (hwv : InWin env vp (16 * vl))
    (hav : vp.toNat % 8 = 0) (hov : env.Owned m top vp (16 * vl)) (hwb : InWin env bp (16 * n))
    (hab : bp.toNat % 8 = 0) (hoz : env.Owned m top zp (16 * zl.toNat))
    (hwz : zl.toNat = 0 ∨ InWin env zp (16 * zl.toNat) ∧ zp.toNat % 8 = 0) :
    ∀ k R M, LInv env ret top regs m vp bp c zp zl vl n k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 150, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m vp bp c zp zl vl n) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, h23, h27, h24, hk1, hkn, h20, h26, h25, hM⟩ := id hI
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  have hwbl := hwb.lt
  have hwvl := hwv.lt
  have hcj : c.toNat * (n - k) < vl := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hcn
  have hea : (R .x25 + 18446744073709551608#64).toNat = bp.toNat + 16 * (n - k) := by
    rw [BitVec.toNat_add, h25, BitVec.toNat_ofNat]; omega
  have hd0 := hwb.dword hW hab hea (by omega) (by omega)
  have hd8 := hwb.dword (x := R .x25) (o := 16 * (n - k) + 8) hW hab (by omega) (by omega) (by omega)
  rv_introT hI
  rv_symT hp stop [150, 38] through [110] with [hL, hlim] using [dotAny hdot, dropPost hmul]
  all_goals
    first
      | have hM2 := call_back hret2_14 keep2_1 hret2_16 hret2_15 hlim
          (call_back hret1_14 keep1_1 hret1_16 hret1_15 hlim hM)
      | have hM2 := call_back hret4_14 keep4_1 hret4_16 hret4_15 hlim
          (call_back hret3_14 keep3_1 hret3_16 hret3_15 hlim hM)
  -- the return, after the last pair
  any_goals exact ret_ok env p i L hp hk hlim hal hW _ _ rfl hM2
  -- back to the head, one pair fewer
  all_goals
    have hk2 : 2 ≤ k := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega))
    have hcj1 : c.toNat * (n - k + 1) < vl := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hcn
    have hcs : c.toNat * (n - k + 1) = c.toNat * (n - k) + c.toNat := Nat.mul_succ _ _
    have hc4 : (c <<< 4).toNat = 16 * c.toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    refine ih (k - 1) _ _ (by omega) ⟨rfl, rfl, rfl, rfl, rfl, ?_, by omega, by omega, ?_, ?_, ?_, hM2⟩
    all_goals simp only [Tactic.rf]
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · rw [show n - (k - 1) = n - k + 1 by omega, BitVec.toNat_add, hc4, h20]; omega
    · rw [show n - (k - 1) = n - k + 1 by omega, BitVec.toNat_sub, h26]; omega
    · rw [toNat_add_ofNat (by omega)]; omega

set_option rv_sym.heap true in
/-- **After the prologue** (instruction 14): the zip's index and length read; the return for an empty zip, else
    the iterator's words and `eq_z`'s read, through `Mem` (`kept`), and the loop from the first pair. -/
theorem entry_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needD needU : Nat} (hnD : 112 + needD ≤ need) (hnU : 112 + needU ≤ need)
    (hdot : DotOwnT.specT env p L.dot.idx needD) (hmul : Field.EMulT.specT env p L.mul.idx needU)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {a : Word} (haa : a.toNat % 8 = 0) (hwa : InWin env a 64) (hoa : env.Owned m top a 64)
    (h40 : m.getMem (a + 40#64) = 0#64) (hzip : ZipW env m top a) (haz : (m.getMem (a + 56#64)).toNat % 8 = 0)
    (hwz : InWin env (m.getMem (a + 56#64)) 24) (hoz : env.Owned m top (m.getMem (a + 56#64)) 24)
    (hvz : VecW env m top (m.getMem (a + 56#64))) :
    ∀ R M, R .x2 = top + 18446744073709551504#64 → R .x10 = a → Mem env ret top regs m M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 28, ret, top⟩ :: rest, R, M⟩ := by
  intro R M h2 h10 hM
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  have hI : R .x2 = top + 18446744073709551504#64 ∧ R .x10 = a := ⟨h2, h10⟩
  have hpack : PLift (ZipW env m top a ∧ VecW env m top (m.getMem (a + 56#64)) ∧ Mem env ret top regs m M) :=
    ⟨⟨hzip, hvz, hM⟩⟩
  clear hzip hvz hM
  rv_introT hI
  rv_symT hp stop [150, 38] with [hL, hlim]
  all_goals
    obtain ⟨hzip, hvz, hM⟩ := hpack.down
    have hwl := hwa.lt
    have ko : ∀ o : Word, o.toNat + 8 ≤ 64 → M.getMem (a + o) = m.getMem (a + o) := fun o ho =>
      kept hM (by omega) (by rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; rcases hoa.1 with h | h <;> omega)
    have k0 : M.getMem a = m.getMem a := by simpa using ko 0#64 (by decide)
    have kz : ∀ o : Word, o.toNat + 8 ≤ 24 →
        M.getMem (m.getMem (a + 56#64) + o) = m.getMem (m.getMem (a + 56#64) + o) := fun o ho =>
      kept hM (by omega) (by
        have := hwz.lt
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; rcases hoz.1 with h | h <;> omega)
  -- `eq_z`'s header
  any_goals (rw [ko 56#64 (by decide)]; first
    | exact (hwz.dword_add (x := m.getMem (a + 56#64)) (o := 0) (k := 8) hW haz (by omega) (by omega)
        (by omega)).1
    | exact (hwz.dword_add (x := m.getMem (a + 56#64)) (o := 0) (k := 8) hW haz (by omega) (by omega)
        (by omega)).2
    | exact (hwz.dword_add (x := m.getMem (a + 56#64)) (o := 0) (k := 16) hW haz (by omega) (by omega)
        (by omega)).1
    | exact (hwz.dword_add (x := m.getMem (a + 56#64)) (o := 0) (k := 16) hW haz (by omega) (by omega)
        (by omega)).2)
  -- the loop from the first pair
  · rw [ko 40#64 (by decide), h40, ko 48#64 (by decide)] at hc
    rw [ko 8#64 (by decide), ko 16#64 (by decide), ko 24#64 (by decide), ko 40#64 (by decide), h40,
      ko 48#64 (by decide), ko 56#64 (by decide), k0, kz 8#64 (by decide), kz 16#64 (by decide)]
    have hn0 : (m.getMem (a + 48#64)).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hcn, hwv, hav, hov, hwb, hab⟩ := hzip.resolve_left hn0
    have := hwb.lt
    refine loop_ok env p i L hp hL hnD hnU hdot hmul hk hstop hstk hal hW hcn hwv hav hov hwb hab hvz.1 hvz.2
      (m.getMem (a + 48#64)).toNat _ _ ⟨rfl, rfl, rfl, rfl, rfl, ?_, by omega, le_rfl, ?_, ?_, ?_, hM⟩
    all_goals simp only [Tactic.rf, BitVec.zero_mul, BitVec.zero_shiftLeft, BitVec.zero_add, BitVec.sub_zero,
      BitVec.add_zero, Nat.sub_self, Nat.mul_zero]
    all_goals first | omega | rw [toNat_add_ofNat (by omega)]
  -- an empty zip: the return
  · exact ret_ok env p i L hp hk hlim hal hW _ _ rfl hM

set_option rv_sym.heap true in
/-- **`verify_layer`'s bit-position sum is total**: none for an empty zip, else the loop from its first pair. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needD needU : Nat} (hnD : 112 + needD ≤ need) (hnU : 112 + needU ≤ need)
    (hdot : DotOwnT.specT env p L.dot.idx needD) (hmul : Field.EMulT.specT env p L.mul.idx needU) :
    SumSafeT env p i need := by
  rv_autoT hp stop [28] with [hL]
  rw [hpre_2] at hpre_8 hpre_14
  rw [hpre_2] at hpre_11 hpre_16
  refine entry_ok env p i L hp hL hnD hnU hdot hmul hk hstop hpre_3 hpre_19 hpre_20 hpre_6 hpre_7 ⟨hpre_8, hpre_9⟩
    hpre_10 hpre_11 hpre_12 hpre_13 ⟨hpre_14, hpre_15⟩ ⟨⟨hpre_16, hpre_17⟩, hpre_18⟩ _ _ rfl rfl ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT

end Rv64mc.Proof.Field.ESumLaneT

/-- info: 'Rv64mc.Proof.Field.ESumLaneT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESumLaneT.total
