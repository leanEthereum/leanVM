/-
  Rv64mc.Proof.Whir.RingTargetT

  `verifier::ring_switch::ring_target(s, f, g) -> E` is total (`specT`): from `s` (`a0`, `a1`) none or in a window
  and 8-byte aligned, `f`'s eight elements (`a2`, the length the compiler took from `RING_MAP_WIDTH`) in a window and
  8-byte aligned, and `g` (`a3`, `a4`) allocated before (`Live`), none or in a window and 8-byte aligned, it returns,
  writing nothing of its caller's besides what it allocates, or the run ends with `a0 = 2` where `alloc` (through
  `handle_error`) or `reserve` does. Safety only: the partial contract's value (`Spec/Whir/RingSwitch.lean`'s
  `targetSpec`, `Model.ringTargetRust`) is owed. It has no partial proof (class C).

  `images` (header at `sp + 8`) is allocated with capacity `s.len` and `reserve`d for them (it has the room), then
  filled with `ring_psi(s_i, g)` (`psi`, `Total.loop` with the images left as the measure); then the eight passes over
  `f` from the last (`fpass`, `Total.loop` with the passes left), each a `frobenius_8`, a `poly_eval` over `images`,
  a `frobenius_8` and an `E::mul`. Cut at the images' loop head (instruction 46), after it (57, `fstart`) and at the
  passes' head (64). Each part keeps `SavedT.MemOk` (the twelve saved registers' slots) and the images' block `Img`,
  carried across its calls and stores by `call_ok`, `heap_ok`, `res_ok`. `ring_psi`, `poly_eval` and `frobenius_8`
  are stepped through their total contracts on the registers alone (`ReadSliceT`, `Frobenius8SafeT`).

  ## Main definitions

  * `PreT`, `specT`, `Mem`, `Img`, `TInv`, `PInv`, `FInv`

  ## Main results

  * `slots`, `call_ok`, `heap_ok`, `res_ok`, `fpass`, `fstart`, `psi`, `total`
-/

import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Multilinear.ReadSliceT
import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Whir.RingCoefficientsT
import Rv64mc.Gen.Tmpl.Verifier.RingSwitch.RingTarget

namespace Rv64mc.Proof.Whir.RingTargetT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Whir.RingCoefficientsT (shl4)
open Rv64mc.Gen.Verifier.RingSwitch.RingTarget (Link tmpl)

/-- The total precondition: `s` (`a1` elements at `a0`) none, or in a window and 8-byte aligned; `f`'s eight
    elements (`128` bytes at `a2`) in a window, 8-byte aligned; `g` (`a4` elements at `a3`) allocated before, none or
    in a window and 8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  ((regs .x11).toNat = 0 ∨ InWin env (regs .x10) (16 * (regs .x11).toNat) ∧ (regs .x10).toNat % 8 = 0) ∧
    InWin env (regs .x12) 128 ∧ (regs .x12).toNat % 8 = 0 ∧ env.Live m (regs .x13) (16 * (regs .x14).toNat) ∧
    ((regs .x14).toNat = 0 ∨ InWin env (regs .x13) (16 * (regs .x14).toNat) ∧ (regs .x13).toNat % 8 = 0)

/-- **The total contract of `ring_target`**: from `PreT` it returns, writing nothing of its caller's, or ends the
    run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

/-- What every part keeps of memory: `SavedT.MemOk` with the twelve saved registers' slots, from `top - 8` (the
    return address) down to `top - 96` (`s10`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (fun _ => False)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64, 18446744073709551528#64, 18446744073709551520#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20, regs .x21, regs .x22, regs .x23, regs .x24,
      regs .x25, regs .x26] m M

/-- The saved slots lie in the `96` bytes below `top`. -/
theorem slots : SlotsIn 96
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64, 18446744073709551528#64, 18446744073709551520#64] :=
  slots_le

/-- The images' block `q` of `n` elements: below `NEXT`, and unless empty allocated since the entry, 8-byte
    aligned. -/
def Img (env : Env) (m : MachineState) (n : Nat) (q : Word) (M : MachineState) : Prop :=
  q.toNat + 16 * n ≤ (env.next M).toNat ∧
    (n = 0 ∨ (env.next m).toNat ≤ q.toNat ∧ 0x10000000 ≤ q.toNat ∧ q.toNat % 8 = 0)

/-- After the images (instruction 57): the stack pointer, the images' block `q` in `x8`, their count `s.len` in `x9`,
    `f` in `x18`, `x27` the entry's (no slot saves it); `Mem`, `Img`. -/
def TInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = q ∧ (R .x9).toNat = (regs .x11).toNat ∧ R .x18 = regs .x12 ∧
    R .x27 = regs .x27 ∧ Mem env ret top regs m M ∧ Img env m (regs .x11).toNat q M

/-- The images' loop head (instruction 46), `j` left: `TInv`'s registers, `g` in `x19`, `x20`, `s.len` in `x22`,
    `s`'s cursor `x23` (`8` past the next element) and end `x21`, the images' cursor `x24` (`8` past the next one). -/
def PInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (j : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  TInv env ret top regs m q R M ∧ R .x19 = regs .x14 ∧ R .x20 = regs .x13 ∧ R .x22 = regs .x11 ∧ 1 ≤ j ∧
    j ≤ (regs .x11).toNat ∧ (R .x23).toNat + 16 * j = (regs .x10).toNat + 8 + 16 * (regs .x11).toNat ∧
    (R .x21).toNat = (regs .x10).toNat + 8 + 16 * (regs .x11).toNat ∧
    (R .x24).toNat + 16 * j = q.toNat + 8 + 16 * (regs .x11).toNat

/-- The passes' head (instruction 64), `k` passes left: `TInv`'s registers but `x18`, now the pass `k - 1`, `f`'s
    cursor `x25` (`8` past `f[k - 1]`), `-1` in `x26`, `x27` the entry's. -/
def FInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551488#64 ∧ R .x8 = q ∧ (R .x9).toNat = (regs .x11).toNat ∧
    (R .x18).toNat + 1 = k ∧ (R .x25).toNat = (regs .x12).toNat + 8 + 16 * (k - 1) ∧
    R .x26 = 18446744073709551615#64 ∧ R .x27 = regs .x27 ∧ 1 ≤ k ∧ k ≤ 8 ∧ Mem env ret top regs m M ∧
    Img env m (regs .x11).toNat q M

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- `Img` kept, `NEXT` not lowered. -/
theorem Img.mono {env : Env} {m M X : MachineState} {n : Nat} {q : Word} (h : Img env m n q M)
    (hn : (env.next M).toNat ≤ (env.next X).toNat) : Img env m n q X :=
  ⟨by have := h.1; omega, h.2⟩

/-- **Across a callee writing nothing of the caller's** (`m1`, from the stack pointer `top - 128`): `Mem`, `Img`
    kept, every word of the frame read as before. -/
theorem call_ok {env : Env} {ret top q : Word} {regs : Reg → Word} {m M m1 : MachineState} {n : Nat}
    (hlim : env.stackLimit.toNat + 128 ≤ top.toNat) (hM : Mem env ret top regs m M) (hI : Img env m n q M)
    (hf : env.Frame (top + 18446744073709551488#64) (fun _ => False) M m1)
    (hk : ∀ a : Word, top + 18446744073709551488#64 ≤ a → m1.getMem a = M.getMem a) (hc : m1.code = M.code)
    (hs : env.Static m1) :
    Mem env ret top regs m m1 ∧ Img env m n q m1 ∧ (env.next M).toNat ≤ (env.next m1).toNat := by
  exact ⟨(hM.call_below slots (by omega) hlim (by tn) hf hk hc hs).1, hI.mono hf.1, hf.1⟩

/-- **A store into what the function allocated**: `Mem`, `Img` kept, `NEXT` kept. -/
theorem heap_ok {env : Env} {ret top a q : Word} {regs : Reg → Word} {m M : MachineState} {n : Nat}
    (hlim : env.stackLimit.toNat + 128 ≤ top.toNat) (hM : Mem env ret top regs m M) (hI : Img env m n q M)
    (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat + 8 ≤ (env.next M).toNat) (v : Word) :
    Mem env ret top regs m (M.setMem a v) ∧ Img env m n q (M.setMem a v) ∧
      env.next (M.setMem a v) = env.next M := by
  obtain ⟨h1, n1⟩ := hM.fresh (v := v) slots (by omega) hlo hhi
  exact ⟨h1, hI.mono (by rw [n1]), n1⟩

/-- The images' header words (at `top - 120`) as `rvCapAt`, `rvPtrAt`, `vecCap`, `vecPtr`, `vecLen` name them. -/
theorem hdr (top : Word) (M : MachineState) :
    rvCapAt (top + 18446744073709551496#64) = top + 18446744073709551496#64 ∧
      rvPtrAt (top + 18446744073709551496#64) = top + 18446744073709551504#64 ∧
      vecCap M (top + 18446744073709551496#64) = M.getMem (top + 18446744073709551496#64) ∧
      vecPtr M (top + 18446744073709551496#64) = M.getMem (top + 18446744073709551504#64) ∧
      vecLen M (top + 18446744073709551496#64) = M.getMem (top + 18446744073709551512#64) :=
  Runtime.SavedT.hdr_at top _ M

/-- The images' header `(c, q, 0)` stored at `top - 120` to `top - 104`, read back, `NEXT` kept. -/
theorem hdr_stores {env : Env} {top c q : Word} {X : MachineState} (hlim : env.stackLimit.toNat + 128 ≤ top.toNat) :
    (((X.setMem (top + 18446744073709551496#64) c).setMem (top + 18446744073709551504#64) q).setMem
        (top + 18446744073709551512#64) 0#64).getMem (top + 18446744073709551496#64) = c ∧
      (((X.setMem (top + 18446744073709551496#64) c).setMem (top + 18446744073709551504#64) q).setMem
        (top + 18446744073709551512#64) 0#64).getMem (top + 18446744073709551504#64) = q ∧
      (((X.setMem (top + 18446744073709551496#64) c).setMem (top + 18446744073709551504#64) q).setMem
        (top + 18446744073709551512#64) 0#64).getMem (top + 18446744073709551512#64) = 0#64 ∧
      env.next (((X.setMem (top + 18446744073709551496#64) c).setMem (top + 18446744073709551504#64) q).setMem
        (top + 18446744073709551512#64) 0#64) = env.next X := by
  have hlay := env.layout
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b h => Tactic.ne_of_toNat h
  have e1 : (top + 18446744073709551496#64).toNat = top.toNat - 120 := by tn
  have e2 : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by tn
  have e3 : (top + 18446744073709551512#64).toNat = top.toNat - 104 := by tn
  refine ⟨?_, ?_, MachineState.getMem_setMem_eq, ?_⟩
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · rw [Tactic.next_setMem (ne _ _ (by omega)), Tactic.next_setMem (ne _ _ (by omega)),
      Tactic.next_setMem (ne _ _ (by omega))]

/-- **After `reserve(n)` of the images with the room** (`n` at most the capacity less the length, `m1`): `Mem`
    kept, the pointer and the length read as before. -/
theorem res_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    {n : Nat} (hlim : env.stackLimit.toNat + 128 ≤ top.toNat) (hM : Mem env ret top regs m M)
    (hf : env.Frame (top + 18446744073709551488#64) out M m1)
    (hout : ∀ a, out a → a = top + 18446744073709551496#64 ∨ a = top + 18446744073709551504#64)
    (hk : ∀ a : Word, top + 18446744073709551488#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1)
    (hlen : vecLen m1 (top + 18446744073709551496#64) = vecLen M (top + 18446744073709551496#64))
    (hroom : n ≤ (vecCap M (top + 18446744073709551496#64)).toNat - (vecLen M (top + 18446744073709551496#64)).toNat →
      vecCap m1 (top + 18446744073709551496#64) = vecCap M (top + 18446744073709551496#64) ∧
        vecPtr m1 (top + 18446744073709551496#64) = vecPtr M (top + 18446744073709551496#64))
    (hr : n ≤ (M.getMem (top + 18446744073709551496#64)).toNat - (M.getMem (top + 18446744073709551512#64)).toNat) :
    Mem env ret top regs m m1 ∧ (env.next M).toNat ≤ (env.next m1).toNat ∧
      m1.getMem (top + 18446744073709551504#64) = M.getMem (top + 18446744073709551504#64) ∧
      m1.getMem (top + 18446744073709551512#64) = M.getMem (top + 18446744073709551512#64) := by
  have hlay := env.layout
  have e488 : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by tn
  have ho : ∀ a, out a → a.toNat = top.toNat - 120 ∨ a.toNat = top.toNat - 112 := fun a ha => by
    rcases hout a ha with rfl | rfl
    · exact .inl (by tn)
    · exact .inr (by tn)
  obtain ⟨-, -, bC, bP, bL⟩ := hdr top m1
  obtain ⟨-, -, bC', bP', bL'⟩ := hdr top M
  rw [bL, bL'] at hlen
  rw [bC', bL', bC, bP, bP'] at hroom
  refine ⟨hM.call slots (by omega) (by omega) hf hc hs
    (fun a ha => Tactic.mw_stack (by rcases ho a ha with h | h <;> omega)) fun a h1 h2 =>
      hk a (Tactic.le_of_toNat (by omega)) fun h => by rcases ho a h with h | h <;> omega, hf.1, (hroom hr).2, hlen⟩

set_option rv_sym.heap true in
/-- **The passes**, from their head: `z` advanced (`frobenius_8`), `f[p]` read, `poly_eval` of the images at `z`,
    its `frobenius_8` and the product with `f[p]` (`E::mul`); then back to the head (one pass fewer) or the return. -/
theorem fpass (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needF needP needU : Nat} (hnF : 128 + needF ≤ need) (hnP : 128 + needP ≤ need) (hnU : 128 + needU ≤ need)
    (hfr : Frobenius8T.specT env p L.frobenius8.idx needF) (hpe : Multilinear.PolyEvalT.specT env p L.polyEval.idx needP)
    (hmul : Field.EMulT.specT env p L.mul.idx needU)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {q : Word} (hwf : InWin env (regs .x12) 128) (haf : (regs .x12).toNat % 8 = 0) :
    ∀ k R M, FInv env ret top regs m q k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 128, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (FInv env ret top regs m q) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, h9, h18, h25, -, -, hk1, hk8, hM, hI1, hI2⟩ := id hI
  have hnM := hM.1.2.1
  have hhe := hW.heapEnd_le
  have hlim : env.stackLimit.toNat + 128 ≤ top.toNat := by omega
  have hwl := hwf.lt
  have hfa : (R .x25 + 18446744073709551608#64).toNat = (regs .x12).toNat + 16 * (k - 1) := by
    rw [BitVec.toNat_add, h25, BitVec.toNat_ofNat]; omega
  have hd0 := hwf.dword hW haf hfa (by omega) (by omega)
  have hd8 := hwf.dword (x := R .x25) (o := 8 + 16 * (k - 1)) hW haf (by rw [h25]; omega) (by omega) (by omega)
  rv_introT hI
  rv_symT hp stop [128] with [hL, hlim]
    using [Whir.Frobenius8SafeT.frobSafe hfr, Multilinear.ReadSliceT.polyEvalSafe hpe, hmul]
  all_goals
    obtain ⟨hM1, hI1', hn1⟩ := call_ok hlim hM ⟨hI1, hI2⟩ hret1_14 keep1_1 hret1_16 hret1_15
    obtain ⟨hM2, hI2', hn2⟩ := call_ok hlim hM1 hI1' hret2_14 keep2_1 hret2_16 hret2_15
    obtain ⟨hM3, hI3', hn3⟩ := call_ok hlim hM2 hI2' hret3_14 keep3_1 hret3_16 hret3_15
    obtain ⟨hM4, hI4', hn4⟩ := call_ok hlim hM3 hI3' hret4_14 keep4_1 hret4_18 hret4_15
  -- back to the head, one pass fewer
  · have hk2 : 2 ≤ k := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨rfl, rfl, h9, ?_, ?_, rfl, rfl, by omega, by omega, hM4, hI4'⟩
    all_goals simp only [Tactic.rf]
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · rw [BitVec.toNat_add, h25, BitVec.toNat_ofNat]; omega
  -- the return
  · obtain ⟨-, -, -, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -⟩ := hM
    refine ⟨?_, hM4.1, hM4.2.2.1, trivial⟩
    simp only [AbiRegs, Tactic.rf]
    exact ⟨trivial, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, trivial⟩

set_option rv_sym.heap true in
/-- **After the images** (instruction 57): the passes' registers set, then the passes' head with all eight left. -/
theorem fstart (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    {q : Word} (hwf : InWin env (regs .x12) 128)
    (hf : ∀ R M, FInv env ret top regs m q 8 R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 128, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, TInv env ret top regs m q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨-, -, h9, -, -, hM, hI1⟩ := id hI
  have hwl := hwf.lt
  rv_introT hI
  rv_symT hp stop [128]
  refine hf _ _ ⟨rfl, rfl, h9, ?_, ?_, rfl, rfl, by omega, Nat.le_refl _, hM, hI1⟩
  all_goals simp only [Tactic.rf]
  · rfl
  · rw [toNat_add_ofNat (by omega)]

set_option rv_sym.heap true in
/-- **The images' loop**, from its head: `ring_psi(s_i, g)` stored after the images, then back to the head or on
    after the loop; one image fewer left. -/
theorem psi (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR : Nat} (hnR : 128 + needR ≤ need) (hrp : Whir.RingPsiT.specT env p L.ringPsi.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {q : Word} (hws : InWin env (regs .x10) (16 * (regs .x11).toNat)) (has : (regs .x10).toNat % 8 = 0)
    (hgl : env.Live m (regs .x13) (16 * (regs .x14).toNat))
    (hg : (regs .x14).toNat = 0 ∨ InWin env (regs .x13) (16 * (regs .x14).toNat) ∧ (regs .x13).toNat % 8 = 0)
    (ht : ∀ R M, TInv env ret top regs m q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, PInv env ret top regs m q j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 92, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (PInv env ret top regs m q) fun j R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, h9, -, -, hM, hI1, hI2⟩, -, -, -, hj1, hjn, h23, h21, h24⟩ := id hI
  obtain ⟨hq1, hq2, hq3⟩ := hI2.resolve_left (by omega)
  have hnM := hM.1.2.1
  have hhe := hW.heapEnd_le
  have hlim : env.stackLimit.toNat + 128 ≤ top.toNat := by omega
  have hwl := hws.lt
  have hglM : env.Live M (regs .x13) (16 * (regs .x14).toNat) := by
    have := hM.next_le; unfold Env.Live at hgl ⊢; omega
  have hsa : (R .x23 + 18446744073709551608#64).toNat = (regs .x10).toNat + 16 * ((regs .x11).toNat - j) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hd0 := hws.dword hW has hsa (by omega) (by omega)
  have hd8 := hws.dword (x := R .x23) (o := 16 * ((regs .x11).toNat - j) + 8) hW has (by omega) (by omega)
    (by omega)
  rv_introT hI
  rv_symT hp stop [92, 114] with [hL, hlim] using [Multilinear.ReadSliceT.ringPsiSafe hrp]
  all_goals
    have e8 : (R .x24 + 18446744073709551608#64).toNat = (R .x24).toNat - 8 := by tn
    obtain ⟨hM1, hI1', hn1⟩ := call_ok hlim hM ⟨hI1, hI2⟩ hret1_14 keep1_1 hret1_16 hret1_15
    obtain ⟨hM2, hI2', hn2⟩ := heap_ok (a := R .x24 + 18446744073709551608#64) hlim hM1 hI1' (by rw [e8]; omega)
      (by rw [e8]; omega) (r1 .x10)
    obtain ⟨hM3, hI3', hn3⟩ := heap_ok (a := R .x24) hlim hM2 hI2' (by omega) (by rw [hn2]; omega) (r1 .x11)
  -- back to the head
  · have hj2 : 2 ≤ j := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega)]; omega))
    refine ih (j - 1) _ _ (by omega) ⟨⟨rfl, rfl, h9, rfl, rfl, hM3, hI3'⟩, rfl, rfl, rfl, by omega, by omega, ?_, h21,
      ?_⟩
    all_goals simp only [Tactic.rf]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
  -- the last image: on after the loop
  · exact ht _ _ ⟨rfl, rfl, h9, rfl, rfl, hM3, hI3'⟩

set_option rv_sym.heap true in
/-- **`ring_target` is total**: `images` allocated with capacity `s.len` (`handle_error` when `alloc` fails) and
    `reserve`d, then the images' loop (none for an empty `s`) and the passes. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needH needR needS needF needP needU : Nat} (hnA : 128 + needA ≤ need) (hnH : 128 + needH ≤ need)
    (hnR : 128 + needR ≤ need) (hnS : 128 + needS ≤ need) (hnF : 128 + needF ≤ need) (hnP : 128 + needP ≤ need)
    (hnU : 128 + needU ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hhe : Aborts env p L.handleError.idx needH)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hrp : Whir.RingPsiT.specT env p L.ringPsi.idx needS) (hfr : Frobenius8T.specT env p L.frobenius8.idx needF)
    (hpe : Multilinear.PolyEvalT.specT env p L.polyEval.idx needP) (hmul : Field.EMulT.specT env p L.mul.idx needU) :
    specT env p i need := by
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 128 ≤ top.toNat)]
  have hn16 : 16 * (regs .x11).toNat < 2 ^ 32 := by
    rcases hpre_6 with h | ⟨h, -⟩
    · omega
    · unfold InWin at h; have := hpre_12.heapEnd_le; omega
  have hs4 : (regs .x11 <<< 4).toNat = 16 * (regs .x11).toNat := shl4 (by omega)
  have hts := fun q => fstart env p i L hp (q := q) hpre_7
    (fpass env p i L hp hL hnF hnP hnU hfr hpe hmul hk hpre_3 hpre_11 hpre_12 hpre_7 hpre_8 _)
  rv_symT hp stop [92, 114] with [hL, (by omega : env.stackLimit.toNat + 128 ≤ top.toNat)] using [hac, hhe, hres]
  all_goals
    have hlim : env.stackLimit.toNat + 128 ≤ top.toNat := by omega
    have hlay := env.layout
    have hge := hpre_12.next_ge
    have bc := (hdr top m).1
    have bp := (hdr top m).2.1
  -- `s` empty: `reserve(0)`'s precondition
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    rw [bc, (hdr_stores hlim).1]; exact .inl (by rw [hc]; rfl)
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    rw [bc, (hdr_stores hlim).1, hc]; decide
  · refine .inl ?_
    simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    rw [bc, (hdr_stores hlim).1, hc]; rfl
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    rw [bc, (hdr_stores hlim).1, hc]; decide
  -- `s` empty: after the loop
  · have hn0 : (regs .x11).toNat = 0 := by rw [hc]; rfl
    obtain ⟨hM1, hn1, g504, g512⟩ := res_ok (n := (regs .x11).toNat) (m := m) (regs := regs) (ret := ret) hlim
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT) hret1_14
      (fun a ha => by
        simp only [GrowOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, bc, bp] at ha
        exact ha) keep1_1 hret1_25 hret1_15 hret1_16 hret1_17
      (by rw [(hdr_stores hlim).1, (hdr_stores hlim).2.2.1]; omega)
    refine hts 8#64 _ _ ⟨rfl, ?_, ?_, rfl, rfl, hM1, ?_, .inl hn0⟩
    all_goals try simp only [Tactic.rf]
    · rw [g504, (hdr_stores hlim).2.1]
    · rw [g512, (hdr_stores hlim).2.2.1, hn0]; rfl
    · have := hM1.next_le
      simp only [BitVec.toNat_ofNat]; omega
  -- `s` empty: never the images' loop
  · exact absurd hc_1 hc
  all_goals
    have hn0 : (regs .x11).toNat ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have h18 := hret2_18
    rw [hs4] at h18
    have hn2 := hret2_14.2.1
    have hq := hret2_16
    have hq8 := hret2_17
  -- `s` not empty: `reserve(s.len)`'s precondition
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    rw [bc, bp, (hdr_stores hlim).1, (hdr_stores hlim).2.1]
    exact .inr (by unfold Env.Live; rw [(hdr_stores hlim).2.2.2]; omega)
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    rw [bc, (hdr_stores hlim).1]; omega
  · refine .inr ?_
    simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    rw [bc, bp, (hdr_stores hlim).1, (hdr_stores hlim).2.1]
    exact ⟨by omega, by unfold Env.Live; rw [(hdr_stores hlim).2.2.2]; omega, hq8⟩
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
    rw [bc, (hdr_stores hlim).1]; omega
  -- `s` not empty: never straight after the loop
  · exact absurd hc hc_1
  -- the images' loop
  · obtain ⟨hws, has⟩ := hpre_6.resolve_left hn0
    have hwl := hws.lt
    obtain ⟨hM3, hn3, g504, g512⟩ := res_ok (n := (regs .x11).toNat) (m := m) (regs := regs) (ret := ret) hlim
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT) hret3_14
      (fun a ha => by
        simp only [GrowOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, bc, bp] at ha
        exact ha) keep3_1 hret3_25 hret3_15 hret3_16 hret3_17
      (by rw [(hdr_stores hlim).1, (hdr_stores hlim).2.2.1]; simp)
    have hp0 : m3.getMem (top + 18446744073709551504#64) = r2 .x10 := by rw [g504, (hdr_stores hlim).2.1]
    have hl0 : m3.getMem (top + 18446744073709551512#64) = 0#64 := by rw [g512, (hdr_stores hlim).2.2.1]
    have hnx : (env.next m2).toNat ≤ (env.next m3).toNat := by
      have := hret3_14.1; rw [(hdr_stores hlim).2.2.2] at this; exact this
    refine psi env p i L hp hL hnS hrp hpre_3 hpre_11 hpre_12 hws has hpre_9 hpre_10 (hts _) (regs .x11).toNat _ _
      ⟨⟨rfl, hp0, ?_, rfl, rfl, hM3, ?_, .inr ⟨?_, ?_, hq8⟩⟩, rfl, rfl, rfl, by omega, Nat.le_refl _, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    · rw [hl0, BitVec.zero_add]
    · omega
    · have := hret2_14.1; omega
    · omega
    · rw [toNat_add_ofNat (by omega)]
    · have := hws; unfold InWin at this
      rw [BitVec.toNat_add, toNat_add_ofNat (by omega), hs4]; omega
    · rw [hl0, BitVec.zero_shiftLeft, BitVec.zero_add, hp0, toNat_add_ofNat (by omega)]

end Rv64mc.Proof.Whir.RingTargetT

/-- info: 'Rv64mc.Proof.Whir.RingTargetT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.RingTargetT.total
