/-
  Rv64mc.Proof.Whir.RingCoefficientsT

  `verifier::ring_switch::ring_coefficients(f, g) -> Vec<E>` is total (`specT`): from a result's slot of `24` bytes
  owned, in a window, 8-byte aligned, `f`'s eight elements (`a1`, the length the compiler took from `RING_MAP_WIDTH`)
  in a window and 8-byte aligned, and `g` (`a2`, `a3`) none or in a window and owned, it returns with the slot a
  vector of `E`s (`VecT`) of `8 g.len` elements, its buffer allocated since the entry, writing at most the slot
  besides what it allocates (`SretOut`, the partial contract's), or the run ends with `a0 = 2` where `alloc`
  (through `handle_error`) or `reserve` does. Safety only: the partial contract's values
  (`Spec/Whir/RingSwitch.lean`'s `coefficientsSpec`, `Model.ringCoefficientsRust`) are owed. It has no partial proof
  (class C).

  The coefficients start with capacity `64` (header at `sp + 0x10`), `powers` as a copy of `g` (`memcpy` into a
  block of `16 g.len` bytes, or none). Each of the eight passes `reserve`s `g.len` more coefficients, stores
  `f[p] * g_b` for every power (`E::mul`), then replaces every power by its Frobenius image (`frobenius_8`). Cut at the
  passes' head (instruction 48, `outer`, `Total.loop` with the passes left as the measure), the products' loop head
  (63, `prods`, the products left), the powers' loop head (76, `frobs`, the powers left) and the exit (86, `fin_ok`).
  Each part keeps `SavedT.MemOk` (the frame, the code, the static data, the thirteen saved registers' slots), the
  coefficients' header `CV` and the powers' block `PW`, carried across its calls and stores by `call_ok`, `heap_ok`,
  `res_ok` and `len_ok`.

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `Mem`, `CV`, `PW`, `FinInv`, `OInv`, `MInv`, `FInv`

  ## Main results

  * `slots`, `shl4`, `call_ok`, `heap_ok`, `res_ok`, `len_ok`, `fin_ok`, `frobs`, `prods`, `outer`, `total`
-/

import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Whir.Frobenius8SafeT
import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Whir.VecWordT
import Rv64mc.Spec.Whir.Basic
import Rv64mc.Gen.Tmpl.Verifier.RingSwitch.RingCoefficients

namespace Rv64mc.Proof.Whir.RingCoefficientsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Whir.VecWordT (vecT_stores)
open Rv64mc.Gen.Verifier.RingSwitch.RingCoefficients (Link tmpl)

/-- The total precondition: the result's slot (`24` bytes) in a window, 8-byte aligned, owned; `f`'s eight elements
    (`128` bytes at `a1`) in a window, 8-byte aligned; `g` (`a3` elements at `a2`) none, or in a window and owned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24 ∧
    InWin env (regs .x11) 128 ∧ (regs .x11).toNat % 8 = 0 ∧
    ((regs .x13).toNat = 0 ∨
      InWin env (regs .x12) (16 * (regs .x13).toNat) ∧ env.Owned m (regs .x2) (regs .x12) (16 * (regs .x13).toNat))

/-- The total postcondition: the slot a vector of `E`s of `8 g.len` elements, its buffer allocated since the entry
    unless it has no capacity. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ (vecLen m' (regs .x10)).toNat = 8 * (regs .x13).toNat ∧
    (vecCap m' (regs .x10) = 0#64 ∨ (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat)

/-- **The total contract of `ring_coefficients`**: `PreT` to `PostT`, writing at most the slot (`SretOut`, the partial
    contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (SretOut Layouts.Vec.byteSize) (Stop := AbortStop)

/-- What every part keeps of memory: `SavedT.MemOk` with the thirteen saved registers' slots, from `top - 8` (the
    return address) down to `top - 104` (`s11`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (SretOut Layouts.Vec.byteSize regs m)
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
      18446744073709551512#64] := slots_le

/-- The coefficients' header at `top - 128` (capacity, pointer at `top - 120`, length at `top - 112`): its length at
    most its capacity, its buffer of fewer than `2^63` bytes, allocated since the entry, 8-byte aligned. -/
def CV (env : Env) (m : MachineState) (top : Word) (M : MachineState) : Prop :=
  (M.getMem (top + 18446744073709551504#64)).toNat ≤ (M.getMem (top + 18446744073709551488#64)).toNat ∧
    (M.getMem (top + 18446744073709551488#64)).toNat * 16 < 2 ^ 63 ∧
    (env.next m).toNat ≤ (M.getMem (top + 18446744073709551496#64)).toNat ∧
    0x10000000 ≤ (M.getMem (top + 18446744073709551496#64)).toNat ∧
    (M.getMem (top + 18446744073709551496#64)).toNat + 16 * (M.getMem (top + 18446744073709551488#64)).toNat ≤
      (env.next M).toNat ∧
    (M.getMem (top + 18446744073709551496#64)).toNat % 8 = 0

/-- The powers' block `q` of `n` elements: none, or allocated since the entry, 8-byte aligned. -/
def PW (env : Env) (m : MachineState) (n : Nat) (q : Word) (M : MachineState) : Prop :=
  n = 0 ∨ (env.next m).toNat ≤ q.toNat ∧ 0x10000000 ≤ q.toNat ∧ q.toNat + 16 * n ≤ (env.next M).toNat ∧
    q.toNat % 8 = 0

/-- The exit (instruction 86): the stack pointer, the slot's address at `sp + 8`, the coefficients' length
    `8 g.len`; `Mem`, `CV`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ M.getMem (top + 18446744073709551480#64) = regs .x10 ∧
    (M.getMem (top + 18446744073709551504#64)).toNat = 8 * (regs .x13).toNat ∧ Mem env ret top regs m M ∧
    CV env m top M

/-- The passes' head (instruction 48), `k` passes left: the stack pointer, `g.len` in `x9`, `f` in `x18`, the
    powers `q` in `x19`, `16 (8 - k)` in `x22`, the powers' end `q + 16 g.len` in `x23` and `q + 8 + 16 g.len` in
    `x25`, `128` in `x26`; the slot's address at `sp + 8`, the coefficients' length `(8 - k) g.len`; `PW`, `Mem`,
    `CV`. -/
def OInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x9 = regs .x13 ∧ R .x18 = regs .x11 ∧ R .x19 = q ∧
    (R .x22).toNat = 16 * (8 - k) ∧ (R .x23).toNat = q.toNat + 16 * (regs .x13).toNat ∧
    (R .x25).toNat = q.toNat + 8 + 16 * (regs .x13).toNat ∧ R .x26 = 128#64 ∧ 1 ≤ k ∧ k ≤ 8 ∧
    M.getMem (top + 18446744073709551480#64) = regs .x10 ∧
    (M.getMem (top + 18446744073709551504#64)).toNat = (8 - k) * (regs .x13).toNat ∧
    PW env m (regs .x13).toNat q M ∧ Mem env ret top regs m M ∧ CV env m top M

/-- The products' loop head (instruction 63), `k` passes left, `j` products left: `OInv`'s registers, the new length
    `(9 - k) g.len` in `x27`, the powers' cursor `x24` (`q + 8` past the products done) and the coefficients' cursor
    `x8` (`8` past the next one), room for `g.len` more coefficients, `g.len ≥ 1`. -/
def MInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (k j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  OInv env ret top regs m q k R M ∧ (R .x27).toNat = (9 - k) * (regs .x13).toNat ∧ 1 ≤ j ∧
    j ≤ (regs .x13).toNat ∧ (R .x24).toNat + 16 * j = q.toNat + 8 + 16 * (regs .x13).toNat ∧
    (R .x8).toNat + 16 * j = (M.getMem (top + 18446744073709551496#64)).toNat +
      16 * ((9 - k) * (regs .x13).toNat) + 8 ∧
    (9 - k) * (regs .x13).toNat ≤ (M.getMem (top + 18446744073709551488#64)).toNat

/-- The powers' loop head (instruction 76), `k` passes left, `j` powers left: `OInv`'s registers but the length,
    now `(9 - k) g.len`; the powers' cursor `x8` (`q + 16 g.len` past the powers left), `g.len ≥ 1`. -/
def FInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (k j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551472#64 ∧ R .x9 = regs .x13 ∧ R .x18 = regs .x11 ∧ R .x19 = q ∧
    (R .x22).toNat = 16 * (8 - k) ∧ (R .x23).toNat = q.toNat + 16 * (regs .x13).toNat ∧
    (R .x25).toNat = q.toNat + 8 + 16 * (regs .x13).toNat ∧ R .x26 = 128#64 ∧ 1 ≤ k ∧ k ≤ 8 ∧
    M.getMem (top + 18446744073709551480#64) = regs .x10 ∧
    (M.getMem (top + 18446744073709551504#64)).toNat = (9 - k) * (regs .x13).toNat ∧
    PW env m (regs .x13).toNat q M ∧ Mem env ret top regs m M ∧ CV env m top M ∧ 1 ≤ j ∧
    j ≤ (regs .x13).toNat ∧ (R .x8).toNat + 16 * j = q.toNat + 16 * (regs .x13).toNat

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- `16 x` as the code computes it. -/
theorem shl4 {x : Word} (h : 16 * x.toNat < 2 ^ 64) : (x <<< 4).toNat = 16 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- `PW` kept, `NEXT` not lowered. -/
theorem PW.mono {env : Env} {m M X : MachineState} {n : Nat} {q : Word} (h : PW env m n q M)
    (hn : (env.next M).toNat ≤ (env.next X).toNat) : PW env m n q X :=
  h.imp id fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, by omega, h4⟩

/-- **`CV` kept** by a memory agreeing on the header's three words, `NEXT` not lowered. -/
theorem CV.keep {env : Env} {m M X : MachineState} {top : Word} (h : CV env m top M)
    (hn : (env.next M).toNat ≤ (env.next X).toNat) (hlim : 144 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 128 ≤ a.toNat → a.toNat < top.toNat - 104 → X.getMem a = M.getMem a) :
    CV env m top X := by
  unfold CV at h ⊢
  rw [hk _ (by tn) (by tn), hk _ (by tn) (by tn), hk _ (by tn) (by tn)]
  omega

/-- **Across a callee writing nothing of the caller's** (`m1`, from the stack pointer `top - 144`): `Mem`, `CV`,
    `PW` kept, every word of the frame read as before. -/
theorem call_ok {env : Env} {ret top q : Word} {regs : Reg → Word} {m M m1 : MachineState} {n : Nat}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : Mem env ret top regs m M) (hB : CV env m top M)
    (hP : PW env m n q M) (hf : env.Frame (top + 18446744073709551472#64) (fun _ => False) M m1)
    (hk : ∀ a : Word, top + 18446744073709551472#64 ≤ a → m1.getMem a = M.getMem a) (hc : m1.code = M.code)
    (hs : env.Static m1) :
    Mem env ret top regs m m1 ∧ CV env m top m1 ∧ PW env m n q m1 ∧
      ∀ c : Word, top.toNat - 144 ≤ (top + c).toNat → m1.getMem (top + c) = M.getMem (top + c) := by
  have e472 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  have rd : ∀ a : Word, top.toNat - 144 ≤ a.toNat → m1.getMem a = M.getMem a := fun a h =>
    hk a (Tactic.le_of_toNat (by omega))
  exact ⟨hM.call slots (by omega) (by omega) hf hc hs (fun _ h => h.elim) fun a h1 _ => rd a (by omega),
    hB.keep hf.1 (by omega) fun a h1 _ => rd a (by omega), hP.mono hf.1, fun c h => rd _ h⟩

/-- **A store into what the function allocated**: `Mem`, `CV`, `PW` kept, `NEXT` kept, every word of the stack read
    as before. -/
theorem heap_ok {env : Env} {ret top a q : Word} {regs : Reg → Word} {m M : MachineState} {n : Nat}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : Mem env ret top regs m M) (hB : CV env m top M)
    (hP : PW env m n q M) (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat + 8 ≤ (env.next M).toNat) (v : Word) :
    Mem env ret top regs m (M.setMem a v) ∧ CV env m top (M.setMem a v) ∧ PW env m n q (M.setMem a v) ∧
      env.next (M.setMem a v) = env.next M ∧
      ∀ c : Word, env.stackLimit.toNat ≤ (top + c).toNat → (M.setMem a v).getMem (top + c) = M.getMem (top + c) := by
  have hlay := env.layout
  have hnM := hM.1.2.1
  obtain ⟨h1, n1⟩ := hM.fresh (v := v) slots (by omega) hlo hhi
  have rd : ∀ x : Word, env.stackLimit.toNat ≤ x.toNat → (M.setMem a v).getMem x = M.getMem x := fun x h =>
    MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))
  exact ⟨h1, hB.keep (by rw [n1]) (by omega) fun x h1 _ => rd x (by omega), hP.mono (by rw [n1]), n1,
    fun c h => rd _ h⟩

/-- The coefficients' header words (at `top - 128`) as `rvCapAt`, `rvPtrAt`, `vecCap`, `vecPtr`, `vecLen` name
    them. -/
theorem hdr (top : Word) (M : MachineState) :
    rvCapAt (top + 18446744073709551488#64) = top + 18446744073709551488#64 ∧
      rvPtrAt (top + 18446744073709551488#64) = top + 18446744073709551496#64 ∧
      vecCap M (top + 18446744073709551488#64) = M.getMem (top + 18446744073709551488#64) ∧
      vecPtr M (top + 18446744073709551488#64) = M.getMem (top + 18446744073709551496#64) ∧
      vecLen M (top + 18446744073709551488#64) = M.getMem (top + 18446744073709551504#64) := by
  refine ⟨Runtime.GrowOne.rvCapAt_eq _, ?_, Runtime.VecHdrT.vecCap_eq _ _, ?_, ?_⟩
  · unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
  · unfold vecPtr; rw [BitVec.add_assoc]; rfl
  · unfold vecLen; rw [BitVec.add_assoc]; rfl

/-- The coefficients' header `(c, q, 0)` and the slot's address `s` stored at `top - 128` to `top - 112` and at
    `top - 136`, read back, `NEXT` kept. -/
theorem hdr_stores {env : Env} {top c q s : Word} {X : MachineState}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) :
    ((((X.setMem (top + 18446744073709551488#64) c).setMem (top + 18446744073709551496#64) q).setMem
        (top + 18446744073709551504#64) 0#64).setMem (top + 18446744073709551480#64) s).getMem
        (top + 18446744073709551488#64) = c ∧
      ((((X.setMem (top + 18446744073709551488#64) c).setMem (top + 18446744073709551496#64) q).setMem
        (top + 18446744073709551504#64) 0#64).setMem (top + 18446744073709551480#64) s).getMem
        (top + 18446744073709551496#64) = q ∧
      env.next ((((X.setMem (top + 18446744073709551488#64) c).setMem (top + 18446744073709551496#64) q).setMem
        (top + 18446744073709551504#64) 0#64).setMem (top + 18446744073709551480#64) s) = env.next X := by
  have hlay := env.layout
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b h => Tactic.ne_of_toNat h
  have e1 : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by tn
  have e2 : (top + 18446744073709551496#64).toNat = top.toNat - 120 := by tn
  have e3 : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by tn
  have e4 : (top + 18446744073709551480#64).toNat = top.toNat - 136 := by tn
  refine ⟨?_, ?_, ?_⟩
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [Tactic.next_setMem (ne _ _ (by omega)), Tactic.next_setMem (ne _ _ (by omega)),
      Tactic.next_setMem (ne _ _ (by omega)), Tactic.next_setMem (ne _ _ (by omega))]

/-- **After `reserve(n)` of the coefficients** (`m1`): `Mem`, `PW` kept, the length kept, room for `n` more, `CV`,
    every other word of the frame read as before. -/
theorem res_ok {env : Env} {ret top q : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    {n : Nat} (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : Mem env ret top regs m M)
    (hB : CV env m top M) (hP : PW env m n q M) (hf : env.Frame (top + 18446744073709551472#64) out M m1)
    (hout : ∀ a, out a → a = top + 18446744073709551488#64 ∨ a = top + 18446744073709551496#64)
    (hk : ∀ a : Word, top + 18446744073709551472#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1)
    (hlen : vecLen m1 (top + 18446744073709551488#64) = vecLen M (top + 18446744073709551488#64))
    (hroom : n ≤ (vecCap M (top + 18446744073709551488#64)).toNat - (vecLen M (top + 18446744073709551488#64)).toNat →
      vecCap m1 (top + 18446744073709551488#64) = vecCap M (top + 18446744073709551488#64) ∧
        vecPtr m1 (top + 18446744073709551488#64) = vecPtr M (top + 18446744073709551488#64))
    (hgrow : ¬ n ≤ (vecCap M (top + 18446744073709551488#64)).toNat -
        (vecLen M (top + 18446744073709551488#64)).toNat →
      Grown env M m1 (top + 18446744073709551488#64) ((vecLen M (top + 18446744073709551488#64)).toNat + n) 16)
    (hbuf : (m1.getMem (rvCapAt (top + 18446744073709551488#64))).toNat = 0 ∨
      0x10000000 ≤ (m1.getMem (rvPtrAt (top + 18446744073709551488#64))).toNat ∧
        env.Live m1 (m1.getMem (rvPtrAt (top + 18446744073709551488#64)))
          ((m1.getMem (rvCapAt (top + 18446744073709551488#64))).toNat * 16) ∧
        (m1.getMem (rvPtrAt (top + 18446744073709551488#64))).toNat % 8 = 0)
    (hcap : (m1.getMem (rvCapAt (top + 18446744073709551488#64))).toNat * 16 < 2 ^ 63) :
    Mem env ret top regs m m1 ∧ CV env m top m1 ∧ PW env m n q m1 ∧
      (m1.getMem (top + 18446744073709551504#64)).toNat + n ≤ (m1.getMem (top + 18446744073709551488#64)).toNat ∧
      m1.getMem (top + 18446744073709551504#64) = M.getMem (top + 18446744073709551504#64) ∧
      ∀ c : Word, top.toNat - 144 ≤ (top + c).toNat → (top + c).toNat ≠ top.toNat - 128 →
        (top + c).toNat ≠ top.toNat - 120 → m1.getMem (top + c) = M.getMem (top + c) := by
  have hlay := env.layout
  have e472 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  have ho : ∀ a, out a → a.toNat = top.toNat - 128 ∨ a.toNat = top.toNat - 120 := fun a ha => by
    rcases hout a ha with rfl | rfl
    · exact .inl (by tn)
    · exact .inr (by tn)
  have rd : ∀ a : Word, top.toNat - 144 ≤ a.toNat → a.toNat ≠ top.toNat - 128 → a.toNat ≠ top.toNat - 120 →
      m1.getMem a = M.getMem a := fun a h1 h2 h3 =>
    hk a (Tactic.le_of_toNat (by omega)) fun h => by rcases ho a h with h | h <;> omega
  have hM1 : Mem env ret top regs m m1 := hM.call slots (by omega) (by omega) hf hc hs
    (fun a ha => Tactic.mw_stack (by rcases ho a ha with h | h <;> omega)) fun a h1 h2 =>
      rd a (by omega) (by omega) (by omega)
  obtain ⟨bc, bp, bC, bP, bL⟩ := hdr top m1
  obtain ⟨-, -, bC', bP', bL'⟩ := hdr top M
  rw [bL, bL'] at hlen
  rw [bC', bL', bC, bP, bP'] at hroom
  rw [bC', bL'] at hgrow
  rw [bc, bp] at hbuf
  rw [bc] at hcap
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hB
  have hn1 := hf.1
  refine ⟨hM1, ?_, hP.mono hn1, ?_, hlen, fun c h1 h2 h3 => rd _ h1 h2 h3⟩
  all_goals by_cases hr : n ≤ (M.getMem (top + 18446744073709551488#64)).toNat -
    (M.getMem (top + 18446744073709551504#64)).toNat
  · obtain ⟨c1, p1⟩ := hroom hr
    unfold CV; rw [c1, p1, hlen]; omega
  · obtain ⟨g1, ⟨g2, g3⟩, -⟩ := hgrow hr
    rw [Runtime.GrowOne.rvCapAt_eq] at g1 g3
    rw [Runtime.GrowOne.rvPtrAt_eq] at g2 g3
    rw [show top + 18446744073709551488#64 + 8#64 = top + 18446744073709551496#64 by
      rw [BitVec.add_assoc]; rfl] at g2 g3
    obtain ⟨p0, -, p8⟩ := hbuf.resolve_left (by omega)
    unfold CV; rw [hlen]; omega
  · obtain ⟨c1, -⟩ := hroom hr
    rw [c1, hlen]; omega
  · obtain ⟨g1, -, -⟩ := hgrow hr
    rw [Runtime.GrowOne.rvCapAt_eq] at g1
    rw [hlen]; omega

/-- **The length stored** (`sp + 0x20`), at most the capacity: `Mem`, `CV`, `PW` kept, `NEXT` kept, every other word
    of the frame read as before. -/
theorem len_ok {env : Env} {ret top v q : Word} {regs : Reg → Word} {m M : MachineState} {n : Nat}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hM : Mem env ret top regs m M) (hB : CV env m top M)
    (hP : PW env m n q M) (hv : v.toNat ≤ (M.getMem (top + 18446744073709551488#64)).toNat) :
    Mem env ret top regs m (M.setMem (top + 18446744073709551504#64) v) ∧
      CV env m top (M.setMem (top + 18446744073709551504#64) v) ∧
      PW env m n q (M.setMem (top + 18446744073709551504#64) v) ∧
      env.next (M.setMem (top + 18446744073709551504#64) v) = env.next M ∧
      ∀ c : Word, c ≠ 18446744073709551504#64 →
        (M.setMem (top + 18446744073709551504#64) v).getMem (top + c) = M.getMem (top + c) := by
  obtain ⟨h1, n1⟩ := hM.slot (a := top + 18446744073709551504#64) (v := v) slots (F := 144) hlim (by tn) (by tn)
  have rd : ∀ c : Word, c ≠ 18446744073709551504#64 →
      (M.setMem (top + 18446744073709551504#64) v).getMem (top + c) = M.getMem (top + c) := fun c hc =>
    MachineState.getMem_setMem_ne fun e => hc ((BitVec.add_right_inj top).1 e)
  refine ⟨h1, ?_, hP.mono (by rw [n1]), n1, rd⟩
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hB
  unfold CV
  rw [MachineState.getMem_setMem_eq, rd _ (by decide), rd _ (by decide), n1]
  exact ⟨hv, hb2, hb3, hb4, hb5, hb6⟩

set_option rv_sym.heap true in
/-- **The exit**: the coefficients' header copied into the slot, the epilogue, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 144 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 24) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 24) :
    ∀ R M, FinInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 172, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, hlen, ⟨hF, -, -, -⟩, hb1, hb2, hb3, hb4, hb5, hb6⟩ := id hinv
  have hlS := hwS.lt
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 144 ≤ top.toNat)]
  all_goals rw [hinv_2]
  · have o : ∀ k : Nat, k < 24 → SretOut Layouts.Vec.byteSize regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      ⟨by rw [toNat_add_ofNat (by omega)]; omega,
        by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega⟩
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF (by simpa using o 0 (by omega))
      (hwS.ne_next (Nat.le_refl _) (by omega))) (o 8 (by omega)) (hwS.ne_next_add (o := 8) (by omega)))
      (o 16 (by omega)) (hwS.ne_next_add (o := 16) (by omega))
  all_goals
    have hB : BufT env M (M.getMem (top + 18446744073709551488#64)) (M.getMem (top + 18446744073709551496#64)) 16 :=
      .inr ⟨hb4, by unfold Env.Live; omega, hb6⟩
  · exact (vecT_stores hwS haS hB hb2 hb1).1.2.1.2.2.1
  · exact (vecT_stores hwS haS hB hb2 hb1).1.2.1.2.2.2
  · rw [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq]; exact hb1
  · rw [(vecT_stores hwS haS hB hb2 hb1).2]; exact hlen
  · exact .inr (by rw [MachineState.getMem_setMem_eq]; exact hb3)

set_option rv_sym.heap true in
/-- **The powers' loop**, from its head: a power replaced by its Frobenius image (`frobenius_8`), then back to the
    head, or on to the passes' head (one pass fewer) or the exit; one power fewer left. -/
theorem frobs (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needF : Nat} (hnF : 144 + needF ≤ need) (hfr : Frobenius8T.specT env p L.frobenius8.idx needF)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {q : Word} {k : Nat} (hn16 : 16 * (regs .x13).toNat < 2 ^ 32)
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 172, ret, top⟩ :: rest, R, M⟩)
    (hloop : ∀ R M, 2 ≤ k → OInv env ret top regs m q (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 96, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, FInv env ret top regs m q k j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 152, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (FInv env ret top regs m q k) fun j R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, -, h22, h23, h25, -, hk1, hk8, h480, h504, hP, hM, hB, hj1, hjn, h8⟩ := id hI
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hP.resolve_left (by omega)
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_introT hI
  rv_symT hp stop [152, 96, 172] through [92] with [hL, hlim] using [Frobenius8SafeT.frobSafe hfr]
  all_goals
    obtain ⟨hM1, hB1, hP1, rd1⟩ := call_ok hlim hM hB hP hret1_14 keep1_1 hret1_16 hret1_15
    have hn1 := hret1_14.1
    have e8 : (R .x8 + 8#64).toNat = (R .x8).toNat + 8 := toNat_add_ofNat (by omega)
    obtain ⟨hM2, hB2, hP2, hn2, rd2⟩ := heap_ok (a := R .x8) hlim hM1 hB1 hP1 (by omega) (by omega) (r1 .x10)
    obtain ⟨hM3, hB3, hP3, hn3, rd3⟩ := heap_ok (a := R .x8 + 8#64) hlim hM2 hB2 hP2 (by omega)
      (by rw [hn2]; omega) (r1 .x11)
    have r : ∀ c : Word, ∀ d, c.toNat + d = 2 ^ 64 → d ≤ 144 →
        ((m1.setMem (R .x8) (r1 .x10)).setMem (R .x8 + 8#64) (r1 .x11)).getMem (top + c) = M.getMem (top + c) :=
      fun c d hc' hd => by
        have e : (top + c).toNat = top.toNat - d := by rw [BitVec.toNat_add]; omega
        rw [rd3 c (by omega), rd2 c (by omega), rd1 c (by omega)]
  -- back to the head
  · have hj2 : 2 ≤ j := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega)]; omega))
    refine ih (j - 1) _ _ (by omega) ⟨rfl, rfl, rfl, rfl, h22, h23, h25, rfl, hk1, hk8, ?_, ?_, hP3, hM3, hB3,
      by omega, by omega, ?_⟩
    all_goals try simp only [Tactic.rf]
    · rw [r _ 136 rfl (by omega)]; exact h480
    · rw [r _ 112 rfl (by omega)]; exact h504
    · rw [toNat_add_ofNat (by omega)]; omega
  -- the last pass: the exit
  · have h := congrArg BitVec.toNat hc
    rw [toNat_add_ofNat (by omega), BitVec.toNat_ofNat] at h
    refine hfin _ _ ⟨rfl, ?_, ?_, hM3, hB3⟩
    · rw [r _ 136 rfl (by omega)]; exact h480
    · rw [r _ 112 rfl (by omega), h504]
      have : k = 1 := by omega
      subst this; rfl
  -- the passes' head, one pass fewer
  · have hk2 : 2 ≤ k := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega), BitVec.toNat_ofNat]; omega))
    refine hloop _ _ hk2 ⟨rfl, rfl, rfl, rfl, ?_, h23, h25, rfl, by omega, by omega, ?_, ?_, hP3, hM3, hB3⟩
    all_goals try simp only [Tactic.rf]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [r _ 136 rfl (by omega)]; exact h480
    · rw [r _ 112 rfl (by omega), h504]
      congr 1; omega

set_option rv_sym.heap true in
/-- **The products' loop**, from its head: `f[p] * g_b` (`E::mul`) stored after the coefficients, then back to the
    head, or the length stored and on to the powers' loop; one product fewer left. -/
theorem prods (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needU : Nat} (hnU : 144 + needU ≤ need) (hmul : Field.EMulT.specT env p L.mul.idx needU)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {q : Word} {k : Nat} (hn16 : 16 * (regs .x13).toNat < 2 ^ 32)
    (hfr : ∀ j R M, FInv env ret top regs m q k j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 152, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, MInv env ret top regs m q k j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 126, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (MInv env ret top regs m q k) fun j R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, h22, h23, h25, -, hk1, hk8, h480, h504, hP, hM, hB⟩, h27, hj1, hjn, h24, h8, hroom⟩ := id hI
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hP.resolve_left (by omega)
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := id hB
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  rv_introT hI
  have hrn : (regs .x13).toNat ≤ (9 - k) * (regs .x13).toNat := Nat.le_mul_of_pos_left _ (by omega)
  rv_symT hp stop [126, 152] with [hL, hlim] using [hmul]
  all_goals
    have hhe := hW.heapEnd_le
    have e8 : (R .x8 + 18446744073709551608#64).toNat = (R .x8).toNat - 8 := by tn
  all_goals
    rw [← hret1_16, ← hret1_17]
    obtain ⟨hM1, hB1, hP1, rd1⟩ := call_ok hlim hM hB hP hret1_14 keep1_1 hret1_18 hret1_15
    have hn1 := hret1_14.1
    have g496 := rd1 18446744073709551496#64 (by tn)
    obtain ⟨hM2, hB2, hP2, hn2, rd2⟩ := heap_ok (a := R .x8 + 18446744073709551608#64) hlim hM1 hB1 hP1
      (by rw [e8]; omega) (by rw [e8]; omega) (r1 .x10)
    obtain ⟨hM3, hB3, hP3, hn3, rd3⟩ := heap_ok (a := R .x8) hlim hM2 hB2 hP2 (by omega)
      (by rw [hn2]; omega) (r1 .x11)
    have r : ∀ c : Word, ∀ d, c.toNat + d = 2 ^ 64 → d ≤ 144 →
        ((m1.setMem (R .x8 + 18446744073709551608#64) (r1 .x10)).setMem (R .x8) (r1 .x11)).getMem (top + c) =
          M.getMem (top + c) :=
      fun c d hc' hd => by
        have e : (top + c).toNat = top.toNat - d := by rw [BitVec.toNat_add]; omega
        rw [rd3 c (by omega), rd2 c (by omega), rd1 c (by omega)]
  -- back to the head
  · have hj2 : 2 ≤ j := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega)]; omega))
    refine ih (j - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, h22, h23, h25, rfl, hk1, hk8, ?_, ?_, hP3, hM3, hB3⟩,
      h27, by omega, by omega, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    · rw [r _ 136 rfl (by omega)]; exact h480
    · rw [r _ 112 rfl (by omega)]; exact h504
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega), r _ 120 rfl (by omega)]; omega
    · rw [r _ 128 rfl (by omega)]; exact hroom
  -- the products done: the length stored, on to the powers' loop
  · have hjj : j = 1 := Nat.le_antisymm (Nat.le_of_not_lt fun h => by
      have := congrArg BitVec.toNat hc; rw [toNat_add_ofNat (by omega)] at this; omega) hj1
    subst hjj
    obtain ⟨hM4, hB4, hP4, hn4, rd4⟩ := len_ok (v := R .x27) hlim hM3 hB3 hP3
      (by rw [r _ 128 rfl (by omega)]; omega)
    refine hfr (regs .x13).toNat _ _ ⟨rfl, rfl, rfl, rfl, h22, h23, h25, rfl, hk1, hk8, ?_, ?_, hP4, hM4, hB4,
      by omega, Nat.le_refl _, ?_⟩
    all_goals try simp only [Tactic.rf]
    · rw [rd4 _ (by decide), r _ 136 rfl (by omega)]; exact h480
    · rw [MachineState.getMem_setMem_eq]; exact h27

set_option rv_sym.heap true in
/-- **The passes**, from their head: `f[p]` read, `g.len` more coefficients `reserve`d, then the products' loop, or
    for an empty `g` the next pass or the exit; one pass fewer left after each. -/
theorem outer (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR : Nat} (hnR : 144 + needR ≤ need) (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {q : Word} (hn16 : 16 * (regs .x13).toNat < 2 ^ 32) (hwf : InWin env (regs .x11) 128)
    (haf : (regs .x11).toNat % 8 = 0)
    (hfin : ∀ R M, FinInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 172, ret, top⟩ :: rest, R, M⟩)
    (hin : ∀ k, (∀ R M, 2 ≤ k → OInv env ret top regs m q (k - 1) R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 96, ret, top⟩ :: rest, R, M⟩) →
      ∀ j R M, MInv env ret top regs m q k j R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 126, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, OInv env ret top regs m q k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 96, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env ret top regs m q) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, -, h22, h23, h25, -, hk1, hk8, h480, h504, hP, hM, hB⟩ := id hI
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := id hB
  have hnM := hM.1.2.1
  have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
  have hwl := hwf.lt
  obtain ⟨bc, bp, -, -, -⟩ := hdr top M
  rv_introT hI
  have hfa : (regs .x11 + R .x22).toNat = (regs .x11).toNat + 16 * (8 - k) := by
    rw [BitVec.toNat_add, h22]; omega
  have hd0 := hwf.dword hW haf hfa (by omega) (by omega)
  have hd8 := hwf.dword_add (k := 8) hW haf hfa (by omega) (by omega)
  rv_symT hp stop [96, 126, 172] through [92] with [hL, hlim] using [hres]
  -- `reserve`'s precondition
  all_goals try simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]
  · rw [bc, bp]; exact .inr (by unfold Env.Live; omega)
  · rw [bc]; exact hb2
  · rw [bc, bp]; exact .inr ⟨hb4, by unfold Env.Live; omega, hb6⟩
  · rw [bc]; exact hb2
  all_goals
    obtain ⟨hM1, hB1, hP1, hroom, g504, rd1⟩ := res_ok (n := (regs .x13).toNat) hlim hM hB hP hret1_14
      (fun a ha => by
        simp only [GrowOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, bc, bp] at ha
        exact ha) keep1_1 hret1_25 hret1_15 hret1_16 hret1_17 hret1_18 hret1_22 hret1_23
    have r : ∀ c : Word, ∀ d, c.toNat + d = 2 ^ 64 → d ≤ 144 → d ≠ 128 → d ≠ 120 →
        m1.getMem (top + c) = M.getMem (top + c) := fun c d hc' hd h1 h2 => by
      have e : (top + c).toNat = top.toNat - d := by rw [BitVec.toNat_add]; omega
      exact rd1 c (by omega) (by omega) (by omega)
  -- `g` empty, the last pass: the exit
  · have h := congrArg BitVec.toNat hc
    rw [toNat_add_ofNat (by omega), BitVec.toNat_ofNat] at h
    have hn0 : (regs .x13).toNat = 0 := by rw [hc_1]; rfl
    refine hfin _ _ ⟨rfl, ?_, ?_, hM1, hB1⟩
    · rw [r _ 136 rfl (by omega) (by omega) (by omega)]; exact h480
    · rw [r _ 112 rfl (by omega) (by omega) (by omega), h504, hn0, Nat.mul_zero, Nat.mul_zero]
  -- `g` empty: the next pass
  · have hn0 : (regs .x13).toNat = 0 := by rw [hc_1]; rfl
    have hk2 : 2 ≤ k := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega), BitVec.toNat_ofNat]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨rfl, rfl, rfl, rfl, ?_, h23, h25, rfl, by omega, by omega, ?_, ?_, hP1, hM1,
      hB1⟩
    all_goals try simp only [Tactic.rf]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [r _ 136 rfl (by omega) (by omega) (by omega)]; exact h480
    · rw [r _ 112 rfl (by omega) (by omega) (by omega), h504, hn0, Nat.mul_zero, Nat.mul_zero]
  -- the products' loop
  · have hn0 : (regs .x13).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hP.resolve_left hn0
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := id hB1
    have e9 : (9 - k) * (regs .x13).toNat = (8 - k) * (regs .x13).toNat + (regs .x13).toNat := by
      rw [show 9 - k = (8 - k) + 1 by omega, Nat.add_mul, Nat.one_mul]
    have hl : (m1.getMem (top + 18446744073709551504#64)).toNat = (8 - k) * (regs .x13).toNat := by rw [g504, h504]
    have hs4 := shl4 (x := m1.getMem (top + 18446744073709551504#64)) (by omega)
    refine hin k (fun R' M' h2 h' => ih (k - 1) R' M' (by omega) h') (regs .x13).toNat _ _ ⟨⟨rfl, rfl, rfl, rfl, h22,
      h23, h25, rfl, hk1, hk8, ?_, ?_, hP1, hM1, hB1⟩, ?_, by omega, Nat.le_refl _, ?_, ?_, ?_⟩
    all_goals try simp only [Tactic.rf]
    · rw [r _ 136 rfl (by omega) (by omega) (by omega)]; exact h480
    · rw [g504]; exact h504
    · rw [BitVec.toNat_add, hl]; omega
    · rw [toNat_add_ofNat (by omega)]
    · rw [toNat_add_ofNat (by rw [BitVec.toNat_add, hs4]; omega), BitVec.toNat_add, hs4]; omega
    · omega

set_option rv_sym.heap true in
/-- **`ring_coefficients` is total**: the coefficients allocated with capacity `64` (`handle_error` when `alloc`
    fails), `powers` copied from `g` into a block allocated for it (`handle_error` when `alloc` fails), then the
    passes. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR needA needH needU needF needM : Nat} (hnR : 144 + needR ≤ need) (hnA : 144 + needA ≤ need)
    (hnH : 144 + needH ≤ need) (hnU : 144 + needU ≤ need) (hnF : 144 + needF ≤ need) (hnM : 144 + needM ≤ need)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hhe : Aborts env p L.handleError.idx needH) (hmul : Field.EMulT.specT env p L.mul.idx needU)
    (hfr : Frobenius8T.specT env p L.frobenius8.idx needF)
    (hcp : Runtime.MemcpyT.MemcpySpecT env p L.memcpy.idx needM) :
    specT env p i need := by
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)]
  have hn16 : 16 * (regs .x13).toNat < 2 ^ 32 := by
    rcases hpre_12 with h | ⟨h, -⟩
    · omega
    · unfold InWin at h; have := hpre_14.heapEnd_le; omega
  have hfin := fin_ok env p i L hp (by omega) hk hpre_3 hpre_13 hpre_14 hpre_6 hpre_7 (hpre_2 ▸ ⟨hpre_8, hpre_9⟩)
  have hout := fun q => outer env p i L hp hL hnR hres hstop hpre_3 hpre_13 hpre_14 (q := q) hn16 hpre_10 hpre_11 hfin
    fun k hl => prods env p i L hp hL hnU hmul hpre_3 hpre_13 hpre_14 hn16
      (frobs env p i L hp hL hnF hfr hpre_3 hpre_13 hpre_14 hn16 hfin hl)
  clear hfin
  rv_symT hp stop [96] with [hL, (by omega : env.stackLimit.toNat + 144 ≤ top.toNat)] using [hac, hhe, hcp]
  all_goals
    have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
    have hs4 : (regs .x13 <<< 4).toNat = 16 * (regs .x13).toNat := shl4 (by omega)
    have hlay := env.layout
    have hn1 := hret1_14.1
    have hn1' := hret1_14.2.1
    have hge := hpre_14.next_ge
  -- `g` empty: `powers` dangling
  · have h0 : (regs .x13).toNat = 0 := by have := congrArg BitVec.toNat hc; simpa using this
    refine hout 8#64 8 _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, .inl h0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rv_closeT
    obtain ⟨r488, r496, rn⟩ := hdr_stores (c := 64#64) (q := r1 .x10) (s := regs .x10) (X := m1) hlim
    rw [r488, r496, rn]
    have := hret1_18
    simp only [BitVec.toNat_ofNat] at this ⊢
    omega
  all_goals
    have hn0 : (regs .x13).toNat ≠ 0 := fun h => ‹¬ regs .x13 = 0#64› (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    obtain ⟨hg, hgo, hgl⟩ := hpre_12.resolve_left hn0
    have hgw := hg.lt
    rw [hpre_2] at hgo
  -- `alloc`'s and `memcpy`'s preconditions
  · rw [hs4]; omega
  · rw [hs4]; exact hgw
  · intro _ b h1 h2
    unfold InRange at h1 h2
    rw [hs4] at h1 h2
    have h3 := hret3_14.2.1
    have h16 := hret3_16
    have h18 := hret3_18
    rw [hs4] at h18
    omega
  · have h3 := hret3_14.2.1
    have h16 := hret3_16
    have h18 := hret3_18
    rw [hs4] at h18 ⊢
    refine .inr ⟨.inl ⟨by omega, by omega⟩, .inl (by omega), hg.inWindow hpre_14, ?_⟩
    rcases hgo with h | h
    · exact .inl (by omega)
    · have e472 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
      exact .inr (by omega)
  -- `powers` copied from `g`
  · have e472 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
    have h3 := hret3_14.2.1
    have h18 := hret3_18
    rw [hs4] at h18
    have rd5 : ∀ c : Word, top.toNat - 144 ≤ (top + c).toNat → m5.getMem (top + c) = m3.getMem (top + c) :=
      fun c h => keep5_1 _ (Tactic.le_of_toNat (by omega)) fun ho => by
        simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] at ho
        rw [toNat_alignToDword, hs4] at ho
        omega
    refine hout (r3 .x10) 8 _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, .inr ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) only [rd5]
    all_goals try rv_closeT
    all_goals simp only [Tactic.rf]
    · rw [BitVec.toNat_add, hs4]; omega
    · rw [BitVec.toNat_add, BitVec.toNat_add, hs4, BitVec.toNat_ofNat]; omega

end Rv64mc.Proof.Whir.RingCoefficientsT

/-- info: 'Rv64mc.Proof.Whir.RingCoefficientsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.RingCoefficientsT.total
