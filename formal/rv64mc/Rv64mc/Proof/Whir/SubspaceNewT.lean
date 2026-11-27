/-
  Rv64mc.Proof.Whir.SubspaceNewT

  `<verifier::whir::Subspace>::new(log_n) -> Subspace` is total (`specT`): from a result's slot of `48` bytes owned, in
  a window, 8-byte aligned (`log_n` anything), it returns with the slot two vectors of `K`s (`roots` at `+0`,
  `inverses` at `+24`, each `VecT`) of `log_n + 1` elements, their buffers allocated since the entry, writing at most
  the slot besides its stack and what it allocates (`SretOut`, the partial contract's), or the run ends with `a0 = 2`
  where `subspace_roots`, `alloc` (through `handle_error`) or `reserve` does. Safety only: the partial contract's
  values (`Spec/Whir/Subspace.lean`'s `NewPost`, `Model.SubspaceRust.new`) are owed. It has no partial proof
  (class C).

  The code builds `roots` (`subspace_roots`, its header at `top - 104`), allocates `inverses` with capacity
  `roots.len` (its header at `top - 80`), `reserve`s `roots.len` (the room is there), and stores `K::inv` of each root
  (loop at instruction 104, `loop`, `Total.loop` with the roots left as measure), then copies both headers into the
  slot (instruction 118, `fin_ok`). `roots.len = log_n + 1` is never `0`: the paths for an empty `roots` are refuted.
  Each part keeps `SavedT.MemOk` with the seven saved registers' slots (`Mem`), `s6` to `s11` (`Keep`) and the roots'
  header (`RT`).

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `Mem`, `Keep`, `RT`, `IB`, `RInv`, `LInv`, `FInv`

  ## Main results

  * `slots`, `RT.keep`, `IB.mono`, `call_ok`, `hdrI`, `res_ok`, `heap_ok`, `fin_ok`, `loop`, `mid`, `total`
-/

import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Proof.Field.KInvT
import Rv64mc.Proof.Whir.SubspaceRootsT
import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Whir.VecWordT
import Rv64mc.Spec.Whir.Subspace
import Rv64mc.Gen.Tmpl.Verifier.Whir.Subspace.New

namespace Rv64mc.Proof.Whir.SubspaceNewT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Whir.VecWordT (vecT_stores shl3 ovf)
open Rv64mc.Gen.Verifier.Whir.Subspace.New (Link tmpl)

/-- The total precondition: the result's slot (`48` bytes) in a window, 8-byte aligned, owned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 48 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 48

/-- The total postcondition: the slot's `roots` (at `+0`) and `inverses` (at `+24`) vectors of `K`s of
    `log_n + 1` elements, their buffers allocated since the entry. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 8 ∧ (vecLen m' (regs .x10)).toNat = (regs .x11).toNat + 1 ∧
    (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat ∧
    VecT env m' (regs .x10 + 24#64) 8 ∧ (vecLen m' (regs .x10 + 24#64)).toNat = (regs .x11).toNat + 1 ∧
    (env.next m).toNat ≤ (vecPtr m' (regs .x10 + 24#64)).toNat

/-- **The total contract of `Subspace::new`**: `PreT` to `PostT`, writing at most the slot (`SretOut`, the partial
    contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (SretOut Layouts.Subspace.byteSize) (Stop := AbortStop)

/-- What every part keeps of memory: `SavedT.MemOk` with the seven saved registers' slots, from `top - 8` (the
    return address) down to `top - 56` (`s5`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (SretOut Layouts.Subspace.byteSize regs m)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20, regs .x21] m M

/-- The saved slots lie in the `56` bytes below `top`. -/
theorem slots : SlotsIn 56
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64] := slots_le

/-- The callee-saved registers the function never saves (`s6` to `s11`), as at the entry. -/
def Keep (regs R : Reg → Word) : Prop :=
  R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27

/-- The roots' header at `top - 104` (capacity, pointer at `top - 96`, length `n` at `top - 88`): `n` at most the
    capacity, the buffer of fewer than `2^63` bytes, allocated since the entry, below `NEXT`, 8-byte aligned. -/
def RT (env : Env) (m : MachineState) (top : Word) (n : Nat) (M : MachineState) : Prop :=
  (M.getMem (top + 18446744073709551528#64)).toNat = n ∧ n ≤ (M.getMem (top + 18446744073709551512#64)).toNat ∧
    (M.getMem (top + 18446744073709551512#64)).toNat * 8 < 2 ^ 63 ∧
    (env.next m).toNat ≤ (M.getMem (top + 18446744073709551520#64)).toNat ∧
    0x10000000 ≤ (M.getMem (top + 18446744073709551520#64)).toNat ∧
    (M.getMem (top + 18446744073709551520#64)).toNat + 8 * (M.getMem (top + 18446744073709551512#64)).toNat ≤
      (env.next M).toNat ∧
    (M.getMem (top + 18446744073709551520#64)).toNat % 8 = 0

/-- The inverses' block `q` of `n` words: allocated since the entry, below `NEXT`, 8-byte aligned. -/
def IB (env : Env) (m : MachineState) (n : Nat) (q : Word) (M : MachineState) : Prop :=
  (env.next m).toNat ≤ q.toNat ∧ 0x10000000 ≤ q.toNat ∧ q.toNat + 8 * n ≤ (env.next M).toNat ∧ q.toNat % 8 = 0

/-- After `subspace_roots` (instruction 24): the stack pointer, the slot's address in `x8`, `Keep`, `Mem`, `RT` of
    `log_n + 1` roots. -/
def RInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x10 ∧ Keep regs R ∧ Mem env ret top regs m M ∧
    RT env m top ((regs .x11).toNat + 1) M

/-- The loop's head (instruction 104), `j` roots left of `n`: `RInv`'s stack pointer, slot's address, `Keep`, `n` in
    `x18` and `x20`, the roots' cursor `x19` and end `x9`, the inverses' cursor `x21` (`q + 8 (n - j)`); the
    inverses' header at `top - 80` (capacity `n`, pointer `q`); `IB`, `Mem`, `RT`. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (j : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x10 ∧ Keep regs R ∧
    (R .x18).toNat = (regs .x11).toNat + 1 ∧ (R .x20).toNat = (regs .x11).toNat + 1 ∧
    (R .x19).toNat + 8 * j = (M.getMem (top + 18446744073709551520#64)).toNat + 8 * ((regs .x11).toNat + 1) ∧
    (R .x9).toNat = (M.getMem (top + 18446744073709551520#64)).toNat + 8 * ((regs .x11).toNat + 1) ∧
    (R .x21).toNat + 8 * j = q.toNat + 8 * ((regs .x11).toNat + 1) ∧ 1 ≤ j ∧ j ≤ (regs .x11).toNat + 1 ∧
    (M.getMem (top + 18446744073709551536#64)).toNat = (regs .x11).toNat + 1 ∧
    M.getMem (top + 18446744073709551544#64) = q ∧ IB env m ((regs .x11).toNat + 1) q M ∧
    Mem env ret top regs m M ∧ RT env m top ((regs .x11).toNat + 1) M

/-- The exit (instruction 118): `LInv`'s stack pointer, slot's address, `Keep`, length `n` in `x20`, the inverses'
    header; `IB`, `Mem`, `RT`. -/
def FInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x10 ∧ Keep regs R ∧
    (R .x20).toNat = (regs .x11).toNat + 1 ∧
    (M.getMem (top + 18446744073709551536#64)).toNat = (regs .x11).toNat + 1 ∧
    M.getMem (top + 18446744073709551544#64) = q ∧ IB env m ((regs .x11).toNat + 1) q M ∧
    Mem env ret top regs m M ∧ RT env m top ((regs .x11).toNat + 1) M

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- **`RT` kept** by a memory agreeing on the header's three words, `NEXT` not lowered. -/
theorem RT.keep {env : Env} {m M X : MachineState} {top : Word} {n : Nat} (h : RT env m top n M)
    (hn : (env.next M).toNat ≤ (env.next X).toNat) (hlim : 112 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 104 ≤ a.toNat → a.toNat < top.toNat - 80 → X.getMem a = M.getMem a) :
    RT env m top n X := by
  unfold RT at h ⊢
  rw [hk _ (by tn) (by tn), hk _ (by tn) (by tn), hk _ (by tn) (by tn)]
  omega

/-- `IB` kept, `NEXT` not lowered. -/
theorem IB.mono {env : Env} {m M X : MachineState} {n : Nat} {q : Word} (h : IB env m n q M)
    (hn : (env.next M).toNat ≤ (env.next X).toNat) : IB env m n q X :=
  ⟨h.1, h.2.1, by have := h.2.2.1; omega, h.2.2.2⟩

/-- **Across a callee writing nothing of the caller's** (`m1`, from the stack pointer `top - 112`): `Mem`, `RT`
    kept, `NEXT` not lowered, every word of the frame read as before. -/
theorem call_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState} {n : Nat}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hM : Mem env ret top regs m M) (hR : RT env m top n M)
    (hf : env.Frame (top + 18446744073709551504#64) (fun _ => False) M m1)
    (hk : ∀ a : Word, top + 18446744073709551504#64 ≤ a → m1.getMem a = M.getMem a) (hc : m1.code = M.code)
    (hs : env.Static m1) :
    Mem env ret top regs m m1 ∧ RT env m top n m1 ∧ (env.next M).toNat ≤ (env.next m1).toNat ∧
      ∀ a : Word, top.toNat - 112 ≤ a.toNat → m1.getMem a = M.getMem a := by
  have e : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by tn
  have rd : ∀ a : Word, top.toNat - 112 ≤ a.toNat → m1.getMem a = M.getMem a := fun a h =>
    hk a (Tactic.le_of_toNat (by omega))
  exact ⟨hM.call slots (by omega) (by omega) hf hc hs (fun _ h => h.elim) fun a h1 _ => rd a (by omega),
    hR.keep hf.1 (by omega) fun a h1 _ => rd a (by omega), hf.1, rd⟩

/-- **Across `subspace_roots`** (`m1`, from the stack pointer `top - 112`, writing at most the roots' header): `Mem`
    kept, every saved slot read as before. -/
theorem roots_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hM : Mem env ret top regs m M)
    (hf : env.Frame (top + 18446744073709551504#64) out M m1)
    (hout : ∀ a, out a → top.toNat - 104 ≤ a.toNat ∧ a.toNat < top.toNat - 80)
    (hk : ∀ a : Word, top + 18446744073709551504#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1) : Mem env ret top regs m m1 := by
  have hlay := env.layout
  have e : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by tn
  exact hM.call slots (by omega) (by omega) hf hc hs
    (fun a ha => Tactic.mw_stack (by have := hout a ha; omega)) fun a h1 h2 =>
      hk a (Tactic.le_of_toNat (by omega)) fun h => by have := hout a h; omega

/-- The roots' header words (at `top - 104`) as `vecCap`, `vecPtr`, `vecLen` name them. -/
theorem hdrR (top : Word) (M : MachineState) :
    rvCapAt (top + 18446744073709551512#64) = top + 18446744073709551512#64 ∧
      rvPtrAt (top + 18446744073709551512#64) = top + 18446744073709551520#64 ∧
      vecCap M (top + 18446744073709551512#64) = M.getMem (top + 18446744073709551512#64) ∧
      vecPtr M (top + 18446744073709551512#64) = M.getMem (top + 18446744073709551520#64) ∧
      vecLen M (top + 18446744073709551512#64) = M.getMem (top + 18446744073709551528#64) := by
  refine ⟨Runtime.GrowOne.rvCapAt_eq _, ?_, Runtime.VecHdrT.vecCap_eq _ _, ?_, ?_⟩
  · unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
  · unfold vecPtr; rw [BitVec.add_assoc]; rfl
  · unfold vecLen; rw [BitVec.add_assoc]; rfl

/-- The inverses' header words (at `top - 80`) as `rvCapAt`, `rvPtrAt`, `vecCap`, `vecPtr`, `vecLen` name them. -/
theorem hdrI (top : Word) (M : MachineState) :
    rvCapAt (top + 18446744073709551536#64) = top + 18446744073709551536#64 ∧
      rvPtrAt (top + 18446744073709551536#64) = top + 18446744073709551544#64 ∧
      vecCap M (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551536#64) ∧
      vecPtr M (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551544#64) ∧
      vecLen M (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551552#64) := by
  refine ⟨Runtime.GrowOne.rvCapAt_eq _, ?_, Runtime.VecHdrT.vecCap_eq _ _, ?_, ?_⟩
  · unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
  · unfold vecPtr; rw [BitVec.add_assoc]; rfl
  · unfold vecLen; rw [BitVec.add_assoc]; rfl

/-- The inverses' header `(c, q, 0)` stored at `top - 80` to `top - 64`: `Mem`, `RT` kept, the words read back,
    `NEXT` kept. -/
theorem hdr_stores {env : Env} {ret top c q : Word} {regs : Reg → Word} {m X : MachineState} {n : Nat}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hM : Mem env ret top regs m X) (hR : RT env m top n X) :
    Mem env ret top regs m (((X.setMem (top + 18446744073709551536#64) c).setMem (top + 18446744073709551544#64)
      q).setMem (top + 18446744073709551552#64) 0#64) ∧
    RT env m top n (((X.setMem (top + 18446744073709551536#64) c).setMem (top + 18446744073709551544#64)
      q).setMem (top + 18446744073709551552#64) 0#64) ∧
    (((X.setMem (top + 18446744073709551536#64) c).setMem (top + 18446744073709551544#64) q).setMem
        (top + 18446744073709551552#64) 0#64).getMem (top + 18446744073709551536#64) = c ∧
      (((X.setMem (top + 18446744073709551536#64) c).setMem (top + 18446744073709551544#64) q).setMem
        (top + 18446744073709551552#64) 0#64).getMem (top + 18446744073709551544#64) = q ∧
      (((X.setMem (top + 18446744073709551536#64) c).setMem (top + 18446744073709551544#64) q).setMem
        (top + 18446744073709551552#64) 0#64).getMem (top + 18446744073709551552#64) = 0#64 ∧
      env.next (((X.setMem (top + 18446744073709551536#64) c).setMem (top + 18446744073709551544#64) q).setMem
        (top + 18446744073709551552#64) 0#64) = env.next X ∧
      (((X.setMem (top + 18446744073709551536#64) c).setMem (top + 18446744073709551544#64) q).setMem
        (top + 18446744073709551552#64) 0#64).getMem (top + 18446744073709551520#64) =
          X.getMem (top + 18446744073709551520#64) := by
  have hlay := env.layout
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b h => Tactic.ne_of_toNat h
  have e1 : (top + 18446744073709551536#64).toNat = top.toNat - 80 := by tn
  have e2 : (top + 18446744073709551544#64).toNat = top.toNat - 72 := by tn
  have e3 : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by tn
  obtain ⟨h1, n1⟩ := hM.slot (a := top + 18446744073709551536#64) (v := c) slots hlim (by omega) (by omega)
  obtain ⟨h2, n2⟩ := h1.slot (a := top + 18446744073709551544#64) (v := q) slots hlim (by omega) (by omega)
  obtain ⟨h3, n3⟩ := h2.slot (a := top + 18446744073709551552#64) (v := 0#64) slots hlim (by omega) (by omega)
  have e4 : (top + 18446744073709551520#64).toNat = top.toNat - 96 := by tn
  refine ⟨h3, hR.keep (by rw [n3, n2, n1]) (by omega) fun a h1 h2 => ?_, ?_, ?_, MachineState.getMem_setMem_eq,
    by rw [n3, n2, n1], ?_⟩
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega))]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega))]

/-- **After `reserve(k)` of the inverses with the room** (`k` at most the capacity less the length, `m1`): `Mem`,
    `RT` kept, `NEXT` not lowered, the header's three words and every word of the frame outside them read as
    before. -/
theorem res_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    {n k : Nat} (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hM : Mem env ret top regs m M)
    (hR : RT env m top n M) (hf : env.Frame (top + 18446744073709551504#64) out M m1)
    (hout : ∀ a, out a → a = top + 18446744073709551536#64 ∨ a = top + 18446744073709551544#64)
    (hk : ∀ a : Word, top + 18446744073709551504#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1)
    (hlen : vecLen m1 (top + 18446744073709551536#64) = vecLen M (top + 18446744073709551536#64))
    (hroom : k ≤ (vecCap M (top + 18446744073709551536#64)).toNat - (vecLen M (top + 18446744073709551536#64)).toNat →
      vecCap m1 (top + 18446744073709551536#64) = vecCap M (top + 18446744073709551536#64) ∧
        vecPtr m1 (top + 18446744073709551536#64) = vecPtr M (top + 18446744073709551536#64))
    (hr : k ≤ (M.getMem (top + 18446744073709551536#64)).toNat - (M.getMem (top + 18446744073709551552#64)).toNat) :
    Mem env ret top regs m m1 ∧ RT env m top n m1 ∧ (env.next M).toNat ≤ (env.next m1).toNat ∧
      m1.getMem (top + 18446744073709551536#64) = M.getMem (top + 18446744073709551536#64) ∧
      m1.getMem (top + 18446744073709551544#64) = M.getMem (top + 18446744073709551544#64) ∧
      m1.getMem (top + 18446744073709551552#64) = M.getMem (top + 18446744073709551552#64) ∧
      m1.getMem (top + 18446744073709551520#64) = M.getMem (top + 18446744073709551520#64) := by
  have hlay := env.layout
  have e504 : (top + 18446744073709551504#64).toNat = top.toNat - 112 := by tn
  have ho : ∀ a, out a → a.toNat = top.toNat - 80 ∨ a.toNat = top.toNat - 72 := fun a ha => by
    rcases hout a ha with rfl | rfl
    · exact .inl (by tn)
    · exact .inr (by tn)
  have rd : ∀ a : Word, top.toNat - 112 ≤ a.toNat → a.toNat ≠ top.toNat - 80 → a.toNat ≠ top.toNat - 72 →
      m1.getMem a = M.getMem a := fun a h1 h2 h3 =>
    hk a (Tactic.le_of_toNat (by omega)) fun h => by rcases ho a h with h | h <;> omega
  obtain ⟨-, -, bC, bP, bL⟩ := hdrI top m1
  obtain ⟨-, -, bC', bP', bL'⟩ := hdrI top M
  rw [bL, bL'] at hlen
  rw [bC', bL', bC, bP, bP'] at hroom
  refine ⟨hM.call slots (by omega) (by omega) hf hc hs
    (fun a ha => Tactic.mw_stack (by rcases ho a ha with h | h <;> omega)) fun a h1 h2 => rd a (by omega) (by omega)
      (by omega), hR.keep hf.1 (by omega) fun a h1 h2 => rd a (by omega) (by omega) (by omega), hf.1, (hroom hr).1,
    (hroom hr).2, hlen, rd _ (by tn) (by tn) (by tn)⟩

/-- **A store into the inverses' block**: `Mem`, `RT`, `IB` kept, `NEXT` kept, every word of the stack read as
    before. -/
theorem heap_ok {env : Env} {ret top a q : Word} {regs : Reg → Word} {m M : MachineState} {n k : Nat}
    (hlim : env.stackLimit.toNat + 112 ≤ top.toNat) (hM : Mem env ret top regs m M) (hR : RT env m top n M)
    (hB : IB env m k q M) (hlo : q.toNat ≤ a.toNat) (hhi : a.toNat + 8 ≤ q.toNat + 8 * k) (v : Word) :
    Mem env ret top regs m (M.setMem a v) ∧ RT env m top n (M.setMem a v) ∧ IB env m k q (M.setMem a v) ∧
      ∀ b : Word, env.stackLimit.toNat ≤ b.toNat → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  have hnM := hM.1.2.1
  obtain ⟨b1, b2, b3, b4⟩ := hB
  obtain ⟨h1, n1⟩ := hM.fresh (a := a) (v := v) slots (by omega) (by omega) (by omega)
  have rd : ∀ b : Word, env.stackLimit.toNat ≤ b.toNat → (M.setMem a v).getMem b = M.getMem b := fun b hb =>
    MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))
  exact ⟨h1, hR.keep (by rw [n1]) (by omega) fun x h1 _ => rd x (by omega), ⟨b1, b2, by rw [n1]; exact b3, b4⟩, rd⟩

set_option rv_sym.heap true in
/-- **After `subspace_roots`**: `roots.len` words' size checked (`handle_error` past `2^63` bytes), the inverses'
    block allocated (`handle_error` when `alloc` fails), its header `(n, q, 0)` stored at `top - 80` and `reserve`d
    (the room is there), then the loop's head with all `n` roots left. `n = log_n + 1` is never `0`, so the paths for
    an empty `roots` are refuted. -/
theorem mid (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needH needR : Nat} (hnA : 112 + needA ≤ need) (hnH : 112 + needH ≤ need) (hnR : 112 + needR ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hhe : Aborts env p L.handleError.idx needH)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 8 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hl : ∀ q R M, LInv env ret top regs m q ((regs .x11).toNat + 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 104, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, RInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 24, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hlay := env.layout
  obtain ⟨-, -, -, hM, hR⟩ := id hI
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := id hR
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  have hHE := hW.heapEnd_le
  have hge := hW.next_ge
  have hnM := hM.next_le
  rv_introT hI
  rv_symT hp stop [104, 118] with [hL, hlim] using [hac, hhe, hres]
  all_goals
    have h3 : (M.getMem (top + 18446744073709551528#64) <<< 3).toNat = 8 * (M.getMem
      (top + 18446744073709551528#64)).toNat := shl3 (by omega)
  -- `n = 0`, `n * 8 = 0`, `n` words past `2^63` bytes: refuted
  all_goals
    try first
    | (have := congrArg BitVec.toNat hc; simp only [BitVec.toNat_ofNat] at this; omega)
    | (have := congrArg BitVec.toNat hc_1; simp only [BitVec.toNat_ofNat] at this; omega)
    | (have := congrArg BitVec.toNat hc_2; simp only [BitVec.toNat_ofNat] at this; omega)
  all_goals
    obtain ⟨hM2, hR2, hn2, rd2⟩ := call_ok hlim hM hR hret2_14 keep2_1 hret2_19 hret2_15
    obtain ⟨hM2', hR2', s1, s2, s3, sn, s520⟩ := hdr_stores (c := M.getMem (top + 18446744073709551528#64))
      (q := r2 .x10) hlim hM2 hR2
    obtain ⟨bc, bp, -, -, -⟩ := hdrI top M
  -- `reserve(n)`'s precondition
  · rw [bc, bp, s1, s2]; exact .inr (by unfold Env.Live; rw [sn]; omega)
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [bc, s1]; omega
  · rw [bc, bp, s1, s2]; exact .inr ⟨by omega, by unfold Env.Live; rw [sn]; omega, hret2_17⟩
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; rw [bc, s1]; omega
  -- the loop's head
  · obtain ⟨hM3, hR3, hn3, g536, g544, g552, g520⟩ := res_ok (k := (M.getMem (top + 18446744073709551528#64)).toNat)
      hlim hM2' hR2' hret3_14 (fun a ha => by
        simp only [GrowOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, bc, bp] at ha
        exact ha) keep3_1 hret3_25 hret3_15 hret3_16 hret3_17 (by rw [s1, s3]; simp)
    rw [sn] at hn3
    rw [g552, s3, g544, s2]
    refine hl (r2 .x10) _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, by omega, Nat.le_refl _, ?_,
      by rw [g544, s2], ⟨by omega, by omega, by omega, hret2_17⟩, hM3, hR3⟩
    all_goals try simp only [Tactic.rf]
    · omega
    · rw [BitVec.add_zero]; omega
    · rw [g520, s520, rd2 _ (by tn)]
    · rw [g520, s520, rd2 _ (by tn), BitVec.toNat_add, h3]; omega
    · rw [BitVec.zero_shiftLeft, BitVec.add_zero]
    · rw [g536, s1]; omega

/-- The memory at the exit: both headers stored into the slot `s`, the inverses' length `v` at `t` (`top - 64`)
    among them, as the code orders the stores. -/
abbrev finMem (M : MachineState) (s t a b c d v e f : Word) : MachineState :=
  ((((((M.setMem s a).setMem (s + 8#64) b).setMem (s + 16#64) c).setMem (s + 24#64) d).setMem t v).setMem
    (s + 32#64) e).setMem (s + 40#64) f

/-- **The slot at the exit**: its six words read back, `NEXT` kept, the frame across the stores. -/
theorem fin_mem {env : Env} {M m : MachineState} {top s t a b c d v e f : Word} {out : Word → Prop}
    (hw : InWin env s 48) (ht : t.toNat + 8 ≤ s.toNat ∨ s.toNat + 48 ≤ t.toNat)
    (htl : env.stackLimit.toNat ≤ t.toNat) (htt : t.toNat < top.toNat) (hF : env.Frame top out m M)
    (ho : ∀ k : Nat, k < 48 → out (s + BitVec.ofNat 64 k)) :
    (finMem M s t a b c d v e f).getMem s = a ∧ (finMem M s t a b c d v e f).getMem (s + 8#64) = b ∧
      (finMem M s t a b c d v e f).getMem (s + 16#64) = c ∧ (finMem M s t a b c d v e f).getMem (s + 24#64) = d ∧
      (finMem M s t a b c d v e f).getMem (s + 32#64) = e ∧ (finMem M s t a b c d v e f).getMem (s + 40#64) = f ∧
      env.next (finMem M s t a b c d v e f) = env.next M ∧ env.Frame top out m (finMem M s t a b c d v e f) := by
  have hl := hw.lt
  have ek : ∀ k : Nat, k < 48 → (s + BitVec.ofNat 64 k).toNat = s.toNat + k := fun k hk => toNat_add_ofNat (by omega)
  have e8 := ek 8 (by omega)
  have e16 := ek 16 (by omega)
  have e24 := ek 24 (by omega)
  have e32 := ek 32 (by omega)
  have e40 := ek 40 (by omega)
  have ne : ∀ x y : Word, x.toNat ≠ y.toNat → x ≠ y := fun x y h => Tactic.ne_of_toNat h
  have nn : ∀ k : Nat, k < 48 → s + BitVec.ofNat 64 k ≠ env.nextAddr := fun k hk => hw.ne_next_add hk
  have n0 : s ≠ env.nextAddr := by simpa using nn 0 (by omega)
  have ntn : t ≠ env.nextAddr := Tactic.next_ne_of_stack htl
  have o0 : out s := by simpa using ho 0 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [finMem]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · simp only [finMem]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · simp only [finMem]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · simp only [finMem]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · simp only [finMem]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · simp only [finMem]
    rw [MachineState.getMem_setMem_eq]
  · simp only [finMem]
    rw [Tactic.next_setMem (by simpa using nn 40 (by omega)), Tactic.next_setMem (by simpa using nn 32 (by omega)),
      Tactic.next_setMem ntn, Tactic.next_setMem (by simpa using nn 24 (by omega)),
      Tactic.next_setMem (by simpa using nn 16 (by omega)), Tactic.next_setMem (by simpa using nn 8 (by omega)),
      Tactic.next_setMem n0]
  · simp only [finMem]
    refine Tactic.frame_out (Tactic.frame_out (Tactic.frame_slot (Tactic.frame_out (Tactic.frame_out
      (Tactic.frame_out (Tactic.frame_out hF o0 n0) (by simpa using ho 8 (by omega)) (by simpa using nn 8 (by omega)))
      (by simpa using ho 16 (by omega)) (by simpa using nn 16 (by omega))) (by simpa using ho 24 (by omega))
      (by simpa using nn 24 (by omega))) htl htt) (by simpa using ho 32 (by omega)) (by simpa using nn 32 (by omega)))
      (by simpa using ho 40 (by omega)) (by simpa using nn 40 (by omega))

set_option rv_sym.heap true in
/-- **The loop**, from its head: the next root's inverse (`K::inv`) stored in the inverses' block; back to the head,
    or on to the exit; one root fewer left. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needI : Nat} (hnI : 112 + needI ≤ need) (hinv : Field.KInvT.specT env p L.inv.idx needI)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m) {q : Word}
    (hfin : ∀ R M, FInv env ret top regs m q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, LInv env ret top regs m q j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 104, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m q) fun j R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, h18, h20, h19, h9, h21, hj1, hjn, h536, h544, hB, hM, hR⟩ := id hI
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := id hR
  obtain ⟨b1, b2, b3, b4⟩ := id hB
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  have hHE := hW.heapEnd_le
  have hnM := hM.next_le
  rv_introT hI
  rv_symT hp stop [104, 118] with [hL, hlim] using [hinv]
  all_goals
    obtain ⟨hM1, hR1, hn1, rd1⟩ := call_ok hlim hM hR hret1_14 keep1_1 hret1_17 hret1_15
    obtain ⟨hM2, hR2, hB2, rd2⟩ := heap_ok (a := R .x21) hlim hM1 hR1 (hB.mono hn1) (by omega) (by omega)
      (Model.kInv (M.getMem (R .x19)))
    have rd : ∀ c : Word, top.toNat - 112 ≤ (top + c).toNat →
        (m1.setMem (R .x21) (Model.kInv (M.getMem (R .x19)))).getMem (top + c) = M.getMem (top + c) :=
      fun c h => by rw [rd2 _ (by omega), rd1 _ h]
    have g536 := rd 18446744073709551536#64 (by tn)
    have g544 := rd 18446744073709551544#64 (by tn)
    have g520 := rd 18446744073709551520#64 (by tn)
  -- back to the head
  · have e8 : (R .x19 + 8#64).toNat = (R .x19).toNat + 8 := toNat_add_ofNat (by omega)
    have hj2 : 2 ≤ j := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by rw [e8]; omega))
    refine ih (j - 1) _ _ (by omega) ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, h18, h20, ?_, ?_, ?_, by omega,
      by omega, by rw [g536]; exact h536, by rw [g544]; exact h544, hB2, hM2, hR2⟩
    all_goals simp only [Tactic.rf]
    · rw [e8, g520]; omega
    · rw [g520]; exact h9
    · rw [toNat_add_ofNat (by omega)]; omega
  -- the exit
  · exact hfin _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, h20, by rw [g536]; exact h536, by rw [g544]; exact h544,
      hB2, hM2, hR2⟩

-- The epilogue's seven loads read through the six stores into the slot and the frame's store, each disequality
-- proved by the closer from the slot's `Owned`: one run of the executor over them exceeds the default budget.
set_option maxHeartbeats 1000000 in
set_option rv_sym.heap true in
/-- **The exit**: both headers stored into the slot (the inverses' length `n`), the epilogue, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 112 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (SretOut Layouts.Subspace.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 48) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 48) :
    ∀ q R M, FInv env ret top regs m q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩ := by
  intro q R M hI
  obtain ⟨-, -, -, h20, h536, h544, hB, hM, hR⟩ := id hI
  have hlS := hwS.lt
  have hlay := env.layout
  have hnM := hM.next_le
  obtain ⟨ho1, -⟩ := hoS
  have hHE := hW.heapEnd_le
  have hnx := hM.1.2.1
  obtain ⟨b1, b2, b3, b4⟩ := id hB
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := id hR
  have e552 : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by tn
  obtain ⟨f0, f8, f16, f24, f32, f40, fn, fF⟩ := fin_mem (M := M) (s := regs .x10)
    (t := top + 18446744073709551552#64) (a := M.getMem (top + 18446744073709551512#64))
    (b := M.getMem (top + 18446744073709551520#64)) (c := M.getMem (top + 18446744073709551528#64))
    (d := M.getMem (top + 18446744073709551536#64)) (v := R .x20) (e := M.getMem (top + 18446744073709551544#64))
    (f := R .x20) hwS (by omega) (by omega) (by omega) hM.1 fun k hk =>
      ⟨by rw [toNat_add_ofNat (by omega)]; omega,
        by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Subspace.byteSize]; omega⟩
  have c24 : rvCapAt (regs .x10 + 24#64) = regs .x10 + 24#64 := Runtime.GrowOne.rvCapAt_eq _
  have p0 : rvPtrAt (regs .x10) = regs .x10 + 8#64 := rfl
  have p24 : rvPtrAt (regs .x10 + 24#64) = regs .x10 + 32#64 := by unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
  have l0 : ∀ N, vecLen N (regs .x10) = N.getMem (regs .x10 + 16#64) := fun _ => rfl
  have l24 : ∀ N, vecLen N (regs .x10 + 24#64) = N.getMem (regs .x10 + 40#64) := fun _ => by
    unfold vecLen; rw [BitVec.add_assoc]; rfl
  have v0 : ∀ N, vecPtr N (regs .x10) = N.getMem (regs .x10 + 8#64) := fun _ => rfl
  have v24 : ∀ N, vecPtr N (regs .x10 + 24#64) = N.getMem (regs .x10 + 32#64) := fun _ => by
    unfold vecPtr; rw [BitVec.add_assoc]; rfl
  rv_introT hI
  rv_symT hp with [(by omega : env.stackLimit.toNat + 112 ≤ top.toNat)]
  all_goals simp only [Runtime.GrowOne.rvCapAt_eq, p0, p24, f0, fn, Env.Live]
  all_goals
    have h544' := congrArg BitVec.toNat h544
    try simp only [MachineState.getMem_setMem_eq]
    omega

set_option rv_sym.heap true in
/-- **`Subspace::new` is total**: the prologue, `subspace_roots` into the frame, then `mid`, the loop and the exit. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS needA needH needR needI : Nat} (hnS : 112 + needS ≤ need) (hnA : 112 + needA ≤ need)
    (hnH : 112 + needH ≤ need) (hnR : 112 + needR ≤ need) (hnI : 112 + needI ≤ need)
    (hroots : SubspaceRootsT.specT env p L.subspaceRoots.idx needS)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hhe : Aborts env p L.handleError.idx needH)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 8 p L.reserve.idx needR)
    (hinv : Field.KInvT.specT env p L.inv.idx needI) :
    specT env p i need := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 112 ≤ top.toNat)]
  have hfin := fin_ok env p i L hp (by omega : 112 ≤ need) hk hpre_3 hpre_10 hpre_11 hpre_6 hpre_7
    (hpre_2 ▸ ⟨hpre_8, hpre_9⟩)
  have hmid := mid env p i L hp hL hnA hnH hnR hal hhe hres hstop hpre_3 hpre_10 hpre_11
    fun q => loop env p i L hp hL hnI hinv hpre_3 hpre_10 hpre_11 (hfin q) _
  clear hfin
  have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
  rv_symT hp stop [24] with [hL, hlim] using [hroots]
  have hlay := env.layout
  have e512 : (top + 18446744073709551512#64).toNat = top.toNat - 104 := by tn
  obtain ⟨bc, bp, bC, bP, bL⟩ := hdrR top m1
  rw [bc, bp] at hret1_19
  rw [bc] at hret1_20
  rw [bC, bL] at hret1_21
  rw [bL] at hret1_22
  rw [bC, bP] at hret1_23
  unfold Env.Live at hret1_19
  refine hmid _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, roots_ok hlim
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT) hret1_14 (fun a ha => by
      simp only [SretOut, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
        Layouts.Vec.byteSize] at ha
      omega) keep1_1 hret1_24 hret1_15, hret1_22, by omega, hret1_20, ?_⟩
  rcases hret1_19 with h | ⟨h1, h2, h3⟩
  · omega
  rcases hret1_23 with h0 | h0
  · have := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_ofNat] at this
    omega
  · exact ⟨h0, h1, by omega, h3⟩

end Rv64mc.Proof.Whir.SubspaceNewT

/-- info: 'Rv64mc.Proof.Whir.SubspaceNewT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.SubspaceNewT.total