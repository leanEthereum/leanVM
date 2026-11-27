/-
  Rv64mc.Proof.Keccak.InstanceWeightsT

  `verifier::keccak::instance_weights(s) -> Vec<E>` is total (`specT`): from a result's slot of `24` bytes owned, in
  a window, 8-byte aligned, it returns with the slot a vector of `16` `E`s (`VecT`), its buffer allocated since the
  entry, writing at most the slot besides its stack and what it allocates (the partial contract's `Out`), or the run
  ends with `a0 = 2` where `alloc` (through `handle_error`), `reserve` or the bit-filtered sum does. Safety only: the
  partial contract's values (`Spec/Keccak/InstanceWeights.lean`'s `Post`, `Model.instanceWeightsRust`) are owed. It
  has no partial proof (class C). The table `RMFE_EMBED` it reads is in the static data (`DataRef.InData`, an
  environment fact).

  The code fills `powers` (`24` `E`s at `top - 520`) with `s^k` (`E::mul`, loop at instruction 64, `loopA`), allocates
  the weights' block with capacity `16` and `reserve`s `16` (`mid`), then for each of the sixteen `u32`s `e` of
  `RMFE_EMBED` stores `e` at `top - 108`, builds the iterator over its bits at `top - 104` and stores its sum into the
  block (loop at instruction 98, `loopB`), and copies the header into the slot (instruction 112, `fin_ok`). Each part
  keeps `SavedT.MemOk` with the nine saved registers' slots (`Mem`) and `s8` to `s11` (`Keep`); the loops are
  `Total.loop` with the powers and the weights left as measures. The `u32` store is its doubleword's (`w32`).

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `Mem`, `Keep`, `Buf`, `AInv`, `MInv`, `BInv`, `FInv`

  ## Main results

  * `slots`, `call_ok`, `slot_ok`, `hdr`, `hdr_stores`, `res_ok`, `tbl_win`, `w32`, `iter_ok`, `heap_ok`, `loopA`,
    `mid`, `loopB`, `fin_ok`, `total`
-/

import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Field.ESumEmbedBitsT
import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Whir.VecWordT
import Rv64mc.Spec.Keccak.InstanceWeights
import Rv64mc.Gen.Tmpl.Verifier.Keccak.InstanceWeights

namespace Rv64mc.Proof.Keccak.InstanceWeightsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Whir.VecWordT (vecT_stores)
open Rv64mc.Gen.Verifier.Keccak.InstanceWeights (Link tmpl d_c64_a72ced70_words)

/-- The total precondition: the result's slot (`24` bytes) in a window, 8-byte aligned, owned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24

/-- The total postcondition: the slot a vector of `16` `E`s, its buffer allocated since the entry. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ (vecLen m' (regs .x10)).toNat = 16 ∧
    (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat

/-- **The total contract of `instance_weights`**: `PreT` to `PostT`, writing at most the slot (the partial contract's
    `Out`), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) Spec.Keccak.InstanceWeights.Out (Stop := AbortStop)

/-- What every part keeps of memory: `SavedT.MemOk` with the nine saved registers' slots, from `top - 8` (the return
    address) down to `top - 72` (`s7`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (Spec.Keccak.InstanceWeights.Out regs m)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20, regs .x21, regs .x22, regs .x23] m M

/-- The saved slots lie in the `72` bytes below `top`. -/
theorem slots : SlotsIn 72
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64] := slots_le

/-- The callee-saved registers the function never saves (`s8` to `s11`), as at the entry. -/
def Keep (regs R : Reg → Word) : Prop :=
  R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The powers' loop head (instruction 64), `j` powers left: the stack pointer, the slot's address in `x8`, the
    cursor `x19` (the next power, `top - 504` first) and its end `x20` (`top - 136`); `Mem`. -/
def AInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551088#64 ∧ R .x8 = regs .x10 ∧ Keep regs R ∧ (R .x19).toNat + 16 * j = top.toNat - 136 ∧
    R .x20 = top + 18446744073709551480#64 ∧ 1 ≤ j ∧ j ≤ 23 ∧ Mem env ret top regs m M

/-- After the powers (instruction 74): the stack pointer, the slot's address in `x8`; `Mem`. -/
def MInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551088#64 ∧ R .x8 = regs .x10 ∧ Keep regs R ∧ Mem env ret top regs m M

/-- The weights' block `q`: allocated since the entry, of `16` elements below `NEXT`, 8-byte aligned. -/
def Buf (env : Env) (m : MachineState) (q : Word) (M : MachineState) : Prop :=
  (env.next m).toNat ≤ q.toNat ∧ 0x10000000 ≤ q.toNat ∧ q.toNat + 256 ≤ (env.next M).toNat ∧ q.toNat % 8 = 0

/-- The weights' loop head (instruction 98), `j` weights left: the stack pointer, the slot's address in `x8`, the
    new length `16` in `x9`, `e`'s address `top - 108` in `x18`, the table's cursor `x19` (`D + 4 (16 - j)`), the
    block's cursor `x20` (`8` past the next weight) and end `x21`, `24` in `x22`, `powers` (`top - 520`) in `x23`;
    the header at `top - 136` (capacity `16`, pointer `q`); `Buf`, `Mem`. -/
def BInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (D q : Word) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551088#64 ∧ R .x8 = regs .x10 ∧ Keep regs R ∧ R .x9 = 16#64 ∧
    R .x18 = top + 18446744073709551508#64 ∧ (R .x19).toNat + 4 * j = D.toNat + 64 ∧
    (R .x20).toNat + 16 * j = q.toNat + 264 ∧ (R .x21).toNat = q.toNat + 264 ∧ R .x22 = 24#64 ∧
    R .x23 = top + 18446744073709551096#64 ∧ 1 ≤ j ∧ j ≤ 16 ∧ M.getMem (top + 18446744073709551480#64) = 16#64 ∧
    M.getMem (top + 18446744073709551488#64) = q ∧ Buf env m q M ∧ Mem env ret top regs m M

/-- After the weights (instruction 112): `BInv`'s stack pointer, slot's address, length and header; `Buf`,
    `Mem`. -/
def FInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551088#64 ∧ R .x8 = regs .x10 ∧ Keep regs R ∧ R .x9 = 16#64 ∧
    M.getMem (top + 18446744073709551480#64) = 16#64 ∧ M.getMem (top + 18446744073709551488#64) = q ∧
    Buf env m q M ∧ Mem env ret top regs m M

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- **Across a callee writing nothing of the caller's** (`m1`, from the stack pointer `top - 528`): `Mem` kept,
    every word of the frame read as before. -/
theorem call_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState}
    (hlim : env.stackLimit.toNat + 528 ≤ top.toNat) (hM : Mem env ret top regs m M)
    (hf : env.Frame (top + 18446744073709551088#64) (fun _ => False) M m1)
    (hk : ∀ a : Word, top + 18446744073709551088#64 ≤ a → m1.getMem a = M.getMem a) (hc : m1.code = M.code)
    (hs : env.Static m1) :
    Mem env ret top regs m m1 ∧ (env.next M).toNat ≤ (env.next m1).toNat ∧
      ∀ a : Word, top.toNat - 528 ≤ a.toNat → m1.getMem a = M.getMem a := by
  have e : (top + 18446744073709551088#64).toNat = top.toNat - 528 := by tn
  have rd : ∀ a : Word, top.toNat - 528 ≤ a.toNat → m1.getMem a = M.getMem a := fun a h =>
    hk a (Tactic.le_of_toNat (by omega))
  exact ⟨hM.call slots (by omega) (by omega) hf hc hs (fun _ h => h.elim) fun a h1 _ => rd a (by omega), hf.1, rd⟩

/-- **A store into the frame below the slots**: `Mem` kept, `NEXT` kept. -/
theorem slot_ok {env : Env} {ret top a : Word} {regs : Reg → Word} {m M : MachineState}
    (hlim : env.stackLimit.toNat + 528 ≤ top.toNat) (hM : Mem env ret top regs m M) (hlo : top.toNat - 528 ≤ a.toNat)
    (hhi : a.toNat + 80 ≤ top.toNat) (v : Word) :
    Mem env ret top regs m (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M :=
  hM.slot slots hlim hlo hhi

/-- The weights' header words (at `top - 136`) as `rvCapAt`, `rvPtrAt`, `vecCap`, `vecPtr`, `vecLen` name them. -/
theorem hdr (top : Word) (M : MachineState) :
    rvCapAt (top + 18446744073709551480#64) = top + 18446744073709551480#64 ∧
      rvPtrAt (top + 18446744073709551480#64) = top + 18446744073709551488#64 ∧
      vecCap M (top + 18446744073709551480#64) = M.getMem (top + 18446744073709551480#64) ∧
      vecPtr M (top + 18446744073709551480#64) = M.getMem (top + 18446744073709551488#64) ∧
      vecLen M (top + 18446744073709551480#64) = M.getMem (top + 18446744073709551496#64) := by
  refine ⟨Runtime.GrowOne.rvCapAt_eq _, ?_, Runtime.VecHdrT.vecCap_eq _ _, ?_, ?_⟩
  · unfold rvPtrAt; rw [BitVec.add_assoc]; rfl
  · unfold vecPtr; rw [BitVec.add_assoc]; rfl
  · unfold vecLen; rw [BitVec.add_assoc]; rfl

/-- The weights' header `(16, q, 0)` stored at `top - 136` to `top - 120`, read back, `NEXT` kept. -/
theorem hdr_stores {env : Env} {top q : Word} {X : MachineState} (hlim : env.stackLimit.toNat + 528 ≤ top.toNat) :
    (((X.setMem (top + 18446744073709551480#64) 16#64).setMem (top + 18446744073709551488#64) q).setMem
        (top + 18446744073709551496#64) 0#64).getMem (top + 18446744073709551480#64) = 16#64 ∧
      (((X.setMem (top + 18446744073709551480#64) 16#64).setMem (top + 18446744073709551488#64) q).setMem
        (top + 18446744073709551496#64) 0#64).getMem (top + 18446744073709551488#64) = q ∧
      (((X.setMem (top + 18446744073709551480#64) 16#64).setMem (top + 18446744073709551488#64) q).setMem
        (top + 18446744073709551496#64) 0#64).getMem (top + 18446744073709551496#64) = 0#64 ∧
      env.next (((X.setMem (top + 18446744073709551480#64) 16#64).setMem (top + 18446744073709551488#64) q).setMem
        (top + 18446744073709551496#64) 0#64) = env.next X := by
  have hlay := env.layout
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b h => Tactic.ne_of_toNat h
  have e1 : (top + 18446744073709551480#64).toNat = top.toNat - 136 := by tn
  have e2 : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by tn
  have e3 : (top + 18446744073709551496#64).toNat = top.toNat - 120 := by tn
  refine ⟨?_, ?_, MachineState.getMem_setMem_eq, ?_⟩
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · rw [Tactic.next_setMem (ne _ _ (by omega)), Tactic.next_setMem (ne _ _ (by omega)),
      Tactic.next_setMem (ne _ _ (by omega))]

/-- **After `reserve(n)` of the weights with the room** (`n` at most the capacity less the length, `m1`): `Mem`
    kept, the header's three words read as before. -/
theorem res_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    {n : Nat} (hlim : env.stackLimit.toNat + 528 ≤ top.toNat) (hM : Mem env ret top regs m M)
    (hf : env.Frame (top + 18446744073709551088#64) out M m1)
    (hout : ∀ a, out a → a = top + 18446744073709551480#64 ∨ a = top + 18446744073709551488#64)
    (hk : ∀ a : Word, top + 18446744073709551088#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1)
    (hlen : vecLen m1 (top + 18446744073709551480#64) = vecLen M (top + 18446744073709551480#64))
    (hroom : n ≤ (vecCap M (top + 18446744073709551480#64)).toNat - (vecLen M (top + 18446744073709551480#64)).toNat →
      vecCap m1 (top + 18446744073709551480#64) = vecCap M (top + 18446744073709551480#64) ∧
        vecPtr m1 (top + 18446744073709551480#64) = vecPtr M (top + 18446744073709551480#64))
    (hr : n ≤ (M.getMem (top + 18446744073709551480#64)).toNat - (M.getMem (top + 18446744073709551496#64)).toNat) :
    Mem env ret top regs m m1 ∧ (env.next M).toNat ≤ (env.next m1).toNat ∧
      m1.getMem (top + 18446744073709551480#64) = M.getMem (top + 18446744073709551480#64) ∧
      m1.getMem (top + 18446744073709551488#64) = M.getMem (top + 18446744073709551488#64) ∧
      m1.getMem (top + 18446744073709551496#64) = M.getMem (top + 18446744073709551496#64) := by
  have hlay := env.layout
  have e528 : (top + 18446744073709551088#64).toNat = top.toNat - 528 := by tn
  have ho : ∀ a, out a → a.toNat = top.toNat - 136 ∨ a.toNat = top.toNat - 128 := fun a ha => by
    rcases hout a ha with rfl | rfl
    · exact .inl (by tn)
    · exact .inr (by tn)
  obtain ⟨-, -, bC, bP, bL⟩ := hdr top m1
  obtain ⟨-, -, bC', bP', bL'⟩ := hdr top M
  rw [bL, bL'] at hlen
  rw [bC', bL', bC, bP, bP'] at hroom
  refine ⟨hM.call slots (by omega) (by omega) hf hc hs
    (fun a ha => Tactic.mw_stack (by rcases ho a ha with h | h <;> omega)) fun a h1 h2 =>
      hk a (Tactic.le_of_toNat (by omega)) fun h => by rcases ho a h with h | h <;> omega, hf.1, (hroom hr).1,
    (hroom hr).2, hlen⟩

/-- **An entry of the embedding's table**: the `k`-th `u32` (`k < 16`) of `RMFE_EMBED` at `D` in a window and 4-byte
    aligned, from the table's eight words in the static data. -/
theorem tbl_win {env : Env} {top : Word} {m : MachineState} (hW : Windows env top m) {d : DataRef}
    (hd : DataRef.InData env [(d, d_c64_a72ced70_words)]) {x : Word} {k : Nat} (hk : k < 16)
    (hx : x.toNat = (d.hi + d.lo).toNat + 4 * k) : inWindow x 4 = true ∧ x.toNat % 4 = 0 := by
  have hl : d_c64_a72ced70_words.length = 8 := rfl
  have h0 := hW.data_ok _ (hd _ (List.mem_singleton_self _) 0 (by rw [hl]; omega))
  have hk2 := hW.data_ok _ (hd _ (List.mem_singleton_self _) (k / 2) (by rw [hl]; omega))
  simp only [Nat.mul_zero, BitVec.add_zero] at h0 hk2
  have b0 := inWindow_iff.1 h0.1
  have e : (d.hi + d.lo + BitVec.ofNat 64 (8 * (k / 2))).toNat = (d.hi + d.lo).toNat + 8 * (k / 2) :=
    toNat_add_ofNat (by omega)
  rw [e] at hk2
  refine ⟨hW.dataSub (hd _ (List.mem_singleton_self _) (k / 2) (by rw [hl]; omega)) ?_ ?_, by omega⟩
  · simp only; rw [e]; omega
  · simp only; rw [e]; omega

/-- The `u32` store at `e`'s address `top - 108` as the store of its doubleword at `top - 112`. -/
theorem w32 {top : Word} (hal : top.toNat % 16 = 0) (M : MachineState) (v : BitVec 32) :
    M.setWord32 (top + 18446744073709551508#64) v = M.setMem (top + 18446744073709551504#64)
      (replaceWord32 (M.getMem (top + 18446744073709551504#64)) (byteOffset (top + 18446744073709551508#64) / 4)
        v) := by
  have e : alignToDword (top + 18446744073709551508#64) = top + 18446744073709551504#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_alignToDword, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := top.isLt
    omega
  simp only [MachineState.setWord32, e]

/-- **The iterator built** (`e` at `top - 112`'s doubleword, the iterator's four words at `top - 104` to `top - 80`):
    `Mem` kept, `NEXT` kept, the static data kept, the header's two words read as before. -/
theorem iter_ok {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState}
    (hlim : env.stackLimit.toNat + 528 ≤ top.toNat) (hM : Mem env ret top regs m M) (w a b c d : Word) :
    Mem env ret top regs m (((((M.setMem (top + 18446744073709551504#64) w).setMem (top + 18446744073709551512#64)
      a).setMem
      (top + 18446744073709551520#64) b).setMem (top + 18446744073709551528#64) c).setMem
      (top + 18446744073709551536#64) d) ∧
    env.next (((((M.setMem (top + 18446744073709551504#64) w).setMem (top + 18446744073709551512#64) a).setMem
      (top + 18446744073709551520#64) b).setMem (top + 18446744073709551528#64) c).setMem
      (top + 18446744073709551536#64) d) = env.next M ∧
    ∀ o : Word, ∀ k, o.toNat + k = 2 ^ 64 → 112 < k → k ≤ 528 → (((((M.setMem (top + 18446744073709551504#64)
      w).setMem (top + 18446744073709551512#64) a).setMem (top + 18446744073709551520#64) b).setMem
      (top + 18446744073709551528#64) c).setMem (top + 18446744073709551536#64) d).getMem (top + o) =
        M.getMem (top + o) := by
  have hlay := env.layout
  obtain ⟨h1, n1⟩ := slot_ok (a := top + 18446744073709551504#64) hlim hM (by tn) (by tn) w
  obtain ⟨h2, n2⟩ := slot_ok (a := top + 18446744073709551512#64) hlim h1 (by tn) (by tn) a
  obtain ⟨h3, n3⟩ := slot_ok (a := top + 18446744073709551520#64) hlim h2 (by tn) (by tn) b
  obtain ⟨h4, n4⟩ := slot_ok (a := top + 18446744073709551528#64) hlim h3 (by tn) (by tn) c
  obtain ⟨h5, n5⟩ := slot_ok (a := top + 18446744073709551536#64) hlim h4 (by tn) (by tn) d
  refine ⟨h5, by rw [n5, n4, n3, n2, n1], fun o k ho hk1 hk2 => ?_⟩
  have e : (top + o).toNat = top.toNat - k := by rw [BitVec.toNat_add]; omega
  have ne : ∀ x : Word, top.toNat - 112 ≤ x.toNat → top + o ≠ x := fun x hx =>
    Tactic.ne_of_toNat (by omega)
  rw [MachineState.getMem_setMem_ne (ne _ (by tn)), MachineState.getMem_setMem_ne (ne _ (by tn)),
    MachineState.getMem_setMem_ne (ne _ (by tn)), MachineState.getMem_setMem_ne (ne _ (by tn)),
    MachineState.getMem_setMem_ne (ne _ (by tn))]

/-- **A store into the weights' block**: `Mem` kept, `Buf` kept, `NEXT` kept, every word of the frame read as
    before. -/
theorem heap_ok {env : Env} {ret top a q : Word} {regs : Reg → Word} {m M : MachineState}
    (hlim : env.stackLimit.toNat + 528 ≤ top.toNat) (hM : Mem env ret top regs m M) (hB : Buf env m q M)
    (hlo : q.toNat ≤ a.toNat) (hhi : a.toNat + 8 ≤ q.toNat + 256) (v : Word) :
    Mem env ret top regs m (M.setMem a v) ∧ Buf env m q (M.setMem a v) ∧
      ∀ b : Word, env.stackLimit.toNat ≤ b.toNat → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  have hnM := hM.1.2.1
  obtain ⟨b1, b2, b3, b4⟩ := hB
  obtain ⟨h1, n1⟩ := hM.fresh (a := a) (v := v) slots (by omega) (by omega) (by omega)
  exact ⟨h1, ⟨b1, b2, by rw [n1]; exact b3, b4⟩, fun b hb =>
    MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))⟩

set_option rv_sym.heap true in
/-- **The powers' loop**, from its head: the next power, the last one times `s` (`E::mul`), stored; back to the head,
    or on after the loop; one power fewer left. -/
theorem loopA (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needU : Nat} (hnU : 528 + needU ≤ need) (hmul : Field.EMulT.specT env p L.mul.idx needU)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hmid : ∀ R M, MInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 148, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, AInv env ret top regs m j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 128, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (AInv env ret top regs m) fun j R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, h19, -, hj1, hj23, hM⟩ := id hI
  have hlim : env.stackLimit.toNat + 528 ≤ top.toNat := by omega
  rv_introT hI
  rv_symT hp stop [128, 148] with [hL, hlim] using [hmul]
  all_goals
    obtain ⟨hM1, hn1, -⟩ := call_ok hlim hM hret1_14 keep1_1 hret1_18 hret1_15
    have e8 : (R .x19 + 8#64).toNat = (R .x19).toNat + 8 := toNat_add_ofNat (by omega)
    obtain ⟨hM2, -⟩ := slot_ok (a := R .x19) hlim hM1 (by omega) (by omega) (r1 .x10)
    obtain ⟨hM3, -⟩ := slot_ok (a := R .x19 + 8#64) hlim hM2 (by omega) (by omega) (r1 .x11)
    rw [← hret1_16, ← hret1_17]
  -- back to the head
  · have e16 : (R .x19 + 16#64).toNat = (R .x19).toNat + 16 := toNat_add_ofNat (by omega)
    have hj2 : 2 ≤ j := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by rw [e16]; tn))
    exact ih (j - 1) _ _ (by omega) ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, by simp only [Tactic.rf]; omega, rfl, by omega,
      by omega, hM3⟩
  -- the powers done
  · exact hmid _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, hM3⟩

set_option rv_sym.heap true in
/-- **After the powers**: the weights' block allocated with capacity `16` (`handle_error` when `alloc` fails) and
    `reserve`d, then the weights' loop head with all sixteen left. -/
theorem mid (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needH needR : Nat} (hnA : 528 + needA ≤ need) (hnH : 528 + needH ≤ need) (hnR : 528 + needR ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hhe : Aborts env p L.handleError.idx needH)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal16 : top.toNat % 16 = 0) (hW : Windows env top m)
    (hb : ∀ q R M, BInv env ret top regs m (L.d_c64_a72ced70.hi + L.d_c64_a72ced70.lo) q 16 R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 196, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, MInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 148, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hlay := env.layout
  obtain ⟨-, -, -, hM⟩ := id hI
  have hlim : env.stackLimit.toNat + 528 ≤ top.toNat := by omega
  rv_introT hI
  rv_symT hp stop [196] with [hL, hlim] using [hac, hhe, hres]
  all_goals
    obtain ⟨bc, bp, -, -, -⟩ := hdr top M
    have hn1 := hret1_14.1
    have hn1' := hret1_14.2.1
    have hhe := hW.heapEnd_le
    have hge := hW.next_ge
    have hnM := hM.next_le
    have h18 := hret1_18
    simp only [BitVec.toNat_ofNat] at h18
  -- `reserve(16)`'s precondition
  iterate 4
    simp only [bc, bp, (hdr_stores hlim).1, (hdr_stores hlim).2.1]
    rotate_left
  rotate_left
  · exact .inr (by unfold Env.Live; rw [(hdr_stores hlim).2.2.2, show (16#64).toNat = 16 from rfl]; omega)
  · decide
  · exact .inr ⟨by omega, by
      unfold Env.Live; rw [(hdr_stores hlim).2.2.2, show (16#64).toNat = 16 from rfl]; omega, hret1_17⟩
  · decide
  -- the weights' loop head
  · obtain ⟨hM1, -⟩ := call_ok hlim hM hret1_14 keep1_1 hret1_19 hret1_15
    have hM2 : Mem env ret top regs m (((m1.setMem (top + 18446744073709551480#64) 16#64).setMem
        (top + 18446744073709551488#64) (r1 .x10)).setMem (top + 18446744073709551496#64) 0#64) :=
      (slot_ok hlim (slot_ok hlim (slot_ok hlim hM1 (by tn) (by tn) _).1 (by tn) (by tn) _).1 (by tn) (by tn) _).1
    obtain ⟨hM3, hn3, g480, g488, g496⟩ := res_ok (n := 16) hlim hM2 hret3_14
      (fun a ha => by
        simp only [GrowOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, bc, bp] at ha
        exact ha) keep3_1 hret3_25 hret3_15 hret3_16 hret3_17
      (by rw [(hdr_stores hlim).1, (hdr_stores hlim).2.2.1]; decide)
    rw [(hdr_stores hlim).1] at g480
    rw [(hdr_stores hlim).2.1] at g488
    rw [(hdr_stores hlim).2.2.1] at g496
    rw [(hdr_stores hlim).2.2.2] at hn3
    rw [g496, g488]
    have hz : 0#64 <<< 4 + r1 .x10 = r1 .x10 := by rw [BitVec.zero_shiftLeft, BitVec.zero_add]
    refine hb (r1 .x10) _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp only [Tactic.rf], ?_, ?_, rfl, rfl,
      by omega, Nat.le_refl _, g480, g488, ⟨by omega, by omega, by omega, hret1_17⟩, hM3⟩
    all_goals simp only [Tactic.rf, hz]
    · rw [toNat_add_ofNat (by omega)]
    · rw [toNat_add_ofNat (by omega)]

set_option rv_sym.heap true in
/-- **The weights' loop**, from its head: the next entry `e` of the table stored at `top - 108`, the iterator over
    its bits built at `top - 104`, their sum (`E::sum`) stored in the block; back to the head, or on to the exit;
    one weight fewer left. -/
theorem loopB (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hd : DataRef.InData env [(L.d_c64_a72ced70, d_c64_a72ced70_words)])
    {need needS : Nat} (hnS : 528 + needS ≤ need)
    (hsum : Field.ESumEmbedBitsT.SumSafeT env p L.sumMapFilterRangeUsizeInHbf23f0ea.idx needS)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m) {q : Word}
    (hfin : ∀ R M, FInv env ret top regs m q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 224, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, BInv env ret top regs m (L.d_c64_a72ced70.hi + L.d_c64_a72ced70.lo) q j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 196, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (BInv env ret top regs m (L.d_c64_a72ced70.hi + L.d_c64_a72ced70.lo) q)
    fun j R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, -, -, h19, h20, h21, -, -, hj1, hj16, h480, h488, hB, hM⟩ := id hI
  have hlim : env.stackLimit.toNat + 528 ≤ top.toNat := by omega
  have ht := tbl_win hW hd (x := R .x19) (k := 16 - j) (by omega) (by omega)
  rv_introT hI
  rv_symT hp stop [196, 224] with [hL, hlim] using [hsum]
  · exact ht.1
  all_goals
    simp only [w32 hal] at *
    obtain ⟨hMX, nX, rdX⟩ := iter_ok hlim hM (replaceWord32 (M.getMem (top + 18446744073709551504#64))
      (byteOffset (top + 18446744073709551508#64) / 4) (BitVec.truncate 32 ((UnOp.sext Width.b4).eval
        (BitVec.zeroExtend 64 (M.getWord32 (R .x19)))))) (top + 18446744073709551508#64) 0#64 24#64
      (top + 18446744073709551096#64)
  · exact hMX.2.2.1
  · rw [Tactic.next_setMem (Tactic.next_ne_of_stack (by tn))]; exact hM.1.2.1
  · rw [nX]; exact hM.next_le
  all_goals
    obtain ⟨hM1, hn1, rd1⟩ := call_ok hlim hMX hret1_14 keep1_1 hret1_16 hret1_15
    rw [nX] at hn1
    have hhe := hW.heapEnd_le
    have hnM := hM.1.2.1
    obtain ⟨b1, b2, b3, b4⟩ := id hB
    have e8 : (R .x20 + 18446744073709551608#64).toNat = (R .x20).toNat - 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    obtain ⟨hM2, hB2, rd2⟩ := heap_ok (a := R .x20 + 18446744073709551608#64) hlim hM1
      (⟨b1, b2, by omega, b4⟩ : Buf env m q m1) (by omega) (by omega) (r1 .x10)
    obtain ⟨hM3, hB3, rd3⟩ := heap_ok (a := R .x20) hlim hM2 hB2 (by omega) (by omega) (r1 .x11)
    have r : ∀ o : Word, ∀ k, o.toNat + k = 2 ^ 64 → 112 < k → k ≤ 528 →
        ((m1.setMem (R .x20 + 18446744073709551608#64) (r1 .x10)).setMem (R .x20) (r1 .x11)).getMem (top + o) =
          M.getMem (top + o) := fun o k ho h1 h2 => by
      have e : (top + o).toNat = top.toNat - k := by rw [BitVec.toNat_add]; omega
      rw [rd3 _ (by omega), rd2 _ (by omega), rd1 _ (by omega), rdX o k ho h1 h2]
    have g480 := r 18446744073709551480#64 136 rfl (by omega) (by omega)
    have g488 := r 18446744073709551488#64 128 rfl (by omega) (by omega)
    rw [h480] at g480
    rw [h488] at g488
  -- back to the head
  · have hw := inWindow_iff.1 ht.1
    have hj2 : 2 ≤ j := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega)]; omega))
    refine ih (j - 1) _ _ (by omega) ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_, ?_, ?_, rfl, rfl, by omega,
      by omega, g480, g488, hB3, hM3⟩
    all_goals simp only [Tactic.rf]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
    · exact h21
  -- the weights done
  · exact hfin _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, g480, g488, hB3, hM3⟩

set_option rv_sym.heap true in
/-- **The exit**: the weights' header (capacity, pointer, length `16`) stored into the slot, the epilogue, the
    return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 528 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) Spec.Keccak.InstanceWeights.Out ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 24) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 24) :
    ∀ q R M, FInv env ret top regs m q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 224, ret, top⟩ :: rest, R, M⟩ := by
  intro q R M hinv
  obtain ⟨-, -, -, -, h480, h488, ⟨b1, b2, b3, b4⟩, ⟨hF, -, -, -⟩⟩ := id hinv
  have hlS := hwS.lt
  have hlay := env.layout
  have hnM := hF.1
  obtain ⟨ho1, -⟩ := hoS
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 528 ≤ top.toNat)]
  · have o : ∀ k : Nat, k < 24 →
        Spec.Keccak.InstanceWeights.Out regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      ⟨by rw [toNat_add_ofNat (by omega)]; omega,
        by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega⟩
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF (by simpa using o 0 (by omega))
      (hwS.ne_next (Nat.le_refl _) (by omega))) (o 8 (by omega)) (hwS.ne_next_add (o := 8) (by omega)))
      (o 16 (by omega)) (hwS.ne_next_add (o := 16) (by omega))
  all_goals
    have hB : BufT env M (M.getMem (top + 18446744073709551480#64)) (M.getMem (top + 18446744073709551488#64)) 16 :=
      .inr ⟨by rw [h488]; omega, by unfold Env.Live; rw [h480, h488]; simp only [BitVec.toNat_ofNat]; omega,
        by rw [h488]; exact b4⟩
    have hc : (M.getMem (top + 18446744073709551480#64)).toNat * 16 < 2 ^ 63 := by rw [h480]; decide
    have hl : (16#64).toNat ≤ (M.getMem (top + 18446744073709551480#64)).toNat := by rw [h480]
  · exact (vecT_stores hwS haS hB hc hl).1.2.1.2.2.1
  · exact (vecT_stores hwS haS hB hc hl).1.2.1.2.2.2

set_option rv_sym.heap true in
/-- **`instance_weights` is total**: the prologue, `powers` set to `[1, 0, ..., 0]`, then the powers' loop, the
    weights' block and the weights' loop. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hd : DataRef.InData env [(L.d_c64_a72ced70, d_c64_a72ced70_words)])
    {need needU needA needH needR needS : Nat} (hnU : 528 + needU ≤ need) (hnA : 528 + needA ≤ need)
    (hnH : 528 + needH ≤ need) (hnR : 528 + needR ≤ need) (hnS : 528 + needS ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needU) (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hhe : Aborts env p L.handleError.idx needH)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hsum : Field.ESumEmbedBitsT.SumSafeT env p L.sumMapFilterRangeUsizeInHbf23f0ea.idx needS) :
    specT env p i need := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 528 ≤ top.toNat)]
  have hfin := fin_ok env p i L hp (by omega : 528 ≤ need) hk hpre_3 hpre_10 hpre_11 hpre_6 hpre_7
    (hpre_2 ▸ ⟨hpre_8, hpre_9⟩)
  have ha := loopA env p i L hp hL hnU hmul hpre_3 hpre_10 hpre_11
    (mid env p i L hp hL hnA hnH hnR hal hhe hres hstop hpre_3 hpre_10 hpre_11
      fun q => loopB env p i L hp hL hd hnS hsum hstop hpre_3 hpre_10 hpre_11 (hfin q) 16)
  clear hfin
  rv_symT hp stop [128] with [hL, (by omega : env.stackLimit.toNat + 528 ≤ top.toNat)]
  refine ha 23 _ _ ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, ?_, rfl, by omega, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, trivial⟩⟩
  all_goals try rv_closeT
  simp only [Tactic.rf]
  tn

end Rv64mc.Proof.Keccak.InstanceWeightsT

/-- info: 'Rv64mc.Proof.Keccak.InstanceWeightsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Keccak.InstanceWeightsT.total
