/-
  Rv64mc.Proof.Whir.ExtRowT

  `verifier::whir::ext_row(words: &[K]) -> Vec<E>` is total (`specT`): from a result's slot of `24` bytes owned, in
  a window, 8-byte aligned, and the words (`a1`, `a2`) none or allocated, in a window and 8-byte aligned (`SliceW`,
  `MerkleT.SliceKT`'s shape), it returns with the slot a vector of `E`s (`VecT`) of `len / 2` elements (the full
  pairs), its buffer allocated since the entry unless it has no capacity, writing at most the slot besides what it
  allocates (`SretOut`, the partial contract's), or the run ends with `a0 = 2` where `alloc`, its `handle_error` or
  `reserve` does. Safety only: the partial contract's values (`Spec/Whir/ExtRow.lean`'s `spec`,
  `Model.extRowRust`) are owed. It has no partial proof (class C).

  The vector is allocated with capacity `len / 2` and `reserve(len / 2)` finds the room (`ReservePost`'s first
  clause), so the copy loop's stores lie in the buffer. Cut at `reserve`'s call (instruction 50, `res_ok`), at the
  copy loop's head (instruction 76, `loop`: `Total.loop` with the pairs left as the measure) and at the exit
  (instruction 90, `fin_ok`).

  ## Main definitions

  * `SliceW`, `PreT`, `PostT`, `specT`, `Saved`, `Hdr`, `Keep`, `RInv`, `LInv`, `FinInv`

  ## Main results

  * `Hdr.push2`, `Hdr.vecT`, `Hdr.reserve`, `fin_ok`, `loop`, `res_ok`, `total`
-/

import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Whir.VecWordT
import Rv64mc.Spec.Whir.ExtRow
import Rv64mc.Gen.Tmpl.Verifier.Whir.ExtRow

namespace Rv64mc.Proof.Whir.ExtRowT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Transcript (getMem_setMem_off)
open Rv64mc.Proof.Whir.VecWordT (vecT_stores)
open Rv64mc.Gen.Verifier.Whir.ExtRow (Link tmpl)

/-- `len` words at `ptr`: none, or allocated, in a window and 8-byte aligned. -/
def SliceW (env : Env) (m : MachineState) (ptr len : Word) : Prop :=
  len.toNat = 0 ∨ (env.Live m ptr (8 * len.toNat) ∧ InWin env ptr (8 * len.toNat) ∧ ptr.toNat % 8 = 0)

/-- The total precondition: the result's slot (`24` bytes) in a window, 8-byte aligned, owned; the words
    `SliceW`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24 ∧
    SliceW env m (regs .x11) (regs .x12)

/-- The total postcondition: the slot a vector of `E`s of `len / 2` elements, its buffer allocated since the entry
    unless it has no capacity. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ (vecLen m' (regs .x10)).toNat = (regs .x12).toNat / 2 ∧
    (vecCap m' (regs .x10) = 0#64 ∨ (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat)

/-- **The total contract of `ext_row`**: `PreT` to `PostT`, writing at most the slot (`SretOut`, the partial
    contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (SretOut Layouts.Vec.byteSize) (Stop := AbortStop)

/-- The saved registers' five slots. -/
def Saved (ret top : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19

/-- The vector's header at `sp` (capacity, pointer, length): its buffer `BufT` of `E`s, of fewer than `2^63` bytes,
    its capacity at least `n`, allocated since the entry unless it has no capacity, its length `0`; the frame, the
    code, the static data, the saved registers' slots. -/
def Hdr (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (n : Nat) (M : MachineState) : Prop :=
  env.Frame top (SretOut Layouts.Vec.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧ Saved ret top regs M ∧
    BufT env M (M.getMem (top + 18446744073709551552#64)) (M.getMem (top + 18446744073709551560#64)) 16 ∧
    (M.getMem (top + 18446744073709551552#64)).toNat * 16 < 2 ^ 63 ∧
    n ≤ (M.getMem (top + 18446744073709551552#64)).toNat ∧
    (M.getMem (top + 18446744073709551552#64) = 0#64 ∨
      (env.next m).toNat ≤ (M.getMem (top + 18446744073709551560#64)).toNat) ∧
    M.getMem (top + 18446744073709551568#64) = 0#64

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- The registers above `x19` the function never writes. -/
def Keep (regs R : Reg → Word) : Prop :=
  R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧
    R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The copy loop's head (instruction 76), `k` pairs left, at least one: the stack pointer, the slot's address, the
    final length `n` in `x10`, the source's cursor `x19` and end `x9` past the words at `w`, the destination's cursor
    `x11` in the buffer; `Hdr`; the words `8 len` bytes, allocated and in a window, 8-byte aligned. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (n : Nat) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x8 = regs .x10 ∧ R .x10 = BitVec.ofNat 64 n ∧
    (R .x19).toNat + 16 * k = (regs .x11).toNat + 8 + 16 * n ∧ (R .x9).toNat = (regs .x11).toNat + 8 + 16 * n ∧
    (R .x11).toNat + 16 * k = (M.getMem (top + 18446744073709551560#64)).toNat + 8 + 16 * n ∧ 1 ≤ k ∧ k ≤ n ∧
    n = (regs .x12).toNat / 2 ∧ Keep regs R ∧ Hdr env ret top regs m n M ∧
    env.Live m (regs .x11) (8 * (regs .x12).toNat) ∧ InWin env (regs .x11) (8 * (regs .x12).toNat) ∧
    (regs .x11).toNat % 8 = 0

/-- The exit (instruction 90): the stack pointer, the slot's address, the length `n` (`len / 2`) in `x10`,
    `Hdr`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (n : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x8 = regs .x10 ∧ R .x10 = BitVec.ofNat 64 n ∧
    n = (regs .x12).toNat / 2 ∧ n < 2 ^ 59 ∧ Keep regs R ∧ Hdr env ret top regs m n M

/-- **`Hdr` after a pair stored** at `b - 8` and `b` in the buffer, below its `n`-th element. -/
theorem Hdr.push2 {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {n : Nat} {b v w : Word}
    (h : Hdr env ret top regs m n M) (hlim : env.stackLimit.toNat + 64 ≤ top.toNat) (hn : 0 < n)
    (hb8 : (M.getMem (top + 18446744073709551560#64)).toNat + 8 ≤ b.toNat)
    (hb' : b.toNat + 8 ≤ (M.getMem (top + 18446744073709551560#64)).toNat + 16 * n) :
    Hdr env ret top regs m n ((M.setMem (b + 18446744073709551608#64) v).setMem b w) ∧
      ((M.setMem (b + 18446744073709551608#64) v).setMem b w).getMem (top + 18446744073709551560#64) =
        M.getMem (top + 18446744073709551560#64) := by
  obtain ⟨hF, hcM, hs, hSv, hbf, hcap, hncap, hfr, hl⟩ := h
  have hlay := env.layout
  have hnM := hF.2.1
  have hcap0 : (M.getMem (top + 18446744073709551552#64)).toNat ≠ 0 := by omega
  obtain ⟨hp0, hpl, hpa⟩ := hbf.resolve_left hcap0
  have hfr' := hfr.resolve_left fun h0 => hcap0 (by rw [h0]; rfl)
  unfold Env.Live at hpl
  have e8 : (b + 18446744073709551608#64).toNat = b.toNat - 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hna : b + 18446744073709551608#64 ≠ env.nextAddr := Tactic.ne_of_toNat (by rw [e8]; omega)
  have hnb : b ≠ env.nextAddr := Tactic.ne_of_toNat (by omega)
  have rd : ∀ x : Word, env.stackLimit.toNat ≤ x.toNat →
      ((M.setMem (b + 18446744073709551608#64) v).setMem b w).getMem x = M.getMem x := fun x hx => by
    rw [MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega)),
      MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by rw [e8]; omega))]
  have hn' : env.next ((M.setMem (b + 18446744073709551608#64) v).setMem b w) = env.next M := by
    rw [Tactic.next_setMem hnb, Tactic.next_setMem hna]
  obtain ⟨s1, s2, s3, s4, s5⟩ := hSv
  refine ⟨⟨Tactic.frame_fresh (Tactic.frame_fresh hF rfl (by rw [e8]; omega) (by rw [e8]; omega))
      (Tactic.next_setMem hna) (by omega) (by omega), by simp only [MachineState.code_setMem]; exact hcM,
    Tactic.static_store (Tactic.static_store hs (by rw [e8]; omega)) (by omega),
    ⟨(rd _ (by tn)).trans s1, (rd _ (by tn)).trans s2, (rd _ (by tn)).trans s3, (rd _ (by tn)).trans s4,
      (rd _ (by tn)).trans s5⟩, ?_, ?_, ?_, ?_, ?_⟩, rd _ (by tn)⟩
  · rw [rd _ (by tn), rd _ (by tn)]; exact hbf.mono (by rw [hn'])
  · rw [rd _ (by tn)]; exact hcap
  · rw [rd _ (by tn)]; exact hncap
  · rw [rd _ (by tn), rd _ (by tn)]; exact hfr
  · rw [rd _ (by tn)]; exact hl

set_option rv_sym.heap true in
/-- **The exit**: the vector's header copied into the slot with the length `n`, the epilogue, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 64 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 24) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 24) {n : Nat} :
    ∀ R M, FinInv env ret top regs m n R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 90, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, hnl, hn64, -, hF, -, -, -, hb, hcap, hncap, hfr, -⟩ := id hinv
  have hlS := hwS.lt
  have hn' : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  rv_introT hinv
  have hlc : (BitVec.ofNat 64 n).toNat ≤ (M.getMem (top + 18446744073709551552#64)).toNat := by rw [hn']; exact hncap
  rv_symT hp with [(by omega : env.stackLimit.toNat + 64 ≤ top.toNat)]
  · have o : ∀ k : Nat, k < 24 → SretOut Layouts.Vec.byteSize regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      ⟨by rw [toNat_add_ofNat (by omega)]; omega,
        by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega⟩
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF (by simpa using o 0 (by omega))
      (hwS.ne_next (Nat.le_refl _) (by omega))) (o 8 (by omega)) (hwS.ne_next_add (o := 8) (by omega)))
      (o 16 (by omega)) (hwS.ne_next_add (o := 16) (by omega))
  · exact (vecT_stores hwS haS hb hcap hlc).1.2.1.2.2.1
  · exact (vecT_stores hwS haS hb hcap hlc).1.2.1.2.2.2

set_option rv_sym.heap true in
/-- **The copy loop**, from its head: a pair of words copied into the buffer, then back to the head or to the exit;
    one pair fewer left. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 64 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {n : Nat}
    (hfin : ∀ R M, FinInv env ret top regs m n R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 90, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv env ret top regs m n k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 76, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m n) fun k R M hI ih => ?_
  obtain ⟨-, -, -, h19, h9, h11, hk1, hkn, hnl, hK, hH, wl, ww, wa⟩ := id hI
  have hlay := env.layout
  have hnM := hH.1.2.1
  have hnm := hH.1.1
  have hcap0 : (M.getMem (top + 18446744073709551552#64)).toNat ≠ 0 := by have := hH.2.2.2.2.2.2.1; omega
  obtain ⟨hp0, hpl, hpa⟩ := hH.2.2.2.2.1.resolve_left hcap0
  unfold Env.Live at hpl wl
  have hncap := hH.2.2.2.2.2.2.1
  have e19 : (R .x19 + 18446744073709551608#64).toNat = (R .x19).toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e11 : (R .x11 + 18446744073709551608#64).toNat = (R .x11).toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rv_introT hI
  clear hI_26 hI_29
  rv_symT hp stop [76, 90] with [(by omega : env.stackLimit.toNat + 64 ≤ top.toNat)]
  all_goals
    have hP := fun v w => Hdr.push2 (b := R .x11) (v := v) (w := w) hH (by omega) (by omega) (by omega) (by omega)
  -- back to the head
  · refine ih (k - 1) _ _ (by omega) ⟨by rv_closeT, by rv_closeT, by rv_closeT, ?_, by rv_closeT, ?_, ?_, by omega,
      hnl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, (hP _ _).1, wl, ww, wa⟩
    all_goals try simp only [Tactic.rf]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [(hP _ _).2, toNat_add_ofNat (by omega)]; omega
    · refine Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq ?_)
      rw [toNat_add_ofNat (by omega)]; omega
  -- the last pair: the exit
  · have hw := ww.lt
    refine hfin _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, hnl, by omega, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      (hP _ _).1⟩

/-- Before `reserve`'s call (instruction 50): the stack pointer, the slot's and the words' addresses, `len / 2` in
    `x18`, its offset in `x9`; `Hdr`; the words `SliceW`. -/
def RInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x8 = regs .x10 ∧ R .x18 = regs .x12 >>> 1 ∧ R .x19 = regs .x11 ∧
    R .x9 = regs .x12 >>> 1 <<< 4 ∧ Keep regs R ∧ Hdr env ret top regs m ((regs .x12).toNat / 2) M ∧
    SliceW env m (regs .x11) (regs .x12)

/-- `len / 2` as the code computes it. -/
theorem shr1 (x : Word) : (x >>> 1).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `16 x` as the code computes it. -/
theorem shl4 {x : Word} (h : 16 * x.toNat < 2 ^ 64) : (x <<< 4).toNat = 16 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- The header at `sp`'s words, as `rvCapAt`, `rvPtrAt`, `vecCap` and `vecLen` name them. -/
theorem hdr_words (top : Word) :
    rvCapAt (top + 18446744073709551552#64) = top + 18446744073709551552#64 ∧
      rvPtrAt (top + 18446744073709551552#64) = top + 18446744073709551560#64 ∧
      top + 18446744073709551552#64 + BitVec.ofNat 64 Layouts.Vec.cap = top + 18446744073709551552#64 ∧
      top + 18446744073709551552#64 + BitVec.ofNat 64 Layouts.Vec.len = top + 18446744073709551568#64 ∧
      top + 18446744073709551552#64 + BitVec.ofNat 64 Layouts.Vec.ptr = top + 18446744073709551560#64 := by
  simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, Layouts.Vec.cap, Layouts.Vec.len,
    Layouts.Vec.ptr, BitVec.add_assoc]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The header at `sp` a vector's (`VecT`), from `Hdr`. -/
theorem Hdr.vecT {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {n : Nat}
    (h : Hdr env ret top regs m n M) (hlim : env.stackLimit.toNat + 64 ≤ top.toNat) (htop : top.toNat ≤ 0xc0000000)
    (hal : top.toNat % 16 = 0) : VecT env M (top + 18446744073709551552#64) 16 := by
  obtain ⟨-, -, -, -, hb, hcap, -, -, hl⟩ := h
  have e : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by tn
  refine ⟨Or.inr ⟨by rw [e]; omega, by rw [e]; simp only [Layouts.Vec.byteSize]; omega⟩,
    ⟨Or.inr ⟨by rw [e]; omega, by rw [e]; simp only [Layouts.RawVecInner.byteSize]; omega⟩, by rw [e]; omega, ?_, ?_⟩,
    ?_⟩
  · rw [(hdr_words top).1, (hdr_words top).2.1]; exact hb
  · rw [(hdr_words top).1]; exact hcap
  · rw [vecLen, vecCap, (hdr_words top).2.2.1, (hdr_words top).2.2.2.1, hl]; simp

/-- **`Hdr` across `reserve(len / 2)`**: the room is there, so the header's capacity and pointer are kept, its
    length too, and the rest of the frame. -/
theorem Hdr.reserve {env : Env} {ret top top' : Word} {regs r : Reg → Word} {m M m1 : MachineState} {n : Nat}
    (h : Hdr env ret top regs m n M) (hlim : env.stackLimit.toNat ≤ top'.toNat) (htop : top'.toNat + 64 ≤ top.toNat)
    (hr10 : r .x10 = top + 18446744073709551552#64) (hr11 : (r .x11).toNat = n)
    (hf : env.Frame top' (GrowOut r M) M m1) (hc : m1.code = M.code) (hs : env.Static m1)
    (hP : ReservePost env 16 r M r m1) : Hdr env ret top regs m n m1 := by
  obtain ⟨hF, hcM, -, hSv, hb, hcap, hncap, hfr, hl⟩ := h
  obtain ⟨hlen, hroom, -⟩ := hP
  have hlay := env.layout
  have e0 : vecCap M (top + 18446744073709551552#64) = M.getMem (top + 18446744073709551552#64) := by
    rw [vecCap, (hdr_words top).2.2.1]
  have e0' : vecCap m1 (top + 18446744073709551552#64) = m1.getMem (top + 18446744073709551552#64) := by
    rw [vecCap, (hdr_words top).2.2.1]
  have hl0 : vecLen M (top + 18446744073709551552#64) = 0#64 := by rw [vecLen, (hdr_words top).2.2.2.1]; exact hl
  rw [hr10] at hlen hroom
  obtain ⟨hc1, hp1⟩ := hroom (by rw [hr11, e0, hl0]; simp; exact hncap)
  rw [e0, e0'] at hc1
  have hp1' : m1.getMem (top + 18446744073709551560#64) = M.getMem (top + 18446744073709551560#64) := by
    rw [vecPtr, vecPtr, (hdr_words top).2.2.2.2] at hp1; exact hp1
  have hl1 : m1.getMem (top + 18446744073709551568#64) = M.getMem (top + 18446744073709551568#64) := by
    have := hlen.trans hl0; rw [vecLen, (hdr_words top).2.2.2.1] at this; rw [this, hl]
  have hsp : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by tn
  have hout : ∀ x : Word, top.toNat - 40 ≤ x.toNat → x.toNat < top.toNat → m1.getMem x = M.getMem x :=
    fun x h0 h1 => hf.getMem_above hlim (by omega) fun hg => by
      simp only [GrowOut, hr10, (hdr_words top).1, (hdr_words top).2.1] at hg
      rcases hg with rfl | rfl
      · omega
      · rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h0; omega
  obtain ⟨s1, s2, s3, s4, s5⟩ := hSv
  refine ⟨Env.Frame.trans hF hf (by omega) fun a ha => Or.inl ?_, hc.trans hcM, hs,
    ⟨(hout _ (by tn) (by tn)).trans s1, (hout _ (by tn) (by tn)).trans s2, (hout _ (by tn) (by tn)).trans s3,
      (hout _ (by tn) (by tn)).trans s4, (hout _ (by tn) (by tn)).trans s5⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [GrowOut, hr10, (hdr_words top).1, (hdr_words top).2.1] at ha
    rcases ha with rfl | rfl <;> exact ⟨by tn, by tn⟩
  · rw [hc1, hp1']; exact hb.mono hf.1
  · rw [hc1]; exact hcap
  · rw [hc1]; exact hncap
  · rw [hc1, hp1']; exact hfr
  · rw [hl1]; exact hl


set_option rv_sym.heap true in
/-- **`reserve(len / 2)`**, then the copy loop, or the exit when there is no pair. -/
theorem res_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR : Nat} (hnR : 64 + needR ≤ need) (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hloop : ∀ k R M, LInv env ret top regs m ((regs .x12).toNat / 2) k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 76, ret, top⟩ :: rest, R, M⟩)
    (hfin : ∀ R M, FinInv env ret top regs m ((regs .x12).toNat / 2) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 90, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, RInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 50, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, -, -, hK, hH, hS⟩ := id hinv
  have hV := hH.vecT (by omega) hW.top_le hal
  rv_introT hinv
  rv_symT hp stop [76, 90] with [hL, (by omega : env.stackLimit.toNat + 64 ≤ top.toNat)] using [hres]
  all_goals
    have hlay := env.layout
    have hsp : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by tn
    have hH1 := hH.reserve (by rw [hsp]; omega) (by rw [hsp]; omega)
      (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte])
      (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]; exact shr1 _) hret1_14 hret1_25 hret1_15
      ⟨hret1_16, hret1_17, hret1_18⟩
    have hz : m1.getMem (top + 18446744073709551568#64) = 0#64 := hH1.2.2.2.2.2.2.2.2
    have hn2 := shr1 (regs .x12)
  -- no pair: the exit
  · refine hfin _ _ ⟨by rv_closeT, by rv_closeT, ?_, rfl, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hH1⟩
    · simp only [Tactic.rf, hz]
      have := congrArg BitVec.toNat hc; rw [hn2] at this; simp only [BitVec.toNat_ofNat] at this; rw [this]
    · have := congrArg BitVec.toNat hc; rw [hn2] at this; simp only [BitVec.toNat_ofNat] at this; omega
  -- the copy loop
  · have hn0 : (regs .x12).toNat / 2 ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [hn2, h]; rfl))
    obtain ⟨wl, ww, wa⟩ := hS.resolve_left (by omega)
    have hw := ww.lt
    have hw2 : (regs .x11).toNat + 8 * (regs .x12).toNat ≤ 0xc0000000 := by
      have := env.layout; unfold InWin at ww; rcases ww with h | h <;> omega
    refine hloop _ _ _ ⟨by rv_closeT, by rv_closeT, ?_, ?_, ?_, ?_, by omega, Nat.le_refl _, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hH1, wl, ww, wa⟩
    all_goals simp only [Tactic.rf, hz]
    · rw [BitVec.zero_add]; apply BitVec.eq_of_toNat_eq; rw [hn2, BitVec.toNat_ofNat]; omega
    · rw [toNat_add_ofNat (by omega)]
    · rw [BitVec.toNat_add, toNat_add_ofNat (by omega), shl4 (x := regs .x12 >>> 1) (by rw [hn2]; omega), hn2]; omega
    · have hcap1 := hH1.2.2.2.2.2.2.1
      obtain ⟨-, hql, -⟩ := hH1.2.2.2.2.1.resolve_left (by omega)
      have hnx1 := hH1.1.2.1
      unfold Env.Live at hql
      have hlay := env.layout
      rw [show (0#64 : Word) <<< 4 = 0#64 from rfl, BitVec.zero_add, toNat_add_ofNat (by omega)]

set_option rv_sym.heap true in
/-- **`ext_row` is total**: the allocation of `len / 2` elements, the header, then `reserve` and the copy. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR needA needH : Nat} (hnR : 64 + needR ≤ need) (hnA : 64 + needA ≤ need) (hnH : 64 + needH ≤ need)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hhe : Aborts env p L.handleError.idx needH) : specT env p i need := by
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 64 ≤ top.toNat)]
  have hfin := fin_ok env p i L hp hk hpre_3 (by omega) hpre_11 hpre_12 hpre_6 hpre_7 (hpre_2 ▸ ⟨hpre_8, hpre_9⟩)
    (n := (regs .x12).toNat / 2)
  have hres_ok := res_ok env p i L hp hL hnR hres hstop hpre_3 hpre_11 hpre_12
    (loop env p i L hp hpre_3 (by omega) hpre_11 hpre_12 hfin) hfin
  clear hfin
  have hl60 : (regs .x12).toNat = 0 ∨ (regs .x12).toNat < 2 ^ 60 := by
    rcases hpre_10 with h | ⟨h1, -, -⟩
    · exact .inl h
    · right; unfold Env.Live at h1; have := env.layout; have := hpre_12.top_le; omega
  have hn2 := shr1 (regs .x12)
  rv_symT hp stop [50] with [hL, (by omega : env.stackLimit.toNat + 64 ≤ top.toNat)] using [hac, hhe]
  · refine hres_ok _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpre_10⟩
    all_goals rv_closeT
    exact .inl rfl
  · have hc' : (regs .x12).toNat / 2 ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [hn2, h]; rfl))
    rw [shl4 (x := regs .x12 >>> 1) (by rw [hn2]; omega), hn2]; omega
  · refine hres_ok _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpre_10⟩
    all_goals rv_closeT
    · have hc' : (regs .x12).toNat / 2 ≠ 0 := fun h => hc_1 (BitVec.eq_of_toNat_eq (by rw [hn2, h]; rfl))
      refine .inr ⟨by have := hpre_12.next_ge; omega, ?_, hret1_17⟩
      unfold Env.Live
      repeat (rw [Env.next_setMem_stack]; rotate_left; tn)
      rw [shl4 (x := regs .x12 >>> 1) (by rw [hn2]; omega)] at hret1_18; omega
    · exact .inr hret1_16

end Rv64mc.Proof.Whir.ExtRowT

/-- info: 'Rv64mc.Proof.Whir.ExtRowT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.ExtRowT.total
