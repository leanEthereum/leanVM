/-
  Rv64mc.Proof.Runtime.MemcpyT

  `compiler_builtins`' `memcpy(dst, src, n)` is total (`MemcpySpecT`, `Spec/Runtime/MemT.lean`'s pre- and
  postcondition): it returns `dst` with `[dst, dst + n)` holding what `[src, src + n)` held, every other byte apart
  from its stack kept. Below 16 bytes it copies a byte at a time; from 16 on, the bytes up to the destination's first
  8-byte boundary, then the destination's doublewords, then the bytes after them. A source as aligned as the
  destination is copied a doubleword at a time; another is read a source doubleword at a time and each destination
  doubleword reassembled from two (`extractByte_shr_or_shl`), the partial first and last source doublewords read
  through the stack slot (`load_aligned_end_partial`, `load_aligned_partial`), so that no byte outside the source is
  read.

  The proof is cut at the loops' heads and at the joins of the partial loads: each part a theorem from its program
  counter, stepped by `rv_symT`, with the copy so far as `CopyT.Inv`. Every loop is `Total.loop` with the bytes or the
  count left as the measure (`DInv`, `CInv`, `BInv`, `AInv`).

  ## Main definitions

  * `MemcpySpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.CopyT
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.CompilerBuiltins.Mem.Memcpy

namespace Rv64mc.Proof.Runtime.MemcpyT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime.CopyT
open Rv64mc.Proof.Runtime.MemsetT (InWin Kept)
open Rv64mc.Gen.CompilerBuiltins.Mem.Memcpy (Link tmpl)

/-- **The total contract of `memcpy`**: from `CopyPreT false`, it returns `dst` with `[dst, dst + n)` holding what
    `[src, src + n)` held, writing at most the doublewords of the destination besides its stack (`CopyOut`). -/
def MemcpySpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (CopyPreT false env) (CopyPostT env) CopyOut

/-- The registers the body keeps: the return address, the stack pointer 16 below `top`, the saved registers and
    `dst`. -/
def Regs (ret top : Word) (regs r : Reg → Word) : Prop :=
  r .x1 = ret ∧ AbiRegs (top + 0xfffffffffffffff0#64) regs r ∧ r .x10 = regs .x10

theorem Regs.upd {ret top : Word} {regs r : Reg → Word} (h : Regs ret top regs r) {d : Reg}
    (hd : d ∈ [.x5, .x6, .x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29]) (v : Word) :
    Regs ret top regs (updReg r d v) := by
  obtain ⟨h1, ha, h10⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  refine ⟨?_, (AbiRegs.updReg_iff (by rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide)).2 ha, ?_⟩ <;>
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [updReg_apply]

/-- A side goal about numbers with literals' `toNat` computed. -/
macro "tlit" : tactic => `(tactic| ((try tnorm) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
  show ((UnOp.sext .b4).eval 6#64 : Word) = 6#64 by decide, show ((UnOp.sext .b4).eval 2#64 : Word) = 2#64 by decide,
  show ((UnOp.sext .b4).eval 3#64 : Word) = 3#64 by decide])
  <;> omega))

/-- `Regs` through the body's writes of scratch registers. -/
macro "regs_ok " h:term : tactic => `(tactic| ((repeat (apply Regs.upd _ (by decide))) <;> exact $h))

/-- What the entry gives every part of the body: `n` bytes, the windows, the stack slot, the two ranges apart. -/
structure Fx (env : Env) (top dst src : Word) (n : Nat) (m : MachineState) : Prop where
  win : Windows env top m
  room : env.stackLimit.toNat + 16 ≤ top.toNat
  al : top.toNat % 16 = 0
  dwin : InWin env dst n
  doff : OffStack env top dst n
  swin : inWindow src n = true
  soff : OffStack env top src n
  disj : ∀ k, k < n → ∀ k', k' < n → dst.toNat + k ≠ src.toNat + k'

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {Q : State rvIsa → Prop} {ret top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState}

theorem ofNat_add_toNat (a : Word) (k : Nat) : BitVec.ofNat 64 (a.toNat + k) = a + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-- The continuation a part of the body is proved against: the contract's, at the return. -/
abbrev Cont (env : Env) (p : Lprog (Op Reg) Reg) (Q : State rvIsa → Prop) (ret top : Word) (rest : List Frame)
    (regs : Reg → Word) (m : MachineState) : Prop :=
  ∀ r' m', HoldsT.post env (CopyPostT env) CopyOut ret top regs m r' m' → rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩

/-- The return, with every byte copied. -/
theorem ret_ok (hp : p[i]? = some (tmpl L)) (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top)
    {r : Reg → Word} {M : MachineState} (hR : Regs ret top regs r)
    (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M (regs .x12).toNat) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 196, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h1, ha, h10⟩ := hR
  have hx2 : r .x2 + 16#64 = top := by
    rw [ha.1, BitVec.add_assoc, show (0xfffffffffffffff0#64 + 16#64 : Word) = 0#64 by decide, BitVec.add_zero]
  rv_symT hp with [h1, hx2]
  refine hk _ _ ⟨⟨?_, hI.1.1, hI.1.2.1, by simpa [updReg_apply] using h10, fun k hk' => ?_, fun b hb hs => ?_⟩,
    hI.1.2.2⟩
  · obtain ⟨_, h8, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ha
    exact ⟨by simpa [updReg_apply] using hx2, by simpa [updReg_apply] using h8, by simpa [updReg_apply] using h9,
      by simpa [updReg_apply] using h18, by simpa [updReg_apply] using h19, by simpa [updReg_apply] using h20,
      by simpa [updReg_apply] using h21, by simpa [updReg_apply] using h22, by simpa [updReg_apply] using h23,
      by simpa [updReg_apply] using h24, by simpa [updReg_apply] using h25, by simpa [updReg_apply] using h26,
      by simpa [updReg_apply] using h27⟩
  · have := hI.2.1 k hk'
    simpa only [bat, ofNat_add_toNat] using this
  · have := hI.2.2 b.toNat b.isLt (by unfold InRange at hb; omega) (by unfold OffStack at hs; rw [hsp] at hs; omega)
    simpa only [bat, ofNat_toNat'] using this

theorem toNat_dec {a : Word} (h : 0 < a.toNat) : (a + 0xffffffffffffffff#64).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

theorem extractByte_zext_getByte (M : MachineState) (x : Word) :
    extractByte ((M.getByte x).zeroExtend 64) 0 = bat M x.toNat := by
  rw [bat, ofNat_toNat']
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [extractByte, hi]

/-- A source byte reads as at entry while the copy runs. -/
theorem Fx.src {top dst src : Word} {n j k : Nat} {M : MachineState} (F : Fx env top dst src n m)
    (hI : Inv env top dst src n m M j) (hj : j ≤ n) (hk : k < n) :
    bat M (src.toNat + k) = bat m (src.toNat + k) := by
  have hsw := inWindow_iff.1 F.swin
  have hs := F.soff
  unfold OffStack at hs
  exact hI.src (by omega) (fun ⟨h1, h2⟩ => F.disj (src.toNat + k - dst.toNat) (by omega) k hk (by omega))
    (by omega)

/-- The last bytes' loop at its head: `c` left, `x13` and `x11` the next byte of each range. -/
def DInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (c : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  Regs ret top regs r ∧ Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M ((regs .x12).toNat - c) ∧
    (r .x13).toNat = (regs .x10).toNat + ((regs .x12).toNat - c) ∧
    (r .x11).toNat = (regs .x11).toNat + ((regs .x12).toNat - c) ∧ (r .x12).toNat = c ∧ 0 < c ∧
    c ≤ (regs .x12).toNat

/-- The last bytes, one at a time. -/
theorem loopD_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) :
    ∀ c r M, DInv env ret top regs m c r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 184, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (DInv env ret top regs m) fun c r M ⟨hR, hI, h13, h11, h12, hc0, hcn⟩ ih => ?_
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hx13 : r .x13 = BitVec.ofNat 64 ((regs .x10).toNat + ((regs .x12).toNat - c)) := by
    rw [← h13, ofNat_toNat']
  have hv : extractByte ((M.getByte (r .x11)).zeroExtend 64) 0 =
      bat m ((regs .x11).toNat + ((regs .x12).toNat - c)) := by
    rw [extractByte_zext_getByte, h11]; exact F.src hI (by omega) (by omega)
  have hI' := hI.byte F.dwin (x := r .x13) (by omega) (by omega) hv
  have h12' := toNat_dec (a := r .x12) (by omega)
  rv_symT hp stop [196]
  · refine ih (c - 1) _ _ (by omega) ⟨by regs_ok hR, ?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [show (regs .x12).toNat - (c - 1) = (regs .x12).toNat - c + 1 by omega]; exact hI'
    · tnorm; rw [toNat_add_ofNat (by omega)]; omega
    · tnorm; rw [toNat_add_ofNat (by omega)]; omega
    · tnorm; omega
    · have : (r .x12 + 0xffffffffffffffff#64).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
      omega
  · have : (r .x12 + 0xffffffffffffffff#64).toNat = 0 := by rw [hc]; rfl
    refine ret_ok hp hk hsp (by regs_ok hR) ?_
    rw [show (regs .x12).toNat - c + 1 = (regs .x12).toNat by omega] at hI'; exact hI'

/-- After the doublewords: `j` bytes copied, `x13` the next byte of the destination, `x11 + x15` of the source, and
    `x12 % 8` bytes left. -/
theorem tail_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (h13 : (r .x13).toNat = (regs .x10).toNat + j) (h11 : (r .x11).toNat + (r .x15).toNat = (regs .x11).toNat + j)
    (h12 : (r .x12).toNat % 8 = (regs .x12).toNat - j) (hj : j ≤ (regs .x12).toNat) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 176, ret, top⟩ :: rest, r, M⟩ := by
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have h7 := Proof.Runtime.Alloc.and7 (r .x12)
  have h11' : (r .x11 + r .x15).toNat = (regs .x11).toNat + j := by rw [BitVec.toNat_add]; omega
  have h14 : (r .x13 + (r .x12 &&& 7#64)).toNat = (regs .x10).toNat + (regs .x12).toNat := by
    rw [BitVec.toNat_add, h7]; omega
  rv_symT hp stop [184, 196]
  · have hc' := BitVec.le_def.1 hc
    rw [h14, h13] at hc'
    refine ret_ok hp hk hsp (by regs_ok hR) ?_
    rw [show j = (regs .x12).toNat by omega] at hI; exact hI
  · have hc' := BitVec.lt_def.1 hc
    rw [h14, h13] at hc'
    refine loopD_ok hp F hk hsp ((regs .x12).toNat - j) _ _ ⟨by regs_ok hR, ?_, ?_, ?_, ?_, by omega, by omega⟩
    · rw [show (regs .x12).toNat - ((regs .x12).toNat - j) = j by omega]; exact hI
    · tnorm; omega
    · tnorm; omega
    · tnorm; omega

/-- The aligned doublewords' loop at its head, `k` bytes of them left: `x14` and `x16` the next doubleword of each
    range, both 8-byte aligned, `j` bytes copied. -/
def CInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  ∃ j, Regs ret top regs r ∧ Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j ∧
    (r .x14).toNat = (regs .x10).toNat + j ∧ (r .x16).toNat = (regs .x11).toNat + j ∧
    (r .x13).toNat = (regs .x10).toNat + j + k ∧ k % 8 = 0 ∧ 0 < k ∧ (r .x14).toNat % 8 = 0 ∧
    (r .x16).toNat % 8 = 0 ∧ (r .x11).toNat + (r .x15).toNat = (regs .x11).toNat + j + k ∧
    (r .x12).toNat % 8 = (regs .x12).toNat - (j + k) ∧ j + k ≤ (regs .x12).toNat

/-- The doublewords, the source as aligned as the destination. -/
theorem loopC_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) :
    ∀ k r M, CInv env ret top regs m k r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 166, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (CInv env ret top regs m)
    fun k r M ⟨j, hR, hI, h14, h16, h13, hk8, hk0, ha14, ha16, h11, h12, hjk⟩ ih => ?_
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hv : ∀ t, t < 8 → extractByte (M.getMem (r .x16)) t = bat m ((regs .x11).toNat + j + t) := by
    intro t ht
    have := extractByte_loadVal (w := .b8) (M := M) (x := r .x16) (t := t) ha16 ht
    rw [show Tactic.loadVal .b8 M (r .x16) = M.getMem (r .x16) from rfl] at this
    rw [this, h16, Nat.add_assoc]; exact F.src hI (by omega) (by omega)
  have hI' := hI.word F.dwin (x := r .x14) h14 ha14 (by omega) hv
  have h14' : (r .x14 + 8#64).toNat = (r .x14).toNat + 8 := toNat_add_ofNat (by omega)
  have h16' : (r .x16 + 8#64).toNat = (r .x16).toNat + 8 := toNat_add_ofNat (by omega)
  rv_symT hp stop [176]
  · have hc' := BitVec.lt_def.1 hc
    rw [h14', h14, h13] at hc'
    refine ih (k - 8) _ _ (by omega) ⟨j + 8, by regs_ok hR, hI', ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_,
      by omega⟩ <;> tnorm <;> omega
  · have hc' := BitVec.le_def.1 hc
    rw [h14', h14, h13] at hc'
    refine tail_ok hp F hk hsp (j := j + 8) (by regs_ok hR) hI' ?_ ?_ ?_ (by omega) <;> tnorm <;> omega

/-- The last doubleword of a misaligned source: `x5` holds the bytes from `o` on of the previous source doubleword, the
    stack slot the first `o` bytes of the next. -/
theorem lastWord_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j o : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (ho1 : 0 < o) (ho8 : o < 8) (h14 : (r .x14).toNat = (regs .x10).toNat + j) (ha14 : (r .x14).toNat % 8 = 0)
    (h13 : (r .x13).toNat = (regs .x10).toNat + j + 8) (hj : j + 8 ≤ (regs .x12).toNat) (hoj : o ≤ (regs .x11).toNat + j)
    (h5 : ∀ t, o ≤ t → t < 8 → extractByte (r .x5) t = bat m ((regs .x11).toNat + j - o + t))
    (hS : ∀ t, t < o → bat M (top.toNat - 8 + t) = bat m ((regs .x11).toNat + j + 8 - o + t))
    (h17 : (r .x17).toNat = 8 * o) (h11 : (r .x11).toNat + (r .x15).toNat = (regs .x11).toNat + j + 8)
    (h12 : (r .x12).toNat % 8 = (regs .x12).toNat - (j + 8)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 138, ret, top⟩ :: rest, r, M⟩ := by
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hroom := F.room
  have hal := F.al
  have hx2 := hR.2.1.1
  have hs8 : (r .x2 + 8#64).toNat = top.toNat - 8 := by
    rw [hx2, BitVec.add_assoc, BitVec.toNat_add,
      show (18446744073709551600#64 + 8#64 : Word).toNat = 18446744073709551608 by decide]; omega
  obtain ⟨s1, s2⟩ := shamt h17 ho1 ho8
  have hv : ∀ t, t < 8 → extractByte (M.getMem (r .x2 + 8#64) <<< (0#64 - r .x17 &&& 56#64 &&& 63#64).toNat |||
      r .x5 >>> (r .x17 &&& 63#64).toNat) t = bat m ((regs .x11).toNat + j + t) := by
    intro t ht
    rw [s1, s2, BitVec.or_comm, extractByte_shr_or_shl _ _ o t ho1 ho8 ht]
    split
    · rw [h5 _ (by omega) (by omega)]; congr 1; omega
    · have := extractByte_loadVal (w := .b8) (M := M) (x := r .x2 + 8#64) (t := t + o - 8)
        (by rw [hs8]; show _ % 8 = 0; omega) (by show _ < 8; omega)
      rw [show Tactic.loadVal .b8 M (r .x2 + 8#64) = M.getMem (r .x2 + 8#64) from rfl] at this
      rw [this, hs8, hS _ (by omega)]; congr 1; omega
  have hI' := hI.word F.dwin h14 ha14 hj hv
  rv_symT hp stop [176] with [hx2]
  refine tail_ok hp F hk hsp (j := j + 8) (by regs_ok hR) hI' ?_ ?_ ?_ hj <;> tnorm <;> omega

theorem slot_addr {top : Word} {r : Reg → Word} (hx2 : r .x2 = top + 0xfffffffffffffff0#64)
    (hroom : 16 ≤ top.toNat) : (r .x2 + 8#64).toNat = top.toNat - 8 := by
  rw [hx2, BitVec.add_assoc, BitVec.toNat_add,
    show (18446744073709551600#64 + 8#64 : Word).toNat = 18446744073709551608 by decide]; omega

/-- The last byte of `load_aligned_partial`, at `x7 = o - 1`. -/
theorem lastByte_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j o : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (ho1 : 0 < o) (ho8 : o < 8) (h14 : (r .x14).toNat = (regs .x10).toNat + j) (ha14 : (r .x14).toNat % 8 = 0)
    (h13 : (r .x13).toNat = (regs .x10).toNat + j + 8) (hj : j + 8 ≤ (regs .x12).toNat) (hoj : o ≤ (regs .x11).toNat + j)
    (h5 : ∀ t, o ≤ t → t < 8 → extractByte (r .x5) t = bat m ((regs .x11).toNat + j - o + t))
    (h17 : (r .x17).toNat = 8 * o) (h11 : (r .x11).toNat + (r .x15).toNat = (regs .x11).toNat + j + 8)
    (h12 : (r .x12).toNat % 8 = (regs .x12).toNat - (j + 8))
    (h6 : (r .x6).toNat + o = (regs .x11).toNat + j + 8) (h7 : (r .x7).toNat + 1 = o)
    (hS : ∀ t, t < o - 1 → bat M (top.toNat - 8 + t) = bat m ((r .x6).toNat + t)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 128, ret, top⟩ :: rest, r, M⟩ := by
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hroom := F.room
  have hal := F.al
  have hx2 := hR.2.1.1
  have hs8 := slot_addr hx2 (by omega)
  have hX : r .x2 + 8#64 ||| r .x7 = BitVec.ofNat 64 (top.toNat - 8 + (o - 1)) := by
    rw [or_eq_add (by rw [hs8]; omega) (by omega)]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hs8, BitVec.toNat_ofNat]; omega
  have hY : (r .x6 + r .x7).toNat = (r .x6).toNat + (o - 1) := by rw [BitVec.toNat_add]; omega
  have hdn : (regs .x10).toNat + (regs .x12).toNat < 2 ^ 64 := by have := env.heapEnd.isLt; omega
  obtain ⟨hI', hS'⟩ := slot_copy (w := .b1) (X := r .x2 + 8#64 ||| r .x7)
    (v := Tactic.loadVal .b1 M (r .x6 + r .x7)) hI F.doff (by omega) hdn hroom (by omega) hS
    (by rw [hX, BitVec.toNat_ofNat]; omega) (Nat.mod_one _) (by show _ + 1 ≤ 8; omega)
    (fun u hu => by
      have hb1 : Width.b1.bytes = 1 := rfl
      rw [show Tactic.loadVal .b1 M (r .x6 + r .x7) = if false then (UnOp.sext .b1).eval
        (Tactic.loadVal .b1 M (r .x6 + r .x7)) else Tactic.loadVal .b1 M (r .x6 + r .x7) from rfl,
        extractByte_load false (Nat.mod_one _) hu, hY]
      have := F.src (k := (regs .x11).toNat + j + 8 - o + (o - 1) + u - (regs .x11).toNat) hI (by omega) (by omega)
      rw [show (regs .x11).toNat + ((regs .x11).toNat + j + 8 - o + (o - 1) + u - (regs .x11).toNat) =
        (r .x6).toNat + (o - 1) + u by omega] at this
      rw [this])
  rv_symT hp stop [138] with [hx2]
  · rw [hX]
    exact hW.stack (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega)
  · refine lastWord_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI' ho1 ho8 ?_ ?_ ?_ hj hoj ?_ ?_ ?_ ?_ ?_
    · tnorm; exact h14
    · tnorm; exact ha14
    · tnorm; exact h13
    · tnorm; exact h5
    · intro t ht
      have hb1 : Width.b1.bytes = 1 := rfl
      exact (hS' t (by omega)).trans (by congr 1; omega)
    · tnorm; exact h17
    · tnorm; exact h11
    · tnorm; exact h12

/-- `load_aligned_partial` at its last chunk: a byte if `o` is odd, the bytes below `o`'s low bit copied. -/
theorem bit0_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j o : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (ho1 : 0 < o) (ho8 : o < 8) (h14 : (r .x14).toNat = (regs .x10).toNat + j) (ha14 : (r .x14).toNat % 8 = 0)
    (h13 : (r .x13).toNat = (regs .x10).toNat + j + 8) (hj : j + 8 ≤ (regs .x12).toNat) (hoj : o ≤ (regs .x11).toNat + j)
    (h5 : ∀ t, o ≤ t → t < 8 → extractByte (r .x5) t = bat m ((regs .x11).toNat + j - o + t))
    (h17 : (r .x17).toNat = 8 * o) (h11 : (r .x11).toNat + (r .x15).toNat = (regs .x11).toNat + j + 8)
    (h12 : (r .x12).toNat % 8 = (regs .x12).toNat - (j + 8)) (h11o : (r .x11).toNat % 8 = o)
    (h6 : (r .x6).toNat + o = (regs .x11).toNat + j + 8) (h7 : (r .x7).toNat = o / 2 * 2)
    (hS : ∀ t, t < o / 2 * 2 → bat M (top.toNat - 8 + t) = bat m ((r .x6).toNat + t)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 124, ret, top⟩ :: rest, r, M⟩ := by
  have hx2 := hR.2.1.1
  rv_symT hp stop [128, 138] with [hx2]
  · have := (and1_zero _).1 hc
    refine lastWord_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI ho1 ho8 ?_ ?_ ?_ hj hoj ?_ ?_ ?_ ?_ ?_
    · tnorm; exact h14
    · tnorm; exact ha14
    · tnorm; exact h13
    · tnorm; exact h5
    · intro t ht; exact (hS t (by omega)).trans (by congr 1; omega)
    · tnorm; exact h17
    · tnorm; exact h11
    · tnorm; exact h12
  · have : ¬ (r .x11).toNat % 2 = 0 := fun h => hc ((and1_zero _).2 h)
    refine lastByte_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI ho1 ho8 ?_ ?_ ?_ hj hoj ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · tnorm; exact h14
    · tnorm; exact ha14
    · tnorm; exact h13
    · tnorm; exact h5
    · tnorm; exact h17
    · tnorm; exact h11
    · tnorm; exact h12
    · tnorm; exact h6
    · tnorm; omega
    · intro t ht; tnorm; exact hS t (by omega)

/-- The first `o` bytes of the last source doubleword, into the stack slot: a word, a halfword and a byte as `o`'s
    bits say (`load_aligned_partial`). -/
theorem partial_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j o : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (ho1 : 0 < o) (ho8 : o < 8) (h14 : (r .x14).toNat = (regs .x10).toNat + j) (ha14 : (r .x14).toNat % 8 = 0)
    (h13 : (r .x13).toNat = (regs .x10).toNat + j + 8) (hj : j + 8 ≤ (regs .x12).toNat) (hoj : o ≤ (regs .x11).toNat + j)
    (h6 : (r .x6).toNat + o = (regs .x11).toNat + j) (ha6 : (r .x6).toNat % 8 = 0)
    (h5 : ∀ t, o ≤ t → t < 8 → extractByte (r .x5) t = bat m ((regs .x11).toNat + j - o + t))
    (h16 : (r .x16).toNat = o) (h17 : (r .x17).toNat = 8 * o) (h11o : (r .x11).toNat % 8 = o)
    (h11 : (r .x11).toNat + (r .x15).toNat = (regs .x11).toNat + j + 8)
    (h12 : (r .x12).toNat % 8 = (regs .x12).toNat - (j + 8)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 110, ret, top⟩ :: rest, r, M⟩ := by
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hroom := F.room
  have hal := F.al
  have hx2 := hR.2.1.1
  have hs8 := slot_addr hx2 (by omega)
  have h6' : (r .x6 + 8#64).toNat = (r .x6).toNat + 8 := toNat_add_ofNat (by omega)
  have hX0 : r .x2 + 8#64 ||| 0#64 = r .x2 + 8#64 := BitVec.or_zero
  have hX4 : r .x2 + 8#64 ||| 4#64 = BitVec.ofNat 64 (top.toNat - 4) := by
    rw [or_eq_add (by rw [hs8]; omega) (by decide)]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hs8, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]
    omega
  have h4 : (BitVec.ofNat 64 (top.toNat - 4)).toNat = top.toNat - 4 := by rw [BitVec.toNat_ofNat]; omega
  have hb1 : Width.b1.bytes = 1 := rfl
  have hb2 : Width.b2.bytes = 2 := rfl
  have hb4 : Width.b4.bytes = 4 := rfl
  have hb8 : Width.b8.bytes = 8 := rfl
  have hdn : (regs .x10).toNat + (regs .x12).toNat < 2 ^ 64 := by have := env.heapEnd.isLt; omega
  have src : ∀ M', Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M' j → ∀ u, u < o →
      bat M' ((r .x6).toNat + 8 + u) = bat m ((r .x6).toNat + 8 + u) := fun M' hI' u hu => by
    have := F.src (k := (r .x6).toNat + 8 + u - (regs .x11).toNat) hI' (by omega) (by omega)
    rwa [show (regs .x11).toNat + ((r .x6).toNat + 8 + u - (regs .x11).toNat) = (r .x6).toNat + 8 + u by omega]
      at this
  have hI1 := hI.slot (w := .b8) (x := r .x2 + 8#64) (v := 0#64) F.doff (by omega) hdn hroom (by omega)
    (by omega) (by omega) (by rw [hs8]; show _ % 8 = 0; omega)
  have hS0 : ∀ t, t < 0 → bat (Tactic.storeMem .b8 M (r .x2 + 8#64) 0#64) (top.toNat - 8 + t) =
      bat m ((r .x6).toNat + 8 + t) := fun _ h => absurd h (Nat.not_lt_zero _)
  -- the halfword or the word at the slot's start
  have cp0 := fun (w : Width) (hw : w = .b2 ∨ w = .b4) (hwo : w.bytes ≤ o) =>
    slot_copy (w := w) (X := r .x2 + 8#64) (i := 0)
      (v := (UnOp.sext w).eval (Tactic.loadVal w (Tactic.storeMem .b8 M (r .x2 + 8#64) 0#64) (r .x6 + 8#64)))
      hI1 F.doff (by omega) hdn hroom (by omega) hS0 (by rw [hs8]; rfl) (by rcases hw with rfl | rfl <;> (rw [hs8]; show _ % _ = 0; simp only [Width.bytes]; omega))
      (by rcases hw with rfl | rfl <;> decide) (fun u hu => by
        have := extractByte_load (M := Tactic.storeMem .b8 M (r .x2 + 8#64) 0#64) (x := r .x6 + 8#64) (u := u) true
          (by rcases hw with rfl | rfl <;> (rw [h6']; simp only [Width.bytes]; omega)) hu
        simp only [↓reduceIte] at this
        rw [this, h6', src _ hI1 u (by omega)])
  -- the halfword at byte 4, after the word
  have h12' : (r .x6 + 12#64).toNat = (r .x6).toNat + 12 := toNat_add_ofNat (by omega)
  have cp4 := fun {M2 : MachineState} (hI2 : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M2 j)
      (hS2 : ∀ t, t < 0 + Width.b4.bytes → bat M2 (top.toNat - 8 + t) = bat m ((r .x6).toNat + 8 + t))
      (ho6 : 6 ≤ o) =>
    slot_copy (w := .b2) (X := BitVec.ofNat 64 (top.toNat - 4)) (i := 4)
      (v := (UnOp.sext .b2).eval (Tactic.loadVal .b2 M2 (r .x6 + 12#64))) hI2 F.doff (by omega) hdn hroom
      (by omega) (fun t ht => hS2 t (by omega)) (by rw [h4]; omega) (by rw [h4, hb2]; omega) (by decide)
      (fun u hu => by
        have := extractByte_load (M := M2) (x := r .x6 + 12#64) (u := u) true (by rw [h12', hb2]; omega) hu
        simp only [↓reduceIte] at this
        rw [this, h12', show (r .x6).toNat + 12 + u = (r .x6).toNat + 8 + (u + 4) by omega,
          src _ hI2 _ (by rw [hb2] at hu; omega)])
  rv_symT hp stop [124, 128, 138] with [hx2]
  all_goals try rw [hX4]
  all_goals try rw [hX0]
  rv_closeT
  -- `o` is 4 or 5: a word
  · have ho4 : 4 ≤ o := by have := BitVec.le_def.1 hc_1; rw [h16] at this; exact this
    have ho2 := (and2_zero _).1 hc
    obtain ⟨hI2, hS2⟩ := cp0 .b4 (.inr rfl) (by rw [hb4]; omega)
    refine bit0_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI2 ho1 ho8 ?_ ?_ ?_ hj hoj ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · tlit
    · tlit
    · intro t ht; tnorm; rw [h6']; exact hS2 t (by omega)
  -- `o` is 7: a word, a halfword, then the last byte
  · have ho4 : 4 ≤ o := by have := BitVec.le_def.1 hc_1; rw [h16] at this; exact this
    have ho2 : ¬ (r .x11).toNat % 4 < 2 := fun h => hc_2 ((and2_zero _).2 h)
    have ho0 : ¬ (r .x11).toNat % 2 = 0 := fun h => hc ((and1_zero _).2 h)
    obtain ⟨hI2, hS2⟩ := cp0 .b4 (.inr rfl) (by rw [hb4]; omega)
    obtain ⟨hI3, hS3⟩ := cp4 hI2 hS2 (by omega)
    refine lastByte_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI3 ho1 ho8 ?_ ?_ ?_ hj hoj ?_ ?_ ?_ ?_ ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · tlit
    · tlit
    · intro t ht; tnorm; rw [h6']; exact hS3 t (by omega)
  -- `o` is 6: a word and a halfword
  · have ho4 : 4 ≤ o := by have := BitVec.le_def.1 hc_1; rw [h16] at this; exact this
    have ho2 : ¬ (r .x11).toNat % 4 < 2 := fun h => hc_2 ((and2_zero _).2 h)
    have ho0 := (and1_zero _).1 hc
    obtain ⟨hI2, hS2⟩ := cp0 .b4 (.inr rfl) (by rw [hb4]; omega)
    obtain ⟨hI3, hS3⟩ := cp4 hI2 hS2 (by omega)
    refine lastWord_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI3 ho1 ho8 ?_ ?_ ?_ hj hoj ?_ ?_ ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · intro t ht; exact (hS3 t (by omega)).trans (by congr 1; omega)
  -- `o` is 3: a halfword, then the last byte
  · have ho4 : o < 4 := by have := BitVec.lt_def.1 hc_1; rw [h16] at this; exact this
    have ho2 : ¬ (r .x11).toNat % 4 < 2 := fun h => hc_2 ((and2_zero _).2 h)
    have ho0 : ¬ (r .x11).toNat % 2 = 0 := fun h => hc ((and1_zero _).2 h)
    obtain ⟨hI2, hS2⟩ := cp0 .b2 (.inl rfl) (by rw [hb2]; omega)
    refine lastByte_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI2 ho1 ho8 ?_ ?_ ?_ hj hoj ?_ ?_ ?_ ?_ ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · tlit
    · tlit
    · intro t ht; tnorm; rw [h6']; exact hS2 t (by omega)
  -- `o` is 2: a halfword
  · have ho4 : o < 4 := by have := BitVec.lt_def.1 hc_1; rw [h16] at this; exact this
    have ho2 : ¬ (r .x11).toNat % 4 < 2 := fun h => hc_2 ((and2_zero _).2 h)
    have ho0 := (and1_zero _).1 hc
    obtain ⟨hI2, hS2⟩ := cp0 .b2 (.inl rfl) (by rw [hb2]; omega)
    refine lastWord_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI2 ho1 ho8 ?_ ?_ ?_ hj hoj ?_ ?_ ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · intro t ht; exact (hS2 t (by omega)).trans (by congr 1; omega)
  -- `o` is 1: the byte alone
  · have ho4 : o < 4 := by have := BitVec.lt_def.1 hc_1; rw [h16] at this; exact this
    have ho2 := (and2_zero _).1 hc
    refine bit0_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI1 ho1 ho8 ?_ ?_ ?_ hj hoj ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · tlit
    · tlit
    · intro t ht; omega

/-- The misaligned doublewords' loop at its head, `k` bytes of the destination's doublewords left, at least two of
    them: `x6` the source doubleword `x5` was loaded from, `o` bytes below the next source byte. -/
def BInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (o k : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  ∃ j, Regs ret top regs r ∧ Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j ∧
    (r .x14).toNat = (regs .x10).toNat + j ∧ (r .x14).toNat % 8 = 0 ∧
    (r .x13).toNat = (regs .x10).toNat + j + k ∧ k % 8 = 0 ∧ 16 ≤ k ∧ j + k ≤ (regs .x12).toNat ∧
    (r .x6).toNat + o = (regs .x11).toNat + j ∧ (r .x6).toNat % 8 = 0 ∧
    (∀ t, o ≤ t → t < 8 → extractByte (r .x5) t = bat m ((r .x6).toNat + t)) ∧
    (r .x17).toNat = 8 * o ∧ (r .x7 &&& 63#64).toNat = 64 - 8 * o ∧ (r .x16).toNat = o ∧
    (r .x11).toNat % 8 = o ∧ (r .x11).toNat + (r .x15).toNat = (regs .x11).toNat + j + k ∧
    (r .x12).toNat % 8 = (regs .x12).toNat - (j + k)

/-- The doublewords of a misaligned source, each reassembled from two source doublewords. -/
theorem loopB_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {o : Nat} (ho1 : 0 < o) (ho8 : o < 8) :
    ∀ k r M, BInv env ret top regs m o k r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 90, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (BInv env ret top regs m o) fun k r M
    ⟨j, hR, hI, h14, ha14, h13, hk8, hk16, hjk, h6, ha6, h5, h17, h7, h16, h11o, h11, h12⟩ ih => ?_
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hx2 := hR.2.1.1
  have h6' : (r .x6 + 8#64).toNat = (r .x6).toNat + 8 := toNat_add_ofNat (by omega)
  have h14' : (r .x14 + 8#64).toNat = (r .x14).toNat + 8 := toNat_add_ofNat (by omega)
  have h14'' : (r .x14 + 16#64).toNat = (r .x14).toNat + 16 := toNat_add_ofNat (by omega)
  have s1 := (shamt h17 ho1 ho8).1
  have hcur : ∀ t, t < 8 → extractByte (M.getMem (r .x6 + 8#64)) t = bat m ((r .x6).toNat + 8 + t) := by
    intro t ht
    have := extractByte_loadVal (w := .b8) (M := M) (x := r .x6 + 8#64) (t := t) (by rw [h6']; show _ % 8 = 0; omega)
      ht
    rw [show Tactic.loadVal .b8 M (r .x6 + 8#64) = M.getMem (r .x6 + 8#64) from rfl] at this
    rw [this, h6']
    have := F.src (k := (r .x6).toNat + 8 + t - (regs .x11).toNat) hI (by omega) (by omega)
    rwa [show (regs .x11).toNat + ((r .x6).toNat + 8 + t - (regs .x11).toNat) = (r .x6).toNat + 8 + t by omega]
      at this
  have hv : ∀ t, t < 8 → extractByte (M.getMem (r .x6 + 8#64) <<< (r .x7 &&& 63#64).toNat |||
      r .x5 >>> (r .x17 &&& 63#64).toNat) t = bat m ((regs .x11).toNat + j + t) := by
    intro t ht
    rw [s1, h7, BitVec.or_comm, extractByte_shr_or_shl _ _ o t ho1 ho8 ht]
    split
    · rw [h5 _ (by omega) (by omega)]; congr 1; omega
    · rw [hcur _ (by omega)]; congr 1; omega
  have hI' := hI.word F.dwin h14 ha14 (by omega) hv
  rv_symT hp stop [110] with [hx2]
  · have hc' := BitVec.lt_def.1 hc
    rw [h14'', h13] at hc'
    refine ih (k - 8) _ _ (by omega) ⟨j + 8, by regs_ok hR, hI', ?_, ?_, ?_, by omega, by omega, by omega, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals (tnorm; assumption)
    any_goals (tnorm; omega)
    · intro t ht1 ht2; tnorm; rw [h6']; exact hcur t ht2
  · have hc' := BitVec.le_def.1 hc
    rw [h14'', h13] at hc'
    refine partial_ok hp F hk hsp (j := j + 8) (o := o) (by regs_ok hR) hI' ho1 ho8 ?_ ?_ ?_ (by omega) (by omega)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    any_goals (tnorm; assumption)
    any_goals (tnorm; omega)
    · intro t ht1 ht2; tnorm; rw [hcur t ht2]; congr 1; omega

/-- After `load_aligned_end_partial`: the stack slot holds the bytes from `o` on of the first source doubleword. -/
theorem prev_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j o N : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (ho1 : 0 < o) (ho8 : o < 8) (h14 : (r .x14).toNat = (regs .x10).toNat + j) (ha14 : (r .x14).toNat % 8 = 0)
    (h13 : (r .x13).toNat = (regs .x10).toNat + j + N) (hN8 : N % 8 = 0) (hN : 8 ≤ N) (hjN : j + N ≤ (regs .x12).toNat)
    (h11 : (r .x11).toNat = (regs .x11).toNat + j) (h16 : (r .x16).toNat = o) (h11o : ((regs .x11).toNat + j) % 8 = o)
    (h15 : (r .x15).toNat = N) (h12 : (r .x12).toNat % 8 = (regs .x12).toNat - (j + N))
    (hS : ∀ t, o ≤ t → t < 8 → bat M (top.toNat - 8 + t) = bat m ((regs .x11).toNat + j - o + t)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 76, ret, top⟩ :: rest, r, M⟩ := by
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hroom := F.room
  have hal := F.al
  have hx2 := hR.2.1.1
  have hs8 := slot_addr hx2 (by omega)
  have h17 := toNat_shl3 (x := r .x16) (by omega)
  rw [h16] at h17
  have h6 : (r .x11 - r .x16).toNat = (regs .x11).toNat + j - o := by rw [BitVec.toNat_sub]; omega
  have h14' : (r .x14 + 8#64).toNat = (r .x14).toNat + 8 := toNat_add_ofNat (by omega)
  have h5 : ∀ t, o ≤ t → t < 8 → extractByte (M.getMem (r .x2 + 8#64)) t =
      bat m ((r .x11 - r .x16).toNat + t) := by
    intro t ht1 ht2
    have := extractByte_loadVal (w := .b8) (M := M) (x := r .x2 + 8#64) (t := t) (by rw [hs8]; show _ % 8 = 0; omega)
      ht2
    rw [show Tactic.loadVal .b8 M (r .x2 + 8#64) = M.getMem (r .x2 + 8#64) from rfl] at this
    rw [this, hs8, hS t ht1 ht2, h6]
  rv_symT hp stop [90, 110] with [hx2]
  · have hc' := BitVec.le_def.1 hc
    rw [h14', h13] at hc'
    refine partial_ok hp F hk hsp (j := j) (o := o) (by regs_ok hR) hI ho1 ho8 ?_ ?_ ?_ (by omega) (by omega)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    any_goals (tnorm; assumption)
    any_goals (tnorm; omega)
    · intro t ht1 ht2; tnorm; rw [h5 t ht1 ht2, h6]
  · have hc' := BitVec.lt_def.1 hc
    rw [h14', h13] at hc'
    have s2 := (shamt h17 ho1 ho8).2
    refine loopB_ok hp F hk hsp ho1 ho8 N _ _ ⟨j, by regs_ok hR, hI, ?_, ?_, ?_, hN8, by omega, hjN, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    any_goals (tnorm; assumption)
    all_goals (tnorm; omega)

/-- `load_aligned_end_partial`'s word: the last four bytes, `c` bytes copied before them. -/
theorem endWord_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j o N c : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (ho1 : 0 < o) (ho8 : o < 8) (h14 : (r .x14).toNat = (regs .x10).toNat + j) (ha14 : (r .x14).toNat % 8 = 0)
    (h13 : (r .x13).toNat = (regs .x10).toNat + j + N) (hN8 : N % 8 = 0) (hN : 8 ≤ N) (hjN : j + N ≤ (regs .x12).toNat)
    (h11 : (r .x11).toNat = (regs .x11).toNat + j) (h16 : (r .x16).toNat = o) (h11o : ((regs .x11).toNat + j) % 8 = o)
    (h15 : (r .x15).toNat = N) (h12 : (r .x12).toNat % 8 = (regs .x12).toNat - (j + N))
    (h6 : (r .x6).toNat = top.toNat - 8 + o) (h17 : (r .x17).toNat = c)
    (hS : ∀ t, o ≤ t → t < o + c → bat M (top.toNat - 8 + t) = bat m ((regs .x11).toNat + j - o + t)) (hc4 : o + c + 4 = 8) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, r, M⟩ := by
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hroom := F.room
  have hal := F.al
  have hx2 := hR.2.1.1
  have hb4 : Width.b4.bytes = 4 := rfl
  have hdn : (regs .x10).toNat + (regs .x12).toNat < 2 ^ 64 := by have := env.heapEnd.isLt; omega
  have hA : (r .x11 + r .x17).toNat = (regs .x11).toNat + j + c := by rw [BitVec.toNat_add]; omega
  have hX : (r .x6 + r .x17).toNat = top.toNat - 8 + (o + c) := by rw [BitVec.toNat_add]; omega
  obtain ⟨hI', hS'⟩ := slot_copy_from (w := .b4) (lo := o) (i := o + c) (B := (regs .x11).toNat + j - o)
    (X := r .x6 + r .x17) (v := (UnOp.sext .b4).eval (Tactic.loadVal .b4 M (r .x11 + r .x17))) hI F.doff
    (by omega) hdn hroom (by omega) hS hX (by rw [hX, hb4]; omega) (by rw [hb4]; omega) (fun u hu => by
      have := extractByte_load (M := M) (x := r .x11 + r .x17) (u := u) true (by rw [hA, hb4]; omega) hu
      simp only [↓reduceIte] at this
      rw [this, hA]
      have := F.src (k := j + c + u) hI (by omega) (by omega)
      rw [← Nat.add_assoc, ← Nat.add_assoc] at this
      rw [this]; congr 1; omega)
  rv_symT hp stop [76] with [hx2]
  refine prev_ok hp F hk hsp (j := j) (o := o) (N := N) (by regs_ok hR) hI' ho1 ho8 ?_ ?_ ?_ hN8 hN hjN ?_ ?_ h11o
    ?_ ?_ ?_
  any_goals (tnorm; assumption)
  · intro t ht1 ht2; exact hS' t ht1 (by rw [hb4]; omega)

/-- `load_aligned_end_partial` at its word: `x5 = 8 - o`, its bits below 4 copied. -/
theorem endBit2_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j o N c : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (ho1 : 0 < o) (ho8 : o < 8) (h14 : (r .x14).toNat = (regs .x10).toNat + j) (ha14 : (r .x14).toNat % 8 = 0)
    (h13 : (r .x13).toNat = (regs .x10).toNat + j + N) (hN8 : N % 8 = 0) (hN : 8 ≤ N) (hjN : j + N ≤ (regs .x12).toNat)
    (h11 : (r .x11).toNat = (regs .x11).toNat + j) (h16 : (r .x16).toNat = o) (h11o : ((regs .x11).toNat + j) % 8 = o)
    (h15 : (r .x15).toNat = N) (h12 : (r .x12).toNat % 8 = (regs .x12).toNat - (j + N))
    (h6 : (r .x6).toNat = top.toNat - 8 + o) (h17 : (r .x17).toNat = c)
    (hS : ∀ t, o ≤ t → t < o + c → bat M (top.toNat - 8 + t) = bat m ((regs .x11).toNat + j - o + t)) (h5 : (r .x5).toNat = 8 - o) (hcv : c = (8 - o) % 4) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 64, ret, top⟩ :: rest, r, M⟩ := by
  have hx2 := hR.2.1.1
  rv_symT hp stop [68, 76] with [hx2]
  · have := (and4_zero _).1 hc
    refine prev_ok hp F hk hsp (j := j) (o := o) (N := N) (by regs_ok hR) hI ho1 ho8 ?_ ?_ ?_ hN8 hN hjN ?_ ?_ h11o
      ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · intro t ht1 ht2; exact hS t ht1 (by omega)
  · have : ¬ (r .x5).toNat % 8 < 4 := fun h => hc ((and4_zero _).2 h)
    refine endWord_ok hp F hk hsp (j := j) (o := o) (N := N) (c := c) (by regs_ok hR) hI ho1 ho8 ?_ ?_ ?_ hN8 hN hjN
      ?_ ?_ h11o ?_ ?_ ?_ ?_ hS (by omega)
    all_goals (tnorm; assumption)

/-- `load_aligned_end_partial`: the bytes of the first source doubleword from `o` on into the stack slot, a byte, a
    halfword and a word as the bits of `8 - o` say. -/
theorem endPartial_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j o N : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (ho1 : 0 < o) (ho8 : o < 8) (h14 : (r .x14).toNat = (regs .x10).toNat + j) (ha14 : (r .x14).toNat % 8 = 0)
    (h13 : (r .x13).toNat = (regs .x10).toNat + j + N) (hN8 : N % 8 = 0) (hN : 8 ≤ N) (hjN : j + N ≤ (regs .x12).toNat)
    (h11 : (r .x11).toNat = (regs .x11).toNat + j) (h16 : (r .x16).toNat = o) (h11o : ((regs .x11).toNat + j) % 8 = o)
    (h15 : (r .x15).toNat = N) (h12 : (r .x12).toNat % 8 = (regs .x12).toNat - (j + N)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 44, ret, top⟩ :: rest, r, M⟩ := by
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hroom := F.room
  have hal := F.al
  have hx2 := hR.2.1.1
  have hs8 := slot_addr hx2 (by omega)
  have hb1 : Width.b1.bytes = 1 := rfl
  have hb2 : Width.b2.bytes = 2 := rfl
  have hb8 : Width.b8.bytes = 8 := rfl
  have hdn : (regs .x10).toNat + (regs .x12).toNat < 2 ^ 64 := by have := env.heapEnd.isLt; omega
  have hX6 : r .x2 + 8#64 ||| r .x16 = BitVec.ofNat 64 (top.toNat - 8 + o) := by
    rw [or_eq_add (by rw [hs8]; omega) (by omega)]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hs8, BitVec.toNat_ofNat]; omega
  have h6 : (BitVec.ofNat 64 (top.toNat - 8 + o)).toNat = top.toNat - 8 + o := by
    rw [BitVec.toNat_ofNat]; omega
  have h5 : (8#64 - r .x16).toNat = 8 - o := by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hI1 := hI.slot (w := .b8) (x := r .x2 + 8#64) (v := 0#64) F.doff (by omega) hdn hroom (by omega)
    (by omega) (by omega) (by rw [hs8]; show _ % 8 = 0; omega)
  have src : ∀ M', Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M' j → ∀ u, u < 8 - o →
      bat M' ((regs .x11).toNat + j + u) = bat m ((regs .x11).toNat + j + u) := fun M' hI' u hu => by
    have := F.src (k := j + u) hI' (by omega) (by omega)
    rwa [← Nat.add_assoc] at this
  -- a byte at `o`, or a halfword at `o + c`
  have cpB := slot_copy_from (w := .b1) (lo := o) (i := o) (B := (regs .x11).toNat + j - o)
    (X := BitVec.ofNat 64 (top.toNat - 8 + o))
    (v := Tactic.loadVal .b1 (Tactic.storeMem .b8 M (r .x2 + 8#64) 0#64) (r .x11)) hI1 F.doff (by omega) hdn hroom
    (by omega) (fun t h1 h2 => absurd h2 (by omega)) h6 (by rw [hb1]; omega) (by rw [hb1]; omega) (fun u hu => by
      have := extractByte_load (M := Tactic.storeMem .b8 M (r .x2 + 8#64) 0#64) (x := r .x11) (u := u) false
        (by rw [hb1]; omega) hu
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [this, h11, src _ hI1 u (by omega)]; congr 1; omega)
  have cpH := fun (c : Nat) (X Y : Word) {M' : MachineState}
      (hI' : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M' j)
      (hS' : ∀ t, o ≤ t → t < o + c → bat M' (top.toNat - 8 + t) = bat m ((regs .x11).toNat + j - o + t))
      (hX : X.toNat = top.toNat - 8 + (o + c)) (hY : Y.toNat = (regs .x11).toNat + j + c)
      (hal : (o + c) % 2 = 0) (hc2 : o + c + 2 ≤ 8) =>
    slot_copy_from (w := .b2) (lo := o) (i := o + c) (B := (regs .x11).toNat + j - o) (X := X)
      (v := (UnOp.sext .b2).eval (Tactic.loadVal .b2 M' Y)) hI' F.doff (by omega) hdn hroom (by omega) hS' hX
      (by rw [hX, hb2]; omega) (by rw [hb2]; omega) (fun u hu => by
        have := extractByte_load (M := M') (x := Y) (u := u) true (by rw [hY, hb2]; omega) hu
        simp only [↓reduceIte] at this
        rw [this, hY, show (regs .x11).toNat + j + c + u = (regs .x11).toNat + j + (c + u) by omega,
          src _ hI' (c + u) (by rw [hb2] at hu; omega)]
        congr 1; omega)
  rv_symT hp stop [64, 68, 76] with [hx2]
  all_goals try rw [hX6]
  rv_closeT
  -- `8 - o` odd, no halfword: the byte
  · rw [and2_zero, h5] at hc
    have hc_1 : ¬ (8 - o) % 2 = 0 := fun h => hc_1 ((and1_zero _).2 (by rw [h5]; exact h))
    obtain ⟨hI2, hS2⟩ := cpB
    refine endBit2_ok hp F hk hsp (j := j) (o := o) (N := N) (c := 1) (by regs_ok hR) hI2 ho1 ho8 ?_ ?_ ?_ hN8 hN
      hjN ?_ ?_ h11o ?_ ?_ ?_ ?_ ?_ ?_ (by omega)
    any_goals (tnorm; assumption)
    intro t ht1 ht2; exact hS2 t ht1 (by rw [hb1]; omega)
  -- the halfword after the byte: its address and alignment
  · have hc_1 : ¬ (8 - o) % 2 = 0 := fun h => hc_1 ((and1_zero _).2 (by rw [h5]; exact h))
    rw [toNat_add_ofNat (by omega)]; omega
  · have hc : ¬ (8 - o) % 4 < 2 := fun h => hc ((and2_zero _).2 (by rw [h5]; exact h))
    have hc_1 : ¬ (8 - o) % 2 = 0 := fun h => hc_1 ((and1_zero _).2 (by rw [h5]; exact h))
    exact hW.stack (by rw [toNat_add_ofNat (by rw [h6]; omega), h6]; omega)
      (by rw [toNat_add_ofNat (by rw [h6]; omega), h6]; omega)
  · have hc_1 : ¬ (8 - o) % 2 = 0 := fun h => hc_1 ((and1_zero _).2 (by rw [h5]; exact h))
    rw [toNat_add_ofNat (by rw [h6]; omega), h6]; omega
  -- `8 - o` is 7: the byte, the halfword, the word
  · have hc_1 : ¬ (8 - o) % 2 = 0 := fun h => hc_1 ((and1_zero _).2 (by rw [h5]; exact h))
    have hc_2 : ¬ (8 - o) % 4 < 2 := fun h => hc_2 ((and2_zero _).2 (by rw [h5]; exact h))
    have hc : ¬ (8 - o) % 8 < 4 := fun h => hc ((and4_zero _).2 (by rw [h5]; exact h))
    obtain ⟨hI2, hS2⟩ := cpB
    obtain ⟨hI3, hS3⟩ := cpH 1 (BitVec.ofNat 64 (top.toNat - 8 + o) + 1#64) (r .x11 + 1#64) hI2 hS2
      (by rw [toNat_add_ofNat (by rw [h6]; omega), h6]; omega) (by rw [toNat_add_ofNat (by omega), h11])
      (by omega) (by omega)
    refine endWord_ok hp F hk hsp (j := j) (o := o) (N := N) (c := 3) (by regs_ok hR) hI3 ho1 ho8 ?_ ?_ ?_ hN8 hN
      hjN ?_ ?_ h11o ?_ ?_ ?_ ?_ ?_ (by omega)
    any_goals (tnorm; assumption)
    all_goals first | (intro t ht1 ht2; exact hS3 t ht1 (by rw [hb2]; omega)) | tlit
  -- `8 - o` is 3: the byte and the halfword
  · have hc_1 : ¬ (8 - o) % 2 = 0 := fun h => hc_1 ((and1_zero _).2 (by rw [h5]; exact h))
    have hc_2 : ¬ (8 - o) % 4 < 2 := fun h => hc_2 ((and2_zero _).2 (by rw [h5]; exact h))
    rw [and4_zero, h5] at hc
    obtain ⟨hI2, hS2⟩ := cpB
    obtain ⟨hI3, hS3⟩ := cpH 1 (BitVec.ofNat 64 (top.toNat - 8 + o) + 1#64) (r .x11 + 1#64) hI2 hS2
      (by rw [toNat_add_ofNat (by rw [h6]; omega), h6]; omega) (by rw [toNat_add_ofNat (by omega), h11])
      (by omega) (by omega)
    refine prev_ok hp F hk hsp (j := j) (o := o) (N := N) (by regs_ok hR) hI3 ho1 ho8 ?_ ?_ ?_ hN8 hN hjN ?_ ?_ h11o
      ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · intro t ht1 ht2; exact hS3 t ht1 (by rw [hb2]; omega)
  -- the halfword alone: its alignment and address
  · rw [and1_zero, h5] at hc_1
    omega
  · have hc : ¬ (8 - o) % 4 < 2 := fun h => hc ((and2_zero _).2 (by rw [h5]; exact h))
    exact hW.stack (by rw [h6]; omega) (by rw [h6]; omega)
  · rw [and1_zero, h5] at hc_1
    rw [h6]; omega
  -- `8 - o` is 6: the halfword and the word
  · rw [and1_zero, h5] at hc_1
    have hc_2 : ¬ (8 - o) % 4 < 2 := fun h => hc_2 ((and2_zero _).2 (by rw [h5]; exact h))
    have hc : ¬ (8 - o) % 8 < 4 := fun h => hc ((and4_zero _).2 (by rw [h5]; exact h))
    obtain ⟨hI3, hS3⟩ := cpH 0 (BitVec.ofNat 64 (top.toNat - 8 + o)) (r .x11) hI1
      (fun t h1 h2 => absurd h2 (by omega)) (by rw [h6, Nat.add_zero]) (by rw [h11, Nat.add_zero])
      (by omega) (by omega)
    refine endWord_ok hp F hk hsp (j := j) (o := o) (N := N) (c := 2) (by regs_ok hR) hI3 ho1 ho8 ?_ ?_ ?_ hN8 hN
      hjN ?_ ?_ h11o ?_ ?_ ?_ ?_ ?_ (by omega)
    any_goals (tnorm; assumption)
    intro t ht1 ht2; exact hS3 t ht1 (by rw [hb2]; omega)
  -- `8 - o` is 2: the halfword
  · rw [and1_zero, h5] at hc_1
    have hc_2 : ¬ (8 - o) % 4 < 2 := fun h => hc_2 ((and2_zero _).2 (by rw [h5]; exact h))
    rw [and4_zero, h5] at hc
    obtain ⟨hI3, hS3⟩ := cpH 0 (BitVec.ofNat 64 (top.toNat - 8 + o)) (r .x11) hI1
      (fun t h1 h2 => absurd h2 (by omega)) (by rw [h6, Nat.add_zero]) (by rw [h11, Nat.add_zero])
      (by omega) (by omega)
    refine prev_ok hp F hk hsp (j := j) (o := o) (N := N) (by regs_ok hR) hI3 ho1 ho8 ?_ ?_ ?_ hN8 hN hjN ?_ ?_ h11o
      ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · intro t ht1 ht2; exact hS3 t ht1 (by rw [hb2]; omega)
  -- `8 - o` is 4: the word alone
  · rw [and1_zero, h5] at hc_1
    rw [and2_zero, h5] at hc
    refine endBit2_ok hp F hk hsp (j := j) (o := o) (N := N) (c := 0) (by regs_ok hR) hI1 ho1 ho8 ?_ ?_ ?_ hN8 hN
      hjN ?_ ?_ h11o ?_ ?_ ?_ ?_ ?_ ?_ (by omega)
    any_goals (tnorm; assumption)
    all_goals first | (intro t ht1 ht2; omega) | tlit

/-- With the destination aligned after `j` bytes: the doublewords, by the source's alignment. -/
theorem words_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {j : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hI : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M j)
    (h13 : (r .x13).toNat = j) (h14 : (r .x14).toNat = (regs .x10).toNat + j) (ha14 : (r .x14).toNat % 8 = 0)
    (hj : j ≤ 7) (hn : 16 ≤ (regs .x12).toNat) (h11 : r .x11 = regs .x11) (h12 : r .x12 = regs .x12) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 32, ret, top⟩ :: rest, r, M⟩ := by
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hx2 := hR.2.1.1
  have hA : (r .x11 + r .x13).toNat = (regs .x11).toNat + j := by rw [BitVec.toNat_add, h11]; omega
  have hB : (r .x12 - r .x13).toNat = (regs .x12).toNat - j := by rw [BitVec.toNat_sub, h12]; omega
  have hN := toNat_and_not7 (r .x12 - r .x13)
  rw [hB] at hN
  have ho := Proof.Runtime.Alloc.and7 (r .x11 + r .x13)
  rw [hA] at ho
  have hE : (r .x14 + (r .x12 - r .x13 &&& 18446744073709551608#64)).toNat =
      (regs .x10).toNat + j + ((regs .x12).toNat - j - ((regs .x12).toNat - j) % 8) := by
    rw [BitVec.toNat_add, hN]; omega
  rv_symT hp stop [44, 166, 176] with [hx2]
  · have := BitVec.le_def.1 hc
    rw [hE, h14] at this
    omega
  · have hc' : ((regs .x11).toNat + j) % 8 = 0 := by rw [← ho, hc_1]; rfl
    refine loopC_ok hp F hk hsp ((regs .x12).toNat - j - ((regs .x12).toNat - j) % 8) _ _ ⟨j, by regs_ok hR, hI, ?_,
      ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, by omega⟩
    all_goals (tnorm; omega)
  · have hc' : ¬ ((regs .x11).toNat + j) % 8 = 0 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [ho, h]; rfl))
    refine endPartial_ok hp F hk hsp (j := j) (o := ((regs .x11).toNat + j) % 8)
      (N := (regs .x12).toNat - j - ((regs .x12).toNat - j) % 8) (by regs_ok hR) hI (by omega) (by omega) ?_ ?_ ?_
      (by omega) (by omega) (by omega) ?_ ?_ rfl ?_ ?_
    all_goals (tnorm; omega)

/-- The bytes up to the destination's first 8-byte boundary, `mis` of them, at the loop's head with `c` left. -/
def AInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (mis c : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  Regs ret top regs r ∧ Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m M (mis - c) ∧ (r .x15).toNat = c ∧
    0 < c ∧ c ≤ mis ∧ (r .x16).toNat = (regs .x10).toNat + (mis - c) ∧
    (r .x17).toNat = (regs .x11).toNat + (mis - c) ∧ (r .x13).toNat = mis ∧ (r .x14).toNat = (regs .x10).toNat + mis ∧
    (r .x14).toNat % 8 = 0 ∧ mis ≤ 7 ∧ 16 ≤ (regs .x12).toNat ∧ r .x11 = regs .x11 ∧ r .x12 = regs .x12

/-- The bytes up to the destination's first 8-byte boundary. -/
theorem loopA_ok (hp : p[i]? = some (tmpl L)) (F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) (mis : Nat) :
    ∀ c r M, AInv env ret top regs m mis c r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 20, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (AInv env ret top regs m mis)
    fun c r M ⟨hR, hI, h15, hc0, hcm, h16, h17, h13, h14, ha14, hm7, hn, h11, h12⟩ ih => ?_
  have hsw := inWindow_iff.1 F.swin
  have hdw := F.dwin
  unfold InWin at hdw
  have hW := F.win
  have hcode := hI.1.2.2
  have hx2 := hR.2.1.1
  have hv : extractByte ((M.getByte (r .x17)).zeroExtend 64) 0 =
      bat m ((regs .x11).toNat + (mis - c)) := by
    rw [extractByte_zext_getByte, h17]; exact F.src hI (by omega) (by omega)
  have hI' := hI.byte F.dwin (x := r .x16) h16 (by omega) hv
  have h15' := toNat_dec (a := r .x15) (by omega)
  rv_symT hp stop [32] with [hx2]
  · have : (r .x15 + 0xffffffffffffffff#64).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    refine ih (c - 1) _ _ (by omega) ⟨by regs_ok hR, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, hm7, hn, ?_, ?_⟩
    · have e : mis - c + 1 = mis - (c - 1) := by omega
      rw [e] at hI'; exact hI'
    · tnorm; omega
    · tnorm; rw [toNat_add_ofNat (by omega)]; omega
    · tnorm; rw [toNat_add_ofNat (by omega)]; omega
    · tnorm; exact h13
    · tnorm; exact h14
    · tnorm; exact ha14
    · tnorm; exact h11
    · tnorm; exact h12
  · have : (r .x15 + 0xffffffffffffffff#64).toNat = 0 := by rw [hc]; rfl
    refine words_ok hp F hk hsp (j := mis) (by regs_ok hR) ?_ ?_ ?_ ?_ hm7 hn ?_ ?_
    · have e : mis - c + 1 = mis := by omega
      rw [e] at hI'; exact hI'
    · tnorm; exact h13
    · tnorm; exact h14
    · tnorm; exact ha14
    · tnorm; exact h11
    · tnorm; exact h12

/-- **`memcpy` is total**, with its 16-byte frame: it returns `dst` with the bytes copied, from `CopyPreT false`. -/
theorem total (hp : p[i]? = some (tmpl L)) : MemcpySpecT env p i 16 := by
  intro Q ret top rest regs m hpre _ hk
  obtain ⟨⟨⟨hra, hsp⟩, hstk, hst, hnx, ⟨⟨hnw1, hnw2, hdisj⟩, hwin0⟩, hal⟩, hwin⟩ := hpre
  have hR0 : Regs ret top regs (updReg regs .x2 (regs .x2 + 0xfffffffffffffff0#64)) := by
    refine ⟨by simp [updReg_apply, hra], ?_, by simp [updReg_apply]⟩
    simp [AbiRegs, updReg_apply, hsp]
  have hI0 : Inv env top (regs .x10) (regs .x11) (regs .x12).toNat m m 0 := Inv.start hst hnx
  have h16 : (16#64 : Word).toNat = 16 := rfl
  by_cases hn0 : (regs .x12).toNat = 0
  · have hz : regs .x10 + regs .x12 = regs .x10 := by
      rw [show regs .x12 = 0#64 from BitVec.eq_of_toNat_eq hn0, BitVec.add_zero]
    rv_symT hp stop [20, 32, 184, 196]
    · exact absurd hc (by rw [hz]; exact BitVec.lt_irrefl _)
    · refine ret_ok hp hk hsp (by regs_ok hR0) ?_
      rw [hn0]; exact Inv.start hst hnx
    · exact absurd (BitVec.le_def.1 hc_1) (by rw [hn0]; decide)
    · exact absurd (BitVec.le_def.1 hc_1) (by rw [hn0]; decide)
  · obtain ⟨hdw, hdoff, hsw, hsoff⟩ := hwin0.resolve_left hn0
    unfold NoWrap at hnw1 hnw2
    have F : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m := by
      refine ⟨hwin, by omega, hal, hdw, hsp ▸ hdoff, hsw, hsp ▸ hsoff, fun k hk k' hk' he => ?_⟩
      refine hdisj rfl (BitVec.ofNat 64 ((regs .x10).toNat + k)) ?_ ?_ <;> unfold InRange <;>
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] <;> omega
    have hmis := toNat_neg_and7 (regs .x10)
    have hE : (regs .x10 + (0#64 - regs .x10 &&& 7#64)).toNat =
        (regs .x10).toNat + (8 - (regs .x10).toNat % 8) % 8 := by
      have := hwin.heapEnd_le
      rw [BitVec.toNat_add, hmis]; omega
    have hN : (regs .x10 + regs .x12).toNat = (regs .x10).toNat + (regs .x12).toNat := by
      rw [BitVec.toNat_add]; omega
    rv_symT hp stop [20, 32, 184, 196]
    · refine loopD_ok hp F hk hsp (regs .x12).toNat _ _ ⟨by regs_ok hR0, ?_, ?_, ?_, ?_, by omega, by omega⟩
      · simpa only [Nat.sub_self] using hI0
      all_goals tomega
    · have := BitVec.le_def.1 hc
      rw [hN] at this
      omega
    · have := BitVec.le_def.1 hc
      rw [hE] at this
      have h16' := BitVec.le_def.1 hc_1
      refine words_ok hp F hk hsp (j := 0) (by regs_ok hR0) hI0 ?_ ?_ ?_ (by omega) (by rw [h16] at h16'; exact h16')
        ?_ ?_
      all_goals tnorm
      · omega
      · omega
      · omega
    · have := BitVec.lt_def.1 hc
      rw [hE] at this
      have h16' := BitVec.le_def.1 hc_1
      refine loopA_ok hp F hk hsp ((8 - (regs .x10).toNat % 8) % 8) _ _ _ ⟨by regs_ok hR0, ?_, ?_, by omega, le_rfl,
        ?_, ?_, ?_, ?_, ?_, by omega, by rw [h16] at h16'; exact h16', ?_, ?_⟩
      · simpa only [Nat.sub_self] using hI0
      all_goals tnorm
      all_goals omega

end Rv64mc.Proof.Runtime.MemcpyT

/-- info: 'Rv64mc.Proof.Runtime.MemcpyT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.MemcpyT.total
