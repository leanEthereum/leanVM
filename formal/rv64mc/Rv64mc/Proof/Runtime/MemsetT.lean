/-
  Rv64mc.Proof.Runtime.MemsetT

  `compiler_builtins`' `memset(dst, c, n)` is total, and the C wrapper `memset` with it: from any
  destination whose bytes lie in a window apart from the static data and `NEXT` (`MemsetPreT`),
  it returns `dst`, having written only the doublewords that hold `[dst, dst + n)` (`CopyOut`, as
  `MemsetSpec` has it), with every store in a window and over no code. Its three loops (the bytes
  up to an 8-byte boundary, the doublewords, the bytes after them) are each `Total.loop` with the
  count left as the measure. It does not state which bytes it writes: that is `MemsetSpec`'s
  `SetPost`, a partial contract not yet proved (`notes/status.md`).

  ## Main definitions

  * `InWin`, `MemsetPreT`, `MemsetSafeT`

  ## Main results

  * `total`
  * `tail_total`, `memset_total`: a tail call, the C wrapper
-/

import Rv64mc.Proof.Runtime.MemWrappers
import Rv64mc.Proof.Runtime.Alloc
import Rv64mc.Gen.Tmpl.CompilerBuiltins.Mem.Memset
import Rv64mc.Core.ReprBytes
import Rv64mc.Tactic.TStep
import Rv64mc.Tactic.Heap

namespace Rv64mc.Proof.Runtime.MemsetT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime
open Rv64mc.Gen.CompilerBuiltins.Mem.Memset (Link tmpl)

variable {env : Env}

/-- The bytes `[a, a + n)` lie in the input and heap window up to the heap's end, or in the stack window from the
    stack's limit. -/
def InWin (env : Env) (a : Word) (n : Nat) : Prop :=
  (0x10000000 ≤ a.toNat ∧ a.toNat + n ≤ env.heapEnd.toNat) ∨
    (env.stackLimit.toNat ≤ a.toNat ∧ a.toNat + n ≤ 0xc0000000)

/-- `memset`'s total precondition: `SetPre`, and the `n` bytes from `dst` in a window, apart from the static data
    and `NEXT` (`InWin`), unless there are none. -/
def MemsetPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SetPre regs m ∧ ((regs .x12).toNat = 0 ∨ InWin env (regs .x10) (regs .x12).toNat)

/-- `memset`'s total postcondition: it returns `dst`. -/
def MemsetPostT (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = regs .x10

/-- **The total contract of `memset`**: it returns `dst`, writing at most the doublewords of `[dst, dst + n)`. It
    does not say what it writes there. -/
def MemsetSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (MemsetPreT env) MemsetPostT CopyOut

/-! ## Stores into the destination -/

theorem InWin.sub {a x : Word} {n w : Nat} (h : InWin env a n) (hlo : a.toNat ≤ x.toNat)
    (hhi : x.toNat + w ≤ a.toNat + n) : InWin env x w := by
  unfold InWin at h ⊢
  omega

theorem InWin.inWindow {a : Word} {n : Nat} {top : Word} {m : MachineState} (h : InWin env a n)
    (hw : Windows env top m) : inWindow a n = true := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hw.heapObj h1 h2
  · exact hw.stackObj h1 h2

/-- A doubleword at most 7 bytes below `[a, a + n)` or in it is neither static data nor `NEXT`. -/
theorem InWin.apart {a b : Word} {n : Nat} (h : InWin env a n) (hb1 : a.toNat ≤ b.toNat + 7)
    (hb2 : b.toNat < a.toNat + n) :
    (b.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ b.toNat) ∧ b ≠ env.nextAddr := by
  have hl := env.layout
  unfold InWin at h
  refine ⟨by omega, fun he => ?_⟩
  rw [he] at hb1 hb2
  omega

/-- What `memset` keeps as it runs, with destination `[dst, dst + n)`: its frame, the static data, the code. -/
def Kept (env : Env) (top dst : Word) (n : Nat) (m m' : MachineState) : Prop :=
  env.Frame top (DwordsOf dst n) m m' ∧ env.Static m' ∧ m'.code = m.code

theorem Kept.setByte {top dst x : Word} {n : Nat} {m m' : MachineState} (h : Kept env top dst n m m')
    (hw : InWin env dst n) (hx1 : dst.toNat ≤ x.toNat) (hx2 : x.toNat < dst.toNat + n) (c : BitVec 8) :
    Kept env top dst n m (m'.setByte x c) := by
  have ha := toNat_alignToDword x
  have ⟨hs, hn⟩ := hw.apart (b := alignToDword x) (by omega) (by omega)
  refine ⟨frame_byte_out h.1 ?_ hn, static_byte h.2.1 hs, h.2.2⟩
  unfold DwordsOf InRange
  rw [ha, toNat_alignToDword]
  omega

theorem Kept.setMem {top dst x : Word} {n : Nat} {m m' : MachineState} (h : Kept env top dst n m m')
    (hw : InWin env dst n) (hal : x.toNat % 8 = 0) (hx1 : dst.toNat ≤ x.toNat) (hx2 : x.toNat + 8 ≤ dst.toNat + n)
    (v : Word) : Kept env top dst n m (m'.setMem x v) := by
  have ⟨hs, hn⟩ := hw.apart (b := x) (by omega) (by omega)
  refine ⟨Tactic.frame_out h.1 ?_ hn, Tactic.static_store h.2.1 hs, h.2.2⟩
  unfold DwordsOf InRange
  rw [toNat_alignToDword]
  omega

/-- The windows hold of the memory as `memset` runs. -/
theorem Kept.windows {top dst : Word} {n : Nat} {m m' : MachineState} (h : Kept env top dst n m m')
    (hw : Windows env top m) : Windows env top m' :=
  hw.after h.2.2 h.1.1

/-! ## The function -/

/-- What `memset` keeps as it runs, entered with `ret`, `top`, `regs` and `m`: the return address, the calling
    convention's registers, `dst` and `c`, and the memory `Kept`. -/
def Base (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (r : Reg → Word) (m' : MachineState) :
    Prop :=
  r .x1 = ret ∧ AbiRegs top regs r ∧ r .x10 = regs .x10 ∧ r .x11 = regs .x11 ∧
    Kept env top (regs .x10) (regs .x12).toNat m m'

theorem Base.upd {ret top : Word} {regs r : Reg → Word} {m m' : MachineState} (h : Base env ret top regs m r m')
    {d : Reg} (hd : d ∈ [.x12, .x13, .x14, .x15, .x16]) (v : Word) : Base env ret top regs m (updReg r d v) m' := by
  obtain ⟨h1, ha, h10, h11, hk⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  refine ⟨?_, (AbiRegs.updReg_iff (by rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide)).2 ha, ?_, ?_, hk⟩ <;>
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> simpa [updReg_apply]

theorem Base.of_agree {ret top : Word} {regs r r' : Reg → Word} {m m' : MachineState}
    (h : Base env ret top regs m r m') (hr : ∀ x, x ≠ .x12 → x ≠ .x13 → x ≠ .x14 → x ≠ .x15 → x ≠ .x16 → r' x = r x) :
    Base env ret top regs m r' m' := by
  obtain ⟨h1, ha, h10, h11, hk⟩ := h
  have e : ∀ x, x ∉ [Reg.x12, .x13, .x14, .x15, .x16] → r' x = r x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    exact hr x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2
  unfold AbiRegs at ha
  unfold Base AbiRegs
  rw [e .x1 (by decide), e .x2 (by decide), e .x8 (by decide), e .x9 (by decide), e .x10 (by decide),
    e .x11 (by decide), e .x18 (by decide), e .x19 (by decide), e .x20 (by decide), e .x21 (by decide),
    e .x22 (by decide), e .x23 (by decide), e .x24 (by decide), e .x25 (by decide), e .x26 (by decide),
    e .x27 (by decide)]
  exact ⟨h1, ha, h10, h11, hk⟩

theorem Base.mem {ret top : Word} {regs r : Reg → Word} {m m' m'' : MachineState} (h : Base env ret top regs m r m')
    (hk : Kept env top (regs .x10) (regs .x12).toNat m m'') : Base env ret top regs m r m'' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hk⟩

theorem toNat_add_one {x : Word} (h : x.toNat + 1 < 2 ^ 64) : (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem toNat_sub_one {x : Word} (h : 0 < x.toNat) : (x + 18446744073709551615#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The loop over the bytes after the doublewords, at its head: `x13` the next byte, `k` left in `x12`. -/
def TailInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (r : Reg → Word)
    (m' : MachineState) : Prop :=
  Base env ret top regs m r m' ∧ (r .x12).toNat = k ∧ 0 < k ∧ (regs .x10).toNat ≤ (r .x13).toNat ∧
    (r .x13).toNat + k = (regs .x10).toNat + (regs .x12).toNat

/-- The loop over the doublewords, at its head: `x14` the next, 8-byte aligned, `k` bytes below their end `x13`,
    with `x12 % 8` bytes after it. -/
def DwInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (r : Reg → Word)
    (m' : MachineState) : Prop :=
  Base env ret top regs m r m' ∧ (r .x14).toNat % 8 = 0 ∧ (regs .x10).toNat ≤ (r .x14).toNat ∧
    (r .x14).toNat + k = (r .x13).toNat ∧ 0 < k ∧ k % 8 = 0 ∧
    (r .x13).toNat + (r .x12).toNat % 8 = (regs .x10).toNat + (regs .x12).toNat

/-- The loop over the bytes before the first doubleword boundary, at its head: `x16` the next, `k` left in `x15`,
    up to `x14 = dst + x13`, the boundary; `x12` still `n`, at least 16. -/
def HeadInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (r : Reg → Word)
    (m' : MachineState) : Prop :=
  Base env ret top regs m r m' ∧ (r .x15).toNat = k ∧ 0 < k ∧ (regs .x10).toNat ≤ (r .x16).toNat ∧
    (r .x16).toNat + k = (r .x14).toNat ∧ (r .x14).toNat = (regs .x10).toNat + (r .x13).toNat ∧
    (r .x14).toNat % 8 = 0 ∧ (r .x13).toNat ≤ 7 ∧ (r .x12).toNat = (regs .x12).toNat ∧ 16 ≤ (regs .x12).toNat

theorem toNat_and_not7 (y : Word) : (y &&& 18446744073709551608#64).toNat = y.toNat - y.toNat % 8 := by
  rw [show (18446744073709551608#64 : Word) = ~~~7#64 by decide]
  exact toNat_alignToDword y

theorem toNat_neg_and7 (x : Word) : (0#64 - x &&& 7#64).toNat = (8 - x.toNat % 8) % 8 := by
  rw [Proof.Runtime.Alloc.and7, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.add_zero]
  omega

/-- A register file written only at `x12` to `x16` agrees with its start elsewhere. -/
local macro "agree" : tactic => `(tactic| (intro x h12 h13 h14 h15 h16) <;>
  simp only [Lprog.updReg_apply, h12, h13, h14, h15, h16, ↓reduceIte])

/-- **`memset` is total.** -/
theorem total (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) :
    MemsetSafeT env p i 0 := by
  intro Q ret top rest regs m hpre _ hk
  have ⟨⟨⟨hra, hsp⟩, hstk, hst, hnx, ⟨hnw, hwin0⟩, hal⟩, hwin⟩ := hpre
  -- the return
  have hRet : ∀ r m', Base env ret top regs m r m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 75, ret, top⟩ :: rest, r, m'⟩ := by
    intro r m' ⟨h1, ha, h10, _, hk'⟩
    refine TotalRv.ret hp rfl h1 ha.1 ?_
    exact hk _ _ ⟨⟨ha, hk'.1, hk'.2.1, h10⟩, hk'.2.2⟩
  -- the bytes after the doublewords: `x13` the next, `x12 = k` left
  have hTail : ∀ k r m', TailInv env ret top regs m k r m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, r, m'⟩ := by
    refine Total.loop (I := rvIsa) (TailInv env ret top regs m) fun k r m' ⟨hb, hk12, hk0, hlo, hend⟩ ih => ?_
    have hw : InWin env (regs .x10) (regs .x12).toNat := hwin0.resolve_left (by omega)
    have hw1 := (hw.sub (x := r .x13) (w := 1) hlo (by omega)).inWindow hwin
    tsteps hp
    refine TotalRv.sb hp rfl (by tnorm; exact hw1)
      (by tnorm; exact (hb.2.2.2.2.windows hwin).noCodeAt hw1 (by decide)) ?_
    tnorm
    tsteps hp
    have hb' := ((hb.upd (d := .x12) (by decide) (r .x12 + 18446744073709551615#64)).upd (d := .x13) (by decide)
      (r .x13 + 1#64)).mem
      (hb.2.2.2.2.setByte hw hlo (by omega) ((r .x11).truncate 8))
    tcond hp as hc
    · have h1 := toNat_sub_one (x := r .x12) (by omega)
      have hx := toNat_add_one (x := r .x13) (by unfold InWin at hw; omega)
      refine ih (k - 1) _ _ (by omega) ⟨hb', ?_, ?_, ?_, ?_⟩ <;>
        tomega
    · tstep hp
      exact hRet _ _ hb'
  -- after the doublewords: `x13` their end, `x12 % 8` bytes after it
  have hSec3 : ∀ r m', Base env ret top regs m r m' → (regs .x10).toNat ≤ (r .x13).toNat →
      (r .x13).toNat + (r .x12).toNat % 8 = (regs .x10).toNat + (regs .x12).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 52, ret, top⟩ :: rest, r, m'⟩ := by
    intro r m' hb hlo hend
    have h7 := Proof.Runtime.Alloc.and7 (r .x12)
    have hx : (r .x13 + (r .x12 &&& 7#64)).toNat = (r .x13).toNat + (r .x12).toNat % 8 := by
      rw [BitVec.toNat_add, h7]
      unfold SetPre NoWrap at hnw
      omega
    have hb' := (hb.upd (d := .x12) (by decide) (r .x12 &&& 7#64)).upd (d := .x14) (by decide)
      (r .x13 + (r .x12 &&& 7#64))
    tsteps hp
    tcond hp as hc
    · exact hTail ((r .x12).toNat % 8) _ _ ⟨hb', by tnorm; exact h7, by omega,
        by tnorm; exact hlo,
        by tomega⟩
    · tsteps hp
      exact hRet _ _ hb'
  -- the doublewords
  have hDw : ∀ k r m', DwInv env ret top regs m k r m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 46, ret, top⟩ :: rest, r, m'⟩ := by
    refine Total.loop (I := rvIsa) (DwInv env ret top regs m)
      fun k r m' ⟨hb, hal8, hlo, hend, hk0, hk8, hend3⟩ ih => ?_
    have hw : InWin env (regs .x10) (regs .x12).toNat := hwin0.resolve_left (by omega)
    have hw8 := (hw.sub (x := r .x14) (w := 8) hlo (by omega)).inWindow hwin
    have hx : (r .x14 + 8#64).toNat = (r .x14).toNat + 8 := by
      rw [BitVec.toNat_add]
      unfold InWin at hw
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    have hb' := (hb.upd (d := .x14) (by decide) (r .x14 + 8#64)).mem
      (hb.2.2.2.2.setMem (v := r .x15) hw hal8 hlo (by omega))
    tsteps hp
    refine TotalRv.sd8 hp rfl (by tnorm; exact hw8) (by tnorm; exact hal8)
      (by tnorm; exact (hb.2.2.2.2.windows hwin).noCodeAt hw8 (by decide)) ?_
    tnorm
    tsteps hp
    tcond hp as hc
    · refine ih (k - 8) _ _ (by omega) ⟨hb', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        tomega
    · exact hSec3 _ _ hb' (by tomega)
        (by tomega)
  -- from the first doubleword boundary `x14 = dst + x13`
  have hSec2 : ∀ r m', Base env ret top regs m r m' → (r .x14).toNat % 8 = 0 →
      (r .x14).toNat = (regs .x10).toNat + (r .x13).toNat → (r .x13).toNat ≤ 7 →
      (r .x12).toNat = (regs .x12).toNat → 16 ≤ (regs .x12).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 24, ret, top⟩ :: rest, r, m'⟩ := by
    intro r m' hb hal8 h14 h13 h12 h16
    have hs : (r .x12 - r .x13).toNat = (regs .x12).toNat - (r .x13).toNat := by
      rw [BitVec.toNat_sub]
      omega
    have ha := toNat_and_not7 (r .x12 - r .x13)
    have he : (r .x14 + (r .x12 - r .x13 &&& 18446744073709551608#64)).toNat =
        (r .x14).toNat + ((regs .x12).toNat - (r .x13).toNat - ((regs .x12).toNat - (r .x13).toNat) % 8) := by
      rw [BitVec.toNat_add, ha, hs]
      unfold SetPre NoWrap at hnw
      omega
    tsteps hp
    tcond hp as hc
    · exact hSec3 _ _ (Base.of_agree hb fun x h12 h13 h14 h15 h16 => by simp [updReg_apply, h12, h13])
        (by tomega)
        (by tomega)
    · iterate 14 tstep hp
      refine hDw ((regs .x12).toNat - (r .x13).toNat - ((regs .x12).toNat - (r .x13).toNat) % 8) _ _
        ⟨Base.of_agree hb fun x h12 h13 h14 h15 h16 => by simp [updReg_apply, h12, h13, h15, h16], ?_, ?_, ?_, ?_, ?_,
          ?_⟩ <;> tomega
  -- the bytes before the first doubleword boundary
  have hHead : ∀ k r m', HeadInv env ret top regs m k r m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 16, ret, top⟩ :: rest, r, m'⟩ := by
    refine Total.loop (I := rvIsa) (HeadInv env ret top regs m)
      fun k r m' ⟨hb, hk15, hk0, hlo, hend, h14, hal8, h13, h12, h16⟩ ih => ?_
    have hw : InWin env (regs .x10) (regs .x12).toNat := hwin0.resolve_left (by omega)
    have hw1 := (hw.sub (x := r .x16) (w := 1) hlo (by omega)).inWindow hwin
    have h1 := toNat_sub_one (x := r .x15) (by omega)
    have hx := toNat_add_one (x := r .x16) (by unfold InWin at hw; omega)
    have hb' := ((hb.upd (d := .x15) (by decide) (r .x15 + 18446744073709551615#64)).upd (d := .x16) (by decide)
      (r .x16 + 1#64)).mem (hb.2.2.2.2.setByte hw hlo (by omega) ((r .x11).truncate 8))
    tsteps hp
    refine TotalRv.sb hp rfl (by tnorm; exact hw1)
      (by tnorm; exact (hb.2.2.2.2.windows hwin).noCodeAt hw1 (by decide)) ?_
    tnorm
    tsteps hp
    tcond hp as hc
    · refine ih (k - 1) _ _ (by omega) ⟨hb', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tomega
    · exact hSec2 _ _ hb' (by tomega) (by tomega) (by tomega) (by tomega) h16
  -- the entry
  have hb0 : Base env ret top regs m regs m := ⟨hra, AbiRegs.refl hsp, rfl, rfl, Env.Frame.refl hnx, hst, rfl⟩
  have hn := hnw
  unfold SetPre NoWrap at hn
  have h16 : (16#64 : Word).toNat = 16 := rfl
  tsteps hp
  tcond hp as hc
  -- fewer than 16 bytes: one byte at a time
  · have hx : (regs .x10 + regs .x12).toNat = (regs .x10).toNat + (regs .x12).toNat := by
      rw [BitVec.toNat_add]
      omega
    tsteps hp
    tcond hp as hc'
    · tsteps hp
      exact hRet _ _ (Base.of_agree hb0 (by agree))
    · exact hTail (regs .x12).toNat _ _ ⟨Base.of_agree hb0 (by agree), by tnorm, by omega, by tomega,
        by tomega⟩
  -- at least 16: the bytes to a doubleword boundary, the doublewords, the bytes after them
  · have h13 := toNat_neg_and7 (regs .x10)
    have hx : (regs .x10 + (0#64 - regs .x10 &&& 7#64)).toNat =
        (regs .x10).toNat + (8 - (regs .x10).toNat % 8) % 8 := by
      rw [BitVec.toNat_add, h13]
      omega
    tsteps hp
    tcond hp as hc'
    · exact hSec2 _ _ (Base.of_agree hb0 (by agree)) (by tomega) (by tomega) (by tomega)
        (by tnorm) (by omega)
    · iterate 4 tstep hp
      exact hHead ((8 - (regs .x10).toNat % 8) % 8) _ _ ⟨Base.of_agree hb0 (by agree), by tomega, by omega,
        by tomega, by tomega, by tomega, by tomega, by tomega, by tnorm, by omega⟩

/-! ## The C wrapper -/

/-- **A tail call has its callee's total contract**, for a contract that does not read `t1`, which the call
    writes: the total counterpart of `tail_ok`. -/
theorem tail_total {p : Lprog (Op Reg) Reg} {i need : Nat} {fd : Lfundef (Op Reg) Reg}
    (hp : p[i]? = some fd) {s : Site} {c : Callee} (hb : fd.body = tailBody s c) (hc : c.WF p) (hs : s.WF c)
    {Pre : (Reg → Word) → MachineState → Prop}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    {Out : (Reg → Word) → MachineState → Word → Prop} (h : HoldsT env p c.idx need Pre Post Out)
    (hpre : ∀ regs m, Pre regs m → Pre (updReg regs .x6 s.hi) m)
    (hpost : ∀ regs m r' m', Post (updReg regs .x6 s.hi) m r' m' → Post regs m r' m')
    (hout : ∀ regs m a, Out (updReg regs .x6 s.hi) m a → Out regs m a) : HoldsT env p i need Pre Post Out := by
  intro Q ret top rest regs m ⟨⟨⟨hra, hsp⟩, hstk, hst, hnx, hP, hal⟩, hwin⟩ _ hk
  obtain ⟨name, addr, depth, body⟩ := fd
  simp only at hb
  subst hb
  tsteps hp
  refine Total.tail_contract hp rfl h.contract (callee_site hc hs (by tnorm)) (by tnorm; exact hsp)
    (WinOk.of_ne hp rfl nofun) ⟨⟨⟨by tnorm; exact hra, by tnorm; exact hsp⟩, hstk, hst, hnx, hpre _ _ hP, hal⟩, hwin⟩
    (fun _ _ _ _ h => h.elim) fun r' m' ⟨⟨hr, hf, hs', hq⟩, hcode⟩ => hk _ _ ⟨⟨?_, ⟨hf.1, hf.2.1, ?_⟩, hs',
      hpost _ _ _ _ hq⟩, hcode⟩
  · simpa [AbiRegs, updReg_apply] using hr
  · intro a ha
    refine hf.2.2 a fun hw => ha ?_
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr (hout _ _ _ hw)))

/-- **The C wrapper `memset` is total**, from `compiler_builtins`' `memset`. -/
theorem memset_total {p : Lprog (Op Reg) Reg} {i need : Nat} (L : Rv64mc.Gen.Memset.Link)
    (hp : p[i]? = some (Rv64mc.Gen.Memset.tmpl L)) (hL : L.WF p) (h : MemsetSafeT env p L.memset.idx need) :
    MemsetSafeT env p i need :=
  tail_total hp rfl hL.memset hL.s0 h (fun _ _ h => by simpa [MemsetPreT, SetPre, updReg_apply] using h)
    (fun _ _ _ _ h => by simpa [MemsetPostT, updReg_apply] using h)
    (fun _ _ _ h => by simpa [CopyOut, updReg_apply] using h)

end Rv64mc.Proof.Runtime.MemsetT

/-- info: 'Rv64mc.Proof.Runtime.MemsetT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.MemsetT.total

/-- info: 'Rv64mc.Proof.Runtime.MemsetT.memset_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.MemsetT.memset_total
