/-
  Rv64mc.Proof.Runtime.MemsetBytesT

  `compiler_builtins`' `memset(dst, c, n)` is total with the bytes it writes, and the C wrapper `memset` with it:
  from `MemsetPreT`, it returns `dst` with `[dst, dst + n)` holding `c`'s low byte and every other byte kept
  (`MemsetSpec`'s `SetPost`), writing at most the doublewords of `[dst, dst + n)`. The proof is `MemsetT.total`'s,
  each loop's invariant extended by `Fill`: the bytes from `dst` up to the loop's cursor hold `c`, and the bytes
  outside `[dst, dst + n)` are the entry's; the doubleword loop's also says its stored doubleword is `c`'s byte
  eight times (`splat`). `MemsetSpecT.safe` gives `MemsetT`'s `MemsetSafeT` back.

  ## Main definitions

  * `Fill`, `splat`, `MemsetSpecT`

  ## Main results

  * `total`, `memset_total`: `compiler_builtins`' `memset`, the C wrapper
  * `MemsetSpecT.safe`: the bytes dropped, `MemsetSafeT`
-/

import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Proof.Runtime.CopyT

namespace Rv64mc.Proof.Runtime.MemsetBytesT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin MemsetPreT MemsetSafeT Kept Base TailInv DwInv HeadInv)
open Rv64mc.Proof.Runtime.CopyT (bat getByte_setMem' byteOffset_ofNat)
open Rv64mc.Gen.CompilerBuiltins.Mem.Memset (Link tmpl)

variable {env : Env}

/-- **The total contract of `memset` with its bytes**: `MemsetSafeT`'s, with `SetPost` for its postcondition. -/
def MemsetSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (MemsetPreT env) SetPost CopyOut

/-- The bytes dropped: `MemsetSafeT`. -/
theorem MemsetSpecT.safe {p : Lprog (Op Reg) Reg} {i need : Nat} (h : MemsetSpecT env p i need) :
    MemsetSafeT env p i need :=
  Isa.TContract.mono h (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ _ _ ⟨⟨ha, hf, hs, hp⟩, hc⟩ => ⟨⟨ha, hf, hs, hp.1⟩, hc⟩) fun _ _ _ _ _ _ _ hs => hs

/-! ## Bytes written -/

/-- A byte store as bytes. -/
theorem bat_setByte {M : MachineState} {x : Word} {c : BitVec 8} {b : Nat} (hb : b < 2 ^ 64) :
    bat (M.setByte x c) b = if b = x.toNat then c else bat M b := by
  split
  · subst_vars; simp [bat, getByte_setByte_eq]
  · exact getByte_setByte_ne fun h => ‹¬_› (by rw [← h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb])

/-- An aligned doubleword store as bytes. -/
theorem bat_setMem {M : MachineState} {x v : Word} {b : Nat} (hx : x.toNat % 8 = 0) (hb : b < 2 ^ 64) :
    bat (M.setMem x v) b = if x.toNat ≤ b ∧ b < x.toNat + 8 then extractByte v (b - x.toNat) else bat M b := by
  have hxl := x.isLt
  unfold bat
  rw [getByte_setMem', byteOffset_ofNat hb]
  by_cases hA : b / 8 = x.toNat / 8
  · have : alignToDword (BitVec.ofNat 64 b) = x := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_alignToDword, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]; omega
    rw [ite_eq_left this, ite_eq_left (by omega), show b - x.toNat = b % 8 by omega]
  · have hne : alignToDword (BitVec.ofNat 64 b) ≠ x := fun h => hA (by
      have := congrArg BitVec.toNat h
      rw [toNat_alignToDword, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
      omega)
    rw [ite_eq_right hne, ite_eq_right (by omega)]

/-- The doubleword the code stores: `c`'s low byte in each of its eight bytes. -/
def splat (c : Word) : Word :=
  let v0 := c &&& 0xff#64
  let v1 := v0 <<< (8#64).toNat ||| v0
  let v2 := v1 <<< (16#64).toNat ||| v1
  v2 <<< (32#64).toNat ||| v2

theorem extractByte_splat (c : Word) {k : Nat} (hk : k < 8) : extractByte (splat c) k = c.truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, splat]
  interval_cases k <;> interval_cases i <;> simp

/-- The bytes `[d, cur)` hold `c`, and every byte outside `[d, d + n)` is `m`'s. -/
def Fill (m m' : MachineState) (d n : Nat) (c : BitVec 8) (cur : Nat) : Prop :=
  (∀ b, d ≤ b → b < cur → bat m' b = c) ∧ ∀ b, b < 2 ^ 64 → (b < d ∨ d + n ≤ b) → bat m' b = bat m b

theorem Fill.refl {m : MachineState} {d n : Nat} {c : BitVec 8} : Fill m m d n c d :=
  ⟨fun _ h1 h2 => absurd h2 (by omega), fun _ _ _ => rfl⟩

/-- A byte store of `c` at the cursor moves it by one. -/
theorem Fill.byte {m m' : MachineState} {d n cur : Nat} {c : BitVec 8} (h : Fill m m' d n c cur) {x : Word}
    (hx : x.toNat = cur) (hd : d ≤ cur) (hc : cur < d + n) (hn : d + n < 2 ^ 64) {v : BitVec 8} (hv : v = c) :
    Fill m (m'.setByte x v) d n c (cur + 1) := by
  refine ⟨fun b h1 h2 => ?_, fun b hb h1 => ?_⟩
  · rw [bat_setByte (by omega)]
    split
    · exact hv
    · exact h.1 b h1 (by omega)
  · rw [bat_setByte hb, ite_eq_right (by omega)]
    exact h.2 b hb h1

/-- An aligned doubleword store of `c` eight times at the cursor moves it by eight. -/
theorem Fill.dword {m m' : MachineState} {d n cur : Nat} {c : BitVec 8} (h : Fill m m' d n c cur) {x v : Word}
    (hx : x.toNat = cur) (hal : cur % 8 = 0) (hd : d ≤ cur) (hc : cur + 8 ≤ d + n) (hn : d + n < 2 ^ 64)
    (hv : ∀ k, k < 8 → extractByte v k = c) : Fill m (m'.setMem x v) d n c (cur + 8) := by
  refine ⟨fun b h1 h2 => ?_, fun b hb h1 => ?_⟩
  · rw [bat_setMem (by omega) (by omega)]
    split
    · exact hv _ (by omega)
    · exact h.1 b h1 (by omega)
  · rw [bat_setMem (by omega) hb, ite_eq_right (by omega)]
    exact h.2 b hb h1

/-- `Fill` up to the end is `SetPost`'s bytes. -/
theorem Fill.setPost {m m' : MachineState} {dst : Word} {n : Nat} {c : BitVec 8}
    (h : Fill m m' dst.toNat n c (dst.toNat + n)) (hn : dst.toNat + n < 2 ^ 64) :
    (∀ k, k < n → m'.getByte (dst + BitVec.ofNat 64 k) = c) ∧ ByteFrame m m' dst n := by
  refine ⟨fun k hk => ?_, fun b hb => ?_⟩
  · have he : dst + BitVec.ofNat 64 k = BitVec.ofNat 64 (dst.toNat + k) := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_add_ofNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [he]
    exact h.1 _ (by omega) (by omega)
  · have := h.2 b.toNat b.isLt (by unfold InRange at hb; omega)
    simpa [bat] using this

/-! ## The function -/

/-- `x - 1` as a number, for `x ≠ 0`. -/
private theorem toNat_sub_one {x : Word} (h : 0 < x.toNat) : (x + 18446744073709551615#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- `y` rounded down to a multiple of 8, as the code computes it. -/
private theorem toNat_and_not7 (y : Word) : (y &&& 18446744073709551608#64).toNat = y.toNat - y.toNat % 8 := by
  rw [show (18446744073709551608#64 : Word) = ~~~7#64 by decide]
  exact toNat_alignToDword y

/-- The bytes from `x` to the next multiple of 8, as the code computes them. -/
private theorem toNat_neg_and7 (x : Word) : (0#64 - x &&& 7#64).toNat = (8 - x.toNat % 8) % 8 := by
  rw [Proof.Runtime.Alloc.and7, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.add_zero]
  omega

/-- A register file written only at `x12` to `x16` agrees with its start elsewhere. -/
local macro "agree" : tactic => `(tactic| (intro x h12 h13 h14 h15 h16) <;>
  simp only [Lprog.updReg_apply, h12, h13, h14, h15, h16, ↓reduceIte])

/-- **`memset` is total, with the bytes it writes.** -/
theorem total (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) :
    MemsetSpecT env p i 0 := by
  intro Q ret top rest regs m hpre _ hk
  have ⟨⟨⟨hra, hsp⟩, hstk, hst, hnx, ⟨hnw, hwin0⟩, hal⟩, hwin⟩ := hpre
  have hn := hnw
  unfold SetPre NoWrap at hn
  -- the return, with every byte of `[dst, dst + n)` written
  have hRet : ∀ r m', Base env ret top regs m r m' →
      Fill m m' (regs .x10).toNat (regs .x12).toNat ((regs .x11).truncate 8)
        ((regs .x10).toNat + (regs .x12).toNat) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 75, ret, top⟩ :: rest, r, m'⟩ :=
    fun _ _ ⟨h1, ha, h10, _, hk'⟩ hf => TotalRv.ret hp rfl h1 ha.1
      (hk _ _ ⟨⟨ha, hk'.1, hk'.2.1, h10, hf.setPost hn⟩, hk'.2.2⟩)
  -- the bytes after the doublewords: `x13` the next, `x12 = k` left
  have hTail : ∀ k r m', (TailInv env ret top regs m k r m' ∧
      Fill m m' (regs .x10).toNat (regs .x12).toNat ((regs .x11).truncate 8) (r .x13).toNat) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, r, m'⟩ := by
    refine Total.loop (I := rvIsa) _ fun k r m' ⟨⟨hb, hk12, hk0, hlo, hend⟩, hf⟩ ih => ?_
    have hw : InWin env (regs .x10) (regs .x12).toNat := hwin0.resolve_left (by omega)
    have hw1 := (hw.sub (x := r .x13) (w := 1) hlo (by omega)).inWindow hwin
    tsteps hp
    refine TotalRv.sb hp rfl (by tnorm; exact hw1)
      (by tnorm; exact (hb.2.2.2.2.windows hwin).noCodeAt hw1 (by decide)) ?_
    tnorm
    tsteps hp
    have hb' := ((hb.upd (d := .x12) (by decide) (r .x12 + 18446744073709551615#64)).upd (d := .x13) (by decide)
      (r .x13 + 1#64)).mem (hb.2.2.2.2.setByte hw hlo (by omega) ((r .x11).truncate 8))
    have hf' := hf.byte (v := (r .x11).truncate 8) rfl hlo (by omega) hn (by rw [hb.2.2.2.1])
    have hx := toNat_add_ofNat (a := r .x13) (k := 1) (by unfold InWin at hw; omega)
    tcond hp as hc
    · have h1 := toNat_sub_one (x := r .x12) (by omega)
      refine ih (k - 1) _ _ (by omega) ⟨⟨hb', ?_, ?_, ?_, ?_⟩, ?_⟩ <;> try tomega
      tnorm
      rw [show (r .x13 + 1#64).toNat = (r .x13).toNat + 1 from hx]
      exact hf'
    · tstep hp
      refine hRet _ _ hb' ?_
      rw [show (regs .x10).toNat + (regs .x12).toNat = (r .x13).toNat + 1 by
        have h1 := toNat_sub_one (x := r .x12) (by omega)
        omega]
      exact hf'
  -- after the doublewords: `x13` their end, `x12 % 8` bytes after it
  have hSec3 : ∀ r m', Base env ret top regs m r m' → (regs .x10).toNat ≤ (r .x13).toNat →
      (r .x13).toNat + (r .x12).toNat % 8 = (regs .x10).toNat + (regs .x12).toNat →
      Fill m m' (regs .x10).toNat (regs .x12).toNat ((regs .x11).truncate 8) (r .x13).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 52, ret, top⟩ :: rest, r, m'⟩ := by
    intro r m' hb hlo hend hf
    have h7 := Proof.Runtime.Alloc.and7 (r .x12)
    have hx : (r .x13 + (r .x12 &&& 7#64)).toNat = (r .x13).toNat + (r .x12).toNat % 8 := by
      rw [BitVec.toNat_add, h7]
      omega
    have hb' := (hb.upd (d := .x12) (by decide) (r .x12 &&& 7#64)).upd (d := .x14) (by decide)
      (r .x13 + (r .x12 &&& 7#64))
    tsteps hp
    tcond hp as hc
    · exact hTail ((r .x12).toNat % 8) _ _ ⟨⟨hb', by tnorm; exact h7, by omega, by tnorm; exact hlo, by tomega⟩,
        by tnorm; exact hf⟩
    · tsteps hp
      refine hRet _ _ hb' ?_
      rw [show (regs .x10).toNat + (regs .x12).toNat = (r .x13).toNat by omega]
      exact hf
  -- the doublewords
  have hDw : ∀ k r m', (DwInv env ret top regs m k r m' ∧ r .x15 = splat (regs .x11) ∧
      Fill m m' (regs .x10).toNat (regs .x12).toNat ((regs .x11).truncate 8) (r .x14).toNat) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 46, ret, top⟩ :: rest, r, m'⟩ := by
    refine Total.loop (I := rvIsa) _
      fun k r m' ⟨⟨hb, hal8, hlo, hend, hk0, hk8, hend3⟩, hs, hf⟩ ih => ?_
    have hw : InWin env (regs .x10) (regs .x12).toNat := hwin0.resolve_left (by omega)
    have hw8 := (hw.sub (x := r .x14) (w := 8) hlo (by omega)).inWindow hwin
    have hx : (r .x14 + 8#64).toNat = (r .x14).toNat + 8 := toNat_add_ofNat (by unfold InWin at hw; omega)
    have hb' := (hb.upd (d := .x14) (by decide) (r .x14 + 8#64)).mem
      (hb.2.2.2.2.setMem (v := r .x15) hw hal8 hlo (by omega))
    have hf' := hf.dword (v := r .x15) rfl hal8 hlo (by omega) hn (fun k hk => by rw [hs]; exact extractByte_splat _ hk)
    tsteps hp
    refine TotalRv.sd8 hp rfl (by tnorm; exact hw8) (by tnorm; exact hal8)
      (by tnorm; exact (hb.2.2.2.2.windows hwin).noCodeAt hw8 (by decide)) ?_
    tnorm
    tsteps hp
    tcond hp as hc
    · refine ih (k - 8) _ _ (by omega) ⟨⟨hb', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals first | tomega | (tnorm; rw [hx]; exact hf')
    · refine hSec3 _ _ hb' (by tomega) (by tomega) ?_
      tnorm
      rw [show (r .x13).toNat = (r .x14).toNat + 8 by omega]
      exact hf'
  -- from the first doubleword boundary `x14 = dst + x13`
  have hSec2 : ∀ r m', Base env ret top regs m r m' → (r .x14).toNat % 8 = 0 →
      (r .x14).toNat = (regs .x10).toNat + (r .x13).toNat → (r .x13).toNat ≤ 7 →
      (r .x12).toNat = (regs .x12).toNat → 16 ≤ (regs .x12).toNat →
      Fill m m' (regs .x10).toNat (regs .x12).toNat ((regs .x11).truncate 8) (r .x14).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 24, ret, top⟩ :: rest, r, m'⟩ := by
    intro r m' hb hal8 h14 h13 h12 h16 hf
    have hs : (r .x12 - r .x13).toNat = (regs .x12).toNat - (r .x13).toNat := by
      rw [BitVec.toNat_sub]
      omega
    have ha := toNat_and_not7 (r .x12 - r .x13)
    have he : (r .x14 + (r .x12 - r .x13 &&& 18446744073709551608#64)).toNat =
        (r .x14).toNat + ((regs .x12).toNat - (r .x13).toNat - ((regs .x12).toNat - (r .x13).toNat) % 8) := by
      rw [BitVec.toNat_add, ha, hs]
      omega
    tsteps hp
    tcond hp as hc
    · refine hSec3 _ _ (Base.of_agree hb (by agree)) (by tomega) (by tomega) ?_
      tnorm
      rw [show (r .x14 + (r .x12 - r .x13 &&& 18446744073709551608#64)).toNat = (r .x14).toNat by omega]
      exact hf
    · iterate 14 tstep hp
      refine hDw ((regs .x12).toNat - (r .x13).toNat - ((regs .x12).toNat - (r .x13).toNat) % 8) _ _
        ⟨⟨Base.of_agree hb (by agree), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals first | tomega | (tnorm; rw [hb.2.2.2.1]; rfl)
  -- the bytes before the first doubleword boundary
  have hHead : ∀ k r m', (HeadInv env ret top regs m k r m' ∧
      Fill m m' (regs .x10).toNat (regs .x12).toNat ((regs .x11).truncate 8) (r .x16).toNat) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 16, ret, top⟩ :: rest, r, m'⟩ := by
    refine Total.loop (I := rvIsa) _
      fun k r m' ⟨⟨hb, hk15, hk0, hlo, hend, h14, hal8, h13, h12, h16⟩, hf⟩ ih => ?_
    have hw : InWin env (regs .x10) (regs .x12).toNat := hwin0.resolve_left (by omega)
    have hw1 := (hw.sub (x := r .x16) (w := 1) hlo (by omega)).inWindow hwin
    have h1 := toNat_sub_one (x := r .x15) (by omega)
    have hx := toNat_add_ofNat (a := r .x16) (k := 1) (by unfold InWin at hw; omega)
    have hb' := ((hb.upd (d := .x15) (by decide) (r .x15 + 18446744073709551615#64)).upd (d := .x16) (by decide)
      (r .x16 + 1#64)).mem (hb.2.2.2.2.setByte hw hlo (by omega) ((r .x11).truncate 8))
    have hf' := hf.byte (v := (r .x11).truncate 8) rfl hlo (by omega) hn (by rw [hb.2.2.2.1])
    tsteps hp
    refine TotalRv.sb hp rfl (by tnorm; exact hw1)
      (by tnorm; exact (hb.2.2.2.2.windows hwin).noCodeAt hw1 (by decide)) ?_
    tnorm
    tsteps hp
    tcond hp as hc
    · refine ih (k - 1) _ _ (by omega) ⟨⟨hb', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> try tomega
      tnorm; rw [hx]; exact hf'
    · refine hSec2 _ _ hb' (by tomega) (by tomega) (by tomega) (by tomega) h16 ?_
      tnorm
      rw [show (r .x14).toNat = (r .x16).toNat + 1 by omega]
      exact hf'
  -- the entry
  have hb0 : Base env ret top regs m regs m := ⟨hra, AbiRegs.refl hsp, rfl, rfl, Env.Frame.refl hnx, hst, rfl⟩
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
      refine hRet _ _ (Base.of_agree hb0 (by agree)) ?_
      rw [show (regs .x10).toNat + (regs .x12).toNat = (regs .x10).toNat by omega]
      exact Fill.refl
    · exact hTail (regs .x12).toNat _ _ ⟨⟨Base.of_agree hb0 (by agree), by tnorm, by omega, by tomega, by tomega⟩,
        by tnorm; exact Fill.refl⟩
  -- at least 16: the bytes to a doubleword boundary, the doublewords, the bytes after them
  · have h13 := toNat_neg_and7 (regs .x10)
    have hx : (regs .x10 + (0#64 - regs .x10 &&& 7#64)).toNat =
        (regs .x10).toNat + (8 - (regs .x10).toNat % 8) % 8 := by
      rw [BitVec.toNat_add, h13]
      omega
    tsteps hp
    tcond hp as hc'
    · refine hSec2 _ _ (Base.of_agree hb0 (by agree)) (by tomega) (by tomega) (by tomega) (by tnorm) (by omega) ?_
      tnorm
      rw [show (regs .x10 + (0#64 - regs .x10 &&& 7#64)).toNat = (regs .x10).toNat by omega]
      exact Fill.refl
    · iterate 4 tstep hp
      exact hHead ((8 - (regs .x10).toNat % 8) % 8) _ _ ⟨⟨Base.of_agree hb0 (by agree), by tomega, by omega,
        by tomega, by tomega, by tomega, by tomega, by tomega, by tnorm, by omega⟩, by tnorm; exact Fill.refl⟩

/-- **The C wrapper `memset` is total, with the bytes it writes**, from `compiler_builtins`' `memset`. -/
theorem memset_total {p : Lprog (Op Reg) Reg} {i need : Nat} (L : Rv64mc.Gen.Memset.Link)
    (hp : p[i]? = some (Rv64mc.Gen.Memset.tmpl L)) (hL : L.WF p) (h : MemsetSpecT env p L.memset.idx need) :
    MemsetSpecT env p i need :=
  MemsetT.tail_total hp rfl hL.memset hL.s0 h (fun _ _ h => by simpa [MemsetPreT, SetPre, updReg_apply] using h)
    (fun _ _ _ _ h => by simpa [SetPost, updReg_apply] using h)
    (fun _ _ _ h => by simpa [CopyOut, updReg_apply] using h)

end Rv64mc.Proof.Runtime.MemsetBytesT

/-- info: 'Rv64mc.Proof.Runtime.MemsetBytesT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.MemsetBytesT.total

/--
info: 'Rv64mc.Proof.Runtime.MemsetBytesT.memset_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.MemsetBytesT.memset_total
