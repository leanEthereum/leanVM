/-
  Rv64mc.Proof.Whir.LanesOfT

  `verify_whir`'s closure `lanes_of(row: &[K]) -> Vec<E>` (`whir.rs`: at level `0` the row's words reversed, each as
  an `E` with high word `0`, else `ext_row(row)`) is total (`specT`): from a result's slot of `24` bytes owned, in a
  window, 8-byte aligned, and the row (`a2`, `a3`) none or allocated, in a window and 8-byte aligned
  (`ExtRowT.SliceW`), it returns with the slot a vector of `E`s (`VecT`) of `len` elements at level `0` (`a1 = 0`),
  `len / 2` otherwise, its buffer allocated since the entry unless it has no capacity, writing at most the slot
  besides what it allocates (`SretOut`), or the run ends with `a0 = 2` where `ext_row`, `alloc`, `handle_error` or
  `reserve` does. Safety only; it has no partial contract (class D).

  At a level above `0` it tail-calls `ext_row` (`ExtRowT.specT`). At level `0` the frame and the header at `sp` are
  `ext_row`'s, and its pieces are reused: `ExtRowT.Hdr` (with its own five saved slots), `Hdr.push2`, `Hdr.vecT`,
  `Hdr.reserve`. The vector is allocated with capacity `len` (`handle_error` above `2^59` words or when `alloc`
  fails) and `reserve(len)` finds the room, so the copy loop's stores lie in the buffer. Cut at `reserve`'s call
  (instruction 92, `res_ok`), at the copy loop's head (instruction 122, `loop`: `Total.loop` with the words left as
  the measure) and at the exit (instruction 134, `fin_ok`).

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `RInv`, `LInv`, `FinInv`

  ## Main results

  * `fin_ok`, `loop`, `res_ok`, `total`
-/

import Rv64mc.Proof.Whir.ExtRowT
import Rv64mc.Gen.Tmpl.Verifier.Whir.VerifyWhirVerifyStackedOpeningClosure1.Closure0

namespace Rv64mc.Proof.Whir.LanesOfT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Whir.VecWordT (vecT_stores)
open Rv64mc.Proof.Whir.ExtRowT (SliceW Hdr Keep shl4 hdr_words)
open Rv64mc.Gen.Verifier.Whir.VerifyWhirVerifyStackedOpeningClosure1.Closure0 (Link tmpl)

/-- The total precondition: the result's slot (`24` bytes) in a window, 8-byte aligned, owned; the row's words
    `SliceW`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24 ∧
    SliceW env m (regs .x12) (regs .x13)

/-- The total postcondition: the slot a vector of `E`s of `len` elements at level `0`, `len / 2` otherwise, its buffer
    allocated since the entry unless it has no capacity. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧
    (vecLen m' (regs .x10)).toNat = (if regs .x11 = 0#64 then (regs .x13).toNat else (regs .x13).toNat / 2) ∧
    (vecCap m' (regs .x10) = 0#64 ∨ (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat)

/-- **The total contract of `lanes_of`**: `PreT` to `PostT`, writing at most the slot (`SretOut`), or ending the run
    with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (SretOut Layouts.Vec.byteSize) (Stop := AbortStop)

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- The copy loop's head (instruction 122), `k` words left, at least one: the stack pointer, the slot's address in
    `s1`, the final length `n` in `x10`, the source's cursor `x11` at the `k`-th word of `row` (`a2`) and its end
    `x13` (`row - 8`), the destination's cursor `x12` in the buffer; `Hdr`; the words `8 n` bytes, allocated and in a
    window, 8-byte aligned. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (n : Nat) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x9 = regs .x10 ∧ R .x10 = BitVec.ofNat 64 n ∧
    (R .x11).toNat + 8 = (regs .x12).toNat + 8 * k ∧ R .x13 = regs .x12 + 18446744073709551608#64 ∧
    (R .x12).toNat + 16 * k = (M.getMem (top + 18446744073709551560#64)).toNat + 8 + 16 * n ∧ 1 ≤ k ∧ k ≤ n ∧
    n = (regs .x13).toNat ∧ Keep regs R ∧ Hdr env ret top regs m n M ∧
    env.Live m (regs .x12) (8 * (regs .x13).toNat) ∧ InWin env (regs .x12) (8 * (regs .x13).toNat) ∧
    (regs .x12).toNat % 8 = 0

/-- The exit (instruction 134): the stack pointer, the slot's address in `s1`, the length `n` (`len`) in `x10`,
    `Hdr`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (n : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x9 = regs .x10 ∧ R .x10 = BitVec.ofNat 64 n ∧
    n = (regs .x13).toNat ∧ n < 2 ^ 59 ∧ Keep regs R ∧ Hdr env ret top regs m n M

set_option rv_sym.heap true in
/-- **The exit**: the vector's header copied into the slot with the length `n`, the epilogue, the return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 64 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 24) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 24) (h11 : regs .x11 = 0#64) {n : Nat} :
    ∀ R M, FinInv env ret top regs m n R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 134, ret, top⟩ :: rest, R, M⟩ := by
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
  · simp only [h11, ↓reduceIte]; rw [hn', hnl]

set_option rv_sym.heap true in
/-- **The copy loop**, from its head: a word copied into the buffer as an `E` (its high word `0`), then back to the
    head or to the exit; one word fewer left. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 64 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {n : Nat}
    (hfin : ∀ R M, FinInv env ret top regs m n R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 134, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv env ret top regs m n k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 122, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env ret top regs m n) fun k R M hI ih => ?_
  obtain ⟨-, -, -, h11, h13, h12, hk1, hkn, hnl, hK, hH, wl, ww, wa⟩ := id hI
  have hlay := env.layout
  have hnM := hH.1.2.1
  have hnm := hH.1.1
  have hcap0 : (M.getMem (top + 18446744073709551552#64)).toNat ≠ 0 := by have := hH.2.2.2.2.2.2.1; omega
  obtain ⟨hp0, hpl, hpa⟩ := hH.2.2.2.2.1.resolve_left hcap0
  unfold Env.Live at hpl wl
  have hncap := hH.2.2.2.2.2.2.1
  have hw := ww.lt
  have hr8 : 8 ≤ (regs .x12).toNat := by unfold InWin at ww; omega
  have e11 : (R .x11 + 18446744073709551608#64).toNat = (R .x11).toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e12 : (R .x12 + 18446744073709551608#64).toNat = (R .x12).toNat - 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rv_introT hI
  clear hI_28 hI_31
  rv_symT hp stop [122, 134] with [(by omega : env.stackLimit.toNat + 64 ≤ top.toNat)]
  all_goals
    have hP := fun v w => ExtRowT.Hdr.push2 (b := R .x12) (v := v) (w := w) hH (by omega) (by omega) (by omega)
      (by omega)
  -- back to the head
  · have er : (regs .x12 + 18446744073709551608#64).toNat = (regs .x12).toNat - 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hk2 : 2 ≤ k := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by rw [e11, er]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨by rv_closeT, by rv_closeT, by rv_closeT, ?_, by rv_closeT, ?_, by omega,
      by omega, hnl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, (hP _ _).1, wl, ww, wa⟩
    all_goals simp only [Tactic.rf]
    · rw [e11]; omega
    · rw [(hP _ _).2, toNat_add_ofNat (by omega)]; omega
  -- the last word: the exit
  · refine hfin _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, hnl, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      (hP _ _).1⟩
    unfold InWin at ww; omega

/-- Before `reserve`'s call (instruction 92): the stack pointer, the slot's address in `s1`, `row` in `s2`, `len` in
    `s0` and `a1`, the header's address in `a0`; `Hdr` for `len` elements; the words `SliceW`, `len < 2^59`. -/
def RInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x9 = regs .x10 ∧ R .x18 = regs .x12 ∧ R .x8 = regs .x13 ∧
    R .x10 = top + 18446744073709551552#64 ∧ R .x11 = regs .x13 ∧ Keep regs R ∧
    Hdr env ret top regs m (regs .x13).toNat M ∧ SliceW env m (regs .x12) (regs .x13) ∧ (regs .x13).toNat < 2 ^ 59

set_option rv_sym.heap true in
/-- **`reserve(len)`**, then the copy loop, or the exit when `row` is empty. -/
theorem res_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needR : Nat} (hnR : 64 + needR ≤ need) (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hloop : ∀ k R M, LInv env ret top regs m (regs .x13).toNat k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 122, ret, top⟩ :: rest, R, M⟩)
    (hfin : ∀ R M, FinInv env ret top regs m (regs .x13).toNat R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 134, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, RInv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 92, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, -, -, -, hK, hH, hS, h59⟩ := id hinv
  have hV := hH.vecT (by omega) hW.top_le hal
  rv_introT hinv
  rv_symT hp stop [122, 134] with [hL, (by omega : env.stackLimit.toNat + 64 ≤ top.toNat)] using [hres]
  all_goals
    have hlay := env.layout
    have hsp : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by tn
    have hH1 := hH.reserve (by rw [hsp]; omega) (by rw [hsp]; omega)
      (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte])
      (by simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte]) hret1_14 hret1_25 hret1_15
      ⟨hret1_16, hret1_17, hret1_18⟩
    have hz : m1.getMem (top + 18446744073709551568#64) = 0#64 := hH1.2.2.2.2.2.2.2.2
  -- `row` empty: the exit
  · refine hfin _ _ ⟨by rv_closeT, by rv_closeT, ?_, rfl, h59, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hH1⟩
    simp only [Tactic.rf, hz, hc]; rfl
  -- the copy loop
  · have hn0 : (regs .x13).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    obtain ⟨wl, ww, wa⟩ := hS.resolve_left hn0
    have hw := ww.lt
    have hw2 : (regs .x12).toNat + 8 * (regs .x13).toNat ≤ 0xc0000000 := by
      unfold InWin at ww; rcases ww with h | h <;> omega
    have s3 : (regs .x13 <<< 3).toNat = 8 * (regs .x13).toNat := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have s8 : (regs .x13 <<< 3 + 18446744073709551608#64).toNat = 8 * (regs .x13).toNat - 8 := by
      rw [BitVec.toNat_add, s3, BitVec.toNat_ofNat]; omega
    refine hloop _ _ _ ⟨by rv_closeT, by rv_closeT, ?_, ?_, rfl, ?_, by omega, Nat.le_refl _, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hH1, wl, ww, wa⟩
    all_goals simp only [Tactic.rf, hz]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, s8, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [BitVec.toNat_add, s8]; omega
    · have hcap1 := hH1.2.2.2.2.2.2.1
      obtain ⟨-, hql, -⟩ := hH1.2.2.2.2.1.resolve_left (by omega)
      have hnx1 := hH1.1.2.1
      unfold Env.Live at hql
      rw [show (0#64 : Word) <<< 4 = 0#64 from rfl, BitVec.zero_add, toNat_add_ofNat (by omega)]

set_option rv_sym.heap true in
/-- **`lanes_of` is total**: `ext_row` above level `0`; else the allocation of `len` elements, the header, then
    `reserve` and the copy. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needE needR needA needH : Nat} (hnE : needE ≤ need) (hnR : 64 + needR ≤ need) (hnA : 64 + needA ≤ need)
    (hnH : 64 + needH ≤ need) (hext : ExtRowT.specT env p L.extRow.idx needE)
    (hres : Runtime.ReserveT.ReserveSpecT env 8 16 p L.reserve.idx needR)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hhe : Aborts env p L.handleError.idx needH) : specT env p i need := by
  have hac : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 64 ≤ top.toNat)]
  have hres_ok := fun (h11 : regs .x11 = 0#64) =>
    have hfin := fin_ok env p i L hp hk hpre_3 (by omega) hpre_11 hpre_12 hpre_6 hpre_7 (hpre_2 ▸ ⟨hpre_8, hpre_9⟩) h11
      (n := (regs .x13).toNat)
    res_ok env p i L hp hL hnR hres hstop hpre_3 hpre_11 hpre_12
      (loop env p i L hp hpre_3 (by omega) hpre_11 hpre_12 hfin) hfin
  rv_symT hp stop [92] with [hL, (by omega : env.stackLimit.toNat + 64 ≤ top.toNat)] using [hext, hac, hhe]
  all_goals try
    have h59 : (regs .x13).toNat < 2 ^ 59 := by
      have := congrArg BitVec.toNat hc_2
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
      simp only [BitVec.toNat_ofNat] at this
      omega
  -- `row` empty: the header `(0, 8, 0)`
  · refine hres_ok hc_1 _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpre_10, h59⟩
    all_goals rv_closeT
    exact .inl rfl
  · rw [shl4 (by omega)]; omega
  -- the header `(len, ptr, 0)`, `ptr` from `alloc`
  · refine hres_ok hc_1 _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpre_10, h59⟩
    all_goals rv_closeT
    · refine .inr ⟨by have := hpre_12.next_ge; omega, ?_, hret1_17⟩
      unfold Env.Live
      repeat (rw [Env.next_setMem_stack]; rotate_left; tn)
      rw [shl4 (by omega)] at hret1_18; omega
    · exact .inr hret1_16
  -- `ext_row`'s result
  · have := hret4_21
    simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero] at this
    exact this
  · simp only [hc, ↓reduceIte]; exact hret4_22
  · simpa only [vecCap, vecPtr, Layouts.Vec.cap, Layouts.Vec.ptr, BitVec.add_zero] using hret4_23

end Rv64mc.Proof.Whir.LanesOfT

/-- info: 'Rv64mc.Proof.Whir.LanesOfT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.LanesOfT.total
