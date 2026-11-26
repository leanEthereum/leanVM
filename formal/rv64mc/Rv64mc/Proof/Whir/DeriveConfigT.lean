/-
  Rv64mc.Proof.Whir.DeriveConfigT

  `verifier::whir::derive_config(log_n, log_inv_rate)` is total (`specT`): from a result's slot owned, in a window
  and 8-byte aligned (`DeriveConfig.Pre` and the window), it writes `Err` (the niche `-1` in the first word) or a
  `WhirConfig` whose `log_inv_rates` and `folds` are vectors (`VecReprT.VecT`) of one length, their buffers allocated
  since the entry, and whose `queries` are `whir_queries`' slice of the same length (`QueriesOk`, the tabulated
  counts), writing at most the slot besides what it allocates (`SretOut`, the partial contract's), or the run ends
  with `a0 = 2` where `alloc`, `grow_one` or the allocation panic does. Safety only: `DeriveConfig.spec`'s functional
  postcondition (`Model.deriveConfigRust`) is owed. Over any program holding its template, from the total contracts
  of `whir_queries`, `alloc`, `RawVec<usize>::grow_one` and `panic_nounwind_fmt`. There was no partial proof
  (class C).

  The code builds both vectors with one element, then runs the first pass (instructions 111 to 132: `log_inv_rates`
  grown, its second element, `folds` grown if full, its second element) and a loop whose head is instruction 168,
  each pass pushing one element onto each vector (`grow_one` where full), `(log_n - 12) >> 2` passes in all. Cut into
  parts at each `grow_one` and at the loop's head, each part taking the next one's invariant as a continuation:
  `total` (the entry, `whir_queries`, both `alloc`s), `g0_ok` (the first `grow_one`, `E2Inv`), `e2_ok` (`E3Inv`),
  `e3_ok` (`LInv`), the loop (`head_ok`, `a_ok`, `b_ok`; `Total.loop` with the passes left as the measure), `exit`
  (the count check, the copy into the slot), `ret_ok` (the epilogue). Each header's facts are `Hd`, carried across
  `grow_one` (`Hd.grown`, `grow_r`, `grow_f`), stores into the heap (`Hd.heap`), the frame (`Hd.stk`) and the
  length (`Hd.len`); the frame and the saved registers are `BaseM`.

  ## Main definitions

  * `PreT`, `QueriesOk`, `OkCfg`, `PostT`, `specT`, `Hd`, `Saved`, `BaseM`, `Hds`, `XInv`, `RetInv`, `RS`, `BaseR`,
    `LoopR`, `LInv`, `AInv`, `BInv`, `E2Inv`, `E3Inv`, `G0Inv`

  ## Main results

  * `ret_ok`, `exit`, `head_ok`, `a_ok`, `b_ok`, `loop`, `e3_ok`, `e2_ok`, `g0_ok`, `total`
-/

import Rv64mc.Proof.Whir.WhirQueriesT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.GrowOneT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Spec.Whir.DeriveConfig
import Rv64mc.Gen.Tmpl.Verifier.Whir.DeriveConfig
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Whir.DeriveConfigT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Whir
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Runtime.GrowOneT (GrowOneSpecT)
open Rv64mc.Gen.Verifier.Whir.DeriveConfig (Link tmpl)

/-- The total precondition: `DeriveConfig.Pre` (the slot owned), and the slot in a window and 8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  DeriveConfig.Pre env regs m ∧ InWin env (regs .x10) Layouts.ResultWhirConfig.byteSize ∧ (regs .x10).toNat % 8 = 0

/-- **The queries' slice** `(qp, ql)`: `whir_queries`' answer at this size and rate, its counts constants of the
    image. -/
def QueriesOk (env : Env) (logN rate : Nat) (qp ql : Word) : Prop :=
  ∃ qs, Model.whirQueriesRust logN rate = some qs ∧ ql = BitVec.ofNat 64 qs.length ∧
    DataWords env qp (qs.map (BitVec.ofNat 64))

/-- **The `WhirConfig` at the slot**: `log_inv_rates` (offset `0`) and `folds` (offset `24`) vectors of `usize`, their
    buffers allocated since the entry, both as long as the queries' slice (offset `48`). -/
def OkCfg (env : Env) (regs : Reg → Word) (m m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 8 ∧ VecT env m' (regs .x10 + 24#64) 8 ∧
    (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat ∧ (env.next m).toNat ≤ (vecPtr m' (regs .x10 + 24#64)).toNat ∧
    vecLen m' (regs .x10) = m'.getMem (regs .x10 + 56#64) ∧
    vecLen m' (regs .x10 + 24#64) = m'.getMem (regs .x10 + 56#64) ∧
    QueriesOk env (regs .x11).toNat (regs .x12).toNat (m'.getMem (regs .x10 + 48#64)) (m'.getMem (regs .x10 + 56#64))

/-- The total postcondition: unless the slot holds `Err` (its first word the niche `-1`), `OkCfg`. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (regs .x10) ≠ 18446744073709551615#64 → OkCfg env regs m m'

/-- **The total contract of `derive_config`**: `PreT` to `PostT`, writing at most the slot (`SretOut`, the partial
    contract's), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (SretOut Layouts.ResultWhirConfig.byteSize) (Stop := AbortStop)

/-- A vector's header in the frame, its capacity, pointer and length at `ac`, `ap`, `al`: its buffer `BufT`, of fewer
    than `2^63` bytes, allocated since the entry, its length `n` within its capacity. -/
def Hd (env : Env) (m : MachineState) (ac ap al : Word) (n : Nat) (M : MachineState) : Prop :=
  BufT env M (M.getMem ac) (M.getMem ap) 8 ∧ (M.getMem ac).toNat * 8 < 2 ^ 63 ∧ M.getMem al = BitVec.ofNat 64 n ∧
    n ≤ (M.getMem ac).toNat ∧ (env.next m).toNat ≤ (M.getMem ap).toNat

/-- The saved registers' twelve slots. -/
def Saved (ret top : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23 ∧ M.getMem (top + 18446744073709551536#64) = regs .x24 ∧
    M.getMem (top + 18446744073709551528#64) = regs .x25 ∧ M.getMem (top + 18446744073709551520#64) = regs .x26

/-- What every part keeps of the memory: the frame, the code, the static data, the saved registers' slots. -/
def BaseM (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (M : MachineState) : Prop :=
  env.Frame top Tactic.F m M ∧ M.code = m.code ∧ env.Static M ∧ Saved ret top regs M

/-- The two vectors, `folds` at `sp` and `log_inv_rates` at `sp + 0x18`, both of length `n`. -/
def Hds (env : Env) (top : Word) (m : MachineState) (n : Nat) (M : MachineState) : Prop :=
  Hd env m (top + 18446744073709551424#64) (top + 18446744073709551432#64) (top + 18446744073709551440#64) n M ∧
    Hd env m (top + 18446744073709551448#64) (top + 18446744073709551456#64) (top + 18446744073709551464#64) n M

/-- At the ladder's end (instruction 212): the stack pointer, the slot, the queries' slice in `x18`, `x9`, the length
    in `x23`. -/
def XInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (qp ql : Word) (n : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x8 = regs .x10 ∧ R .x9 = ql ∧ R .x18 = qp ∧
    R .x23 = BitVec.ofNat 64 n ∧ R .x27 = regs .x27 ∧
    BaseM env ret top regs m M ∧ Hds env top m n M ∧ QueriesOk env (regs .x11).toNat (regs .x12).toNat qp ql

/-- At the epilogue (instruction 268): the result written, `PostT`, the frame writing the slot. -/
def RetInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x27 = regs .x27 ∧
    env.Frame top (SretOut Layouts.ResultWhirConfig.byteSize regs m) m M ∧ M.code = m.code ∧ env.Static M ∧
    Saved ret top regs M ∧ PostT env regs m R M

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))

/-- A store outside the saved registers' slots keeps them. -/
theorem Saved.setMem {ret top a v : Word} {regs : Reg → Word} {M : MachineState} (h : Saved ret top regs M)
    (h96 : 96 ≤ top.toNat) (ha : a.toNat + 8 ≤ top.toNat - 96 ∨ top.toNat ≤ a.toNat) :
    Saved ret top regs (M.setMem a v) := by
  have e : ∀ c : Nat, 0 < c → c ≤ 96 → (M.setMem a v).getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) := fun c h0 h1 =>
    MachineState.getMem_setMem_ne fun he => by
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      have := top.isLt
      omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨(e 8 (by omega) (by omega)).trans h1, (e 16 (by omega) (by omega)).trans h2,
    (e 24 (by omega) (by omega)).trans h3, (e 32 (by omega) (by omega)).trans h4,
    (e 40 (by omega) (by omega)).trans h5, (e 48 (by omega) (by omega)).trans h6,
    (e 56 (by omega) (by omega)).trans h7, (e 64 (by omega) (by omega)).trans h8,
    (e 72 (by omega) (by omega)).trans h9, (e 80 (by omega) (by omega)).trans h10,
    (e 88 (by omega) (by omega)).trans h11, (e 96 (by omega) (by omega)).trans h12⟩

set_option rv_sym.heap true in
/-- **The epilogue**: the saved registers restored, the return. -/
theorem ret_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (SretOut Layouts.ResultWhirConfig.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 192 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) :
    ∀ R M, RetInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 268, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 192 ≤ top.toNat)]

/-- What the epilogue reads back, over a memory `M0` the stores start from: the frame writing the slot, the static
    data, the saved registers' slots, `NEXT` kept. -/
def RS (env : Env) (ret top : Word) (regs : Reg → Word) (m M0 : MachineState) (M : MachineState) : Prop :=
  env.Frame top (SretOut Layouts.ResultWhirConfig.byteSize regs m) m M ∧ env.Static M ∧ Saved ret top regs M ∧
    env.next M = env.next M0

/-- A frame writing nothing writes at most the slot. -/
theorem frame_sret {env : Env} {top : Word} {regs : Reg → Word} {m M : MachineState} (hF : env.Frame top Tactic.F m M) :
    env.Frame top (SretOut Layouts.ResultWhirConfig.byteSize regs m) m M :=
  ⟨hF.1, hF.2.1, fun a ha => hF.2.2 a fun hw => ha (hw.imp_right (·.imp_right (·.imp_right False.elim)))⟩

/-- `RS` across a store into the frame below the saved registers' slots. -/
theorem RS.tmp {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M0 M : MachineState}
    (h : RS env ret top regs m M0 M) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (ha : top.toNat - 192 ≤ a.toNat) (ha' : a.toNat + 8 ≤ top.toNat - 96) :
    RS env ret top regs m M0 (M.setMem a v) :=
  ⟨Tactic.frame_slot h.1 (by omega) (by omega), Env.static_setMem_stack h.2.1 (by omega),
    h.2.2.1.setMem (by omega) (.inl ha'), (Env.next_setMem_stack (by omega)).trans h.2.2.2⟩

/-- `RS` across a store into the slot. -/
theorem RS.sret {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M0 M : MachineState}
    (h : RS env ret top regs m M0 M) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hw : InWin env (regs .x10) 64)
    (ho : env.Owned m top (regs .x10) 64) (hin : InRange (regs .x10) 64 a) :
    RS env ret top regs m M0 (M.setMem a v) := by
  have hlay := env.layout
  have hlt := hw.lt
  unfold InRange at hin
  have hne := hw.ne_next (x := a) (by omega) (by omega)
  refine ⟨Tactic.frame_out h.1 hin hne, Env.static_setMem h.2.1 (ho.not_static hnx (by omega) hin),
    h.2.2.1.setMem (by omega) ?_, (Tactic.next_setMem hne).trans h.2.2.2⟩
  rcases ho.1 with h1 | h1
  · left; omega
  · right; omega

/-- **A `Vec` header** at `a` from its three words. -/
theorem vecT_of {env : Env} {M : MachineState} {a c q l : Word} (hw : InWin env a 24) (ha : a.toNat % 8 = 0)
    (h0 : M.getMem a = c) (h8 : M.getMem (a + 8#64) = q) (h16 : M.getMem (a + 16#64) = l)
    (hb : BufT env M c q 8) (hc : c.toNat * 8 < 2 ^ 63) (hl : l.toNat ≤ c.toNat) : VecT env M a 8 := by
  have r0 : M.getMem (a + BitVec.ofNat 64 0) = c := by rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, h0]
  refine ⟨hw, ⟨hw.sub (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega), ha, ?_, ?_⟩, ?_⟩
  · simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, r0]
    rw [show BitVec.ofNat 64 8 = 8#64 from rfl, h8]; exact hb
  · simp only [rvCapAt, Layouts.RawVecInner.cap, r0]; exact hc
  · simp only [vecCap, vecLen, Layouts.Vec.cap, Layouts.Vec.len, r0]
    rw [show BitVec.ofNat 64 16 = 16#64 from rfl, h16]; exact hl

/-- A word read through a store at another offset from the same base. -/
theorem rd_off {M : MachineState} {t c d v : Word} (h : c ≠ d) :
    (M.setMem (t + d) v).getMem (t + c) = M.getMem (t + c) :=
  MachineState.getMem_setMem_ne fun he => h ((BitVec.add_right_inj t).1 he)

/-- The base word read through a store at a nonzero offset from it. -/
theorem rd_base_off {M : MachineState} {t d v : Word} (h : d ≠ 0#64) : (M.setMem (t + d) v).getMem t = M.getMem t :=
  MachineState.getMem_setMem_ne fun he => h ((BitVec.add_right_inj t).1 (by rw [BitVec.add_zero]; exact he)).symm

/-- `RetInv` from `RS`, the registers and the code; `PostT` may use `RS`. -/
theorem retInv_of {env : Env} {ret top : Word} {regs R : Reg → Word} {m M0 M : MachineState}
    (hR : RS env ret top regs m M0 M) (h2 : R .x2 = top + 18446744073709551424#64) (h27 : R .x27 = regs .x27)
    (hc : M.code = m.code) (hP : RS env ret top regs m M0 M → PostT env regs m R M) : RetInv env ret top regs m R M :=
  ⟨h2, h27, hR.1, hc, hR.2.1, hR.2.2.1, hP hR⟩

set_option rv_sym.heap true in
/-- From the ladder's end: the queries' count against the ladder's, `Ok` or `Err` into the slot, on to the
    epilogue. -/
theorem exit (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 192 ≤ need) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    (hwS : InWin env (regs .x10) 64) (haS : (regs .x10).toNat % 8 = 0) (hoS : env.Owned m top (regs .x10) 64)
    (hret : ∀ R M, RetInv env ret top regs m R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 268, ret, top⟩ :: rest, R, M⟩)
    {qp ql : Word} {n : Nat} :
    ∀ R M, XInv env ret top regs m qp ql n R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 212, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, -, -, -, ⟨hF, hcode, hS, hSv⟩, ⟨hHf, hHr⟩, hQ⟩ := id hinv
  have hRS : RS env ret top regs m M M := ⟨frame_sret hF, hS, hSv, rfl⟩
  have hlay := env.layout
  have hlt := hwS.lt
  rv_introT hinv
  clear hinv_22 hinv_23 hinv_24 hinv_25 hinv_26 hinv_27 hinv_28 hinv_29 hinv_30 hinv_31 hinv_32
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  have hin : ∀ k : Nat, k < 64 → InRange (regs .x10) 64 (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
    ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩
  have hin0 : InRange (regs .x10) 64 (regs .x10) := ⟨Nat.le_refl _, by omega⟩
  rv_symT hp stop [268] with [hlim]
  -- `Err(QueryCountLadder)`
  · refine hret _ _ ⟨by rv_closeT, by rv_closeT, ?_⟩
    have h2 := (hRS.sret (a := regs .x10) (v := 18446744073709551615#64) hlim hnx hwS hoS hin0).sret
      (a := regs .x10 + 8#64) (v := 17#64) hlim hnx hwS hoS (hin 8 (by omega))
    refine ⟨h2.1, by rv_closeT, h2.2.1, h2.2.2.1, fun h => absurd ?_ h⟩
    rw [MachineState.getMem_setMem_ne (fun he => by
      have := congrArg BitVec.toNat he; rw [toNat_add_ofNat (by omega)] at this; omega),
      MachineState.getMem_setMem_eq]
  -- `Ok`
  · refine hret _ _ (retInv_of (M0 := M) ?_ (by rv_closeT) (by rv_closeT)
      (by simp only [MachineState.code_setMem]; exact hcode) ?_)
    · repeat (first
        | refine RS.tmp ?_ hlim (by tn) (by tn)
        | refine RS.sret ?_ hlim hnx hwS hoS hin0
        | refine RS.sret ?_ hlim hnx hwS hoS ⟨by tn, by tn⟩)
      exact hRS
    intro hR _
    have hnn := hR.2.2.2
    obtain ⟨hbf, hcf, hlf, hnf, hpf⟩ := hHf
    obtain ⟨hbr, hcr, hlr, hnr, hpr⟩ := hHr
    have e24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by omega)
    have hn64 : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat]; have := (M.getMem (top + 18446744073709551448#64)).isLt; omega
    simp only [OkCfg, vecPtr, vecLen, Layouts.Vec.ptr, Layouts.Vec.len, BitVec.add_assoc]
    refine ⟨vecT_of (hwS.sub (Nat.le_refl _) (by omega)) haS ?_ ?_ ?_ (hbr.mono (by rw [hnn])) hcr
      (by rw [hn64]; exact hnr), vecT_of (hwS.sub (by omega) (by omega)) (by omega) ?_ ?_ ?_ (hbf.mono (by rw [hnn]))
      hcf (by rw [hn64]; exact hnf), ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp (disch := decide) only [rd_off, rd_base_off, MachineState.getMem_setMem_eq, BitVec.add_assoc,
      show (24#64 : Word) + 8#64 = 32#64 from rfl, show (24#64 : Word) + 16#64 = 40#64 from rfl]
    exacts [hlr, hlf, hpr, hpf, hlr.trans hc.symm, hlf.trans hc.symm, hQ]

/-- What every part keeps of the registers: the stack pointer, the slot, the queries' slice, `x27`. -/
def BaseR (top : Word) (regs : Reg → Word) (qp ql : Word) (R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x8 = regs .x10 ∧ R .x9 = ql ∧ R .x18 = qp ∧ R .x27 = regs .x27

/-- The loop's registers at `j` passes done, the count `c`: the offset `8 j`, `-c`, the length `j + 2`, `4` and `2`. -/
def LoopR (c : Word) (j : Nat) (R : Reg → Word) : Prop :=
  R .x20 = 4#64 ∧ R .x21 = BitVec.ofNat 64 (8 * j) ∧ R .x22 = 0#64 - c ∧ R .x24 = 2#64 ∧
    R .x25 = BitVec.ofNat 64 (j + 2)

/-- The loop's head (instruction 168), `j` passes done, `k` left after this one: both vectors of length `j + 2`,
    their pointers in `x10` and `x19`. -/
def LInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (qp ql c : Word) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  ∃ j, c.toNat = j + 1 + k ∧ BaseR top regs qp ql R ∧ LoopR c j R ∧
    R .x10 = M.getMem (top + 18446744073709551432#64) ∧ R .x19 = M.getMem (top + 18446744073709551456#64) ∧
    BaseM env ret top regs m M ∧ Hds env top m (j + 2) M ∧ QueriesOk env (regs .x11).toNat (regs .x12).toNat qp ql

/-- After `log_inv_rates` has room (instruction 188): its pointer in `x19`, its length below its capacity. -/
def AInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (qp ql c : Word) (j k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  c.toNat = j + 1 + k ∧ BaseR top regs qp ql R ∧ LoopR c j R ∧ R .x19 = M.getMem (top + 18446744073709551456#64) ∧
    BaseM env ret top regs m M ∧ Hds env top m (j + 2) M ∧ j + 2 < (M.getMem (top + 18446744073709551448#64)).toNat ∧
    QueriesOk env (regs .x11).toNat (regs .x12).toNat qp ql

/-- `log_inv_rates`' header words as `rvCapAt`, `rvPtrAt` name them. -/
theorem hdr_r (top : Word) : rvCapAt (top + 18446744073709551448#64) = top + 18446744073709551448#64 ∧
    rvPtrAt (top + 18446744073709551448#64) = top + 18446744073709551456#64 := by
  simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_assoc]
  exact ⟨rfl, rfl⟩

/-- `folds`' header words as `rvCapAt`, `rvPtrAt` name them. -/
theorem hdr_f (top : Word) : rvCapAt (top + 18446744073709551424#64) = top + 18446744073709551424#64 ∧
    rvPtrAt (top + 18446744073709551424#64) = top + 18446744073709551432#64 := by
  simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_assoc]
  exact ⟨rfl, rfl⟩

/-- A header kept word for word, `NEXT` not lowered. -/
theorem Hd.keep {env : Env} {m M m1 : MachineState} {ac ap al : Word} {n : Nat} (hH : Hd env m ac ap al n M)
    (h1 : m1.getMem ac = M.getMem ac) (h2 : m1.getMem ap = M.getMem ap) (h3 : m1.getMem al = M.getMem al)
    (hn : (env.next M).toNat ≤ (env.next m1).toNat) : Hd env m ac ap al n m1 := by
  obtain ⟨hb, hc, hl, hnc, hp⟩ := hH
  exact ⟨by rw [h1, h2]; exact hb.mono hn, by rw [h1]; exact hc, by rw [h3]; exact hl, by rw [h1]; exact hnc,
    by rw [h2]; exact hp⟩

/-- **A header after `grow_one`**: its new buffer fresh, the length kept, now below the capacity. -/
theorem Hd.grown {env : Env} {m M m1 : MachineState} {ac ap al : Word} {n : Nat} (hH : Hd env m ac ap al n M)
    (hc : rvCapAt ac = ac) (hp : rvPtrAt ac = ap)
    (h16 : (M.getMem (rvCapAt ac)).toNat + 1 ≤ (m1.getMem (rvCapAt ac)).toNat)
    (h17 : env.Fresh M m1 (m1.getMem (rvPtrAt ac)) ((m1.getMem (rvCapAt ac)).toNat * 8))
    (h21 : BufT env m1 (m1.getMem (rvCapAt ac)) (m1.getMem (rvPtrAt ac)) 8)
    (h22 : (m1.getMem (rvCapAt ac)).toNat * 8 < 2 ^ 63) (hl : m1.getMem al = M.getMem al)
    (hnM : (env.next m).toNat ≤ (env.next M).toNat) :
    Hd env m ac ap al n m1 ∧ n < (m1.getMem ac).toNat := by
  rw [hc] at h16 h22
  rw [hc, hp] at h17 h21
  obtain ⟨-, -, hl0, hnc, -⟩ := hH
  exact ⟨⟨h21, h22, by rw [hl]; exact hl0, by omega, by have := h17.1; omega⟩, by omega⟩

/-- What `grow_one` writes of the header at `h`: its capacity and pointer. -/
theorem growOut_at {r : Reg → Word} {M : MachineState} {h a : Word} (hr : r .x10 = h) (hlt : h.toNat + 16 < 2 ^ 64)
    (ha : GrowOut r M a) : a.toNat = h.toNat ∨ a.toNat = h.toNat + 8 := by
  simp only [GrowOut, rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, hr] at ha
  rcases ha with rfl | rfl
  · left; rw [toNat_add_ofNat (by omega)]; rfl
  · right; rw [toNat_add_ofNat (by omega)]

/-- **`BaseM` across a call from the stack pointer** writing at most words of the frame below the saved registers'
    slots. -/
theorem BaseM.call {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hf : env.Frame (top + 18446744073709551424#64) out M m1)
    (hout : ∀ b, out b → top.toNat - 192 ≤ b.toNat ∧ b.toNat + 8 ≤ top.toNat - 96) (hc : m1.code = M.code)
    (hs : env.Static m1) : BaseM env ret top regs m m1 := by
  obtain ⟨hF, hcM, -, hSv⟩ := hB
  have hsp : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by tn
  have hsl : ∀ c : Nat, 0 < c → c ≤ 96 → m1.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) =
      M.getMem (top + BitVec.ofNat 64 (2 ^ 64 - c)) := fun c hc0 hc1 => by
    have e : (top + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = top.toNat - c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := top.isLt; omega
    exact hf.getMem_above (by rw [hsp]; omega) (by rw [e, hsp]; omega) fun h => by
      have := hout _ h; rw [e] at this; omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hSv
  refine ⟨Env.Frame.trans hF hf (by rw [hsp]; omega) fun b hb => Or.inl ⟨by have := hout b hb; omega,
    by have := hout b hb; omega⟩, hc.trans hcM, hs, ?_⟩
  exact ⟨(hsl 8 (by omega) (by omega)).trans h1, (hsl 16 (by omega) (by omega)).trans h2,
    (hsl 24 (by omega) (by omega)).trans h3, (hsl 32 (by omega) (by omega)).trans h4,
    (hsl 40 (by omega) (by omega)).trans h5, (hsl 48 (by omega) (by omega)).trans h6,
    (hsl 56 (by omega) (by omega)).trans h7, (hsl 64 (by omega) (by omega)).trans h8,
    (hsl 72 (by omega) (by omega)).trans h9, (hsl 80 (by omega) (by omega)).trans h10,
    (hsl 88 (by omega) (by omega)).trans h11, (hsl 96 (by omega) (by omega)).trans h12⟩

/-- **The two vectors and `BaseM` across `grow_one` of `log_inv_rates`** (the header at `sp + 0x18`). -/
theorem grow_r {env : Env} {ret top : Word} {regs r : Reg → Word} {m M m1 : MachineState} {n : Nat}
    (hB : BaseM env ret top regs m M) (hH : Hds env top m n M) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hr : r .x10 = top + 18446744073709551448#64)
    (hf : env.Frame (top + 18446744073709551424#64) (GrowOut r M) M m1) (hc : m1.code = M.code)
    (hs : env.Static m1)
    (h16 : (M.getMem (rvCapAt (top + 18446744073709551448#64))).toNat + 1 ≤
      (m1.getMem (rvCapAt (top + 18446744073709551448#64))).toNat)
    (h17 : env.Fresh M m1 (m1.getMem (rvPtrAt (top + 18446744073709551448#64)))
      ((m1.getMem (rvCapAt (top + 18446744073709551448#64))).toNat * 8))
    (h21 : BufT env m1 (m1.getMem (rvCapAt (top + 18446744073709551448#64)))
      (m1.getMem (rvPtrAt (top + 18446744073709551448#64))) 8)
    (h22 : (m1.getMem (rvCapAt (top + 18446744073709551448#64))).toNat * 8 < 2 ^ 63) :
    BaseM env ret top regs m m1 ∧ Hds env top m n m1 ∧ n < (m1.getMem (top + 18446744073709551448#64)).toNat := by
  have e : (top + 18446744073709551448#64).toNat = top.toNat - 168 := by tn
  have ho := fun b (h : GrowOut r M b) => growOut_at hr (by omega) h
  have hk : ∀ a : Word, top.toNat - 192 ≤ a.toNat → a.toNat ≠ top.toNat - 168 → a.toNat ≠ top.toNat - 160 →
      m1.getMem a = M.getMem a := fun a h1 h2 h3 =>
    hf.getMem_above (by tn) (by rw [show (top + 18446744073709551424#64).toNat = top.toNat - 192 by tn]; omega)
      fun h => by have := ho a h; omega
  have hnM := hB.1.1
  obtain ⟨h1, h2⟩ := hH.2.grown (hdr_r top).1 (hdr_r top).2 h16 h17 h21 h22 (hk _ (by tn) (by tn) (by tn)) hnM
  exact ⟨hB.call hlim hf (fun b h => by have := ho b h; omega) hc hs, ⟨hH.1.keep (hk _ (by tn) (by tn) (by tn))
    (hk _ (by tn) (by tn) (by tn)) (hk _ (by tn) (by tn) (by tn)) hf.1, h1⟩, h2⟩

/-- **The two vectors and `BaseM` across `grow_one` of `folds`** (the header at `sp`). -/
theorem grow_f {env : Env} {ret top : Word} {regs r : Reg → Word} {m M m1 : MachineState} {nf nr : Nat}
    (hB : BaseM env ret top regs m M)
    (hHf : Hd env m (top + 18446744073709551424#64) (top + 18446744073709551432#64) (top + 18446744073709551440#64)
      nf M)
    (hHr : Hd env m (top + 18446744073709551448#64) (top + 18446744073709551456#64) (top + 18446744073709551464#64)
      nr M)
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hr : r .x10 = top + 18446744073709551424#64)
    (hf : env.Frame (top + 18446744073709551424#64) (GrowOut r M) M m1) (hc : m1.code = M.code)
    (hs : env.Static m1)
    (h16 : (M.getMem (rvCapAt (top + 18446744073709551424#64))).toNat + 1 ≤
      (m1.getMem (rvCapAt (top + 18446744073709551424#64))).toNat)
    (h17 : env.Fresh M m1 (m1.getMem (rvPtrAt (top + 18446744073709551424#64)))
      ((m1.getMem (rvCapAt (top + 18446744073709551424#64))).toNat * 8))
    (h21 : BufT env m1 (m1.getMem (rvCapAt (top + 18446744073709551424#64)))
      (m1.getMem (rvPtrAt (top + 18446744073709551424#64))) 8)
    (h22 : (m1.getMem (rvCapAt (top + 18446744073709551424#64))).toNat * 8 < 2 ^ 63) :
    BaseM env ret top regs m m1 ∧
      Hd env m (top + 18446744073709551424#64) (top + 18446744073709551432#64) (top + 18446744073709551440#64) nf m1 ∧
      nf < (m1.getMem (top + 18446744073709551424#64)).toNat ∧
      Hd env m (top + 18446744073709551448#64) (top + 18446744073709551456#64) (top + 18446744073709551464#64) nr m1 ∧
      m1.getMem (top + 18446744073709551456#64) = M.getMem (top + 18446744073709551456#64) := by
  have e : (top + 18446744073709551424#64).toNat = top.toNat - 192 := by tn
  have ho := fun b (h : GrowOut r M b) => growOut_at hr (by omega) h
  have hk : ∀ a : Word, top.toNat - 192 ≤ a.toNat → a.toNat ≠ top.toNat - 192 → a.toNat ≠ top.toNat - 184 →
      m1.getMem a = M.getMem a := fun a h1 h2 h3 =>
    hf.getMem_above (by tn) (by rw [e]; omega) fun h => by have := ho a h; omega
  have hnM := hB.1.1
  obtain ⟨h1, h2⟩ := hHf.grown (hdr_f top).1 (hdr_f top).2 h16 h17 h21 h22 (hk _ (by tn) (by tn) (by tn)) hnM
  exact ⟨hB.call hlim hf (fun b h => by have := ho b h; omega) hc hs, h1, h2,
    hHr.keep (hk _ (by tn) (by tn) (by tn)) (hk _ (by tn) (by tn) (by tn)) (hk _ (by tn) (by tn) (by tn)) hf.1,
    hk _ (by tn) (by tn) (by tn)⟩

/-- A word of the stack is not one of the heap. -/
theorem heap_ne {env : Env} {x a : Word} (hx : env.stackLimit.toNat ≤ x.toNat) (ha : a.toNat < env.heapEnd.toNat) :
    x ≠ a := fun e => by have := env.layout; rw [e] at hx; omega

/-- Two offsets from one base. -/
theorem ne_off {t c d : Word} (h : c ≠ d) : t + c ≠ t + d := fun e => h ((BitVec.add_right_inj t).1 e)

set_option rv_sym.heap true in
/-- The loop's head: the two last elements read, `log_inv_rates` grown if full. -/
theorem head_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG : Nat} (hnG : 192 + needG ≤ need) (hgo : GrowOneSpecT env 8 8 p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {qp ql c : Word} {k : Nat} :
    ∀ R M, LInv env ret top regs m qp ql c k R M →
      (∀ j R M, AInv env ret top regs m qp ql c j k R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 188, ret, top⟩ :: rest, R, M⟩) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 168, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv hA
  obtain ⟨j, hcj, hinv⟩ := hinv
  have hBM := hinv.2.2.2.2.1
  have hHf := hinv.2.2.2.2.2.1.1
  have hHr := hinv.2.2.2.2.2.1.2
  have hQ := hinv.2.2.2.2.2.2
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  obtain ⟨hbf, hcf, hlf, hnf, hpf⟩ := id hHf
  obtain ⟨hbr, hcr, hlr, hnr, hpr⟩ := id hHr
  have hnM := hBM.1.2.1
  obtain ⟨hpf0, hpfl, hpfa⟩ := hbf.resolve_left (by omega)
  obtain ⟨hpr0, hprl, hpra⟩ := hbr.resolve_left (by omega)
  unfold Env.Live at hpfl hprl
  have hj8 : (BitVec.ofNat 64 (8 * j)).toNat = 8 * j := by rw [BitVec.toNat_ofNat]; omega
  have hA1 : (M.getMem (top + 18446744073709551456#64) + BitVec.ofNat 64 (8 * j) + 8#64).toNat =
      (M.getMem (top + 18446744073709551456#64)).toNat + 8 * j + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hj8]; simp only [BitVec.toNat_ofNat]; omega
  have hA2 : (M.getMem (top + 18446744073709551432#64) + BitVec.ofNat 64 (8 * j) + 8#64).toNat =
      (M.getMem (top + 18446744073709551432#64)).toNat + 8 * j + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hj8]; simp only [BitVec.toNat_ofNat]; omega
  rv_introT hinv
  clear hinv_28 hinv_33 hinv_38 hbf hbr
  rv_symT hp stop [188] with [hL, hlim] using [hgo]
  -- room: on to the next element
  · have hne : j + 2 ≠ (M.getMem (top + 18446744073709551448#64)).toNat := fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ofNat, h]; exact Nat.mod_eq_of_lt (M.getMem _).isLt))
    exact hA j _ _ ⟨hcj, ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩,
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩, by rv_closeT, hBM, ⟨hHf, hHr⟩,
      by omega, hQ⟩
  -- full: `grow_one`'s precondition
  iterate 4
    · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, (hdr_r top).1, (hdr_r top).2]
      first
        | exact hcr
        | exact .inr ⟨hpr0, by unfold Env.Live; omega, hpra⟩
        | exact .inr (by unfold Env.Live; omega)
  -- grown
  · obtain ⟨hB1, hH1, hroom⟩ := grow_r hBM ⟨hHf, hHr⟩ hlim rfl hret1_14 hret1_23 hret1_15 hret1_16 hret1_17 hret1_21
      hret1_22
    exact hA j _ _ ⟨hcj, ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩,
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩, by rv_closeT, hB1, hH1, hroom, hQ⟩

/-- `BaseM` across a store into memory allocated since the entry. -/
theorem BaseM.heap {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat < (env.next M).toNat) :
    BaseM env ret top regs m (M.setMem a v) := by
  have hlay := env.layout
  have hnM := hB.1.2.1
  exact ⟨Tactic.frame_fresh hB.1 rfl hlo hhi, by rw [MachineState.code_setMem]; exact hB.2.1,
    Env.static_setMem hB.2.2.1 (.inl (by omega)), hB.2.2.2.setMem (by omega) (.inl (by omega))⟩

/-- `BaseM` across a store into the frame below the saved registers' slots. -/
theorem BaseM.stk {env : Env} {ret top a v : Word} {regs : Reg → Word} {m M : MachineState}
    (hB : BaseM env ret top regs m M) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (ha : top.toNat - 192 ≤ a.toNat) (ha' : a.toNat + 8 ≤ top.toNat - 96) : BaseM env ret top regs m (M.setMem a v) :=
  ⟨Tactic.frame_store hB.1 (by omega) (by omega), by rw [MachineState.code_setMem]; exact hB.2.1,
    Env.static_setMem_stack hB.2.2.1 (by omega), hB.2.2.2.setMem (by omega) (.inl ha')⟩

/-- A header in the frame across a store into the heap. -/
theorem Hd.heap {env : Env} {m M : MachineState} {ac ap al a v : Word} {n : Nat} (hH : Hd env m ac ap al n M)
    (hc : env.stackLimit.toNat ≤ ac.toNat) (hp : env.stackLimit.toNat ≤ ap.toNat)
    (hl : env.stackLimit.toNat ≤ al.toNat) (ha : a.toNat < env.heapEnd.toNat) : Hd env m ac ap al n (M.setMem a v) := by
  have hlay := env.layout
  have ne := fun (x : Word) (h : env.stackLimit.toNat ≤ x.toNat) =>
    (MachineState.getMem_setMem_ne (s := M) (v := v) (a := a) (a' := x) fun e => by rw [e] at h; omega)
  exact hH.keep (ne _ hc) (ne _ hp) (ne _ hl) (by
    rw [Tactic.next_setMem (fun e => by rw [e] at ha; omega)])

/-- A header in the frame across a store into another word of the stack. -/
theorem Hd.stk {env : Env} {m M : MachineState} {ac ap al a v : Word} {n : Nat} (hH : Hd env m ac ap al n M)
    (hc : ac ≠ a) (hp : ap ≠ a) (hl : al ≠ a) (ha : env.stackLimit.toNat ≤ a.toNat) :
    Hd env m ac ap al n (M.setMem a v) :=
  hH.keep (MachineState.getMem_setMem_ne hc) (MachineState.getMem_setMem_ne hp) (MachineState.getMem_setMem_ne hl)
    (by rw [Env.next_setMem_stack ha])

/-- A header whose length is raised to `n'`, within its capacity. -/
theorem Hd.len {env : Env} {m M : MachineState} {ac ap al : Word} {n n' : Nat} (hH : Hd env m ac ap al n M)
    (hc : ac ≠ al) (hp : ap ≠ al) (ha : env.stackLimit.toNat ≤ al.toNat) (hn : n' ≤ (M.getMem ac).toNat) :
    Hd env m ac ap al n' (M.setMem al (BitVec.ofNat 64 n')) := by
  obtain ⟨hb, hcc, -, -, hpp⟩ := hH
  have e1 := MachineState.getMem_setMem_ne (s := M) (v := BitVec.ofNat 64 n') hc
  have e2 := MachineState.getMem_setMem_ne (s := M) (v := BitVec.ofNat 64 n') hp
  refine ⟨by rw [e1, e2]; exact hb.mono (by rw [Env.next_setMem_stack ha]), by rw [e1]; exact hcc,
    MachineState.getMem_setMem_eq, by rw [e1]; exact hn, by rw [e2]; exact hpp⟩

/-- After `log_inv_rates`' element (instruction 152): `log_inv_rates` of length `j + 3`, `folds` of `j + 2` with
    room, `x23 = j + 3`. -/
def BInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (qp ql c : Word) (j k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  c.toNat = j + 1 + k ∧ BaseR top regs qp ql R ∧ LoopR c j R ∧ R .x23 = BitVec.ofNat 64 (j + 3) ∧
    R .x19 = M.getMem (top + 18446744073709551456#64) ∧ BaseM env ret top regs m M ∧
    Hd env m (top + 18446744073709551424#64) (top + 18446744073709551432#64) (top + 18446744073709551440#64) (j + 2) M ∧
    j + 2 < (M.getMem (top + 18446744073709551424#64)).toNat ∧
    Hd env m (top + 18446744073709551448#64) (top + 18446744073709551456#64) (top + 18446744073709551464#64) (j + 3) M ∧
    QueriesOk env (regs .x11).toNat (regs .x12).toNat qp ql

set_option rv_sym.heap true in
/-- `log_inv_rates`' next element, its length, `folds` grown if full. -/
theorem a_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG : Nat} (hnG : 192 + needG ≤ need) (hgo : GrowOneSpecT env 8 8 p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {qp ql c : Word} {j k : Nat} :
    ∀ R M, AInv env ret top regs m qp ql c j k R M →
      (∀ R M, BInv env ret top regs m qp ql c j k R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 152, ret, top⟩ :: rest, R, M⟩) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 188, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv hB
  obtain ⟨hcj, -, -, -, hBM, ⟨hHf, hHr⟩, hroom, hQ⟩ := id hinv
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  have hlay := env.layout
  obtain ⟨hbf, hcf, hlf, hnf, hpf⟩ := id hHf
  obtain ⟨hbr, hcr, hlr, hnr, hpr⟩ := id hHr
  have hnM := hBM.1.2.1
  have hnM0 := hBM.1.1
  obtain ⟨hpf0, hpfl, hpfa⟩ := hbf.resolve_left (by omega)
  obtain ⟨hpr0, hprl, hpra⟩ := hbr.resolve_left (by omega)
  unfold Env.Live at hpfl hprl
  have hj8 : (BitVec.ofNat 64 (8 * j)).toNat = 8 * j := by rw [BitVec.toNat_ofNat]; omega
  have hA1 : (M.getMem (top + 18446744073709551456#64) + BitVec.ofNat 64 (8 * j) + 16#64).toNat =
      (M.getMem (top + 18446744073709551456#64)).toNat + 8 * j + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hj8]; simp only [BitVec.toNat_ofNat]; omega
  have hj3 : BitVec.ofNat 64 (j + 2) + 1#64 = BitVec.ofNat 64 (j + 3) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rv_introT hinv
  clear hinv_28 hinv_33 hinv_39 hbf hbr
  have hhp : (env.next m).toNat ≤ (M.getMem (top + 18446744073709551456#64) + BitVec.ofNat 64 (8 * j) + 16#64).toNat ∧
      (M.getMem (top + 18446744073709551456#64) + BitVec.ofNat 64 (8 * j) + 16#64).toNat < (env.next M).toNat := by
    rw [hA1]; omega
  have hha : (M.getMem (top + 18446744073709551456#64) + BitVec.ofNat 64 (8 * j) + 16#64).toNat <
      env.heapEnd.toNat := by omega
  have hB2 := (hBM.heap (v := R .x23 + R .x26 + 18446744073709551615#64) hlim hhp.1 hhp.2).stk
    (v := BitVec.ofNat 64 (j + 3)) (a := top + 18446744073709551464#64) hlim (by tn) (by tn)
  have hHf2 := (hHf.heap (v := R .x23 + R .x26 + 18446744073709551615#64) (by tn) (by tn) (by tn)
    hha).stk (a := top + 18446744073709551464#64) (v := BitVec.ofNat 64 (j + 3)) (ne_off (by decide))
    (ne_off (by decide)) (ne_off (by decide)) (by tn)
  have hHr2 := (hHr.heap (v := R .x23 + R .x26 + 18446744073709551615#64) (by tn) (by tn) (by tn) hha).len
    (n' := j + 3) (ne_off (by decide)) (ne_off (by decide)) (by tn) (by
      rw [MachineState.getMem_setMem_ne (heap_ne (x := top + 18446744073709551448#64) (by tn) hha)]
      omega)
  have rd2 : ∀ c : Word, c ≠ 18446744073709551464#64 → env.stackLimit.toNat ≤ (top + c).toNat →
      ((M.setMem (M.getMem (top + 18446744073709551456#64) + BitVec.ofNat 64 (8 * j) + 16#64)
        (R .x23 + R .x26 + 18446744073709551615#64)).setMem (top + 18446744073709551464#64)
        (BitVec.ofNat 64 (j + 3))).getMem (top + c) = M.getMem (top + c) := fun c h1 h2 => by
    rw [MachineState.getMem_setMem_ne (ne_off h1), MachineState.getMem_setMem_ne (heap_ne h2 hha)]
  rv_symT hp stop [152] with [hL, hlim] using [hgo]
  all_goals simp only [hj3] at *
  -- room: on to `folds`' element
  · have hne : j + 2 ≠ (M.getMem (top + 18446744073709551424#64)).toNat := fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ofNat, h]; exact Nat.mod_eq_of_lt (M.getMem _).isLt))
    refine hB _ _ ⟨hcj, ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩,
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩, by rv_closeT, ?_, hB2, hHf2, ?_, hHr2,
      hQ⟩
    · simp only [Tactic.rf]; rw [rd2 _ (by decide) (by tn)]
    · rw [rd2 _ (by decide) (by tn)]; omega
  -- full: `grow_one`'s precondition
  iterate 4
    · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, (hdr_f top).1, (hdr_f top).2]
      first
        | exact hHf2.2.1
        | exact hHf2.1
        | exact hHf2.1.live
  -- grown
  · obtain ⟨hB1, hHf1, hroom, hHr1, hk19⟩ := grow_f hB2 hHf2 hHr2 hlim rfl hret1_14 hret1_23 hret1_15 hret1_16
      hret1_17 hret1_21 hret1_22
    refine hB _ _ ⟨hcj, ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩,
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩, by rv_closeT, ?_, hB1, hHf1, hroom, hHr1,
      hQ⟩
    simp only [Tactic.rf]; rw [hk19, rd2 _ (by decide) (by tn)]

/-- The loop's exit test: `-c + (j + 3) = 2` only when no pass is left. -/
theorem cnt_left {c : Word} {j k : Nat} (h : c.toNat = j + 1 + k) (hc : ¬ (0#64 - c + BitVec.ofNat 64 (j + 3) = 2#64)) :
    k ≠ 0 := fun hk => hc (BitVec.eq_of_toNat_eq (by
  have := c.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega))

set_option rv_sym.heap true in
/-- `folds`' next element and length, then the exit test: back to the head or on to the end. -/
theorem b_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 192 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {qp ql c : Word} {j k : Nat}
    (hX : ∀ R M, XInv env ret top regs m qp ql (j + 3) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 212, ret, top⟩ :: rest, R, M⟩)
    (ih : ∀ k' R M, k' < k → LInv env ret top regs m qp ql c k' R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 168, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, BInv env ret top regs m qp ql c j k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 152, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨hcj, -, -, -, -, hBM, hHf, hroom, hHr, hQ⟩ := id hinv
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  have hlay := env.layout
  obtain ⟨hbf, hcf, hlf, hnf, hpf⟩ := id hHf
  have hnM := hBM.1.2.1
  obtain ⟨hpf0, hpfl, hpfa⟩ := hbf.resolve_left (by omega)
  unfold Env.Live at hpfl
  have hj8 : (BitVec.ofNat 64 (8 * j)).toNat = 8 * j := by rw [BitVec.toNat_ofNat]; omega
  have hA1 : (M.getMem (top + 18446744073709551432#64) + BitVec.ofNat 64 (8 * j) + 16#64).toNat =
      (M.getMem (top + 18446744073709551432#64)).toNat + 8 * j + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hj8]; simp only [BitVec.toNat_ofNat]; omega
  have hha : (M.getMem (top + 18446744073709551432#64) + BitVec.ofNat 64 (8 * j) + 16#64).toNat <
      env.heapEnd.toNat := by omega
  have hhp : (env.next m).toNat ≤ (M.getMem (top + 18446744073709551432#64) + BitVec.ofNat 64 (8 * j) + 16#64).toNat ∧
      (M.getMem (top + 18446744073709551432#64) + BitVec.ofNat 64 (8 * j) + 16#64).toNat < (env.next M).toNat := by
    rw [hA1]; omega
  have hB3 := ((hBM.stk (v := BitVec.ofNat 64 (j + 3)) (a := top + 18446744073709551440#64) hlim (by tn) (by tn)).heap
    (v := 4#64) hlim hhp.1 (by rw [Env.next_setMem_stack (by tn)]; exact hhp.2))
  have hHf3 := (hHf.len (n' := j + 3) (ne_off (by decide)) (ne_off (by decide)) (by tn) (by omega)).heap
    (v := 4#64) (by tn) (by tn) (by tn) hha
  have hHr3 := (hHr.stk (a := top + 18446744073709551440#64) (v := BitVec.ofNat 64 (j + 3)) (ne_off (by decide))
    (ne_off (by decide)) (ne_off (by decide)) (by tn)).heap (v := 4#64) (by tn) (by tn) (by tn) hha
  have rd2 : ∀ c : Word, c ≠ 18446744073709551440#64 → env.stackLimit.toNat ≤ (top + c).toNat →
      ((M.setMem (top + 18446744073709551440#64) (BitVec.ofNat 64 (j + 3))).setMem
        (M.getMem (top + 18446744073709551432#64) + BitVec.ofNat 64 (8 * j) + 16#64) 4#64).getMem (top + c) =
        M.getMem (top + c) := fun c h1 h2 => by
    rw [MachineState.getMem_setMem_ne (heap_ne h2 hha), MachineState.getMem_setMem_ne (ne_off h1)]
  rv_introT hinv
  clear hinv_29 hinv_35 hinv_40 hbf
  rv_symT hp stop [168, 212] with [hlim]
  -- the ladder's end
  · exact hX _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, hB3,
      ⟨hHf3, hHr3⟩, hQ⟩
  -- back to the head
  · have hk := cnt_left hcj hc
    have h8 : BitVec.ofNat 64 (8 * j) + 8#64 = BitVec.ofNat 64 (8 * (j + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ih (k - 1) _ _ (by omega) ⟨j + 1, by omega,
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩,
      ⟨by rv_closeT, ?_, by rv_closeT, by rv_closeT, by rv_closeT⟩, ?_, ?_, hB3, ⟨hHf3, hHr3⟩, hQ⟩
    · simp only [Tactic.rf]; exact h8
    · simp only [Tactic.rf]; rw [rd2 _ (by decide) (by tn)]
    · simp only [Tactic.rf]; rw [rd2 _ (by decide) (by tn)]

/-- **The ladder's loop**, from its head: `Total.loop` with the passes left as the measure. -/
theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG : Nat} (hnG : 192 + needG ≤ need) (hgo : GrowOneSpecT env 8 8 p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {qp ql c : Word}
    (hX : ∀ n R M, XInv env ret top regs m qp ql n R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 212, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, LInv env ret top regs m qp ql c k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 168, ret, top⟩ :: rest, R, M⟩ :=
  Total.loop (I := rvIsa) (LInv env ret top regs m qp ql c) fun _ R M hI ih =>
    head_ok env p i L hp hL hnG hgo hstop hstk hal hW R M hI fun _ R M hA =>
      a_ok env p i L hp hL hnG hgo hstop hstk hal hW R M hA
        (b_ok env p i L hp hstk (by omega) hal hW (hX _) ih)

/-- The first pass, after `log_inv_rates` has room (instruction 114): both vectors of length `1`, `x20 = log_n - 12`,
    `x21 = 1`. -/
def E2Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (qp ql : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  BaseR top regs qp ql R ∧ R .x19 = M.getMem (top + 18446744073709551456#64) ∧
    R .x20 = regs .x11 + 18446744073709551604#64 ∧ R .x21 = 1#64 ∧ BaseM env ret top regs m M ∧ Hds env top m 1 M ∧
    1 < (M.getMem (top + 18446744073709551448#64)).toNat ∧ QueriesOk env (regs .x11).toNat (regs .x12).toNat qp ql

/-- The first pass, after `folds` has room (instruction 132): `log_inv_rates` of length `2`, `folds` of `1`, the
    passes' count `(log_n - 12) >> 2` in `x22`. -/
def E3Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (qp ql : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  BaseR top regs qp ql R ∧ R .x19 = M.getMem (top + 18446744073709551456#64) ∧
    R .x22 = (regs .x11 + 18446744073709551604#64) >>> 2 ∧ R .x23 = 2#64 ∧ BaseM env ret top regs m M ∧
    Hd env m (top + 18446744073709551424#64) (top + 18446744073709551432#64) (top + 18446744073709551440#64) 1 M ∧
    1 < (M.getMem (top + 18446744073709551424#64)).toNat ∧
    Hd env m (top + 18446744073709551448#64) (top + 18446744073709551456#64) (top + 18446744073709551464#64) 2 M ∧
    QueriesOk env (regs .x11).toNat (regs .x12).toNat qp ql

set_option rv_sym.heap true in
/-- The first pass: `log_inv_rates`' second element and length, `folds` grown if full. -/
theorem e2_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG : Nat} (hnG : 192 + needG ≤ need) (hgo : GrowOneSpecT env 8 8 p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {qp ql : Word}
    (hE : ∀ R M, E3Inv env ret top regs m qp ql R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 132, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, E2Inv env ret top regs m qp ql R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, -, hBM, ⟨hHf, hHr⟩, hroom, hQ⟩ := id hinv
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  have hlay := env.layout
  obtain ⟨hbr, hcr, hlr, hnr, hpr⟩ := id hHr
  have hnM := hBM.1.2.1
  obtain ⟨hpr0, hprl, hpra⟩ := hbr.resolve_left (by omega)
  unfold Env.Live at hprl
  have hA1 : (M.getMem (top + 18446744073709551456#64) + 8#64).toNat =
      (M.getMem (top + 18446744073709551456#64)).toNat + 8 := toNat_add_ofNat (by omega)
  have hha : (M.getMem (top + 18446744073709551456#64) + 8#64).toNat < env.heapEnd.toNat := by omega
  have hhp : (env.next m).toNat ≤ (M.getMem (top + 18446744073709551456#64) + 8#64).toNat ∧
      (M.getMem (top + 18446744073709551456#64) + 8#64).toNat < (env.next M).toNat := by
    rw [hA1]; omega
  have hB2 := (hBM.heap (v := R .x22) hlim hhp.1 hhp.2).stk
    (v := 2#64) (a := top + 18446744073709551464#64) hlim (by tn) (by tn)
  have hHf2 := (hHf.heap (v := R .x22) (by tn) (by tn) (by tn) hha).stk (a := top + 18446744073709551464#64)
    (v := 2#64) (ne_off (by decide)) (ne_off (by decide)) (ne_off (by decide)) (by tn)
  have hHr2 := (hHr.heap (v := R .x22) (by tn) (by tn) (by tn) hha).len (n' := 2) (ne_off (by decide))
    (ne_off (by decide)) (by tn) (by
      rw [MachineState.getMem_setMem_ne (heap_ne (x := top + 18446744073709551448#64) (by tn) hha)]
      omega)
  have rd2 : ∀ c : Word, c ≠ 18446744073709551464#64 → env.stackLimit.toNat ≤ (top + c).toNat →
      ((M.setMem (M.getMem (top + 18446744073709551456#64) + 8#64) (R .x22)).setMem (top + 18446744073709551464#64)
        2#64).getMem (top + c) = M.getMem (top + c) := fun c h1 h2 => by
    rw [MachineState.getMem_setMem_ne (ne_off h1), MachineState.getMem_setMem_ne (heap_ne h2 hha)]
  have hnf := hHf.2.2.2.1
  rv_introT hinv
  clear hinv_24 hinv_29 hinv_35 hbr
  rv_symT hp stop [132] with [hL, hlim] using [hgo]
  -- room
  · have hne : 1 ≠ (M.getMem (top + 18446744073709551424#64)).toNat := fun h => hc (BitVec.eq_of_toNat_eq h.symm)
    refine hE _ _ ⟨⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩, ?_, by rv_closeT,
      by rv_closeT, hB2, hHf2, ?_, hHr2, hQ⟩
    · simp only [Tactic.rf]; rw [rd2 _ (by decide) (by tn)]
    · rw [rd2 _ (by decide) (by tn)]; omega
  -- full: `grow_one`'s precondition
  iterate 4
    · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, (hdr_f top).1, (hdr_f top).2]
      first
        | exact hHf2.2.1
        | exact hHf2.1
        | exact hHf2.1.live
  -- grown
  · obtain ⟨hB1, hHf1, hroom, hHr1, hk19⟩ := grow_f hB2 hHf2 hHr2 hlim rfl hret1_14 hret1_23 hret1_15 hret1_16
      hret1_17 hret1_21 hret1_22
    refine hE _ _ ⟨⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩, ?_, by rv_closeT,
      by rv_closeT, hB1, hHf1, hroom, hHr1, hQ⟩
    simp only [Tactic.rf]; rw [hk19, rd2 _ (by decide) (by tn)]

set_option rv_sym.heap true in
/-- The first pass: `folds`' second element and length, then the passes' count: none, or on to the loop's head. -/
theorem e3_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 192 ≤ need)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {qp ql : Word}
    (hX : ∀ R M, XInv env ret top regs m qp ql 2 R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 212, ret, top⟩ :: rest, R, M⟩)
    (hLp : ∀ k R M, LInv env ret top regs m qp ql ((regs .x11 + 18446744073709551604#64) >>> 2) k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 168, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, E3Inv env ret top regs m qp ql R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 132, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, -, hBM, hHf, hroom, hHr, hQ⟩ := id hinv
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  have hlay := env.layout
  obtain ⟨hbf, hcf, hlf, hnf, hpf⟩ := id hHf
  have hnM := hBM.1.2.1
  obtain ⟨hpf0, hpfl, hpfa⟩ := hbf.resolve_left (by omega)
  unfold Env.Live at hpfl
  have hA1 : (M.getMem (top + 18446744073709551432#64) + 8#64).toNat =
      (M.getMem (top + 18446744073709551432#64)).toNat + 8 := toNat_add_ofNat (by omega)
  have hha : (M.getMem (top + 18446744073709551432#64) + 8#64).toNat < env.heapEnd.toNat := by omega
  have hhp : (env.next m).toNat ≤ (M.getMem (top + 18446744073709551432#64) + 8#64).toNat ∧
      (M.getMem (top + 18446744073709551432#64) + 8#64).toNat < (env.next M).toNat := by
    rw [hA1]; omega
  have hB3 := (hBM.heap (v := 4#64) hlim hhp.1 hhp.2).stk (v := 2#64) (a := top + 18446744073709551440#64) hlim
    (by tn) (by tn)
  have hHf3 := (hHf.heap (v := 4#64) (by tn) (by tn) (by tn) hha).len (n' := 2) (ne_off (by decide))
    (ne_off (by decide)) (by tn) (by
      rw [MachineState.getMem_setMem_ne (heap_ne (x := top + 18446744073709551424#64) (by tn) hha)]
      omega)
  have hHr3 := (hHr.heap (v := 4#64) (by tn) (by tn) (by tn) hha).stk (a := top + 18446744073709551440#64)
    (v := 2#64) (ne_off (by decide)) (ne_off (by decide)) (ne_off (by decide)) (by tn)
  have rd2 : ∀ c : Word, c ≠ 18446744073709551440#64 → env.stackLimit.toNat ≤ (top + c).toNat →
      ((M.setMem (M.getMem (top + 18446744073709551432#64) + 8#64) 4#64).setMem (top + 18446744073709551440#64)
        2#64).getMem (top + c) = M.getMem (top + c) := fun c h1 h2 => by
    rw [MachineState.getMem_setMem_ne (ne_off h1), MachineState.getMem_setMem_ne (heap_ne h2 hha)]
  rv_introT hinv
  clear hinv_24 hinv_30 hinv_35 hbf
  rv_symT hp stop [168, 212] with [hlim]
  -- no further pass
  · exact hX _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, hB3,
      ⟨hHf3, hHr3⟩, hQ⟩
  -- the loop
  · have hc0 : ((regs .x11 + 18446744073709551604#64) >>> 2).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    refine hLp (((regs .x11 + 18446744073709551604#64) >>> 2).toNat - 1) _ _ ⟨0, by omega,
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩,
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩, ?_, ?_, hB3, ⟨hHf3, hHr3⟩, hQ⟩
    · simp only [Tactic.rf]; rw [rd2 _ (by decide) (by tn)]
    · simp only [Tactic.rf]; rw [rd2 _ (by decide) (by tn)]

/-- At the first pass' `grow_one` of `log_inv_rates` (instruction 111): both vectors of length and capacity `1`, the
    call's arguments. -/
def G0Inv (env : Env) (L : Link) (ret top : Word) (regs : Reg → Word) (m : MachineState) (qp ql : Word)
    (R : Reg → Word) (M : MachineState) : Prop :=
  BaseR top regs qp ql R ∧ R .x1 = L.s3.hi ∧ R .x10 = top + 18446744073709551448#64 ∧
    R .x20 = regs .x11 + 18446744073709551604#64 ∧ R .x21 = 1#64 ∧ BaseM env ret top regs m M ∧ Hds env top m 1 M ∧
    QueriesOk env (regs .x11).toNat (regs .x12).toNat qp ql

set_option rv_sym.heap true in
/-- The first pass: `log_inv_rates` grown (it is full). -/
theorem g0_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needG : Nat} (hnG : 192 + needG ≤ need) (hgo : GrowOneSpecT env 8 8 p L.growOne.idx needG)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {qp ql : Word}
    (hE : ∀ R M, E2Inv env ret top regs m qp ql R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 114, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, G0Inv env L ret top regs m qp ql R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 111, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, -, -, -, -, hBM, ⟨hHf, hHr⟩, hQ⟩ := id hinv
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  obtain ⟨hbr, hcr, hlr, hnr, hpr⟩ := id hHr
  have hnM := hBM.1.2.1
  obtain ⟨hpr0, hprl, hpra⟩ := hbr.resolve_left (by omega)
  unfold Env.Live at hprl
  rv_introT hinv
  rv_symT hp stop [114] with [hL, hlim] using [hgo]
  iterate 4
    · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, (hdr_r top).1, (hdr_r top).2]
      first
        | exact hcr
        | exact .inr ⟨hpr0, by unfold Env.Live; omega, hpra⟩
        | exact .inr (by unfold Env.Live; omega)
  · obtain ⟨hB1, hH1, hroom⟩ := grow_r hBM ⟨hHf, hHr⟩ hlim rfl hret1_14 hret1_23 hret1_15 hret1_16 hret1_17 hret1_21
      hret1_22
    exact hE _ _ ⟨⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩, by rv_closeT,
      by rv_closeT, by rv_closeT, hB1, hH1, hroom, hQ⟩

/-- A header naming a block of one element that `alloc` returned since the entry, of length `1`. -/
theorem hd_of {env : Env} {m M : MachineState} {ac ap al ptr : Word} (h1 : M.getMem ac = 1#64) (h2 : M.getMem ap = ptr)
    (h3 : M.getMem al = 1#64) (hlo : (env.next m).toNat ≤ ptr.toNat) (hhi : ptr.toNat + 8 ≤ (env.next M).toNat)
    (hal : ptr.toNat % 8 = 0) (hge : 0x10000000 ≤ (env.next m).toNat) : Hd env m ac ap al 1 M :=
  ⟨by rw [h1, h2]; exact .inr ⟨by omega, by unfold Env.Live; simpa using hhi, hal⟩, by rw [h1]; decide,
    by rw [h3], by rw [h1]; decide, by rw [h2]; exact hlo⟩

/-- The queries `whir_queries` returned: not `None`, so the tabulated counts. -/
theorem queriesOk_of {env : Env} {regs r : Reg → Word}
    (h : match Model.whirQueriesRust (regs .x11).toNat (regs .x12).toNat with
      | none => r .x10 = 0#64
      | some qs => WhirQueries.SliceRet env r qs) (h0 : ¬ r .x10 = 0#64) :
    QueriesOk env (regs .x11).toNat (regs .x12).toNat (r .x10) (r .x11) := by
  revert h
  cases hq : Model.whirQueriesRust (regs .x11).toNat (regs .x12).toNat with
  | none => exact fun h => absurd h h0
  | some qs => exact fun h => ⟨qs, hq, h.2.1, h.2.2⟩

set_option rv_sym.heap true in
/-- **`derive_config` is total**, with 192 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needQ needA needG needP : Nat} (hnQ : 192 + needQ ≤ need) (hnA : 192 + needA ≤ need)
    (hnG : 192 + needG ≤ need) (hnP : 192 + needP ≤ need)
    (hwq : WhirQueriesT.specT env p L.whirQueries.idx needQ)
    (hac : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA)
    (hgo : GrowOneSpecT env 8 8 p L.growOne.idx needG)
    (hpn : Aborts env p L.panicNounwindFmt.idx needP) : specT env p i need := by
  have hac' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hac.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [111, 212, 268] with [hL, (by omega : env.stackLimit.toNat + 192 ≤ top.toNat)]
    using [hwq, hac', hpn]
  all_goals
    have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
    have hoS : env.Owned m top (regs .x10) 64 := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
    have hwS : InWin env (regs .x10) 64 := hpre_8
    have hRet := ret_ok env p i L hp hk hpre_3 (by omega) hpre_10 hpre_11
  -- `Err(WhirShape)`
  · have hF1 : env.Frame top Tactic.F m m1 := by rv_closeT
    have hS1 : Saved ret top regs m1 := ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩
    have hRS : RS env ret top regs m m1 m1 := ⟨frame_sret hF1, hret1_15, hS1, rfl⟩
    have hlt := hwS.lt
    refine hRet _ _ (retInv_of ((hRS.sret hlim hpre_5 hwS hoS ⟨Nat.le_refl _, by omega⟩).sret hlim hpre_5 hwS
      hoS ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩) (by rv_closeT)
      (by rv_closeT) (by simp only [MachineState.code_setMem]; rv_closeT) fun _ h => absurd ?_ h)
    rw [MachineState.getMem_setMem_ne (fun he => by
      have := congrArg BitVec.toNat he; rw [toNat_add_ofNat (by omega)] at this; omega),
      MachineState.getMem_setMem_eq]
  all_goals
    have hQ := queriesOk_of hret1_16 hc_1
    have hX := fun n => exit env p i L hp hpre_3 (by omega) hpre_5 hpre_10 hpre_11 hwS hpre_9 hoS hRet
      (qp := r1 .x10) (ql := r1 .x11) (n := n)
    have hge := hpre_11.next_ge
    have h2b : (r2 .x10).toNat + 8 ≤ env.heapEnd.toNat := by
      have := hret2_14.2.1; have := hret2_18; simp only [show (8#64 : Word).toNat = 8 from rfl] at this; omega
    have h4b : (r4 .x10).toNat + 8 ≤ env.heapEnd.toNat := by
      have := hret4_14.2.1; have := hret4_18; simp only [show (8#64 : Word).toNat = 8 from rfl] at this; omega
    have n1 : (env.next m).toNat ≤ (env.next m1).toNat := by
      have := hret1_14.1
      simp (disch := (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) only [Env.next_setMem_stack] at this
      exact this
    have n2 := hret2_14.1
    have n4 : (env.next m2).toNat ≤ (env.next m4).toNat := by
      have := hret4_14.1
      simp (disch := (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) only [Env.next_setMem_stack] at this
      rwa [Tactic.next_setMem (fun e => by have := env.layout; rw [e] at h2b; omega)] at this
    have e2 := hret2_18
    have e4 := hret4_18
    simp only [show (8#64 : Word).toNat = 8 from rfl] at e2 e4
    have nc : ∀ v1 v2 v3 v4 : Word, env.next ((((m4.setMem (r4 .x10) v1).setMem (top + 18446744073709551448#64)
        v2).setMem (top + 18446744073709551456#64) v3).setMem (top + 18446744073709551464#64) v4) = env.next m4 :=
      fun v1 v2 v3 v4 => by
        simp (disch := (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) only [Env.next_setMem_stack]
        exact Tactic.next_setMem (fun e => by have := env.layout; rw [e] at h4b; omega)
  -- no ladder: both of length `1`
  · refine hX 1 _ _ ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
        by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩⟩,
      ⟨hd_of (by rv_closeT) (by rv_closeT) (by rv_closeT) ?_ ?_ ?_ hge,
        hd_of (by rv_closeT) (by rv_closeT) (by rv_closeT) ?_ ?_ ?_ hge⟩, hQ⟩
    all_goals (try rw [nc])
    all_goals omega
  -- the first pass: `log_inv_rates` full, its `grow_one`
  · have hLoop := loop env p i L hp hL hnG hgo hstop hpre_3 hpre_10 hpre_11 (qp := r1 .x10) (ql := r1 .x11)
      (c := (regs .x11 + 18446744073709551604#64) >>> 2) hX
    have hE3 := e3_ok env p i L hp hpre_3 (by omega) hpre_10 hpre_11 (hX 2) hLoop
    have hE2 := e2_ok env p i L hp hL hnG hgo hstop hpre_3 hpre_10 hpre_11 hE3
    refine g0_ok env p i L hp hL hnG hgo hstop hpre_3 hpre_10 hpre_11 hE2 _ _
      ⟨⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩, by rv_closeT, by rv_closeT,
        by rv_closeT, by rv_closeT,
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT,
        by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩⟩,
      ⟨hd_of (by rv_closeT) (by rv_closeT) (by rv_closeT) ?_ ?_ ?_ hge,
        hd_of (by rv_closeT) (by rv_closeT) (by rv_closeT) ?_ ?_ ?_ hge⟩, hQ⟩
    all_goals (try rw [nc])
    all_goals omega

end Rv64mc.Proof.Whir.DeriveConfigT

/-- info: 'Rv64mc.Proof.Whir.DeriveConfigT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.DeriveConfigT.total
