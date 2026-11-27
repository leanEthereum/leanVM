/-
  Rv64mc.Proof.Field.ScaledNewT

  The parts of a total proof of `Scaled::new(r) -> Scaled` (`specT`, not yet proved: the entry part `total` is
  missing). `specT` is a safety contract: from a result's slot of `24` bytes owned, in a window, 8-byte aligned, it
  returns with the slot a vector of `1408` `E`s (`VecT`), its buffer allocated since the entry, writing at most the
  slot besides its stack and what it allocates (the partial contract's `NewOut`), or the run ends with `a0 = 2`.

  The code allocates the tables zeroed (`from_elem`, `1408` entries at `p`, header at `top - 128`), then for each
  chunk of `704` entries (`chunks_exact_mut`, two: the end `p + 22528` at `top - 160`, from the image's division
  constant, the table `d_c8_a4f5b9af`) fills its eleven blocks of `64` entries: sixteen straight, then sixteen
  (`inner1`, entry `x6`, offset `16 x6 ||| 256`, `or256`) and thirty-two (`inner2`, offset `16 x31 ||| 512`,
  `or512`) in loops; then copies the header into the slot (`fin_ok`). The loops are `Total.loop` (`chunk`: chunks
  left; `middle`: blocks left; `inner1`, `inner2`: entries left), nested as `RingCoefficientsT`'s. Each part keeps
  `Frm`: the frame's words (`Hdr`), `SavedT.MemOk` with the thirteen saved registers' slots (`Mem`) and the chunk's
  second word at `top - 152`, carried through the stores into the buffer by `Frm.store` (`frm_chain`).

  ## Main definitions

  * `PreT`, `PostT`, `specT`, `Mem`, `Hdr`, `Frm`, `Base`, `I1Inv`, `I2Inv`, `CInv`, `FinInv`

  ## Main results

  * `slots`, `or256`, `or512`, `heap_ok`, `Frm.store`, `inner1`, `inner2`, `middle`, `chunk_stores`, `chunk`,
    `fin_ok`, `hdr`, `call_mem`, `slot_off`
-/

import Rv64mc.Proof.Runtime.FromElemT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Core.AbortStop
import Rv64mc.Proof.Whir.VecWordT
import Rv64mc.Spec.Field.Scaled
import Rv64mc.Gen.Tmpl.Verifier.Field.Scaled.New

namespace Rv64mc.Proof.Field.ScaledNewT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Whir.VecWordT (vecT_stores)
open Rv64mc.Gen.Verifier.Field.Scaled.New (Link tmpl d_c8_a4f5b9af_words)

/-- The total precondition: the result's slot (`24` bytes) in a window, 8-byte aligned, owned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24

/-- The total postcondition: the slot a vector of `1408` `E`s (the tables), its buffer allocated since the entry. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ (vecLen m' (regs .x10)).toNat = 1408 ∧
    (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat

/-- **The total contract of `Scaled::new`**: `PreT` to `PostT`, writing at most the slot (the partial contract's
    `NewOut`), or ending the run with `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) Spec.Field.Scaled.NewOut (Stop := AbortStop)

/-- What every part keeps of memory: `SavedT.MemOk` with the thirteen saved registers' slots, from `top - 8` (the
    return address) down to `top - 104` (`s11`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (Spec.Field.Scaled.NewOut regs m)
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

/-- The frame's words besides the slots: the slot's address at `top - 168`, the chunks' end `p + 22528` at
    `top - 160`, the tables' header at `top - 128` (capacity `cp`, pointer `p`, length `1408`); the buffer `p` of `cp`
    elements allocated since the entry, below `NEXT`, 8-byte aligned. -/
def Hdr (env : Env) (m : MachineState) (top : Word) (regs : Reg → Word) (cp p : Word) (M : MachineState) : Prop :=
  M.getMem (top + 18446744073709551448#64) = regs .x10 ∧
    (M.getMem (top + 18446744073709551456#64)).toNat = p.toNat + 22528 ∧
    M.getMem (top + 18446744073709551488#64) = cp ∧ M.getMem (top + 18446744073709551496#64) = p ∧
    M.getMem (top + 18446744073709551504#64) = 1408#64 ∧ 1408 ≤ cp.toNat ∧ cp.toNat * 16 < 2 ^ 63 ∧
    0x10000000 ≤ p.toNat ∧ p.toNat % 8 = 0 ∧ p.toNat + 16 * cp.toNat ≤ (env.next M).toNat ∧
    (env.next m).toNat ≤ p.toNat

/-- `Hdr`, `Mem`, and the chunk's second word `w` at `top - 152`. -/
def Frm (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (cp p : Word) (w : Nat)
    (M : MachineState) : Prop :=
  Hdr env m top regs cp p M ∧ Mem env ret top regs m M ∧ (M.getMem (top + 18446744073709551464#64)).toNat = w

/-- The blocks' loop head (instruction 44), `c` chunks and `k` blocks of the chunk left: the stack pointer, the
    chunk's size `11264` in `x10`, `16` and `32` in `x14`, `x15`, the chunk `x11`, the block's offset `x16`, the block's
    second word `x17`, the chunk's second word at `top - 152`; `Hdr`, `Mem`. -/
def Base (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (cp p : Word) (c k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551440#64 ∧ R .x10 = 11264#64 ∧ R .x14 = 16#64 ∧ R .x15 = 32#64 ∧
    (R .x11).toNat = p.toNat + 11264 * (2 - c) ∧ (R .x16).toNat = 1024 * (11 - k) ∧
    (R .x17).toNat = (R .x11).toNat + 8 + 1024 * (11 - k) ∧ 1 ≤ c ∧ c ≤ 2 ∧ 1 ≤ k ∧ k ≤ 11 ∧
    Frm env ret top regs m cp p ((R .x11).toNat + 8) M

/-- The first inner loop's head (instruction 141), `j` of its `16` entries left: `Base`, the block `x5`, the entry
    `x6`, the read cursor `x31`. -/
def I1Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (cp p : Word) (c k j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m cp p c k R M ∧ (R .x5).toNat = (R .x11).toNat + (R .x16).toNat ∧
    (R .x6).toNat = 16 - j ∧ (R .x31).toNat = (R .x17).toNat + 16 * (16 - j) ∧ 1 ≤ j ∧ j ≤ 16

/-- The second inner loop's head (instruction 164), `j` of its `32` entries left: `Base`, the block `x5`, the entry
    `x31`, the read cursor `x28`. -/
def I2Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (cp p : Word) (c k j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m cp p c k R M ∧ (R .x5).toNat = (R .x11).toNat + (R .x16).toNat ∧
    (R .x31).toNat = 32 - j ∧ (R .x28).toNat = (R .x17).toNat + 16 * (32 - j) ∧ 1 ≤ j ∧ j ≤ 32

/-- The chunks' loop head (instruction 39), `c` chunks left: `Base`'s registers but the block's, the chunk's second
    word `x17`; `Frm` with any word at `top - 152`. -/
def CInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (cp p : Word) (c : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551440#64 ∧ R .x10 = 11264#64 ∧ R .x14 = 16#64 ∧ R .x15 = 32#64 ∧
    (R .x11).toNat = p.toNat + 11264 * (2 - c) ∧ (R .x17).toNat = (R .x11).toNat + 8 ∧ 1 ≤ c ∧ c ≤ 2 ∧
    ∃ w, Frm env ret top regs m cp p w M

/-- The exit (instruction 200): the stack pointer; `Frm` with any word at `top - 152`. -/
def FinInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (cp p : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551440#64 ∧ ∃ w, Frm env ret top regs m cp p w M

set_option hygiene false in
/-- A word `top + c` of the frame, as a number. -/
local macro "tn" : tactic => `(tactic| (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))


/-- An entry's offset `16 x + 256` as the code computes it, `x < 16`. -/
theorem or256 {x : Word} (hx : x.toNat < 16) : (x <<< 4 ||| 256#64).toNat = 16 * x.toNat + 256 := by
  have h : ∀ n, n < 16 → ((BitVec.ofNat 64 n) <<< 4 ||| 256#64).toNat = 16 * n + 256 := by decide
  simpa using h x.toNat hx

/-- An entry's offset `16 x + 512` as the code computes it, `x < 32`. -/
theorem or512 {x : Word} (hx : x.toNat < 32) : (x <<< 4 ||| 512#64).toNat = 16 * x.toNat + 512 := by
  have h : ∀ n, n < 32 → ((BitVec.ofNat 64 n) <<< 4 ||| 512#64).toNat = 16 * n + 512 := by decide
  simpa using h x.toNat hx

/-- **A store into the tables' buffer** (`a` among its `cp` elements): `Hdr`, `Mem` kept, every word of the stack
    read as before. -/
theorem heap_ok {env : Env} {ret top a cp q : Word} {regs : Reg → Word} {m M : MachineState}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hH : Hdr env m top regs cp q M) (hM : Mem env ret top regs m M)
    (hlo : q.toNat ≤ a.toNat) (hhi : a.toNat + 8 ≤ q.toNat + 16 * cp.toNat) (v : Word) :
    Hdr env m top regs cp q (M.setMem a v) ∧ Mem env ret top regs m (M.setMem a v) ∧
      ∀ b : Word, env.stackLimit.toNat ≤ b.toNat → (M.setMem a v).getMem b = M.getMem b := by
  have hlay := env.layout
  have hnM := hM.1.2.1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hH
  obtain ⟨hM', n1⟩ := hM.fresh (a := a) (v := v) slots (by omega) (by omega) (by omega)
  have rd : ∀ b : Word, env.stackLimit.toNat ≤ b.toNat → (M.setMem a v).getMem b = M.getMem b := fun b hb =>
    MachineState.getMem_setMem_ne (Tactic.ne_of_toNat (by omega))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8, h9, by rw [n1]; exact h10, h11⟩, hM', rd⟩
  · rw [rd _ (by tn)]; exact h1
  · rw [rd _ (by tn)]; exact h2
  · rw [rd _ (by tn)]; exact h3
  · rw [rd _ (by tn)]; exact h4
  · rw [rd _ (by tn)]; exact h5

/-- `Frm` across a store into the tables' buffer. -/
theorem Frm.store {env : Env} {ret top a cp q : Word} {regs : Reg → Word} {m X : MachineState} {w : Nat}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (h : Frm env ret top regs m cp q w X)
    (hlo : q.toNat ≤ a.toNat) (hhi : a.toNat + 8 ≤ q.toNat + 16 * cp.toNat) (v : Word) :
    Frm env ret top regs m cp q w (X.setMem a v) := by
  obtain ⟨hH, hM, h152⟩ := h
  obtain ⟨hH', hM', rd⟩ := heap_ok hlim hH hM hlo hhi v
  exact ⟨hH', hM', by rw [rd _ (by tn)]; exact h152⟩

set_option hygiene false in
/-- `Frm` through a chain of `n` stores into the tables' buffer, from `hF`, each address's bounds by `omega` (after
    reading `x + c` as a number). -/
local macro "frm_chain " n:num : tactic => `(tactic| (
  try simp only [Tactic.rf]
  iterate $n apply Frm.store hlim
  · exact hF
  all_goals first | omega | (rw [toNat_add_ofNat (by omega)]; omega)))

-- The executor's run over the block's xor values and the two `Frm` chains together pass the default budget.
set_option maxHeartbeats 400000 in
set_option rv_sym.heap true in
/-- **The first inner loop**, from its head: entry `x6` of the block's second sixteen written; back to the head, or
    on to the second inner loop; one entry fewer left. -/
theorem inner1 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 176 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) {cp q : Word} {c k : Nat}
    (h2 : ∀ j R M, I2Inv env ret top regs m cp q c k j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 328, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, I1Inv env ret top regs m cp q c k j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 282, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (I1Inv env ret top regs m cp q c k) fun j R M hI ih => ?_
  have hlay := env.layout
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  obtain ⟨⟨-, -, -, -, h11, h16, h17, hc1, hc2, hk1, hk11, hF⟩, h5, h6, h31, hj1, hj16⟩ := id hI
  obtain ⟨⟨-, -, -, -, -, hcp1, hcp2, hp1, hp2, hpn, hpm⟩, hM, -⟩ := id hF
  have hhe := hW.heapEnd_le
  have hnM := hM.1.2.1
  have ho := or256 (x := R .x6) (by omega)
  have hx8 : (R .x5 + (R .x6 <<< 4 ||| 256#64)).toNat = (R .x5).toNat + 16 * (R .x6).toNat + 256 := by
    rw [BitVec.toNat_add, ho]; omega
  have hx8' : (R .x5 + (R .x6 <<< 4 ||| 256#64) + 8#64).toNat = (R .x5).toNat + 16 * (R .x6).toNat + 264 := by
    rw [toNat_add_ofNat (by omega), hx8]
  rv_introT hI
  rv_symT hp stop [282, 328] with [hlim]
  -- back to the head
  · have hj2 : 2 ≤ j := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega)]; simp only [BitVec.toNat_ofNat]; omega))
    refine ih (j - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, h11, h16, h17, hc1, hc2, hk1, hk11, ?_⟩, h5, ?_, ?_,
      by omega, by omega⟩
    · frm_chain 2
    all_goals simp only [Tactic.rf]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
  -- on to the second inner loop
  · refine h2 32 _ _ ⟨⟨rfl, rfl, rfl, rfl, h11, h16, h17, hc1, hc2, hk1, hk11, ?_⟩, h5, ?_, ?_, by omega,
      by omega⟩
    · frm_chain 2
    all_goals simp only [Tactic.rf]
    · rfl
    · omega

-- As `inner1`, with four exits, each rebuilding `Frm` through the two stores.
set_option maxHeartbeats 1000000 in
set_option rv_sym.heap true in
/-- **The second inner loop**, from its head: entry `x31` of the block's last thirty-two written; back to the head,
    or after the block on to the next block (`k - 1` left), the next chunk (`c - 1` left) or the exit; one entry
    fewer left. -/
theorem inner2 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 176 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) {cp q : Word} {c k : Nat}
    (hfin : ∀ R M, FinInv env ret top regs m cp q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 400, ret, top⟩ :: rest, R, M⟩)
    (hch : ∀ R M, 2 ≤ c → CInv env ret top regs m cp q (c - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩)
    (hmid : ∀ R M, 2 ≤ k → Base env ret top regs m cp q c (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 88, ret, top⟩ :: rest, R, M⟩) :
    ∀ j R M, I2Inv env ret top regs m cp q c k j R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 328, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (I2Inv env ret top regs m cp q c k) fun j R M hI ih => ?_
  have hlay := env.layout
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  obtain ⟨⟨-, -, -, -, h11, h16, h17, hc1, hc2, hk1, hk11, hF⟩, h5, h31, h28, hj1, hj32⟩ := id hI
  obtain ⟨⟨-, h160, -, -, -, hcp1, hcp2, hp1, hp2, hpn, hpm⟩, hM, h152⟩ := id hF
  have hhe := hW.heapEnd_le
  have hnM := hM.1.2.1
  have ho := or512 (x := R .x31) (by omega)
  have hx8 : (R .x5 + (R .x31 <<< 4 ||| 512#64)).toNat = (R .x5).toNat + 16 * (R .x31).toNat + 512 := by
    rw [BitVec.toNat_add, ho]; omega
  have hx8' : (R .x5 + (R .x31 <<< 4 ||| 512#64) + 8#64).toNat = (R .x5).toNat + 16 * (R .x31).toNat + 520 := by
    rw [toNat_add_ofNat (by omega), hx8]
  rv_introT hI
  rv_symT hp stop [328, 88, 78, 400] with [hlim]
  -- back to the head
  · have hj2 : 2 ≤ j := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega)]; simp only [BitVec.toNat_ofNat]; omega))
    refine ih (j - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, h11, h16, h17, hc1, hc2, hk1, hk11, ?_⟩, h5, ?_, ?_,
      by omega, by omega⟩
    · frm_chain 2
    all_goals simp only [Tactic.rf]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
  -- the next block
  · have hk2 : 2 ≤ k := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega)]; simp only [BitVec.toNat_ofNat]; omega))
    refine hmid _ _ hk2 ⟨rfl, rfl, rfl, rfl, h11, ?_, ?_, hc1, hc2, by omega, by omega, ?_⟩
    · simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]; omega
    · simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]; omega
    · frm_chain 2
  -- the next chunk
  · have hk : k = 1 := by
      have := congrArg BitVec.toNat hc_2
      rw [toNat_add_ofNat (by omega)] at this; simp only [BitVec.toNat_ofNat] at this; omega
    have hc2' : 2 ≤ c := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [toNat_add_ofNat (by omega), h160]; omega))
    refine hch _ _ hc2' ⟨rfl, rfl, rfl, rfl, ?_, ?_, by omega, by omega, (R .x11).toNat + 8, ?_⟩
    · simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]; omega
    · simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]; omega
    · frm_chain 2
  -- the exit
  · exact hfin _ _ ⟨rfl, (R .x11).toNat + 8, by frm_chain 2⟩

-- `Frm` is rebuilt through the block's thirty stores, each address's bounds by `omega`.
set_option maxHeartbeats 1000000 in
set_option rv_sym.heap true in
/-- **The blocks' loop**, from its head: the block's first sixteen entries written, then the first inner loop; one
    block fewer left after each. -/
theorem middle (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 176 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) {cp q : Word} {c : Nat}
    (hin : ∀ k, (∀ R M, 2 ≤ k → Base env ret top regs m cp q c (k - 1) R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 88, ret, top⟩ :: rest, R, M⟩) →
      ∀ j R M, I1Inv env ret top regs m cp q c k j R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 282, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, Base env ret top regs m cp q c k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 88, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (Base env ret top regs m cp q c) fun k R M hI ih => ?_
  have hlay := env.layout
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  obtain ⟨-, -, -, -, h11, h16, h17, hc1, hc2, hk1, hk11, hF⟩ := id hI
  obtain ⟨⟨-, -, -, -, -, hcp1, hcp2, hp1, hp2, hpn, hpm⟩, hM, -⟩ := id hF
  have hhe := hW.heapEnd_le
  have hnM := hM.1.2.1
  have h5 : (R .x11 + R .x16).toNat = (R .x11).toNat + (R .x16).toNat := by rw [BitVec.toNat_add]; omega
  rv_introT hI
  rv_symT hp stop [282] with [hlim]
  all_goals try (rw [inWindow_iff, toNat_add_ofNat (by omega)]; omega)
  refine hin k (fun R' M' _ h => ih (k - 1) R' M' (Nat.sub_lt hk1 Nat.one_pos) h) 16 _ _
    ⟨⟨rfl, rfl, rfl, rfl, h11, h16, h17, hc1, hc2,
    hk1, hk11, ?_⟩, ?_, ?_, ?_, by omega, Nat.le_refl _⟩
  · frm_chain 30
  all_goals simp only [Tactic.rf]
  · exact h5
  · rfl
  · omega

/-- **The chunk's frame words stored** (its second word at `top - 152`, two values at `top - 136` and `top - 144`):
    `Frm` with the new second word. -/
theorem chunk_stores {env : Env} {ret top cp q x v1 v2 : Word} {regs : Reg → Word} {m M : MachineState} {w : Nat}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (h : Frm env ret top regs m cp q w M) :
    Frm env ret top regs m cp q x.toNat (((M.setMem (top + 18446744073709551464#64) x).setMem
      (top + 18446744073709551480#64) v1).setMem (top + 18446744073709551472#64) v2) := by
  have hlay := env.layout
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hM, -⟩ := h
  have s1 := hM.slot (a := top + 18446744073709551464#64) (v := x) slots (F := 176) hlim (by tn) (by tn)
  have s2 := s1.1.slot (a := top + 18446744073709551480#64) (v := v1) slots (F := 176) hlim (by tn) (by tn)
  have s3 := s2.1.slot (a := top + 18446744073709551472#64) (v := v2) slots (F := 176) hlim (by tn) (by tn)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b h => Tactic.ne_of_toNat h
  have e152 : (top + 18446744073709551464#64).toNat = top.toNat - 152 := by tn
  have e136 : (top + 18446744073709551480#64).toNat = top.toNat - 136 := by tn
  have e144 : (top + 18446744073709551472#64).toNat = top.toNat - 144 := by tn
  have rd : ∀ o : Word, ∀ k, o.toNat + k = 2 ^ 64 → k ≤ 176 → k ≠ 152 → k ≠ 136 → k ≠ 144 →
      (((M.setMem (top + 18446744073709551464#64) x).setMem (top + 18446744073709551480#64) v1).setMem
        (top + 18446744073709551472#64) v2).getMem (top + o) = M.getMem (top + o) := fun o k ho hk h1 h2 h3 => by
    have e : (top + o).toNat = top.toNat - k := by rw [BitVec.toNat_add]; omega
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega))]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8, h9, by rw [s3.2, s2.2, s1.2]; exact h10, h11⟩, s3.1, ?_⟩
  · rw [rd 18446744073709551448#64 168 rfl (by omega) (by omega) (by omega) (by omega)]; exact h1
  · rw [rd 18446744073709551456#64 160 rfl (by omega) (by omega) (by omega) (by omega)]; exact h2
  · rw [rd 18446744073709551488#64 128 rfl (by omega) (by omega) (by omega) (by omega)]; exact h3
  · rw [rd 18446744073709551496#64 120 rfl (by omega) (by omega) (by omega) (by omega)]; exact h4
  · rw [rd 18446744073709551504#64 112 rfl (by omega) (by omega) (by omega) (by omega)]; exact h5
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]

set_option rv_sym.heap true in
/-- **The chunks' loop**, from its head: the chunk's frame words stored, then the blocks' loop; one chunk fewer left
    after each. -/
theorem chunk (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hn : 176 ≤ need) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) {cp q : Word}
    (hm : ∀ c, (∀ R M, 2 ≤ c → CInv env ret top regs m cp q (c - 1) R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩) →
      ∀ k R M, Base env ret top regs m cp q c k R M →
        rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 88, ret, top⟩ :: rest, R, M⟩) :
    ∀ c R M, CInv env ret top regs m cp q c R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (CInv env ret top regs m cp q) fun c R M hI ih => ?_
  have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
  obtain ⟨-, -, -, -, h11, h17, hc1, hc2, w, hF⟩ := id hI
  have hcd : M.code = m.code := hF.2.1.2.1
  rv_introT hI
  rv_symT hp stop [88] with [hlim]
  refine hm c (fun R' M' _ h => ih (c - 1) R' M' (Nat.sub_lt hc1 Nat.one_pos) h) 11 _ _
    ⟨rfl, rfl, rfl, rfl, h11, ?_, ?_, hc1, hc2,
    by omega, Nat.le_refl _, ?_⟩
  · simp only [Tactic.rf]; rfl
  · simp only [Tactic.rf]; omega
  · have := chunk_stores (x := R .x17) (v1 := R .x12) (v2 := R .x9) hlim hF
    simp only [Tactic.rf]
    rw [h17] at this
    exact this

set_option rv_sym.heap true in
/-- **The exit**: the tables' header (capacity, pointer, length `1408`) stored into the slot, the epilogue, the
    return. -/
theorem fin_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 176 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) Spec.Field.Scaled.NewOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0)
    (hW : Windows env top m) (hwS : InWin env (regs .x10) 24) (haS : (regs .x10).toNat % 8 = 0)
    (hoS : env.Owned m top (regs .x10) 24) {cp q : Word} :
    ∀ R M, FinInv env ret top regs m cp q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 400, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  obtain ⟨-, w, ⟨h168, -, h128, h120, h112, hcp1, hcp2, hp1, hp2, hpn, hpm⟩, ⟨hF, hcd, hst, s1, s2, s3, s4, s5, s6, s7,
    s8, s9, s10, s11, s12, s13, -⟩, -⟩ := id hinv
  have hlS := hwS.lt
  have hlay := env.layout
  have hnM := hF.1
  obtain ⟨ho1, -⟩ := hoS
  rv_introT hinv
  rv_symT hp with [(by omega : env.stackLimit.toNat + 176 ≤ top.toNat), h168]
  all_goals simp only [h168]
  all_goals try rv_closeT
  · have o : ∀ k : Nat, k < 24 → Spec.Field.Scaled.NewOut regs m (regs .x10 + BitVec.ofNat 64 k) := fun k hk =>
      ⟨by rw [toNat_add_ofNat (by omega)]; omega,
        by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega⟩
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out hF (by simpa using o 0 (by omega))
      (hwS.ne_next (Nat.le_refl _) (by omega))) (o 8 (by omega)) (hwS.ne_next_add (o := 8) (by omega)))
      (o 16 (by omega)) (hwS.ne_next_add (o := 16) (by omega))
  all_goals
    have hB : BufT env M (M.getMem (top + 18446744073709551488#64)) (M.getMem (top + 18446744073709551496#64)) 16 :=
      .inr ⟨by rw [h120]; omega, by unfold Env.Live; rw [h128, h120]; omega, by rw [h120]; exact hp2⟩
    have hc : (M.getMem (top + 18446744073709551488#64)).toNat * 16 < 2 ^ 63 := by rw [h128]; exact hcp2
    have hl : (M.getMem (top + 18446744073709551504#64)).toNat ≤ (M.getMem (top + 18446744073709551488#64)).toNat := by
      rw [h112, h128]; simp only [BitVec.toNat_ofNat]; omega
  · exact (vecT_stores hwS haS hB hc hl).1.2.1.2.2.1
  · exact (vecT_stores hwS haS hB hc hl).1.2.1.2.2.2

/-- The tables' header words (at `top - 128`) as `rvCapAt`, `rvPtrAt`, `vecCap`, `vecPtr`, `vecLen` name them. -/
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

/-- **Across `from_elem`** (`m1`, from the stack pointer `top - 176`, writing the header at `top - 128`): `Mem`
    kept, every other word of the frame read as before. -/
theorem call_mem {env : Env} {ret top : Word} {regs : Reg → Word} {m M m1 : MachineState} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 176 ≤ top.toNat) (hM : Mem env ret top regs m M)
    (hf : env.Frame (top + 18446744073709551440#64) out M m1)
    (hout : ∀ a, out a → InRange (top + 18446744073709551488#64) 24 a)
    (hk : ∀ a : Word, top + 18446744073709551440#64 ≤ a → ¬ out a → m1.getMem a = M.getMem a)
    (hc : m1.code = M.code) (hs : env.Static m1) :
    Mem env ret top regs m m1 ∧ (env.next m).toNat ≤ (env.next M).toNat ∧ ∀ a : Word, top.toNat - 176 ≤ a.toNat →
      ¬ InRange (top + 18446744073709551488#64) 24 a → m1.getMem a = M.getMem a := by
  have hlay := env.layout
  have e1 : (top + 18446744073709551440#64).toNat = top.toNat - 176 := by tn
  have e2 : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by tn
  have rd : ∀ a : Word, top.toNat - 176 ≤ a.toNat → ¬ InRange (top + 18446744073709551488#64) 24 a →
      m1.getMem a = M.getMem a := fun a h1 h2 => hk a (Tactic.le_of_toNat (by omega)) fun h => h2 (hout a h)
  refine ⟨hM.call slots (by omega) (by omega) hf hc hs (fun a ha => Tactic.mw_stack ?_) fun a h1 h2 =>
    rd a (by omega) fun h => by unfold InRange at h; omega, hM.next_le, rd⟩
  have := hout a ha
  unfold InRange at this
  omega

/-- The slot's address's word (`top - 168`) lies in the frame, apart from the header `from_elem` writes. -/
theorem slot_off {top : Word} (h : 176 ≤ top.toNat) :
    top.toNat - 176 ≤ (top + 18446744073709551448#64).toNat ∧
      ¬ InRange (top + 18446744073709551488#64) 24 (top + 18446744073709551448#64) := by
  have e1 : (top + 18446744073709551448#64).toNat = top.toNat - 168 := by tn
  have e2 : (top + 18446744073709551488#64).toNat = top.toNat - 128 := by tn
  unfold InRange
  rw [e1, e2]
  omega

set_option rv_sym.heap true in
/-- **`Scaled::new` is total**: the tables allocated zeroed (`from_elem`, `1408` entries), then the chunks of `704`
    entries, the exit. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hd : DataRef.InData env [(L.d_c8_a4f5b9af, d_c8_a4f5b9af_words)])
    {need needF : Nat} (hnF : 176 + needF ≤ need)
    (hfe : Runtime.FromElemT.FromElemSpecT env p L.fromElemGlobal.idx needF) :
    specT env p i need := by
  rv_autoT hp stop [2] with [hL, (by omega : env.stackLimit.toNat + 176 ≤ top.toNat)]
  have hW := hpre_11
  have hfin := fun cp q => fin_ok env p i L hp (by omega : 176 ≤ need) hk hpre_3 hpre_10 hpre_11 hpre_6 hpre_7
    (hpre_2 ▸ ⟨hpre_8, hpre_9⟩) (cp := cp) (q := q)
  have hch := fun cp q => chunk env p i L hp hpre_3 (by omega) hpre_10 hpre_11 (cp := cp) (q := q)
    fun c hc => middle env p i L hp hpre_3 (by omega) hpre_10 hpre_11 fun k hk =>
      inner1 env p i L hp hpre_3 (by omega) hpre_10 hpre_11
        (inner2 env p i L hp hpre_3 (by omega) hpre_10 hpre_11 (hfin cp q) hc hk)
  clear hfin
  rv_symT hp stop [78, 400] with [hL, (by omega : env.stackLimit.toNat + 176 ≤ top.toNat)] using [hfe]
  all_goals
    have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
    have hlay := env.layout
    obtain ⟨bc, bp, -, -, bL⟩ := hdr top m1
    have h112 : m1.getMem (top + 18446744073709551504#64) = 1408#64 := by rw [← bL]; exact hret1_22
  -- never fewer than `704` entries
  · rw [h112] at hc
    exact absurd hc (by decide : ¬ (1408#64 < 704#64))
  all_goals
    have hD0 := hW.data_ok _ (hd _ (List.mem_singleton_self _) 0 Nat.zero_lt_one)
    simp only [Nat.mul_zero, BitVec.add_zero] at hD0
  · exact hD0.1
  · exact hD0.2
  · have hDv : m1.getMem (L.d_c8_a4f5b9af.hi + L.d_c8_a4f5b9af.lo) = 0x2e8ba2e8ba2e8ba3#64 := by
      simpa [d_c8_a4f5b9af_words] using (hd.words (List.mem_singleton_self _)).get0 hret1_15 Nat.zero_lt_one
    have hend : (BinOp.mulhu.eval 1408#64 0x2e8ba2e8ba2e8ba3#64 >>> 7 * 11264#64 : Word) = 22528#64 := by decide
    have hM0 := (call_mem (m := m) (regs := regs) (ret := ret) hlim (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
        rv_closeT) hret1_14 (fun a ha => by
          simp only [SretVecOut, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte] at ha
          exact ha) keep1_1 hret1_24 hret1_15)
    obtain ⟨hM1, hn0, rd1⟩ := hM0
    obtain ⟨-, -, bC, bP, -⟩ := hdr top m1
    have hhe := hW.heapEnd_le
    have hn1 := hret1_14.1
    have hn1' := hret1_14.2.1
    have h19 := hret1_19
    rw [bc, bp] at h19
    have h20 := hret1_20
    rw [bc] at h20
    have h21 := hret1_21
    rw [bL, bC, h112] at h21
    simp only [BitVec.toNat_ofNat] at h21
    obtain ⟨hq0, hqL, hq8⟩ := h19.resolve_left (by omega)
    unfold Env.Live at hqL
    obtain ⟨hf1, -⟩ := hret1_23.resolve_left (by decide)
    rw [bP] at hf1
    have e160 : (top + 18446744073709551456#64).toNat = top.toNat - 160 := by tn
    have hns : ∀ v, env.next (m1.setMem (top + 18446744073709551456#64) v) = env.next m1 := fun _ =>
      Tactic.next_setMem (Tactic.next_ne_of_stack (by omega))
    have h168 : m1.getMem (top + 18446744073709551448#64) = regs .x10 := by
      rw [rd1 _ (slot_off (by omega)).1 (slot_off (by omega)).2]
      exact MachineState.getMem_setMem_eq
    refine hch (m1.getMem (top + 18446744073709551488#64)) (m1.getMem (top + 18446744073709551496#64)) 2 _ _
      ⟨rfl, rfl, rfl, rfl, ?_, ?_, by omega, Nat.le_refl _, _, ⟨?_, ?_, ?_, ?_, ?_, by omega, h20, hq0, hq8, ?_,
        by omega⟩, (hM1.slot slots (F := 176) hlim (by omega) (by omega)).1, rfl⟩
    · simp only [Tactic.rf]; omega
    · simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]
    · rv_closeT
    · rw [MachineState.getMem_setMem_eq, h112, hDv, hend, toNat_add_ofNat (by omega)]
    · rv_closeT
    · rv_closeT
    · rv_closeT
    · rw [hns]; omega

end Rv64mc.Proof.Field.ScaledNewT

/-- info: 'Rv64mc.Proof.Field.ScaledNewT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ScaledNewT.total
