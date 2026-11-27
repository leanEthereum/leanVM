/-
  Rv64mc.Proof.Field.ESumProjectT

  `E::sum` over `(0..PACK).filter(|&i| RMFE_PROJECT[i] >> c & 1 == 1).map(|i| claim.mu[i])` (`verify_layer`'s
  functional term, index 29) is total (`SumSafeT`): passed the iterator by reference (the closure's reference to
  `c`, the range, the closure's reference to the claim), it returns without writing memory, or ends the run with
  `a0 = 2` on an index past `RMFE_PROJECT`'s sixteen words or past `mu` (`panic_bounds_check`). The precondition
  (`SumPreT`): the iterator's four words, `c` and the claim's first `24` bytes (`mu`'s header) in windows and 8-byte
  aligned, `mu` a `TabW`. The table `RMFE_PROJECT` is in the static data (`DataRef.InData`, an environment fact; only
  its addresses matter). The sum is not stated: no caller's safety reads it. The loop is `Total.loop` with the indices
  left as the measure; an index reaches the table only below `16` (the code checks it against `max(start, 16)`).

  ## Main definitions

  * `SumPreT`, `SumSafeT`, `Tab`

  ## Main results

  * `tbl_win`, `ret_ok`, `loop_ok`, `total`
-/

import Rv64mc.Proof.Field.ESumWinT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT
import Rv64mc.Tactic.TStep
import Rv64mc.Gen.Tmpl.Verifier.Field.E.SumMapFilterRangeUsizeVeHf05a01b5

namespace Rv64mc.Proof.Field.ESumProjectT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Field.ESumWinT
open Rv64mc.Gen.Verifier.Field.E.SumMapFilterRangeUsizeVeHf05a01b5 (Link tmpl d_c128_bf6fc22b_words)

/-- The total precondition: the iterator at `x10` (the reference to `c`, the range's start and end, the reference
    to the claim), `c` and the claim's first `24` bytes (`mu`: pointer at `8`, length at `16`) in windows and 8-byte
    aligned, `mu` a `TabW`. -/
def SumPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ InWin env (regs .x10) 32 ∧
    (m.getMem (regs .x10)).toNat % 8 = 0 ∧ InWin env (m.getMem (regs .x10)) 8 ∧
    (m.getMem (regs .x10 + 24#64)).toNat % 8 = 0 ∧ InWin env (m.getMem (regs .x10 + 24#64)) 24 ∧
    TabW env (m.getMem (m.getMem (regs .x10 + 24#64) + 8#64)) (m.getMem (m.getMem (regs .x10 + 24#64) + 16#64))

/-- **The total contract**: it returns, writing nothing, or ends the run with `a0 = 2`. It does not state the sum. -/
def SumSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (SumPreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

/-- `RMFE_PROJECT` in the static data. -/
abbrev Tab (env : Env) (L : Link) : Prop := DataRef.InData env [(L.d_c128_bf6fc22b, d_c128_bf6fc22b_words)]

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {Q : State rvIsa → Prop} {ret top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState}

/-- `AbiRegs` through writes of registers it does not read. -/
local macro "abi_ok " h:term : tactic =>
  `(tactic| ((repeat rw [AbiRegs.updReg_iff (by decide)]) <;> exact $h))

/-- **Word `j` of `RMFE_PROJECT`** (`j < 16`), as the code addresses it: in a window and 8-byte aligned. -/
theorem tbl_win (hW : Windows env top m) (hd : Tab env L) {j : Word} (hj : j.toNat < 16) :
    inWindow (L.d_c128_bf6fc22b.hi + L.d_c128_bf6fc22b.lo + j <<< 3) 8 = true ∧
      (L.d_c128_bf6fc22b.hi + L.d_c128_bf6fc22b.lo + j <<< 3).toNat % 8 = 0 := by
  have hl : d_c128_bf6fc22b_words.length = 16 := rfl
  have h := hW.data_ok _ (hd _ (List.mem_singleton_self _) j.toNat (by rw [hl]; omega))
  have e : j <<< 3 = BitVec.ofNat 64 (8 * j.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]; omega
  rw [e]; exact h

/-- The table's cursor after one more word. -/
theorem succ_shl3 (c q : Word) : q + c <<< 3 + 8#64 = q + (c + 1#64) <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]; omega

/-- The element's first doubleword, from the pointer kept 8 bytes into it. -/
theorem back8 (c q : Word) : c <<< 4 + q + 8#64 + 18446744073709551608#64 = c <<< 4 + q := by
  rw [BitVec.add_assoc]; simp

/-- The return after the loop. -/
theorem ret_ok (hp : p[i]? = some (tmpl L)) (hk : Cont env p Q ret top rest regs m) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) {r : Reg → Word} (h1 : r .x1 = ret) (ha : AbiRegs top regs r) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 84, ret, top⟩ :: rest, r, m⟩ := by
  have hx2 := ha.1
  rv_symT hp with [h1, hx2]
  exact hk _ _ ⟨⟨ha, Env.Frame.refl hnx, hst, trivial⟩, rfl⟩

/-- The loop from its head (instruction 28) at index `x10`, below the end `e`, `k + 1` indices left: the table's
    bound `b` in `x12` (`max(start, 16)`: `16`, or the index itself), `mu`'s cursor `x5` (`8` past its element),
    the table's cursor `x16`. -/
theorem loop_ok (hp : p[i]? = some (tmpl L)) (hL : L.WF p) (hd : Tab env L) {need : Nat}
    (hpanic : Aborts env p L.panicBoundsCheck.idx need) (hk : Cont env p Q ret top rest regs m)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hal : top.toNat % 16 = 0) (hW : Windows env top m) {ptr lw e b : Word} (ht : TabW env ptr lw) :
    ∀ k r M, (M = m ∧ r .x1 = ret ∧ r .x2 = top ∧ AbiRegs top regs r ∧ r .x15 = e ∧ r .x14 = lw ∧ r .x12 = b ∧
      (r .x10).toNat < e.toNat ∧ e.toNat - (r .x10).toNat - 1 = k ∧ (r .x10).toNat ≤ b.toNat ∧
      (b.toNat = 16 ∨ r .x10 = b) ∧ r .x5 = r .x10 <<< 4 + ptr + 8#64 ∧
      r .x16 = L.d_c128_bf6fc22b.hi + L.d_c128_bf6fc22b.lo + r .x10 <<< 3) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 56, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) _ fun k r M ⟨hM, h1, h2, ha, h15, h14, h12, hlt, hk', hb, hb16, h5, h16⟩ ih => ?_
  subst hM
  have hx10 : (r .x10 + 1#64).toNat = (r .x10).toNat + 1 := toNat_add_ofNat (by omega)
  rv_symT hp stop [56, 84] through [48] with [hL, h1, h2, h12, h14, h15] using [hpanic]
  -- the stack at both panics
  any_goals (rw [h2]; omega)
  -- the table's word, below `16` since the index is not the bound
  any_goals
    have h16' : (r .x10).toNat < 16 := by
      rcases hb16 with hb | hb
      · have : (r .x10).toNat ≠ b.toNat := fun h => hc (by rw [h12]; exact (BitVec.eq_of_toNat_eq h).symm)
        omega
      · exact absurd (h12.trans hb.symm) hc
    first
      | rw [h16]; exact (tbl_win hW hd h16').1
      | rw [h16]; exact (tbl_win hW hd h16').2
  -- `mu`'s element
  any_goals first
    | rw [h5, back8]; exact (ht.entry' hW (h14 ▸ hc)).1.1
    | rw [h5, back8]; exact (ht.entry' hW (h14 ▸ hc)).1.2
    | rw [h5]; exact (ht.entry' hW (h14 ▸ hc)).2.1
    | rw [h5]; exact (ht.entry' hW (h14 ▸ hc)).2.2
  -- the returns
  any_goals exact ret_ok hp hk hst hnx (by tnorm; exact h1) (by abi_ok ha)
  -- back to the head, one index fewer
  all_goals
    have hne : (r .x10 + 1#64).toNat ≠ e.toNat := fun h => hc (by rw [h15]; exact BitVec.eq_of_toNat_eq h.symm)
    have hnb : (r .x10).toNat ≠ b.toNat := fun h => hc_1 (by rw [h12]; exact (BitVec.eq_of_toNat_eq h).symm)
    refine ih (k - 1) _ _ (by omega) ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · tnorm; exact h1
    · tnorm; exact h2
    · abi_ok ha
    · tnorm; exact h15
    · tnorm; exact h14
    · tnorm; exact h12
    · tnorm; omega
    · tnorm; omega
    · tnorm; omega
    · tnorm; exact .inl (hb16.resolve_right fun h => hc_1 (h12.trans h.symm))
    · tnorm; rw [h5, succ_shl8]
    · tnorm; rw [h16, succ_shl3]

/-- **`E::sum` over `RMFE_PROJECT`'s filter is total**, with no stack. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (hd : Tab env L) {need : Nat} (hpanic : Aborts env p L.panicBoundsCheck.idx need) :
    SumSafeT env p i need := by
  rv_autoT hp stop [56] with [hL] using [hpanic]
  all_goals
    refine loop_ok (e := m.getMem (regs .x10 + 16#64)) hp hL hd hpanic hk hstop hpre_4 hpre_5 hpre_3 hpre_13 hpre_14
      hpre_12 ((m.getMem (regs .x10 + 16#64)).toNat - (m.getMem (regs .x10 + 8#64)).toNat - 1) _ _
      ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, hc_1, rfl, ?_, ?_,
        rfl, rfl⟩
  -- the start past the table: the bound is the start
  · exact Nat.le_refl _
  · exact .inr rfl
  -- the start within the table: the bound is `16`
  · exact hc
  · exact .inl rfl

end Rv64mc.Proof.Field.ESumProjectT

/-- info: 'Rv64mc.Proof.Field.ESumProjectT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESumProjectT.total
