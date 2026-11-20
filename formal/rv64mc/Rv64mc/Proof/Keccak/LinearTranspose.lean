/-
  Rv64mc.Proof.Keccak.LinearTranspose

  `linear_transpose::<E>` keeps its contract (`Spec.Keccak.LinearTranspose.spec`). Its frame holds `g` (1600 `E`s
  at `top - 30792`) and the column sums (320 `E`s at `top - 5192`), and the result's header at `top - 72`. Three
  loops: `g`'s fill (`loop1`, by lane and bit, the tables `KECCAK_PI` and `KECCAK_RHO` read at the lane), the
  column sums (`loop2`, `columns[j % 320] += g[j]`, the index by a multiplication), and the result (`loop3`, the
  rows `(x + 1) % 5` and `(x + 4) % 5` by a multiplication and masks). Each loop lemma ends at a continuation, the
  next segment's.
-/

import Rv64mc.Spec.Keccak.LinearTranspose
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Spec.Runtime.Alloc
import Rv64mc.Spec.Runtime.VecReserve
import Rv64mc.Core.ReprLemmas
import Rv64mc.Model.Extra.Keccak
import Rv64mc.Proof.Keccak.Mem
import Rv64mc.Proof.Multilinear.SliceLoop
import Rv64mc.Gen.Tmpl.Verifier.Keccak.LinearTransposeE
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Keccak.LinearTranspose

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Keccak.LinearTranspose
open Rv64mc.Gen.Verifier.Keccak.LinearTransposeE (Link tmpl)
open Rv64mc.Proof.Multilinear (step_ptr)

/-! ## Arithmetic -/

theorem mulhu_eval (a c : Word) : BinOp.mulhu.eval a c = BitVec.ofNat 64 (a.toNat * c.toNat / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.eval, BitVec.truncate_eq_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have ha := a.isLt; have hc := c.isLt
  have h : a.toNat * c.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hc
  have e : (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 := by rw [← Nat.pow_add]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt (show c.toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show a.toNat * c.toNat < 2 ^ 128 by omega)]

theorem ofNat_ushiftRight {x : Nat} (hx : x < 2 ^ 64) (k : Nat) :
    BitVec.ofNat 64 x >>> k = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)).symm

theorem mulhu_lit {j c : Nat} (hj : j < 2 ^ 64) (hc : c < 2 ^ 64) :
    BinOp.mulhu.eval (BitVec.ofNat 64 j) (BitVec.ofNat 64 c) = BitVec.ofNat 64 (j * c / 2 ^ 64) := by
  rw [mulhu_eval, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hc]

theorem div320 {j : Nat} (hj : j < 1600) : j * 14757395258967641293 / 2 ^ 64 / 2 ^ 8 = j / 320 := by
  rw [Nat.div_div_eq_div_mul, show (2 : Nat) ^ 64 * 2 ^ 8 = 4722366482869645213696 from rfl]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 320 ∧ j = 320 * q + r :=
    ⟨j / 320, j % 320, Nat.mod_lt _ (by omega), (Nat.div_add_mod j 320).symm⟩
  rw [show (320 * q + r) / 320 = q by omega]
  apply Nat.div_eq_of_lt_le <;> omega

theorem neg5120 : (18446744073709546496#64 : BitVec 64) = -5120#64 := by decide +kernel

/-- The column `columns[j % 320]` of the column loop: `j - 320 (j / 320)`, the quotient by `mulhu`. -/
theorem cols_off {j : Nat} (hj : j < 1600) :
    BitVec.ofNat 64 (16 * j) +
      BinOp.mulhu.eval (BitVec.ofNat 64 j) 14757395258967641293#64 >>> 8 * 18446744073709546496#64 =
      BitVec.ofNat 64 (16 * (j % 320)) := by
  rw [mulhu_lit (by omega) (by decide), ofNat_ushiftRight (Nat.div_lt_of_lt_mul (by omega)), div320 hj, neg5120,
    show 16 * j = 16 * (j % 320) + j / 320 * 5120 by omega, BitVec.ofNat_add (16 * (j % 320)),
    BitVec.ofNat_mul (j / 320) 5120, BitVec.mul_neg, BitVec.add_assoc, BitVec.add_right_neg, BitVec.add_zero]

theorem cols_addr (q : Word) {j : Nat} (hj : j < 1600) :
    q + BitVec.ofNat 64 (16 * j) +
      BinOp.mulhu.eval (BitVec.ofNat 64 j) 14757395258967641293#64 >>> 8 * 18446744073709546496#64 =
      q + BitVec.ofNat 64 (16 * (j % 320)) := by
  rw [BitVec.add_assoc, cols_off hj]

theorem cols_addr8 (q : Word) {j : Nat} (hj : j < 1600) :
    q + BitVec.ofNat 64 (16 * j) + 8#64 +
      BinOp.mulhu.eval (BitVec.ofNat 64 j) 14757395258967641293#64 >>> 8 * 18446744073709546496#64 =
      q + BitVec.ofNat 64 (16 * (j % 320)) + 8#64 := by
  rw [BitVec.add_assoc, BitVec.add_comm 8#64, ← BitVec.add_assoc, cols_addr q hj]

theorem step16 (q : Word) (j : Nat) : q + BitVec.ofNat 64 (16 * j) + 16#64 = q + BitVec.ofNat 64 (16 * (j + 1)) := by
  rw [BitVec.add_assoc, show 16 * (j + 1) = 16 * j + 16 by omega, BitVec.ofNat_add (16 * j)]

theorem ofNat_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem succ_ofNat (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.ofNat_add j 1]

theorem div5 {q : Nat} (hq : q < 25) : q * 3689348814741910324 / 2 ^ 64 = q / 5 := by
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < 5 ∧ q = 5 * a + b :=
    ⟨q / 5, q % 5, Nat.mod_lt _ (by omega), (Nat.div_add_mod q 5).symm⟩
  rw [show (5 * a + b) / 5 = a by omega]
  apply Nat.div_eq_of_lt_le <;> omega

set_option maxHeartbeats 200000 in
theorem xval {j : Nat} (hj : j < 1600) :
    BitVec.ofNat 64 j >>> 6 -
      (BinOp.mulhu.eval (BitVec.ofNat 64 j >>> 6) 3689348814741910324#64 <<< 2 +
        BinOp.mulhu.eval (BitVec.ofNat 64 j >>> 6) 3689348814741910324#64) = BitVec.ofNat 64 (j / 64 % 5) := by
  rw [ofNat_ushiftRight (by omega), show (2 : Nat) ^ 6 = 64 from rfl, mulhu_lit (by omega) (by decide),
    div5 (by omega), BitVec.shiftLeft_eq_mul_twoPow]
  obtain ⟨a, b, hb, e⟩ : ∃ a b, b < 5 ∧ j / 64 = 5 * a + b :=
    ⟨j / 64 / 5, j / 64 % 5, Nat.mod_lt _ (by omega), (Nat.div_add_mod _ 5).symm⟩
  rw [e, show (5 * a + b) / 5 = a by omega, show (5 * a + b) % 5 = b by omega,
    show BitVec.twoPow 64 2 = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul, BitVec.ofNat_add_ofNat,
    show a * 4 + a = 5 * a by omega, BitVec.ofNat_add (5 * a) b, BitVec.add_comm, BitVec.add_sub_cancel]

/-- `top + c` below `top` by `2^64 - c`, as a number. -/
theorem toNat_below {t : Word} {c d : Nat} (hcd : c + d = 2 ^ 64) (hd : d ≤ t.toNat) :
    (t + BitVec.ofNat 64 c).toNat = t.toNat - d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := t.isLt; omega

/-- `top + c` below `top`, as a number, for `rw`: the side conditions only in `c`. -/
theorem toNat_top {t : Word} {c : Nat} (hc : c < 2 ^ 64) (hd : 2 ^ 64 - c ≤ t.toNat) :
    (t + BitVec.ofNat 64 c).toNat = t.toNat - (2 ^ 64 - c) := toNat_below (by omega) hd

/-! ## The frame's objects -/

/-- `g`'s entries: the weight each position of θ's output carries. -/
def gF (ws : List E) (k : Nat) : Word × Word := Model.limbs ((Model.transposeG ws).getD k 0)

/-- The column sums after `j` positions. -/
def colsF (ws : List E) (j c : Nat) : Word × Word := Model.limbs ((Model.colsUpTo (Model.transposeG ws) j).getD c 0)

theorem gBase_toNat {top : Word} (h : 30792 ≤ top.toNat) : (top + 18446744073709520824#64).toNat = top.toNat - 30792 :=
  toNat_below (by decide) h

theorem colsBase_toNat {top : Word} (h : 5192 ≤ top.toNat) :
    (top + 18446744073709546424#64).toNat = top.toNat - 5192 :=
  toNat_below (by decide) h

theorem savedBase_toNat {top : Word} (h : 48 ≤ top.toNat) : (top + 18446744073709551568#64).toNat = top.toNat - 48 :=
  toNat_below (by decide) h

/-- A store below the prologue's keeps what it stored. -/
theorem saved_store {M : MachineState} {S : MachineState} {top x v : Word}
    (h : ∀ a, top + 18446744073709551568#64 ≤ a → M.getMem a = S.getMem a)
    (hx : x.toNat < (top + 18446744073709551568#64).toNat) :
    ∀ a, top + 18446744073709551568#64 ≤ a → (M.setMem x v).getMem a = S.getMem a := by
  intro a ha
  have hne : a ≠ x := fun he => by rw [he, BitVec.le_def] at ha; omega
  rw [MachineState.getMem_setMem_ne hne]; exact h a ha

/-- An element of the column sums, as a number. -/
theorem cols_elem {top : Word} (h : 30816 ≤ top.toNat) {c : Nat} (hc : c < 320) :
    (top + 18446744073709546424#64 + BitVec.ofNat 64 (16 * c)).toNat = top.toNat - 5192 + 16 * c ∧
      (top + 18446744073709546424#64 + BitVec.ofNat 64 (16 * c) + 8#64).toNat = top.toNat - 5192 + 16 * c + 8 := by
  have hb := colsBase_toNat (top := top) (by omega)
  have := top.isLt
  exact ⟨by rw [toNat_elem (by omega), hb], by rw [toNat_elem8 (by omega), hb]⟩

/-- The column sums after one more position. -/
theorem colsF_succ (ws : List E) {j : Nat} (hj : j < 1600) (c : Nat) :
    colsF ws (j + 1) c = if c = j % 320 then Model.eAdd (colsF ws j (j % 320)) (gF ws j) else colsF ws j c := by
  have hl : j < (Model.transposeG ws).length := by rw [Model.transposeG_length_eq]; exact hj
  unfold colsF gF
  rw [Model.colsUpTo_succ _ hl, Model.set_getD_eq, Model.colsUpTo_length, Model.eAdd_eq,
    ← List.getD_eq_getElem _ 0 hl]
  by_cases h : c = j % 320
  · rw [ite_eq_left ⟨h.symm, Nat.mod_lt _ (by decide)⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.1.symm), ite_eq_right h]


/-- What every loop keeps: the stack pointer, the result's slot, the header's address, `s3`, `s4` and the saved
    registers, the frame, and the prologue's stores. -/
def Base (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709520800#64 ∧ R .x8 = regs .x10 ∧ R .x18 = top + 18446744073709551544#64 ∧
    R .x19 = 1600#64 ∧ R .x20 = 25#64 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xffffffffffffffd0#64 ≤ a → M.getMem a =
      ((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
        (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
        (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).getMem a

/-- The prologue's stores kept: `Base`'s last fact. -/
abbrev Saved (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  ∀ a, top + 0xffffffffffffffd0#64 ≤ a → M.getMem a =
    ((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
      (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
      (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).getMem a

/-- Two stores into the frame below the prologue's keep the frame and the prologue's stores. -/
theorem frame_saved2 {env : Env} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {x y v w : Word}
    (hf : env.Frame top Tactic.F m M) (hs : Saved ret top regs m M) (htop : 48 ≤ top.toNat)
    (hx : env.stackLimit.toNat ≤ x.toNat ∧ x.toNat < top.toNat - 48)
    (hy : env.stackLimit.toNat ≤ y.toNat ∧ y.toNat < top.toNat - 48) :
    env.Frame top Tactic.F m ((M.setMem x v).setMem y w) ∧ Saved ret top regs m ((M.setMem x v).setMem y w) := by
  have hb := savedBase_toNat htop
  refine ⟨Tactic.frame_store (Tactic.frame_store hf hx.1 (by omega)) hy.1 (by omega), ?_⟩
  exact saved_store (saved_store hs (by omega)) (by omega)

/-! ## The column sums -/

/-- One position of the column loop on memory: `columns[j % 320] += g[j]`. -/
theorem loop2_mem {env : Env} {ws : List E} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {j : Nat}
    (htop : env.stackLimit.toNat + 30816 ≤ top.toNat) (hj : j < 1600) (hf : env.Frame top Tactic.F m M)
    (hs : Saved ret top regs m M) (hg : PairsAt M (top + 18446744073709520824#64) (gF ws) 1600)
    (hc : PairsAt M (top + 18446744073709546424#64) (colsF ws j) 320) :
    let A := top + 18446744073709546424#64 + BitVec.ofNat 64 (16 * (j % 320))
    let M' := (M.setMem A ((colsF ws j (j % 320)).1 ^^^ (gF ws j).1)).setMem (A + 8#64)
      ((colsF ws j (j % 320)).2 ^^^ (gF ws j).2)
    env.Frame top Tactic.F m M' ∧ Saved ret top regs m M' ∧
      PairsAt M' (top + 18446744073709520824#64) (gF ws) 1600 ∧
      PairsAt M' (top + 18446744073709546424#64) (colsF ws (j + 1)) 320 := by
  intro A M'
  have := top.isLt
  have hc320 : j % 320 < 320 := Nat.mod_lt _ (by decide)
  obtain ⟨e0, e8⟩ := cols_elem (top := top) (by omega) hc320
  have hgb := gBase_toNat (top := top) (by omega)
  have hcb := colsBase_toNat (top := top) (by omega)
  obtain ⟨h1, h2⟩ := frame_saved2 (v := (colsF ws j (j % 320)).1 ^^^ (gF ws j).1)
    (w := (colsF ws j (j % 320)).2 ^^^ (gF ws j).2) hf hs (by omega) (x := A) (y := A + 8#64)
    ⟨by simp only [A]; omega, by simp only [A]; omega⟩ ⟨by simp only [A]; omega, by simp only [A]; omega⟩
  refine ⟨h1, h2, ?_, ?_⟩
  · exact (hg.store_out (by omega) (by simp only [A]; omega)).store_out (by omega) (by simp only [A]; omega)
  · have := hc.set (by omega) hc320
      ((colsF ws j (j % 320)).1 ^^^ (gF ws j).1, (colsF ws j (j % 320)).2 ^^^ (gF ws j).2)
    intro c hc'
    rw [colsF_succ ws hj c]
    exact this c hc'

/-- The column loop's invariant at its head after `j` positions. -/
def Inv2 (env : Env) (ws : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧
    R .x9 = top + 18446744073709546424#64 + BitVec.ofNat 64 (16 * j) ∧ R .x10 = BitVec.ofNat 64 j ∧
    R .x11 = top + 18446744073709546424#64 + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    R .x12 = top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    R .x13 = 14757395258967641293#64 ∧ R .x14 = 18446744073709546496#64 ∧ R .x15 = 1600#64 ∧
    PairsAt M (top + 18446744073709520824#64) (gF ws) 1600 ∧
    PairsAt M (top + 18446744073709546424#64) (colsF ws j) 320

/-- After the column loop. -/
def Exit2 (env : Env) (ws : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ PairsAt M (top + 18446744073709520824#64) (gF ws) 1600 ∧
    PairsAt M (top + 18446744073709546424#64) (colsF ws 1600) 320

set_option maxHeartbeats 1000000 in
theorem loop2 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (ws : List E)
    (hp : p[i]? = some (tmpl L))
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (htop : env.stackLimit.toNat + 30816 ≤ top.toNat)
    (hnext : ∀ R M, Exit2 env ws ret top regs m R M → rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 190, ret, top⟩ :: rest, R, M⟩) :
    ∀ k j R M, j + k + 1 = 1600 → Inv2 env ws ret top regs m j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 154, ret, top⟩ :: rest, R, M⟩ := by
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp stop [190]
    · exact absurd (by rw [succ_ofNat, show j + 1 = 1600 by omega]) hc
    have hjl : j < 1600 := by omega
    rw [cols_addr _ hjl, cols_addr8 _ hjl, (hinv_23 _ (Nat.mod_lt _ (by decide))).1,
      (hinv_23 _ (Nat.mod_lt _ (by decide))).2, (hinv_22 _ hjl).1, (hinv_22 _ hjl).2]
    obtain ⟨f1, f2, f3, f4⟩ := loop2_mem htop hjl hinv_13 hinv_14 hinv_22 hinv_23
    apply hnext
    rv_close
    · exact f2
    · exact f3
    · rw [show 1600 = j + 1 by omega]; exact f4
  | succ k ih =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp stop [190]
    · have hjl : j < 1600 := by omega
      rw [cols_addr _ hjl, cols_addr8 _ hjl, (hinv_23 _ (Nat.mod_lt _ (by decide))).1,
        (hinv_23 _ (Nat.mod_lt _ (by decide))).2, (hinv_22 _ hjl).1, (hinv_22 _ hjl).2]
      obtain ⟨f1, f2, f3, f4⟩ := loop2_mem htop hjl hinv_13 hinv_14 hinv_22 hinv_23
      apply ih (j + 1) _ _ (by omega)
      rv_close
      · exact f2
      · exact step16 _ _
      · exact succ_ofNat _
      · exact step_ptr _ _
      · exact step_ptr _ _
      · exact f3
      · exact f4
    · exact absurd hc (by rw [succ_ofNat, ofNat_inj (by omega) (by omega)]; omega)

/-! ## The result -/

theorem and63 (j : Nat) : (BitVec.ofNat 64 j &&& 63#64) <<< 4 = BitVec.ofNat 64 (16 * (j % 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show 63 % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
  omega

theorem and63s (j : Nat) : (BitVec.ofNat 64 j + 1#64 &&& 63#64) <<< 4 = BitVec.ofNat 64 (16 * ((j + 1) % 64)) := by
  rw [BitVec.ofNat_add_ofNat]; exact and63 _

theorem add_ofNat2 (t : Word) (a b : Nat) :
    t + BitVec.ofNat 64 a + BitVec.ofNat 64 b = t + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The row `(x + 1) % 5`'s element, at the offset `k` of its row. -/
theorem colA_eq (t : Word) (j k : Nat) :
    t + (BitVec.ofNat 64 j &&& 63#64) <<< 4 + BitVec.ofNat 64 k = t + BitVec.ofNat 64 (16 * (j % 64) + k) := by
  rw [and63, add_ofNat2]

/-- The row `(x + 4) % 5`'s element for `x = 0`, the row's offset folded into the base. -/
theorem colB0_eq (t : Word) (j : Nat) :
    t + 18446744073709550520#64 + (BitVec.ofNat 64 j + 1#64 &&& 63#64) <<< 4 =
      t + 18446744073709546424#64 + BitVec.ofNat 64 (4096 + 16 * ((j + 1) % 64)) := by
  rw [and63s, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- The row `(x + 4) % 5`'s element, at the offset `k` of its row. -/
theorem colB_eq (t : Word) (j k : Nat) :
    t + BitVec.ofNat 64 k + (BitVec.ofNat 64 j + 1#64 &&& 63#64) <<< 4 =
      t + BitVec.ofNat 64 (k + 16 * ((j + 1) % 64)) := by
  rw [and63s, add_ofNat2]

theorem PairsAt.get0 {M : MachineState} {a : Word} {f : Nat → Word × Word} {n : Nat} (h : PairsAt M a f n) {o : Nat}
    (ho : o < 16 * n) (h16 : o % 16 = 0) : M.getMem (a + BitVec.ofNat 64 o) = (f (o / 16)).1 := by
  have := (h (o / 16) (by omega)).1; rwa [show 16 * (o / 16) = o by omega] at this

theorem PairsAt.get1 {M : MachineState} {a : Word} {f : Nat → Word × Word} {n : Nat} (h : PairsAt M a f n) {o : Nat}
    (ho : o < 16 * n) (h16 : o % 16 = 0) : M.getMem (a + BitVec.ofNat 64 o + 8#64) = (f (o / 16)).2 := by
  have := (h (o / 16) (by omega)).2; rwa [show 16 * (o / 16) = o by omega] at this

/-- Position `k` of the result. -/
def outE (ws : List E) (k : Nat) : E :=
  (Model.transposeG ws).getD k 0 +
    (Model.transposeColumns (Model.transposeG ws)).getD (64 * ((k / 64 % 5 + 1) % 5) + k % 64) 0 +
    (Model.transposeColumns (Model.transposeG ws)).getD (64 * ((k / 64 % 5 + 4) % 5) + (k % 64 + 1) % 64) 0

/-- The limbs of position `j` of the result, from `g` and the two column sums the code reads, in its order. -/
theorem outE_limbs (ws : List E) {j : Nat} {a b : Nat}
    (ha : a / 16 = 64 * ((j / 64 % 5 + 1) % 5) + j % 64) (hb : b / 16 = 64 * ((j / 64 % 5 + 4) % 5) + (j % 64 + 1) % 64) :
    ((colsF ws 1600 (a / 16)).1 ^^^ (gF ws j).1 ^^^ (colsF ws 1600 (b / 16)).1) = (Model.limbs (outE ws j)).1 ∧
      ((colsF ws 1600 (a / 16)).2 ^^^ (gF ws j).2 ^^^ (colsF ws 1600 (b / 16)).2) = (Model.limbs (outE ws j)).2 := by
  have hl : (Model.transposeG ws).length = 1600 := Model.transposeG_length_eq ws
  have hc : Model.colsUpTo (Model.transposeG ws) 1600 = Model.transposeColumns (Model.transposeG ws) := by
    rw [← hl]; exact Model.colsUpTo_full _
  rw [ha, hb]
  unfold outE colsF gF
  rw [hc, ← Model.eAdd_eq, ← Model.eAdd_eq]
  simp only [Model.eAdd]
  exact ⟨by rw [BitVec.xor_comm ((Model.limbs _).1)], by rw [BitVec.xor_comm ((Model.limbs _).2)]⟩

/-- A store into what the call allocated is in its frame. -/
theorem frame_store_heap {env : Env} {top x v : Word} {m M : MachineState} (hf : env.Frame top Tactic.F m M)
    (hlo : (env.next m).toNat ≤ x.toNat) (hhi : x.toNat < (env.next M).toNat) :
    env.Frame top Tactic.F m (M.setMem x v) ∧ env.next (M.setMem x v) = env.next M := by
  have hlay := env.layout
  have hfe := hf.2.1
  have hne : env.nextAddr ≠ x := fun he => by rw [← he] at hhi; omega
  have hn : env.next (M.setMem x v) = env.next M := by
    simp [Env.next, MachineState.getMem, MachineState.setMem, hne]
  refine ⟨⟨by rw [hn]; exact hf.1, by rw [hn]; exact hfe, fun a ha => ?_⟩, hn⟩
  have hax : a ≠ x := fun he => ha (Or.inr (Or.inl ⟨by rw [he]; exact hlo, by rw [he, hn]; exact hhi⟩))
  rw [MachineState.getMem_setMem_ne hax]
  refine hf.2.2 a fun hw => ha ?_
  rcases hw with hw | hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl ⟨hw.1, by rw [hn]; exact hw.2⟩)
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact hw.elim

/-- What the result's loop keeps and fills, besides the registers. -/
def Mem3 (env : Env) (ws : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (P : Word) (cap : Nat)
    (j : Nat) (M : MachineState) : Prop :=
  env.Frame top Tactic.F m M ∧ Saved ret top regs m M ∧
    PairsAt M (top + 18446744073709520824#64) (gF ws) 1600 ∧
    PairsAt M (top + 18446744073709546424#64) (colsF ws 1600) 320 ∧
    PairsAt M P (fun k => Model.limbs (outE ws k)) j ∧
    M.getMem (top + 18446744073709551544#64) = BitVec.ofNat 64 cap ∧ M.getMem (top + 18446744073709551552#64) = P ∧
    (env.next m).toNat ≤ P.toNat ∧ P.toNat + 16 * cap ≤ (env.next M).toNat ∧ 1600 ≤ cap ∧ cap < 2 ^ 63

/-- One position of the result's loop on memory. -/
theorem loop3_mem {env : Env} {ws : List E} {ret top : Word} {regs : Reg → Word} {m M : MachineState}
    {P : Word} {cap : Nat} {j : Nat} (htop : env.stackLimit.toNat + 30816 ≤ top.toNat) (hj : j < 1600)
    (h : Mem3 env ws ret top regs m P cap j M) :
    Mem3 env ws ret top regs m P cap (j + 1)
      ((M.setMem (P + BitVec.ofNat 64 (16 * j)) (Model.limbs (outE ws j)).1).setMem
        (P + BitVec.ofNat 64 (16 * j) + 8#64) (Model.limbs (outE ws j)).2) := by
  obtain ⟨hf, hs, hg, hc, ho, hcap, hptr, hP1, hP2, hc1, hc2⟩ := h
  have hlay := env.layout
  have hfe := hf.2.1
  have := top.isLt
  have e0 := toNat_elem (a := P) (k := j) (by omega)
  have e8 := toNat_elem8 (a := P) (k := j) (by omega)
  obtain ⟨f1, n1⟩ := frame_store_heap (v := (Model.limbs (outE ws j)).1) hf (x := P + BitVec.ofNat 64 (16 * j))
    (by omega) (by omega)
  obtain ⟨f2, n2⟩ := frame_store_heap (v := (Model.limbs (outE ws j)).2) f1
    (x := P + BitVec.ofNat 64 (16 * j) + 8#64) (by omega) (by rw [n1]; omega)
  have hgb := gBase_toNat (top := top) (by omega)
  have hcb := colsBase_toNat (top := top) (by omega)
  have hsb := savedBase_toNat (top := top) (by omega)
  have hh0 := toNat_below (t := top) (c := 18446744073709551544) (d := 72) (by decide) (by omega)
  have hh8 := toNat_below (t := top) (c := 18446744073709551552) (d := 64) (by decide) (by omega)
  have ne1 : top + 18446744073709551544#64 ≠ P + BitVec.ofNat 64 (16 * j) := fun he => by
    have := congrArg BitVec.toNat he; omega
  have ne2 : top + 18446744073709551544#64 ≠ P + BitVec.ofNat 64 (16 * j) + 8#64 := fun he => by
    have := congrArg BitVec.toNat he; omega
  have ne3 : top + 18446744073709551552#64 ≠ P + BitVec.ofNat 64 (16 * j) := fun he => by
    have := congrArg BitVec.toNat he; omega
  have ne4 : top + 18446744073709551552#64 ≠ P + BitVec.ofNat 64 (16 * j) + 8#64 := fun he => by
    have := congrArg BitVec.toNat he; omega
  refine ⟨f2, saved_store (saved_store hs (by omega)) (by omega), ?_, ?_, ho.push (by omega), ?_, ?_, hP1,
    by rw [n2, n1]; exact hP2, hc1, hc2⟩
  · exact (hg.store_out (by omega) (by omega)).store_out (by omega) (by omega)
  · exact (hc.store_out (by omega) (by omega)).store_out (by omega) (by omega)
  · rw [MachineState.getMem_setMem_ne ne2, MachineState.getMem_setMem_ne ne1, hcap]
  · rw [MachineState.getMem_setMem_ne ne4, MachineState.getMem_setMem_ne ne3, hptr]

/-- The result's loop's invariant at its head after `j` positions. -/
def Inv3 (env : Env) (ws : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (P : Word) (cap : Nat)
    (j : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧
    R .x15 = BitVec.ofNat 64 j ∧ R .x12 = P + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    R .x13 = top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    R .x14 = top + 18446744073709546424#64 ∧ R .x11 = 0x3333333333333334#64 ∧ R .x9 = 1600#64 ∧ R .x10 = 0#64 ∧
    Mem3 env ws ret top regs m P cap j M

/-- After the result's loop. -/
def Exit3 (env : Env) (ws : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (P : Word) (cap : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ R .x10 = 0#64 ∧ R .x16 = 1600#64 ∧ Mem3 env ws ret top regs m P cap 1600 M

set_option hygiene false in
/-- One position of the result's loop after its last stop: the three column reads normalized and read, the stores
    made the next position's, and the head or the exit. -/
macro "lt_close3" : tactic => `(tactic| first
  | exact absurd (by rw [succ_ofNat, show j + 1 = 1600 by omega]) hc
  | (
  rw [colA_eq]
  first | rw [colB0_eq] | rw [colB_eq]
  simp (disch := omega) only [PairsAt.get0 hinv_25, PairsAt.get1 hinv_25, (hinv_24 _ hjl).1, (hinv_24 _ hjl).2]
  rw [(outE_limbs ws (by omega) (by omega)).1, (outE_limbs ws (by omega) (by omega)).2]
  have hm := loop3_mem htop hjl ⟨hinv_22, hinv_23, hinv_24, hinv_25, hinv_26, hinv_27, hinv_28, hinv_29, hinv_30, hinv_31, hinv_32⟩
  first
  | (apply ih (j + 1) _ _ (by omega)
     obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩ := hm
     rv_close
     all_goals first | exact succ_ofNat _ | exact step_ptr _ _ | with_reducible assumption)
  | (have e : j + 1 = 1600 := (ofNat_inj (by omega) (by omega)).1 ((succ_ofNat j).symm.trans hc)
     rw [e] at hm
     obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩ := hm
     apply hfin
     rv_close
     all_goals first | exact hc | with_reducible assumption)))

/-! The masks and row offsets of the result's loop for each `x = j / 64 % 5`, closed words. -/

theorem maskA0 : (1024#64 &&& BinOp.ult.eval 18446744073709551612#64 1#64 <<< 4 + 18446744073709551600#64) = 1024#64 := by
  decide +kernel
theorem maskA1 : (2048#64 &&& BinOp.ult.eval 18446744073709551613#64 1#64 <<< 4 + 18446744073709551600#64) = 2048#64 := by
  decide +kernel
theorem maskA2 : (3072#64 &&& BinOp.ult.eval 18446744073709551614#64 1#64 <<< 4 + 18446744073709551600#64) = 3072#64 := by
  decide +kernel
theorem maskA3 : (4096#64 &&& BinOp.ult.eval 18446744073709551615#64 1#64 <<< 4 + 18446744073709551600#64) = 4096#64 := by
  decide +kernel
theorem maskA4 : (5120#64 &&& BinOp.ult.eval 0#64 1#64 <<< 4 + 18446744073709551600#64) = 0#64 := by
  decide +kernel
theorem rowB1 : (1#64 <<< 10 + 18446744073709550592#64 : Word) = 0#64 := by decide +kernel
theorem rowB2 : (2#64 <<< 10 + 18446744073709550592#64 : Word) = 1024#64 := by decide +kernel
theorem rowB3 : (3#64 <<< 10 + 18446744073709550592#64 : Word) = 2048#64 := by decide +kernel
theorem rowB4 : (4#64 <<< 10 + 18446744073709550592#64 : Word) = 3072#64 := by decide +kernel

set_option hygiene false in
/-- One pass of the result's loop from its head: `x = j / 64 % 5` by cases, each to the next head or the exit. -/
macro "lt_iter3" : tactic => `(tactic| (
  have hjl : j < 1600 := by omega
  rv_intro hinv
  rv_sym hp stop [314, 332]
  · rw [xval hjl] at hc ⊢
    have hx : j / 64 % 5 = 0 := by rw [ofNat_inj (by omega) (by decide)] at hc; exact hc
    rw [hx]
    rv_sym hp stop [314, 332]
    rv_sym hp stop [314, 332]
    all_goals (rw [maskA0]; lt_close3)
  · rw [xval hjl] at hc ⊢
    have hx : j / 64 % 5 = 1 ∨ j / 64 % 5 = 2 ∨ j / 64 % 5 = 3 ∨ j / 64 % 5 = 4 := by
      rw [ofNat_inj (by omega) (by decide)] at hc; omega
    rcases hx with hx | hx | hx | hx <;> rw [hx] <;> rv_sym hp stop [314, 332]
    all_goals (first | rw [maskA1, rowB1] | rw [maskA2, rowB2] | rw [maskA3, rowB3] | rw [maskA4, rowB4])
    all_goals lt_close3))

set_option maxHeartbeats 4000000 in
/-- **The result's loop**, from its head with `k + 1` positions to go. -/
theorem loop3 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (ws : List E)
    (hp : p[i]? = some (tmpl L))
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (P : Word) (cap : Nat) (htop : env.stackLimit.toNat + 30816 ≤ top.toNat)
    (hfin : ∀ R M, Exit3 env ws ret top regs m P cap R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 332, ret, top⟩ :: rest, R, M⟩) :
    ∀ k j R M, j + k + 1 = 1600 → Inv3 env ws ret top regs m P cap j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 314, ret, top⟩ :: rest, R, M⟩ := by
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    lt_iter3
  | succ k ih =>
    intro j R M hj hinv
    lt_iter3


/-! ## The return: the header into the result's slot -/

/-- **Three stores into a caller's slot of 24 bytes**: what they keep (the frame's stack and the heap the call
    allocated), the frame with the slot as `Out`, the static data, and what they store. -/
theorem slot3 {env : Env} {m M : MachineState} {top s : Word} (ho : env.Owned m top s 24)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat + 48 ≤ top.toNat)
    (hf : env.Frame top Tactic.F m M) (a b c : Word) :
    let M3 := ((M.setMem s a).setMem (s + 8#64) b).setMem (s + 16#64) c
    (∀ x : Word, env.stackLimit.toNat ≤ x.toNat → x.toNat < top.toNat → M3.getMem x = M.getMem x) ∧
      (∀ x : Word, (env.next m).toNat ≤ x.toNat → x.toNat < (env.next M).toNat → M3.getMem x = M.getMem x) ∧
      env.Frame top (fun y => InRange s Layouts.Vec.byteSize y) m M3 ∧ (env.Static m → env.Static M3) ∧
      env.next M3 = env.next M ∧
      M3.getMem s = a ∧ M3.getMem (s + 8#64) = b ∧ M3.getMem (s + 16#64) = c := by
  intro M3
  have hlay := env.layout
  have hfe := hf.2.1
  have hfm := hf.1
  obtain ⟨hown, hwrap⟩ := ho
  have e8 : (s + 8#64).toNat = s.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (s + 16#64).toNat = s.toNat + 16 := toNat_add_ofNat (by omega)
  -- what lies outside the slot is kept
  have keep : ∀ x : Word, ¬ InRange s 24 x → M3.getMem x = M.getMem x := by
    intro x hx
    have n0 : x ≠ s := fun he => hx (by rw [he]; exact ⟨Nat.le_refl _, by omega⟩)
    have n8 : x ≠ s + 8#64 := fun he => hx (by rw [he]; exact ⟨by omega, by omega⟩)
    have n16 : x ≠ s + 16#64 := fun he => hx (by rw [he]; exact ⟨by omega, by omega⟩)
    simp only [M3]
    rw [MachineState.getMem_setMem_ne n16, MachineState.getMem_setMem_ne n8, MachineState.getMem_setMem_ne n0]
  have hn : env.next M3 = env.next M := keep _ fun h => by unfold InRange at h; rcases hown with h1 | h1 <;> omega
  refine ⟨fun x h1 h2 => keep x fun h => by unfold InRange at h; rcases hown with h1 | h1 <;> omega,
    fun x h1 h2 => keep x fun h => by unfold InRange at h; rcases hown with h1 | h1 <;> omega, ?_, ?_, hn, ?_, ?_, ?_⟩
  · refine ⟨by rw [hn]; exact hfm, by rw [hn]; exact hfe, fun x hx => ?_⟩
    have hxs : ¬ InRange s 24 x := fun h => hx (Or.inr (Or.inr (Or.inr h)))
    rw [keep x hxs]
    refine hf.2.2 x fun hw => hx ?_
    rcases hw with hw | hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr (Or.inl ⟨hw.1, by rw [hn]; exact hw.2⟩)
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact hw.elim
  · intro hs
    refine env.static_frame M M3 (fun x h1 h2 => keep x fun h => by
      unfold InRange at h; rcases hown with h3 | h3 <;> omega) (Tactic.static_of_frame hs hf)
  · have n1 : s ≠ s + 16#64 := fun he => by have := congrArg BitVec.toNat he; omega
    have n2 : s ≠ s + 8#64 := fun he => by have := congrArg BitVec.toNat he; omega
    simp only [M3]
    rw [MachineState.getMem_setMem_ne n1, MachineState.getMem_setMem_ne n2, MachineState.getMem_setMem_eq]
  · have n1 : s + 8#64 ≠ s + 16#64 := fun he => by have := congrArg BitVec.toNat he; omega
    simp only [M3]
    rw [MachineState.getMem_setMem_ne n1, MachineState.getMem_setMem_eq]
  · simp only [M3]; rw [MachineState.getMem_setMem_eq]

/-- The result's elements, read from the buffer the loop filled. -/
theorem result_elems {ws : List E} {M M' : MachineState} {P : Word} (hlen : ws.length = 1600)
    (h : PairsAt M P (fun k => Model.limbs (outE ws k)) 1600) (hP : P.toNat + 25600 < 2 ^ 64)
    (hk : ∀ x : Word, P.toNat ≤ x.toNat → x.toNat < P.toNat + 25600 → M'.getMem x = M.getMem x) :
    ∀ v, Model.linearTransposeRust ws = some v → EListAt M' P (v.map Model.limbs) := by
  intro v hv
  rw [Model.linearTransposeRust_some hlen, Option.some.injEq] at hv
  subst hv
  refine ⟨by simp only [List.length_map, List.length_range, Layouts.E.byteSize]; omega, fun k hk' => ?_⟩
  simp only [List.length_map, List.length_range] at hk'
  have e0 := toNat_elem (a := P) (k := k) (by omega)
  have e8 := toNat_elem8 (a := P) (k := k) (by omega)
  simp only [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize, List.getElem_map, List.getElem_range,
    BitVec.add_zero]
  rw [hk _ (by omega) (by omega), hk _ (by omega) (by omega)]
  exact h k hk'

set_option maxHeartbeats 1000000 in
/-- **The return**: the header into the result's slot, the saved registers back. -/
theorem fin (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (ws : List E)
    (hp : p[i]? = some (tmpl L))
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (P : Word) (cap : Nat) (htop : env.stackLimit.toNat + 30816 ≤ top.toNat)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (ho : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hlen : ws.length = 1600)
    (hk : ∀ r' m', Holds.post env (Post env ws) Out ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩) :
    ∀ R M, Exit3 env ws ret top regs m P cap R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 332, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  rv_intro hinv
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    slot3 ho hnx (by omega) hinv_13 (BitVec.ofNat 64 cap) P 1600#64
  have hs := savedBase_toNat (top := top) (by omega)
  have hsv : ∀ x : Word, top + 18446744073709551568#64 ≤ x → x.toNat < top.toNat → _ := fun x h1 h2 =>
    (k1 x (by rw [BitVec.le_def] at h1; omega) h2).trans (hinv_14 x h1)
  rv_sym hp
  all_goals rw [hinv_22, hinv_23] at *
  have sv : ∀ x, top + 18446744073709551568#64 ≤ x → x.toNat < top.toNat → _ := hsv
  iterate 6
    rw [hsv]
    · simp (disch := first | exact Tactic.add_ne_add (by decide) | fail) only [MachineState.getMem_setMem_ne,
        MachineState.getMem_setMem_eq]
    · first | with_reducible exact BitVec.le_refl _ | (rw [BitVec.le_def, toNat_top (by decide) (by omega), toNat_top (by decide) (by omega)]; omega)
    · rw [toNat_top (by decide) (by omega)]; omega
  · exact k3
  · exact k4 hst
  · intro v hv
    have hvl : v.length = 1600 := by
      rw [Model.linearTransposeRust_some hlen, Option.some.injEq] at hv; subst hv; simp
    have hP : P.toNat + 16 * cap ≤ (env.next M).toNat := hinv_25
    have hlay := env.layout
    have hfe := hinv_17.2.1
    refine ⟨P, cap, ⟨?_, ?_, ?_, ?_, hinv_27, ?_⟩, hinv_24, by rw [k5]; exact hP⟩
    · exact k7
    · simp [vecCap, Layouts.Vec.cap, k6]
    · simp [vecLen, Layouts.Vec.len, hvl, k8]
    · simp only [List.length_map, hvl]; exact hinv_26
    · exact result_elems hlen hinv_21 (by omega) (fun x h1 h2 => k2 x (by omega) (by omega)) v hv

/-! ## Between the column sums and the result: the buffer and its header -/

/-- The header's three stores, then `reserve`, from a frame of the call: the frame, the prologue's stores, `g` and
    the column sums kept, the header as stored. -/
theorem mid_mem {env : Env} {ws : List E} {ret top : Word} {regs : Reg → Word} {m M m1 m3 : MachineState}
    {P : Word} {out : Word → Prop} (htop : env.stackLimit.toNat + 30816 ≤ top.toNat)
    (hf : env.Frame top Tactic.F m M) (hs : Saved ret top regs m M)
    (hg : PairsAt M (top + 18446744073709520824#64) (gF ws) 1600)
    (hc : PairsAt M (top + 18446744073709546424#64) (colsF ws 1600) 320)
    (h1 : env.Frame (top + 18446744073709520800#64) Tactic.F M m1)
    (hP1 : (env.next M).toNat ≤ P.toNat) (hP2 : P.toNat + 25600 = (env.next m1).toNat)
    (h3 : env.Frame (top + 18446744073709520800#64) out
      (((m1.setMem (top + 18446744073709551544#64) 1600#64).setMem (top + 18446744073709551552#64) P).setMem
        (top + 18446744073709551560#64) 0#64) m3)
    (hout : ∀ b, out b → b = top + 18446744073709551544#64 ∨ b = top + 18446744073709551544#64 + 8#64)
    (hcap : m3.getMem (top + 18446744073709551544#64) = 1600#64)
    (hptr : m3.getMem (top + 18446744073709551552#64) = P) :
    Mem3 env ws ret top regs m P 1600 0 m3 ∧ m3.getMem (top + 18446744073709551560#64) = 0#64 := by
  have := top.isLt
  have hlay := env.layout
  have esp := toNat_top (t := top) (c := 18446744073709520800) (by decide) (by omega)
  have eH := toNat_top (t := top) (c := 18446744073709551544) (by decide) (by omega)
  have eH8 := toNat_top (t := top) (c := 18446744073709551552) (by decide) (by omega)
  have eH16 := toNat_top (t := top) (c := 18446744073709551560) (by decide) (by omega)
  have eH8' : (top + 18446744073709551544#64 + 8#64).toNat = top.toNat - 64 := by
    rw [BitVec.toNat_add, eH]; simp only [BitVec.toNat_ofNat]; omega
  have hgb := gBase_toNat (top := top) (by omega)
  have hcb := colsBase_toNat (top := top) (by omega)
  have hsb := savedBase_toNat (top := top) (by omega)
  -- the memory before `reserve`
  set m2 := ((m1.setMem (top + 18446744073709551544#64) 1600#64).setMem (top + 18446744073709551552#64) P).setMem
    (top + 18446744073709551560#64) 0#64 with hm2
  have f2 : env.Frame top Tactic.F m m2 :=
    Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_call hf h1 (by omega))
      (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)
  have f3 : env.Frame top Tactic.F m m3 := f2.trans h3 (by omega) fun b hb => by
    rcases hout b hb with rfl | rfl
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
  -- what `reserve` keeps: its stack's frame, all but the header's two words
  have k3 : ∀ a : Word, (top + 18446744073709520800#64).toNat ≤ a.toNat → a ≠ top + 18446744073709551544#64 →
      a ≠ top + 18446744073709551544#64 + 8#64 → m3.getMem a = m2.getMem a := fun a ha n1 n2 =>
    h3.getMem_above (by omega) ha fun hb => by rcases hout a hb with h | h; exact n1 h; exact n2 h
  have k1 : ∀ a : Word, top + 18446744073709520800#64 ≤ a → m1.getMem a = M.getMem a :=
    Tactic.frame_above h1 (by omega)
  -- the region of the frame above the header's three words, or below them
  have keep : ∀ a : Word, (top + 18446744073709520800#64).toNat ≤ a.toNat →
      (a.toNat < top.toNat - 72 ∨ top.toNat - 48 ≤ a.toNat) → m3.getMem a = M.getMem a := by
    intro a ha hr
    have n1 : a ≠ top + 18446744073709551544#64 := fun he => by rw [he] at hr; omega
    have n2 : a ≠ top + 18446744073709551544#64 + 8#64 := fun he => by rw [he] at hr; omega
    have n3 : a ≠ top + 18446744073709551552#64 := fun he => by rw [he] at hr; omega
    have n4 : a ≠ top + 18446744073709551560#64 := fun he => by rw [he] at hr; omega
    rw [k3 a ha n1 n2, hm2, MachineState.getMem_setMem_ne n4, MachineState.getMem_setMem_ne n3,
      MachineState.getMem_setMem_ne n1, k1 a (by rw [BitVec.le_def]; exact ha)]
  have n16a : top + 18446744073709551560#64 ≠ top + 18446744073709551544#64 := Tactic.add_ne_add (by decide)
  have n16b : top + 18446744073709551560#64 ≠ top + 18446744073709551544#64 + 8#64 := fun he => by
    have := congrArg BitVec.toNat he; omega
  refine ⟨⟨f3, fun a ha => ?_, hg.congr (by omega) fun b hb => keep b (by unfold InRange at hb; omega)
      (by unfold InRange at hb; omega),
    hc.congr (by omega) fun b hb => keep b (by unfold InRange at hb; omega) (by unfold InRange at hb; omega),
    fun k hk => absurd hk (Nat.not_lt_zero _), hcap, hptr, by have := hf.1; omega,
    by have := h3.1; have : (env.next m2).toNat = (env.next m1).toNat := by
         rw [hm2, Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega),
           Env.next_setMem_stack (by omega)]
       omega, by decide, by decide⟩, ?_⟩
  · rw [BitVec.le_def] at ha
    rw [keep a (by omega) (by omega)]; exact hs a (by rw [BitVec.le_def]; exact ha)
  · rw [k3 _ (by omega) n16a n16b, hm2, MachineState.getMem_setMem_eq]

set_option maxHeartbeats 2000000 in
/-- **From the column sums to the result's loop**: the buffer allocated, its header stored, `reserve`, and the
    loop's registers. -/
theorem mid (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (ws : List E)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need nAl nRes nHe : Nat} (hnAl : 30816 + nAl ≤ need)
    (hnRes : 30816 + nRes ≤ need) (hnHe : 30816 + nHe ≤ need)
    (hal : Spec.Runtime.AllocSpec env p L.alloc.idx nAl) (hres : Spec.Runtime.ReserveSpec env 8 16 p L.reserve.idx nRes)
    (hhe : Spec.Runtime.NoReturn env p L.handleError.idx nHe)
    (hmagic : DataRef.Words env L.d_c8_e5d50e4a Gen.Verifier.Keccak.LinearTransposeE.d_c8_e5d50e4a_words)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hsp16 : top.toNat % 16 = 0)
    (hl3 : ∀ P, ∀ k j R M, j + k + 1 = 1600 → Inv3 env ws ret top regs m P 1600 j R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 314, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Exit2 env ws ret top regs m R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 190, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  have htop : env.stackLimit.toNat + 30816 ≤ top.toNat := by omega
  have := top.isLt
  have hlay := env.layout
  have esp := toNat_top (t := top) (c := 18446744073709520800) (by decide) (by omega)
  have eH := toNat_top (t := top) (c := 18446744073709551544) (by decide) (by omega)
  rv_intro hinv
  rv_sym hp stop [314] with [hL] using [hal, hres, hhe]
  rotate_right
  · -- the loop's head
    simp (disch := first | exact Tactic.add_ne_add (by decide) | fail) only [vecLen, vecCap, vecPtr, Layouts.Vec.cap,
      Layouts.Vec.ptr, Layouts.Vec.len, add_ofNat2, Nat.reduceAdd, MachineState.getMem_setMem_ne,
      MachineState.getMem_setMem_eq] at hret3_16 hret3_17
    obtain ⟨hcap, hptr⟩ := hret3_17 (by decide)
    have hmg : m3.getMem (L.d_c8_e5d50e4a.hi + L.d_c8_e5d50e4a.lo) = 0x3333333333333334#64 :=
      DataRef.Words.get0 hmagic hret3_15 (by decide)
    rw [hret3_16, hptr, hmg]
    obtain ⟨h3, -⟩ := mid_mem htop hinv_13 hinv_14 hinv_15 hinv_16 hret1_14 hret1_16 (by simpa using hret1_18)
      hret3_14 (fun b hb => by
        simp only [Spec.Runtime.GrowOut, Spec.Runtime.rvCapAt, Spec.Runtime.rvPtrAt, Layouts.RawVecInner.cap,
          Layouts.RawVecInner.ptr, Lprog.updReg_apply, Tactic.rf] at hb
        rcases hb with h | h
        · left; simpa using h
        · right; exact h) hcap hptr
    apply hl3 (r1 .x10) 1599 0 _ _ (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h3⟩
    rv_close
    · exact h3.1
    · exact h3.2.1
    · simp
    · rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  all_goals try simp (disch := first | exact Tactic.add_ne_add (by decide) | fail) only [Spec.Runtime.rvCapAt,
    Spec.Runtime.rvPtrAt, vecLen, vecCap, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, Layouts.Vec.cap,
    Layouts.Vec.len, Layouts.Vec.byteSize, Layouts.RawVecInner.byteSize, add_ofNat2, Nat.reduceAdd,
    MachineState.getMem_setMem_ne, MachineState.getMem_setMem_eq]
  all_goals first
    | decide
    | (rw [eH]; omega)
    | (refine Or.inr ?_
       unfold Env.Live
       rw [Env.next_setMem_stack (by rw [toNat_top (by decide) (by omega)]; omega),
         Env.next_setMem_stack (by rw [toNat_top (by decide) (by omega)]; omega),
         Env.next_setMem_stack (by rw [toNat_top (by decide) (by omega)]; omega)]
       simp only [BitVec.toNat_ofNat] at hret1_18 ⊢
       omega)

/-! ## The tables -/

/-- **`KECCAK_RHO` at the data reference `d`**, its `u32`s wherever the static data hold. -/
def RhoAt (env : Env) (d : DataRef) : Prop :=
  ∀ M, env.Static M → ∀ k, k < 25 →
    M.getWord32 (d.hi + d.lo + BitVec.ofNat 64 (4 * k)) = BitVec.ofNat 32 (Model.keccakRhoRust.getD k 0)

theorem rho_lt (k : Nat) (hk : k < 25) : Model.keccakRhoRust.getD k 0 < 64 := by
  have : ∀ k, k < 25 → Model.keccakRhoRust.getD k 0 < 64 := by decide
  exact this k hk

theorem pi_lt (k : Nat) (hk : k < 25) : Model.keccakPiRust.getD k 0 < 25 := by
  have : ∀ k, k < 25 → Model.keccakPiRust.getD k 0 < 25 := by decide
  exact this k hk

theorem sext32 {r : Nat} (hr : r < 64) :
    UnOp.eval (UnOp.sext .b4) ((BitVec.ofNat 32 r).zeroExtend 64) = BitVec.ofNat 64 r := by
  have : ∀ r, r < 64 → UnOp.eval (UnOp.sext .b4) ((BitVec.ofNat 32 r).zeroExtend 64) = BitVec.ofNat 64 r := by
    decide +kernel
  exact this r hr

theorem shl_ofNat (k s : Nat) : BitVec.ofNat 64 k <<< s = BitVec.ofNat 64 (2 ^ s * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_comm (2 ^ s), Nat.mod_mul_mod]

theorem rho_load {env : Env} {d : DataRef} {M : MachineState} (h : RhoAt env d) (hs : env.Static M) {k : Nat}
    (hk : k < 25) :
    UnOp.eval (UnOp.sext .b4) (BitVec.zeroExtend 64 (M.getWord32 (d.hi + d.lo + BitVec.ofNat 64 k <<< 2))) =
      BitVec.ofNat 64 (Model.keccakRhoRust.getD k 0) := by
  rw [shl_ofNat, show 2 ^ 2 * k = 4 * k by omega, h M hs k hk, sext32 (rho_lt k hk)]

theorem pi_words : ∀ k, k < 25 → Gen.Verifier.Keccak.LinearTransposeE.d_c200_f4afdee4_words.getD k 0 <<< 6 =
    BitVec.ofNat 64 (64 * Model.keccakPiRust.getD k 0) := by decide +kernel

theorem pi_load {env : Env} {d : DataRef} {M : MachineState}
    (h : DataRef.Words env d Gen.Verifier.Keccak.LinearTransposeE.d_c200_f4afdee4_words) (hs : env.Static M)
    {k : Nat} (hk : k < 25) :
    M.getMem (d.hi + d.lo + BitVec.ofNat 64 k <<< 3) <<< 6 = BitVec.ofNat 64 (64 * Model.keccakPiRust.getD k 0) := by
  have hl : k < Gen.Verifier.Keccak.LinearTransposeE.d_c200_f4afdee4_words.length := by
    simp [Gen.Verifier.Keccak.LinearTransposeE.d_c200_f4afdee4_words]; omega
  rw [shl_ofNat, show 2 ^ 3 * k = 8 * k by omega, h M hs k hl, ← List.getD_eq_getElem _ 0 hl]
  exact pi_words k hk

/-! ## `g`'s fill -/

/-- The index of `w` the code reads for bit `z` of a lane: `(RHO + z) & 63 | PI << 6`, times 16. -/
theorem idx_eq {r z pi : Nat} (hpi : pi < 25) :
    (BitVec.ofNat 64 (r + z) &&& 63#64 ||| BitVec.ofNat 64 (64 * pi)) <<< 4 =
      BitVec.ofNat 64 (16 * (64 * pi + (z + r) % 64)) := by
  have h1 : BitVec.ofNat 64 (r + z) &&& 63#64 = BitVec.ofNat 64 ((r + z) % 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show 63 % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, show (2 : Nat) ^ 6 = 64 from rfl]
    omega
  have h2 : ∀ a, a < 64 → ∀ q, q < 25 →
      BitVec.ofNat 64 a ||| BitVec.ofNat 64 (64 * q) = BitVec.ofNat 64 (a + 64 * q) := by decide +kernel
  rw [h1, h2 _ (Nat.mod_lt _ (by decide)) _ hpi, shl_ofNat]
  congr 1; omega

/-- `g`'s entry at position `64 lane + z`, as the code reads it from `w`. -/
theorem load_g {env : Env} {top : Word} {m M : MachineState} {ws : List E} {w : Word} {lane z : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hx : EListAt m w (ws.map Model.limbs)) (hl : env.Live m w (Layouts.E.byteSize * ws.length))
    (hlen : ws.length = 1600) (hlane : lane < 25) (hz : z < 64) :
    M.getMem (w + BitVec.ofNat 64 (16 * (64 * Model.keccakPiRust.getD lane 0 +
        (z + Model.keccakRhoRust.getD lane 0) % 64))) = (gF ws (64 * lane + z)).1 ∧
      M.getMem (w + BitVec.ofNat 64 (16 * (64 * Model.keccakPiRust.getD lane 0 +
        (z + Model.keccakRhoRust.getD lane 0) % 64)) + 8#64) = (gF ws (64 * lane + z)).2 := by
  have hp := pi_lt lane hlane
  have hj : 64 * Model.keccakPiRust.getD lane 0 + (z + Model.keccakRhoRust.getD lane 0) % 64 < ws.length := by
    have := Nat.mod_lt (z + Model.keccakRhoRust.getD lane 0) (show 64 > 0 by decide); omega
  have e := EListAt.load (j := 64 * Model.keccakPiRust.getD lane 0 + (z + Model.keccakRhoRust.getD lane 0) % 64)
    hf hnx hx (by simpa using hl) (by simpa using hj)
  rw [e.1, e.2]
  have hg : gF ws (64 * lane + z) = Model.limbs (ws[64 * Model.keccakPiRust.getD lane 0 +
      (z + Model.keccakRhoRust.getD lane 0) % 64]'hj) := by
    unfold gF
    rw [Model.transposeG_getD_eq ws (by omega), Model.gIdx, show (64 * lane + z) / 64 = lane by omega,
      show (64 * lane + z) % 64 = z by omega, List.getD_eq_getElem _ _ hj]
  simp only [List.getElem_map, hg, and_self]

theorem start_ofs (t : Word) (c : Nat) : t + BitVec.ofNat 64 c = t + BitVec.ofNat 64 c + BitVec.ofNat 64 (16 * 0) := by
  rw [Nat.mul_zero]; exact (BitVec.add_zero _).symm

theorem start_ofs8 (t : Word) (c : Nat) :
    t + BitVec.ofNat 64 (c + 8) = t + BitVec.ofNat 64 c + BitVec.ofNat 64 (16 * 0) + 8#64 := by
  rw [Nat.mul_zero, ← start_ofs, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem succ_ofNat2 (a b : Nat) : BitVec.ofNat 64 (a + b) + 1#64 = BitVec.ofNat 64 (a + (b + 1)) := by
  rw [BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem step_ptr2 (q : Word) (a b : Nat) :
    q + BitVec.ofNat 64 (16 * (a + b)) + 24#64 = q + BitVec.ofNat 64 (16 * (a + (b + 1))) + 8#64 :=
  step_ptr q (a + b)

theorem dec_ofNat {z : Nat} (hz : z < 64) :
    BitVec.ofNat 64 (64 - z) + 18446744073709551615#64 = BitVec.ofNat 64 (64 - (z + 1)) := by
  rw [show 64 - z = 64 - (z + 1) + 1 by omega, BitVec.ofNat_add, BitVec.add_assoc,
    show BitVec.ofNat 64 1 + 18446744073709551615#64 = 0#64 by decide +kernel, BitVec.add_zero]

theorem lane_ptr (q : Word) (lane : Nat) :
    q + BitVec.ofNat 64 (16 * (64 * lane)) + 1032#64 = q + BitVec.ofNat 64 (16 * (64 * (lane + 1) + 0)) + 8#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  congr 2

theorem lane_ptr' (q : Word) (lane : Nat) :
    q + BitVec.ofNat 64 (16 * (64 * lane)) + 1032#64 = q + BitVec.ofNat 64 (16 * (64 * (lane + 1))) + 8#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  congr 2


/-- One position of `g`'s fill on memory. -/
theorem loop1_mem {env : Env} {ws : List E} {ret top : Word} {regs : Reg → Word} {m M : MachineState} {k : Nat}
    (htop : env.stackLimit.toNat + 30816 ≤ top.toNat) (hk : k < 1600) (hst : env.Static m)
    (hf : env.Frame top Tactic.F m M) (hs : Saved ret top regs m M)
    (hg : PairsAt M (top + 18446744073709520824#64) (gF ws) k) :
    let M' := (M.setMem (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * k)) (gF ws k).1).setMem
      (top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * k) + 8#64) (gF ws k).2
    env.Frame top Tactic.F m M' ∧ Saved ret top regs m M' ∧
      PairsAt M' (top + 18446744073709520824#64) (gF ws) (k + 1) ∧ env.Static M' ∧
      (env.next M').toNat ≤ env.heapEnd.toNat := by
  intro M'
  have := top.isLt
  have hgb := gBase_toNat (top := top) (by omega)
  have e0 := toNat_elem (a := top + 18446744073709520824#64) (k := k) (by omega)
  have e8 := toNat_elem8 (a := top + 18446744073709520824#64) (k := k) (by omega)
  obtain ⟨h1, h2⟩ := frame_saved2 (v := (gF ws k).1) (w := (gF ws k).2) hf hs (by omega)
    (x := top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * k))
    (y := top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * k) + 8#64) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  exact ⟨h1, h2, hg.push (by omega), Tactic.static_of_frame hst h1, h1.2.1⟩

theorem alignToDword_self {a : Word} (h : a.toNat % 8 = 0) : alignToDword a = a := by
  apply BitVec.eq_of_toNat_eq; rw [toNat_alignToDword]; omega

/-- **A `memset` of the frame below the prologue's stores**: the frame and those stores kept, and every word of the
    frame outside the range. -/
theorem memset_frame {env : Env} {ret top : Word} {regs : Reg → Word} {m M m2 : MachineState} {a : Word} {len : Nat}
    {out : Word → Prop} (htop : env.stackLimit.toNat + 30816 ≤ top.toNat) (hf : env.Frame top Tactic.F m M)
    (hs : Saved ret top regs m M) (h2 : env.Frame (top + 18446744073709520800#64) out M m2)
    (hout : ∀ b, out b → InRange a len b) (ha : (top + 18446744073709520800#64).toNat ≤ a.toNat)
    (ha' : a.toNat + len ≤ top.toNat - 48) :
    env.Frame top Tactic.F m m2 ∧ Saved ret top regs m m2 ∧
      ∀ b : Word, (top + 18446744073709520800#64).toNat ≤ b.toNat → ¬ InRange a len b → m2.getMem b = M.getMem b := by
  have := top.isLt
  have esp := toNat_top (t := top) (c := 18446744073709520800) (by decide) (by omega)
  have hsb := savedBase_toNat (top := top) (by omega)
  have keep : ∀ b : Word, (top + 18446744073709520800#64).toNat ≤ b.toNat → ¬ InRange a len b →
      m2.getMem b = M.getMem b := fun b hb hn => h2.getMem_above (by omega) hb fun ho => hn (hout b ho)
  refine ⟨hf.trans h2 (by omega) fun b hb => ?_, fun b hb => ?_, keep⟩
  · have := hout b hb; unfold InRange at this; exact Or.inl ⟨by omega, by omega⟩
  · rw [BitVec.le_def, hsb] at hb
    rw [keep b (by omega) (fun h => by unfold InRange at h; omega)]
    exact hs b (by rw [BitVec.le_def, hsb]; exact hb)

/-- **A doubleword whose eight bytes are zero** is zero, at an aligned address. -/
theorem getMem_eq_zero {M : MachineState} {a : Word} (ha : a.toNat % 8 = 0) (ha' : a.toNat + 8 < 2 ^ 64)
    (h : ∀ k, k < 8 → M.getByte (a + BitVec.ofNat 64 k) = 0#8) : M.getMem a = 0#64 := by
  have e : ∀ k, k < 8 → extractByte (M.getMem a) k = 0#8 := fun k hk => by
    have := h k hk
    have hn : (a + BitVec.ofNat 64 k).toNat = a.toNat + k := toNat_add_ofNat (by omega)
    have hal : alignToDword (a + BitVec.ofNat 64 k) = a := by
      apply BitVec.eq_of_toNat_eq; rw [toNat_alignToDword, hn]; omega
    simpa [MachineState.getByte, hal, byteOffset_eq_toNat_mod, hn, Nat.add_mod, ha, Nat.mod_eq_of_lt hk] using this
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun b => BitVec.getLsbD b (i % 8)) (e (i / 8) (by omega))
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_zero] at this
  simp only [BitVec.getLsbD_zero]
  rw [show i = i / 8 * 8 + i % 8 by omega]
  simpa [Nat.mod_lt _ (show 8 > 0 by decide)] using this

/-- `memset` of the column sums: they read zero, which is the column sums after no position. -/
theorem memset_cols {env : Env} {ws : List E} {ret top : Word} {regs : Reg → Word} {m M m2 : MachineState}
    {out : Word → Prop} (htop : env.stackLimit.toNat + 30816 ≤ top.toNat) (htal : top.toNat % 8 = 0)
    (hf : env.Frame top Tactic.F m M) (hs : Saved ret top regs m M)
    (hg : PairsAt M (top + 18446744073709520824#64) (gF ws) 1600)
    (h2 : env.Frame (top + 18446744073709520800#64) out M m2)
    (hout : ∀ b, out b → InRange (top + 18446744073709546424#64) 5120 b)
    (hz : ∀ k, k < 5120 → m2.getByte (top + 18446744073709546424#64 + BitVec.ofNat 64 k) = 0#8) :
    env.Frame top Tactic.F m m2 ∧ Saved ret top regs m m2 ∧
      PairsAt m2 (top + 18446744073709520824#64) (gF ws) 1600 ∧
      PairsAt m2 (top + 18446744073709546424#64) (colsF ws 0) 320 := by
  have := top.isLt
  have esp := toNat_top (t := top) (c := 18446744073709520800) (by decide) (by omega)
  have hgb := gBase_toNat (top := top) (by omega)
  have hcb := colsBase_toNat (top := top) (by omega)
  obtain ⟨f2, s2, k2⟩ := memset_frame htop hf hs h2 hout (by omega) (by omega)
  refine ⟨f2, s2, hg.congr (by omega) fun b hb => k2 b (by unfold InRange at hb; omega)
    (fun h => by unfold InRange at h hb; omega), fun c hc => ?_⟩
  have h0 : colsF ws 0 c = (0#64, 0#64) := by
    unfold colsF; rw [Model.colsUpTo_zero, Model.limbs_zero]; rfl
  rw [h0]
  have e0 := toNat_elem (a := top + 18446744073709546424#64) (k := c) (by omega)
  have zero : ∀ o, o < 5120 → o % 8 = 0 → m2.getMem (top + 18446744073709546424#64 + BitVec.ofNat 64 o) = 0#64 := by
    intro o ho ho8
    have eo := toNat_elem (a := top + 18446744073709546424#64) (k := o / 16) (by omega)
    refine getMem_eq_zero (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)
      fun k hk => ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact hz (o + k) (by omega)
  refine ⟨zero (16 * c) (by omega) (by omega), ?_⟩
  have := zero (16 * c + 8) (by omega) (by omega)
  rwa [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc] at this

/-- `g`'s fill's invariant at the inner head, at bit `z` of lane `lane`. -/
def Inv1 (env : Env) (ws : List E) (L : Link) (ret top : Word) (regs : Reg → Word) (m : MachineState)
    (lane z : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  Base env ret top regs m R M ∧ R .x9 = regs .x11 ∧
    R .x12 = L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo ∧ R .x13 = L.d_c100_179d68cc.hi + L.d_c100_179d68cc.lo ∧
    R .x14 = BitVec.ofNat 64 (lane + 1) ∧
    R .x11 = top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * (64 * lane)) + 8#64 ∧
    R .x16 = BitVec.ofNat 64 (64 * Model.keccakPiRust.getD lane 0) ∧
    R .x15 = BitVec.ofNat 64 (Model.keccakRhoRust.getD lane 0 + z) ∧ R .x17 = BitVec.ofNat 64 (64 - z) ∧
    R .x5 = top + 18446744073709520824#64 + BitVec.ofNat 64 (16 * (64 * lane + z)) + 8#64 ∧
    PairsAt M (top + 18446744073709520824#64) (gF ws) (64 * lane + z)

set_option hygiene false in
/-- One bit of `g`'s fill from the inner head: the read from `w`, the two stores, and the inner head again, the
    outer head and on to the inner one, or the column sums' head after `memset`. -/
macro "lt_iter1" : tactic => `(tactic| (
  have hlane : lane < 25 := by omega
  have hkn : 64 * lane + z < 1600 := by omega
  rv_intro hinv
  obtain ⟨f1, f2, f3, f4, f5⟩ := loop1_mem htop hkn hst hinv_13 hinv_14 hinv_24
  have := top.isLt
  have hg := load_g hinv_13 hnx hx hl hlen hlane hz
  rv_sym hp stop [154] with [hL] using [hms, hpb]
  all_goals (try rw [idx_eq (pi_lt lane hlane)] at *)
  all_goals (try rw [hg.1, hg.2] at *)
  all_goals first
    | with_reducible exact f4
    | with_reducible exact f5
    | (rw [colsBase_toNat (by omega)]; simp only [BitVec.toNat_ofNat]; omega)
    | (have hz1 : z + 1 < 64 := by rw [dec_ofNat hz, ofNat_inj (by omega) (by omega)] at hc; omega
       first
       | (exfalso; omega)
       | (apply ih lane (z + 1) _ _ (by omega) hz1
          rv_close
          all_goals
            first
            | with_reducible exact f1
            | with_reducible exact f2
            | (rw [← Nat.add_assoc]; exact f3)
            | rw [succ_ofNat2]
            | rw [dec_ofNat hz]
            | rw [step_ptr2]))
    | (have hl1 : lane + 1 < 25 := by rw [ofNat_inj (by omega) (by omega)] at hc; omega
       have hz63 : z = 63 := by rw [dec_ofNat hz, ofNat_inj (by omega) (by omega)] at hc_2; omega
       first
       | (exfalso; omega)
       | (rv_sym hp stop [78] with [hL] using [hms, hpb]
          rw [pi_load hpi f4 hl1, rho_load hrho f4 hl1]
          apply ih (lane + 1) 0 _ _ (by omega) (by omega)
          rv_close
          all_goals
            first
            | with_reducible exact f2
            | rw [succ_ofNat]
            | (rw [lane_ptr]; done)
            | (rw [lane_ptr']; done)
            | rfl
            | (rw [show 64 * (lane + 1) + 0 = 64 * lane + z + 1 by omega]; exact f3)))
    | (have hl24 : lane = 24 := by rw [ofNat_inj (by omega) (by omega)] at hc; omega
       have hz63 : z = 63 := by rw [dec_ofNat hz, ofNat_inj (by omega) (by omega)] at hc_2; omega
       first
       | (exfalso; omega)
       | (obtain ⟨g1, g2, g3, g4⟩ := memset_cols (ws := ws) htop htal f1 f2
            (by rw [show (1600 : Nat) = 64 * lane + z + 1 by omega]; exact f3) hret2_14
            (fun b hb => by
              simp only [Spec.Runtime.CopyOut, Spec.Runtime.DwordsOf, Lprog.updReg_apply, Tactic.rf,
                reduceCtorEq, ite_false] at hb
              rw [alignToDword_self hcal, hcal] at hb
              exact hb)
            (fun k hk => (hret2_17 k (by simpa using hk)).trans (by decide))
          apply hl2
          refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g1, g2⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g3, g4⟩
          all_goals rv_close
          · exact start_ofs top 18446744073709546424
          · exact start_ofs8 top 18446744073709546424
          · exact start_ofs8 top 18446744073709520824))))

set_option maxHeartbeats 4000000 in
theorem loop1 (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (ws : List E)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need nMs nPb : Nat} (hnMs : 30816 + nMs ≤ need)
    (hnPb : 30816 + nPb ≤ need)
    (hms : Spec.Runtime.MemsetSpec env p L.memset.idx nMs) (hpb : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx nPb)
    (hpi : DataRef.Words env L.d_c200_f4afdee4 Gen.Verifier.Keccak.LinearTransposeE.d_c200_f4afdee4_words)
    (hrho : RhoAt env L.d_c100_179d68cc)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ top.toNat)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hsp16 : top.toNat % 16 = 0)
    (htal : top.toNat % 8 = 0)
    (hx : EListAt m (regs .x11) (ws.map Model.limbs)) (hl : env.Live m (regs .x11) (Layouts.E.byteSize * ws.length))
    (hlen : ws.length = 1600)
    (hl2 : ∀ R M, Inv2 env ws ret top regs m 0 R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 154, ret, top⟩ :: rest, R, M⟩) :
    ∀ k lane z R M, 64 * lane + z + k + 1 = 1600 → z < 64 → Inv1 env ws L ret top regs m lane z R M →
      rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  have htop : env.stackLimit.toNat + 30816 ≤ top.toNat := by omega
  have hcal : (top + 18446744073709546424#64).toNat % 8 = 0 := by
    rw [colsBase_toNat (by omega)]; omega
  intro k
  induction k with
  | zero =>
    intro lane z R M hk hz hinv
    lt_iter1
  | succ k ih =>
    intro lane z R M hk hz hinv
    lt_iter1


theorem rho_load0 {env : Env} {d : DataRef} {M : MachineState} (h : RhoAt env d) (hs : env.Static M) :
    UnOp.eval (UnOp.sext .b4) (BitVec.zeroExtend 64 (M.getWord32 (d.hi + d.lo))) =
      BitVec.ofNat 64 (Model.keccakRhoRust.getD 0 0) := by
  have := h M hs 0 (by decide)
  rw [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  rw [this]; exact sext32 (rho_lt 0 (by decide))

set_option maxHeartbeats 4000000 in
/-- **`linear_transpose::<E>` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need nMs nAl nRes nPb nAf nHe : Nat} (hnMs : 30816 + nMs ≤ need) (hnAl : 30816 + nAl ≤ need)
    (hnRes : 30816 + nRes ≤ need) (hnPb : 30816 + nPb ≤ need) (hnAf : 30816 + nAf ≤ need)
    (hnHe : 30816 + nHe ≤ need)
    (hms : Spec.Runtime.MemsetSpec env p L.memset.idx nMs) (hal : Spec.Runtime.AllocSpec env p L.alloc.idx nAl)
    (hres : Spec.Runtime.ReserveSpec env 8 16 p L.reserve.idx nRes)
    (hpb : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx nPb)
    (haf : Spec.Runtime.NoReturn env p L.assertFailedUsizeUsize.idx nAf)
    (hhe : Spec.Runtime.NoReturn env p L.handleError.idx nHe)
    (hpi : DataRef.Words env L.d_c200_f4afdee4 Gen.Verifier.Keccak.LinearTransposeE.d_c200_f4afdee4_words)
    (hrho : RhoAt env L.d_c100_179d68cc)
    (hmagic : DataRef.Words env L.d_c8_e5d50e4a Gen.Verifier.Keccak.LinearTransposeE.d_c8_e5d50e4a_words) :
    spec env p i need := by
  intro ws
  rv_auto hp with [hL] using [hms, hal, hres, hpb, haf, hhe]
  all_goals have htop : env.stackLimit.toNat + 30816 ≤ top.toNat := by omega
  all_goals have := top.isLt
  · rw [toNat_top (by decide) (by omega)]; simp only [BitVec.toNat_ofNat]; omega
  have hlen : ws.length = 1600 := by
    have h7 := hpre_7.1
    simp only [List.length_map, Layouts.E.byteSize] at h7 hc
    exact (ofNat_inj (by omega) (by decide)).1 hc
  have hlay := env.layout
  rw [hpre_2] at hpre_9 hpre_11
  -- the prologue's stores, then `g`'s `memset`
  have f0 : env.Frame top Tactic.F m ((((((m.setMem (top + 18446744073709551608#64) ret).setMem
      (top + 18446744073709551600#64) (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9)).setMem
      (top + 18446744073709551584#64) (regs .x18)).setMem (top + 18446744073709551576#64) (regs .x19)).setMem
      (top + 18446744073709551568#64) (regs .x20)) := by
    refine Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
      (Tactic.frame_store (Tactic.frame_refl hpre_5) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_ <;>
      rw [toNat_top (by decide) (by omega)] <;> omega
  obtain ⟨f1, s1, -⟩ := memset_frame (ret := ret) (regs := regs) htop f0 (fun a _ => rfl) hret2_14
    (a := top + 18446744073709520824#64) (len := 25600)
    (fun b hb => by
      simp only [Spec.Runtime.CopyOut, Spec.Runtime.DwordsOf, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
        ite_false] at hb
      have hal8 : (top + 18446744073709520824#64).toNat % 8 = 0 := by rw [gBase_toNat (by omega)]; omega
      rw [alignToDword_self hal8, hal8] at hb
      exact hb)
    (by rw [toNat_top (by decide) (by omega), gBase_toNat (by omega)]; omega)
    (by rw [gBase_toNat (by omega)]; omega)
  rv_sym hp stop [78] with [hL] using [hms, hpb]
  rw [rho_load0 hrho hret2_15]
  have h3 := fun P => loop3 env p i L ws hp P 1600 htop
    (fin env p i L ws hp P 1600 htop hpre_4 hpre_5 ⟨hpre_9, hpre_10⟩ hlen hk)
  have h2 := mid env p i L ws hp hL hnAl hnRes hnHe hal hres hhe hmagic hpre_3 hpre_4 hpre_5 (by assumption) h3
  have h1 := loop2 env p i L ws hp htop h2
  refine loop1 env p i L ws hp hL hnMs hnPb hms hpb hpi hrho hpre_3 hpre_4 hpre_5 (by assumption) hpre_11 hpre_7 hpre_8 hlen
    (fun R M h => h1 1599 0 R M (by omega) h) 1599 0 0 _ _ (by omega) (by omega) ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, f1, s1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  all_goals rv_close
  · exact start_ofs8 top 18446744073709520824
  · decide +kernel
  · rfl
  · exact start_ofs8 top 18446744073709520824

end Rv64mc.Proof.Keccak.LinearTranspose
