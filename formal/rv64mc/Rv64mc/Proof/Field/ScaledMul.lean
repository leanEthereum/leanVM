/-
  Rv64mc.Proof.Field.ScaledMul

  `Scaled::mul` keeps its contract (`Spec.Field.Scaled.mulSpec`), over any program holding its template, from the
  contract of `panic_bounds_check` (which does not return). The code checks and looks up the first limb's 11 windows
  unrolled, then loops over the second limb's (head: instruction 238). The indices are `Model.mulStep`'s (`idx`, as
  the code computes them: `win*`); the entries are read from the memory at the head (`rd`), and are the table's
  where the frame keeps it (`rd_eq`), which the bounds checks allow.
-/

import Rv64mc.Spec.Field.Scaled
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Core.ReprLemmas
import Rv64mc.Proof.Field.U128
import Rv64mc.Gen.Tmpl.Verifier.Field.Scaled.Mul
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.ScaledMul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field.Scaled Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.Scaled.Mul (Link tmpl)

/-! ## The table indices -/

/-- The index of window `w` of limb `t`, as `Model.mulStep` computes it (its counter is `11 t + w`). -/
def idx (t w : Nat) (c : Word) : Nat := (11 * t + w) <<< 6 ||| (c >>> (6 * w)).toNat % (1 <<< 6)

theorem idx_eq (t w : Nat) (c : Word) : idx t w c = 64 * (11 * t + w) + (c >>> (6 * w)).toNat % 64 := by
  have h : (c >>> (6 * w)).toNat % 64 < 2 ^ 6 := Nat.mod_lt _ (by decide)
  rw [idx, show (1 <<< 6 : Nat) = 64 from rfl, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]
  ring

theorem idx_lt (t w : Nat) (c : Word) (ht : t < 2) (hw : w < 11) : idx t w c < 1408 := by
  rw [idx_eq]; have := Nat.mod_lt (c >>> (6 * w)).toNat (show 0 < 64 by decide); omega

/-- A sign extension of the low word of a small value keeps it. -/
theorem sext32_small (v : Word) (h : v.toNat < 2 ^ 31) : (UnOp.sext Width.b4).eval v = v := by
  have hm : (v.setWidth 32).msb = false := by
    rw [BitVec.msb_setWidth'', BitVec.getLsbD, Nat.testBit_eq_false_of_lt h]
  apply BitVec.eq_of_toNat_eq
  simp only [UnOp.eval, Width.bits]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  omega

theorem shl_shr (c : Word) (w k : Nat) (hk : k + 6 * w = 58) : c <<< k >>> 58 = (c >>> (6 * w)) &&& 63#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm := (by decide +kernel : ∀ j : Fin 64, (63#64).getLsbD j = decide (j.val < 6)) ⟨i, hi⟩
  simp only at hm
  rw [BitVec.getLsbD_and, hm, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 6
  · simp [h, show 58 + i < 64 by omega, show ¬ 58 + i < k by omega, show 58 + i - k = 6 * w + i by omega]
  · simp [h, show ¬ 58 + i < 64 by omega]

theorem toNat_and63 (x : Word) : (x &&& 63#64).toNat = x.toNat % 64 := by
  rw [BitVec.toNat_and, show (63#64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem ofNat_shl4 (j : Nat) (_h : j < 2 ^ 60) : BitVec.ofNat 64 j <<< 4 = BitVec.ofNat 64 (16 * j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

/-- Window `w` (from 1 to 9) of the first limb, as the code computes its index. -/
theorem win (c : Word) (w k o : Nat) (hw : w < 11) (hk : k + 6 * w = 58) (ho : o = 64 * w) :
    (UnOp.sext Width.b4).eval (c <<< k >>> 58 + BitVec.ofNat 64 o) = BitVec.ofNat 64 (idx 0 w c) := by
  have e : c <<< k >>> 58 + BitVec.ofNat 64 o = BitVec.ofNat 64 (idx 0 w c) := by
    apply BitVec.eq_of_toNat_eq
    rw [shl_shr c w k hk, BitVec.toNat_add, toNat_and63, BitVec.toNat_ofNat, BitVec.toNat_ofNat, idx_eq]
    have := Nat.mod_lt (c >>> (6 * w)).toNat (show 0 < 64 by decide); omega
  rw [e, sext32_small]
  have := idx_lt 0 w c (by decide) hw
  rw [BitVec.toNat_ofNat]; omega

/-- Window `0` of the first limb. -/
theorem win0 (c : Word) : c &&& 63#64 = BitVec.ofNat 64 (idx 0 0 c) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and63, BitVec.toNat_ofNat, idx_eq]
  have := Nat.mod_lt c.toNat (show 0 < 64 by decide); simp; omega

/-- Window `10` of the first limb. -/
theorem win10 (c : Word) : (UnOp.sext Width.b4).eval (c >>> 60 + 640#64) = BitVec.ofNat 64 (idx 0 10 c) := by
  have e : c >>> 60 + 640#64 = BitVec.ofNat 64 (idx 0 10 c) := by
    apply BitVec.eq_of_toNat_eq
    have h1 : (c >>> 60).toNat < 16 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := c.isLt; omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, idx_eq]
    simp only [show 6 * 10 = 60 from rfl]
    omega
  rw [e, sext32_small]
  have := idx_lt 0 10 c (by decide) (by decide)
  rw [BitVec.toNat_ofNat]; omega

/-- Window `j` of the second limb, in the loop. -/
theorem winLoop (c : Word) (j : Nat) (hj : j < 11) :
    BitVec.ofNat 64 (704 + 64 * j) + (c >>> (BitVec.ofNat 64 (6 * j) &&& 63#64).toNat &&& 63#64) =
      BitVec.ofNat 64 (idx 1 j c) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and63 (BitVec.ofNat 64 (6 * j)), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 6 * j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 6 * j < 64 by omega), BitVec.toNat_add, toNat_and63, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, idx_eq]
  have := Nat.mod_lt (c >>> (6 * j)).toNat (show 0 < 64 by decide); omega

theorem shl_idx (t w : Nat) (c : Word) (ht : t < 2) (hw : w < 11) :
    BitVec.ofNat 64 (idx t w c) <<< 4 = BitVec.ofNat 64 (16 * idx t w c) :=
  ofNat_shl4 _ (by have := idx_lt t w c ht hw; omega)

theorem lt_of_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : BitVec.ofNat 64 a < BitVec.ofNat 64 b) :
    a < b := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h; exact h

/-! ## The sums -/

/-- Entry `j`'s limbs read from `M`, for the slice at `q`. -/
def rd (M : MachineState) (q : Word) (j : Nat) : Model.Limbs :=
  (M.getMem (q + BitVec.ofNat 64 (16 * j)), M.getMem (q + BitVec.ofNat 64 (16 * j) + 8#64))

/-- The sum from `acc` of the entries `f` gives the first `k` windows of limb `t`. -/
def part (f : Nat → Model.Limbs) (t : Nat) (c : Word) (k : Nat) (acc : Model.Limbs) : Model.Limbs :=
  (List.range k).foldl (fun a w => Model.eAdd a (f (idx t w c))) acc

theorem part_zero (f : Nat → Model.Limbs) (t : Nat) (c : Word) (acc : Model.Limbs) : part f t c 0 acc = acc := rfl

theorem part_succ (f : Nat → Model.Limbs) (t : Nat) (c : Word) (k : Nat) (acc : Model.Limbs) :
    part f t c (k + 1) acc = Model.eAdd (part f t c k acc) (f (idx t k c)) := by
  simp [part, List.range_succ, List.foldl_append]

theorem part_congr {f g : Nat → Model.Limbs} {t : Nat} {c : Word} {k : Nat} (acc : Model.Limbs)
    (h : ∀ w < k, f (idx t w c) = g (idx t w c)) : part f t c k acc = part g t c k acc := by
  induction k with
  | zero => rfl
  | succ k ih => rw [part_succ, part_succ, ih (fun w hw => h w (by omega)), h k (by omega)]

theorem mulStep_fold (tabs : List Model.Limbs) (c : Word) (t k : Nat) (acc : Model.Limbs) :
    (List.range k).foldl (Model.mulStep tabs c) (acc, 11 * t) =
      (part (fun j => tabs.getD j Model.eZero) t c k acc, 11 * t + k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih]; simp [Model.mulStep, part_succ, idx]; rfl

theorem scaledMul_eq (tabs : List Model.Limbs) (c0 c1 : Word) :
    Model.scaledMul tabs (c0, c1) = part (fun j => tabs.getD j Model.eZero) 1 c1 11
      (part (fun j => tabs.getD j Model.eZero) 0 c0 11 Model.eZero) := by
  simp only [Model.scaledMul, List.foldl_cons, List.foldl_nil]
  rw [show ((Model.eZero, 0) : Model.Limbs × Nat) = (Model.eZero, 11 * 0) from rfl, mulStep_fold,
    show 11 * 0 + 11 = 11 * 1 from rfl, mulStep_fold]

theorem rd_eq {env : Env} {top : Word} {m M : MachineState} {q : Word} {tabs : List Model.Limbs} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (he : EListAt m q tabs)
    (hl : env.Live m q (Layouts.E.byteSize * tabs.length)) (hj : j < tabs.length) :
    rd M q j = tabs.getD j Model.eZero := by
  have h := EListAt.load hf hnx he hl hj
  rw [rd, h.1, h.2, List.getD_eq_getElem _ _ hj]

theorem sum_eq {env : Env} {top : Word} {m M : MachineState} {q c0 c1 : Word} {tabs : List Model.Limbs}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (he : EListAt m q tabs)
    (hl : env.Live m q (Layouts.E.byteSize * tabs.length)) (hb0 : ∀ w < 11, idx 0 w c0 < tabs.length)
    (hb1 : ∀ w < 11, idx 1 w c1 < tabs.length) :
    Model.scaledMul tabs (c0, c1) = part (rd M q) 1 c1 11 (part (rd M q) 0 c0 11 Model.eZero) := by
  rw [scaledMul_eq, part_congr (t := 0) _ (fun w hw => (rd_eq hf hnx he hl (hb0 w hw)).symm),
    part_congr (t := 1) _ (fun w hw => (rd_eq hf hnx he hl (hb1 w hw)).symm)]

/-- One pass of the loop: window `j` of the second limb read and added. -/
theorem body_val (M : MachineState) (q c1 : Word) (acc : Model.Limbs) (j : Nat) (hj : j < 11) :
    (M.getMem (q + (BitVec.ofNat 64 (704 + 64 * j) + (c1 >>> (BitVec.ofNat 64 (6 * j) &&& 63#64).toNat &&& 63#64)) <<<
        4) ^^^ (part (rd M q) 1 c1 j acc).1,
      M.getMem (q + (BitVec.ofNat 64 (704 + 64 * j) + (c1 >>> (BitVec.ofNat 64 (6 * j) &&& 63#64).toNat &&& 63#64)) <<<
        4 + 8#64) ^^^ (part (rd M q) 1 c1 j acc).2) = part (rd M q) 1 c1 (j + 1) acc := by
  rw [winLoop _ j hj, shl_idx 1 j _ (by decide) hj, part_succ, Model.eAdd, rd, BitVec.xor_comm (M.getMem _),
    BitVec.xor_comm (M.getMem _)]

theorem step16 (j : Nat) : BitVec.ofNat 64 (6 * j) + 6#64 = BitVec.ofNat 64 (6 * (j + 1)) := by
  rw [show 6 * (j + 1) = 6 * j + 6 by omega, BitVec.ofNat_add]

theorem step17 (j : Nat) : BitVec.ofNat 64 (704 + 64 * j) + 64#64 = BitVec.ofNat 64 (704 + 64 * (j + 1)) := by
  rw [show 704 + 64 * (j + 1) = (704 + 64 * j) + 64 by omega, BitVec.ofNat_add (704 + 64 * j) 64]

theorem end17 {j : Nat} (hj : j < 11) : BitVec.ofNat 64 (704 + 64 * j) + 64#64 = 1408#64 ↔ j = 10 := by
  rw [step17, ← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- The bound the loop's check gives. -/
theorem bound_j {len : Nat} (hlen : len < 2 ^ 64) {c1 : Word} {j : Nat} (hj : j < 11)
    (h : BitVec.ofNat 64 (704 + 64 * j) + (c1 >>> (BitVec.ofNat 64 (6 * j) &&& 63#64).toNat &&& 63#64) <
      BitVec.ofNat 64 len) : idx 1 j c1 < len := by
  rw [winLoop _ j hj] at h
  exact lt_of_ofNat (by have := idx_lt 1 j c1 (by decide) hj; omega) hlen h

theorem len_lt {env : Env} {m : MachineState} {q : Word} {tabs : List Model.Limbs}
    (hl : env.Live m q (Layouts.E.byteSize * tabs.length)) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    tabs.length < 2 ^ 64 := by
  have := env.layout; have := env.stackLimit.isLt; unfold Env.Live at hl; simp only [Layouts.E.byteSize] at hl; omega

/-- The first limb's eleven entries in the order the code XORs them. -/
theorem xor11 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) :
    a10 ^^^ (a9 ^^^ (a8 ^^^ a7)) ^^^ (a6 ^^^ (a5 ^^^ a4) ^^^ (a3 ^^^ a2 ^^^ (a1 ^^^ a0))) =
      a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5 ^^^ a6 ^^^ a7 ^^^ a8 ^^^ a9 ^^^ a10 := by
  ac_rfl

/-! ## The loop -/

/-- The loop's head after `j` windows of the second limb: the counters, the sum so far read from `M`, the saved
    registers it keeps, the frame and the prologue's stores. -/
def Inv (env : Env) (tabs : List Model.Limbs) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x1 = ret ∧ R .x2 = top + 0xffffffffffffffb0#64 ∧ R .x10 = regs .x10 ∧
    R .x11 = BitVec.ofNat 64 tabs.length ∧ R .x13 = regs .x13 ∧ R .x5 = 1408#64 ∧
    R .x16 = BitVec.ofNat 64 (6 * j) ∧ R .x17 = BitVec.ofNat 64 (704 + 64 * j) ∧
    R .x12 = (part (rd M (regs .x10)) 1 (regs .x13) j (part (rd M (regs .x10)) 0 (regs .x12) 11 Model.eZero)).1 ∧
    R .x15 = (part (rd M (regs .x10)) 1 (regs .x13) j (part (rd M (regs .x10)) 0 (regs .x12) 11 Model.eZero)).2 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    env.Frame top Tactic.F m M ∧
    ∀ a, top + 0xffffffffffffffb0#64 ≤ a → M.getMem a =
      ((((((((((m.setMem (top + 0xfffffffffffffff8#64) (regs .x8)).setMem (top + 0xfffffffffffffff0#64)
        (regs .x9)).setMem (top + 0xffffffffffffffe8#64) (regs .x18)).setMem (top + 0xffffffffffffffe0#64)
        (regs .x19)).setMem (top + 0xffffffffffffffd8#64) (regs .x20)).setMem (top + 0xffffffffffffffd0#64)
        (regs .x21)).setMem (top + 0xffffffffffffffc8#64) (regs .x22)).setMem (top + 0xffffffffffffffc0#64)
        (regs .x23)).setMem (top + 0xffffffffffffffb8#64) (regs .x24)).setMem (top + 0xffffffffffffffb0#64)
        (regs .x25)).getMem a

theorem loop (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (tabs : List Model.Limbs)
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p) {need needP : Nat} (hnP : 80 + needP ≤ need)
    (hpanic : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx needP)
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (MulPost tabs) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (he : EListAt m (regs .x10) tabs)
    (hl : env.Live m (regs .x10) (Layouts.E.byteSize * tabs.length))
    (hb0 : ∀ w < 11, idx 0 w (regs .x12) < tabs.length) :
    ∀ k j R M, j + k + 1 = 11 → (∀ w < j, idx 1 w (regs .x13) < tabs.length) →
      Inv env tabs ret top regs m j R M → rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 238, ret, top⟩ :: rest, R, M⟩ := by
  have hlen := len_lt hl hnx
  intro k
  induction k with
  | zero =>
    intro j R M hj hb1 hinv
    have hj10 : j = 10 := by omega
    rv_intro hinv
    rv_sym hp with [hL] using [hpanic]
    · exact absurd ((end17 (by omega)).2 hj10) hc
    all_goals have hbj := bound_j hlen (by omega) hc_1
    all_goals have hb : ∀ w < 11, idx 1 w (regs .x13) < tabs.length := fun w hw =>
      if h : w < j then hb1 w h else (show w = j by omega) ▸ hbj
    · rw [sum_eq hinv_13 hnx he hl hb0 hb, hj10, ← body_val M _ _ _ 10 (by decide), ← hj10]
    · rw [sum_eq hinv_13 hnx he hl hb0 hb, hj10, ← body_val M _ _ _ 10 (by decide), ← hj10]
  | succ k ih =>
    intro j R M hj hb1 hinv
    rv_intro hinv
    rv_sym hp with [hL] using [hpanic]
    · have hbj := bound_j hlen (by omega) hc_1
      apply ih (j + 1) _ _ (by omega) (fun w hw => if h : w < j then hb1 w h else (show w = j by omega) ▸ hbj)
      rv_close
      · exact step16 j
      · exact step17 j
      · rw [← body_val M _ _ _ j (by omega)]
      · rw [← body_val M _ _ _ j (by omega)]
    all_goals exact absurd ((end17 (by omega)).1 hc) (by omega)

/-- **`Scaled::mul` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needP : Nat} (hnP : 80 + needP ≤ need)
    (hpanic : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx needP) : mulSpec env p i need := by
  intro tabs
  rv_auto hp with [hL] using [hpanic]
  have hlen := len_lt hpre_8 hpre_5
  have w1 := win (regs .x12) 1 52 64 (by decide) rfl rfl
  have w2 := win (regs .x12) 2 46 128 (by decide) rfl rfl
  have w3 := win (regs .x12) 3 40 192 (by decide) rfl rfl
  have w4 := win (regs .x12) 4 34 256 (by decide) rfl rfl
  have w5 := win (regs .x12) 5 28 320 (by decide) rfl rfl
  have w6 := win (regs .x12) 6 22 384 (by decide) rfl rfl
  have w7 := win (regs .x12) 7 16 448 (by decide) rfl rfl
  have w8 := win (regs .x12) 8 10 512 (by decide) rfl rfl
  have w9 := win (regs .x12) 9 4 576 (by decide) rfl rfl
  have b : ∀ w, w < 11 → BitVec.ofNat 64 (idx 0 w (regs .x12)) < BitVec.ofNat 64 tabs.length →
      idx 0 w (regs .x12) < tabs.length := fun w hw h =>
    lt_of_ofNat (by have := idx_lt 0 w (regs .x12) (by decide) hw; omega) hlen h
  rw [win0] at hc_1
  rw [w1] at hc_2; rw [w2] at hc_3; rw [w3] at hc_4; rw [w4] at hc_5; rw [w5] at hc_6; rw [w6] at hc_7
  rw [w7] at hc_8; rw [w8] at hc_9; rw [w9] at hc_10; rw [win10] at hc
  have hb0 : ∀ w < 11, idx 0 w (regs .x12) < tabs.length := by
    intro w hw
    interval_cases w
    · exact b 0 (by decide) hc_1
    · exact b 1 (by decide) hc_2
    · exact b 2 (by decide) hc_3
    · exact b 3 (by decide) hc_4
    · exact b 4 (by decide) hc_5
    · exact b 5 (by decide) hc_6
    · exact b 6 (by decide) hc_7
    · exact b 7 (by decide) hc_8
    · exact b 8 (by decide) hc_9
    · exact b 9 (by decide) hc_10
    · exact b 10 (by decide) hc
  refine loop env p i L tabs hp hL hnP hpanic hk hpre_3 hpre_4 hpre_5 hpre_7 hpre_8 hb0 10 0 _ _ (by omega)
    (fun w hw => absurd hw (Nat.not_lt_zero w)) ?_
  rv_close
  all_goals simp only [win0, w1, w2, w3, w4, w5, w6, w7, w8, w9, win10, shl_idx, part_succ, part_zero, rd,
    Model.eAdd, Model.eZero, BitVec.zero_xor, Nat.reduceLT]
  all_goals exact xor11 _ _ _ _ _ _ _ _ _ _ _

end Rv64mc.Proof.Field.ScaledMul
