/-
  Rv64mc.Tactic.Bench.EqEvalAuto

  The contract of `verifier::multilinear::eq_eval` over any program holding its template, from the contracts of
  `<E as Mul>::mul` (whatever product `mul` it computes) and of `assert_failed` (it does not return), by
  `rv_auto`: the loop is a lemma at its head (instruction 28), its invariant the fold's prefix.
-/

import Rv64mc.Tactic.Bench.EqEval
import Rv64mc.Tactic.Sym

namespace Rv64mc.Tactic.Bench.EqEvalAuto

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Tactic.Bench Rv64mc.Tactic.Bench.EqEval

variable (mul : Word × Word → Word × Word → Word × Word)

/-- One step of the loop: `result * (ONE + x + y)`, on limbs. -/
def stepW (acc : Word × Word) (xy : (Word × Word) × (Word × Word)) : Word × Word :=
  mul acc (xy.1.1 ^^^ xy.2.1 ^^^ 1#64, xy.1.2 ^^^ xy.2.2)

/-- What `eq_eval` computes from the slices' limbs. -/
def spec (xs ys : List (Word × Word)) : Word × Word := (xs.zip ys).foldl (stepW mul) (1#64, 0#64)

/-- The slice `xs` at `ptr` in `m`, at or above `top`: element `k`'s limbs at `ptr + 16 k` and `ptr + 16 k + 8`. -/
def Slice (m : MachineState) (top ptr : Word) (xs : List (Word × Word)) : Prop :=
  top ≤ ptr ∧ ptr.toNat + 16 * xs.length < 2 ^ 63 ∧
    ∀ k (h : k < xs.length), m.getMem (ptr + BitVec.ofNat 64 (16 * k)) = xs[k].1 ∧
      m.getMem (ptr + BitVec.ofNat 64 (16 * k) + 8#64) = xs[k].2

/-- `<E as Mul>::mul`'s contract, its product `mul`. -/
def MulPre (ret top : Word) (regs : Reg → Word) (_m : MachineState) : Prop :=
  Entry ret top regs ∧ 0x10000#64 ≤ top ∧ top ≤ 0x7fffffffffffffff#64

def MulPost (_ret top : Word) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  r' .x10 = (mul (regs .x10, regs .x11) (regs .x12, regs .x13)).1 ∧
    r' .x11 = (mul (regs .x10, regs .x11) (regs .x12, regs .x13)).2 ∧ Abi top regs r' m m'

/-- The precondition: the slices and their lengths, and room for the frame and `mul`'s. -/
def Pre (xs ys : List (Word × Word)) (ret top : Word) (regs : Reg → Word) (m : MachineState) : Prop :=
  Entry ret top regs ∧ 0x10030#64 ≤ top ∧ top ≤ 0x7fffffffffffffff#64 ∧
    regs .x11 = BitVec.ofNat 64 xs.length ∧ regs .x13 = BitVec.ofNat 64 ys.length ∧
    Slice m top (regs .x10) xs ∧ Slice m top (regs .x12) ys

/-- The postcondition: the product in `a0`, `a1`, and the ABI kept. -/
def Post (xs ys : List (Word × Word)) (_ret top : Word) (regs : Reg → Word) (m : MachineState)
    (r' : Reg → Word) (m' : MachineState) : Prop :=
  r' .x10 = (spec mul xs ys).1 ∧ r' .x11 = (spec mul xs ys).2 ∧ Abi top regs r' m m'

/-! ## The loop's arithmetic and the fold's step -/

theorem step_ptr (q : Word) (j : Nat) :
    q + BitVec.ofNat 64 (16 * j) + 24#64 = q + BitVec.ofNat 64 (16 * (j + 1)) + 8#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem slice_le {m : MachineState} {top q : Word} {xs : List (Word × Word)} (h : Slice m top q xs) {j : Nat}
    (hj : j < xs.length) :
    top ≤ q + BitVec.ofNat 64 (16 * j) ∧ top ≤ q + BitVec.ofNat 64 (16 * j) + 8#64 := by
  obtain ⟨h1, h2, -⟩ := h
  rw [BitVec.le_def] at h1
  constructor <;> rw [BitVec.le_def] <;> simp [BitVec.toNat_add] <;> omega

/-- The loop's exit test: past the last element. -/
theorem end_iff {q : Word} {j len : Nat} (hq : q.toNat + 16 * len < 2 ^ 63) (hj : j < len) :
    q + BitVec.ofNat 64 (16 * j) + 24#64 = q + 8#64 + BitVec.ofNat 64 len <<< 4 ↔ j + 1 = len := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_right_inj, ← BitVec.toNat_inj]
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- A length that is zero as a word is zero. -/
theorem len_eq {q q' : Word} {a b : Nat} (hq : q.toNat + 16 * a < 2 ^ 63) (hq' : q'.toNat + 16 * b < 2 ^ 63)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  rw [← BitVec.toNat_inj] at h; simp at h; omega

theorem start_ptr (q : Word) : q + 8#64 = q + BitVec.ofNat 64 (16 * 0) + 8#64 := by simp

theorem spec_nil {xs ys : List (Word × Word)} (h : xs.length = 0) : spec mul xs ys = (1#64, 0#64) := by
  simp [List.eq_nil_of_length_eq_zero h, spec]

theorem len_zero {q : Word} {len : Nat} (hq : q.toNat + 16 * len < 2 ^ 63) :
    BitVec.ofNat 64 len = 0#64 ↔ len = 0 := by
  rw [← BitVec.toNat_inj]; simp; omega

theorem fold_succ {xs ys : List (Word × Word)} {j : Nat} (hx : j < xs.length) (hy : j < ys.length) :
    ((xs.zip ys).take (j + 1)).foldl (stepW mul) (1#64, 0#64) =
      stepW mul (((xs.zip ys).take j).foldl (stepW mul) (1#64, 0#64)) (xs[j], ys[j]) := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp; omega)]
  simp [List.getElem_zip]

/-- What one pass of the body computes, as `mul` gets it, is the fold one element further. -/
theorem body_val {m : MachineState} {top l q : Word} {xs ys : List (Word × Word)} (hx : Slice m top l xs)
    (hy : Slice m top q ys) {j : Nat} (hjx : j < xs.length) (hjy : j < ys.length) :
    mul ((((xs.zip ys).take j).foldl (stepW mul) (1#64, 0#64)).1,
        (((xs.zip ys).take j).foldl (stepW mul) (1#64, 0#64)).2)
        (m.getMem (l + BitVec.ofNat 64 (16 * j)) ^^^ m.getMem (q + BitVec.ofNat 64 (16 * j)) ^^^ 1#64,
          m.getMem (q + BitVec.ofNat 64 (16 * j) + 8#64) ^^^ m.getMem (l + BitVec.ofNat 64 (16 * j) + 8#64)) =
      ((xs.zip ys).take (j + 1)).foldl (stepW mul) (1#64, 0#64) := by
  rw [fold_succ mul hjx hjy, (hx.2.2 j hjx).1, (hx.2.2 j hjx).2, (hy.2.2 j hjy).1, (hy.2.2 j hjy).2,
    BitVec.xor_comm (ys[j].2)]
  rfl

theorem spec_take {xs ys : List (Word × Word)} {j : Nat} (h : j + 1 = xs.length) (hlen : xs.length = ys.length) :
    spec mul xs ys = ((xs.zip ys).take (j + 1)).foldl (stepW mul) (1#64, 0#64) := by
  rw [List.take_of_length_le (by simp; omega)]; rfl

/-- The loop's invariant at its head (instruction 28) after `j` elements: the two pointers, the end, the product
    of the first `j` factors, the saved registers, the elements above the frame, and the memory the prologue left,
    kept above `mul`'s frame. -/
def Inv (xs ys : List (Word × Word)) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 0xffffffffffffffd0#64 ∧
    R .x8 = regs .x12 + BitVec.ofNat 64 (16 * j) + 8#64 ∧ R .x9 = regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    R .x18 = regs .x12 + 8#64 + BitVec.ofNat 64 xs.length <<< 4 ∧
    R .x10 = (((xs.zip ys).take j).foldl (stepW mul) (1#64, 0#64)).1 ∧
    R .x11 = (((xs.zip ys).take j).foldl (stepW mul) (1#64, 0#64)).2 ∧
    R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    top ≤ regs .x10 + BitVec.ofNat 64 (16 * j) ∧ top ≤ regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    top ≤ regs .x12 + BitVec.ofNat 64 (16 * j) ∧ top ≤ regs .x12 + BitVec.ofNat 64 (16 * j) + 8#64 ∧
    ∀ a, top + 0xffffffffffffffd0#64 ≤ a → M.getMem a =
      ((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
        (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).getMem a

/-- **The loop**, from its head with `k + 1` elements to go. -/
theorem loop {E : Type} (c : Context rvIsa E) (p : Lprog (Op Reg) Reg) (L : Link) (i : Nat)
    (xs ys : List (Word × Word)) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hmul : rvIsa.Contract p c L.mul.idx MulPre (MulPost mul))
    {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Post mul xs ys ret top regs m r' m' → rvIsa.SafeN p c G n Q ⟨rest, r', m'⟩)
    (hlo : 0x10030#64 ≤ top) (hhi : top ≤ 0x7fffffffffffffff#64) (hlen : xs.length = ys.length)
    (hx : Slice m top (regs .x10) xs) (hy : Slice m top (regs .x12) ys) :
    ∀ k j R M, j + k + 1 = xs.length → Inv mul xs ys ret top regs m j R M →
      rvIsa.SafeN p c G n Q ⟨⟨i, 28, ret, top⟩ :: rest, R, M⟩ := by
  intro k
  induction k with
  | zero =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL.mul, hL.s0] using [hmul]
    · exact absurd ((end_iff (hlen ▸ hy.2.1) (by omega)).2 (by omega)) hc
    all_goals rw [spec_take mul (by omega) hlen, ← body_val mul hx hy (by omega) (by omega)]
  | succ k ih =>
    intro j R M hj hinv
    rv_intro hinv
    rv_sym hp with [hL.mul, hL.s0] using [hmul]
    · apply ih (j + 1) _ _ (by omega)
      rv_close
      · exact step_ptr _ _
      · exact step_ptr _ _
      · rw [body_val mul hx hy (by omega) (by omega)]
      · rw [body_val mul hx hy (by omega) (by omega)]
      · exact (slice_le hx (by omega)).1
      · exact (slice_le hx (by omega)).2
      · exact (slice_le hy (by omega)).1
      · exact (slice_le hy (by omega)).2
    all_goals exact absurd ((end_iff (hlen ▸ hy.2.1) (by omega)).1 hc) (by omega)

theorem ok {E : Type} (c : Context rvIsa E) (p : Lprog (Op Reg) Reg) (L : Link) (i : Nat) (xs ys : List (Word × Word))
    (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hmul : rvIsa.Contract p c L.mul.idx MulPre (MulPost mul))
    (hfail : rvIsa.Contract p c L.fail.idx (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => False)) :
    rvIsa.Contract p c i (Pre xs ys) (Post mul xs ys) := by
  rv_auto hp with [hL.mul, hL.fail, hL.s0, hL.s1] using [hmul, hfail]
  all_goals have hx : Slice m top (regs .x10) xs := ⟨hpre_7, hpre_8, hpre_9⟩
  all_goals have hy : Slice m top (regs .x12) ys := ⟨hpre_10, hpre_11, hpre_12⟩
  all_goals have hlen : xs.length = ys.length := len_eq hpre_8 hpre_11 hc_1
  · rw [spec_nil mul ((len_zero hpre_8).1 hc)]
  · rw [spec_nil mul ((len_zero hpre_8).1 hc)]
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero hpre_8).2 h)
  refine loop mul c p L i xs ys hp hL hmul hk hpre_3 hpre_4 hlen hx hy (xs.length - 1) 0 _ _ (by omega) ?_
  rv_close
  · exact start_ptr _
  · exact start_ptr _
  · rfl
  · rfl
  · exact (slice_le hx (by omega)).1
  · exact (slice_le hx (by omega)).2
  · exact (slice_le hy (by omega)).1
  · exact (slice_le hy (by omega)).2

end Rv64mc.Tactic.Bench.EqEvalAuto
