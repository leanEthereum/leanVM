/-
  LeanVM.Guest.B1.KeccakGkr.ShiftMath

  The carry ripple of `keccak_shifts_eq` (G:2547-2600): the multilinear extension of
  "x = y + r mod 64", bit by bit with the carry.
-/

module

public import LeanVM.Protocol.Keccak.Multilinear

/-!
# Shifts of equality weights, by the carry

For points `as`, `bs` of `t` coordinates, `carryK as bs c p` weighs the pairs `(x, y)` of `t`-bit
indices with `x + c·2^t = y + p`: `y + p` lands on `x` with carry `c`. `carryK_snoc`: adding a top
coordinate is one step of a carry chain (`carry_step`), its weights per bit `e = 1 + a + b`,
`u = a + ab`, `v = b + ab`; `modK` (both carries, `carry_wrap`) is "`x = y + q` mod `2^t`".
`modK_split` composes a low and a high chain: the low carry moves the high shift by one.
`shiftSum_eq`: `Σ_z eq(a, z + r) eq(b, z) = modK`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier Finset

@[expose] public section

/-- The weight of bit `b` at `r`. -/
def eq1 (r : E) (b : ℕ) : E := if b % 2 = 1 then r else 1 + r

theorem eqAt_snoc (as : List E) (α : E) {x : ℕ} (xb : ℕ) (hx : x < 2 ^ as.length) :
    eqAt (as ++ [α]) (x + 2 ^ as.length * xb) = eqAt as x * eq1 α xb := by
  rw [eqAt_append, eqAt_mod as, show (x + 2 ^ as.length * xb) % 2 ^ as.length = x by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx],
    show (x + 2 ^ as.length * xb) / 2 ^ as.length = xb by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]]
  simp [eqAt, eq1]

/-- Pairs `(x, y)` of `t`-bit indices with `x + c·2^t = y + p`, weighed. -/
def carryK (as bs : List E) (c p : ℕ) : E :=
  ∑ x ∈ range (2 ^ as.length), ∑ y ∈ range (2 ^ as.length),
    if x + c * 2 ^ as.length = y + p then eqAt as x * eqAt bs y else 0

/-- Pairs with `x = y + q` mod `2^t`, weighed. -/
def modK (as bs : List E) (q : ℕ) : E :=
  ∑ x ∈ range (2 ^ as.length), ∑ y ∈ range (2 ^ as.length),
    if x = (y + q) % 2 ^ as.length then eqAt as x * eqAt bs y else 0

/-- The weight of one bit's step: `xb + 2c' = yb + r + c`. -/
def carryW (α β : E) (c r c' : ℕ) : E :=
  ∑ xb ∈ range 2, ∑ yb ∈ range 2,
    if xb + 2 * c' = yb + r + c then eq1 α xb * eq1 β yb else 0

theorem sum_range_two_pow_succ (t : ℕ) (F : ℕ → E) :
    ∑ w ∈ range (2 ^ (t + 1)), F w = ∑ xb ∈ range 2, ∑ x ∈ range (2 ^ t), F (x + 2 ^ t * xb) := by
  rw [pow_succ, mul_two, Finset.sum_range_add]
  simp [Finset.sum_range_succ, add_comm]

theorem ite_or_split {P Q : Prop} [Decidable P] [Decidable Q] (h : ¬ (P ∧ Q)) (v : E) :
    (if P ∨ Q then v else 0) = (if P then v else 0) + (if Q then v else 0) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp_all

theorem carry_cond {n x y p xb yb r c' : ℕ} (hx : x < n) (hy : y < n) (hp : p < n)
    (hxb : xb < 2) (hyb : yb < 2) (hr : r < 2) (hc : c' < 2) :
    (x + n * xb + c' * (2 * n) = y + n * yb + (p + n * r)) ↔
      (xb + 2 * c' = yb + r + 0 ∧ x + 0 * n = y + p) ∨
        (xb + 2 * c' = yb + r + 1 ∧ x + 1 * n = y + p) := by
  interval_cases xb <;> interval_cases yb <;> interval_cases r <;> interval_cases c' <;> omega

theorem sum4_factor (f g : ℕ → ℕ → E) (m n : ℕ) :
    ∑ xb ∈ range m, ∑ x ∈ range n, ∑ yb ∈ range m, ∑ y ∈ range n, f xb yb * g x y =
      (∑ xb ∈ range m, ∑ yb ∈ range m, f xb yb) * (∑ x ∈ range n, ∑ y ∈ range n, g x y) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun xb _ ↦ ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun yb _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]

/-- **One step of the carry chain** (`carry_step`, G:2516-2530). -/
theorem carryK_snoc (as bs : List E) (hl : bs.length = as.length) (α β : E) {p r c' : ℕ}
    (hp : p < 2 ^ as.length) (hr : r < 2) (hc : c' < 2) :
    carryK (as ++ [α]) (bs ++ [β]) c' (p + 2 ^ as.length * r) =
      carryK as bs 0 p * carryW α β 0 r c' + carryK as bs 1 p * carryW α β 1 r c' := by
  set n := 2 ^ as.length with hn
  have hlen : (as ++ [α]).length = as.length + 1 := by simp
  unfold carryK
  rw [hlen, sum_range_two_pow_succ]
  simp_rw [sum_range_two_pow_succ as.length]
  rw [← hn]
  have key : ∀ xb ∈ range 2, ∀ x ∈ range n,
      (∑ yb ∈ range 2, ∑ y ∈ range n,
        if x + n * xb + c' * 2 ^ (as.length + 1) = y + n * yb + (p + n * r) then
          eqAt (as ++ [α]) (x + n * xb) * eqAt (bs ++ [β]) (y + n * yb) else 0) =
      ∑ yb ∈ range 2, ∑ y ∈ range n,
        ((if xb + 2 * c' = yb + r + 0 then eq1 α xb * eq1 β yb else 0) *
            (if x + 0 * n = y + p then eqAt as x * eqAt bs y else 0) +
          (if xb + 2 * c' = yb + r + 1 then eq1 α xb * eq1 β yb else 0) *
            (if x + 1 * n = y + p then eqAt as x * eqAt bs y else 0)) := by
    intro xb hxb x hx
    refine Finset.sum_congr rfl fun yb hyb ↦ Finset.sum_congr rfl fun y hy ↦ ?_
    have hxb' := Finset.mem_range.1 hxb
    have hyb' := Finset.mem_range.1 hyb
    have hx' := Finset.mem_range.1 hx
    have hy' := Finset.mem_range.1 hy
    have e1 := eqAt_snoc as α xb hx'
    have e2 := eqAt_snoc bs β yb (by rw [hl]; exact hy')
    rw [hl, ← hn] at e2
    rw [← hn] at e1
    rw [e1, e2]
    simp only [show c' * 2 ^ (as.length + 1) = c' * (2 * n) by rw [hn, pow_succ]; ring,
      carry_cond hx' hy' hp hxb' hyb' hr hc]
    rw [ite_or_split (fun h ↦ by omega), ite_zero_mul_ite_zero, ite_zero_mul_ite_zero,
      show eqAt as x * eq1 α xb * (eqAt bs y * eq1 β yb) =
        eq1 α xb * eq1 β yb * (eqAt as x * eqAt bs y) by ring]
  rw [Finset.sum_congr rfl fun xb hxb ↦ Finset.sum_congr rfl fun x hx ↦ key xb hxb x hx]
  simp only [Finset.sum_add_distrib]
  rw [sum4_factor (fun xb yb ↦ if xb + 2 * c' = yb + r + 0 then eq1 α xb * eq1 β yb else 0)
      (fun x y ↦ if x + 0 * n = y + p then eqAt as x * eqAt bs y else 0),
    sum4_factor (fun xb yb ↦ if xb + 2 * c' = yb + r + 1 then eq1 α xb * eq1 β yb else 0)
      (fun x y ↦ if x + 1 * n = y + p then eqAt as x * eqAt bs y else 0), carryW, carryW,
    mul_comm, mul_comm (∑ xb ∈ range 2, _)]

/-! ## The bit weights -/

theorem carryW_vals (α β : E) :
    carryW α β 0 0 0 = 1 + α + β ∧ carryW α β 0 0 1 = 0 ∧
    carryW α β 1 0 0 = α + α * β ∧ carryW α β 1 0 1 = β + α * β ∧
    carryW α β 0 1 0 = α + α * β ∧ carryW α β 0 1 1 = β + α * β ∧
    carryW α β 1 1 0 = 0 ∧ carryW α β 1 1 1 = 1 + α + β := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [carryW, Finset.sum_range_succ, Finset.sum_range_zero, eq1] <;> norm_num <;>
    first | ring1 | linear_combination (α * β) * h2

/-- No pair of `t`-bit indices carries out of `y + 0`. -/
theorem carryK_one_zero (as bs : List E) : carryK as bs 1 0 = 0 := by
  unfold carryK
  refine Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun y hy ↦ ?_
  have := Finset.mem_range.1 hy
  simp only [show ¬ (x + 1 * 2 ^ as.length = y + 0) by omega, ↓reduceIte]

theorem carryK_nil (c p : ℕ) : carryK [] [] c p = if c = p then 1 else 0 := by
  simp only [carryK, List.length_nil, pow_zero, Finset.sum_range_one, eqAt_nil, mul_one,
    zero_add]

/-- **Both carries**: `x = y + q` mod `2^t`. -/
theorem modK_eq (as bs : List E) {q : ℕ} (hq : q < 2 ^ as.length) :
    modK as bs q = carryK as bs 0 q + carryK as bs 1 q := by
  unfold modK carryK
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have hx' := Finset.mem_range.1 hx
  have hy' := Finset.mem_range.1 hy
  set n := 2 ^ as.length
  rcases Nat.lt_or_ge (y + q) n with h | h
  · rw [Nat.mod_eq_of_lt h]
    simp only [show ¬ (x + 1 * n = y + q) by omega, ↓reduceIte, add_zero, zero_mul]
  · have hm : (y + q) % n = y + q - n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    simp only [show ¬ (x + 0 * n = y + q) by omega, ↓reduceIte, zero_add,
      show (x = y + q - n) ↔ (x + 1 * n = y + q) by omega]

/-! ## Low and high bits -/

theorem sum_range_mul_split (m : ℕ) (F : ℕ → E) : ∀ k,
    ∑ w ∈ range (m * k), F w = ∑ h ∈ range k, ∑ l ∈ range m, F (l + m * h)
  | 0 => by simp
  | k + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_mul_split m F k, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [add_comm]

theorem eqAt_append_split (a b : List E) {l : ℕ} (hl : l < 2 ^ a.length) (h : ℕ) :
    eqAt (a ++ b) (l + 2 ^ a.length * h) = eqAt a l * eqAt b h := by
  rw [eqAt_append, eqAt_mod a, show (l + 2 ^ a.length * h) % 2 ^ a.length = l by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl],
    show (l + 2 ^ a.length * h) / 2 ^ a.length = h by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hl, zero_add]]

theorem split_cond {xl yl xh yh q : ℕ} (hxl : xl < 8) (hyl : yl < 8) (hxh : xh < 8) :
    (xl + 8 * xh = (yl + 8 * yh + q) % 64) ↔
      (xh = (yh + q / 8 % 8) % 8 ∧ xl + 0 * 8 = yl + q % 8) ∨
        (xh = (yh + (q / 8 + 1) % 8) % 8 ∧ xl + 1 * 8 = yl + q % 8) := by
  omega

/-- **Low and high bits** (G:2585-2590): with the low three bits' carry `c`, the high three bits
add `q / 8 + c`. -/
theorem modK_split (aL bL aH bH : List E) (hal : aL.length = 3) (hbl : bL.length = 3)
    (hah : aH.length = 3) (q : ℕ) :
    modK (aL ++ aH) (bL ++ bH) q =
      carryK aL bL 0 (q % 8) * modK aH bH (q / 8 % 8) +
        carryK aL bL 1 (q % 8) * modK aH bH ((q / 8 + 1) % 8) := by
  unfold modK carryK
  have hlen : (aL ++ aH).length = 6 := by simp [hal, hah]
  rw [hlen, hal, hah, show (2 : ℕ) ^ 6 = 8 * 8 by norm_num, show (2 : ℕ) ^ 3 = 8 by norm_num,
    sum_range_mul_split]
  simp_rw [sum_range_mul_split 8 _ 8]
  have key : ∀ xh ∈ range 8, ∀ xl ∈ range 8,
      (∑ yh ∈ range 8, ∑ yl ∈ range 8,
        if xl + 8 * xh = (yl + 8 * yh + q) % (8 * 8) then
          eqAt (aL ++ aH) (xl + 8 * xh) * eqAt (bL ++ bH) (yl + 8 * yh) else 0) =
      ∑ yh ∈ range 8, ∑ yl ∈ range 8,
        ((if xh = (yh + q / 8 % 8) % 8 then eqAt aH xh * eqAt bH yh else 0) *
            (if xl + 0 * 8 = yl + q % 8 then eqAt aL xl * eqAt bL yl else 0) +
          (if xh = (yh + (q / 8 + 1) % 8) % 8 then eqAt aH xh * eqAt bH yh else 0) *
            (if xl + 1 * 8 = yl + q % 8 then eqAt aL xl * eqAt bL yl else 0)) := by
    intro xh hxh xl hxl
    refine Finset.sum_congr rfl fun yh hyh ↦ Finset.sum_congr rfl fun yl hyl ↦ ?_
    have hxh' := Finset.mem_range.1 hxh
    have hyh' := Finset.mem_range.1 hyh
    have hxl' := Finset.mem_range.1 hxl
    have hyl' := Finset.mem_range.1 hyl
    have e1 := eqAt_append_split aL aH (show xl < 2 ^ aL.length by rw [hal]; norm_num; omega) xh
    have e2 := eqAt_append_split bL bH (show yl < 2 ^ bL.length by rw [hbl]; norm_num; omega) yh
    rw [hal, show (2 : ℕ) ^ 3 = 8 by norm_num] at e1
    rw [hbl, show (2 : ℕ) ^ 3 = 8 by norm_num] at e2
    rw [e1, e2]
    simp only [show (8 : ℕ) * 8 = 64 by norm_num, split_cond hxl' hyl' hxh']
    rw [ite_or_split (fun h ↦ by omega), ite_zero_mul_ite_zero, ite_zero_mul_ite_zero,
      show eqAt aL xl * eqAt aH xh * (eqAt bL yl * eqAt bH yh) =
        eqAt aH xh * eqAt bH yh * (eqAt aL xl * eqAt bL yl) by ring]
  rw [Finset.sum_congr rfl fun xh hxh ↦ Finset.sum_congr rfl fun xl hxl ↦ key xh hxh xl hxl]
  simp only [Finset.sum_add_distrib]
  rw [sum4_factor (fun xh yh ↦ if xh = (yh + q / 8 % 8) % 8 then eqAt aH xh * eqAt bH yh else 0)
      (fun xl yl ↦ if xl + 0 * 8 = yl + q % 8 then eqAt aL xl * eqAt bL yl else 0),
    sum4_factor (fun xh yh ↦ if xh = (yh + (q / 8 + 1) % 8) % 8 then eqAt aH xh * eqAt bH yh
      else 0) (fun xl yl ↦ if xl + 1 * 8 = yl + q % 8 then eqAt aL xl * eqAt bL yl else 0)]
  ring

/-- **The shift sum** `Σ_z eq(a, z + r) eq(b, z)` is `modK`. -/
theorem shiftSum_eq (a b : List E) (ha : a.length = 6) {r : ℕ} :
    ∑ z ∈ range 64, eqAt a ((z + r) % 64) * eqAt b z = modK a b r := by
  unfold modK
  rw [ha, show (2 : ℕ) ^ 6 = 64 by norm_num, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Finset.sum_ite_eq' (range 64) ((z + r) % 64)]
  simp [Nat.mod_lt]

end
end LeanVM.Protocol.KeccakGkr
