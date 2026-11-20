module

public import Rv64mc.Model.Field

/-!
# `multilinear.rs` as the Rust computes it

Mirrors of `crates/verifier/src/multilinear.rs`, following the Rust's loops: a loop
`for i in 0..n` over a buffer is `(List.range n).foldl` of one iteration's update, so the state
after `i` iterations is the fold over `List.range i`. Each mirror is proved equal to its
counterpart in `Statement/LeanVmVerifier.lean`.

Conventions. An `E` value is the statement's `E`, its arithmetic the statement's `+` and `*`,
which `Model.Field` proves the Rust's (`eAdd_eq`, `eMul_eq`); a call of a distinct Rust function
(`E::square`, `Scaled`) is its `Model.Field` mirror. A `u64` is a `BitVec 64`, and a shift by a
`usize` amount is masked to six bits, as the release build (no overflow checks) computes it.
Where the Rust panics (an `assert!`, an index out of bounds, a wrapped length) a mirror may return
anything, and it fails (`none`) only where the Rust fails (`require` returns an `Err`); an
`assert!` the verifier relies on is a `none` too. The theorems' hypotheses are the conditions
under which the Rust does not panic, as at every call of the verifier.
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- `E::new(x, 0)`. -/
def eNew (x : BitVec 64) : E := ofK (BF64.ofBitVec x)

/-- `E::new(n >> k & 1, 0)`, a shift by a `usize`. -/
def bitE (n : BitVec 64) (k : ℕ) : E := eNew ((n >>> (k % 64)) &&& 1#64)

private theorem bitE_eq (n : BitVec 64) {k : ℕ} (hk : k < 64) :
    bitE n k = eOfNat ((n.toNat >>> k) % 2) := by
  have h : (n >>> (k % 64)) &&& 1#64 = BitVec.ofNat 64 ((n.toNat >>> k) % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [Nat.mod_eq_of_lt hk, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.and_one_is_mod]
    have : (n.toNat >>> k) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  simp only [bitE, eNew, eOfNat, K.ofBits, h]

/-! ## `Scaler` -/

/-- `Scaler`: a product by `r` through `Scaled`'s tables, or plain. -/
inductive Scaler where
  /-- `Scaler::Table(Scaled::new(r))`. -/
  | table (tables : List Limbs)
  /-- `Scaler::Plain(r)`. -/
  | plain (r : E)

/-- `Scaler::new(r, uses)`: the tables once they multiply at least `256` values. -/
def Scaler.new (r : E) (uses : ℕ) : Scaler :=
  if 256 ≤ uses then .table (scaledNewE r) else .plain r

/-- `Scaler::mul(value)`. -/
def Scaler.mul : Scaler → E → E
  | .table tables, value => scaledMulE tables value
  | .plain r, value => value * r

/-- **A `Scaler` of `r` multiplies by `r`.** -/
@[simp] theorem Scaler.mul_new (r : E) (uses : ℕ) (value : E) :
    (Scaler.new r uses).mul value = value * r := by
  unfold Scaler.new
  split
  · exact scaledMulE_eq r value
  · rfl

/-! ## `eq_eval`, `dot`, `poly_eval`, `index_mle` -/

/-- `eq_eval`: `assert_eq!` of the lengths, then `result *= 1 + x + y` over the zipped slices. -/
def eqEvalRust (left right : List E) : Option E :=
  if left.length = right.length then
    some ((left.zip right).foldl (fun result (x, y) ↦ result * (1 + x + y)) 1)
  else none

theorem eqEvalRust_eq {left right : List E} (h : left.length = right.length) :
    eqEvalRust left right = some (eqEval left right) := by
  simp only [eqEvalRust, h, ↓reduceIte, eqEval, ← List.map_uncurry_zip_eq_zipWith, List.foldl_map]
  rfl

/-- `dot`: `assert_eq!` of the lengths, then `result += x * y` over the zipped slices. -/
def dotRust (left right : List E) : Option E :=
  if left.length = right.length then
    some ((left.zip right).foldl (fun result (x, y) ↦ result + x * y) 0)
  else none

theorem dotRust_eq {left right : List E} (h : left.length = right.length) :
    dotRust left right = some (dot left right) := by
  simp only [dotRust, h, ↓reduceIte, dot, ← List.map_uncurry_zip_eq_zipWith, List.foldl_map]
  rfl

/-- `poly_eval`: Horner over the reversed coefficients. -/
def polyEvalRust (coefficients : List E) (point : E) : E :=
  coefficients.reverse.foldl (fun acc c ↦ acc * point + c) 0

theorem polyEvalRust_eq (coefficients : List E) (point : E) :
    polyEvalRust coefficients point = polyEval coefficients point := by
  simp only [polyEvalRust, polyEval, List.foldl_reverse]

/-- `index_mle`: `result *= 1 + c·(1 + g)`, then `g = g.square()`, from `(ONE, GEN)`. -/
def indexMleRust (point : List E) : E :=
  (point.foldl (fun (acc : E × E) c ↦ (acc.1 * (1 + c * (1 + acc.2)), squareE acc.2)) (1, gen)).1

theorem indexMleRust_eq (point : List E) : indexMleRust point = indexMle point := by
  suffices ∀ (acc g : E), (point.foldl (fun (acc : E × E) c ↦
      (acc.1 * (1 + c * (1 + acc.2)), squareE acc.2)) (acc, g)).1 = indexMleFrom g point acc from
    this 1 gen
  induction point with
  | nil => intro acc g; rfl
  | cons r rs ih => intro acc g; rw [List.foldl_cons, ih, squareE_eq]; rfl

/-! ## `log2_ceil`, `log2_strict` -/

/-- `saturating_sub(1)` on a `u64`. -/
def satSubOne (value : BitVec 64) : BitVec 64 := if value = 0#64 then 0#64 else value - 1#64

/-- `log2_ceil`: `64 - value.saturating_sub(1).leading_zeros()`. -/
def log2CeilRust (value : BitVec 64) : ℕ := 64 - (satSubOne value).clz.toNat

/-- A word's width less its leading zeros is its bit length (API: `grinding_bits` uses it at
`128`). -/
theorem sub_clz_eq_bitLength {w : ℕ} (x : BitVec w) : w - x.clz.toNat = bitLength x.toNat := by
  by_cases hx : x = 0#w
  · subst hx
    have : (0#w).clz = BitVec.ofNat w w := BitVec.clz_eq_iff_eq_zero.mpr rfl
    simp [this, bitLength, Nat.mod_eq_of_lt Nat.lt_two_pow_self]
  · have hne : x.toNat ≠ 0 := fun h ↦ hx (BitVec.eq_of_toNat_eq (by simpa using h))
    have hlt : x.clz.toNat < w := by
      simpa [Nat.mod_eq_of_lt Nat.lt_two_pow_self] using
        BitVec.lt_def.mp (BitVec.clz_lt_iff_ne_zero.mpr hx)
    have hlog : Nat.log2 x.toNat = w - 1 - x.clz.toNat := by
      rw [Nat.log2_eq_iff hne]
      refine ⟨BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by omega) hx, ?_⟩
      rw [show w - 1 - x.clz.toNat + 1 = w - x.clz.toNat by omega]
      exact BitVec.toNat_lt_two_pow_sub_clz
    simp only [bitLength, hne, ite_false, hlog]
    omega

theorem log2CeilRust_eq (value : BitVec 64) : log2CeilRust value = log2Ceil value.toNat := by
  rw [log2CeilRust, sub_clz_eq_bitLength, log2Ceil]
  congr 1
  unfold satSubOne
  split
  · next h => subst h; rfl
  · next h =>
    have : value.toNat ≠ 0 := fun h' ↦ h (BitVec.eq_of_toNat_eq (by simpa using h'))
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega)]
    simp

/-- A nonzero `n` with `n & (n - 1) = 0` is a power of two. -/
private theorem eq_two_pow_log2 {n : ℕ} (h0 : n ≠ 0) (h : n &&& (n - 1) = 0) :
    n = 2 ^ Nat.log2 n := by
  have hlo := Nat.log2_self_le h0
  have hhi := Nat.lt_log2_self (n := n)
  generalize Nat.log2 n = k at hlo hhi ⊢
  by_contra hne
  obtain ⟨m, hm⟩ : ∃ m, n = 2 ^ k + m := ⟨n - 2 ^ k, by omega⟩
  have hmk : m < 2 ^ k := by rw [pow_succ] at hhi; omega
  have h1 : n.testBit k = true := by
    rw [hm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hmk]; rfl
  have h2 : (n - 1).testBit k = true := by
    rw [show n - 1 = 2 ^ k + (m - 1) by omega, Nat.testBit_two_pow_add_eq,
      Nat.testBit_lt_two_pow (by omega)]
    rfl
  have := congrArg (Nat.testBit · k) h
  simp [Nat.testBit_and, h1, h2] at this

/-- `log2_strict`: `require(value.is_power_of_two())`, then `trailing_zeros`. In this core
`is_power_of_two` is `count_ones() == 1`; the mirror tests the equivalent `value != 0 &&
value & (value - 1) == 0`. -/
def log2StrictRust (value : BitVec 64) : Option ℕ :=
  if value ≠ 0#64 ∧ value &&& (value - 1#64) = 0#64 then some value.ctz.toNat else none

theorem log2StrictRust_eq (value : BitVec 64) : log2StrictRust value = log2Strict value.toNat := by
  have hc : (value ≠ 0#64 ∧ value &&& (value - 1#64) = 0#64) ↔
      (0 < value.toNat ∧ value.toNat &&& (value.toNat - 1) = 0) := by
    by_cases hv : value = 0#64
    · subst hv; simp
    · have hv' : value.toNat ≠ 0 := fun h ↦ hv (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega)]
      simp [hv, Nat.pos_of_ne_zero hv']
  unfold log2StrictRust log2Strict
  by_cases h : 0 < value.toNat ∧ value.toNat &&& (value.toNat - 1) = 0
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h]
    have hk := eq_two_pow_log2 h.1.ne' h.2
    have hbit := BitVec.getLsbD_true_ctz_of_ne_zero (hc.mpr h).1
    rw [BitVec.getLsbD, hk, Nat.testBit_two_pow] at hbit
    rw [bitLength, ite_eq_right h.1.ne', Nat.add_sub_cancel, ← of_decide_eq_true hbit]
  · rw [ite_eq_right (mt hc.mp h), ite_eq_right h]

/-! ## `selector_point`, `padding_weight` -/

/-- `selector_point`: `E::new(selector >> bit & 1, 0)` for `bit` in `0..length`. -/
def selectorPointRust (selector : BitVec 64) (length : ℕ) : List E :=
  (List.range length).map (bitE selector)

theorem selectorPointRust_eq (selector : BitVec 64) {length : ℕ} (h : length ≤ 64) :
    selectorPointRust selector length = selectorPoint selector.toNat length := by
  unfold selectorPointRust selectorPoint
  apply List.map_congr_left
  intro bit hbit
  rw [List.mem_range] at hbit
  exact bitE_eq selector (by omega)

/-- `padding_weight`: the fold over `point.iter().enumerate()`, then the factor of bit `len`. -/
def paddingWeightRust (point : List E) (n : BitVec 64) : E :=
  let low := point.zipIdx.foldl
    (fun pad (rk : E × ℕ) ↦ (1 + bitE n rk.2) * rk.1 + (1 + bitE n rk.2 + rk.1) * pad) 1
  (1 + bitE n point.length) * low

theorem paddingWeightRust_eq (point : List E) (n : BitVec 64) (h : point.length < 64) :
    paddingWeightRust point n = paddingWeight point n.toNat := by
  have hlow : point.zipIdx.foldl
      (fun pad (rk : E × ℕ) ↦ (1 + bitE n rk.2) * rk.1 + (1 + bitE n rk.2 + rk.1) * pad) 1 =
      point.zipIdx.foldl (fun pad (rk : E × ℕ) ↦
        let b := eOfNat ((n.toNat >>> rk.2) % 2)
        (1 + b) * rk.1 + (1 + b + rk.1) * pad) 1 := by
    apply List.foldl_ext
    intro pad rk hrk
    have hk : rk.2 < point.length := by
      have := List.mem_zipIdx hrk
      omega
    simp only [bitE_eq n (show rk.2 < 64 by omega)]
  simp only [paddingWeightRust, paddingWeight, bitE_eq n h, hlow]

/-! ## `multilinear_eval` -/

/-- One iteration of `multilinear_eval`'s inner loop: `cur[i] = cur[2i] + scale.mul(cur[2i] +
cur[2i+1])`. -/
def mleStep (scale : Scaler) (cur : List E) (i : ℕ) : List E :=
  cur.set i (cur.getD (2 * i) 0 + scale.mul (cur.getD (2 * i) 0 + cur.getD (2 * i + 1) 0))

/-- One coordinate: `Scaler::new(r, len / 2)`, the inner loop over `0..len/2`, then
`truncate(len/2)`. -/
def mlePass (cur : List E) (r : E) : List E :=
  ((List.range (cur.length / 2)).foldl (mleStep (Scaler.new r (cur.length / 2))) cur).take
    (cur.length / 2)

/-- `multilinear_eval`: the size check, the passes, then `cur[0]`. The table's entries are the
`E` images of the Rust's `T: Into<E>` (`ofK` for a table of `K`). -/
def multilinearEvalRust (mle point : List E) : Option E :=
  if point.length < 64 ∧ mle.length = 2 ^ point.length then
    some ((point.foldl mlePass mle).getD 0 0)
  else none

private theorem foldPairs_getElem? (r : E) : ∀ (A : List E) (i : ℕ), (foldPairs r A)[i]? =
    if i < A.length / 2 then some (A.getD (2 * i) 0 * (1 + r) + A.getD (2 * i + 1) 0 * r)
    else none
  | [], i => by simp [foldPairs]
  | [a], i => by simp [foldPairs]
  | a :: b :: rest, 0 => by simp [foldPairs]
  | a :: b :: rest, i + 1 => by
    rw [foldPairs, List.getElem?_cons_succ, foldPairs_getElem? r rest i]
    have h1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    simp only [List.length_cons, h1, List.getD_cons_succ]
    congr 1
    apply propext
    omega

private theorem foldPairs_length (r : E) : ∀ (A : List E), (foldPairs r A).length = A.length / 2
  | [] => by simp [foldPairs]
  | [a] => by simp [foldPairs]
  | a :: b :: rest => by
    rw [foldPairs, List.length_cons, foldPairs_length r rest]
    simp only [List.length_cons]
    omega

private theorem mle_inner (r : E) (n : ℕ) (A : List E) :
    ∀ i, i ≤ A.length / 2 →
      (List.range i).foldl (mleStep (Scaler.new r n)) A = (foldPairs r A).take i ++ A.drop i
  | 0, _ => by simp
  | i + 1, hi => by
    rw [List.range_succ, List.foldl_append, mle_inner r n A i (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, mleStep, Scaler.mul_new]
    have hF := foldPairs_length r A
    have hread : ∀ n, i ≤ n → ((foldPairs r A).take i ++ A.drop i).getD n 0 = A.getD n 0 := by
      intro n hn
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_take, List.getElem?_drop]
      congr 2
      omega
    rw [hread (2 * i) (by omega), hread (2 * i + 1) (by omega)]
    apply List.ext_getElem?
    intro n
    have hval := foldPairs_getElem? r A i
    rw [ite_eq_left (by omega)] at hval
    rw [List.getElem?_set]
    by_cases hn : n = i
    · subst hn
      simp only [ite_true, List.length_append, List.length_take, List.length_drop]
      rw [ite_eq_left (by omega)]
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_take, ite_eq_left (by omega),
        hval]
      congr 1
      ring
    · rw [ite_eq_right (Ne.symm hn)]
      by_cases hlt : n < i
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
        simp only [List.getElem?_take]
        rw [ite_eq_left hlt, ite_eq_left (by omega)]
      · rw [List.getElem?_append_right (by simp; omega),
          List.getElem?_append_right (by simp; omega)]
        simp only [List.length_take, List.getElem?_drop]
        congr 1
        omega

private theorem mlePass_eq (cur : List E) (r : E) : mlePass cur r = foldPairs r cur := by
  rw [mlePass, mle_inner r _ cur _ le_rfl, ← foldPairs_length r cur]
  simp

/-- **`multilinear_eval` is `multilinearEval`** on a table of the right size. -/
theorem multilinearEvalRust_eq (mle point : List E)
    (h : point.length < 64 ∧ mle.length = 2 ^ point.length) :
    multilinearEvalRust mle point = some (multilinearEval mle point) := by
  rw [multilinearEvalRust, ite_eq_left h, multilinearEval]
  have : point.foldl mlePass mle = point.foldl (fun cur r ↦ foldPairs r cur) mle := by
    congr 1
    funext cur r
    exact mlePass_eq cur r
  rw [this]
  cases point.foldl (fun cur r ↦ foldPairs r cur) mle <;> rfl

theorem multilinearEvalRust_some {mle point : List E} {v : E}
    (h : multilinearEvalRust mle point = some v) : v = multilinearEval mle point := by
  by_cases hc : point.length < 64 ∧ mle.length = 2 ^ point.length
  · rw [multilinearEvalRust_eq _ _ hc] at h
    exact (Option.some.inj h).symm
  · simp [multilinearEvalRust, hc] at h

/-! ## `eq_kernel` -/

/-- One iteration of `eq_kernel`'s inner loop at `j < half`: `h = scale.mul(v)` into
`out[j + half]`, then `v += h`. -/
def eqKernelStep (scale : Scaler) (half : ℕ) (out : List E) (j : ℕ) : List E :=
  let h := scale.mul (out.getD j 0)
  (out.set (j + half) h).set j (out.getD j 0 + h)

/-- The pass for coordinate `k`: `Scaler::new(r, 1 << k)`, the inner loop over `0..1 << k`. -/
def eqKernelPass (r : E) (k : ℕ) (out : List E) : List E :=
  (List.range (2 ^ k)).foldl (eqKernelStep (Scaler.new r (2 ^ k)) (2 ^ k)) out

/-- `eq_kernel`: `1 << len` zeros (the shift masked), `out[0] = ONE`, then a pass per `(k, r)` of
`point.iter().enumerate()`. -/
def eqKernelRust (point : List E) : List E :=
  point.zipIdx.foldl (fun out rk ↦ eqKernelPass rk.1 rk.2 out)
    ((List.replicate (2 ^ (point.length % 64)) 0).set 0 1)

private theorem eqKernel_length (point : List E) : (eqKernel point).length = 2 ^ point.length := by
  suffices ∀ (out : List E), (point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r))
      out).length = out.length * 2 ^ point.length by
    have := this [1]
    simpa [eqKernel] using this
  induction point with
  | nil => intro out; simp
  | cons r rs ih =>
    intro out
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_map, List.length_cons]
    ring

/-- The buffer after `j` iterations of the pass over `A ++ 0^m`. -/
private theorem eqKernel_inner (r : E) (n : ℕ) (A : List E) (m : ℕ) (hm : A.length ≤ m) :
    ∀ j, j ≤ A.length →
      (List.range j).foldl (eqKernelStep (Scaler.new r n) A.length) (A ++ List.replicate m 0) =
        (A.take j).map (fun a ↦ a + a * r) ++ A.drop j ++ (A.take j).map (· * r) ++
          List.replicate (m - j) 0
  | 0, _ => by simp
  | j + 1, hj => by
    have hjA : j < A.length := by omega
    rw [List.range_succ, List.foldl_append, eqKernel_inner r n A m hm j (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, eqKernelStep, Scaler.mul_new]
    rw [List.drop_eq_getElem_cons hjA, show m - j = m - (j + 1) + 1 by omega,
      List.replicate_succ, List.take_add_one, List.getElem?_eq_getElem hjA]
    generalize A[j] = a
    generalize hX : (A.take j).map (fun a ↦ a + a * r) = X
    generalize hY : (A.take j).map (· * r) = Y
    have hXl : X.length = j := by rw [← hX]; simp; omega
    have hYl : Y.length = j := by rw [← hY]; simp; omega
    have hDl : (A.drop (j + 1)).length = A.length - (j + 1) := List.length_drop
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
      List.getElem?_append_right (by omega), hXl, Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.getD_some, Option.toList_some, List.map_append,
      List.map_cons, List.map_nil, hX, hY, List.append_assoc, List.cons_append, List.nil_append]
    rw [show j + A.length = X.length + ((A.drop (j + 1)).length + Y.length + 1) by omega,
      List.set_append_right (s := X) _ _ (by omega), Nat.add_sub_cancel_left,
      List.set_cons_succ, List.set_append_right (s := X) _ _ (by omega), hXl, Nat.sub_self,
      List.set_cons_zero, List.set_append_right (s := List.drop (j + 1) A) _ _ (by omega),
      Nat.add_sub_cancel_left, List.set_append_right (s := Y) _ _ le_rfl, Nat.sub_self,
      List.set_cons_zero]

private theorem eqKernelPass_eq (r : E) (k : ℕ) (A : List E) (m : ℕ) (hA : A.length = 2 ^ k)
    (hm : 2 ^ k ≤ m) :
    eqKernelPass r k (A ++ List.replicate m 0) =
      A.map (· * (1 + r)) ++ A.map (· * r) ++ List.replicate (m - 2 ^ k) 0 := by
  rw [eqKernelPass, ← hA, eqKernel_inner r _ A m (by omega) A.length le_rfl]
  simp only [List.take_length, List.drop_length, List.append_nil]
  congr 2
  apply List.map_congr_left
  intro a _
  ring

private theorem eqKernelRust_prefix (n : ℕ) (pre : List E) (h : pre.length ≤ n) :
    pre.zipIdx.foldl (fun out rk ↦ eqKernelPass rk.1 rk.2 out)
        ((List.replicate (2 ^ n) 0).set 0 1) =
      eqKernel pre ++ List.replicate (2 ^ n - 2 ^ pre.length) 0 := by
  induction pre using List.reverseRecOn with
  | nil =>
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = t + 1 :=
      ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
    rw [ht]
    simp [eqKernel, List.replicate_succ]
  | append_singleton l r ih =>
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    rw [List.zipIdx_append, List.foldl_append, ih (by omega)]
    have hpow : 2 * 2 ^ l.length ≤ 2 ^ n := by
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    rw [eqKernelPass_eq r l.length _ _ (eqKernel_length l) (by omega)]
    have hk : eqKernel (l ++ [r]) =
        (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
      simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hk, show 2 ^ n - 2 ^ l.length - 2 ^ l.length = 2 ^ n - 2 ^ (l ++ [r]).length by
      simp only [List.length_append, List.length_cons, List.length_nil, pow_succ]
      omega]

/-- **`eq_kernel` is `eqKernel`**, for fewer than `64` coordinates. -/
theorem eqKernelRust_eq (point : List E) (h : point.length < 64) :
    eqKernelRust point = eqKernel point := by
  rw [eqKernelRust, Nat.mod_eq_of_lt h, eqKernelRust_prefix _ point le_rfl]
  simp

/-! ## Placements -/

/-- `Placement`: `variables: usize` (here `variableCount`), `index: u64`. -/
structure PlacementRust where
  /-- `variables`. -/
  variableCount : ℕ
  /-- `index`. -/
  index : BitVec 64

/-- The statement's placement. -/
def PlacementRust.toSpec (p : PlacementRust) : Placement := ⟨p.variableCount, p.index.toNat⟩

/-- `Placement::stack_point`: `[point, selector_point(index >> variables, stack_log -
variables)].concat()`. -/
def PlacementRust.stackPoint (p : PlacementRust) (point : List E) (stackLog : ℕ) : List E :=
  point ++ selectorPointRust (p.index >>> (p.variableCount % 64)) (stackLog - p.variableCount)

/-- `Placement::eq_above`: `eq_eval(selector_point(index >> variables, len - variables),
&point[variables..])`. -/
def PlacementRust.eqAbove (p : PlacementRust) (point : List E) : Option E :=
  eqEvalRust (selectorPointRust (p.index >>> (p.variableCount % 64))
    (point.length - p.variableCount)) (point.drop p.variableCount)

private theorem selectorPointRust_shift (index : BitVec 64) (v L : ℕ) (h : L ≤ 64 - v) :
    selectorPointRust (index >>> (v % 64)) L = selectorPoint (index.toNat >>> v) L := by
  by_cases hv : v < 64
  · rw [Nat.mod_eq_of_lt hv, selectorPointRust_eq _ (by omega), BitVec.toNat_ushiftRight]
  · have : L = 0 := by omega
    subst this
    rfl

theorem PlacementRust.stackPoint_eq (p : PlacementRust) (point : List E) (stackLog : ℕ)
    (h : stackLog ≤ 64) :
    p.stackPoint point stackLog = p.toSpec.stackPoint point stackLog := by
  rw [PlacementRust.stackPoint, Placement.stackPoint, selectorPointRust_shift _ _ _ (by omega)]
  rfl

theorem PlacementRust.eqAbove_eq (p : PlacementRust) (point : List E) (h : point.length ≤ 64) :
    p.eqAbove point = some (p.toSpec.eqAbove point) := by
  rw [PlacementRust.eqAbove, Placement.eqAbove, eqEvalRust_eq (by simp [selectorPointRust]),
    selectorPointRust_shift _ _ _ (by omega)]
  rfl

/-! ## `stack_offsets`

A pass per size from the largest down, the blocks of that size in index order; the statement
sorts the blocks (largest first, ties by index) by `mergeSort`. -/

/-- One iteration of the pass for `size`: block `index`, placed if it has that size. -/
def stackStep (sizes : List ℕ) (size : ℕ) (st : List (BitVec 64) × BitVec 64) (index : ℕ) :
    List (BitVec 64) × BitVec 64 :=
  if sizes.getD index 0 = size then (st.1.set index st.2, st.2 + 1#64 <<< (size % 64)) else st

/-- The pass for `size`: the blocks in index order. -/
def stackPass (sizes : List ℕ) (st : List (BitVec 64) × BitVec 64) (size : ℕ) :
    List (BitVec 64) × BitVec 64 :=
  (List.range sizes.length).foldl (stackStep sizes size) st

/-- `stack_offsets`: `largest = max(sizes)` (`0` if none), a pass per size from `largest` down,
then `(offsets, log2_ceil(total))`. -/
def stackOffsetsRust (sizes : List ℕ) : List (BitVec 64) × ℕ :=
  let largest := sizes.foldl max 0
  let st := (List.range (largest + 1)).reverse.foldl (stackPass sizes)
    (List.replicate sizes.length 0#64, 0#64)
  (st.1, log2CeilRust st.2)

/-- The blocks in the order the passes place them. -/
private def stackOrder (sizes : List ℕ) : List ℕ :=
  (List.range (sizes.foldl max 0 + 1)).reverse.flatMap fun s ↦
    (List.range sizes.length).filter fun i ↦ decide (sizes.getD i 0 = s)

/-- The specification's order. -/
private def stackLe (sizes : List ℕ) (i j : ℕ) : Bool :=
  decide (sizes.getD j 0 < sizes.getD i 0) ||
    (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j))

private theorem le_foldl_max (l : List ℕ) (a : ℕ) :
    a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := ih (max a b)
    refine ⟨le_trans (le_max_left a b) h1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right a x) h1
    · exact h2 x hx

private theorem mem_stackOrder (sizes : List ℕ) (i : ℕ) :
    i ∈ stackOrder sizes ↔ i < sizes.length := by
  simp only [stackOrder, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨_, _, h, _⟩
    exact h
  · intro h
    refine ⟨sizes.getD i 0, ?_, h, rfl⟩
    have := (le_foldl_max sizes 0).2 (sizes.getD i 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      exact List.getElem_mem h)
    omega

private theorem nodup_stackOrder (sizes : List ℕ) : (stackOrder sizes).Nodup := by
  rw [stackOrder, List.nodup_flatMap]
  refine ⟨fun s _ ↦ List.nodup_range.filter _, ?_⟩
  refine (List.nodup_range.reverse).imp ?_
  intro a b hab x hxa hxb
  simp only [List.mem_filter, decide_eq_true_eq] at hxa hxb
  exact hab (by omega)

private theorem stackOrder_perm (sizes : List ℕ) :
    (stackOrder sizes).Perm (List.range sizes.length) := by
  rw [List.perm_ext_iff_of_nodup (nodup_stackOrder sizes) List.nodup_range]
  intro i
  rw [mem_stackOrder, List.mem_range]

private theorem pairwise_stackOrder (sizes : List ℕ) :
    (stackOrder sizes).Pairwise fun i j ↦ stackLe sizes i j = true := by
  rw [stackOrder, List.pairwise_flatMap]
  constructor
  · intro s _
    refine (List.pairwise_lt_range.filter _).imp_of_mem ?_
    intro a b ha hb hab
    simp only [List.mem_filter, decide_eq_true_eq] at ha hb
    simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · rw [List.pairwise_reverse]
    refine List.pairwise_lt_range.imp ?_
    intro a b hab x hx y hy
    simp only [List.mem_filter, decide_eq_true_eq] at hx hy
    simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

private theorem stackOrder_eq (sizes : List ℕ) :
    (List.range sizes.length).mergeSort (stackLe sizes) = stackOrder sizes := by
  apply List.Perm.eq_of_pairwise (le := fun i j ↦ stackLe sizes i j = true)
  · intro a b _ _ hab hba
    simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab hba
    omega
  · apply List.pairwise_mergeSort
    · intro a b c hab hbc
      simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab hbc ⊢
      omega
    · intro a b
      simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      omega
  · exact pairwise_stackOrder sizes
  · exact (List.mergeSort_perm _ _).trans (stackOrder_perm sizes).symm

/-- The passes, as one fold over `stackOrder`. -/
private theorem stackPasses_eq (sizes : List ℕ) (st : List (BitVec 64) × BitVec 64) :
    (List.range (sizes.foldl max 0 + 1)).reverse.foldl (stackPass sizes) st =
      (stackOrder sizes).foldl (fun st i ↦
        (st.1.set i st.2, st.2 + 1#64 <<< (sizes.getD i 0 % 64))) st := by
  rw [stackOrder, List.foldl_flatMap]
  congr 1
  funext st s
  rw [List.foldl_filter, stackPass]
  congr 1
  funext st i
  unfold stackStep
  by_cases h : sizes.getD i 0 = s
  · subst h
    simp
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- The machine-word fold and the specification's fold agree while the total fits in `u64`. -/
private theorem stackFold_rel (sizes : List ℕ) :
    ∀ (Q : List ℕ) (o : List (BitVec 64)) (t : BitVec 64),
      t.toNat + (Q.map fun i ↦ 2 ^ sizes.getD i 0).sum < 2 ^ 64 →
      let R := Q.foldl (fun st i ↦
        (st.1.set i st.2, st.2 + 1#64 <<< (sizes.getD i 0 % 64))) (o, t)
      let R' := Q.foldl (fun (acc : List ℕ × ℕ) i ↦
        (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0)) (o.map BitVec.toNat, t.toNat)
      R.1.map BitVec.toNat = R'.1 ∧ R.2.toNat = R'.2
  | [], o, t, _ => by simp
  | i :: Q, o, t, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    have hs : 2 ^ sizes.getD i 0 < 2 ^ 64 := by omega
    have hs' : sizes.getD i 0 < 64 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hs
    have hadd : (t + 1#64 <<< (sizes.getD i 0 % 64)).toNat = t.toNat + 2 ^ sizes.getD i 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hs', Nat.shiftLeft_eq]
      simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow (by norm_num : 0 < 64), one_mul,
        Nat.mod_eq_of_lt hs]
      exact Nat.mod_eq_of_lt (by omega)
    have := stackFold_rel sizes Q (o.set i t) (t + 1#64 <<< (sizes.getD i 0 % 64))
      (by rw [hadd]; omega)
    simp only [List.foldl_cons]
    rw [List.map_set, hadd] at this
    exact this

private theorem sum_map_range_getD (sizes : List ℕ) :
    ((List.range sizes.length).map fun i ↦ 2 ^ sizes.getD i 0).sum = (sizes.map (2 ^ ·)).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [List.getElem?_eq_getElem h1]

/-- **`stack_offsets` is `stackOffsets`**, while the blocks' total fits a `u64` (at the verifier's
calls it is at most `2^30`). -/
theorem stackOffsetsRust_eq (sizes : List ℕ) (h : (sizes.map (2 ^ ·)).sum < 2 ^ 64) :
    (stackOffsetsRust sizes).1.map BitVec.toNat = (stackOffsets sizes).1 ∧
      (stackOffsetsRust sizes).2 = (stackOffsets sizes).2 := by
  have hsum : ((stackOrder sizes).map fun i ↦ 2 ^ sizes.getD i 0).sum < 2 ^ 64 := by
    rw [((stackOrder_perm sizes).map _).sum_eq, sum_map_range_getD]
    exact h
  have hrel := stackFold_rel sizes (stackOrder sizes) (List.replicate sizes.length 0#64) 0#64
    (by simpa using hsum)
  have hspec : stackOffsets sizes =
      let placed := (stackOrder sizes).foldl (fun (acc : List ℕ × ℕ) i ↦
        (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0)) (List.replicate sizes.length 0, 0)
      (placed.1, log2Ceil placed.2) := by
    rw [← stackOrder_eq]
    rfl
  simp only [List.map_replicate, BitVec.toNat_ofNat, Nat.zero_mod] at hrel
  rw [hspec]
  simp only [stackOffsetsRust, stackPasses_eq, log2CeilRust_eq]
  exact ⟨hrel.1, by rw [hrel.2]⟩

end

end Rv64mc.Model
