import Statement.LeanVmVerifier

/-!
# The multilinear helpers as the Rust computes them

`crates/verifier/src/multilinear.rs`, one mirror per function, following the Rust's loops: a loop
`for i in 0..n` over a buffer is `(List.range n).foldl` of one iteration's update, so the state
after `i` iterations is the fold over `List.range i`. Each mirror is proved equal to its
counterpart in `Statement/LeanVmVerifier.lean`. A `u64` is a `BitVec 64`; a shift by a `usize`
amount is masked to six bits, as the release build (no overflow checks) computes it.
A multiplication the Rust does through `Scaler` is written `* r`.
-/

namespace Rv64Verifier.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- `E::new(x, 0, 0)`. -/
def eNew (x : BitVec 64) : E := ofK (BF64.ofBitVec x)

/-- `E::new(n >> k & 1, 0, 0)`, a shift by a `usize`. -/
def bitE (n : BitVec 64) (k : ℕ) : E := eNew ((n >>> (k % 64)) &&& 1#64)

theorem bitE_eq (n : BitVec 64) {k : ℕ} (hk : k < 64) :
    bitE n k = eOfNat ((n.toNat >>> k) % 2) := by
  have h : (n >>> (k % 64)) &&& 1#64 = BitVec.ofNat 64 ((n.toNat >>> k) % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [Nat.mod_eq_of_lt hk, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.and_one_is_mod]
    have : (n.toNat >>> k) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  simp only [bitE, eNew, eOfNat, K.ofBits, h]

/-! ## `eq_eval`, `dot`, `poly_eval`, `index_mle` -/

/-- `eq_eval`: `result *= 1 + x + y` over the zipped slices. -/
def eqEvalRust (left right : List E) : E :=
  (left.zip right).foldl (fun result (x, y) ↦ result * (1 + x + y)) 1

theorem eqEvalRust_eq (left right : List E) : eqEvalRust left right = eqEval left right := by
  simp only [eqEvalRust, eqEval, ← List.map_uncurry_zip_eq_zipWith, List.foldl_map]
  rfl

/-- `dot`: `result += x * y` over the zipped slices. -/
def dotRust (left right : List E) : E :=
  (left.zip right).foldl (fun result (x, y) ↦ result + x * y) 0

theorem dotRust_eq (left right : List E) : dotRust left right = dot left right := by
  simp only [dotRust, dot, ← List.map_uncurry_zip_eq_zipWith, List.foldl_map]
  rfl

/-- `poly_eval`: Horner over the reversed coefficients. -/
def polyEvalRust (coefficients : List E) (point : E) : E :=
  coefficients.reverse.foldl (fun acc c ↦ acc * point + c) 0

theorem polyEvalRust_eq (coefficients : List E) (point : E) :
    polyEvalRust coefficients point = polyEval coefficients point := by
  simp only [polyEvalRust, polyEval, List.foldl_reverse]

/-- `index_mle`: `result *= 1 + c·(1 + g)`, then `g = g.square()`, from `(1, GEN)`. -/
def indexMleRust (point : List E) : E :=
  (point.foldl (fun (acc : E × E) c ↦ (acc.1 * (1 + c * (1 + acc.2)), acc.2 ^ 2)) (1, gen)).1

theorem indexMleRust_eq (point : List E) : indexMleRust point = indexMle point := by
  suffices ∀ (acc g : E), (point.foldl (fun (acc : E × E) c ↦
      (acc.1 * (1 + c * (1 + acc.2)), acc.2 ^ 2)) (acc, g)).1 = indexMleFrom g point acc from
    this 1 gen
  induction point with
  | nil => intro acc g; rfl
  | cons r rs ih => intro acc g; exact ih _ _

/-! ## `log2_ceil`, `log2_strict` -/

/-- `saturating_sub(1)` on a `u64`. -/
def satSubOne (value : BitVec 64) : BitVec 64 := if value = 0#64 then 0#64 else value - 1#64

/-- `log2_ceil`: `64 - value.saturating_sub(1).leading_zeros()`. -/
def log2CeilRust (value : BitVec 64) : ℕ := 64 - (satSubOne value).clz.toNat

theorem sub_clz_eq_bitLength (x : BitVec 64) : 64 - x.clz.toNat = bitLength x.toNat := by
  by_cases hx : x = 0#64
  · subst hx
    have : (0#64).clz = 64#64 := BitVec.clz_eq_iff_eq_zero.mpr rfl
    simp [this, bitLength]
  · have hlt : x.clz < 64#64 := BitVec.clz_lt_iff_ne_zero.mpr hx
    have hlt' : x.clz.toNat < 64 := by
      have := BitVec.lt_def.mp hlt
      simpa using this
    have hlo := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by norm_num) hx
    have hhi := BitVec.toNat_lt_two_pow_sub_clz (x := x)
    have hne : x.toNat ≠ 0 := by
      intro h
      exact hx (BitVec.eq_of_toNat_eq (by simpa using h))
    have hlog : Nat.log2 x.toNat = 64 - 1 - x.clz.toNat := by
      rw [Nat.log2_eq_iff hne]
      refine ⟨hlo, ?_⟩
      have : 64 - 1 - x.clz.toNat + 1 = 64 - x.clz.toNat := by omega
      rw [this]
      exact hhi
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
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      simp only [BitVec.toNat_ofNat]
      omega)]
    simp

/-- `log2_strict`: `value.is_power_of_two()` (as `value != 0 && value & (value - 1) == 0`), then
`trailing_zeros`. -/
def log2StrictRust (value : BitVec 64) : Option ℕ :=
  if value ≠ 0#64 ∧ value &&& (value - 1#64) = 0#64 then some value.ctz.toNat else none

theorem log2StrictRust_eq (value : BitVec 64) : log2StrictRust value = log2Strict value.toNat := by
  have hz : value ≠ 0#64 ↔ value.toNat ≠ 0 := by
    constructor
    · intro h h'; exact h (BitVec.eq_of_toNat_eq (by simpa using h'))
    · intro h h'; subst h'; exact h rfl
  have hand : value ≠ 0#64 →
      (value &&& (value - 1#64) = 0#64 ↔ value.toNat &&& (value.toNat - 1) = 0) := by
    intro hv
    have hv' := hz.mp hv
    rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      simp only [BitVec.toNat_ofNat]
      omega)]
    simp
  unfold log2StrictRust log2Strict
  by_cases hv : value = 0#64
  · subst hv; simp
  · have hv' := hz.mp hv
    by_cases hp : value &&& (value - 1#64) = 0#64
    · have hp' := (hand hv).mp hp
      obtain ⟨k, hk⟩ := Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mp ⟨hv', hp'⟩
      have hbit := BitVec.getLsbD_true_ctz_of_ne_zero hv
      rw [BitVec.getLsbD, hk, Nat.testBit_two_pow] at hbit
      have hc : value.ctz.toNat = k := (by simpa using hbit : k = value.ctz.toNat).symm
      have c1 : (value ≠ 0#64 ∧ value &&& (value - 1#64) = 0#64) = True := eq_true ⟨hv, hp⟩
      have c2 : (0 < value.toNat ∧ value.toNat &&& (value.toNat - 1) = 0) = True :=
        eq_true ⟨Nat.pos_of_ne_zero hv', hp'⟩
      have c3 : (value.toNat = 0) = False := eq_false hv'
      simp only [c1, c2, ite_true, bitLength, c3, ite_false]
      rw [hc, hk, Nat.log2_two_pow, Nat.add_sub_cancel]
    · have c1 : (value ≠ 0#64 ∧ value &&& (value - 1#64) = 0#64) = False :=
        eq_false (fun h ↦ hp h.2)
      have c2 : (0 < value.toNat ∧ value.toNat &&& (value.toNat - 1) = 0) = False :=
        eq_false (fun h ↦ hp ((hand hv).mpr h.2))
      simp only [c1, c2, ite_false]

/-! ## `selector_point`, `padding_weight` -/

/-- `selector_point`: `E::new(selector >> bit & 1, 0, 0)` for `bit` in `0..length`. -/
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

theorem foldl_congr_mem {α β : Type} {l : List α} {f g : β → α → β}
    (h : ∀ b, ∀ a ∈ l, f b a = g b a) (init : β) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h init a (by simp)]
    exact ih (fun b a' ha' ↦ h b a' (by simp [ha'])) _

theorem paddingWeightRust_eq (point : List E) (n : BitVec 64) (h : point.length < 64) :
    paddingWeightRust point n = paddingWeight point n.toNat := by
  have hlow : point.zipIdx.foldl
      (fun pad (rk : E × ℕ) ↦ (1 + bitE n rk.2) * rk.1 + (1 + bitE n rk.2 + rk.1) * pad) 1 =
      point.zipIdx.foldl (fun pad (rk : E × ℕ) ↦
        let b := eOfNat ((n.toNat >>> rk.2) % 2)
        (1 + b) * rk.1 + (1 + b + rk.1) * pad) 1 := by
    apply foldl_congr_mem
    intro pad rk hrk
    have hk : rk.2 < point.length := by
      have := List.mem_zipIdx hrk
      omega
    simp only [bitE_eq n (show rk.2 < 64 by omega)]
  simp only [paddingWeightRust, paddingWeight, bitE_eq n h, hlow]

/-! ## `multilinear_eval` -/

/-- One iteration of `multilinear_eval`'s inner loop: `cur[i] = cur[2i] + (cur[2i] + cur[2i+1])·r`. -/
def mleStep (r : E) (cur : List E) (i : ℕ) : List E :=
  cur.set i (cur.getD (2 * i) 0 + (cur.getD (2 * i) 0 + cur.getD (2 * i + 1) 0) * r)

/-- One coordinate: the inner loop over `0..len/2`, then `truncate(len/2)`. -/
def mlePass (cur : List E) (r : E) : List E :=
  ((List.range (cur.length / 2)).foldl (mleStep r) cur).take (cur.length / 2)

/-- `multilinear_eval`: the size check, the passes, then `cur[0]`. -/
def multilinearEvalRust (mle point : List E) : Option E :=
  if point.length < 64 ∧ mle.length = 2 ^ point.length then
    some ((point.foldl mlePass mle).getD 0 0)
  else none

theorem foldPairs_getElem? (r : E) : ∀ (A : List E) (i : ℕ), (foldPairs r A)[i]? =
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

theorem foldPairs_length (r : E) : ∀ (A : List E), (foldPairs r A).length = A.length / 2
  | [] => by simp [foldPairs]
  | [a] => by simp [foldPairs]
  | a :: b :: rest => by
    rw [foldPairs, List.length_cons, foldPairs_length r rest]
    simp only [List.length_cons]
    omega

theorem mle_inner (r : E) (A : List E) :
    ∀ i, i ≤ A.length / 2 →
      (List.range i).foldl (mleStep r) A = (foldPairs r A).take i ++ A.drop i
  | 0, _ => by simp
  | i + 1, hi => by
    rw [List.range_succ, List.foldl_append, mle_inner r A i (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, mleStep]
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
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_take, ite_eq_left (by omega), hval]
      congr 1
      ring
    · rw [ite_eq_right (Ne.symm hn)]
      by_cases hlt : n < i
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
        simp only [List.getElem?_take]
        rw [ite_eq_left hlt, ite_eq_left (by omega)]
      · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
        simp only [List.length_take, List.getElem?_drop]
        congr 1
        omega

theorem mlePass_eq (cur : List E) (r : E) : mlePass cur r = foldPairs r cur := by
  rw [mlePass, mle_inner r cur _ le_rfl, ← foldPairs_length r cur]
  simp

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

/-! ## `eq_kernel` -/

/-- One iteration of `eq_kernel`'s inner loop at `j < half`: `h = v·r` into `out[j + half]`, then
`v += h`. -/
def eqKernelStep (r : E) (half : ℕ) (out : List E) (j : ℕ) : List E :=
  let h := out.getD j 0 * r
  (out.set (j + half) h).set j (out.getD j 0 + h)

/-- The pass for coordinate `k`: the inner loop over `0..2^k`. -/
def eqKernelPass (r : E) (k : ℕ) (out : List E) : List E :=
  (List.range (2 ^ k)).foldl (eqKernelStep r (2 ^ k)) out

/-- `eq_kernel`: `2^len` zeros, `out[0] = 1`, then a pass per `(k, r)` of `point.iter().enumerate()`. -/
def eqKernelRust (point : List E) : List E :=
  point.zipIdx.foldl (fun out rk ↦ eqKernelPass rk.1 rk.2 out)
    ((List.replicate (2 ^ point.length) 0).set 0 1)

theorem eqKernel_length (point : List E) : (eqKernel point).length = 2 ^ point.length := by
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
theorem eqKernel_inner (r : E) (A : List E) (m : ℕ) (hm : A.length ≤ m) :
    ∀ j, j ≤ A.length →
      (List.range j).foldl (eqKernelStep r A.length) (A ++ List.replicate m 0) =
        (A.take j).map (fun a ↦ a + a * r) ++ A.drop j ++ (A.take j).map (· * r) ++
          List.replicate (m - j) 0
  | 0, _ => by simp
  | j + 1, hj => by
    rw [List.range_succ, List.foldl_append, eqKernel_inner r A m hm j (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, eqKernelStep]
    have hv : ((A.take j).map (fun a ↦ a + a * r) ++ A.drop j ++ (A.take j).map (· * r) ++
        List.replicate (m - j) 0).getD j 0 = A.getD j 0 := by
      simp only [List.getD_eq_getElem?_getD, List.append_assoc]
      rw [List.getElem?_append_right (by simp)]
      simp only [List.length_map, List.length_take]
      rw [List.getElem?_append_left (by simp; omega)]
      simp only [List.getElem?_drop]
      congr 2
      omega
    rw [hv]
    apply List.ext_getElem?
    intro n
    simp only [List.getElem?_set, List.length_set, List.length_append, List.length_map,
      List.length_take, List.length_drop, List.length_replicate, List.append_assoc,
      List.getElem?_append, List.getElem?_map, List.getElem?_take, List.getElem?_drop,
      List.getElem?_replicate, List.getD_eq_getElem?_getD]
    have hjA : j < A.length := by omega
    have hmin : min j A.length = j := by omega
    have hmin' : min (j + 1) A.length = j + 1 := by omega
    simp only [hmin, hmin']
    obtain ⟨a, ha⟩ : ∃ a, A[j]? = some a := ⟨A[j], List.getElem?_eq_getElem hjA⟩
    split_ifs <;> first
      | (exfalso; omega)
      | rfl
      | (simp only [ha, Option.getD_some]; done)
      | (have e1 : n = j := by omega
         subst e1; simp [ha])
      | (rw [show n - (j + 1) - (A.length - (j + 1)) = j by omega, ha]; simp)
      | (congr 1; omega)
      | (congr 2; omega)

theorem eqKernelPass_eq (r : E) (k : ℕ) (A : List E) (m : ℕ) (hA : A.length = 2 ^ k)
    (hm : 2 ^ k ≤ m) :
    eqKernelPass r k (A ++ List.replicate m 0) =
      A.map (· * (1 + r)) ++ A.map (· * r) ++ List.replicate (m - 2 ^ k) 0 := by
  rw [eqKernelPass, ← hA, eqKernel_inner r A m (by omega) A.length le_rfl]
  simp only [List.take_length, List.drop_length, List.append_nil]
  congr 2
  apply List.map_congr_left
  intro a _
  ring

theorem eqKernelRust_prefix (n : ℕ) (pre : List E) (h : pre.length ≤ n) :
    pre.zipIdx.foldl (fun out rk ↦ eqKernelPass rk.1 rk.2 out)
        ((List.replicate (2 ^ n) 0).set 0 1) =
      eqKernel pre ++ List.replicate (2 ^ n - 2 ^ pre.length) 0 := by
  induction pre using List.reverseRecOn with
  | nil =>
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = t + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
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
    have hk : eqKernel (l ++ [r]) = (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
      simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hk, show 2 ^ n - 2 ^ l.length - 2 ^ l.length = 2 ^ n - 2 ^ (l ++ [r]).length by
      simp only [List.length_append, List.length_cons, List.length_nil, pow_succ]
      omega]

theorem eqKernelRust_eq (point : List E) : eqKernelRust point = eqKernel point := by
  rw [eqKernelRust, eqKernelRust_prefix _ point le_rfl]
  simp

/-! ## Placements -/

/-- `Placement`: `variables: usize` (here `variableCount`), `index: u64`. -/
structure PlacementRust where
  variableCount : ℕ
  index : BitVec 64

/-- The specification's placement. -/
def PlacementRust.toSpec (p : PlacementRust) : Placement := ⟨p.variableCount, p.index.toNat⟩

/-- `Placement::stack_point`: `[point, selector_point(index >> variables, stack_log - variables)]`. -/
def PlacementRust.stackPoint (p : PlacementRust) (point : List E) (stackLog : ℕ) : List E :=
  point ++ selectorPointRust (p.index >>> (p.variableCount % 64)) (stackLog - p.variableCount)

/-- `Placement::eq_above`: `eq_eval(selector_point(index >> variables, len - variables),
&point[variables..])`. -/
def PlacementRust.eqAbove (p : PlacementRust) (point : List E) : E :=
  eqEvalRust (selectorPointRust (p.index >>> (p.variableCount % 64)) (point.length - p.variableCount))
    (point.drop p.variableCount)

theorem selectorPointRust_shift (index : BitVec 64) (v L : ℕ) (h : L ≤ 64 - v) :
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
    p.eqAbove point = p.toSpec.eqAbove point := by
  rw [PlacementRust.eqAbove, Placement.eqAbove, eqEvalRust_eq,
    selectorPointRust_shift _ _ _ (by omega)]
  rfl

/-! ## `stack_offsets` -/

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
def stackOrder (sizes : List ℕ) : List ℕ :=
  (List.range (sizes.foldl max 0 + 1)).reverse.flatMap fun s ↦
    (List.range sizes.length).filter fun i ↦ decide (sizes.getD i 0 = s)

/-- The specification's order. -/
def stackLe (sizes : List ℕ) (i j : ℕ) : Bool :=
  decide (sizes.getD j 0 < sizes.getD i 0) ||
    (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j))

theorem le_foldl_max (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := ih (max a b)
    refine ⟨le_trans (le_max_left a b) h1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right a x) h1
    · exact h2 x hx

theorem mem_stackOrder (sizes : List ℕ) (i : ℕ) : i ∈ stackOrder sizes ↔ i < sizes.length := by
  simp only [stackOrder, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨_, _, h, _⟩
    exact h
  · intro h
    refine ⟨sizes.getD i 0, ?_, h, rfl⟩
    have := (le_foldl_max sizes 0).2 (sizes.getD i 0) (by
      rw [List.getD_eq_getElem _ _ h]
      exact List.getElem_mem h)
    omega

theorem nodup_stackOrder (sizes : List ℕ) : (stackOrder sizes).Nodup := by
  rw [stackOrder, List.nodup_flatMap]
  refine ⟨fun s _ ↦ List.nodup_range.filter _, ?_⟩
  refine (List.nodup_range.reverse).imp ?_
  intro a b hab x hxa hxb
  simp only [List.mem_filter, decide_eq_true_eq] at hxa hxb
  exact hab (by omega)

theorem stackOrder_perm (sizes : List ℕ) : (stackOrder sizes).Perm (List.range sizes.length) := by
  rw [List.perm_ext_iff_of_nodup (nodup_stackOrder sizes) List.nodup_range]
  intro i
  rw [mem_stackOrder, List.mem_range]

theorem pairwise_stackOrder (sizes : List ℕ) :
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

theorem stackOrder_eq (sizes : List ℕ) :
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
theorem stackPasses_eq (sizes : List ℕ) (st : List (BitVec 64) × BitVec 64) :
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
theorem stackFold_rel (sizes : List ℕ) :
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

theorem sum_map_range_getD (sizes : List ℕ) :
    ((List.range sizes.length).map fun i ↦ 2 ^ sizes.getD i 0).sum = (sizes.map (2 ^ ·)).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [List.getElem?_eq_getElem h1]

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

theorem multilinearEvalRust_some {mle point : List E} {v : E}
    (h : multilinearEvalRust mle point = some v) : v = multilinearEval mle point := by
  by_cases hc : point.length < 64 ∧ mle.length = 2 ^ point.length
  · rw [multilinearEvalRust_eq _ _ hc] at h
    exact (Option.some.inj h).symm
  · simp [multilinearEvalRust, hc] at h

end Rv64Verifier.Model
