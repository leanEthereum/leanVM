/-
  LeanVM.Facts.Hotwire

  Hotwire's generic lemmas at leanVM's field `E`: the statement's multilinear definitions are the
  generic equality weights, and the link phase's Rust forms are the generic definitions.
-/

module

public import Statement.Verifier.Lib
public import LeanVM.Protocol.Hotwire.ShiftEq
public import LeanVM.Protocol.Hotwire.Window
import Mathlib.Data.List.GetD
import LeanVM.Parameters.Field
import Mathlib.Tactic.Ring

/-!
# Hotwire at `E`

`LeanVM/Protocol/Hotwire/` holds over any commutative ring; here it meets the statement's
definitions (`Statement/Verifier/Multilinear.lean`, transcribing `crates/verifier/src/multilinear.rs`),
over `E`, of characteristic two, where `1 − z = 1 + z`:

* `eqEval_eq_eqPt`: `eqEval` (`eq_eval`) is `eqPt`; `eqEval_eq_sum`: `Σ_j eq(r, j)·eq(ζ, j)`;
* `eqKernel_getD`: `eqKernel` (`eq_kernel`) lists `eqAt pt j` for `j < 2^|pt|`;
* `multilinearEval_eq_mle`, `dot_eqKernel_eq_mle`: `multilinear_eval` and `dot(eq_kernel(pt), ·)`
  are `mle`;
* `paddingWeight_eq_mle`: `padding_weight(pt, n)` is the multilinear extension of `[j ≥ n]`, for
  `n ≤ 2^|pt|`; `one_add_paddingWeight_eq_mle`: `1 + padding_weight(pt, n)`, the link's
  `less_than`, that of `[j < n]`;
* `eqEval_selectorPoint`: `eq_eval(selector_point(s, |x|), x) = eq(x, s)`.

The link phase's own functions (`crates/verifier/src/link.rs`) are not in the statement yet; their
Rust forms, written out, are the generic definitions (`link*`): `linkEqAt_eq` (`eq_at`),
`linkShiftEq_eq_shiftSum` (`shift_eq`), `linkWindowShift_getD` and `linkWindowShift_eq`
(`window_shift(eq_kernel(r_0), s)` read against a chunk).
-/

namespace LeanVM.Protocol.Hotwire

open Finset LeanVM.Parameters

@[expose] public section

/-! ## Integers -/

theorem eOfNat_zero : Verifier.eOfNat 0 = 0 := by
  unfold Verifier.eOfNat
  rw [show K.ofBits 0 = 0 by decide +kernel]
  simp

theorem eOfNat_one : Verifier.eOfNat 1 = 1 := by
  unfold Verifier.eOfNat
  rw [show K.ofBits 1 = 1 by decide +kernel]
  simp

/-- A bit as `0` or `1` in `E`. -/
theorem eOfNat_mod_two (m : ℕ) : Verifier.eOfNat (m % 2) = if m % 2 = 1 then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h, eOfNat_zero, eOfNat_one]

/-! ## Characteristic two -/

/-- `eq(z, x) = 1 + z + x` in `E`, as the Rust writes it. -/
theorem eq1_E (z x : E) : eq1 z x = 1 + z + x := eq1_of_charTwo z x

/-! ## `eq_eval` -/

theorem foldl_mul_zipWith_eqPt : ∀ (ζ r : List E) (a : E),
    (List.zipWith (fun x z ↦ 1 + x + z) ζ r).foldl (· * ·) a = a * eqPt ζ r
  | [], _, a => by simp
  | _ :: _, [], a => by simp [eqPt]
  | z :: ζ, x :: r, a => by
    rw [List.zipWith_cons_cons, List.foldl_cons, foldl_mul_zipWith_eqPt ζ r, eqPt_cons, eq1_E,
      mul_assoc]

/-- **`eq_eval` is the equality weight between two points** (a longer one's extra coordinates
dropped, as `zip` drops them). -/
theorem eqEval_eq_eqPt (ζ r : List E) : Verifier.eqEval ζ r = eqPt ζ r :=
  (foldl_mul_zipWith_eqPt ζ r 1).trans (one_mul _)

/-- `eq_eval(ζ, r) = Σ_{j < 2^n} eq(r, j)·eq(ζ, j)` for two points of `n` coordinates. -/
theorem eqEval_eq_sum (ζ r : List E) (h : ζ.length = r.length) :
    Verifier.eqEval ζ r = ∑ j ∈ range (2 ^ ζ.length), eqAt r j * eqAt ζ j := by
  rw [eqEval_eq_eqPt, sum_eqAt_mul_eqAt ζ r h]

/-! ## `eq_kernel` -/

theorem eqKernel_append (pt : List E) (r : E) :
    Verifier.eqKernel (pt ++ [r]) =
      (Verifier.eqKernel pt).map (· * (1 + r)) ++ (Verifier.eqKernel pt).map (· * r) := by
  unfold Verifier.eqKernel
  rw [List.foldl_concat]

theorem eqKernel_length (pt : List E) : (Verifier.eqKernel pt).length = 2 ^ pt.length := by
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [eqKernel_append, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

theorem getD_map_mul (l : List E) (c : E) (w : ℕ) :
    (l.map (· * c)).getD w 0 = l.getD w 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[w]? <;> simp

/-- **`eq_kernel` lists the equality weights**, the first coordinate on the lowest bit. -/
theorem eqKernel_getD (pt : List E) (w : ℕ) :
    (Verifier.eqKernel pt).getD w 0 = if w < 2 ^ pt.length then eqAt pt w else 0 := by
  induction pt using List.reverseRecOn generalizing w with
  | nil =>
    rcases w with _ | w
    · rfl
    · simp [Verifier.eqKernel, List.getD_eq_getElem?_getD]
  | append_singleton pt r ih =>
    have hlen := eqKernel_length pt
    have hp : 2 ^ (pt.length + 1) = 2 ^ pt.length + 2 ^ pt.length := by rw [pow_succ]; ring
    rw [eqKernel_append, List.length_append, List.length_singleton, eqAt_append]
    by_cases hw : w < 2 ^ pt.length
    · rw [List.getD_append _ _ _ _ (by simpa [hlen] using hw), getD_map_mul, ih,
        ite_eq_left hw, ite_eq_left (by omega), Nat.div_eq_of_lt hw]
      simp [eqAt_cons, CharTwo.sub_eq_add]
    · rw [List.getD_append_right _ _ _ _ (by simp [hlen]; omega), List.length_map, hlen,
        getD_map_mul, ih]
      by_cases hw2 : w < 2 ^ (pt.length + 1)
      · have hq : w / 2 ^ pt.length = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [ite_eq_left hw2, hq, ite_eq_left (by omega), eqAt_mod pt w,
          eqAt_mod pt (w - 2 ^ pt.length), ← Nat.mod_eq_sub_mod (by omega)]
        simp [eqAt_cons]
      · rw [ite_eq_right hw2, ite_eq_right (by omega), zero_mul]

/-! ## `multilinear_eval` and `dot` -/

theorem foldPairs_getD (r : E) : ∀ (l : List E) (w : ℕ), 2 * w + 1 < l.length →
    (Verifier.foldPairs r l).getD w 0 = l.getD (2 * w) 0 * (1 + r) + l.getD (2 * w + 1) 0 * r
  | a :: b :: rest, 0, _ => by simp [Verifier.foldPairs]
  | a :: b :: rest, w + 1, h => by
    rw [show 2 * (w + 1) = 2 * w + 1 + 1 by ring]
    simp only [Verifier.foldPairs, List.getD_cons_succ]
    exact foldPairs_getD r rest w (by simp at h; omega)
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

theorem foldPairs_length (r : E) : ∀ l : List E, (Verifier.foldPairs r l).length = l.length / 2
  | a :: b :: rest => by
    simp only [Verifier.foldPairs, List.length_cons, foldPairs_length r rest]; omega
  | [] => rfl
  | [_] => by simp [Verifier.foldPairs]

/-- **`multilinear_eval`** of a table of `2^|pt|` entries is its multilinear extension. -/
theorem multilinearEval_eq_mle : ∀ (pt t : List E), t.length = 2 ^ pt.length →
    Verifier.multilinearEval t pt = mle pt (t.getD · 0)
  | [], t, h => by
    rcases t with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at h
    · simp [Verifier.multilinearEval, mle]
    · simp at h
  | r :: rs, t, h => by
    have hl : (Verifier.foldPairs r t).length = 2 ^ rs.length := by
      rw [foldPairs_length, h, List.length_cons, pow_succ]; omega
    have step : Verifier.multilinearEval t (r :: rs) =
        Verifier.multilinearEval (Verifier.foldPairs r t) rs := rfl
    rw [step, multilinearEval_eq_mle rs _ hl, mle, mle, List.length_cons, pow_succ,
      mul_comm (2 ^ rs.length) 2, sum_range_two_mul]
    refine sum_congr rfl fun w hw ↦ ?_
    have hw' := mem_range.1 hw
    rw [foldPairs_getD r t w (by rw [h, List.length_cons, pow_succ]; omega), eqAt_cons_two_mul,
      eqAt_cons_two_mul_add_one, CharTwo.sub_eq_add]
    ring

theorem foldl_add_eq (l : List E) (a : E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-- `dot` of two lists of one length is the sum of the products. -/
theorem dot_eq_sum : ∀ (a b : List E), a.length = b.length →
    Verifier.dot a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0
  | [], [], _ => by simp [Verifier.dot]
  | x :: a, y :: b, h => by
    have ih := dot_eq_sum a b (by simpa using h)
    rw [Verifier.dot, foldl_add_eq, zero_add] at ih ⊢
    rw [List.zipWith_cons_cons, List.sum_cons, ih, List.length_cons, sum_range_succ']
    simp [add_comm]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **`dot(eq_kernel(pt), w)`** of a table of `2^|pt|` entries is its multilinear extension. -/
theorem dot_eqKernel_eq_mle (pt w : List E) (h : w.length = 2 ^ pt.length) :
    Verifier.dot (Verifier.eqKernel pt) w = mle pt (w.getD · 0) := by
  rw [dot_eq_sum _ _ (by rw [eqKernel_length, h]), eqKernel_length, mle]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [eqKernel_getD, ite_eq_left (mem_range.mp hj)]

/-! ## `padding_weight` -/

/-- One coordinate of `padding_weight`'s fold: from the extension of `[j ≥ n mod 2^k]` over the
first `k` coordinates to that of `[j ≥ n mod 2^{k+1}]` over `k + 1`, by bit `k` of `n`. -/
theorem padding_step (n : ℕ) (pt : List E) (r : E) :
    (1 + Verifier.eOfNat ((n >>> pt.length) % 2)) * r +
        (1 + Verifier.eOfNat ((n >>> pt.length) % 2) + r) *
          mle pt (fun j ↦ if n % 2 ^ pt.length ≤ j then 1 else 0) =
      mle (pt ++ [r]) (fun j ↦ if n % 2 ^ (pt ++ [r]).length ≤ j then 1 else 0) := by
  have hlen : (pt ++ [r]).length = pt.length + 1 := by simp
  have hpos : 0 < 2 ^ pt.length := Nat.two_pow_pos _
  have hm : n % 2 ^ pt.length < 2 ^ pt.length := Nat.mod_lt _ hpos
  have hlow : ∀ j < 2 ^ pt.length, eqAt (pt ++ [r]) j = eqAt pt j * (1 + r) := by
    intro j hj
    rw [eqAt_append, Nat.div_eq_of_lt hj]
    simp [eqAt_cons, CharTwo.sub_eq_add]
  have hhigh : ∀ j < 2 ^ pt.length, eqAt (pt ++ [r]) (2 ^ pt.length + j) = eqAt pt j * r := by
    intro j hj
    have hq : (2 ^ pt.length + j) / 2 ^ pt.length = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [eqAt_append, hq, eqAt_mod pt (2 ^ pt.length + j), Nat.add_mod_left, Nat.mod_eq_of_lt hj]
    simp [eqAt_cons]
  have hR : ∀ g : ℕ → E, mle (pt ++ [r]) g =
      (1 + r) * ∑ j ∈ range (2 ^ pt.length), eqAt pt j * g j +
        r * ∑ j ∈ range (2 ^ pt.length), eqAt pt j * g (2 ^ pt.length + j) := by
    intro g
    rw [mle, hlen, pow_succ, mul_two, sum_range_add, mul_sum, mul_sum]
    exact congrArg₂ (· + ·)
      (sum_congr rfl fun j hj ↦ by rw [hlow j (mem_range.mp hj)]; ring)
      (sum_congr rfl fun j hj ↦ by rw [hhigh j (mem_range.mp hj)]; ring)
  rw [hR, hlen, Nat.shiftRight_eq_div_pow, Nat.mod_pow_succ]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ pt.length) with hc | hc <;> rw [hc]
  · simp only [Nat.mul_zero, eOfNat_zero, add_zero, one_mul]
    rw [show ∑ j ∈ range (2 ^ pt.length), eqAt pt j *
        (if n % 2 ^ pt.length ≤ 2 ^ pt.length + j then (1 : E) else 0) = 1 from
      (sum_congr rfl fun j _ ↦ by rw [ite_eq_left (by omega), mul_one]).trans (sum_eqAt pt), mle]
    ring
  · simp only [Nat.mul_one, eOfNat_one, CharTwo.add_self_eq_zero, zero_mul, zero_add]
    rw [sum_eq_zero fun j hj ↦ by rw [ite_eq_right (by have := mem_range.mp hj; omega), mul_zero],
      mul_zero, zero_add, mle]
    refine congrArg (r * ·) (sum_congr rfl fun j _ ↦ ?_)
    by_cases hj : n % 2 ^ pt.length ≤ j
    · rw [ite_eq_left hj, ite_eq_left (by omega)]
    · rw [ite_eq_right hj, ite_eq_right (by omega)]

/-- `padding_weight`'s fold over the first `k` coordinates is the extension of
`[j ≥ n mod 2^k]`. -/
theorem foldl_padding (n : ℕ) (f : E → E × ℕ → E)
    (hf : ∀ pad r k, f pad (r, k) = (1 + Verifier.eOfNat ((n >>> k) % 2)) * r +
      (1 + Verifier.eOfNat ((n >>> k) % 2) + r) * pad) (pt : List E) :
    pt.zipIdx.foldl f 1 = mle pt (fun j ↦ if n % 2 ^ pt.length ≤ j then 1 else 0) := by
  induction pt using List.reverseRecOn with
  | nil =>
    simp only [List.zipIdx_nil, List.foldl_nil, mle, List.length_nil, pow_zero, sum_range_one,
      eqAt_nil, one_mul, Nat.mod_one, le_refl, ↓reduceIte]
  | append_singleton pt r ih =>
    rw [List.zipIdx_append, List.foldl_append, ih, List.zipIdx_singleton, List.foldl_cons,
      List.foldl_nil, hf, Nat.zero_add, padding_step]

/-- **`padding_weight(pt, n)` is the multilinear extension of `[j ≥ n]`**, for `n ≤ 2^|pt|`
(`doc/leanvm`, Lemma `lem:suffix`). -/
theorem paddingWeight_eq_mle (pt : List E) (n : ℕ) (hn : n ≤ 2 ^ pt.length) :
    Verifier.paddingWeight pt n = mle pt (fun j ↦ if n ≤ j then 1 else 0) := by
  unfold Verifier.paddingWeight
  rw [foldl_padding n _ ?_ pt, Nat.shiftRight_eq_div_pow]
  · rcases hn.lt_or_eq with hlt | rfl
    · rw [Nat.div_eq_of_lt hlt, Nat.zero_mod, eOfNat_zero, add_zero, one_mul, Nat.mod_eq_of_lt hlt]
    · rw [Nat.div_self (Nat.two_pow_pos _), show 1 % 2 = 1 from rfl, eOfNat_one,
        CharTwo.add_self_eq_zero, zero_mul]
      exact (sum_eq_zero fun j hj ↦ by
        dsimp only
        rw [ite_eq_right (by have := mem_range.mp hj; omega), mul_zero]).symm
  · intro _ _ _
    rfl

/-- **The link's `less_than(pt, n) = 1 + padding_weight(pt, n)`** is the multilinear extension of
`[j < n]`, for `n ≤ 2^|pt|`. -/
theorem one_add_paddingWeight_eq_mle (pt : List E) (n : ℕ) (hn : n ≤ 2 ^ pt.length) :
    1 + Verifier.paddingWeight pt n = mle pt (fun j ↦ if j < n then 1 else 0) := by
  rw [paddingWeight_eq_mle pt n hn]
  calc 1 + mle pt (fun j ↦ if n ≤ j then 1 else 0)
      = mle pt (fun _ ↦ 1) + mle pt (fun j ↦ if n ≤ j then 1 else 0) := by rw [mle_one]
    _ = mle pt (fun j ↦ if j < n then 1 else 0) := by
      unfold mle
      rw [← sum_add_distrib]
      refine sum_congr rfl fun j _ ↦ ?_
      dsimp only
      split_ifs <;> first | (exfalso; omega) | simp [CharTwo.add_self_eq_zero]

/-! ## `selector_point` -/

theorem selectorPoint_succ (s n : ℕ) :
    Verifier.selectorPoint s (n + 1) =
      Verifier.eOfNat (s % 2) :: Verifier.selectorPoint (s / 2) n := by
  simp [Verifier.selectorPoint, List.range_succ_eq_map, Nat.shiftRight_succ_inside]

theorem eqPt_selectorPoint : ∀ (x : List E) (s : ℕ),
    eqPt (Verifier.selectorPoint s x.length) x = eqAt x s
  | [], s => by simp [Verifier.selectorPoint]
  | x :: xs, s => by
    rw [List.length_cons, selectorPoint_succ, eqPt_cons, eqPt_selectorPoint xs, eqAt_cons,
      eOfNat_mod_two]
    rcases Nat.mod_two_eq_zero_or_one s with h | h <;> simp [h]

/-- **`eq_eval(selector_point(s, |x|), x) = eq(x, s)`**: the weight of the integer `s`'s low
`|x|` bits. -/
theorem eqEval_selectorPoint (x : List E) (s : ℕ) :
    Verifier.eqEval (Verifier.selectorPoint s x.length) x = eqAt x s := by
  rw [eqEval_eq_eqPt, eqPt_selectorPoint]

/-! ## The link phase's functions, as the Rust writes them

`crates/verifier/src/link.rs`'s functions are not in the statement yet; each lemma below states
its Rust form over `E` and equates it with the generic definition, for the statement's
transcription to meet by unfolding. -/

/-- **`eq_at(point, j)`**: the product from `1` over `point.iter().enumerate()` of `x` if bit `h`
of `j` is set and `1 + x` otherwise is `eq(point, j)`. -/
theorem linkEqAt_eq (pt : List E) (j : ℕ) :
    pt.zipIdx.foldl (fun acc p ↦ acc * if j >>> p.2 % 2 = 1 then p.1 else 1 + p.1) 1 =
      eqAt pt j :=
  (eqAt_eq_foldl_zipIdx pt j).symm

/-- **`shift_eq(zeta, r)`**: the loop from `(shift, carry) = (0, 1)` over `zeta.iter().zip(r)`,
`shift := shift·(1 + z + x) + carry·(1 + x)·z`, `carry *= x·(1 + z)`, ends at
`Σ_{j + 1 < 2^n} eq(r, j)·eq(ζ, j + 1)`. -/
theorem linkShiftEq_eq_shiftSum (ζ r : List E) (h : ζ.length = r.length) :
    ((ζ.zip r).foldl (fun acc zx ↦ (acc.1 * (1 + zx.1 + zx.2) + acc.2 * (1 + zx.2) * zx.1,
      acc.2 * (zx.2 * (1 + zx.1)))) (0, 1)).1 = shiftSum ζ r :=
  (shiftEq_of_charTwo ζ r).symm.trans (shiftEq_eq_shiftSum ζ r h)

/-- **`window_shift(eq_kernel(r_0), s)`**, entry `v` the kernel's entry `v + s` and zero past the
end, is `eq(r_0, v + s)` inside the window and zero past it. -/
theorem linkWindowShift_getD (r0 : List E) (s v : ℕ) (hv : v < 2 ^ r0.length) :
    ((List.range (Verifier.eqKernel r0).length).map
        fun v ↦ (Verifier.eqKernel r0).getD (v + s) 0).getD v 0 =
      if v + s < 2 ^ r0.length then eqAt r0 (v + s) else 0 := by
  simp [List.getD_eq_getElem?_getD, eqKernel_length, hv, ← eqKernel_getD]

/-- **A chunk read against `window_shift(eq_kernel(r_0), s)`** is `T_s` (`windowShift`). -/
theorem linkWindowShift_eq (r0 : List E) (e0 : ℕ → E) (s : ℕ) :
    ∑ v ∈ range (2 ^ r0.length), e0 v * ((List.range (Verifier.eqKernel r0).length).map
        fun v ↦ (Verifier.eqKernel r0).getD (v + s) 0).getD v 0 = windowShift r0 e0 s :=
  sum_congr rfl fun v hv ↦ by rw [linkWindowShift_getD r0 s v (mem_range.mp hv)]

end

end LeanVM.Protocol.Hotwire

/-! The bridges use Lean's three standard axioms at most. -/

/-- info: 'LeanVM.Protocol.Hotwire.eqEval_eq_eqPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.eqEval_eq_eqPt

/-- info: 'LeanVM.Protocol.Hotwire.eqEval_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.eqEval_eq_sum

/-- info: 'LeanVM.Protocol.Hotwire.eqKernel_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.eqKernel_getD

/-- info: 'LeanVM.Protocol.Hotwire.multilinearEval_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.multilinearEval_eq_mle

/-- info: 'LeanVM.Protocol.Hotwire.dot_eqKernel_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.dot_eqKernel_eq_mle

/-- info: 'LeanVM.Protocol.Hotwire.paddingWeight_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.paddingWeight_eq_mle

/-- info: 'LeanVM.Protocol.Hotwire.one_add_paddingWeight_eq_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.one_add_paddingWeight_eq_mle

/-- info: 'LeanVM.Protocol.Hotwire.eqEval_selectorPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.eqEval_selectorPoint

/-- info: 'LeanVM.Protocol.Hotwire.linkEqAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.linkEqAt_eq

/-- info: 'LeanVM.Protocol.Hotwire.linkShiftEq_eq_shiftSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.linkShiftEq_eq_shiftSum

/-- info: 'LeanVM.Protocol.Hotwire.linkWindowShift_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.linkWindowShift_getD

/-- info: 'LeanVM.Protocol.Hotwire.linkWindowShift_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.linkWindowShift_eq
