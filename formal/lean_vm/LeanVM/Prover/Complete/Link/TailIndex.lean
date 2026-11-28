/-
  LeanVM.Prover.Complete.Link.TailIndex

  The index side's tables at the index point are the verifier's closed forms, and the row weights
  at a table's row point are the extensions of the prover's.
-/

module

public import LeanVM.Prover.Complete.Link.TailFold
public import LeanVM.Prover.Complete.Link.State
import LeanVM.Parameters.Field
import LeanVM.ToMathlib.List

/-!
# The link's tail: the index tables and the row weights

After the index side's rounds at `r`, the verifier reads five of its thirteen tables in closed form
(`linkTail`, `tailRowSide`); each is the table's multilinear extension at `r`
(`at_foldl`):

* `indexAt_six`: `eq(ζ, ·)` at `r` is `eq_eval(ζ, r)` (`eqEval_eq_sum`);
* `indexAt_seven`: its shift by one is `shift_eq(ζ, r)` (`linkShiftEq_eq_shiftSum`);
* `indexAt_three`: the memory's address table `Y` is `γ_addr·index_mle(r) + γ_pres·below(κ) +
  γ_word·M_1`, from `indexMle_eq_mle`: `index_mle`'s product `Π (1 + r_k·(1 + g^(2^k)))` is the
  extension of `j ↦ g^j`;
* `indexAt_five`, `indexAt_twelve`: `X_ω` and `P_fp` are `η_bc·α_1·index_mle(r) + below(log_bc)·
  (η_bc·α_2 + X)` and `below(log_bc)·P`, `(X, P)` the program side of the split at `r`'s low
  coordinates (`programSide_splitAt`: both sums over the instructions; the `pc` weights vanish off
  `pc_slots`, `slotWeights_pc_zero`, decided; an honest instruction's slot `3` is `g^op`,
  `tailBcSlot_three`);
* `honestIndexAt`: the five, on the honest prefix, in `tailRowSide`'s exact forms.

At a table's row point (`Link/TailFold.lean`'s `rowSideOf`):

* `omegaAt_eq_mleA`: `omega_at(θ, τ_h, χ_h, n)` is the extension of `omegaTable θ τ h n`, from
  `prefixSum_eq`: `prefix_sum(low, high, n)` is `Σ_{g < n} Π_h e_h(g_h)`;
* `lessThan_eq_mleA`: `less_than(χ_h, n)` is the extension of the activity `[u < n]`;
* `eqEval_eq_mleA`: `eq_eval(τ_h, χ_h)` is the extension of `eq(τ_h, ·)`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Hotwire LeanVM.Protocol.Verifier.Defers Finset

/-! ## Equality weights -/

theorem tail_eqAt_zero_eq_prodE : ∀ l : List E, eqAt l 0 = prodE (l.map (1 + ·))
  | [] => rfl
  | z :: zs => by
    rw [eqAt_cons, show (0 : ℕ) / 2 = 0 from rfl, tail_eqAt_zero_eq_prodE zs]
    simp only [prodE, List.map_cons, List.foldl_cons, List.foldl_mul_eq_mul_prod, Nat.zero_mod,
      zero_ne_one, ↓reduceIte, CharTwo.sub_eq_add, one_mul]

/-- **A sum over the cube of a table zero from `2^κ` on**: the low `κ` coordinates' sum, times the
high coordinates' `eq(·, 0)`. -/
theorem tail_sum_eqAt_ite_lt (r : List E) {κ : ℕ} (hκ : κ ≤ r.length) (f : ℕ → E) :
    ∑ j ∈ range (2 ^ r.length), eqAt r j * (if j < 2 ^ κ then f j else 0) =
      (∑ j ∈ range (2 ^ κ), eqAt (r.take κ) j * f j) * prodE ((r.drop κ).map (1 + ·)) := by
  have hle : 2 ^ κ ≤ 2 ^ r.length := Nat.pow_le_pow_right (by norm_num) hκ
  rw [← Finset.sum_range_add_sum_Ico _ hle, Finset.sum_mul,
    Finset.sum_eq_zero (s := Ico _ _) (fun j hj ↦ by
      rw [ite_eq_right (by simp only [mem_Ico] at hj; omega), mul_zero]), add_zero]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' := mem_range.mp hj
  rw [ite_eq_left hj']
  conv_lhs => rw [← List.take_append_drop κ r]
  rw [eqAt_append, List.length_take, min_eq_left hκ, Nat.div_eq_of_lt hj', tail_eqAt_zero_eq_prodE]
  ring

/-! ## `index_mle` -/

theorem indexMleFrom_eq : ∀ (rs : List E) (k : ℕ) (acc : E),
    indexMleFrom (gen ^ 2 ^ k) rs acc =
      acc * ∑ j ∈ range (2 ^ rs.length), eqAt rs j * gen ^ (2 ^ k * j)
  | [], k, acc => by simp [indexMleFrom]
  | x :: xs, k, acc => by
    rw [indexMleFrom, show (gen ^ 2 ^ k) ^ 2 = gen ^ 2 ^ (k + 1) by rw [← pow_mul, pow_succ],
      indexMleFrom_eq xs (k + 1), List.length_cons, pow_succ 2 xs.length,
      mul_comm (2 ^ xs.length) 2, sum_range_two_mul, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [eqAt_cons_two_mul, eqAt_cons_two_mul_add_one, CharTwo.sub_eq_add,
      show 2 ^ k * (2 * j + 1) = 2 ^ (k + 1) * j + 2 ^ k by ring,
      show 2 ^ k * (2 * j) = 2 ^ (k + 1) * j by ring, pow_add]
    ring

/-- **`index_mle(r)` is the multilinear extension of `j ↦ g^j`.** -/
theorem indexMle_eq_mle (r : List E) : indexMle r = mle r gpow := by
  have h := indexMleFrom_eq r 0 1
  simp only [pow_zero, pow_one, one_mul] at h
  rw [indexMle, h]
  rfl

/-! ## The index tables at `r` -/

theorem indexArrays_six (W : Witness) (ch : LinkChallenges) :
    (indexArrays W ch).getD 6 #[] = eqTable ch.zeta := rfl

/-- **`eq(ζ, ·)` at `r`** is `eq_eval(ζ, r)`. -/
theorem indexAt_six (W : Witness) (ch : LinkChallenges) (r : List E)
    (hz : ch.zeta.length = r.length) :
    (r.foldl Prods.fold (indexProds W ch)).at 6 = eqEval ch.zeta r := by
  rw [at_foldl, show (indexProds W ch).tables.getD 6 #[] = eqTable ch.zeta from rfl,
    mleA_eq_sum _ _ (by rw [← Array.length_toList, Keccak.toList_eqTable, eqKernel_length, hz]), eqEval_eq_sum _ _ hz, hz]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [getD_eqTable_eqAt, ite_eq_left (by rw [hz]; exact mem_range.mp hj)]

/-- **`eq(ζ, · + 1)` at `r`** is `shift_eq(ζ, r)`. -/
theorem indexAt_seven (W : Witness) (ch : LinkChallenges) (r : List E)
    (hz : ch.zeta.length = r.length) (hr : r.length = W.chunks.width) :
    (r.foldl Prods.fold (indexProds W ch)).at 7 = linkShiftEq ch.zeta r := by
  rw [at_foldl, show (indexProds W ch).tables.getD 7 #[] =
      Array.ofFn (n := 2 ^ W.chunks.width) (fun j ↦ (eqTable ch.zeta).getD (j.val + 1) 0) from rfl,
    mleA_eq_sum _ _ (by rw [Array.size_ofFn, hr]), linkShiftEq, linkShiftEq_eq_shiftSum _ _ hz,
    shiftSum, hz]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' : j < 2 ^ W.chunks.width := hr ▸ mem_range.mp hj
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hj', Option.getD_some,
    getD_eqTable_eqAt, hz, mul_ite, mul_zero]

/-! ## The memory's address table -/

variable {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {W : Witness}

theorem tail_logMemory_le_width (hW : witness? prog input ex = some W) :
    W.layout.logMemory ≤ W.chunks.width := by
  obtain ⟨-, hch, -, -⟩ := linkSizes hW
  rw [Chunks.new_width hch]
  unfold pointerWidth
  omega

theorem tail_size_memory (hW : witness? prog input ex = some W) :
    (W.cols.getD memory0 #[]).size = 2 ^ W.layout.logMemory ∧
      (W.cols.getD memory1 #[]).size = 2 ^ W.layout.logMemory := by
  obtain ⟨h0, h1⟩ := cols_memory hW
  obtain ⟨-, steps, -, -, hl, -⟩ := witness?_spec hW
  rw [h0, h1, (buildLayout_spec hl).1]
  simp

theorem tail_getD_map_ofK (m : Array K) (j : ℕ) : (m.map ofK).getD j 0 = ofK (m.getD j 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases m[j]? <;> simp [show ofK 0 = 0 from map_zero (algebraMap K E)]

theorem tail_mleK_eq_sum (m : Array K) (pt : List E) (h : m.size = 2 ^ pt.length) :
    mleK m pt = ∑ j ∈ range (2 ^ pt.length), eqAt pt j * ofK (m.getD j 0) := by
  rw [mleK, mleA_eq_sum _ _ (by rw [Array.size_map, h])]
  simp only [tail_getD_map_ofK]

theorem tail_getD_powers_toArray (n j : ℕ) (hj : j < n) : (powers gen n).toArray.getD j 0 = gpow j := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  have key : ∀ (m b : ℕ) (acc : E), b < m → (powersFrom acc gen m).getD b 0 = acc * gen ^ b := by
    intro m
    induction m with
    | zero => intro b _ h; omega
    | succ m ih =>
      intro b acc h
      cases b with
      | zero => simp [powersFrom]
      | succ b =>
        rw [powersFrom, List.getD_cons_succ, ih b _ (by omega), pow_succ]
        ring
  rw [powers, key n j 1 hj, one_mul, gpow]

/-- **The memory's address table at `r`**: `γ_addr·index_mle(r) + γ_pres·below(κ) + γ_word·M_1`,
`M_1` the honest one. -/
theorem indexAt_three (hW : witness? prog input ex = some W) (ch : LinkChallenges) (r : List E)
    (hr : r.length = W.chunks.width) (hg : ch.gammaMem.getD 2 0 = ch.gammaMem.getD 1 0 * eY) :
    (r.foldl Prods.fold (indexProds W ch)).at 3 =
      ch.gammaMem.getD 0 0 * indexMle r +
        ch.gammaMem.getD 3 0 * prodE ((r.drop (min W.layout.logMemory W.chunks.width)).map (1 + ·)) +
        ch.gammaMem.getD 1 0 * honestM1 W r := by
  have hκ := tail_logMemory_le_width hW
  obtain ⟨hs0, hs1⟩ := tail_size_memory hW
  have hκr : W.layout.logMemory ≤ r.length := hr ▸ hκ
  have hlt : (r.take W.layout.logMemory).length = W.layout.logMemory := by
    rw [List.length_take, min_eq_left hκr]
  rw [at_foldl, show (indexProds W ch).tables.getD 3 #[] = Array.ofFn (n := 2 ^ W.chunks.width)
      (fun j ↦ if j.val < 2 ^ W.layout.logMemory then
        ch.gammaMem.getD 0 0 * (powers gen (2 ^ W.chunks.width)).toArray.getD j 0 +
          ch.gammaMem.getD 1 0 * ofK ((W.cols.getD memory0 #[]).getD j 0) +
          ch.gammaMem.getD 2 0 * ofK ((W.cols.getD memory1 #[]).getD j 0) + ch.gammaMem.getD 3 0
      else ch.gammaMem.getD 0 0 * (powers gen (2 ^ W.chunks.width)).toArray.getD j 0) from rfl,
    mleA_eq_sum _ _ (by rw [Array.size_ofFn, hr])]
  have hsplit : ∀ j ∈ range (2 ^ r.length), eqAt r j * (Array.ofFn (n := 2 ^ W.chunks.width)
      (fun j ↦ if j.val < 2 ^ W.layout.logMemory then
        ch.gammaMem.getD 0 0 * (powers gen (2 ^ W.chunks.width)).toArray.getD j 0 +
          ch.gammaMem.getD 1 0 * ofK ((W.cols.getD memory0 #[]).getD j 0) +
          ch.gammaMem.getD 2 0 * ofK ((W.cols.getD memory1 #[]).getD j 0) + ch.gammaMem.getD 3 0
      else ch.gammaMem.getD 0 0 * (powers gen (2 ^ W.chunks.width)).toArray.getD j 0)).getD j 0 =
      ch.gammaMem.getD 0 0 * (eqAt r j * gpow j) + eqAt r j * (if j < 2 ^ W.layout.logMemory then
        ch.gammaMem.getD 3 0 + ch.gammaMem.getD 1 0 * (ofK ((W.cols.getD memory0 #[]).getD j 0) +
          eY * ofK ((W.cols.getD memory1 #[]).getD j 0)) else 0) := by
    intro j hj
    have hj' : j < 2 ^ W.chunks.width := hr ▸ mem_range.mp hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hj', Option.getD_some]
    dsimp only
    rw [tail_getD_powers_toArray _ _ hj', hg]
    split_ifs <;> ring
  have hsum : ∑ j ∈ range (2 ^ W.layout.logMemory), eqAt (r.take W.layout.logMemory) j *
      (ch.gammaMem.getD 3 0 + ch.gammaMem.getD 1 0 * (ofK ((W.cols.getD memory0 #[]).getD j 0) +
        eY * ofK ((W.cols.getD memory1 #[]).getD j 0))) =
      ch.gammaMem.getD 3 0 + ch.gammaMem.getD 1 0 *
        (mleK (W.cols.getD memory0 #[]) (r.take W.layout.logMemory) +
          eY * mleK (W.cols.getD memory1 #[]) (r.take W.layout.logMemory)) := by
    rw [tail_mleK_eq_sum _ _ (by rw [hlt, hs0]), tail_mleK_eq_sum _ _ (by rw [hlt, hs1]), hlt]
    have h1 := sum_eqAt (r.take W.layout.logMemory)
    rw [hlt] at h1
    conv_rhs => rw [← mul_one (ch.gammaMem.getD 3 0), ← h1]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  rw [sum_congr rfl hsplit, sum_add_distrib, ← Finset.mul_sum, tail_sum_eqAt_ite_lt r hκr, hsum,
    show ∑ j ∈ range (2 ^ r.length), eqAt r j * gpow j = mle r gpow from rfl, ← indexMle_eq_mle,
    honestM1, min_eq_left hκ]
  ring

/-! ## `prefix_sum` -/

/-- `Π_{h < L} e_h(g_h)`, `e_h(0) = low[h]` and `e_h(1) = high[h]`. -/
def bitProd (low high : List E) (L g : ℕ) : E :=
  ∏ h ∈ range L, if g.testBit h then high.getD h 0 else low.getD h 0

theorem bitProd_succ_low (low high : List E) {L g : ℕ} (hg : g < 2 ^ L) :
    bitProd low high (L + 1) g = bitProd low high L g * low.getD L 0 := by
  rw [bitProd, prod_range_succ, Nat.testBit_lt_two_pow hg]
  rfl

theorem bitProd_succ_high (low high : List E) {L g : ℕ} (hg : g < 2 ^ L) :
    bitProd low high (L + 1) (2 ^ L + g) = bitProd low high L g * high.getD L 0 := by
  rw [bitProd, prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hg]
  simp only [Bool.not_false, ↓reduceIte, bitProd]
  congr 1
  refine prod_congr rfl fun h hh ↦ ?_
  rw [Nat.testBit_two_pow_add_gt (mem_range.mp hh)]

theorem sum_bitProd_low (low high : List E) {L m : ℕ} (hm : m ≤ 2 ^ L) :
    ∑ g ∈ range m, bitProd low high (L + 1) g = low.getD L 0 * ∑ g ∈ range m, bitProd low high L g := by
  rw [mul_sum]
  refine sum_congr rfl fun g hg ↦ ?_
  rw [bitProd_succ_low _ _ (by have := mem_range.mp hg; omega), mul_comm]

theorem sum_bitProd_high (low high : List E) {L m : ℕ} (hm : m ≤ 2 ^ L) :
    ∑ g ∈ range (2 ^ L + m), bitProd low high (L + 1) g =
      low.getD L 0 * ∑ g ∈ range (2 ^ L), bitProd low high L g +
        high.getD L 0 * ∑ g ∈ range m, bitProd low high L g := by
  rw [sum_range_add, sum_bitProd_low _ _ le_rfl, mul_sum (s := range m)]
  congr 1
  refine sum_congr rfl fun g hg ↦ ?_
  rw [bitProd_succ_high _ _ (by have := mem_range.mp hg; omega), mul_comm]

theorem sum_bitProd_full (low high : List E) : ∀ L,
    ∑ g ∈ range (2 ^ L), bitProd low high L g = ∏ h ∈ range L, (low.getD h 0 + high.getD h 0)
  | 0 => by simp [bitProd]
  | L + 1 => by
    rw [pow_succ, mul_two, sum_bitProd_high _ _ le_rfl, sum_bitProd_full low high L, prod_range_succ]
    ring

/-- The prefix products `prefix_sum` builds: entry `h` is `Π_{i < h} (low_i + high_i)`. -/
theorem getD_prefixFull (low high : List E) : ∀ L, ∀ h ≤ L,
    ((List.range L).foldl (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)])
        [(1 : E)]).getD h 0 = ∏ i ∈ range h, (low.getD i 0 + high.getD i 0) ∧
      ((List.range L).foldl (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)])
        [(1 : E)]).length = L + 1
  | 0, h, hh => by
    obtain rfl : h = 0 := by omega
    simp
  | L + 1, h, hh => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := getD_prefixFull low high L
    obtain ⟨-, hlen⟩ := ih 0 (by omega)
    generalize (List.range L).foldl (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)])
      [(1 : E)] = full at ih hlen
    refine ⟨?_, by rw [List.length_append, hlen, List.length_singleton]⟩
    rcases Nat.lt_or_ge h (L + 1) with hlt | hge
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact (ih h (by omega)).1
    · obtain rfl : h = L + 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero,
        (ih L le_rfl).1, prod_range_succ]

/-- The walk over `n`'s bits from `L - 1` down: from `(s, p)`, `s + p·Σ_{g < n mod 2^L}`. -/
theorem prefixWalk (low high full : List E) (L₀ : ℕ)
    (hfull : ∀ h < L₀, full.getD h 0 = ∏ i ∈ range h, (low.getD i 0 + high.getD i 0)) (n : ℕ) :
    ∀ L ≤ L₀, ∀ s p : E, ((List.range L).reverse.foldl (fun (acc : E × E) h ↦
        if n >>> h % 2 = 1 then (acc.1 + acc.2 * low.getD h 0 * full.getD h 0, acc.2 * high.getD h 0)
        else (acc.1, acc.2 * low.getD h 0)) (s, p)).1 =
      s + p * ∑ g ∈ range (n % 2 ^ L), bitProd low high L g
  | 0, _, s, p => by simp [Nat.mod_one]
  | L + 1, hL, s, p => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    have hmod : n % 2 ^ (L + 1) = n % 2 ^ L + 2 ^ L * (n >>> L % 2) := by
      rw [Nat.shiftRight_eq_div_pow, pow_succ, Nat.mod_mul, add_comm]
    have hlt : n % 2 ^ L < 2 ^ L := Nat.mod_lt _ (Nat.two_pow_pos L)
    rcases Nat.mod_two_eq_zero_or_one (n >>> L) with hb | hb
    · rw [ite_eq_right (by omega), prefixWalk low high full L₀ hfull n L (by omega), hmod, hb,
        mul_zero, add_zero, sum_bitProd_low _ _ hlt.le]
      ring
    · rw [ite_eq_left hb, prefixWalk low high full L₀ hfull n L (by omega), hmod, hb, mul_one,
        add_comm (n % 2 ^ L), sum_bitProd_high _ _ hlt.le, hfull L (by omega),
        ← sum_bitProd_full low high L]
      ring

/-- **`prefix_sum(low, high, n) = Σ_{g < n} Π_h e_h(g_h)`**, for `n ≤ 2^|low|`. -/
theorem prefixSum_eq (low high : List E) (n : ℕ) (hn : n ≤ 2 ^ low.length) :
    prefixSum low high n = ∑ g ∈ range n, bitProd low high low.length g := by
  have hfull := getD_prefixFull low high low.length
  unfold prefixSum
  dsimp only
  split_ifs with h
  · rw [(hfull low.length le_rfl).1, ← sum_bitProd_full, show n = 2 ^ low.length by omega]
  · rw [prefixWalk low high _ low.length (fun k hk ↦ (hfull k hk.le).1) n low.length le_rfl,
      Nat.mod_eq_of_lt (by omega), zero_add, one_mul]

/-! ## The row weights at a table's row point -/

/-- `omega_at`'s factors are the two points' equality weights. -/
theorem bitProd_zipWith : ∀ (τ x : List E), τ.length = x.length → ∀ g,
    bitProd (List.zipWith (fun t x ↦ (1 + t) * (1 + x)) τ x) (List.zipWith (fun t x ↦ t * x) τ x)
      τ.length g = eqAt τ g * eqAt x g
  | [], [], _, g => by simp [bitProd]
  | t :: τ, y :: x, h, g => by
    have h' : τ.length = x.length := by simpa using h
    rw [bitProd, List.length_cons, prod_range_succ', eqAt_cons_of_charTwo, eqAt_cons_of_charTwo]
    have ih := bitProd_zipWith τ x h' (g / 2)
    rw [bitProd] at ih
    simp only [List.zipWith_cons_cons, List.getD_cons_succ, List.getD_cons_zero, Nat.testBit_succ,
      Nat.testBit_zero, ih]
    rcases Nat.mod_two_eq_zero_or_one g with hg | hg <;> simp [hg] <;> ring
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

theorem tail_sum_range_eq_ite (N n : ℕ) (hn : n ≤ N) (f : ℕ → E) :
    ∑ u ∈ range N, (if u < n then f u else 0) = ∑ u ∈ range n, f u := by
  rw [← Finset.sum_range_add_sum_Ico _ hn,
    Finset.sum_eq_zero (s := Ico _ _) (fun u hu ↦ by
      rw [ite_eq_right (by simp only [mem_Ico] at hu; omega)]), add_zero]
  exact sum_congr rfl fun u hu ↦ ite_eq_left (mem_range.mp hu)

/-- **`omega_at(θ, τ_h, χ_h, n)` is the extension of `ω_F`** at a table's row point. -/
theorem omegaAt_eq_mleA (θ : E) (τ pt : List E) {h n : ℕ} (hτ : h ≤ τ.length)
    (hpt : pt.length = h) (hn : n ≤ 2 ^ h) :
    omegaAt θ (τ.take h) pt n = mleA (omegaTable θ τ h n) pt := by
  have hth : (τ.take h).length = h := by rw [List.length_take, min_eq_left hτ]
  have hlow : (List.zipWith (fun t x ↦ (1 + t) * (1 + x)) (τ.take h) pt).length = h := by
    rw [List.length_zipWith, hth, hpt, min_self]
  rw [omegaAt, prefixSum_eq _ _ _ (by rw [hlow]; exact hn), hlow,
    mleA_eq_sum _ _ (by rw [omegaTable, Array.size_ofFn, hpt]), hpt, mul_sum]
  rw [← tail_sum_range_eq_ite (2 ^ h) n hn]
  refine sum_congr rfl fun u hu ↦ ?_
  have hu' := mem_range.mp hu
  rw [omegaTable, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hu',
    Option.getD_some]
  dsimp only
  have hb := bitProd_zipWith (τ.take h) pt (by rw [hth, hpt]) u
  rw [hth] at hb
  rw [hb]
  split_ifs
  · rw [getD_eqTable_eqAt, ite_eq_left (by rw [hth]; exact hu')]
    ring
  · simp

/-- **`less_than(χ_h, n)` is the extension of the activity `[u < n]`.** -/
theorem lessThan_eq_mleA (pt : List E) {h n : ℕ} (hpt : pt.length = h) (hn : n ≤ 2 ^ h) :
    lessThan pt n = mleA (Array.ofFn (n := 2 ^ h) fun u ↦ if u.val < n then (1 : E) else 0) pt := by
  rw [lessThan, one_add_paddingWeight_eq_mle _ _ (by rw [hpt]; exact hn),
    mleA_eq_sum _ _ (by rw [Array.size_ofFn, hpt]), mle, hpt]
  refine sum_congr rfl fun u hu ↦ ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left (mem_range.mp hu),
    Option.getD_some]

/-- **`eq_eval(τ_h, χ_h)` is the extension of `eq(τ_h, ·)`.** -/
theorem eqEval_eq_mleA (τ pt : List E) (h : τ.length = pt.length) :
    eqEval τ pt = mleA (eqTable τ) pt := by
  rw [eqEval_eq_sum _ _ h, mleA_eq_sum _ _ (by
    rw [← Array.length_toList, Keccak.toList_eqTable, eqKernel_length, h]), h]
  refine sum_congr rfl fun u hu ↦ ?_
  rw [getD_eqTable_eqAt, ite_eq_left (by rw [h]; exact mem_range.mp hu)]

/-! ## The program side's weights -/

/-- Whether a read is `Read::Pc` at slot `s`. -/
def readsPcAt (s : ℕ) : Read → Bool
  | .pc s' _ => s' == s
  | _ => false

theorem tail_getD_addAtSlot_ne (w : List E) {s s' : ℕ} (h : s' ≠ s) (v : E) :
    (addAtSlot w s' v).getD s 0 = w.getD s 0 := by
  simp only [addAtSlot, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- **A table's `pc` weight is zero at a slot it never reads times `pc`.** -/
theorem tableSlotWeights_pc_zero (table : Table) (slot : List E) (gamma : E × E) (mu : List E)
    (etaMem etaBc : E) {s : ℕ}
    (h : (table.links.memory.all fun a ↦ a.reads.all fun rd ↦ !readsPcAt s rd) = true) :
    (tableSlotWeights table slot gamma mu etaMem etaBc).2.1.getD s 0 = 0 := by
  unfold tableSlotWeights
  dsimp only
  have inner : ∀ (reads : List Read), (reads.all fun rd ↦ !readsPcAt s rd) = true →
      ∀ (m : E) (acc : List E × List E × List E), acc.2.1.getD s 0 = 0 →
      (reads.foldl (fun (acc : List E × List E × List E) read ↦
        match read with
        | .word _ _ => acc
        | .slot s scale => (addAtSlot acc.1 s (m * gamma.2 * scale), acc.2.1, acc.2.2)
        | .frame s scale => (acc.1, acc.2.1, addAtSlot acc.2.2 s (m * gamma.2 * scale))
        | .pc s scale => (acc.1, addAtSlot acc.2.1 s (m * gamma.2 * scale), acc.2.2))
        acc).2.1.getD s 0 = 0 := by
    intro reads
    induction reads with
    | nil => intro _ _ _ h0; exact h0
    | cons rd reads ih =>
      intro hall m acc h0
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rw [List.foldl_cons]
      refine ih hall.2 m _ ?_
      cases rd with
      | word => exact h0
      | slot => exact h0
      | frame => exact h0
      | pc s' scale =>
        have hne : s' ≠ s := by simpa [readsPcAt] using hall.1
        exact (tail_getD_addAtSlot_ne _ hne _).trans h0
  have outer : ∀ (L : List (Access × E)), (∀ p ∈ L, (p.1.reads.all fun rd ↦ !readsPcAt s rd) = true) →
      ∀ (acc : List E × List E × List E), acc.2.1.getD s 0 = 0 →
      (L.foldl (fun (acc : List E × List E × List E) (am : Access × E) ↦
        let m := etaMem * am.2
        let frame := match am.1.frame with
          | some (s, e) => addAtSlot acc.2.2 s (m * gamma.1 * gpow e)
          | none => acc.2.2
        am.1.reads.foldl (fun (acc : List E × List E × List E) read ↦
          match read with
          | .word _ _ => acc
          | .slot s scale => (addAtSlot acc.1 s (m * gamma.2 * scale), acc.2.1, acc.2.2)
          | .frame s scale => (acc.1, acc.2.1, addAtSlot acc.2.2 s (m * gamma.2 * scale))
          | .pc s scale => (acc.1, addAtSlot acc.2.1 s (m * gamma.2 * scale), acc.2.2))
          (acc.1, acc.2.1, frame)) acc).2.1.getD s 0 = 0 := by
    intro L
    induction L with
    | nil => intro _ _ h0; exact h0
    | cons am L ih =>
      intro hall acc h0
      rw [List.foldl_cons]
      exact ih (fun p hp ↦ hall p (List.mem_cons_of_mem _ hp)) _
        (inner _ (hall am List.mem_cons_self) _ _ h0)
  refine outer _ (fun p hp ↦ ?_) _ (by simp [List.getD_eq_getElem?_getD])
  have hm := (List.of_mem_zip hp).1
  simp only [List.all_eq_true] at h
  simpa only [List.all_eq_true] using h p.1 hm

/-- Every slot a table reads times `pc` is an operand slot `pc_slots` lists. -/
theorem pcSlots_cover : ∀ t < nTables, ∀ s < 2 ^ bytecodeSlotBits,
    ¬(4 ≤ s ∧ (pcSlots tables).contains (t, s) = true) →
      ((tables.getD t default).links.memory.all fun a ↦ a.reads.all fun rd ↦ !readsPcAt s rd) =
        true := by
  decide +kernel

theorem getD_slotWeights_pc (slot : List E) (gamma : E × E) (mu : List (List E)) (etaMem etaBc : E)
    {t : ℕ} (ht : t < nTables) :
    (slotWeights tables slot gamma mu etaMem etaBc).pc.getD t [] =
      (tableSlotWeights (tables.getD t default) slot gamma (mu.getD t []) etaMem etaBc).2.1 := by
  have hl : tables.length = nTables := by decide +kernel
  have ht' : t < tables.length := hl ▸ ht
  simp [slotWeights, List.getD_eq_getElem?_getD, ht']

/-- **The `pc` weights vanish off `pc_slots`.** -/
theorem slotWeights_pc_zero (slot : List E) (gamma : E × E) (mu : List (List E)) (etaMem etaBc : E)
    {t s : ℕ} (ht : t < nTables) (hs : s < 2 ^ bytecodeSlotBits)
    (h : ¬(4 ≤ s ∧ (pcSlots tables).contains (t, s) = true)) :
    ((slotWeights tables slot gamma mu etaMem etaBc).pc.getD t []).getD s 0 = 0 := by
  rw [getD_slotWeights_pc _ _ _ _ _ ht]
  exact tableSlotWeights_pc_zero _ _ _ _ _ _ (pcSlots_cover t ht s hs h)

/-! ## The program's split, as sums over the instructions -/

theorem tail_sum_map_zipIdx {α : Type} (F : α × ℕ → E) (d : α) :
    ∀ (l : List α) (n : ℕ), ((l.zipIdx n).map F).sum = ∑ v ∈ range l.length, F (l.getD v d, n + v)
  | [], _ => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, tail_sum_map_zipIdx F d l (n + 1),
      List.length_cons, sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun v _ ↦ ?_
    rw [show n + 1 + v = n + (v + 1) by omega]

theorem tail_getD_zip_pair : ∀ (a b : List E) (v : ℕ), v < a.length → v < b.length →
    (a.zip b).getD v (0, 0) = (a.getD v 0, b.getD v 0)
  | [], _, _, h, _ => by simp at h
  | _, [], _, _, h => by simp at h
  | x :: a, y :: b, 0, _, _ => rfl
  | x :: a, y :: b, v + 1, ha, hb => by
    simp only [List.zip_cons_cons, List.getD_cons_succ]
    exact tail_getD_zip_pair a b v (by simpa using ha) (by simpa using hb)

theorem tail_length_powersFrom (base : E) : ∀ (n : ℕ) (acc : E), (powersFrom acc base n).length = n
  | 0, _ => rfl
  | n + 1, acc => by rw [powersFrom, List.length_cons, tail_length_powersFrom base n]

theorem tail_getD_powers (n j : ℕ) (hj : j < n) : (powers gen n).getD j 0 = gpow j := by
  rw [← tail_getD_powers_toArray n j hj, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

/-- Slot `s` of instruction `k` of a program's words (`Bytecode::split`'s `slot`). -/
def tailBcSlot (bc : List K) (s k : ℕ) : K := bc.getD (s * (bc.length >>> bytecodeSlotBits) + k) 0

/-- `Bytecode::split`'s rows, summed: a sum over the instructions with `eq(point, k)` and `g^k`. -/
theorem sum_splitRows (pt : List E) (F : (E × E) × ℕ → E) :
    ((((eqKernel pt).zip (powers gen (2 ^ pt.length))).zipIdx).map F).sum =
      ∑ k ∈ range (2 ^ pt.length), F ((eqAt pt k, gpow k), k) := by
  have hk := eqKernel_length pt
  have hp : (powers gen (2 ^ pt.length)).length = 2 ^ pt.length := tail_length_powersFrom _ _ _
  rw [tail_sum_map_zipIdx F ((0 : E), (0 : E)), List.length_zip, hk, hp, min_self]
  refine sum_congr rfl fun k hk' ↦ ?_
  have hk'' := mem_range.mp hk'
  rw [tail_getD_zip_pair _ _ _ (by rw [hk]; exact hk'') (by rw [hp]; exact hk''), eqKernel_getD,
    ite_eq_left hk'', tail_getD_powers _ _ hk'', zero_add]

/-- **The split's entries** for an opcode `t`: its weight, an operand slot's sum and its `pc`
sum, each a sum over the instructions. -/
theorem splitAt_entries (bc : List K) (pt : List E) (pc : List (ℕ × ℕ)) {t : ℕ} (ht : t < nTables) :
    (splitAt bc pt pc).count.getD t 0 = ∑ k ∈ range (2 ^ pt.length),
        (if opcodeOf (tailBcSlot bc 3 k) = t then eqAt pt k else 0) ∧
      ∀ s, 4 ≤ s → s < 2 ^ bytecodeSlotBits →
        ((splitAt bc pt pc).slots.getD t []).getD s 0 = ∑ k ∈ range (2 ^ pt.length),
          (if opcodeOf (tailBcSlot bc 3 k) = t then eqAt pt k * ofK (tailBcSlot bc s k) else 0) ∧
        ((splitAt bc pt pc).pc.getD t []).getD s 0 = if pc.contains (t, s) = true then
          ∑ k ∈ range (2 ^ pt.length),
            (if opcodeOf (tailBcSlot bc 3 k) = t then eqAt pt k * (gpow k * ofK (tailBcSlot bc s k)) else 0)
          else 0 := by
  have ht' : t < opKeccak + 1 := ht
  refine ⟨?_, fun s hs4 hs ↦ ⟨?_, ?_⟩⟩
  · simp only [splitAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht',
      Option.map_some, Option.getD_some, sumE_eq_sum, sum_splitRows, tailBcSlot]
  · simp only [splitAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht',
      List.getElem?_range hs, Option.map_some, Option.getD_some, sumE_eq_sum, sum_splitRows, tailBcSlot]
    rw [ite_eq_left hs4]
  · simp only [splitAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht',
      List.getElem?_range hs, Option.map_some, Option.getD_some, sumE_eq_sum, sum_splitRows, tailBcSlot]
    by_cases hc : pc.contains (t, s) = true
    · rw [ite_eq_left ⟨hs4, hc⟩, ite_eq_left hc]
    · rw [ite_eq_right (fun h ↦ hc h.2), ite_eq_right hc]

theorem tail_foldl_add_pair {α : Type} (F : E × E → α → E × E) (f g : α → E)
    (hF : ∀ acc x, F acc x = (acc.1 + f x, acc.2 + g x)) :
    ∀ (L : List α) (a b : E), L.foldl F (a, b) = (a + (L.map f).sum, b + (L.map g).sum)
  | [], a, b => by simp
  | x :: L, a, b => by
    rw [List.foldl_cons, hF, tail_foldl_add_pair F f g hF L]
    simp only [List.map_cons, List.sum_cons, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

/-- **The program side as sums** over the tables and their operand slots. -/
theorem programSide_eq_sum (w : SlotWeights) (sp : Split) :
    programSide w sp =
      (∑ t ∈ range nTables, ((w.omega.getD t []).getD 3 0 * gpow t * sp.count.getD t 0 +
          ∑ i ∈ range (2 ^ bytecodeSlotBits - 4),
            ((w.omega.getD t []).getD (i + 4) 0 * (sp.slots.getD t []).getD (i + 4) 0 +
              (w.pc.getD t []).getD (i + 4) 0 * (sp.pc.getD t []).getD (i + 4) 0)),
        ∑ t ∈ range nTables, ∑ i ∈ range (2 ^ bytecodeSlotBits - 4),
          (w.frame.getD t []).getD (i + 4) 0 * (sp.slots.getD t []).getD (i + 4) 0) := by
  unfold programSide
  rw [tail_foldl_add_pair _ (fun t ↦ (w.omega.getD t []).getD 3 0 * gpow t * sp.count.getD t 0 +
      ∑ i ∈ range (2 ^ bytecodeSlotBits - 4),
        ((w.omega.getD t []).getD (i + 4) 0 * (sp.slots.getD t []).getD (i + 4) 0 +
          (w.pc.getD t []).getD (i + 4) 0 * (sp.pc.getD t []).getD (i + 4) 0))
    (fun t ↦ ∑ i ∈ range (2 ^ bytecodeSlotBits - 4),
      (w.frame.getD t []).getD (i + 4) 0 * (sp.slots.getD t []).getD (i + 4) 0)
    (fun acc t ↦ ?_), sum_map_range, sum_map_range, zero_add, zero_add]
  dsimp only
  rw [tail_foldl_add_pair _ (fun s ↦ (w.omega.getD t []).getD s 0 * (sp.slots.getD t []).getD s 0 +
      (w.pc.getD t []).getD s 0 * (sp.pc.getD t []).getD s 0)
    (fun s ↦ (w.frame.getD t []).getD s 0 * (sp.slots.getD t []).getD s 0) (fun _ _ ↦ rfl),
    List.map_map, List.map_map, sum_map_range, sum_map_range]
  simp only [Function.comp_def, Prod.mk.injEq]
  exact ⟨by ring, trivial⟩

/-- What the program side weighs instruction `k` by, on `ω` (`X_ω`'s operand part). -/
def progX (bc : List K) (w : SlotWeights) (k : ℕ) : E :=
  let op := opcodeOf (tailBcSlot bc 3 k)
  (w.omega.getD op []).getD 3 0 * gpow op + ∑ i ∈ range (2 ^ bytecodeSlotBits - 4),
    ((w.omega.getD op []).getD (i + 4) 0 * ofK (tailBcSlot bc (i + 4) k) +
      (w.pc.getD op []).getD (i + 4) 0 * (gpow k * ofK (tailBcSlot bc (i + 4) k)))

/-- What the program side weighs instruction `k` by, on `ω·fp` (`P_fp`). -/
def progF (bc : List K) (w : SlotWeights) (k : ℕ) : E :=
  let op := opcodeOf (tailBcSlot bc 3 k)
  ∑ i ∈ range (2 ^ bytecodeSlotBits - 4), (w.frame.getD op []).getD (i + 4) 0 * ofK (tailBcSlot bc (i + 4) k)

/-- **The program side of the split** is the instructions' weights under `eq(point, k)`, for a
program whose opcodes are tables'. -/
theorem programSide_splitAt (bc : List K) (pt : List E) (slot : List E) (gamma : E × E)
    (mu : List (List E)) (etaMem etaBc : E)
    (hop : ∀ k < 2 ^ pt.length, opcodeOf (tailBcSlot bc 3 k) < nTables) :
    programSide (slotWeights tables slot gamma mu etaMem etaBc) (splitAt bc pt (pcSlots tables)) =
      (∑ k ∈ range (2 ^ pt.length), eqAt pt k * progX bc (slotWeights tables slot gamma mu etaMem etaBc) k,
        ∑ k ∈ range (2 ^ pt.length), eqAt pt k * progF bc (slotWeights tables slot gamma mu etaMem etaBc) k) := by
  set w := slotWeights tables slot gamma mu etaMem etaBc with hw
  rw [programSide_eq_sum]
  -- Each table's part, a sum over its instructions.
  have hX : ∀ t ∈ range nTables, (w.omega.getD t []).getD 3 0 * gpow t *
        (splitAt bc pt (pcSlots tables)).count.getD t 0 +
      ∑ i ∈ range (2 ^ bytecodeSlotBits - 4),
        ((w.omega.getD t []).getD (i + 4) 0 * ((splitAt bc pt (pcSlots tables)).slots.getD t []).getD (i + 4) 0 +
          (w.pc.getD t []).getD (i + 4) 0 * ((splitAt bc pt (pcSlots tables)).pc.getD t []).getD (i + 4) 0) =
      ∑ k ∈ range (2 ^ pt.length), if opcodeOf (tailBcSlot bc 3 k) = t then eqAt pt k *
        ((w.omega.getD t []).getD 3 0 * gpow t + ∑ i ∈ range (2 ^ bytecodeSlotBits - 4),
          ((w.omega.getD t []).getD (i + 4) 0 * ofK (tailBcSlot bc (i + 4) k) +
            (w.pc.getD t []).getD (i + 4) 0 * (gpow k * ofK (tailBcSlot bc (i + 4) k)))) else 0 := by
    intro t ht
    have ht' := mem_range.mp ht
    obtain ⟨hc, hrest⟩ := splitAt_entries bc pt (pcSlots tables) ht'
    have hi : ∀ i ∈ range (2 ^ bytecodeSlotBits - 4),
        (w.omega.getD t []).getD (i + 4) 0 * ((splitAt bc pt (pcSlots tables)).slots.getD t []).getD (i + 4) 0 +
          (w.pc.getD t []).getD (i + 4) 0 * ((splitAt bc pt (pcSlots tables)).pc.getD t []).getD (i + 4) 0 =
        ∑ k ∈ range (2 ^ pt.length), if opcodeOf (tailBcSlot bc 3 k) = t then eqAt pt k *
          ((w.omega.getD t []).getD (i + 4) 0 * ofK (tailBcSlot bc (i + 4) k) +
            (w.pc.getD t []).getD (i + 4) 0 * (gpow k * ofK (tailBcSlot bc (i + 4) k))) else 0 := by
      intro i hi
      have hi' := mem_range.mp hi
      have hs : i + 4 < 2 ^ bytecodeSlotBits := by
        have : (2 : ℕ) ^ bytecodeSlotBits = 16 := rfl
        omega
      obtain ⟨hsl, hpc⟩ := hrest (i + 4) (by omega) hs
      rw [hsl, hpc]
      by_cases hcon : (pcSlots tables).contains (t, i + 4) = true
      · rw [ite_eq_left hcon, Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun k _ ↦ ?_
        split_ifs <;> ring
      · rw [ite_eq_right hcon, slotWeights_pc_zero _ _ _ _ _ ht' hs (fun h ↦ hcon h.2), mul_zero,
          add_zero, Finset.mul_sum]
        refine sum_congr rfl fun k _ ↦ ?_
        split_ifs <;> ring
    rw [sum_congr rfl hi, Finset.sum_comm, hc, Finset.mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    by_cases h : opcodeOf (tailBcSlot bc 3 k) = t
    · simp only [ite_eq_left h]
      rw [mul_add, Finset.mul_sum]
      ring
    · simp only [ite_eq_right h]
      simp
  have hF : ∀ t ∈ range nTables, ∑ i ∈ range (2 ^ bytecodeSlotBits - 4),
        (w.frame.getD t []).getD (i + 4) 0 * ((splitAt bc pt (pcSlots tables)).slots.getD t []).getD (i + 4) 0 =
      ∑ k ∈ range (2 ^ pt.length), if opcodeOf (tailBcSlot bc 3 k) = t then eqAt pt k *
        ∑ i ∈ range (2 ^ bytecodeSlotBits - 4), (w.frame.getD t []).getD (i + 4) 0 * ofK (tailBcSlot bc (i + 4) k)
        else 0 := by
    intro t ht
    obtain ⟨-, hrest⟩ := splitAt_entries bc pt (pcSlots tables) (mem_range.mp ht)
    rw [sum_congr rfl fun i hi ↦ by
      rw [(hrest (i + 4) (by omega) (by
        have := mem_range.mp hi
        have : (2 : ℕ) ^ bytecodeSlotBits = 16 := rfl
        omega)).1, Finset.mul_sum], Finset.sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    by_cases h : opcodeOf (tailBcSlot bc 3 k) = t
    · simp only [ite_eq_left h]
      rw [Finset.mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      ring
    · simp only [ite_eq_right h]
      simp
  rw [sum_congr rfl hX, sum_congr rfl hF, Finset.sum_comm, Finset.sum_comm (s := range nTables)]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> refine sum_congr rfl fun k hk ↦ ?_ <;>
    rw [Finset.sum_ite_eq, ite_eq_left (mem_range.mpr (hop k (mem_range.mp hk)))] <;> rfl

/-! ## The program's opcodes on the honest witness -/

theorem tail_instructionSlots_three (ins : LeanIsaInstruction) :
    (LeanVM.Arithmetization.instructionSlots ins)[3] = ins.opcode.code := by
  cases ins <;> rfl

theorem tail_ofK_code (op : Opcode) : ofK op.code = gpow (LeanVM.Protocol.Relation.opIndex op) := by
  rw [LeanVM.Protocol.Relation.gpow_eq_ofK]
  cases op <;> rfl

/-- **An instruction's slot `3` is `g^op`**, `op` a table's. -/
theorem tailBcSlot_three (hW : witness? prog input ex = some W) {k : ℕ}
    (hk : k < 2 ^ W.layout.logBytecode) :
    opcodeOf (tailBcSlot W.layout.bytecode 3 k) < nTables ∧
      ofK (tailBcSlot W.layout.bytecode 3 k) = gpow (opcodeOf (tailBcSlot W.layout.bytecode 3 k)) := by
  obtain ⟨-, steps, -, -, hl, -⟩ := witness?_spec hW
  obtain ⟨hbc, -, hshift, -⟩ := buildLayout_facts hl
  have hlog : W.layout.logBytecode = prog.logSize := by
    rw [LeanVM.Protocol.Relation.length_bytecodeWords, Nat.shiftRight_eq_div_pow,
      show bytecodeSlotBits = 4 from rfl, show (2 : ℕ) ^ 4 = 16 from rfl,
      Nat.mul_div_cancel_left _ (by norm_num)] at hshift
    exact (Nat.pow_right_injective le_rfl hshift).symm
  have hk' : k < 2 ^ prog.logSize := hlog ▸ hk
  rw [tailBcSlot, hbc, hshift, hlog,
    LeanVM.Protocol.Relation.bytecodeWords_getD prog (by norm_num : 3 < 16) hk',
    tail_instructionSlots_three, LeanVM.Protocol.Relation.opcodeOf_code, tail_ofK_code]
  exact ⟨by cases (prog.instructions ⟨k, hk'⟩).opcode <;> decide, rfl⟩

/-! ## The program side's tables at `r` -/

/-- Entry `j` of the index side's `X_ω` (`indexArrays`). -/
def xBcEntry (W : Witness) (ch : LinkChallenges) (j : ℕ) : E :=
  let layout := W.layout
  let bytecode := layout.bytecode.toArray
  let nBc := bytecode.size >>> bytecodeSlotBits
  let slot := fun (s j : ℕ) ↦ bytecode.getD (s * nBc + j) 0
  let gm := fun i ↦ ch.gammaMem.getD i 0
  let gPow := (powers gen (2 ^ W.chunks.width)).toArray
  let gj := fun j ↦ gPow.getD j 0
  let weights := slotWeights tables ch.slot (gm 0, gm 1) ch.mu ch.etaMem ch.etaBc
  let (xG, xOne) := (ch.etaBc * ch.slot.getD 1 0, ch.etaBc * ch.slot.getD 2 0)
  if j < nBc then
    let op := opcodeOf (slot 3 j)
    let omega := weights.omega.getD op []
    let pc := weights.pc.getD op []
    xG * gj j + xOne + sumE ((List.range (2 ^ bytecodeSlotBits - 3)).map fun i ↦
      let s := i + 3
      omega.getD s 0 * ofK (slot s j) + pc.getD s 0 * (gj j * ofK (slot s j)))
  else xG * gj j

/-- Entry `j` of the index side's `P_fp` (`indexArrays`). -/
def pFpEntry (W : Witness) (ch : LinkChallenges) (j : ℕ) : E :=
  let layout := W.layout
  let bytecode := layout.bytecode.toArray
  let nBc := bytecode.size >>> bytecodeSlotBits
  let slot := fun (s j : ℕ) ↦ bytecode.getD (s * nBc + j) 0
  let gm := fun i ↦ ch.gammaMem.getD i 0
  let weights := slotWeights tables ch.slot (gm 0, gm 1) ch.mu ch.etaMem ch.etaBc
  if j < nBc then
    let frame := weights.frame.getD (opcodeOf (slot 3 j)) []
    sumE ((List.range (2 ^ bytecodeSlotBits - 4)).map fun i ↦ frame.getD (i + 4) 0 * ofK (slot (i + 4) j))
  else 0

theorem indexArrays_five (W : Witness) (ch : LinkChallenges) :
    (indexArrays W ch).getD 5 #[] = Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦ xBcEntry W ch j.val :=
  rfl

theorem indexArrays_twelve (W : Witness) (ch : LinkChallenges) :
    (indexArrays W ch).getD 12 #[] = Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦ pFpEntry W ch j.val :=
  rfl

theorem tail_getD_bytecode_toArray (bc : List K) (s k : ℕ) :
    bc.toArray.getD (s * (bc.toArray.size >>> bytecodeSlotBits) + k) 0 = tailBcSlot bc s k := by
  rw [tailBcSlot, List.size_toArray, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

theorem xBcEntry_eq (hW : witness? prog input ex = some W) (ch : LinkChallenges) {j : ℕ}
    (hj : j < 2 ^ W.chunks.width) :
    xBcEntry W ch j = ch.etaBc * ch.slot.getD 1 0 * gpow j +
      if j < 2 ^ W.layout.logBytecode then
        ch.etaBc * ch.slot.getD 2 0 + progX W.layout.bytecode
          (slotWeights tables ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) ch.mu ch.etaMem
            ch.etaBc) j
      else 0 := by
  have hn : W.layout.bytecode.toArray.size >>> bytecodeSlotBits = 2 ^ W.layout.logBytecode := by
    rw [List.size_toArray]
    exact (linkSizes hW).2.2.2.2
  unfold xBcEntry
  dsimp only
  simp only [tail_getD_bytecode_toArray]
  rw [hn, tail_getD_powers_toArray _ _ hj]
  split_ifs with h
  · obtain ⟨hop, h3⟩ := tailBcSlot_three hW h
    rw [sumE_eq_sum, sum_map_range,
      show 2 ^ bytecodeSlotBits - 3 = 2 ^ bytecodeSlotBits - 4 + 1 from rfl, sum_range_succ']
    simp only [zero_add, show ∀ i : ℕ, i + 1 + 3 = i + 4 from fun _ ↦ rfl]
    rw [slotWeights_pc_zero _ _ _ _ _ hop (by decide) (fun h ↦ absurd h.1 (by decide)), h3]
    unfold progX
    dsimp only
    ring
  · ring

theorem pFpEntry_eq (W : Witness) (hn : W.layout.bytecode.length >>> bytecodeSlotBits =
      2 ^ W.layout.logBytecode) (ch : LinkChallenges) (j : ℕ) :
    pFpEntry W ch j = if j < 2 ^ W.layout.logBytecode then progF W.layout.bytecode
      (slotWeights tables ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) ch.mu ch.etaMem
        ch.etaBc) j else 0 := by
  unfold pFpEntry
  dsimp only
  simp only [tail_getD_bytecode_toArray]
  rw [List.size_toArray, hn]
  split_ifs
  · rw [sumE_eq_sum, sum_map_range]
    rfl
  · rfl

/-- **`X_ω` at `r`** is the verifier's `η_bc·α_1·index_mle(r) + below(log_bc)·(η_bc·α_2 + X)`, `X`
the program side of the split at `r`'s low coordinates. -/
theorem indexAt_five (hW : witness? prog input ex = some W) (ch : LinkChallenges) (r : List E)
    (hr : r.length = W.chunks.width) :
    (r.foldl Prods.fold (indexProds W ch)).at 5 =
      ch.etaBc * ch.slot.getD 1 0 * indexMle r +
        prodE ((r.drop (min W.layout.logBytecode W.chunks.width)).map (1 + ·)) *
          (ch.etaBc * ch.slot.getD 2 0 +
            (programSide (slotWeights tables ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0)
              ch.mu ch.etaMem ch.etaBc)
              (splitAt W.layout.bytecode (r.take W.layout.logBytecode) (pcSlots tables))).1) := by
  have hb := (linkSizes hW).2.2.2.1
  have hbr : W.layout.logBytecode ≤ r.length := hr ▸ hb
  have hlt : (r.take W.layout.logBytecode).length = W.layout.logBytecode := by
    rw [List.length_take, min_eq_left hbr]
  set xOne := ch.etaBc * ch.slot.getD 2 0
  set xG := ch.etaBc * ch.slot.getD 1 0
  set w := slotWeights tables ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) ch.mu ch.etaMem
    ch.etaBc
  rw [at_foldl, show (indexProds W ch).tables.getD 5 #[] = _ from indexArrays_five W ch,
    mleA_eq_sum _ _ (by rw [Array.size_ofFn, hr])]
  have hentry : ∀ j ∈ range (2 ^ r.length),
      eqAt r j * (Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦ xBcEntry W ch j.val).getD j 0 =
        xG * (eqAt r j * gpow j) +
          eqAt r j * (if j < 2 ^ W.layout.logBytecode then xOne + progX W.layout.bytecode w j else 0) := by
    intro j hj
    have hj' : j < 2 ^ W.chunks.width := hr ▸ mem_range.mp hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hj', Option.getD_some]
    dsimp only
    rw [xBcEntry_eq hW ch hj']
    ring
  have h1 := sum_eqAt (r.take W.layout.logBytecode)
  rw [hlt] at h1
  rw [sum_congr rfl hentry, sum_add_distrib, ← Finset.mul_sum,
    show ∑ j ∈ range (2 ^ r.length), eqAt r j * gpow j = mle r gpow from rfl, ← indexMle_eq_mle,
    tail_sum_eqAt_ite_lt r hbr, min_eq_left hb,
    programSide_splitAt _ _ _ _ _ _ _ (fun k hk ↦ (tailBcSlot_three hW (hlt ▸ hk)).1), hlt]
  dsimp only
  rw [sum_congr rfl fun j _ ↦ mul_add _ _ _, sum_add_distrib, ← sum_mul, h1, one_mul]
  ring

/-- **`P_fp` at `r`** is the verifier's `below(log_bc)·P`, `P` the frame part of the split's
program side. -/
theorem indexAt_twelve (hW : witness? prog input ex = some W) (ch : LinkChallenges) (r : List E)
    (hr : r.length = W.chunks.width) :
    (r.foldl Prods.fold (indexProds W ch)).at 12 =
      prodE ((r.drop (min W.layout.logBytecode W.chunks.width)).map (1 + ·)) *
        (programSide (slotWeights tables ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0)
          ch.mu ch.etaMem ch.etaBc)
          (splitAt W.layout.bytecode (r.take W.layout.logBytecode) (pcSlots tables))).2 := by
  have hb := (linkSizes hW).2.2.2.1
  have hn := (linkSizes hW).2.2.2.2
  have hbr : W.layout.logBytecode ≤ r.length := hr ▸ hb
  have hlt : (r.take W.layout.logBytecode).length = W.layout.logBytecode := by
    rw [List.length_take, min_eq_left hbr]
  rw [at_foldl, show (indexProds W ch).tables.getD 12 #[] = _ from indexArrays_twelve W ch,
    mleA_eq_sum _ _ (by rw [Array.size_ofFn, hr])]
  have hentry : ∀ j ∈ range (2 ^ r.length),
      eqAt r j * (Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦ pFpEntry W ch j.val).getD j 0 =
        eqAt r j * (if j < 2 ^ W.layout.logBytecode then progF W.layout.bytecode
          (slotWeights tables ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) ch.mu ch.etaMem
            ch.etaBc) j else 0) := by
    intro j hj
    have hj' : j < 2 ^ W.chunks.width := hr ▸ mem_range.mp hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hj', Option.getD_some]
    dsimp only
    rw [pFpEntry_eq W hn ch j]
  rw [sum_congr rfl hentry, tail_sum_eqAt_ite_lt r hbr, min_eq_left hb,
    programSide_splitAt _ _ _ _ _ _ _ (fun k hk ↦ (tailBcSlot_three hW (hlt ▸ hk)).1), hlt]
  dsimp only
  rw [mul_comm]

/-! ## On the honest prefix -/

/-- `verify_link`'s slot weights are `slot_weights` of its challenges. -/
theorem linkWeights_eq (layout : Layout) (y : LinkPre) :
    linkWeights layout y = slotWeights layout.tables (verCh layout y).slot
      ((verCh layout y).gammaMem.getD 0 0, (verCh layout y).gammaMem.getD 1 0) (verCh layout y).mu
      (verCh layout y).etaMem (verCh layout y).etaBc :=
  rfl

/-- **The verifier's challenges are the honest prover's.** -/
theorem verCh_honest (hW : witness? prog input ex = some W) {y : LinkPre} {x : LinkProverPre}
    (hp : HonestPre W y x) : verCh W.layout y = x.ch := by
  rw [verCh_eq W.layout y (linkSizes hW).1, hp.ch, hp.chunks]

/-- **The five index tables the verifier reads at `r`**, on the honest prefix: each the closed
form `linkTail` computes (`tailRowSide`). -/
theorem honestIndexAt (hW : witness? prog input ex = some W) {y : LinkPre} {x : LinkProverPre}
    (hp : HonestPre W y x) :
    let ch := verCh W.layout y
    let r := y.r
    let below := fun (k : ℕ) ↦ prodE ((r.drop (min k y.chunks.width)).map (1 + ·))
    x.index.at 6 = eqEval ch.zeta r ∧
      x.index.at 7 = linkShiftEq ch.zeta r ∧
      x.index.at 3 = ch.gammaMem.getD 0 0 * indexMle r +
        ch.gammaMem.getD 3 0 * below W.layout.logMemory + ch.gammaMem.getD 1 0 * y.m1 ∧
      x.index.at 5 = ch.etaBc * ch.slot.getD 1 0 * indexMle r +
        below W.layout.logBytecode * (ch.etaBc * ch.slot.getD 2 0 + (honestProgramSide W y).1) ∧
      x.index.at 12 = below W.layout.logBytecode * (honestProgramSide W y).2 := by
  have hch : verCh W.layout y = x.ch := verCh_honest hW hp
  have hrl : x.r.length = W.chunks.width := hp.rlen
  have hz : x.ch.zeta.length = x.r.length := by
    rw [hp.ch, hrl]
    exact length_zeta tables rfl _ _ _ _ _ hp.drawn
  have hps : honestProgramSide W y = programSide (slotWeights tables x.ch.slot
      (x.ch.gammaMem.getD 0 0, x.ch.gammaMem.getD 1 0) x.ch.mu x.ch.etaMem x.ch.etaBc)
      (splitAt W.layout.bytecode (x.r.take W.layout.logBytecode) (pcSlots tables)) := by
    rw [honestProgramSide, linkWeights_eq, (linkSizes hW).1, hch, hp.r]
  dsimp only
  rw [hch, hp.r, hp.chunks, hp.index, hps, hp.m1, hp.m1eq]
  exact ⟨indexAt_six W x.ch x.r hz, indexAt_seven W x.ch x.r hz hrl,
    indexAt_three hW x.ch x.r hrl (by rw [hp.ch]; rfl), indexAt_five hW x.ch x.r hrl,
    indexAt_twelve hW x.ch x.r hrl⟩

end LeanVM.Prover.Complete

end
