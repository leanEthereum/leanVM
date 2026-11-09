/-
  LeanVM.Prover.Keccak.Tables

  The array helpers of the executable Keccak prover read as sums: loops as `Finset` sums, the
  equality table as `eqAt`, a folded table as the multilinear extension at the challenges, the
  coefficient lists as the polynomials they evaluate to, packed bits and byte tables.
-/

module

public import LeanVM.Prover.Sumcheck
public import LeanVM.Prover.Mle
public import Statement.Prover.Keccak
public import LeanVM.Protocol.Keccak.Complete

/-!
# Tables

* `foldl_range_sum`: a loop adding `f i` is `Σ_i f i`;
* `eqTable_eq`, `eqTable_getD`: `eqTable pt` is `eqKernel pt`, entry `w` is `eqAt pt w`;
* `Affine F`: `F` is affine in each coordinate (`affine_mle`: a multilinear extension is);
  `TabInv t F n acc`: `t` lists `F` at `acc` followed by the remaining cube points;
  `tabInv_fold`: `foldPairsA` keeps it, one coordinate further; `tabInv_split`: the next
  coordinate's values from the table's rows;
* `polyEval_sumCoeffs`, `polyEval_scaleCoeffs`, `polyEval_addCoeffs`: coefficient lists add and
  scale as their polynomials do;
* `testBit_packBits`, `byteSums_getD`, `wordDot_laneTabs`, `addBits_getD`.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

/-! ## Loops -/

theorem foldl_range_sum (step : E → ℕ → E) (f : ℕ → E) (hstep : ∀ acc i, step acc i = acc + f i) :
    ∀ (n : ℕ) (a : E), (List.range n).foldl step a = a + ∑ i ∈ range n, f i
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, foldl_range_sum step f hstep n a, List.foldl_cons,
      List.foldl_nil, hstep, Finset.sum_range_succ, add_assoc]

theorem array_getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) :
    (Array.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split <;> simp_all

theorem array_getD_ofFn_lt {α : Type} {n : ℕ} (f : Fin n → α) {i : ℕ} (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  rw [array_getD_ofFn, dite_eq_left h]

/-! ## The equality table -/

theorem eqTable_eq (pt : List E) : eqTable pt = (eqKernel pt).toArray := by
  unfold eqTable eqKernel
  suffices h : ∀ (l a : List E), l.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r))
      a.toArray = (l.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) a).toArray from
    h pt [1]
  intro l
  induction l with
  | nil => intro a; rfl
  | cons r l ih =>
    intro a
    rw [List.foldl_cons, List.foldl_cons, ← ih]
    simp

theorem eqTable_getD (pt : List E) (w : ℕ) :
    (eqTable pt).getD w 0 = if w < 2 ^ pt.length then eqAt pt w else 0 := by
  rw [eqTable_eq, array_getD_toArray, eqKernel_getD]

theorem eqTable_getD_lt (pt : List E) {w : ℕ} (hw : w < 2 ^ pt.length) :
    (eqTable pt).getD w 0 = eqAt pt w := by
  rw [eqTable_getD, ite_eq_left hw]

/-! ## Folded tables -/

/-- `F` is affine in each coordinate, between its values at `0` and `1`. -/
def Affine (F : List E → E) : Prop :=
  ∀ pre post x, F (pre ++ x :: post) =
    F (pre ++ 0 :: post) + x * (F (pre ++ 0 :: post) + F (pre ++ 1 :: post))

theorem one_add_one_E : (1 : E) + 1 = 0 := CharTwo.add_self_eq_zero 1

/-- **A multilinear extension is affine** in each coordinate. -/
theorem affine_mle (N : ℕ) (f : ℕ → E) : Affine fun p ↦ ∑ w ∈ range N, eqAt p w * f w := by
  intro pre post x
  dsimp only
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp only [eqAt_append, eqAt_cons]
  split_ifs
  · ring
  · rw [show (1 : E) + 1 = 0 from one_add_one_E]; ring

/-- `t` lists `F` at `acc` followed by each point of the remaining cube of `n - |acc|`
coordinates. -/
def TabInv (t : Array E) (F : List E → E) (n : ℕ) (acc : List E) : Prop :=
  acc.length ≤ n ∧ t.size = 2 ^ (n - acc.length) ∧
    ∀ u < 2 ^ (n - acc.length), t.getD u 0 = F (acc ++ bitsE u (n - acc.length))

/-- The next coordinate's values from the rows `2u`, `2u + 1`. -/
theorem affine_bitsE {F : List E → E} (hF : Affine F) (acc : List E) (m u : ℕ) (x : E) :
    F (acc ++ x :: bitsE u m) = F (acc ++ bitsE (2 * u) (m + 1)) +
      x * (F (acc ++ bitsE (2 * u) (m + 1)) + F (acc ++ bitsE (2 * u + 1) (m + 1))) := by
  rw [bitsE_two_mul, bitsE_two_mul_add_one, hF]

theorem tabInv_split {t : Array E} {F : List E → E} {n : ℕ} {acc : List E} (hF : Affine F)
    (h : TabInv t F n acc) (hlt : acc.length < n) {u : ℕ}
    (hu : u < 2 ^ (n - (acc.length + 1))) (x : E) :
    F (acc ++ x :: bitsE u (n - (acc.length + 1))) =
      t.getD (2 * u) 0 + x * (t.getD (2 * u) 0 + t.getD (2 * u + 1) 0) := by
  have hm : n - acc.length = n - (acc.length + 1) + 1 := by omega
  have h2 : 2 * u + 1 < 2 ^ (n - acc.length) := by rw [hm, pow_succ]; omega
  rw [affine_bitsE hF, h.2.2 _ (by omega), h.2.2 _ h2, hm]

/-- **The fold keeps the table**, one coordinate further. -/
theorem tabInv_fold {t : Array E} {F : List E → E} {n : ℕ} {acc : List E} (hF : Affine F)
    (h : TabInv t F n acc) (hlt : acc.length < n) (c : E) :
    TabInv (foldPairsA c t) F n (acc ++ [c]) := by
  have hm : n - acc.length = n - (acc.length + 1) + 1 := by omega
  have hsz : (foldPairsA c t).size = 2 ^ (n - (acc.length + 1)) := by
    rw [foldPairsA, Array.size_ofFn, h.2.1, hm, pow_succ]; omega
  rw [TabInv, List.length_append, List.length_singleton]
  refine ⟨by omega, hsz, fun u hu ↦ ?_⟩
  rw [getD_foldPairsA _ _ (by rw [h.2.1, hm, pow_succ]; omega), List.append_assoc,
    List.singleton_append, tabInv_split hF h hlt hu]
  ring

/-- An affine function of a table's next coordinate, summed over the rest. -/
theorem tabInv_full {t : Array E} {F : List E → E} {n : ℕ} {acc : List E}
    (h : TabInv t F n acc) (hn : acc.length = n) : t.getD 0 0 = F acc := by
  have := h.2.2 0 (by rw [hn, Nat.sub_self]; norm_num)
  rw [this, hn, Nat.sub_self]
  simp [bitsE]

/-! ## Coefficient lists -/

theorem polyEval_nil' (x : E) : polyEval [] x = 0 := rfl

theorem polyEval_cons' (c : E) (l : List E) (x : E) : polyEval (c :: l) x = polyEval l x * x + c :=
  rfl

theorem polyEval_addCoeffs : ∀ (a b : List E), a.length = b.length → ∀ x,
    polyEval (addCoeffs a b) x = polyEval a x + polyEval b x
  | [], [], _, x => by simp [addCoeffs, polyEval_nil']
  | c :: a, d :: b, h, x => by
    have ih := polyEval_addCoeffs a b (by simpa using h) x
    simp only [addCoeffs, List.zipWith_cons_cons] at ih ⊢
    rw [polyEval_cons', ih, polyEval_cons', polyEval_cons']
    ring
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

theorem length_addCoeffs (a b : List E) : (addCoeffs a b).length = min a.length b.length := by
  simp [addCoeffs]

theorem polyEval_replicate_zero : ∀ (k : ℕ) (x : E), polyEval (List.replicate k 0) x = 0
  | 0, _ => rfl
  | k + 1, x => by
    rw [List.replicate_succ, polyEval_cons', polyEval_replicate_zero k x]; ring

/-- **A sum of coefficient lists evaluates as the sum.** -/
theorem polyEval_sumCoeffs (k n : ℕ) (v : ℕ → List E) (hv : ∀ i < n, (v i).length = k) (x : E) :
    (sumCoeffs k n v).length = k ∧
      polyEval (sumCoeffs k n v) x = ∑ i ∈ range n, polyEval (v i) x := by
  unfold sumCoeffs
  induction n with
  | zero => simp [polyEval_replicate_zero]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi ↦ hv i (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl : (v n).length = k := hv n (by omega)
    refine ⟨by rw [length_addCoeffs, h1, hl, min_self], ?_⟩
    rw [polyEval_addCoeffs _ _ (by rw [h1, hl]), h2, Finset.sum_range_succ]

theorem polyEval_scaleCoeffs (s : E) (a : List E) (x : E) :
    polyEval (scaleCoeffs s a) x = s * polyEval a x := by
  induction a with
  | nil => simp [scaleCoeffs, polyEval_nil']
  | cons c a ih =>
    simp only [scaleCoeffs, List.map_cons] at ih ⊢
    rw [polyEval_cons', ih, polyEval_cons']
    ring

theorem length_scaleCoeffs (s : E) (a : List E) : (scaleCoeffs s a).length = a.length := by
  simp [scaleCoeffs]

/-! ## Bits -/

theorem ite_bitE (b : Bool) (w : E) : (if b = true then w else 0) = w * bitE b := by
  cases b <;> simp

theorem testBit_packBits (f : ℕ → Bool) : ∀ (n i : ℕ),
    (packBits f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [packBits]
  | n + 1, i => by
    rw [packBits, Nat.testBit_or, testBit_packBits f n i]
    split_ifs with hf
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases h1 : i < n
      · have h2 : ¬ n = i := by omega
        have h3 : i < n + 1 := by omega
        simp [h1, h2, h3]
      · by_cases h2 : n = i
        · subst h2; simp [hf]
        · have h3 : ¬ i < n + 1 := by omega
          simp [h1, h2, h3]
    · rw [Nat.zero_testBit, Bool.or_false]
      by_cases h1 : i < n
      · have h3 : i < n + 1 := by omega
        simp [h1, h3]
      · by_cases h2 : i = n
        · subst h2; simp [hf]
        · have h3 : ¬ i < n + 1 := by omega
          simp [h1, h3]

theorem packBits_lt (f : ℕ → Bool) : ∀ n, packBits f n < 2 ^ n
  | 0 => by simp [packBits]
  | n + 1 => by
    rw [packBits]
    refine Nat.or_lt_two_pow ((packBits_lt f n).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))) ?_
    split_ifs
    · rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · positivity

theorem testBit_mod_256 (m : ℕ) {t : ℕ} (ht : t < 8) : (m % 256).testBit t = m.testBit t := by
  rw [show (256 : ℕ) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]
  simp [ht]

theorem testBit_div_256 (m : ℕ) {t : ℕ} (ht : t < 8) :
    (m / 256 % 256).testBit t = m.testBit (8 + t) := by
  rw [testBit_mod_256 _ ht, show (256 : ℕ) = 2 ^ 8 from rfl, Nat.testBit_div_two_pow, Nat.add_comm]

theorem testBit_shift_mod (m k : ℕ) {t : ℕ} (ht : t < 8) :
    ((m >>> (8 * k)) % 256).testBit t = m.testBit (8 * k + t) := by
  rw [testBit_mod_256 _ ht, Nat.testBit_shiftRight]

theorem foldl_cond_sum (p : ℕ → Prop) [DecidablePred p] (v : ℕ → E) (n : ℕ) (a : E) :
    (List.range n).foldl (fun acc t ↦ if p t then acc + v t else acc) a =
      a + ∑ t ∈ range n, if p t then v t else 0 :=
  foldl_range_sum _ _ (fun acc t ↦ by split_ifs <;> simp) n a

/-- **A byte table's entry** is the sum of the values the byte selects. -/
theorem byteSums_getD (v : ℕ → E) {b : ℕ} (hb : b < 256) :
    (byteSums v).getD b 0 = ∑ t ∈ range 8, if b.testBit t then v t else 0 := by
  rw [byteSums, array_getD_ofFn_lt _ hb]
  simp only
  rw [foldl_cond_sum (fun t ↦ b.testBit t = true), zero_add]

/-- **A word's bits against the weights `v(64·l + ·)`**, by eight byte tables. -/
theorem wordDot_laneTabs (v : ℕ → E) (l word : ℕ) :
    wordDot (laneTabs v l) word = ∑ b ∈ range 64, if word.testBit b then v (64 * l + b) else 0 := by
  rw [wordDot, sumRange_eq, show 64 = 8 * 8 from rfl, sum_range_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.1 hk
  rw [laneTabs, array_getD_ofFn_lt _ hk', byteSums_getD _ (Nat.mod_lt _ (by norm_num))]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [testBit_shift_mod _ _ (Finset.mem_range.1 ht), add_assoc]

theorem modify_getD' (a : Array E) (i c : ℕ) (f : E → E) :
    (a.modify i f).getD c 0 = if i = c ∧ c < a.size then f (a.getD c 0) else a.getD c 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : i = c
  · subst h1
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

/-- **`addBits`**: `x` added at the set bits below `n`. -/
theorem addBits_getD (x : E) (g : ℕ) : ∀ (n : ℕ) (acc : Array E),
    (addBits x g n acc).size = acc.size ∧ ∀ c, (addBits x g n acc).getD c 0 =
      acc.getD c 0 + if c < n ∧ c < acc.size ∧ g.testBit c = true then x else 0
  | 0, acc => ⟨rfl, fun c ↦ by simp [addBits]⟩
  | n + 1, acc => by
    let acc' := if g.testBit n then acc.modify n (· + x) else acc
    have hsz : acc'.size = acc.size := by
      simp only [acc']; split <;> simp
    have hget : ∀ c, acc'.getD c 0 =
        acc.getD c 0 + if c = n ∧ c < acc.size ∧ g.testBit c = true then x else 0 := by
      intro c
      simp only [acc']
      split_ifs with h1 h2 h2
      · rw [modify_getD', ite_eq_left ⟨h2.1.symm, h2.2.1⟩]
      · rw [modify_getD']
        by_cases h3 : n = c ∧ c < acc.size
        · exact absurd ⟨h3.1.symm, h3.2, h3.1 ▸ h1⟩ h2
        · rw [ite_eq_right h3, add_zero]
      · exact absurd (h2.1 ▸ h2.2.2) (by simp [h1])
      · rw [add_zero]
    obtain ⟨h1, h2⟩ := addBits_getD x g n acc'
    refine ⟨h1.trans hsz, fun c ↦ ?_⟩
    show (addBits x g n acc').getD c 0 = _
    rw [h2, hget, hsz, add_assoc]
    congr 1
    by_cases hc : c < n + 1 ∧ c < acc.size ∧ g.testBit c = true
    · rw [ite_eq_left hc]
      by_cases hcn : c = n
      · rw [ite_eq_left ⟨hcn, hc.2⟩, ite_eq_right (fun h ↦ absurd h.1 (by omega)), add_zero]
      · rw [ite_eq_right (fun h ↦ hcn h.1),
          ite_eq_left ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hc.1) hcn, hc.2⟩, zero_add]
    · rw [ite_eq_right hc,
        ite_eq_right (fun (h : c = n ∧ c < acc.size ∧ g.testBit c = true) ↦
          hc ⟨by rw [h.1]; exact Nat.lt_succ_self n, h.2⟩),
        ite_eq_right (fun (h : c < n ∧ c < acc.size ∧ g.testBit c = true) ↦
          hc ⟨Nat.lt_succ_of_lt h.1, h.2⟩), add_zero]

/-- A loop of `addBits` from zeros: entry `c` is the sum of the `x i` whose `g i` has bit `c`. -/
theorem foldl_addBits (n k : ℕ) (x : ℕ → E) (g : ℕ → ℕ) :
    ((List.range n).foldl (fun acc i ↦ addBits (x i) (g i) k acc) (Array.replicate k 0)).size = k ∧
      ∀ c < k, ((List.range n).foldl (fun acc i ↦ addBits (x i) (g i) k acc)
        (Array.replicate k 0)).getD c 0 =
        ∑ i ∈ range n, if (g i).testBit c then x i else 0 := by
  induction n with
  | zero =>
    refine ⟨by simp, fun c hc ↦ ?_⟩
    simp [Array.getD_eq_getD_getElem?, hc]
  | succ n ih =>
    obtain ⟨hs, hg⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2⟩ := addBits_getD (x n) (g n) k
      ((List.range n).foldl (fun acc i ↦ addBits (x i) (g i) k acc) (Array.replicate k 0))
    refine ⟨h1.trans hs, fun c hc ↦ ?_⟩
    rw [h2, hg c hc, hs, Finset.sum_range_succ]
    congr 1
    by_cases hb : (g n).testBit c = true
    · rw [ite_eq_left ⟨hc, hc, hb⟩, ite_eq_left hb]
    · rw [ite_eq_right (fun h ↦ hb h.2.2), ite_eq_right hb]

end
end LeanVM.Prover.KeccakGkr
