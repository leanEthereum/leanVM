/-
  LeanVM.Prover.Complete.Prods

  A sum-check over a sum of products of multilinear tables (`Prods`, the link's three sum-checks)
  is honest: each round's polynomial is the next claim's, a cube sum.
-/

module

public import LeanVM.Prover.Complete.Keccak.Sumcheck
public import Statement.Prover.Link
import LeanVM.Parameters.Field

/-!
# Sums of products, honestly sum-checked

`Prods` (`Statement/Prover/LinkIndex.lean`) is a sum of terms, each a coefficient times a product of
tables of `2^n` entries. Its cube sum over `m` entries (`cubeSum`) is what a plain sum-check over it
claims. A round's polynomial (`Prods.round`) is the sum over the pairs of entries of the products of
each factor's line, and it evaluates at `x` to the cube sum of the tables folded at `x`
(`polyEval_round`); folding at `0` and `1` splits the cube sum in characteristic two
(`cubeSum_fold_zero_add_one`). So `prodsSumcheck` wins the verifier's plain `sumcheck` from the cube
sum, to its challenges and the folded tables' value (`wins_prodsSumcheck`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Prover.Complete.Keccak

/-! ## Coefficient arrays -/

/-- The polynomial of a coefficient array, constant first, at `x`. -/
noncomputable def aeval (a : Array E) (x : E) : E := ∑ i ∈ Finset.range a.size, a.getD i 0 * x ^ i

theorem polyEval_toList (a : Array E) (x : E) : polyEval a.toList x = aeval a x := by
  rw [polyEval_eq_sum, aeval, Array.length_toList]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem size_mulLineA (p : Array E) (lo hi : E) : (mulLineA p lo hi).size = p.size + 1 := by
  simp [mulLineA]

theorem aeval_mulLineA (p : Array E) (lo hi x : E) :
    aeval (mulLineA p lo hi) x = aeval p x * (lo + x * (lo + hi)) := by
  have hget : ∀ j, (mulLineA p lo hi).getD j 0 =
      if j < p.size + 1 then lo * p.getD j 0 + (if j = 0 then 0 else (lo + hi) * p.getD (j - 1) 0)
      else 0 := by
    intro j
    simp only [mulLineA, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    split <;> simp
  have hlast : p.getD p.size 0 = 0 := by simp [Array.getD_eq_getD_getElem?]
  rw [aeval, size_mulLineA, aeval]
  have e : ∀ j ∈ Finset.range (p.size + 1), (mulLineA p lo hi).getD j 0 * x ^ j =
      lo * (p.getD j 0 * x ^ j) + (if j = 0 then 0 else (lo + hi) * p.getD (j - 1) 0 * x ^ j) := by
    intro j hj
    rw [hget, ite_eq_left (Finset.mem_range.mp hj)]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_succ,
    hlast, zero_mul, add_zero, Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, add_zero]
  rw [Finset.sum_congr rfl fun j _ ↦ show (lo + hi) * p.getD j 0 * x ^ (j + 1) =
      x * (lo + hi) * (p.getD j 0 * x ^ j) by ring, ← Finset.mul_sum]
  ring

theorem getD_modify_self (a : Array E) (f : E → E) {i : ℕ} (hi : i < a.size) :
    (a.modify i f).getD i 0 = f (a.getD i 0) := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getElem?_eq_getElem hi]

theorem getD_modify_ne (a : Array E) (f : E → E) {i j : ℕ} (h : i ≠ j) :
    (a.modify i f).getD j 0 = a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, h]

theorem addInto_spec (acc p : Array E) (hp : p.size ≤ acc.size) :
    (addInto acc p).size = acc.size ∧ ∀ i, (addInto acc p).getD i 0 = acc.getD i 0 + p.getD i 0 := by
  have key : ∀ n ≤ p.size, (Nat.fold n (fun j _ acc ↦ acc.modify j (· + p.getD j 0)) acc).size =
      acc.size ∧ ∀ i, (Nat.fold n (fun j _ acc ↦ acc.modify j (· + p.getD j 0)) acc).getD i 0 =
        acc.getD i 0 + if i < n then p.getD i 0 else 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      obtain ⟨hs, hg⟩ := ih (by omega)
      rw [Nat.fold_succ]
      refine ⟨by rw [Array.size_modify]; exact hs, fun i ↦ ?_⟩
      by_cases hi : i = n
      · subst hi
        rw [getD_modify_self _ _ (by rw [hs]; omega), hg]
        simp
      · rw [getD_modify_ne _ _ (Ne.symm hi), hg]
        by_cases hlt : i < n
        · simp [hlt, show i < n + 1 by omega]
        · simp [hlt, show ¬ i < n + 1 by omega]
  obtain ⟨hs, hg⟩ := key p.size le_rfl
  refine ⟨hs, fun i ↦ ?_⟩
  unfold addInto
  rw [hg]
  by_cases hi : i < p.size
  · simp [hi]
  · simp [hi, Array.getD_eq_getD_getElem?]

theorem aeval_addInto (acc p : Array E) (hp : p.size ≤ acc.size) (x : E) :
    aeval (addInto acc p) x = aeval acc x + aeval p x := by
  obtain ⟨hs, hg⟩ := addInto_spec acc p hp
  unfold aeval
  rw [hs]
  simp only [hg, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_range_add_sum_Ico _ hp]
  have : ∑ i ∈ Finset.Ico p.size acc.size, p.getD i 0 * x ^ i = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      simp [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none (show p.size ≤ i from (Finset.mem_Ico.mp hi).1)]
  rw [this, add_zero]

/-! ## Cube sums -/

/-- A sum of products' value at entry `u` of its tables. -/
def termsAt (P : Prods) (u : ℕ) : E :=
  P.terms.foldl (fun acc cf ↦ acc + cf.2.foldl (fun v f ↦ v * (P.tables.getD f #[]).getD u 0) cf.1) 0

/-- **The cube sum** of a sum of products over its first `m` entries. -/
noncomputable def cubeSum (m : ℕ) (P : Prods) : E := ∑ u ∈ Finset.range m, termsAt P u

theorem value_eq_cubeSum_one (P : Prods) : P.value = cubeSum 1 P := by
  simp [cubeSum, termsAt, Prods.value, Prods.at]

/-- Every table has `2m` entries. -/
def Uniform (m : ℕ) (P : Prods) : Prop := ∀ t ∈ P.tables, t.size = 2 * m

theorem getD_fold_tables (P : Prods) (x : E) (f : ℕ) :
    (P.fold x).tables.getD f #[] = foldPairsA x (P.tables.getD f #[]) := by
  simp only [Prods.fold, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases P.tables[f]? <;> simp [foldPairsA]

theorem getD_foldPairsA {x : E} {t : Array E} {k : ℕ} (hk : k < t.size / 2) :
    (foldPairsA x t).getD k 0 = t.getD (2 * k) 0 + x * (t.getD (2 * k) 0 + t.getD (2 * k + 1) 0) := by
  simp only [foldPairsA, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hk, ↓reduceDIte,
    Option.getD_some, Array.getElem?_eq_getElem (show 2 * k < t.size by omega),
    Array.getElem?_eq_getElem (show 2 * k + 1 < t.size by omega)]
  ring

/-- A factor's entry at `k` once folded at `x`: the line through its entries `2k`, `2k + 1`. -/
theorem fold_entry {m : ℕ} {P : Prods} (hP : Uniform m P) (x : E) (f : ℕ) {k : ℕ} (hk : k < m) :
    ((P.fold x).tables.getD f #[]).getD k 0 =
      (P.tables.getD f #[]).getD (2 * k) 0 + x * ((P.tables.getD f #[]).getD (2 * k) 0 +
        (P.tables.getD f #[]).getD (2 * k + 1) 0) := by
  rw [getD_fold_tables]
  rcases h : P.tables[f]? with _ | t
  · simp [Array.getD_eq_getD_getElem?, h, foldPairsA]
  · have ht : P.tables.getD f #[] = t := by simp [Array.getD_eq_getD_getElem?, h]
    rw [ht]
    exact getD_foldPairsA (by rw [hP t (Array.mem_of_getElem? h)]; omega)

/-- One term's polynomial at the pair `k`: the product of its factors' lines. -/
theorem aeval_foldl_mulLineA (T : Array (Array E)) (k : ℕ) (x : E) :
    ∀ (fs : List ℕ) (p : Array E),
      aeval (fs.foldl (fun p f ↦ mulLineA p ((T.getD f #[]).getD (2 * k) 0)
          ((T.getD f #[]).getD (2 * k + 1) 0)) p) x =
        fs.foldl (fun v f ↦ v * ((T.getD f #[]).getD (2 * k) 0 + x * ((T.getD f #[]).getD (2 * k) 0 +
          (T.getD f #[]).getD (2 * k + 1) 0))) (aeval p x) ∧
      (fs.foldl (fun p f ↦ mulLineA p ((T.getD f #[]).getD (2 * k) 0)
          ((T.getD f #[]).getD (2 * k + 1) 0)) p).size = p.size + fs.length
  | [], p => ⟨rfl, rfl⟩
  | f :: fs, p => by
    obtain ⟨h1, h2⟩ := aeval_foldl_mulLineA T k x fs (mulLineA p _ _)
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons]
      rw [h1, aeval_mulLineA]
    · simp only [List.foldl_cons, h2, size_mulLineA, List.length_cons]
      omega

theorem foldl_mul_congr (g h : ℕ → E) (hgh : ∀ f, g f = h f) (fs : List ℕ) :
    ∀ v : E, fs.foldl (fun v f ↦ v * g f) v = fs.foldl (fun v f ↦ v * h f) v := by
  induction fs with
  | nil => intro v; simp only [List.foldl_nil]
  | cons f fs ih => intro v; simp only [List.foldl_cons, hgh f]; exact ih _

theorem foldl_mul_zero (g : ℕ → E) (fs : List ℕ) : fs.foldl (fun v f ↦ v * g f) 0 = 0 := by
  induction fs with
  | nil => simp only [List.foldl_nil]
  | cons f fs ih => simp only [List.foldl_cons, zero_mul]; exact ih

theorem aeval_single (c x : E) : aeval #[c] x = c := by simp [aeval]

/-- One term's polynomial at the pair `k`: its coefficient times its factors' lines. -/
def termPoly (P : Prods) (k : ℕ) (cf : E × Array ℕ) : Array E :=
  cf.2.foldl (fun p f ↦ mulLineA p ((P.tables.getD f #[]).getD (2 * k) 0)
    ((P.tables.getD f #[]).getD (2 * k + 1) 0)) #[cf.1]

/-- One term added at the pair `k`, as `Prods.round` adds it. -/
def roundStep (P : Prods) (k : ℕ) (acc : Array E) (cf : E × Array ℕ) : Array E :=
  if cf.1 = 0 then acc else addInto acc (termPoly P k cf)

theorem round_eq (P : Prods) (count : ℕ) :
    P.round count = (Nat.fold ((P.tables.getD 0 #[]).size / 2)
      (fun k _ acc ↦ P.terms.foldl (roundStep P k) acc) (Array.replicate count 0)).toList := rfl

/-- A term's value at `k` once folded at `x`. -/
def termAt (P : Prods) (k : ℕ) (cf : E × Array ℕ) : E :=
  cf.2.foldl (fun v f ↦ v * (P.tables.getD f #[]).getD k 0) cf.1

theorem termPoly_spec {m : ℕ} {P : Prods} (hP : Uniform m P) (x : E) {k : ℕ} (hk : k < m)
    (cf : E × Array ℕ) :
    (termPoly P k cf).size = cf.2.size + 1 ∧ aeval (termPoly P k cf) x = termAt (P.fold x) k cf := by
  obtain ⟨hev, hsz⟩ := aeval_foldl_mulLineA P.tables k x cf.2.toList #[cf.1]
  refine ⟨?_, ?_⟩
  · unfold termPoly; rw [← Array.foldl_toList, hsz]; simp; omega
  · unfold termPoly termAt
    rw [← Array.foldl_toList, hev, aeval_single, ← Array.foldl_toList]
    exact (foldl_mul_congr _ _ (fun f ↦ fold_entry hP x f hk) _ _).symm

theorem roundStep_spec {m : ℕ} {P : Prods} (hP : Uniform m P) (count : ℕ) (x : E) {k : ℕ}
    (hk : k < m) (acc : Array E) (cf : E × Array ℕ) (hcf : cf.2.size + 1 ≤ count)
    (hacc : acc.size = count) :
    (roundStep P k acc cf).size = count ∧
      aeval (roundStep P k acc cf) x = aeval acc x + termAt (P.fold x) k cf := by
  obtain ⟨hs, hv⟩ := termPoly_spec hP x hk cf
  unfold roundStep
  split
  · next h0 =>
    refine ⟨hacc, ?_⟩
    rw [termAt, ← Array.foldl_toList, h0, foldl_mul_zero, add_zero]
  · obtain ⟨hs2, -⟩ := addInto_spec acc (termPoly P k cf) (by omega)
    exact ⟨by rw [hs2, hacc], by rw [aeval_addInto _ _ (by omega), hv]⟩

theorem foldl_add_shift {γ : Type} (f : γ → E) : ∀ (ts : List γ) (c : E),
    ts.foldl (fun a cf ↦ a + f cf) c = c + ts.foldl (fun a cf ↦ a + f cf) 0
  | [], c => by simp
  | t :: ts, c => by
    simp only [List.foldl_cons]
    rw [foldl_add_shift f ts (c + f t), foldl_add_shift f ts (0 + f t)]
    ring

theorem terms_spec {m : ℕ} {P : Prods} (hP : Uniform m P) (count : ℕ) (x : E) {k : ℕ}
    (hk : k < m) (ts : List (E × Array ℕ)) (hts : ∀ cf ∈ ts, cf.2.size + 1 ≤ count) :
    ∀ acc : Array E, acc.size = count →
      (ts.foldl (roundStep P k) acc).size = count ∧
        aeval (ts.foldl (roundStep P k) acc) x =
          aeval acc x + ts.foldl (fun a cf ↦ a + termAt (P.fold x) k cf) 0 := by
  induction ts with
  | nil => intro acc h; simp [h]
  | cons cf ts ih =>
    intro acc hacc
    obtain ⟨h1, h2⟩ := roundStep_spec hP count x hk acc cf (hts cf (by simp)) hacc
    obtain ⟨h3, h4⟩ := ih (fun c hc ↦ hts c (by simp [hc])) _ h1
    simp only [List.foldl_cons]
    refine ⟨h3, ?_⟩
    rw [h4, h2, foldl_add_shift _ ts (0 + _)]
    ring

theorem termsAt_eq (P : Prods) (k : ℕ) :
    termsAt P k = P.terms.toList.foldl (fun a cf ↦ a + termAt P k cf) 0 := by
  rw [termsAt, ← Array.foldl_toList]
  rfl

/-- **A round's polynomial is the next claim's**: it evaluates at `x` to the cube sum of the tables
folded at `x`. -/
theorem round_spec {m : ℕ} {P : Prods} (hP : Uniform m P) (h0 : (P.tables.getD 0 #[]).size = 2 * m)
    (count : ℕ) (hc : ∀ cf ∈ P.terms, cf.2.size + 1 ≤ count) (x : E) :
    (P.round count).length = count ∧ polyEval (P.round count) x = cubeSum m (P.fold x) := by
  have hts : ∀ cf ∈ P.terms.toList, cf.2.size + 1 ≤ count := fun cf h ↦ hc cf (by simpa using h)
  have key : ∀ j ≤ m, (Nat.fold j (fun k _ acc ↦ P.terms.foldl (roundStep P k) acc)
      (Array.replicate count 0)).size = count ∧
      aeval (Nat.fold j (fun k _ acc ↦ P.terms.foldl (roundStep P k) acc)
        (Array.replicate count 0)) x = cubeSum j (P.fold x) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp, ?_⟩
      simp only [Nat.fold_zero, aeval, cubeSum, Finset.range_zero, Finset.sum_empty,
        Array.size_replicate]
      exact Finset.sum_eq_zero fun i hi ↦ by
        simp [Array.getD_eq_getD_getElem?, Finset.mem_range.mp hi]
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [Nat.fold_succ, ← Array.foldl_toList]
      obtain ⟨h3, h4⟩ := terms_spec hP count x (by omega : j < m) P.terms.toList hts _ h1
      refine ⟨h3, ?_⟩
      rw [h4, h2, cubeSum, cubeSum, Finset.sum_range_succ, termsAt_eq]
      rfl
  rw [round_eq, h0, Nat.mul_div_cancel_left _ (by norm_num)]
  obtain ⟨h1, h2⟩ := key m le_rfl
  exact ⟨by simp [h1], by rw [polyEval_toList, h2]⟩

theorem sum_range_two_mul (f : ℕ → E) : ∀ m : ℕ,
    ∑ u ∈ Finset.range (2 * m), f u = ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1))
  | 0 => by simp
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul f m, Finset.sum_range_succ]
    ring

theorem line_zero (a b : E) : a + 0 * (a + b) = a := by rw [zero_mul, add_zero]

theorem line_one (a b : E) : a + 1 * (a + b) = b := by
  rw [one_mul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem termAt_fold_zero {m : ℕ} {P : Prods} (hP : Uniform m P) {k : ℕ} (hk : k < m)
    (cf : E × Array ℕ) : termAt (P.fold 0) k cf = termAt P (2 * k) cf := by
  unfold termAt
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_mul_congr _ _ (fun f ↦ (fold_entry hP 0 f hk).trans (line_zero _ _)) _ _

theorem termAt_fold_one {m : ℕ} {P : Prods} (hP : Uniform m P) {k : ℕ} (hk : k < m)
    (cf : E × Array ℕ) : termAt (P.fold 1) k cf = termAt P (2 * k + 1) cf := by
  unfold termAt
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_mul_congr _ _ (fun f ↦ (fold_entry hP 1 f hk).trans (line_one _ _)) _ _

theorem fold_terms (P : Prods) (x : E) : (P.fold x).terms = P.terms := rfl

/-- **Folding at `0` and `1` splits the cube sum**, in characteristic two. -/
theorem cubeSum_fold_zero_add_one {m : ℕ} {P : Prods} (hP : Uniform m P) :
    cubeSum m (P.fold 0) + cubeSum m (P.fold 1) = cubeSum (2 * m) P := by
  unfold cubeSum
  rw [sum_range_two_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  rw [termsAt_eq, termsAt_eq, termsAt_eq, termsAt_eq, fold_terms, fold_terms,
    show (fun a cf ↦ a + termAt (P.fold 0) k cf) = (fun a cf ↦ a + termAt P (2 * k) cf) from
      funext fun a ↦ funext fun cf ↦ by rw [termAt_fold_zero hP hk' cf],
    show (fun a cf ↦ a + termAt (P.fold 1) k cf) = (fun a cf ↦ a + termAt P (2 * k + 1) cf) from
      funext fun a ↦ funext fun cf ↦ by rw [termAt_fold_one hP hk' cf]]

/-! ## The sum-check -/

/-- Every table of `2^n` entries, the first among them. -/
def Tabs (n : ℕ) (P : Prods) : Prop :=
  (∀ t ∈ P.tables, t.size = 2 ^ n) ∧ (P.tables.getD 0 #[]).size = 2 ^ n

theorem size_foldPairsA (r : E) (t : Array E) : (foldPairsA r t).size = t.size / 2 := by
  simp [foldPairsA]

theorem foldl_fold_terms (P : Prods) : ∀ pre : List E, (pre.foldl Prods.fold P).terms = P.terms := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil => rfl
  | append_singleton pre x ih => rw [List.foldl_append, List.foldl_cons, List.foldl_nil, fold_terms, ih]

theorem Tabs.uniform {n : ℕ} {P : Prods} (h : Tabs (n + 1) P) : Uniform (2 ^ n) P :=
  fun t ht ↦ by rw [h.1 t ht, pow_succ]; ring

theorem Tabs.fold {n : ℕ} {P : Prods} (h : Tabs (n + 1) P) (x : E) : Tabs n (P.fold x) := by
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · obtain ⟨t0, ht0, rfl⟩ := Array.mem_map.mp ht
    rw [size_foldPairsA, h.1 t0 ht0, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  · rw [getD_fold_tables, size_foldPairsA, h.2, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem Tabs.foldl {n : ℕ} {P : Prods} (h : Tabs n P) :
    ∀ pre : List E, pre.length ≤ n → Tabs (n - pre.length) (pre.foldl Prods.fold P) := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil => intro _; simpa using h
  | append_singleton pre x ih =>
    intro hl
    simp only [List.length_append, List.length_singleton] at hl ⊢
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have := ih (by omega)
    rw [show n - pre.length = n - (pre.length + 1) + 1 by omega] at this
    exact this.fold x

/-- The claim after the challenges `pre`: the cube sum of the tables folded at them. -/
noncomputable def prodsClaim (n : ℕ) (P : Prods) (pre : List E) : E :=
  cubeSum (2 ^ (n - pre.length)) (pre.foldl Prods.fold P)

theorem polyLE_polyEval (l : List E) : PolyLE (l.length - 1) (polyEval l) :=
  ⟨polyOfList l, natDegree_polyOfList l, fun x ↦ (eval_polyOfList l x).symm⟩

/-- **The honest sum-check over a sum of products wins** the verifier's plain `sumcheck` from the
cube sum, to its challenges and the folded tables' value. -/
theorem wins_prodsSumcheck {B : ℕ} (count n : ℕ) (hcount : 2 ≤ count) (hc' : count ≤ 2 ^ 128)
    (hB : roundBits count none ≤ B) (P : Prods) (hP : Tabs n P)
    (hc : ∀ cf ∈ P.terms, cf.2.size + 1 ≤ count) (cs : List Committed) :
    Wins B (fun a s g cs' ↦ a.1 = s.1 ∧ s.1.length = n ∧ s.2 = s.1.foldl Prods.fold P ∧
        a.2 = s.2.value ∧ g = false ∧ cs' = cs)
      (sumcheck (cubeSum (2 ^ n) P) count (List.replicate n none)) (prodsSumcheck count n P)
      false cs := by
  have hround : ∀ pre : List E, pre.length < n →
      (Prods.round (pre.foldl Prods.fold P) count).length = count ∧
        ∀ x, polyEval (Prods.round (pre.foldl Prods.fold P) count) x = prodsClaim n P (pre ++ [x]) := by
    intro pre hl
    have ht := hP.foldl pre hl.le
    obtain ⟨k, hk⟩ : ∃ k, n - pre.length = k + 1 := ⟨n - pre.length - 1, by omega⟩
    rw [hk] at ht
    have hspec := round_spec ht.uniform (by rw [ht.2, pow_succ]; ring) count
      (fun cf h ↦ hc cf (by rwa [foldl_fold_terms] at h))
    refine ⟨(hspec 0).1, fun x ↦ ?_⟩
    rw [(hspec x).2, prodsClaim, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton, show n - (pre.length + 1) = k by omega]
  have hcorr := corr_sumcheckBy_lt count (by omega) hc' (prodsClaim n P) (fun P ↦ P.round count)
    Prods.fold (fun pre st ↦ st = pre.foldl Prods.fold P) n
    (fun pre st h hl ↦ by subst h; exact hround pre hl)
    (fun pre st c h _ ↦ by subst h; rw [List.foldl_append, List.foldl_cons, List.foldl_nil])
    (List.replicate n none) [] P rfl (by simp)
  have hwin := wins_sumcheck (B := B) count hcount (prodsClaim n P) (List.replicate n none) [] cs
    (fun m hm ↦ by rw [List.eq_of_mem_replicate hm]; exact hB)
    (fun ext hext ↦ by
      simp only [List.length_replicate] at hext
      obtain ⟨hl, hev⟩ := hround ext hext
      have := polyLE_polyEval (Prods.round (ext.foldl Prods.fold P) count)
      rw [hl] at this
      simp only [List.nil_append]
      exact PolyLE.congr this hev)
    (fun ext hext ↦ by
      simp only [List.length_replicate] at hext
      simp only [List.getElem_replicate, RoundSplit, List.nil_append]
      have ht := hP.foldl ext hext.le
      obtain ⟨k, hk⟩ : ∃ k, n - ext.length = k + 1 := ⟨n - ext.length - 1, by omega⟩
      rw [hk] at ht
      unfold prodsClaim
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_singleton, show n - (ext.length + 1) = k by omega, hk]
      rw [cubeSum_fold_zero_add_one ht.uniform, pow_succ, mul_comm])
  have := Wins.corr _ _ _ _ _ hcorr hwin
  have h0 : prodsClaim n P [] = cubeSum (2 ^ n) P := by simp [prodsClaim]
  rw [h0] at this
  refine Wins.mono (fun a s g cs' h ↦ ?_) _ _ _ _ this
  obtain ⟨b, ⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9⟩ := h
  subst h5
  simp only [List.nil_append, List.length_replicate] at h1 h2 h3 h4 h6 h7
  refine ⟨h1.symm, h4, h2, ?_, h8, h9⟩
  rw [h7, prodsClaim, ← h1, ← h2, h4, Nat.sub_self, pow_zero, value_eq_cubeSum_one]

end LeanVM.Prover.Complete

end
