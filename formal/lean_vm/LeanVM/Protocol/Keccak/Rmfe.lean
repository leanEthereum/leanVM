/-
  LeanVM.Protocol.Keccak.Rmfe

  The reverse multiplication-friendly embedding of `verifyKeccak`: the verifier's `RMFE_EMBED`
  and `RMFE_PROJECT` as literals, the product property checked by the kernel, and its reading
  over `E`: the projection of a product of two embeddings is the AND of what they embed.
-/

module

public import LeanVM.Protocol.Keccak.Multilinear

/-!
# The embedding

`RMFE_EMBED` and `RMFE_PROJECT` (`crates/verifier/src/keccak.rs:22-46`, `rmfe`) are sixteen binary
polynomials `emb_a` of degree at most `23` (`rmfeEmbed`) and sixteen masks over the `47`
coefficients of a product (`rmfeProject`); the lemma of `doc/leanvm` §`keccak:rmfe-proof` is that
the parity of `mask_i ∧ (emb(u)·emb(v))` is `u_i ∧ v_i`. By bilinearity it is enough on unit
vectors:

* `rmfeOk_lit` (kernel): for all `a, b, i < 16`, the parity of the masked coefficients of the
  carry-less product `emb_a · emb_b` is `[i = a = b]`; `rmfe_carryless` states it with the
  verifier's own `carryless` and `bitParity`;
* `embP a`, the embedding as a polynomial over `E` with `0/1` coefficients, and `projE`, the
  projection of a polynomial with `E` coefficients (the masked sum of its coefficients);
* `projE_embP_mul`: `projE_i (embP a · embP b) = [i = a = b]` in `E` (characteristic two:
  a coefficient of the product over `E` is the parity of the carry-less one);
* `projE_bilin`: for `E`-combinations, `projE_i ((Σ_a u_a emb_a)(Σ_b v_b emb_b)) = u_i v_i`;
* `keccakInstanceWeights_getD`: the verifier's instance weights at `s` are `emb_a(s)`;
* `projected_eq`: the verifier's projected value `Σ_c (Σ_{i : mask_i ∋ c} μ_i) · G_c` is
  `Σ_i μ_i · projE_i(G)`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete Finset Polynomial

@[expose] public section

/-! ## The literals -/

/-- `RMFE_EMBED` (`keccak.rs:25-28`), in decimal. -/
def embedLit : List ℕ := [4244747, 8354290, 4935178, 7500812, 5461978, 1907870, 310894, 7885382,
  621788, 1089150, 2036820, 2178300, 5045448, 7821168, 1602438, 8489494]

/-- `RMFE_PROJECT` (`keccak.rs:29-46`), in decimal. -/
def projectLit : List ℕ := [1, 140737488355327, 43218598786281, 32136906789799, 111925089164473,
  101951566367639, 112771593653537, 102871349771039, 126754541004432, 60819261648545,
  20682647020959, 30409630824272, 11891857888673, 6939470531743, 76314673122000, 70368744177664]

set_option maxRecDepth 100000 in
theorem rmfeEmbed_eq : rmfeEmbed = embedLit := by decide +kernel

set_option maxRecDepth 100000 in
theorem rmfeProject_eq : rmfeProject = projectLit := by decide +kernel

theorem rmfeEmbed_length : rmfeEmbed.length = 16 := by rw [rmfeEmbed_eq]; rfl

theorem rmfeProject_length : rmfeProject.length = 16 := by rw [rmfeProject_eq]; rfl

/-! ## The kernel check -/

/-- The low `k` bits of `n`, as a list. -/
def bitsFrom : ℕ → ℕ → List Bool
  | _, 0 => []
  | n, k + 1 => decide (n % 2 = 1) :: bitsFrom (n / 2) k

/-- The sum of two binary polynomials. -/
def xorL : List Bool → List Bool → List Bool
  | [], l => l
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x ^^ y) :: xorL xs ys

/-- The product of two binary polynomials. -/
def mulGF2 : List Bool → List Bool → List Bool
  | [], _ => []
  | a :: A, B => xorL (if a then B else []) (false :: mulGF2 A B)

/-- The parity of the coefficients of `M` that `mask` selects, among the first `47`. -/
def parityL (mask : ℕ) (M : List Bool) : Bool :=
  (List.range 47).foldl (fun acc c ↦ acc ^^ (mask.testBit c && M.getD c false)) false

/-- The embedding lemma on unit vectors, as a boolean. -/
def rmfeOk (emb proj : List ℕ) : Bool :=
  (List.range 16).all fun a ↦ (List.range 16).all fun b ↦ (List.range 16).all fun i ↦
    parityL (proj.getD i 0) (mulGF2 (bitsFrom (emb.getD a 0) 24) (bitsFrom (emb.getD b 0) 24)) ==
      (i == a && a == b)

set_option maxRecDepth 100000 in
/-- **The embedding lemma**, checked by the kernel on the literals. -/
theorem rmfeOk_lit : rmfeOk embedLit projectLit = true := by decide +kernel

theorem rmfeOk_at {a b i : ℕ} (ha : a < 16) (hb : b < 16) (hi : i < 16) :
    parityL (rmfeProject.getD i 0)
      (mulGF2 (bitsFrom (rmfeEmbed.getD a 0) 24) (bitsFrom (rmfeEmbed.getD b 0) 24)) =
        (i == a && a == b) := by
  have h := rmfeOk_lit
  rw [← rmfeEmbed_eq, ← rmfeProject_eq] at h
  simp only [rmfeOk, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h a ha b hb i hi

/-! ## Binary polynomials over `E` -/

/-- A binary polynomial, coefficient list lowest first, over `E`. -/
noncomputable def polyOfBits : List Bool → E[X]
  | [] => 0
  | b :: l => C (bitE b) + X * polyOfBits l

theorem coeff_polyOfBits : ∀ (l : List Bool) (c : ℕ),
    (polyOfBits l).coeff c = bitE (l.getD c false)
  | [], c => by simp [polyOfBits]
  | b :: l, 0 => by simp [polyOfBits]
  | b :: l, c + 1 => by simp [polyOfBits, coeff_polyOfBits l c]

theorem polyOfBits_xorL : ∀ A B : List Bool, polyOfBits (xorL A B) = polyOfBits A + polyOfBits B
  | [], l => by simp [xorL, polyOfBits]
  | x :: xs, [] => by simp [xorL, polyOfBits]
  | x :: xs, y :: ys => by
    simp only [xorL, polyOfBits, polyOfBits_xorL xs ys, bitE_xor, C_add]
    ring

theorem polyOfBits_mulGF2 : ∀ A B : List Bool,
    polyOfBits (mulGF2 A B) = polyOfBits A * polyOfBits B
  | [], B => by simp [mulGF2, polyOfBits]
  | a :: A, B => by
    rw [mulGF2, polyOfBits_xorL]
    cases a <;> simp [polyOfBits, polyOfBits_mulGF2 A B] <;> ring

theorem bitsFrom_getD : ∀ (n k c : ℕ), (bitsFrom n k).getD c false = (decide (c < k) && n.testBit c)
  | n, 0, c => by simp [bitsFrom]
  | n, k + 1, 0 => by simp [bitsFrom, Nat.testBit_zero]
  | n, k + 1, c + 1 => by
    rw [bitsFrom, List.getD_cons_succ, bitsFrom_getD (n / 2) k c, Nat.testBit_div_two]
    simp

/-! ## The embedding and the projection over `E` -/

/-- `emb_a`, the embedding of the unit vector `a`, a polynomial of degree at most `23`. -/
noncomputable def embP (a : ℕ) : E[X] := polyOfBits (bitsFrom (rmfeEmbed.getD a 0) 24)

theorem embP_coeff (a c : ℕ) :
    (embP a).coeff c = if c < 24 then bitE ((rmfeEmbed.getD a 0).testBit c) else 0 := by
  rw [embP, coeff_polyOfBits, bitsFrom_getD]
  by_cases h : c < 24 <;> simp [h]

theorem embP_natDegree (a : ℕ) : (embP a).natDegree ≤ 23 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro c hc
  rw [embP_coeff, ite_eq_right (by exact_mod_cast (show ¬ c < 24 by omega))]

/-- The projection to bit `mask`: the sum of the masked coefficients among the first `47`. -/
noncomputable def projE (mask : ℕ) (P : E[X]) : E :=
  ∑ c ∈ range 47, if mask.testBit c then P.coeff c else 0

theorem projE_add (mask : ℕ) (P Q : E[X]) : projE mask (P + Q) = projE mask P + projE mask Q := by
  simp only [projE, coeff_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  split_ifs <;> simp

theorem projE_C_mul (mask : ℕ) (a : E) (P : E[X]) : projE mask (C a * P) = a * projE mask P := by
  simp only [projE, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  split_ifs <;> simp

theorem projE_sum {ι : Type} (mask : ℕ) (s : Finset ι) (P : ι → E[X]) :
    projE mask (∑ i ∈ s, P i) = ∑ i ∈ s, projE mask (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [projE]
  | insert a s ha ih => rw [Finset.sum_insert ha, projE_add, ih, Finset.sum_insert ha]

theorem sum_bitE_xor (f : ℕ → Bool) (n : ℕ) :
    ∑ c ∈ range n, bitE (f c) = bitE ((List.range n).foldl (fun acc c ↦ acc ^^ f c) false) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.foldl_concat, bitE_xor]

/-- **The embedding lemma over `E`**: the projection to bit `i` of `emb_a · emb_b` is
`[i = a = b]`. -/
theorem projE_embP_mul {i a b : ℕ} (hi : i < 16) (ha : a < 16) (hb : b < 16) :
    projE (rmfeProject.getD i 0) (embP a * embP b) = if i = a ∧ a = b then 1 else 0 := by
  rw [embP, embP, ← polyOfBits_mulGF2]
  unfold projE
  simp_rw [coeff_polyOfBits]
  have h : ∀ c, (if (rmfeProject.getD i 0).testBit c then
      bitE ((mulGF2 (bitsFrom (rmfeEmbed.getD a 0) 24) (bitsFrom (rmfeEmbed.getD b 0) 24)).getD
        c false) else 0) =
      bitE ((rmfeProject.getD i 0).testBit c &&
        (mulGF2 (bitsFrom (rmfeEmbed.getD a 0) 24) (bitsFrom (rmfeEmbed.getD b 0) 24)).getD
          c false) := by
    intro c
    cases (rmfeProject.getD i 0).testBit c <;> simp
  simp_rw [h]
  rw [sum_bitE_xor]
  have := rmfeOk_at ha hb hi
  unfold parityL at this
  rw [this]
  by_cases h2 : a = b
  · subst h2
    by_cases h1 : i = a
    · subst h1; simp
    · have h3 : (i == a) = false := by simpa using h1
      simp [h3, h1]
  · have : (a == b) = false := by simpa using h2
    simp [this, h2]

/-- **Bilinearity**: the projection to bit `i` of a product of two combinations of the
embeddings is the product of their `i`-th weights. -/
theorem projE_bilin {i : ℕ} (hi : i < 16) (u v : ℕ → E) :
    projE (rmfeProject.getD i 0)
      ((∑ a ∈ range 16, C (u a) * embP a) * (∑ b ∈ range 16, C (v b) * embP b)) = u i * v i := by
  rw [Finset.sum_mul_sum, projE_sum]
  have h : ∀ a ∈ range 16, projE (rmfeProject.getD i 0)
      (∑ b ∈ range 16, C (u a) * embP a * (C (v b) * embP b)) =
        if a = i then u i * v i else 0 := by
    intro a ha
    rw [projE_sum]
    have h2 : ∀ b ∈ range 16, projE (rmfeProject.getD i 0) (C (u a) * embP a * (C (v b) * embP b)) =
        u a * v b * (if i = a ∧ a = b then 1 else 0) := by
      intro b hb
      rw [show C (u a) * embP a * (C (v b) * embP b) = C (u a * v b) * (embP a * embP b) by
        rw [C_mul]; ring, projE_C_mul, projE_embP_mul hi (Finset.mem_range.1 ha)
          (Finset.mem_range.1 hb)]
    rw [Finset.sum_congr rfl h2]
    by_cases hai : a = i
    · subst hai
      rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [Ne.symm hb]) (fun h ↦ absurd ha h)]
      simp
    · rw [ite_eq_right hai]
      exact Finset.sum_eq_zero fun b _ ↦ by simp [Ne.symm hai]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (range 16) i, ite_eq_left (Finset.mem_range.2 hi)]

/-! ## The verifier's sums -/

theorem sumE_filterMap_range (n : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → E) :
    sumE ((List.range n).filterMap fun b ↦ if p b then some (f b) else none) =
      ∑ b ∈ range n, if p b then f b else 0 := by
  rw [sumE_eq_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.sum_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem powersFrom_getD (acc base : E) : ∀ (n b : ℕ), b < n →
    (powersFrom acc base n).getD b 0 = acc * base ^ b
  | n + 1, 0, _ => by simp [powersFrom]
  | n + 1, b + 1, h => by
    rw [powersFrom, List.getD_cons_succ, powersFrom_getD _ base n b (by omega), pow_succ]
    ring

theorem powers_getD (base : E) {n b : ℕ} (h : b < n) : (powers base n).getD b 0 = base ^ b := by
  rw [powers, powersFrom_getD 1 base n b h, one_mul]

theorem embP_eval (a : ℕ) (s : E) :
    (embP a).eval s = ∑ b ∈ range 24, if (rmfeEmbed.getD a 0).testBit b then s ^ b else 0 := by
  rw [eval_eq_sum_range' (n := 24) (by have := embP_natDegree a; omega)]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [embP_coeff, ite_eq_left (Finset.mem_range.1 hb)]
  cases (rmfeEmbed.getD a 0).testBit b <;> simp

theorem keccakInstanceWeights_length (s : E) : (keccakInstanceWeights s).length = 16 := by
  simp [keccakInstanceWeights, rmfeEmbed_length]

/-- **The instance weights at `s`** are the embeddings' values there, `emb_a(s)`. -/
theorem keccakInstanceWeights_getD (s : E) {a : ℕ} (ha : a < 16) :
    (keccakInstanceWeights s).getD a 0 = (embP a).eval s := by
  have hl : a < rmfeEmbed.length := by rw [rmfeEmbed_length]; exact ha
  rw [embP_eval, keccakInstanceWeights, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hl, List.getD_eq_getElem _ 0 hl]
  simp only [Option.map_some, Option.getD_some]
  rw [sumE_filterMap_range, show embedBits = 24 from rfl]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [powers_getD s (Finset.mem_range.1 hb)]

theorem sumE_zip_filterMap (p : ℕ → Prop) [DecidablePred p] :
    ∀ (l₁ : List E) (l₂ : List ℕ), l₁.length = l₂.length →
      sumE ((List.zip l₁ l₂).filterMap fun x ↦ if p x.2 then some x.1 else none) =
        ∑ i ∈ range l₁.length, if p (l₂.getD i 0) then l₁.getD i 0 else 0
  | [], [], _ => by simp [sumE]
  | x :: l₁, y :: l₂, h => by
    rw [List.zip_cons_cons, List.length_cons, Finset.sum_range_succ']
    have ih := sumE_zip_filterMap p l₁ l₂ (by simpa using h)
    rw [sumE_eq_sum] at ih ⊢
    by_cases hp : p y
    · simp only [List.filterMap_cons, hp, ite_true, List.sum_cons, ih, List.getD_cons_succ,
        List.getD_cons_zero]
      ring
    · simp only [List.filterMap_cons, hp, ite_false, ih, List.getD_cons_succ, List.getD_cons_zero,
        add_zero]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **The verifier's projected value** (`keccak.rs:125-132`): `Σ_c (Σ_{i ∋ c} μ_i) · G_c` is
`Σ_i μ_i · projE_i(G)`, for coefficients `G_c = product[c]`. -/
theorem projected_eq (mu product : List E) (hmu : mu.length = 16) (G : E[X])
    (hG : ∀ c < 47, product.getD c 0 = G.coeff c) :
    sumE ((List.range productBits).map fun c ↦
      sumE ((List.zip mu rmfeProject).filterMap fun (m, mask) ↦
        if mask.testBit c then some m else none) * product.getD c 0) =
      ∑ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) G := by
  rw [sumE_eq_sum, list_sum_range]
  have h : ∀ c ∈ range productBits, sumE ((List.zip mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0 =
        ∑ i ∈ range 16, mu.getD i 0 * (if (rmfeProject.getD i 0).testBit c then G.coeff c else 0) := by
    intro c hc
    have e : (fun (x : E × ℕ) ↦ match x with | (m, mask) => if mask.testBit c then some m else none) =
        fun x ↦ if x.2.testBit c then some x.1 else none := by
      funext x; rfl
    rw [e, sumE_zip_filterMap (fun mask ↦ mask.testBit c) mu rmfeProject
      (by rw [hmu, rmfeProject_length]), hmu, Finset.sum_mul, hG c (Finset.mem_range.1 hc)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [projE, Finset.mul_sum]
  rfl

end
end LeanVM.Protocol.KeccakGkr
