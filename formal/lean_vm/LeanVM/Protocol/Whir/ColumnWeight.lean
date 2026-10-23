/-
  LeanVM.Protocol.Whir.ColumnWeight

  The column weights of leanVM's binary Reed-Solomon code: a codeword entry is the inner product
  of the message with a tensor weight, whose multilinear extension is a `κ`-factor product; and the
  pinned Python verifier's batched query weight, transcribed and proved equal to the sum of those
  extensions.
-/

module

public import LeanVM.Protocol.Whir.NovelBasis
public import LeanVM.Protocol.ToArkLib.InnerProduct
public import LeanVM.Protocol.ToCompPoly.Multilinear

/-!
# Column weights

Two parts, both against leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`.

**Annex D**, Lemma `lem:colweight` (`doc/leanvm/body/d-novel-basis.tex:99-117`; in
Annex B until `127510d1`): for `x ∈ D_{κ,R}` the weight
`W_x(u) = ∏_i Ŵ_i(x)^{u_i}` (`colWeight`) satisfies

* `Enc_{κ,R}(g)[x] = ⟨W_x, g⟩ = Σ_u W_x(u)·g(u)` (`enc_eq_sum_colWeight`, for `κ ≤ 64`), and
* `mle(W_x)(r) = ∏_{i<κ} ((1 + r_i) + r_i·Ŵ_i(x))` (`eval₂Mle_colWeightTable`), where
  `colWeightTable κ x` is `W_x` as CompPoly's value table (bit `i` of the index is `u_i`) and the
  extension is `CMlPolynomialEval.eval₂Mle` into `E`, the one `answer_eqWeight` speaks of.

`colWeightE κ x` packages the two as a `Weight E κ` of the inner-product interface
(`LeanVM.Protocol.ToArkLib.InnerProduct`), whose evaluator is the product; `enc_eq_pair` reads
a codeword entry as `Weight.pair` against the message table `msgTable g`.

**The pinned Python verifier**, `python-verifier/verifier.py:964-992`:
`subspaceRoots` transcribes `_subspace_roots` and `inducedWeight` transcribes `_induced_weight`,
line by line: the roots `W_i(e_i)` by the layer recurrence `value ← value² + root·value`, their
inverses (zero kept as zero), and per query the running product
`product ← product·(1 + p_i·(1 + basis·inverse_i))` with `basis ← basis² + root_i·basis` starting
from `basis = E(query)`, the element whose `K`-limb `0` has bits `query`, i.e. `x_query`. The
Python's `require` on the point's length and `zip(..., strict=True)` on the queries and their
weights are the `none` branch.

* `subspaceRoots_eq`: `_subspace_roots(n)` is `[W_0(e_0), …, W_n(e_n)]`;
* `inducedWeight_eq`: on well-formed input, `_induced_weight(n, qs, ws, p)` is
  `Σ_q w_q·mle(W_{x_q})(p)`. In characteristic two the Python's factor `1 + p(1 + Ŵ)` is the
  Annex's `(1 + p) + p·Ŵ`.

## Wrong readings excluded

* The Python builds `E(2**i)` and `E(query)`, which raise on integers `≥ 2^64`; the Lean reads
  them with `K.ofBits`, which reduces modulo `2^64`. The verifier only calls these with
  `message_log ≤ 28` and queries below the block length, where the two agree.
* `Ŵ_i` is evaluated through the *unnormalized* recurrence and one inverse per coordinate; the
  recurrence is Annex Lemma `lem:subspace` (i) evaluated (`vanishingAt_succ`), the same update as
  the Rust `next_s` (`crates/pcs/src/ntt.rs`, `crates/pcs/src/whir_induce.rs`).
* `mle(W_x)` is the multilinear extension of the weight over the *message* cube `{0,1}^κ`, not
  over the domain.
-/

namespace LeanVM.Protocol.Whir

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-! ## The column weight -/

/-- The column weight `W_x(u) = ∏_i Ŵ_i(x)^{u_i}`. -/
def colWeight {κ : ℕ} (x : K) (u : Fin κ → Bool) : K :=
  ∏ i : Fin κ, if u i then normVanishingAt i x else 1

/-- Lemma `lem:colweight`, first identity: `Enc_{κ,R}(g)[x_v] = Σ_u W_{x_v}(u)·g(u)`. -/
theorem enc_eq_sum_colWeight {κ : ℕ} (R : ℕ) (hκ : κ ≤ 64) (g : (Fin κ → Bool) → E)
    (v : Fin (2 ^ (κ + R))) :
    enc κ R g v = ∑ u, ofK (colWeight (K.ofBits v) u) * g u := by
  rw [enc_apply]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [novelAt_bitsToNat hκ, colWeight, mul_comm]

/-- `W_x` as a value table on `κ` variables: entry `j` is `W_x` at the cube point with bits
`j`, bit `0` first. -/
def colWeightTable (κ : ℕ) (x : K) : CMlPolynomialEval K κ :=
  Vector.ofFn fun j ↦ colWeight x ((bitsEquiv κ).symm j)

/-- A message as a value table on `κ` variables. -/
def msgTable {κ : ℕ} (g : (Fin κ → Bool) → E) : CMlPolynomialEval E κ :=
  Vector.ofFn fun j ↦ g ((bitsEquiv κ).symm j)

/-- Lemma `lem:colweight`, second identity: `mle(W_x)(r) = ∏_{i<κ} ((1 + r_i) + r_i·Ŵ_i(x))`. -/
theorem eval₂Mle_colWeightTable (κ : ℕ) (x : K) (r : Vector E κ) :
    eval₂Mle (colWeightTable κ x) (algebraMap K E) r =
      ∏ i : Fin κ, ((1 + r[i]) + r[i] * ofK (normVanishingAt i x)) := by
  set f : Fin κ → Bool → E := fun i b ↦ if b then r[i] * ofK (normVanishingAt i x) else 1 + r[i]
  have hterm : ∀ j : Fin (2 ^ κ),
      (map (algebraMap K E) (colWeightTable κ x))[j] * (lagrangeBasis r)[j] =
        ∏ i : Fin κ, f i ((bitsEquiv κ).symm j i) := by
    intro j
    simp only [Fin.getElem_fin]
    rw [lagrangeBasis_getElem_nat r j.isLt]
    simp only [map, colWeightTable, colWeight, Vector.getElem_map, Vector.getElem_ofFn, map_prod,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [bitsEquiv_symm_apply]
    simp only [f, CharTwo.sub_eq_add]
    split
    · rw [mul_comm]
      rfl
    · rw [map_one, one_mul]
  rw [eval₂Mle, evalMle_eq_sum, Finset.sum_congr rfl fun j _ ↦ hterm j,
    Equiv.sum_comp (bitsEquiv κ).symm (fun u ↦ ∏ i, f i (u i)), ← Fintype.prod_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [f, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  ring

/-- `W_x` as a weight of the inner-product interface: its cube values, and the product as the
evaluator of its extension. -/
def colWeightE (κ : ℕ) (x : K) : Weight E κ where
  onCube := map (algebraMap K E) (colWeightTable κ x)
  mle r := ∏ i : Fin κ, ((1 + r[i]) + r[i] * ofK (normVanishingAt i x))
  mle_eq r := (eval₂Mle_colWeightTable κ x r).symm

/-- A codeword entry is the inner product of the column weight with the message table. -/
theorem enc_eq_pair {κ : ℕ} (R : ℕ) (hκ : κ ≤ 64) (g : (Fin κ → Bool) → E)
    (v : Fin (2 ^ (κ + R))) :
    enc κ R g v = (colWeightE κ (K.ofBits v)).pair (RingHom.id E) (msgTable g) := by
  rw [enc_eq_sum_colWeight R hκ, Weight.pair,
    ← Equiv.sum_comp (bitsEquiv κ).symm (fun u ↦ ofK (colWeight (K.ofBits v) u) * g u)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [colWeightE, map, colWeightTable, msgTable]

/-! ## The Python verifier's induced weight -/

/-- `_subspace_roots(log_n)` (`verifier.py:964-970`):

```python
roots = [ONE]
layer = [E(2**i) for i in range(1, log_n + 1)]
for _ in range(log_n):
    layer = [value**2 + roots[-1] * value for value in layer]
    roots.append(layer.pop(0))
return roots
``` -/
def subspaceRoots (logN : ℕ) : List E :=
  loop logN [1] ((List.range' 1 logN).map fun i ↦ ofK (K.ofBits (2 ^ i)))
where
  /-- The `for` loop: `k` iterations remain. -/
  loop : ℕ → List E → List E → List E
    | 0, roots, _ => roots
    | k + 1, roots, layer =>
      let layer := layer.map fun value ↦ value ^ 2 + roots.getLastD 0 * value
      loop k (roots ++ [layer.headD 0]) layer.tail

/-- `_induced_weight(message_log, queries, query_weights, point)` (`verifier.py:973-992`):

```python
require(len(point) == message_log, "bad induced-basis dimensions")
roots = _subspace_roots(message_log)
inverses = [value.inv() if value else ZERO for value in roots]
total = ZERO
for weight, query in zip(query_weights, queries, strict=True):
    basis = E(query)
    product = weight
    for coordinate, challenge in enumerate(point):
        product *= ONE + challenge * (ONE + basis * inverses[coordinate])
        basis = basis**2 + roots[coordinate] * basis
    total += product
return total
```

A failed `require` or a length mismatch in the strict `zip` is `none`. -/
def inducedWeight (messageLog : ℕ) (queries : List ℕ) (queryWeights : List E)
    (point : List E) : Option E :=
  if point.length = messageLog ∧ queryWeights.length = queries.length then
    let roots := subspaceRoots messageLog
    let inverses := roots.map fun value ↦ if value = 0 then 0 else value⁻¹
    some <| (queryWeights.zip queries).foldl (fun total wq ↦
      total + (point.zipIdx.foldl (fun pb cc ↦
          (pb.1 * (1 + cc.1 * (1 + pb.2 * inverses.getD cc.2 0)),
            pb.2 ^ 2 + roots.getD cc.2 0 * pb.2))
        (wq.1, ofK (K.ofBits wq.2))).1) 0
  else none

/-! ## Correctness of the transcription -/

/-- The root `W_i(e_i)`, in `E`. -/
private abbrev root (i : ℕ) : E := ofK (vanishingAt i (basisVec i))

/-- `ofK` preserves powers. -/
private theorem ofK_pow (a : K) (m : ℕ) : ofK (a ^ m) = ofK a ^ m := map_pow (algebraMap K E) a m

/-- `ofK` preserves inverses. -/
private theorem ofK_inv (a : K) : ofK a⁻¹ = (ofK a)⁻¹ := map_inv₀ (algebraMap K E) a

/-- `W_0` is the identity. -/
private theorem vanishingAt_zero_left (a : K) : vanishingAt 0 a = a := by
  simp [vanishingAt]

/-- The loop invariant of `_subspace_roots`: after `j` iterations the roots are
`W_0(e_0), …, W_j(e_j)` and the layer is `W_j(e_{j+1}), …`. -/
private theorem subspaceRoots_loop (k j : ℕ) :
    subspaceRoots.loop k ((List.range (j + 1)).map root)
        ((List.range' (j + 1) k).map fun c ↦ ofK (vanishingAt j (basisVec c))) =
      (List.range (j + k + 1)).map root := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    rw [subspaceRoots.loop, List.range'_succ]
    have hlast : ((List.range (j + 1)).map root).getLastD 0 = root j := by
      rw [List.range_succ, List.map_append, List.map_singleton, List.getLastD_concat]
    have hstep : ∀ c, ofK (vanishingAt j (basisVec c)) ^ 2 +
        root j * ofK (vanishingAt j (basisVec c)) = ofK (vanishingAt (j + 1) (basisVec c)) := by
      intro c
      rw [vanishingAt_succ, ofK_add, ofK_mul, ofK_pow]
    simp only [hlast, List.map_cons, List.map_map, Function.comp_def, hstep, List.headD_cons,
      List.tail_cons]
    have h := ih (j + 1)
    rw [show j + 1 + k + 1 = j + (k + 1) + 1 by omega] at h
    rw [← h, List.range_succ (n := j + 1), List.map_append, List.map_singleton]

/-- `_subspace_roots(n) = [W_0(e_0), …, W_n(e_n)]`. -/
theorem subspaceRoots_eq (n : ℕ) :
    subspaceRoots n = (List.range (n + 1)).map fun i ↦ ofK (vanishingAt i (basisVec i)) := by
  have h := subspaceRoots_loop n 0
  simp only [Nat.zero_add] at h
  change _ = (List.range (n + 1)).map root
  rw [← h, subspaceRoots]
  congr 1
  refine List.map_congr_left fun c _ ↦ ?_
  rw [vanishingAt_zero_left, basisVec]

/-- The inner loop of `_induced_weight`: after the coordinates `l`, starting at coordinate `s`
with `basis = W_s(x)`, the product has gained `∏ (1 + p_c·(1 + W_c(x)·W_c(e_c)⁻¹))` and the
basis is `W_{s+|l|}(x)`. -/
private theorem inner_fold (roots inverses : List E) (x : K) (l : List E) (s : ℕ) (p : E)
    (hr : ∀ c, s ≤ c → c < s + l.length → roots.getD c 0 = root c)
    (hi : ∀ c, s ≤ c → c < s + l.length → inverses.getD c 0 = (root c)⁻¹) :
    (l.zipIdx s).foldl (fun pb cc ↦
        (pb.1 * (1 + cc.1 * (1 + pb.2 * inverses.getD cc.2 0)),
          pb.2 ^ 2 + roots.getD cc.2 0 * pb.2)) (p, ofK (vanishingAt s x)) =
      (p * ∏ i : Fin l.length, ((1 + l[i]) + l[i] * ofK (normVanishingAt (s + i) x)),
        ofK (vanishingAt (s + l.length) x)) := by
  induction l generalizing s p with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.foldl_cons]
    have hs : s < s + (a :: l).length := by simp
    simp only [hr s le_rfl hs, hi s le_rfl hs]
    have hW : ofK (vanishingAt s x) ^ 2 + root s * ofK (vanishingAt s x) =
        ofK (vanishingAt (s + 1) x) := by
      rw [vanishingAt_succ, ofK_add, ofK_mul, ofK_pow]
    rw [hW, ih (s + 1) _ (fun c h1 h2 ↦ hr c (by omega) (by simp; omega))
      (fun c h1 h2 ↦ hi c (by omega) (by simp; omega))]
    have hn : ofK (vanishingAt s x) * (root s)⁻¹ = ofK (normVanishingAt s x) := by
      rw [normVanishingAt, ofK_mul, ofK_inv]
    refine Prod.ext ?_ ?_
    · change _ * _ * _ = p * ∏ i : Fin (l.length + 1), _
      rw [Fin.prod_univ_succ, hn]
      have hprod : ∏ i : Fin l.length, (1 + l[i] + l[i] * ofK (normVanishingAt (s + 1 + i) x)) =
          ∏ i : Fin l.length, (1 + (a :: l)[(i.succ : ℕ)] +
            (a :: l)[(i.succ : ℕ)] * ofK (normVanishingAt (s + (i.succ : ℕ)) x)) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        simp only [Fin.val_succ, List.getElem_cons_succ, Fin.getElem_fin]
        rw [show s + 1 + (i : ℕ) = s + ((i : ℕ) + 1) by omega]
      rw [hprod]
      simp only [Fin.val_zero, add_zero, List.getElem_cons_zero, Fin.getElem_fin]
      ring
    · change ofK (vanishingAt (s + 1 + l.length) x) = ofK (vanishingAt (s + (l.length + 1)) x)
      rw [show s + 1 + l.length = s + (l.length + 1) by omega]

/-- The outer loop of `_induced_weight` is a sum. -/
private theorem foldl_add_eq_sum {α : Type*} (f : α → E) (t : E)
    (m : List α) : m.foldl (fun total a ↦ total + f a) t = t + (m.map f).sum := by
  induction m generalizing t with
  | nil => simp
  | cons a m ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

/-- The pinned Python verifier's `_induced_weight` computes `Σ_q w_q·mle(W_{x_q})(p)`: the batched
column weights of `lem:colweight` at the point. -/
theorem inducedWeight_eq (n : ℕ) (queries : List ℕ) (queryWeights : List E) (point : Vector E n)
    (h : queryWeights.length = queries.length) :
    inducedWeight n queries queryWeights point.toList =
      some ((queryWeights.zip queries).map fun wq ↦
        wq.1 * eval₂Mle (colWeightTable n (K.ofBits wq.2)) (algebraMap K E) point).sum := by
  simp only [inducedWeight, Vector.length_toList, h, and_self, ↓reduceIte]
  rw [foldl_add_eq_sum, zero_add]
  congr 2
  refine List.map_congr_left fun wq _ ↦ ?_
  have hroots : ∀ c, c < n + 1 → (subspaceRoots n).getD c 0 = root c := by
    intro c hc
    rw [List.getD_eq_getElem _ _ (by rw [subspaceRoots_eq]; simpa using hc)]
    simp [subspaceRoots_eq, root]
  have hb0 : ofK (K.ofBits wq.2) = ofK (vanishingAt 0 (K.ofBits wq.2)) := by
    rw [vanishingAt_zero_left]
  have hlen : point.toList.length = n := by simp
  rw [hb0, inner_fold _ _ _ _ 0 _ (fun c _ h2 ↦ hroots c (by omega)) ?inv,
    eval₂Mle_colWeightTable]
  · dsimp only
    rw [← Fin.prod_congr' _ hlen]
    refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
    simp [Vector.getElem_toList]
  · intro c _ h2
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, subspaceRoots_eq]; simp; omega)]
    rw [List.getElem_map]
    have := hroots c (by omega)
    rw [List.getD_eq_getElem _ _ (by rw [subspaceRoots_eq]; simp; omega)] at this
    rw [this]
    split
    · rename_i h0
      rw [h0, inv_zero]
    · rfl

end
end LeanVM.Protocol.Whir
