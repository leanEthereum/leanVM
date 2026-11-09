/-
  LeanVM.Prover.GkrRound

  The executable GKR step's round polynomials and folds (`Statement/Prover/Gkr.lean`) are the
  specification's: a round's coefficients evaluate as `stepClaim`, a fold keeps the folded layers
  the layers' extensions at the challenges bound so far.
-/

module

public import Statement.Prover.Gkr
public import LeanVM.Prover.Mle
public import LeanVM.Prover.Sumcheck
public import LeanVM.Protocol.EndToEnd.Complete.Gkr

/-!
# The GKR step's rounds

* `Script.AllRet`, `Corr.bind_allRet`, `allRet_sampleN`: a property of every result of a script,
  and the composition of `Corr` along a script whose results have it (the fresh coordinates of a
  step have `step` entries);
* `corr_sumcheckBy_lt`: the stateful sumcheck makes the specification's moves when the round's
  coefficients evaluate as the claim while coordinates remain (the variant of `corr_sumcheckBy`
  whose invariant need not hold after the last round's claim), and it draws one challenge per
  round;
* `polyEval_mulLine`, `polyEval_addScaled`, `foldLines`, `foldAdd`: coefficient lists;
* `multilinearEval_affine`: an extension is affine in any one coordinate;
* `TabInv`: a folded layer, entry `j + 2^h·b` the layer's extension at the child bits `j`, the
  challenges, the remaining bits `b`; `tabInv_init`, `tabInv_fold`, `toList_eq_child`;
* `gkrRound_eval`: **a round's coefficients evaluate as the specification's `stepClaim`**.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd.Complete Finset

@[expose] public section

/-! ## Results of a script -/

/-- Every result of the script satisfies `P`. -/
def Script.AllRet {α : Type} (P : α → Prop) : Script α → Prop
  | .ret a => P a
  | .send _ k => Script.AllRet P k
  | .sample k => ∀ c, Script.AllRet P (k c)
  | .grind k => Script.AllRet P k
  | .commit _ k => Script.AllRet P k
  | .query k => ∀ rows, Script.AllRet P (k rows)

theorem Script.AllRet.bind {α β : Type} {P : α → Prop} {Q : β → Prop} {f : α → Script β}
    (hk : ∀ a, P a → Script.AllRet Q (f a)) :
    ∀ H : Script α, Script.AllRet P H → Script.AllRet Q (H.bind f)
  | .ret a, h => hk a h
  | .send _ k, h => Script.AllRet.bind hk k h
  | .sample k, h => fun c ↦ Script.AllRet.bind hk (k c) (h c)
  | .grind k, h => Script.AllRet.bind hk k h
  | .commit _ k, h => Script.AllRet.bind hk k h
  | .query k, h => fun rows ↦ Script.AllRet.bind hk (k rows) (h rows)

/-- `n` challenges are `n`. -/
theorem allRet_sampleN : ∀ n : ℕ, Script.AllRet (fun y : List E ↦ y.length = n) (Script.sampleN n)
  | 0 => rfl
  | n + 1 => by
    show ∀ c, Script.AllRet _ ((Script.sampleN n).bind fun xs ↦ Script.ret (c :: xs))
    intro c
    exact Script.AllRet.bind (Q := fun y : List E ↦ y.length = n + 1)
      (f := fun xs ↦ Script.ret (c :: xs))
      (fun xs (hxs : xs.length = n) ↦ show (c :: xs).length = n + 1 by simp [hxs]) _
      (allRet_sampleN n)

/-- The same script, then continuations related at every result it can return. -/
theorem Corr.bind_allRet {α γ δ : Type} {P : α → Prop} {S : γ → δ → Prop} {f : α → Script γ}
    {g : α → Script δ} (hk : ∀ a, P a → Corr S (f a) (g a)) :
    ∀ H : Script α, Script.AllRet P H → Corr S (H.bind f) (H.bind g)
  | .ret a, h => hk a h
  | .send _ k, h => ⟨rfl, Corr.bind_allRet hk k h⟩
  | .sample k, h => fun c ↦ Corr.bind_allRet hk (k c) (h c)
  | .grind k, h => Corr.bind_allRet hk k h
  | .commit _ k, h => ⟨rfl, Corr.bind_allRet hk k h⟩
  | .query k, h => fun rows ↦ Corr.bind_allRet hk (k rows) (h rows)

/-! ## The stateful sumcheck, while coordinates remain -/

/-- **The stateful sumcheck makes the specification's moves** for `N` rounds in all: given an
invariant under which, while rounds remain, the state's `count` coefficients evaluate as the
round's claim, and which each fold keeps; it draws one challenge per round. -/
theorem corr_sumcheckBy_lt {σ : Type} (count : ℕ) (hc : 1 ≤ count) (hc' : count ≤ 2 ^ 192)
    (claimOf : List E → E) (round : σ → List E) (fold : σ → E → σ) (Inv : List E → σ → Prop)
    (N : ℕ)
    (hround : ∀ pre st, Inv pre st → pre.length < N →
      (round st).length = count ∧ ∀ x, polyEval (round st) x = claimOf (pre ++ [x]))
    (hfold : ∀ pre st c, Inv pre st → pre.length < N → Inv (pre ++ [c]) (fold st c)) :
    ∀ (modes : List (Option E)) (pre : List E) (st : σ), Inv pre st →
      pre.length + modes.length = N →
      Corr (fun a b ↦ a.1 = b.1 ∧ a.1.length = modes.length ∧ Inv (pre ++ a.1) a.2)
        (sumcheckBy round fold modes st) (hSumcheck count claimOf modes pre)
  | [], pre, st, h, _ => by
    simp only [sumcheckBy, hSumcheck, Corr, List.append_nil]
    exact ⟨by simp, by simp, h⟩
  | mode :: modes, pre, st, h, hN => by
    have hlt : pre.length < N := by simp only [List.length_cons] at hN; omega
    obtain ⟨hlen, hev⟩ := hround pre st h hlt
    have hco : coeffsOf (count - 1) (fun x ↦ claimOf (pre ++ [x])) = round st :=
      coeffsOf_eq (by omega) (by omega) hev
    simp only [sumcheckBy, hSumcheck, hco, ← wire_eq]
    refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun c ↦ ?_
    refine Corr.bind (fun a b hab ↦ ?_) _ _
      (corr_sumcheckBy_lt count hc hc' claimOf round fold Inv N hround hfold modes (pre ++ [c])
        (fold st c) (hfold pre st c h hlt)
        (by simp only [List.length_append, List.length_cons, List.length_nil] at hN ⊢
            omega))
    obtain ⟨h1, h2, h3⟩ := hab
    simp only [Corr, List.append_assoc, List.singleton_append] at h3 ⊢
    exact ⟨by rw [h1], by simp [h2], h3⟩

/-! ## Coefficient lists -/

theorem polyEval_cons' (c : E) (l : List E) (x : E) : polyEval (c :: l) x = polyEval l x * x + c :=
  rfl

theorem polyEval_nil' (x : E) : polyEval [] x = 0 := rfl

theorem length_mulLineFrom (a₀ a₁ : E) :
    ∀ (prev : E) (P : List E), (mulLineFrom a₀ a₁ prev P).length = P.length + 1
  | _, [] => rfl
  | _, _ :: ps => by simp [mulLineFrom, length_mulLineFrom a₀ a₁ _ ps]

theorem polyEval_mulLineFrom (a₀ a₁ x : E) : ∀ (prev : E) (P : List E),
    polyEval (mulLineFrom a₀ a₁ prev P) x = (a₀ + a₁ * x) * polyEval P x + a₁ * prev
  | prev, [] => by simp only [mulLineFrom, polyEval_cons', polyEval_nil']; ring
  | prev, p :: ps => by
    simp only [mulLineFrom, polyEval_cons', polyEval_mulLineFrom a₀ a₁ x p ps]; ring

theorem length_mulLine (a₀ a₁ : E) (P : List E) : (mulLine a₀ a₁ P).length = P.length + 1 :=
  length_mulLineFrom a₀ a₁ 0 P

/-- **A line times a polynomial.** -/
theorem polyEval_mulLine (a₀ a₁ x : E) (P : List E) :
    polyEval (mulLine a₀ a₁ P) x = (a₀ + a₁ * x) * polyEval P x := by
  rw [mulLine, polyEval_mulLineFrom]; ring

theorem length_addScaled (acc v : List E) (w : E) (h : acc.length = v.length) :
    (addScaled acc v w).length = acc.length := by
  simp [addScaled, h]

/-- **A polynomial plus a multiple of another**, of the same length. -/
theorem polyEval_addScaled (w x : E) : ∀ (acc v : List E), acc.length = v.length →
    polyEval (addScaled acc v w) x = polyEval acc x + w * polyEval v x
  | [], [], _ => by simp [addScaled, polyEval_nil']
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: acc, b :: v, h => by
    have ih := polyEval_addScaled w x acc v (by simpa using h)
    simp only [addScaled] at ih ⊢
    simp only [List.zipWith_cons_cons, polyEval_cons', ih]
    ring

theorem polyEval_replicate_zero (x : E) : ∀ n : ℕ, polyEval (List.replicate n 0) x = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, polyEval_cons', polyEval_replicate_zero x n]; ring

/-- **A product of lines**, expanded into coefficients. -/
theorem foldLines (lo hi : ℕ → E) (x : E) : ∀ n : ℕ,
    (Nat.fold n (fun j _ P ↦ mulLine (lo j) (lo j + hi j) P) [1]).length = n + 1 ∧
    polyEval (Nat.fold n (fun j _ P ↦ mulLine (lo j) (lo j + hi j) P) [1]) x =
      ∏ j ∈ range n, ((1 + x) * lo j + x * hi j)
  | 0 => by simp [polyEval_cons', polyEval_nil']
  | n + 1 => by
    obtain ⟨h1, h2⟩ := foldLines lo hi x n
    simp only [Nat.fold_succ]
    refine ⟨by rw [length_mulLine, h1], ?_⟩
    rw [polyEval_mulLine, h2, prod_range_succ]
    ring

/-- **A weighted sum of polynomials**, accumulated. -/
theorem foldAdd (v : ℕ → List E) (w : ℕ → E) (x : E) (N : ℕ) (hv : ∀ b, (v b).length = N)
    (acc₀ : List E) (h₀ : acc₀.length = N) : ∀ n : ℕ,
    (Nat.fold n (fun b _ acc ↦ addScaled acc (v b) (w b)) acc₀).length = N ∧
    polyEval (Nat.fold n (fun b _ acc ↦ addScaled acc (v b) (w b)) acc₀) x =
      polyEval acc₀ x + ∑ b ∈ range n, w b * polyEval (v b) x
  | 0 => by simp [h₀]
  | n + 1 => by
    obtain ⟨h1, h2⟩ := foldAdd v w x N hv acc₀ h₀ n
    simp only [Nat.fold_succ]
    refine ⟨by rw [length_addScaled _ _ _ (by rw [h1, hv]), h1], ?_⟩
    rw [polyEval_addScaled _ _ _ _ (by rw [h1, hv]), h2, sum_range_succ]
    ring

theorem length_lineProd (h : ℕ) (t : Array E) (b : ℕ) : (lineProd h t b).length = 2 ^ h + 1 :=
  (foldLines (fun j ↦ t.getD (j + 2 ^ (h + 1) * b) 0)
    (fun j ↦ t.getD (j + 2 ^ (h + 1) * b + 2 ^ h) 0) 0 (2 ^ h)).1

theorem polyEval_lineProd (h : ℕ) (t : Array E) (b : ℕ) (x : E) :
    polyEval (lineProd h t b) x = ∏ j ∈ range (2 ^ h),
      ((1 + x) * t.getD (j + 2 ^ (h + 1) * b) 0 + x * t.getD (j + 2 ^ (h + 1) * b + 2 ^ h) 0) :=
  (foldLines (fun j ↦ t.getD (j + 2 ^ (h + 1) * b) 0)
    (fun j ↦ t.getD (j + 2 ^ (h + 1) * b + 2 ^ h) 0) x (2 ^ h)).2

/-- The three trees' line products of a row, batched by the combiner. -/
theorem polyEval_rowPoly (h : ℕ) (st : GkrFold) (c : E) (b : ℕ) (x : E) :
    (addScaled (addScaled (lineProd h st.t₀ b) (lineProd h st.t₁ b) c) (lineProd h st.t₂ b)
      (c * c)).length = 2 ^ h + 1 ∧
    polyEval (addScaled (addScaled (lineProd h st.t₀ b) (lineProd h st.t₁ b) c)
      (lineProd h st.t₂ b) (c * c)) x =
      polyEval (lineProd h st.t₀ b) x + c * polyEval (lineProd h st.t₁ b) x +
        c * c * polyEval (lineProd h st.t₂ b) x := by
  have l0 := length_lineProd h st.t₀ b
  have l1 := length_lineProd h st.t₁ b
  have l2 := length_lineProd h st.t₂ b
  have la : (addScaled (lineProd h st.t₀ b) (lineProd h st.t₁ b) c).length = 2 ^ h + 1 := by
    rw [length_addScaled _ _ _ (by rw [l0, l1]), l0]
  refine ⟨by rw [length_addScaled _ _ _ (by rw [la, l2]), la], ?_⟩
  rw [polyEval_addScaled _ _ _ _ (by rw [la, l2]), polyEval_addScaled _ _ _ _ (by rw [l0, l1])]

theorem length_gkrRound (h : ℕ) (c : E) (st : GkrFold) : (gkrRound h c st).length = 2 ^ h + 1 :=
  (foldAdd _ _ 0 (2 ^ h + 1) (fun b ↦ (polyEval_rowPoly h st c b 0).1) _ (by simp) _).1

/-- A round's polynomial: the equality weights times the rows' batched line products. -/
theorem polyEval_gkrRound (h : ℕ) (c : E) (st : GkrFold) (x : E) :
    polyEval (gkrRound h c st) x =
      ∑ b ∈ range (eqTable st.rest.tail).size, (eqTable st.rest.tail).getD b 0 *
        (polyEval (lineProd h st.t₀ b) x + c * polyEval (lineProd h st.t₁ b) x +
          c * c * polyEval (lineProd h st.t₂ b) x) := by
  rw [gkrRound, (foldAdd _ _ x (2 ^ h + 1) (fun b ↦ (polyEval_rowPoly h st c b 0).1) _
    (by simp) _).2, polyEval_replicate_zero, zero_add]
  exact sum_congr rfl fun b _ ↦ by rw [(polyEval_rowPoly h st c b x).2]

/-! ## Extensions in one coordinate -/

/-- The equality weight is affine in any one coordinate of its second point. -/
theorem eqEval_affine (X : E) : ∀ (a u v : List E),
    eqEval a (u ++ X :: v) = (1 + X) * eqEval a (u ++ 0 :: v) + X * eqEval a (u ++ 1 :: v)
  | [], [], v => by
    simp only [eqEval, List.zipWith_nil_left, List.foldl_nil]
    linear_combination (-X) * two_eq_zero_E
  | a₀ :: a, [], v => by
    simp only [List.nil_append, eqEval_cons]
    linear_combination (-(X * (a₀ + 1) * eqEval a v)) * two_eq_zero_E
  | [], _ :: _, v => by
    simp only [eqEval, List.zipWith_nil_left, List.foldl_nil]
    linear_combination (-X) * two_eq_zero_E
  | a₀ :: a, u₀ :: u, v => by
    simp only [List.cons_append, eqEval_cons, eqEval_affine X a u v]
    ring

/-- **An extension is affine in any one coordinate.** -/
theorem multilinearEval_affine {C : List E} (u v : List E)
    (hC : C.length = 2 ^ (u.length + 1 + v.length)) (X : E) :
    multilinearEval C (u ++ X :: v) =
      (1 + X) * multilinearEval C (u ++ 0 :: v) + X * multilinearEval C (u ++ 1 :: v) := by
  have hl : ∀ Y : E, (u ++ Y :: v).length = u.length + 1 + v.length := fun Y ↦ by
    simp only [List.length_append, List.length_cons]; ring
  rw [multilinearEval_eq_sum _ C _ hC (hl X), multilinearEval_eq_sum _ C _ hC (hl 0),
    multilinearEval_eq_sum _ C _ hC (hl 1), mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [eqEval_affine]
  ring

/-! ## The folded layers -/

/-- **A folded layer**: `2^(h + r)` entries, entry `j + 2^h·b` the layer's extension at the child
bits `j`, the challenges `pre`, the remaining bits `b`. -/
def TabInv (C : List E) (T : Array E) (h : ℕ) (pre : List E) (r : ℕ) : Prop :=
  T.size = 2 ^ (h + r) ∧ ∀ j < 2 ^ h, ∀ b < 2 ^ r,
    T.getD (j + 2 ^ h * b) 0 = multilinearEval C (boolPoint h j ++ pre ++ boolPoint r b)

/-- The layer itself, before any challenge. -/
theorem tabInv_init {C : List E} {T : Array E} (hT : T.toList = C) {h m : ℕ}
    (hC : C.length = 2 ^ (h + m)) : TabInv C T h [] m := by
  refine ⟨by rw [← Array.length_toList, hT, hC], fun j hj b hb ↦ ?_⟩
  rw [getD_toList, hT, List.append_nil, ← boolPoint_add h m j b hj,
    multilinearEval_boolPoint hC (by rw [pow_add]; exact add_mul_lt hj hb)]

/-- Entries `j + 2^h·2b` and `j + 2^h·(2b+1)`: the next coordinate at `0` and `1`. -/
theorem tabInv_pair {C : List E} {T : Array E} {h r : ℕ} {pre : List E}
    (hI : TabInv C T h pre (r + 1)) {j b : ℕ} (hj : j < 2 ^ h) (hb : b < 2 ^ r) :
    T.getD (j + 2 ^ (h + 1) * b) 0 = multilinearEval C ((boolPoint h j ++ pre) ++ 0 ::
      boolPoint r b) ∧
    T.getD (j + 2 ^ (h + 1) * b + 2 ^ h) 0 = multilinearEval C ((boolPoint h j ++ pre) ++ 1 ::
      boolPoint r b) := by
  have e0 := hI.2 j hj (2 * b) (by rw [pow_succ]; omega)
  have e1 := hI.2 j hj (2 * b + 1) (by rw [pow_succ]; omega)
  rw [boolPoint_two_mul] at e0
  rw [boolPoint_two_mul_add_one] at e1
  refine ⟨?_, ?_⟩
  · rw [show j + 2 ^ (h + 1) * b = j + 2 ^ h * (2 * b) by ring, e0]
  · rw [show j + 2 ^ (h + 1) * b + 2 ^ h = j + 2 ^ h * (2 * b + 1) by ring, e1]

/-- **A fold binds the next coordinate.** -/
theorem tabInv_fold {C : List E} {T : Array E} {h r : ℕ} {pre : List E}
    (hC : C.length = 2 ^ (h + pre.length + 1 + r)) (hI : TabInv C T h pre (r + 1)) (c : E) :
    TabInv C (foldStride h c T) h (pre ++ [c]) r := by
  have hs := hI.1
  refine ⟨?_, fun j hj b hb ↦ ?_⟩
  · simp only [foldStride, Array.size_ofFn, hs]
    rw [show h + (r + 1) = h + r + 1 by ring, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  · have hlt : j + 2 ^ h * b < T.size / 2 := by
      rw [hs, show h + (r + 1) = h + r + 1 by ring, pow_succ, Nat.mul_div_cancel _ (by norm_num),
        pow_add]
      exact add_mul_lt hj hb
    have hmod : (j + 2 ^ h * b) % 2 ^ h = j := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    have hdiv : (j + 2 ^ h * b) / 2 ^ h = b := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hj, zero_add]
    rw [foldStride, getD_ofFn _ _ hlt]
    simp only [hmod, hdiv]
    obtain ⟨e0, e1⟩ := tabInv_pair hI hj hb
    rw [e0, e1, show boolPoint h j ++ (pre ++ [c]) ++ boolPoint r b =
      (boolPoint h j ++ pre) ++ c :: boolPoint r b by simp,
      multilinearEval_affine (boolPoint h j ++ pre) (boolPoint r b)
        (by rw [hC]; simp only [List.length_append, length_boolPoint]) c]

/-- **The fully folded layer is the children**: `C̃(j, x)` for every `j`. -/
theorem toList_eq_child {C : List E} {T : Array E} {h : ℕ} {x : List E}
    (hI : TabInv C T h x 0) : T.toList = child C h x := by
  have hs := hI.1
  apply List.ext_getElem (by simp [child, hs])
  intro j h1 h2
  have hj : j < 2 ^ h := by simpa [child] using h2
  have e := hI.2 j hj 0 (by norm_num)
  rw [mul_zero, add_zero, getD_toList, List.getD_eq_getElem _ _ h1] at e
  rw [e]
  simp [child]

/-! ## The round -/

/-- A product over a range, as a list. -/
theorem list_prod_map_range (f : ℕ → E) : ∀ n : ℕ,
    ((List.range n).map f).prod = ∏ j ∈ range n, f j
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, list_prod_map_range f n,
      prod_range_succ]
    simp

/-- A row's children product at the next challenge `x`: the product of its lines. -/
theorem prod_child_line {C : List E} {T : Array E} {h r : ℕ} {pre : List E}
    (hC : C.length = 2 ^ (h + pre.length + 1 + r)) (hI : TabInv C T h pre (r + 1)) {b : ℕ}
    (hb : b < 2 ^ r) (x : E) :
    (child C h (pre ++ [x] ++ boolPoint r b)).prod = ∏ j ∈ range (2 ^ h),
      ((1 + x) * T.getD (j + 2 ^ (h + 1) * b) 0 + x * T.getD (j + 2 ^ (h + 1) * b + 2 ^ h) 0) := by
  rw [child, list_prod_map_range]
  refine prod_congr rfl fun j hj ↦ ?_
  obtain ⟨e0, e1⟩ := tabInv_pair hI (mem_range.mp hj) hb
  rw [e0, e1, show boolPoint h j ++ (pre ++ [x] ++ boolPoint r b) =
      (boolPoint h j ++ pre) ++ x :: boolPoint r b by simp,
    multilinearEval_affine (boolPoint h j ++ pre) (boolPoint r b)
      (by rw [hC]; simp only [List.length_append, length_boolPoint]) x]

/-- **A round's coefficients evaluate as the specification's claim** `stepClaim`, at every
point, while a coordinate of `p` remains. -/
theorem gkrRound_eval {C₀ C₁ C₂ : List E} {h : ℕ} {p : List E} {c : E} {pre : List E}
    {st : GkrFold} (hrest : st.rest = p.drop pre.length)
    (hC₀ : C₀.length = 2 ^ (h + pre.length + 1 + (p.length - (pre.length + 1))))
    (hC₁ : C₁.length = 2 ^ (h + pre.length + 1 + (p.length - (pre.length + 1))))
    (hC₂ : C₂.length = 2 ^ (h + pre.length + 1 + (p.length - (pre.length + 1))))
    (hI₀ : TabInv C₀ st.t₀ h pre (p.length - (pre.length + 1) + 1))
    (hI₁ : TabInv C₁ st.t₁ h pre (p.length - (pre.length + 1) + 1))
    (hI₂ : TabInv C₂ st.t₂ h pre (p.length - (pre.length + 1) + 1)) (x : E) :
    polyEval (gkrRound h c st) x = stepClaim C₀ C₁ C₂ h p c (pre ++ [x]) := by
  have htail : st.rest.tail = p.drop (pre.length + 1) := by
    rw [hrest, List.tail_drop]
  have hsz : (eqTable st.rest.tail).size = 2 ^ (p.length - (pre.length + 1)) := by
    rw [size_eqTable, htail, List.length_drop]
  rw [polyEval_gkrRound, hsz, stepClaim]
  simp only [List.length_append, List.length_singleton]
  refine sum_congr rfl fun b hb ↦ ?_
  have hb' := mem_range.mp hb
  rw [getD_eqTable _ _ (by rw [htail, List.length_drop]; exact hb'), htail, List.length_drop,
    eqEval_comm, stepF, polyEval_three, prod_child_line hC₀ hI₀ hb' x,
    prod_child_line hC₁ hI₁ hb' x, prod_child_line hC₂ hI₂ hb' x, polyEval_lineProd,
    polyEval_lineProd, polyEval_lineProd]
  ring

end
end LeanVM.Prover
