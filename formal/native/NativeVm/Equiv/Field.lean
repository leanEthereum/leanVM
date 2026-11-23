module

public import NativeVm.Model.Field
public import LeanVM.Parameters.Field
public import Statement.LeanVmVerifier

/-!
# The model's field arithmetic is the statement's

Through `K.ofLane` and `EW.toE`: `kmul` is the product in `K` (`BF64.mul_eq_mulShift`), `mulX`
the product by `g`, `kpow` the power, `kinv` the inverse (`0 ↦ 0`, as `a^(2^64 - 2)`); `EW`'s sum and
product are `E`'s. Then each array helper of `NativeVm.Model` is the statement's function of the
same name on the elements' list (`toE_sumE`, `toList_map_eqKernel`, …).
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol

/-! ## `K` -/

theorem K_ofLane_xor (a b : UInt64) : K.ofLane (a ^^^ b) = K.ofLane a + K.ofLane b := (rfl)

@[simp] theorem K_ofLane_zero : K.ofLane 0 = 0 := (rfl)

@[simp] theorem K_ofLane_one : K.ofLane 1 = 1 := (rfl)

@[simp] theorem K_ofLane_lane (a : K) : K.ofLane a.lane = a := (rfl)

@[simp] theorem K_lane_ofLane (w : UInt64) : (K.ofLane w).lane = w := (rfl)

theorem K_ofLane_injective : Function.Injective K.ofLane := fun _ _ h ↦ congrArg K.lane h

theorem K_ofLane_two : K.ofLane 2 = g := (rfl)

theorem K_ofLane_kmul (a b : UInt64) : K.ofLane (kmul a b) = K.ofLane a * K.ofLane b := by
  show _ = BF64.mul _ _
  rw [BF64.mul_eq_mulShift]
  rfl

/-- `mulX t` is `kmul 2 t`, whose loop runs two rounds. -/
theorem mulX_eq_kmul (t : UInt64) : mulX t = kmul 2 t := by
  rw [kmul, BF64.mulShift, ite_eq_right (by decide), BF64.mulShift, ite_eq_right (by decide),
    BF64.mulShift, ite_eq_left (by decide)]
  simp only [BF64.reduceWords, BF64.tailLow, BF64.tailHigh, mulX]
  have h2 : (t >>> 63).toNat < 2 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have := t.toNat_lt
    exact Nat.div_lt_of_lt_mul (by simpa using this)
  generalize t >>> 63 = h at h2 ⊢
  generalize t <<< 1 = u
  have : h = 0 ∨ h = 1 := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h3 | h3
    · left; exact UInt64.toNat_inj.mp (by simpa using h3)
    · right; exact UInt64.toNat_inj.mp (by simpa using h3)
  rcases this with rfl | rfl <;> (apply UInt64.toBitVec_inj.mp; simp)

theorem K_ofLane_mulX (t : UInt64) : K.ofLane (mulX t) = g * K.ofLane t := by
  rw [mulX_eq_kmul, K_ofLane_kmul]
  rfl

/-- The loop of `kpow` is `acc · base^n` while `n` has at most `fuel` bits. -/
theorem K_ofLane_kpowAux : ∀ (fuel : ℕ) (b acc : UInt64) (n : ℕ), n < 2 ^ fuel →
    K.ofLane (kpowAux fuel b acc n) = K.ofLane acc * K.ofLane b ^ n
  | 0, b, acc, n, h => by
    obtain rfl : n = 0 := by simpa using h
    simp [kpowAux]
  | fuel + 1, b, acc, n, h => by
    rw [kpowAux]
    split
    · subst ‹n = 0›
      simp
    · rw [K_ofLane_kpowAux fuel _ _ (n / 2) (by rw [pow_succ] at h; omega), K_ofLane_kmul]
      split
      · have hn : n = 2 * (n / 2) + 1 := by omega
        conv_rhs => rw [hn]
        rw [K_ofLane_kmul, pow_succ, pow_mul, sq]
        ring
      · have hn : n = 2 * (n / 2) := by omega
        conv_rhs => rw [hn]
        rw [pow_mul, sq]

theorem K_ofLane_kpow (a : UInt64) (n : ℕ) : K.ofLane (kpow a n) = K.ofLane a ^ n := by
  rw [kpow, K_ofLane_kpowAux _ _ _ _ Nat.lt_log2_self, K_ofLane_one, one_mul]

/-- `a^(2^64 - 2) = a⁻¹` in `K`, `0` included. -/
theorem K_pow_card_sub_two (a : K) : a ^ (2 ^ 64 - 2) = a⁻¹ := by
  by_cases ha : a = 0
  · subst ha
    rw [inv_zero, zero_pow (by norm_num)]
  · let := Fintype.ofFinite K
    have h1 := FiniteField.pow_card_sub_one_eq_one a ha
    rw [show Fintype.card K = 2 ^ 64 from BF64.card_bf64] at h1
    have h2 : a ^ (2 ^ 64 - 2) * a = 1 := by
      rw [← pow_succ]
      exact h1
    exact eq_inv_of_mul_eq_one_left h2

theorem K_ofLane_kinv (a : UInt64) : K.ofLane (kinv a) = (K.ofLane a)⁻¹ := by
  rw [kinv, K_ofLane_kpow, K_pow_card_sub_two]

theorem K_ofLane_gpowK (n : ℕ) : K.ofLane (gpowK n) = g ^ n := by
  rw [gpowK, K_ofLane_kpow, K_ofLane_two]

/-! ## `E` -/

namespace EW

theorem toE_mk (c0 c1 : UInt64) : (EW.mk c0 c1).toE = E.ofLimbs (K.ofLane c0) (K.ofLane c1) := rfl

@[simp] theorem toE_add (a b : EW) : (a + b).toE = a.toE + b.toE := by
  show E.ofLimbs (K.ofLane (a.c0 ^^^ b.c0)) (K.ofLane (a.c1 ^^^ b.c1)) = _
  rw [K_ofLane_xor, K_ofLane_xor, EW.toE, EW.toE, add_limbs]

@[simp] theorem toE_mul (a b : EW) : (a * b).toE = a.toE * b.toE := by
  show E.ofLimbs (K.ofLane (kmul a.c0 b.c0 ^^^ kmul a.c1 b.c1))
    (K.ofLane (kmul a.c0 b.c1 ^^^ kmul a.c1 b.c0 ^^^ mulX (kmul a.c1 b.c1))) = _
  rw [EW.toE, EW.toE, mul_limbs]
  simp only [K_ofLane_xor, K_ofLane_kmul, K_ofLane_mulX]

@[simp] theorem toE_ofK (a : UInt64) : (EW.ofK a).toE = ofK (K.ofLane a) :=
  (ofK_eq_ofLimbs _).symm

@[simp] theorem toE_zero : (0 : EW).toE = 0 := by
  show (EW.ofK 0).toE = 0
  rw [toE_ofK, K_ofLane_zero]
  exact map_zero (algebraMap K E)

@[simp] theorem toE_one : (1 : EW).toE = 1 := by
  show (EW.ofK 1).toE = 1
  rw [toE_ofK, K_ofLane_one]
  exact map_one (algebraMap K E)

@[simp] theorem toE_ofNat (n : ℕ) : (EW.ofNat n).toE = Verifier.eOfNat n := by
  show (EW.ofK n.toUInt64).toE = _
  rw [toE_ofK]
  rfl

@[simp] theorem toE_ofE (x : E) : (EW.ofE x).toE = x := ofLimbs_limb x

@[simp] theorem ofE_toE (x : EW) : EW.ofE x.toE = x := by
  rcases x with ⟨c0, c1⟩
  simp [EW.ofE, EW.toE]

theorem toE_injective : Function.Injective EW.toE := fun a b h ↦ by
  rw [← ofE_toE a, h, ofE_toE]

@[simp] theorem toE_inj {a b : EW} : a.toE = b.toE ↔ a = b := toE_injective.eq_iff

@[simp] theorem limb0_toE (x : EW) : x.toE.limb 0 = K.ofLane x.c0 := by
  rw [EW.toE, limb_ofLimbs]
  rfl

@[simp] theorem limb1_toE (x : EW) : x.toE.limb 1 = K.ofLane x.c1 := by
  rw [EW.toE, limb_ofLimbs]
  rfl

theorem isInK_toE_iff (x : EW) : IsInK x.toE ↔ x.c1 = 0 := by
  rw [IsInK, limb1_toE, ← K_ofLane_zero, K_ofLane_injective.eq_iff]

theorem beq_iff_toE {a b : EW} : (a == b) = true ↔ a.toE = b.toE := by
  rw [beq_iff_eq, toE_inj]

theorem toE_scale (k : UInt64) (x : EW) : (EW.scale k x).toE = ofK (K.ofLane k) * x.toE := by
  show E.ofLimbs (K.ofLane (kmul k x.c0)) (K.ofLane (kmul k x.c1)) =
    ofK (K.ofLane k) * E.ofLimbs (K.ofLane x.c0) (K.ofLane x.c1)
  rw [ofK_eq_ofLimbs, mul_limbs]
  simp only [K_ofLane_kmul, zero_mul, add_zero, mul_zero]

theorem toE_sqIter (k : ℕ) (x : EW) : (EW.sqIter k x).toE = x.toE ^ 2 ^ k := by
  induction k generalizing x with
  | zero => simp [EW.sqIter]
  | succ k ih => rw [EW.sqIter, ih, toE_mul, ← sq, ← pow_mul, pow_succ']

end EW

theorem toE_gen : gen.toE = Verifier.gen := by
  show (EW.ofK 2).toE = _
  rw [EW.toE_ofK]
  rfl

theorem toE_gpow (n : ℕ) : (gpow n).toE = Verifier.gpow n := by
  rw [gpow, EW.toE_ofK, K_ofLane_gpowK, Verifier.gpow, ← toE_gen]
  show _ = (EW.ofK 2).toE ^ n
  rw [EW.toE_ofK, K_ofLane_two]
  exact map_pow (algebraMap K E) g n

/-! ## Folds through a map -/

/-- A left fold through a map that carries each step. -/
theorem foldl_hom {α β γ δ : Type} (φ : β → δ) (ψ : α → γ) {f : β → α → β} {g : δ → γ → δ}
    (h : ∀ b a, φ (f b a) = g (φ b) (ψ a)) :
    ∀ (l : List α) (b : β), φ (l.foldl f b) = (l.map ψ).foldl g (φ b)
  | [], _ => rfl
  | a :: l, b => by rw [List.foldl_cons, foldl_hom φ ψ h l, h]; rfl

/-- A right fold through a map that carries each step. -/
theorem foldr_hom {α β γ δ : Type} (φ : β → δ) (ψ : α → γ) {f : α → β → β} {g : γ → δ → δ}
    (h : ∀ a b, φ (f a b) = g (ψ a) (φ b)) :
    ∀ (l : List α) (b : β), φ (l.foldr f b) = (l.map ψ).foldr g (φ b)
  | [], _ => rfl
  | a :: l, b => by rw [List.foldr_cons, h, foldr_hom φ ψ h l]; rfl

/-! ## Arrays of `E` -/

theorem toE_sumE (xs : Array EW) : (sumE xs).toE = Verifier.sumE (xs.toList.map EW.toE) := by
  rw [sumE, ← Array.foldl_toList, foldl_hom EW.toE EW.toE (fun a b ↦ EW.toE_add a b), EW.toE_zero]
  rfl

theorem toE_prodE (xs : Array EW) : (prodE xs).toE = Verifier.prodE (xs.toList.map EW.toE) := by
  rw [prodE, ← Array.foldl_toList, foldl_hom EW.toE EW.toE (fun a b ↦ EW.toE_mul a b), EW.toE_one]
  rfl

theorem powers_loop (b : EW) : ∀ (l : List ℕ) (acc : Array EW) (c : EW),
    (l.foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * b)) (acc, c)).1.toList.map
      EW.toE = acc.toList.map EW.toE ++ Verifier.powersFrom c.toE b.toE l.length
  | [], acc, c => by simp [Verifier.powersFrom]
  | _ :: l, acc, c => by
    rw [List.foldl_cons, powers_loop b l, List.length_cons, Verifier.powersFrom]
    simp

theorem toList_map_powers (b : EW) (n : ℕ) :
    (powers b n).toList.map EW.toE = Verifier.powers b.toE n := by
  rw [powers, powers_loop, List.length_range]
  simp [Verifier.powers]

theorem toList_map_eqKernel (point : Array EW) :
    (eqKernel point).toList.map EW.toE = Verifier.eqKernel (point.toList.map EW.toE) := by
  rw [eqKernel, ← Array.foldl_toList,
    foldl_hom (fun a : Array EW ↦ a.toList.map EW.toE) EW.toE
      (g := fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r))
      (fun out r ↦ by simp [Function.comp_def])]
  simp [Verifier.eqKernel]

theorem foldPairs_list (r : EW) : ∀ (l : List EW),
    ((List.range (l.length / 2)).map fun i ↦ l[2 * i]! * (1 + r) + l[2 * i + 1]! * r).map
      EW.toE = Verifier.foldPairs r.toE (l.map EW.toE)
  | [] => by simp [Verifier.foldPairs]
  | [_] => by simp [Verifier.foldPairs]
  | a :: b :: l => by
    rw [show (a :: b :: l).length / 2 = l.length / 2 + 1 by simp; omega, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.map, Verifier.foldPairs, ← foldPairs_list r l]
    simp [Function.comp_def, Nat.mul_add]

theorem toList_map_foldPairs (r : EW) (cur : Array EW) :
    (foldPairs r cur).toList.map EW.toE = Verifier.foldPairs r.toE (cur.toList.map EW.toE) := by
  rw [← foldPairs_list r cur.toList, foldPairs, Array.toList_map, Array.toList_range,
    Array.length_toList]
  simp [getElem!_def]

theorem toE_getD_zero (a : Array EW) : (a.getD 0 0).toE = (a.toList.map EW.toE).headD 0 := by
  rcases a with ⟨_ | ⟨x, l⟩⟩ <;> simp [Array.getD]

theorem toE_multilinearEval (mle point : Array EW) :
    (multilinearEval mle point).toE =
      Verifier.multilinearEval (mle.toList.map EW.toE) (point.toList.map EW.toE) := by
  rw [multilinearEval, toE_getD_zero, ← Array.foldl_toList,
    foldl_hom (fun a : Array EW ↦ a.toList.map EW.toE) EW.toE
      (g := fun cur r ↦ Verifier.foldPairs r cur) (fun cur r ↦ toList_map_foldPairs r cur)]
  rfl

theorem toE_eqEval (left right : Array EW) :
    (eqEval left right).toE =
      Verifier.eqEval (left.toList.map EW.toE) (right.toList.map EW.toE) := by
  rw [eqEval, ← Array.foldl_toList, foldl_hom EW.toE EW.toE (fun a b ↦ EW.toE_mul a b),
    EW.toE_one, Array.toList_zipWith, Verifier.eqEval, List.map_zipWith, List.zipWith_map]
  simp

theorem toE_dot (left right : Array EW) :
    (dot left right).toE = Verifier.dot (left.toList.map EW.toE) (right.toList.map EW.toE) := by
  rw [dot, ← Array.foldl_toList, foldl_hom EW.toE EW.toE (fun a b ↦ EW.toE_add a b),
    EW.toE_zero, Array.toList_zipWith, Verifier.dot, List.map_zipWith, List.zipWith_map]
  simp

theorem toE_paddingWeight (point : Array EW) (n : ℕ) :
    (paddingWeight point n).toE = Verifier.paddingWeight (point.toList.map EW.toE) n := by
  rw [paddingWeight, Verifier.paddingWeight, EW.toE_mul, ← Array.foldl_toList,
    foldl_hom EW.toE (Prod.map EW.toE id)
      (g := fun pad (p : E × ℕ) ↦
        (1 + Verifier.eOfNat ((n >>> p.2) % 2)) * p.1 +
          (1 + Verifier.eOfNat ((n >>> p.2) % 2) + p.1) * pad)
      (fun pad p ↦ by simp)]
  simp [Array.toList_zipIdx, List.zipIdx_map]

theorem indexMle_loop : ∀ (l : List EW) (acc gp : EW),
    (l.foldl (fun (acc : EW × EW) r ↦ (acc.1 * (1 + r * (1 + acc.2)), acc.2 * acc.2))
      (acc, gp)).1.toE = Verifier.indexMleFrom gp.toE (l.map EW.toE) acc.toE
  | [], _, _ => rfl
  | r :: l, acc, gp => by
    rw [List.foldl_cons, indexMle_loop l, List.map_cons, Verifier.indexMleFrom]
    simp [sq]

theorem toE_indexMle (point : Array EW) :
    (indexMle point).toE = Verifier.indexMle (point.toList.map EW.toE) := by
  rw [indexMle, indexMleFrom, ← Array.foldl_toList, indexMle_loop, toE_gen, EW.toE_one]
  rfl

theorem toE_polyEval (coefficients : Array EW) (point : EW) :
    (polyEval coefficients point).toE =
      Verifier.polyEval (coefficients.toList.map EW.toE) point.toE := by
  rw [polyEval, ← Array.foldr_toList,
    foldr_hom EW.toE EW.toE (g := fun c acc ↦ acc * point.toE + c) (fun c acc ↦ by simp),
    EW.toE_zero]
  rfl

theorem toList_map_selectorPoint (selector length : ℕ) :
    (selectorPoint selector length).toList.map EW.toE = Verifier.selectorPoint selector length := by
  simp [selectorPoint, Verifier.selectorPoint]

end NativeVm.Equiv
