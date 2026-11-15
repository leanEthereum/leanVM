/-
  LeanVM.Protocol.Keccak.LayerSum

  The algebra of a layer's sumchecks: the pack and segment rounds and the position rounds as
  sumcheck families, the final check's terms, and the batched claim on the states before the
  round, through the transpose of the linear map.
-/

module

public import LeanVM.Protocol.Keccak.LayerAlg
public import LeanVM.Protocol.Keccak.Rounds

/-!
# A layer: the sumchecks and the next claim

After the evaluation point `s`, the packs' states at `s`, `Ŝ_j(z) = Σ_i emb_i(s)·b(z, i, j)`
(`Shat0`), are extended multilinearly in the (pack, segment) point (`Shat`), and

  `g(c) = Σ_j w_j (κ·Ŝ_j(c) + (κ + Ŝ_{j+1}(c))·Ŝ_{j+2}(c))`   (`gt`)

is the summand of the pack rounds (eq. `keccak:eq:after-packs`):

* `FP r acc = Σ_{z} eq(r_{≥|acc|}, z) · g(acc ++ z)` is an equality-mode family of degree two
  at `r` (`FP_eqFamily`), equal to `G(s)` before any challenge (`FP_nil`) and to `g(c)` after all
  (`FP_full`);
* with `c` bound, `FX acc = scale · Σ_u φ(acc ++ u)`,
  `φ(p) = W(p)·(κ·T_0(p) + (κ + T_1(p))·T_2(p))`, `W` and `T_k(p) = Σ_j eq(p, j)·Ŝ_{j+k}(c)` the
  multilinear extensions over the `11` position bits, is a plain family of degree three
  (`FX_plainFamily`), equal to `scale · g(c)` before any challenge (`FX_nil`); `dot_weights`: the
  verifier's `dot(eq[:1600], w)` is `W` (eq. `keccak:eq:terminal`);
* `batch_eq`: `T_0 + β(T_1 + βT_2)` at the position point is the claim's sum on the states before
  the round, with weights `keccakLinearTranspose` of the verifier's batched weights and instance
  weights `emb_i(s)` (eq. `keccak:eq:flat` and step 6).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete Finset Polynomial

@[expose] public section

variable (T : States) (P : ℕ) (s : E) (w : List E)

/-! ## The pack and segment rounds -/

/-- The packs' states at `s`, extended multilinearly in the (pack, segment) point. -/
noncomputable def Shat (j : ℕ) (c : List E) : E :=
  ∑ z ∈ range (2 ^ (P + 1)), eqAt c z * Shat0 T P s z j

/-- χ of the packs' states at the point `c`. -/
noncomputable def gt (c : List E) : E :=
  ∑ j ∈ range 1600, w.getD j 0 * (kappaAt s * Shat T P s j c +
    (kappaAt s + Shat T P s (keccakAlong j 1) c) * Shat T P s (keccakAlong j 2) c)

/-- The pack and segment rounds' family at the claim's point `r`. -/
noncomputable def FP (r acc : List E) : E :=
  ∑ z ∈ range (2 ^ (P + 1 - acc.length)), eqAt (r.drop acc.length) z *
    gt T P s w (acc ++ bitsE z (P + 1 - acc.length))

theorem Shat_bitsE (j : ℕ) {z : ℕ} (hz : z < 2 ^ (P + 1)) :
    Shat T P s j (bitsE z (P + 1)) = Shat0 T P s z j :=
  sum_eqAt_bitsE hz _

/-- Before any challenge, the family is `G(s)`. -/
theorem FP_nil (r : List E) : FP T P s w r [] = (Gpoly T P r w).eval s := by
  rw [eval_Gpoly, FP]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  simp only [List.length_nil, Nat.sub_zero, List.drop_zero, List.nil_append, gt]
  have hz' := Finset.mem_range.1 hz
  simp only [Shat_bitsE T P s _ hz']

/-- After all the challenges, the family is `g(c)`. -/
theorem FP_full (r acc : List E) (hr : r.length = P + 1) (h : acc.length = P + 1) :
    FP T P s w r acc = gt T P s w acc := by
  rw [FP, h, Nat.sub_self, List.drop_eq_nil_of_le (by omega)]
  simp [bitsE]

theorem polyLE_Shat (pre post : List E) (j : ℕ) :
    PolyLE 1 fun x ↦ Shat T P s j (pre ++ x :: post) :=
  polyLE_mle pre post _ _

theorem polyLE_gt (pre post : List E) : PolyLE 2 fun x ↦ gt T P s w (pre ++ x :: post) := by
  refine PolyLE.sum _ fun j _ ↦ PolyLE.const_mul ?_ _
  refine PolyLE.add ((PolyLE.const_mul (polyLE_Shat T P s pre post j) _).mono (by norm_num)) ?_
  exact (PolyLE.mul ((PolyLE.add (PolyLE.const 1 _) (polyLE_Shat T P s pre post _)))
    (polyLE_Shat T P s pre post _))

/-- **The pack and segment rounds' family**: degree two, split by the equality weights. -/
theorem FP_eqFamily {β : Type} (Tq : β → States) (r : List E) (hr : r.length = P + 1) :
    EqFamily (fun q acc ↦ FP (Tq q) P s w r acc) r 2 := by
  intro q acc hacc
  have hm : P + 1 - acc.length = (P + 1 - (acc.length + 1)) + 1 := by omega
  have hdrop : r.drop acc.length = r[acc.length] :: r.drop (acc.length + 1) :=
    List.drop_eq_getElem_cons hacc
  refine ⟨?_, ?_⟩
  · have e : ∀ x, FP (Tq q) P s w r (acc ++ [x]) =
        ∑ z ∈ range (2 ^ (P + 1 - (acc.length + 1))), eqAt (r.drop (acc.length + 1)) z *
          gt (Tq q) P s w (acc ++ x :: bitsE z (P + 1 - (acc.length + 1))) := by
      intro x
      simp only [FP, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
    refine PolyLE.congr (f := fun x ↦ ∑ z ∈ range (2 ^ (P + 1 - (acc.length + 1))),
      eqAt (r.drop (acc.length + 1)) z *
        gt (Tq q) P s w (acc ++ x :: bitsE z (P + 1 - (acc.length + 1)))) ?_ fun x ↦ (e x).symm
    exact PolyLE.sum _ fun z _ ↦ PolyLE.const_mul (polyLE_gt (Tq q) P s w acc _) _
  · simp only [FP, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succ, hdrop, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [eqAt_cons, eqAt_cons, bitsE_two_mul, bitsE_two_mul_add_one]
    have h1 : 2 * z % 2 = 0 := by omega
    have h2 : (2 * z + 1) % 2 = 1 := by omega
    have h3 : 2 * z / 2 = z := by omega
    have h4 : (2 * z + 1) / 2 = z := by omega
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false, List.append_assoc,
      List.singleton_append]
    ring

/-! ## The position rounds -/

/-- The packs' state at `c`, `k` columns along, extended over the position bits. -/
noncomputable def Tk (c : List E) (k : ℕ) (p : List E) : E :=
  ∑ j ∈ range 1600, eqAt p j * Shat T P s (keccakAlong j k) c

/-- The position weights, extended over the position bits. -/
noncomputable def Wt (p : List E) : E := ∑ j ∈ range 1600, eqAt p j * w.getD j 0

/-- The position rounds' summand. -/
noncomputable def phi (c p : List E) : E :=
  Wt w p * (kappaAt s * Tk T P s c 0 p + (kappaAt s + Tk T P s c 1 p) * Tk T P s c 2 p)

/-- The position rounds' family. -/
noncomputable def FX (c : List E) (scale : E) (acc : List E) : E :=
  scale * ∑ u ∈ range (2 ^ (11 - acc.length)), phi T P s w c (acc ++ bitsE u (11 - acc.length))

theorem sum1600_bitsE {u : ℕ} (hu : u < 2 ^ 11) (f : ℕ → E) :
    ∑ j ∈ range 1600, eqAt (bitsE u 11) j * f j = if u < 1600 then f u else 0 := by
  have h : ∀ j ∈ range 1600, eqAt (bitsE u 11) j * f j = if u = j then f j else 0 := by
    intro j hj
    rw [eqAt_bitsE_lt hu (by have := Finset.mem_range.1 hj; omega)]
    by_cases h : j = u
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]
  simp

/-- Before any position challenge, the family is `scale · g(c)`. -/
theorem FX_nil (c : List E) (scale : E) : FX T P s w c scale [] = scale * gt T P s w c := by
  unfold FX
  refine congrArg (HMul.hMul _) ?_
  simp only [List.length_nil, Nat.sub_zero, List.nil_append]
  rw [show 2 ^ 11 = 1600 + 448 from rfl, Finset.sum_range_add]
  have hrest : ∑ x ∈ range 448, phi T P s w c (bitsE (1600 + x) 11) = 0 := by
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    have hx' := Finset.mem_range.1 hx
    rw [phi, Wt, sum1600_bitsE (by omega), ite_eq_right (by omega), zero_mul]
  rw [hrest, add_zero, gt]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  rw [phi, Wt, Tk, Tk, Tk, sum1600_bitsE (by omega), sum1600_bitsE (by omega),
    sum1600_bitsE (by omega), sum1600_bitsE (by omega), ite_eq_left hu', ite_eq_left hu',
    ite_eq_left hu', ite_eq_left hu', keccakAlong_zero hu']

theorem FX_full (c : List E) (scale : E) (acc : List E) (h : acc.length = 11) :
    FX T P s w c scale acc = scale * phi T P s w c acc := by
  rw [FX, h, Nat.sub_self]
  simp [bitsE]

theorem polyLE_phi (c pre post : List E) : PolyLE 3 fun x ↦ phi T P s w c (pre ++ x :: post) := by
  unfold phi Wt Tk
  refine PolyLE.mul (d := 1) (d' := 2) (polyLE_mle pre post _ _) ?_
  refine PolyLE.add ((PolyLE.const_mul (polyLE_mle pre post _ _) _).mono (by norm_num)) ?_
  exact PolyLE.mul (PolyLE.add (PolyLE.const 1 _) (polyLE_mle pre post _ _))
    (polyLE_mle pre post _ _)

/-- **The position rounds' family**: degree three, plain. -/
theorem FX_plainFamily {β : Type} (Tq : β → States) (c : List E) (scale : E) :
    PlainFamily (fun q acc ↦ FX (Tq q) P s w c scale acc) 3 11 := by
  intro q acc hacc
  have hm : 11 - acc.length = (11 - (acc.length + 1)) + 1 := by omega
  refine ⟨?_, ?_⟩
  · have e : ∀ x, FX (Tq q) P s w c scale (acc ++ [x]) =
        scale * ∑ u ∈ range (2 ^ (11 - (acc.length + 1))),
          phi (Tq q) P s w c (acc ++ x :: bitsE u (11 - (acc.length + 1))) := by
      intro x
      simp only [FX, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
    refine PolyLE.congr (f := fun x ↦ scale * ∑ u ∈ range (2 ^ (11 - (acc.length + 1))),
      phi (Tq q) P s w c (acc ++ x :: bitsE u (11 - (acc.length + 1)))) ?_ fun x ↦ (e x).symm
    exact PolyLE.const_mul (PolyLE.sum _ fun u _ ↦ polyLE_phi (Tq q) P s w c acc _) scale
  · simp only [FX, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succ, ← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun u _ ↦ ?_)
    rw [bitsE_two_mul, bitsE_two_mul_add_one]
    simp only [List.append_assoc, List.singleton_append]

/-- **The final check's weight**: the verifier's `dot(eq[:1600], w)` is `W`. -/
theorem dot_weights (p : List E) (hp : p.length = 11) (hw : w.length = 1600) :
    dot ((eqKernel p).take keccakBits) w = Wt w p := by
  rw [show keccakBits = w.length from hw.symm, dot_eqKernel p w (by rw [hp, hw]; norm_num), hw]
  rfl

/-! ## The batched claim -/

theorem list_sum_getD (l : List E) : l.sum = ∑ i ∈ range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']; simp [add_comm]

theorem kappa_eq (s : E) : sumE (keccakInstanceWeights s) = kappaAt s := by
  rw [sumE_eq_sum, list_sum_getD, keccakInstanceWeights_length, kappaAt]
  exact Finset.sum_congr rfl fun i hi ↦ keccakInstanceWeights_getD s (Finset.mem_range.1 hi)

/-- `T_k` with the shift moved onto the weights. -/
theorem Tk_shift (c p : List E) {k k' : ℕ} (hk : k + k' = 5) :
    Tk T P s c k p = ∑ j ∈ range 1600, eqAt p (keccakAlong j k') * Shat T P s j c := by
  unfold Tk
  calc ∑ j ∈ range 1600, eqAt p j * Shat T P s (keccakAlong j k) c
      = ∑ j ∈ range 1600, eqAt p (keccakAlong (keccakAlong j k) k') *
          Shat T P s (keccakAlong j k) c :=
        Finset.sum_congr rfl fun j _ ↦ by rw [keccakAlong_along hk]
    _ = _ := sum_perm 1600 (fun j ↦ keccakAlong j k) (fun j ↦ keccakAlong j k')
        (fun j hj ↦ keccakAlong_lt k hj) (fun j hj ↦ keccakAlong_lt k' hj)
        (fun j _ ↦ keccakAlong_along (by omega)) (fun j _ ↦ keccakAlong_along hk)
        (fun j ↦ eqAt p (keccakAlong j k') * Shat T P s j c)

/-- The verifier's batched weights (`crates/verifier/src/keccak.rs`). -/
def batchW (p : List E) (beta : E) : List E :=
  (List.range keccakBits).map fun j ↦ (eqKernel p).getD j 0 +
    beta * ((eqKernel p).getD (keccakAlong j 4) 0 + beta * (eqKernel p).getD (keccakAlong j 3) 0)

theorem batchW_getD (p : List E) (hp : p.length = 11) (beta : E) {j : ℕ} (hj : j < 1600) :
    (batchW p beta).getD j 0 =
      eqAt p j + beta * (eqAt p (keccakAlong j 4) + beta * eqAt p (keccakAlong j 3)) := by
  have hA : ∀ k, (eqKernel p).getD (keccakAlong j k) 0 = eqAt p (keccakAlong j k) :=
    fun k ↦ by rw [eqKernel_getD, hp, ite_eq_left (by have := keccakAlong_lt k hj; omega)]
  rw [batchW, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa [keccakBits] using hj)]
  simp only [Option.map_some, Option.getD_some]
  rw [hA 4, hA 3, eqKernel_getD, hp, ite_eq_left (by omega)]

/-- **The batched claim** (eqs. `keccak:eq:flat` and step 6): `T_0 + β(T_1 + βT_2)` at the
position point is the claim's sum on the states before the round, at the pack point `c`, with
instance weights `emb_i(s)` and position weights `Lᵀ` of the batched weights. -/
theorem batch_eq (c p : List E) (hp : p.length = 11) (beta : E) :
    Tk T P s c 0 p + beta * (Tk T P s c 1 p + beta * Tk T P s c 2 p) =
      claimSum T P c (keccakInstanceWeights s) (keccakLinearTranspose (batchW p beta)) := by
  have h0 : Tk T P s c 0 p = ∑ j ∈ range 1600, eqAt p j * Shat T P s j c :=
    Finset.sum_congr rfl fun j hj ↦ by rw [keccakAlong_zero (Finset.mem_range.1 hj)]
  have hcomb : Tk T P s c 0 p + beta * (Tk T P s c 1 p + beta * Tk T P s c 2 p) =
      ∑ j ∈ range 1600, (batchW p beta).getD j 0 * Shat T P s j c := by
    rw [h0, Tk_shift T P s c p (show 1 + 4 = 5 from rfl),
      Tk_shift T P s c p (show 2 + 3 = 5 from rfl)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [batchW_getD p hp beta (Finset.mem_range.1 hj)]
    ring
  have step1 : ∑ j ∈ range 1600, (batchW p beta).getD j 0 * Shat T P s j c =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt c z * ∑ i ∈ range 16, (embP i).eval s *
        ∑ j ∈ range 1600, (batchW p beta).getD j 0 * bitE (Lb (stAt T P z i) j) := by
    simp only [Shat, Shat0, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hcomb, step1, claimSum]
  refine Finset.sum_congr rfl fun z _ ↦ congrArg (HMul.hMul _)
    (Finset.sum_congr rfl fun i hi ↦ ?_)
  rw [transpose_bits, keccakInstanceWeights_getD s (Finset.mem_range.1 hi)]

end
end LeanVM.Protocol.KeccakGkr
