module

public import Quantum.StdModel.Sphincs.Instances
public import Quantum.Qrom.Classical
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# Uniform laws for the hybrid hops of leanSPHINCS

The hops of the reduction replace a uniform function by what the scheme reads from it. Each law
here says that this reading is again uniform, as normalized sums `unifAvg X Φ = |X|⁻¹ ∑ x, Φ x`.
The laws are proved over abstract finite types and instantiated at the end.

* `unifAvg_update`: the value of a uniform function at `x0` is uniform and independent of the
  rest, for a statistic insensitive to the rest's value at `x0`.
* `unifAvg_restrictTrunc`: a uniform function restricted along an injection and truncated by a
  map with fibers of equal size is uniform; `unifAvg_dep`, `unifAvg_joint`, `unifAvg_dep_extra`:
  jointly with a truncated value at `x0` outside the restriction (the restriction may depend on
  that value), and with one more untouched value.
* Instances: `kim_law`, `kim_law_prfKey` (the `SK.seed`-keyed calls), `msg_law` (`PRF_msg`),
  `cpreJ_law` (the CPRE chain starts are the secrets), and the sampling bridge
  `sum_prEvent_uniformSample`, `tsum_prEvent_uniformSample`.
-/

open OracleComp
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs

/-! ## Uniform averages -/

/-- **The uniform average** of `Φ` over a finite type. -/
noncomputable def unifAvg (X : Type) [Fintype X] (Φ : X → ℝ≥0∞) : ℝ≥0∞ :=
  (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ x, Φ x

section Abstract

variable {A B U V D D' X : Type}

theorem unifAvg_congr [Fintype A] {Φ Ψ : A → ℝ≥0∞} (h : ∀ a, Φ a = Ψ a) :
    unifAvg A Φ = unifAvg A Ψ :=
  congrArg (unifAvg A) (funext h)

theorem inv_mul_mul_cancel {n k : ℕ} (hk : k ≠ 0) (S : ℝ≥0∞) :
    ((n * k : ℕ) : ℝ≥0∞)⁻¹ * (k * S) = (n : ℝ≥0∞)⁻¹ * S := by
  have hk' : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inr hk'),
    show (n : ℝ≥0∞)⁻¹ * (k : ℝ≥0∞)⁻¹ * (k * S) = (n : ℝ≥0∞)⁻¹ * ((k : ℝ≥0∞)⁻¹ * k) * S by ring,
    ENNReal.inv_mul_cancel hk' (ENNReal.natCast_ne_top _), mul_one]

/-- **A map with fibers of equal size pushes the uniform law to the uniform law.** -/
theorem unifAvg_comp_of_fiber [Fintype A] [Fintype B] [DecidableEq B] (π : A → B) {k : ℕ}
    (hk : k ≠ 0) (hfib : ∀ b, Fintype.card {a // π a = b} = k) (Φ : B → ℝ≥0∞) :
    unifAvg A (fun a ↦ Φ (π a)) = unifAvg B Φ := by
  have hsum : ∑ a, Φ (π a) = (k : ℝ≥0∞) * ∑ b, Φ b := by
    rw [← Fintype.sum_equiv (Equiv.sigmaFiberEquiv π) (fun x ↦ Φ (π x.2)) (fun a ↦ Φ (π a))
      (fun _ ↦ rfl), Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.sum_congr rfl (fun (a : {a // π a = b}) _ ↦ congrArg Φ a.2), Finset.sum_const,
      Finset.card_univ, hfib, nsmul_eq_mul]
  have hcard : Fintype.card A = Fintype.card B * k := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv π), Fintype.card_sigma,
      Finset.sum_congr rfl (fun b _ ↦ hfib b), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  unfold unifAvg
  rw [hsum, hcard, inv_mul_mul_cancel hk]

/-- A bijection pushes the uniform law to the uniform law. -/
theorem unifAvg_equiv [Fintype A] [Fintype B] (e : A ≃ B) (Φ : B → ℝ≥0∞) :
    unifAvg A (fun a ↦ Φ (e a)) = unifAvg B Φ := by
  unfold unifAvg
  rw [Fintype.card_congr e, Fintype.sum_equiv e _ Φ (fun _ ↦ rfl)]

/-- A uniform pair is a pair of independent uniform components. -/
theorem unifAvg_prod [Fintype A] [Fintype B] (Φ : A × B → ℝ≥0∞) :
    unifAvg (A × B) Φ = unifAvg A fun a ↦ unifAvg B fun b ↦ Φ (a, b) := by
  unfold unifAvg
  rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _)), Fintype.sum_prod_type, mul_assoc]
  simp only [Finset.mul_sum]

/-- Two independent uniform averages commute. -/
theorem unifAvg_comm [Fintype A] [Fintype B] (Φ : A → B → ℝ≥0∞) :
    (unifAvg A fun a ↦ unifAvg B fun b ↦ Φ a b) = unifAvg B fun b ↦ unifAvg A fun a ↦ Φ a b := by
  unfold unifAvg
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

theorem unifAvg_const [Fintype A] [Nonempty A] (c : ℝ≥0∞) : unifAvg A (fun _ ↦ c) = c := by
  unfold unifAvg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

/-- **Independence of one coordinate**: the value of a uniform function at `x0` is uniform and
independent of the function, for a statistic that ignores the function's value at `x0`. -/
theorem unifAvg_update [Fintype X] [DecidableEq X] [Fintype U] [Nonempty U] (x0 : X)
    (Φ : U → (X → U) → ℝ≥0∞) (hΦ : ∀ u f w, Φ u (Function.update f x0 w) = Φ u f) :
    unifAvg (X → U) (fun f ↦ Φ (f x0) f) = unifAvg U fun u ↦ unifAvg (X → U) fun f ↦ Φ u f := by
  have h := Quantum.Qrom.sum_sum_update_eq_card_smul x0 fun f u ↦ Φ u f
  simp only [hΦ] at h
  have hU : (Fintype.card U : ℝ≥0∞)⁻¹ * Fintype.card U = 1 :=
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  unfold unifAvg
  rw [← Finset.mul_sum, h, nsmul_eq_mul,
    show ∀ a b c : ℝ≥0∞, a * (b * (c * ∑ f : X → U, Φ (f x0) f)) =
      (a * c) * (b * ∑ f : X → U, Φ (f x0) f) from fun _ _ _ ↦ by ring, hU, one_mul]

/-- A uniform function truncated pointwise by a map with fibers of equal size is uniform. -/
theorem unifAvg_piMap [Fintype D] [DecidableEq D] [Fintype U] [Fintype V] [DecidableEq V]
    (t : U → V) {k : ℕ} (hk : k ≠ 0) (hfib : ∀ v, Fintype.card {u // t u = v} = k)
    (Φ : (D → V) → ℝ≥0∞) :
    unifAvg (D → U) (fun f ↦ Φ (fun d ↦ t (f d))) = unifAvg (D → V) Φ := by
  classical
  refine unifAvg_comp_of_fiber (fun (f : D → U) (d : D) ↦ t (f d)) (k := k ^ Fintype.card D)
    (pow_ne_zero _ hk) (fun g ↦ ?_) Φ
  rw [Fintype.card_congr ((Equiv.subtypeEquivRight fun f : D → U ↦ funext_iff).trans
    (Equiv.subtypePiEquivPi (p := fun d u ↦ t u = g d))), Fintype.card_pi]
  simp [hfib]

/-- A uniform function restricted along an injection is uniform. -/
theorem unifAvg_restrict [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] [Fintype U]
    [Nonempty U] (ι : D' → D) (hι : Function.Injective ι) (Φ : (D' → U) → ℝ≥0∞) :
    unifAvg (D → U) (fun f ↦ Φ (fun d' ↦ f (ι d'))) = unifAvg (D' → U) Φ := by
  classical
  let e1 := Equiv.piEquivPiSubtypeProd (· ∈ Set.range ι) fun _ ↦ U
  let e2 : ({d // d ∈ Set.range ι} → U) ≃ (D' → U) :=
    Equiv.arrowCongr (Equiv.ofInjective ι hι).symm (Equiv.refl U)
  have h : ∀ f : D → U, (fun d' ↦ f (ι d')) = e2 (e1 f).1 := fun _ ↦ rfl
  simp only [h]
  rw [unifAvg_equiv e1 fun p ↦ Φ (e2 p.1), unifAvg_prod]
  rw [unifAvg_congr fun r ↦ unifAvg_const (Φ (e2 r))]
  exact unifAvg_equiv e2 Φ

/-- **Restriction and truncation**: a uniform function restricted along an injection and
truncated by a map with fibers of equal size is uniform. -/
theorem unifAvg_restrictTrunc [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
    [Fintype U] [Nonempty U] [Fintype V] [DecidableEq V] (t : U → V) {k : ℕ} (hk : k ≠ 0)
    (hfib : ∀ v, Fintype.card {u // t u = v} = k) (ι : D' → D) (hι : Function.Injective ι)
    (Φ : (D' → V) → ℝ≥0∞) :
    unifAvg (D → U) (fun f ↦ Φ (fun d' ↦ t (f (ι d')))) = unifAvg (D' → V) Φ :=
  (unifAvg_restrict ι hι fun g ↦ Φ (fun d' ↦ t (g d'))).trans (unifAvg_piMap t hk hfib Φ)

/-- **The dependent joint law**: the truncated value at `x0` and the truncated restriction along
`ι v` (avoiding `x0`, chosen by that value `v`) are independent and uniform. -/
theorem unifAvg_dep [Fintype X] [DecidableEq X] [Fintype D'] [DecidableEq D'] [Fintype U]
    [Nonempty U] [Fintype V] [DecidableEq V] (t : U → V) {k : ℕ} (hk : k ≠ 0)
    (hfib : ∀ v, Fintype.card {u // t u = v} = k) (x0 : X) (ι : V → D' → X)
    (hι : ∀ v, Function.Injective (ι v)) (hx0 : ∀ v d', ι v d' ≠ x0)
    (Φ : V → (D' → V) → ℝ≥0∞) :
    unifAvg (X → U) (fun f ↦ Φ (t (f x0)) (fun d' ↦ t (f (ι (t (f x0)) d')))) =
      unifAvg V fun v ↦ unifAvg (D' → V) (Φ v) := by
  refine (unifAvg_update x0 (fun u f ↦ Φ (t u) (fun d' ↦ t (f (ι (t u) d'))))
    (fun u f w ↦ congrArg (Φ (t u)) (funext fun d' ↦
      congrArg t (Function.update_of_ne (hx0 _ d') _ _)))).trans ?_
  rw [unifAvg_congr fun u ↦ unifAvg_restrictTrunc t hk hfib (ι (t u)) (hι _) (Φ (t u))]
  exact unifAvg_comp_of_fiber t hk hfib fun v ↦ unifAvg (D' → V) (Φ v)

/-- **The joint law**: the truncated value at `x0` and the truncated restriction along `ι`
(avoiding `x0`) are independent and uniform. -/
theorem unifAvg_joint [Fintype X] [DecidableEq X] [Fintype D'] [DecidableEq D'] [Fintype U]
    [Nonempty U] [Fintype V] [DecidableEq V] (t : U → V) {k : ℕ} (hk : k ≠ 0)
    (hfib : ∀ v, Fintype.card {u // t u = v} = k) (x0 : X) (ι : D' → X)
    (hι : Function.Injective ι) (hx0 : x0 ∉ Set.range ι) (Φ : V → (D' → V) → ℝ≥0∞) :
    unifAvg (X → U) (fun f ↦ Φ (t (f x0)) (fun d' ↦ t (f (ι d')))) =
      unifAvg V fun v ↦ unifAvg (D' → V) (Φ v) :=
  unifAvg_dep t hk hfib x0 (fun _ ↦ ι) (fun _ ↦ hι) (fun _ d' h ↦ hx0 ⟨d', h⟩) Φ

/-- The dependent joint law with one more untouched coordinate `x1`. -/
theorem unifAvg_dep_extra [Fintype X] [DecidableEq X] [Fintype D'] [DecidableEq D'] [Fintype U]
    [Nonempty U] [Fintype V] [DecidableEq V] (t : U → V) {k : ℕ} (hk : k ≠ 0)
    (hfib : ∀ v, Fintype.card {u // t u = v} = k) (x0 x1 : X) (h01 : x0 ≠ x1) (ι : V → D' → X)
    (hι : ∀ v, Function.Injective (ι v)) (hx0 : ∀ v d', ι v d' ≠ x0) (hx1 : ∀ v d', ι v d' ≠ x1)
    (Φ : V → (D' → V) → U → ℝ≥0∞) :
    unifAvg (X → U) (fun f ↦ Φ (t (f x0)) (fun d' ↦ t (f (ι (t (f x0)) d'))) (f x1)) =
      unifAvg V fun v ↦ unifAvg (D' → V) fun s ↦ unifAvg U fun K ↦ Φ v s K := by
  refine (unifAvg_update x1 (fun K f ↦ Φ (t (f x0)) (fun d' ↦ t (f (ι (t (f x0)) d'))) K)
    (fun K f w ↦ ?_)).trans ?_
  · simp only [Function.update_of_ne h01, Function.update_of_ne (hx1 _ _)]
  rw [unifAvg_congr fun K ↦ unifAvg_dep t hk hfib x0 ι hι hx0 fun v s ↦ Φ v s K,
    unifAvg_comm]
  exact unifAvg_congr fun v ↦ unifAvg_comm fun K s ↦ Φ v s K

/-! ## Sampling -/

/-- Uniform sampling weighs every element by `|X|⁻¹`. -/
theorem sum_prEvent_uniformSample [SampleableType A] [Fintype A] (Φ : A → ℝ≥0∞) :
    ∑ a, Pr{let z ← $ᵗ A}[z = a] * Φ a = unifAvg A Φ := by
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, unifAvg, Finset.mul_sum]

theorem tsum_prEvent_uniformSample [SampleableType A] [Fintype A] (Φ : A → ℝ≥0∞) :
    ∑' a, Pr{let z ← $ᵗ A}[z = a] * Φ a = unifAvg A Φ := by
  rw [tsum_fintype, sum_prEvent_uniformSample]

end Abstract

/-! ## The truncation's fibers -/

theorem toNat_truncateHash (o : HashOutput) : (truncateHash o).toNat = o.toNat % 2 ^ 128 := by
  show (o.extractLsb' 0 128).toNat = _
  simp

/-- The low and the high 128 bits of a hash output. -/
def splitOutput : HashOutput ≃ Digest × BitVec 128 where
  toFun o := (truncateHash o, o.extractLsb' 128 128)
  invFun p := BitVec.ofNat 256 (p.1.toNat + 2 ^ 128 * p.2.toNat)
  left_inv o := by
    apply BitVec.eq_of_toNat_eq
    have ho : o.toNat < 2 ^ 256 := o.isLt
    rw [BitVec.toNat_ofNat, toNat_truncateHash, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow]
    omega
  right_inv p := by
    obtain ⟨a, b⟩ := p
    have ha : a.toNat < 2 ^ 128 := a.isLt
    have hb : b.toNat < 2 ^ 128 := b.isLt
    refine Prod.ext (BitVec.eq_of_toNat_eq ?_) (BitVec.eq_of_toNat_eq ?_)
    · show (truncateHash (BitVec.ofNat 256 (a.toNat + 2 ^ 128 * b.toNat))).toNat = a.toNat
      rw [toNat_truncateHash, BitVec.toNat_ofNat]
      omega
    · show (BitVec.extractLsb' 128 128 (BitVec.ofNat 256 (a.toNat + 2 ^ 128 * b.toNat))).toNat =
        b.toNat
      rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega

theorem splitOutput_fst (o : HashOutput) : (splitOutput o).1 = truncateHash o :=
  rfl

/-- **Every digest has `|BitVec 128|` preimages under `truncateHash`.** -/
theorem card_fiber_truncateHash (d : Digest) :
    Fintype.card {o : HashOutput // truncateHash o = d} = Fintype.card (BitVec 128) := by
  refine Fintype.card_congr ((Equiv.subtypeEquiv (q := fun p : Digest × BitVec 128 ↦ p.1 = d)
    splitOutput fun _ ↦ Iff.rfl).trans ?_)
  exact {
    toFun := fun p ↦ p.1.2
    invFun := fun b ↦ ⟨(d, b), rfl⟩
    left_inv := fun ⟨⟨d', b⟩, h⟩ ↦ by subst h; rfl
    right_inv := fun _ ↦ rfl }

theorem card_bitVec128_ne_zero : Fintype.card (BitVec 128) ≠ 0 :=
  Fintype.card_ne_zero

/-! ## The secrets and the CPRE chain starts -/

/-- The secrets as the CPRE chains: a chain start is chain `i` of its key, a FORS secret its
leaf. -/
def cpreJ_equiv : KeygenDomain ≃ CpreJ where
  toFun
    | .oneTimeChain l τ e i => .inl ((l, τ, e), i)
    | .forsSecret idx κ s => .inr (idx, κ, s)
  invFun
    | .inl ((l, τ, e), i) => .oneTimeChain l τ e i
    | .inr (idx, κ, s) => .forsSecret idx κ s
  left_inv d := by cases d <;> rfl
  right_inv j := by rcases j with ⟨⟨l, τ, e⟩, i⟩ | ⟨idx, κ, s⟩ <;> rfl

instance instFintypeKeygenDomain : Fintype KeygenDomain :=
  Fintype.ofEquiv CpreJ cpreJ_equiv.symm

/-- **Uniform CPRE chain starts are uniform secrets.** -/
theorem cpreJ_law (Φ : (KeygenDomain → Digest) → ℝ≥0∞) :
    unifAvg (CpreJ → Digest) (fun s ↦ Φ (s ∘ cpreJ_equiv)) =
      unifAvg (KeygenDomain → Digest) Φ :=
  unifAvg_equiv (Equiv.arrowCongr cpreJ_equiv.symm (Equiv.refl Digest)) Φ

/-! ## KIM-PRF and PRF_msg -/

/-- **The law of the `SK.seed`-keyed calls**: from a uniform function on the formats, `PK.seed`
and the secrets at `PK.seed` are uniform and independent. -/
theorem kim_law (Φ : PublicParameter → (KeygenDomain → Digest) → ℝ≥0∞) :
    unifAvg (KimDom → HashOutput) (fun f ↦ Φ (truncateHash (f .publicSeed))
        (fun d ↦ truncateHash (f (.prf (truncateHash (f .publicSeed)) d)))) =
      unifAvg PublicParameter fun P ↦ unifAvg (KeygenDomain → Digest) (Φ P) :=
  unifAvg_dep truncateHash card_bitVec128_ne_zero card_fiber_truncateHash KimDom.publicSeed
    (fun P d ↦ KimDom.prf P d) (fun _ _ _ h ↦ (KimDom.prf.inj h).2)
    (fun _ _ h ↦ KimDom.noConfusion h) Φ

/-- The law of the `SK.seed`-keyed calls with `SK.prf`, uniform and independent of the rest. -/
theorem kim_law_prfKey (Φ : PublicParameter → (KeygenDomain → Digest) → HashOutput → ℝ≥0∞) :
    unifAvg (KimDom → HashOutput) (fun f ↦ Φ (truncateHash (f .publicSeed))
        (fun d ↦ truncateHash (f (.prf (truncateHash (f .publicSeed)) d))) (f .prfKey)) =
      unifAvg PublicParameter fun P ↦ unifAvg (KeygenDomain → Digest) fun s ↦
        unifAvg HashOutput fun K ↦ Φ P s K :=
  unifAvg_dep_extra truncateHash card_bitVec128_ne_zero card_fiber_truncateHash
    KimDom.publicSeed KimDom.prfKey (fun h ↦ KimDom.noConfusion h) (fun P d ↦ KimDom.prf P d)
    (fun _ _ _ h ↦ (KimDom.prf.inj h).2) (fun _ _ h ↦ KimDom.noConfusion h)
    (fun _ _ h ↦ KimDom.noConfusion h) Φ

/-- **The law of `PRF_msg`**: at a fixed optional randomness `P`, the randomizers of a uniform
function are uniform. -/
theorem msg_law (P : PublicParameter) (Ψ : (Message → Digest) → ℝ≥0∞) :
    unifAvg (MsgDom → HashOutput) (fun g ↦ Ψ (fun M ↦ truncateHash (g (P, M)))) =
      unifAvg (Message → Digest) Ψ :=
  unifAvg_restrictTrunc truncateHash card_bitVec128_ne_zero card_fiber_truncateHash
    (fun M ↦ ((P, M) : MsgDom)) (fun _ _ h ↦ (Prod.mk.inj h).2) Ψ

end Quantum.StdModel.Sphincs

end
