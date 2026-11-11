/-
  LeanVM.Protocol.Whir.Sound.Tuple

  Polynomial tuples against interleaved words, the weighted claims they are held to through the
  novel basis's low part, the lists the round-by-round invariant ranges over, the affine fold of a
  word, and the Johnson count of a list.
-/

module

public import LeanVM.Protocol.Whir.Sound.Sumcheck
public import LeanVM.Protocol.Whir.NovelBasis
public import LeanVM.Protocol.ToArkLib.Whir.Johnson
public import LeanVM.Protocol.Field

/-!
# Polynomial tuples and their claims

Annex B of the leanVM specification (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`,
Definitions `def:interleaved`, `def:tuple-claim`, `def:affine-fold`), for the deployed code: the
domain `D_{κ,R}` (`domain κ R`, `n = 2^(κ+R)` points of `K`), lanes indexed by the cube points of
`m` lane variables, a word `Q : (Fin m → Bool) → Fin n → E`.

* `vanE κ`: the subspace polynomial `W_κ`, monic of degree `2^κ`, over `E`. A polynomial `P` splits
  as `P = P mod W_κ + W_κ (P div W_κ)`, its *low part* of degree below `2^κ` a message
  (`lowMsg κ P`, the inverse of `msgPoly κ` on degrees below `2^κ`). The Annex's low part, the
  coefficients of `X_c`, `c < 2^κ`, in the novel basis, is this one on degrees below `2^(κ+1)`, as
  `X_{2^κ + j} = Ŵ_κ X_j` is a multiple of `W_κ` (`lowMsg_msgPoly_add`).
* `tclaim κ Φ U = claimSum Φ (lowMsg κ ∘ U)`: the weight `Φ` against a tuple `U`, the lane variables
  first; coefficients of `W_κ` and above carry no weight. On a tuple of degree below `2^κ` it is the
  weight against the decoded message.
* `agreeT dom U Q`: the columns where every lane of `U` agrees with `Q`; `TViol κ dom Q Φ σ a d`:
  every tuple of degree at most `d` agreeing with `Q` on at least `a` columns violates `(Φ, σ)`,
  the invariant of the Annex's round-by-round argument (`thm:rbr`).
* `foldQ dom α β Q`: the affine fold `G + (α + β x) F`, `F` and `G` the lanes whose first lane bit
  is `0` and `1` (`def:affine-fold`).
* `tlist dom Q a d`: the tuples of degree at most `d` agreeing with `Q` on at least `a` columns, and
  `card_tlist_le_jl`: at most `jl n a d` of them when `a² > n d` (`thm:johnson-interleaved`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir Polynomial Finset

@[expose] public section

/-! ## The low part -/

/-- The subspace polynomial `W_κ` over `E`. -/
noncomputable def vanE (κ : ℕ) : E[X] := (vanishing κ).map (algebraMap K E)

theorem vanE_monic (κ : ℕ) : (vanE κ).Monic := by
  refine Monic.map _ ?_
  exact monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

theorem natDegree_vanE (κ : ℕ) : (vanE κ).natDegree = 2 ^ κ := by
  rw [vanE, natDegree_map, natDegree_vanishing]

/-- The low part of a polynomial lies in the range of the message polynomial. -/
theorem modByMonic_mem_range {κ : ℕ} (hκ : κ ≤ 64) (P : E[X]) :
    P %ₘ vanE κ ∈ LinearMap.range (msgPoly κ) := by
  rw [range_msgPoly hκ, mem_degreeLT]
  have := degree_modByMonic_lt P (vanE_monic κ)
  rwa [degree_eq_natDegree (vanE_monic κ).ne_zero, natDegree_vanE] at this

/-- **The message of the low part** of a polynomial, `E`-linear: `msgPoly κ (lowMsg κ P) =
P mod W_κ` (`0` beyond `κ = 64`, which no code reaches). -/
noncomputable def lowMsg (κ : ℕ) : E[X] →ₗ[E] ((Fin κ → Bool) → E) :=
  if hκ : κ ≤ 64 then
    (LinearEquiv.ofInjective (msgPoly κ) (msgPoly_injective hκ)).symm.toLinearMap ∘ₗ
      (modByMonicHom (vanE κ)).codRestrict _ (modByMonic_mem_range hκ)
  else 0

theorem msgPoly_lowMsg {κ : ℕ} (hκ : κ ≤ 64) (P : E[X]) :
    msgPoly κ (lowMsg κ P) = P %ₘ vanE κ := by
  simp only [lowMsg, hκ, ↓reduceDIte, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply]
  rfl

/-- The message polynomial has degree below `2^κ`. -/
theorem natDegree_msgPoly_lt {κ : ℕ} (hκ : κ ≤ 64) (g : (Fin κ → Bool) → E) :
    (msgPoly κ g).degree < (2 ^ κ : ℕ) := by
  have : msgPoly κ g ∈ degreeLT E (2 ^ κ) := range_msgPoly hκ ▸ LinearMap.mem_range_self _ g
  rwa [mem_degreeLT] at this

/-- The low part of `P_g + W_κ H` is `g`. -/
theorem lowMsg_msgPoly_add {κ : ℕ} (hκ : κ ≤ 64) (g : (Fin κ → Bool) → E) (H : E[X]) :
    lowMsg κ (msgPoly κ g + vanE κ * H) = g := by
  apply msgPoly_injective hκ
  rw [msgPoly_lowMsg hκ]
  have hlt : (msgPoly κ g).degree < (vanE κ).degree := by
    rw [degree_eq_natDegree (vanE_monic κ).ne_zero, natDegree_vanE]
    exact natDegree_msgPoly_lt hκ g
  have h0 : (vanE κ * H) %ₘ vanE κ = 0 :=
    (modByMonic_eq_zero_iff_dvd (vanE_monic κ)).mpr (dvd_mul_right _ _)
  rw [← modByMonicHom_apply, map_add, modByMonicHom_apply, modByMonicHom_apply, h0, add_zero,
    (modByMonic_eq_self_iff (vanE_monic κ)).mpr hlt]

/-- The low part of a message polynomial is its message. -/
theorem lowMsg_msgPoly {κ : ℕ} (hκ : κ ≤ 64) (g : (Fin κ → Bool) → E) :
    lowMsg κ (msgPoly κ g) = g := by
  simpa using lowMsg_msgPoly_add hκ g 0

/-- Evaluation splits over the low part: `P(x) = P_low(x) + W_κ(x)·(P div W_κ)(x)`. -/
theorem eval_eq_low_add {κ : ℕ} (hκ : κ ≤ 64) (P : E[X]) (x : E) :
    P.eval x = (msgPoly κ (lowMsg κ P)).eval x + (vanE κ).eval x * (P /ₘ vanE κ).eval x := by
  rw [msgPoly_lowMsg hκ, ← eval_mul, ← eval_add, modByMonic_add_div P (vanE κ)]

/-! ## Tuples, agreement and claims -/

variable {n : ℕ} {ρ : Type} [Fintype ρ]

/-- Every lane of `U` has degree at most `d`. -/
def DegLE (d : ℕ) (U : ρ → E[X]) : Prop := ∀ r, (U r).natDegree ≤ d

open Classical in
/-- The columns where every lane of `U` agrees with the word `Q`. -/
noncomputable def agreeT (dom : Fin n ↪ E) (U : ρ → E[X]) (Q : ρ → Fin n → E) : Finset (Fin n) :=
  univ.filter fun x ↦ ∀ r, (U r).eval (dom x) = Q r x

@[simp] theorem mem_agreeT (dom : Fin n ↪ E) (U : ρ → E[X]) (Q : ρ → Fin n → E) (x : Fin n) :
    x ∈ agreeT dom U Q ↔ ∀ r, (U r).eval (dom x) = Q r x := by
  classical
  simp [agreeT]

/-- The weight `Φ` against a tuple on `m` lane variables: `Σ_u Σ_c Φ(u ++ c)·lowMsg(U_u)(c)`. -/
noncomputable def tclaim {m : ℕ} (κ : ℕ) (Φ : List E → E) (U : (Fin m → Bool) → E[X]) : E :=
  claimSum Φ fun u ↦ lowMsg κ (U u)

/-- **The invariant**: every tuple of degree at most `d` agreeing with `Q` on at least `a` columns
violates `(Φ, σ)`. -/
def TViol {m : ℕ} (κ : ℕ) (dom : Fin n ↪ E) (Q : (Fin m → Bool) → Fin n → E) (Φ : List E → E)
    (σ : E) (a d : ℕ) : Prop :=
  ∀ U : (Fin m → Bool) → E[X], DegLE d U → a ≤ (agreeT dom U Q).card → tclaim κ Φ U ≠ σ

/-- A higher threshold and a lower degree keep the invariant. -/
theorem TViol.mono {m κ : ℕ} {dom : Fin n ↪ E} {Q : (Fin m → Bool) → Fin n → E} {Φ : List E → E}
    {σ : E} {a a' d d' : ℕ} (h : TViol κ dom Q Φ σ a d) (ha : a ≤ a') (hd : d' ≤ d) :
    TViol κ dom Q Φ σ a' d' :=
  fun U hU hag ↦ h U (fun r ↦ (hU r).trans hd) (ha.trans hag)

/-! ## The affine fold -/

/-- **The affine fold** of a word on `m + 1` lane variables: lane `u` of the fold is
`G_u + (α + β x) F_u`, `F_u` and `G_u` the lanes `(0, u)` and `(1, u)`. -/
def foldQ {m : ℕ} (dom : Fin n ↪ E) (α β : E) (Q : (Fin (m + 1) → Bool) → Fin n → E) :
    (Fin m → Bool) → Fin n → E :=
  fun u x ↦ Q (Fin.cons true u) x + (α + β * dom x) * Q (Fin.cons false u) x

/-! ## Lists and the Johnson count -/

/-- Over the finite field `E`, there are finitely many polynomials of degree at most `d`. -/
theorem finite_natDegree_le (d : ℕ) : {P : E[X] | P.natDegree ≤ d}.Finite := by
  refine Set.Finite.of_finite_image (f := fun P : E[X] ↦ fun i : Fin (d + 1) ↦ P.coeff i)
    (Set.toFinite _) fun P hP Q hQ h ↦ Polynomial.ext fun i ↦ ?_
  by_cases hi : i ≤ d
  · exact congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt ((show P.natDegree ≤ d from hP).trans_lt (not_le.mp hi)),
      coeff_eq_zero_of_natDegree_lt ((show Q.natDegree ≤ d from hQ).trans_lt (not_le.mp hi))]

/-- Finitely many tuples have degree at most `d`. -/
theorem finite_degLE (d : ℕ) : {U : ρ → E[X] | DegLE d U}.Finite := by
  have : {U : ρ → E[X] | DegLE d U} = Set.pi Set.univ fun _ ↦ {P : E[X] | P.natDegree ≤ d} := by
    ext U; simp [DegLE]
  rw [this]
  exact Set.Finite.pi fun _ ↦ finite_natDegree_le d

/-- **The list** of `Q` at threshold `a` and degree `d`. -/
noncomputable def tlist (dom : Fin n ↪ E) (Q : ρ → Fin n → E) (a d : ℕ) : Finset (ρ → E[X]) :=
  Set.Finite.toFinset (s := {U : ρ → E[X] | DegLE d U ∧ a ≤ (agreeT dom U Q).card})
    ((finite_degLE d).subset fun _ hU ↦ hU.1)

@[simp] theorem mem_tlist (dom : Fin n ↪ E) (Q : ρ → Fin n → E) (a d : ℕ) (U : ρ → E[X]) :
    U ∈ tlist dom Q a d ↔ DegLE d U ∧ a ≤ (agreeT dom U Q).card := by
  simp [tlist]

/-- Two distinct tuples of degree at most `d` agree on at most `d` common columns of `Q`. -/
theorem card_agreeT_inter_le (dom : Fin n ↪ E) {d : ℕ} {U V : ρ → E[X]} (hU : DegLE d U)
    (hV : DegLE d V) (hne : U ≠ V) (Q : ρ → Fin n → E) :
    (agreeT dom U Q ∩ agreeT dom V Q).card ≤ d := by
  classical
  obtain ⟨r, hr⟩ : ∃ r, U r ≠ V r := by
    by_contra h
    exact hne (funext fun r ↦ not_not.mp ((not_exists.mp h) r))
  have hD : U r - V r ≠ 0 := sub_ne_zero.mpr hr
  calc (agreeT dom U Q ∩ agreeT dom V Q).card
      ≤ (U r - V r).roots.toFinset.card :=
        Finset.card_le_card_of_injOn dom (fun x hx ↦ by
          rw [Finset.mem_coe, Finset.mem_inter, mem_agreeT, mem_agreeT] at hx
          rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hD, IsRoot, eval_sub,
            hx.1 r, hx.2 r, sub_self]) dom.injective.injOn
    _ ≤ (U r - V r).roots.card := Multiset.toFinset_card_le _
    _ ≤ (U r - V r).natDegree := card_roots' _
    _ ≤ d := (natDegree_sub_le _ _).trans (max_le (hU r) (hV r))

/-- **The Johnson count of a list**: with `a² > n d`, at most `jl n a d` tuples. -/
theorem card_tlist_le_jl (dom : Fin n ↪ E) (Q : ρ → Fin n → E) (a d : ℕ) (hgap : n * d < a * a) :
    (tlist dom Q a d).card ≤ jl n a d := by
  classical
  have h := card_le_jl (tlist dom Q a d) (fun U ↦ agreeT dom U Q) a d
    (fun U hU ↦ ((mem_tlist _ _ _ _ U).mp hU).2)
    (fun U hU V hV hne ↦ card_agreeT_inter_le dom ((mem_tlist _ _ _ _ U).mp hU).1
      ((mem_tlist _ _ _ _ V).mp hV).1 hne Q) (by simpa using hgap)
  simpa using h

end
end LeanVM.Protocol.Whir.Sound
