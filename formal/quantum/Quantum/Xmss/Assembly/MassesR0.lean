module

public import Quantum.Xmss.Assembly.MassSources
public import Quantum.Xmss.Hybrid.Mismatch
public import Quantum.Xmss.Hybrid.R0Stage

@[expose] public section

/-!
# The hidden masses with the randomizer bases and the seed paths

Masses' averaged bound (`uavg_totalWeight_portMass_le`) for runtime 1's full table, whose cells
are the honest paths' (`pathH`, `pathK`, `pathK'`), the seed paths' (the master seed's derivation,
the parameter's and the chain starts', `seedH`, `seedK`, `seedK'`) and the randomizer-base paths'
(`r0H`, `r0K`, `r0K'`) (r0-design, sections 5 to 7).

* **`covers`** (`covers_r0`, `covers_of_progs_or`): a table whose cells are path, seed or
  randomizer-base cells is covered by `pathH ∪ seedH ∪ r0H` (and likewise for `k`, `k'`).
* **Masses over a never-revealed part** (`sum_totalWeight_portMass_le_count`): hidden sets
  `H k` depending on a coordinate `k ∈ K` the run ignores, each cell in `H k` for at most an `ε`
  fraction of the `k`, weigh at most `ε` per call on average.
* **The averaged bound with the mismatch** (`uavg_totalWeight_portMass_le_r0`): the table, padded,
  is mapped injectively on a good set into public data `P`, hidden values `V = HPos → Digest` and a
  never-revealed part `K`. On the good set the game at the table is the template game at the
  public datum realized at hidden values agreeing with `V`'s off a set `B` of coordinates
  (`hgame`, an inequality through Mismatch's `totalWeight_portMass_le_mismatch`); the table's hidden
  sets lie in sets of `(P, V)` with sources (`Sources`, per call `κ`) united with sets of `(P, K)`
  of multiplicity `εK`; the record mass of `B` averages over `K` to `R εB`
  (`sum_revW_le`). The averaged mass is at most `N (κ + εK + R εB)` plus `N` times the bad fraction.
* **leanXMSS's never-revealed part** (`RK`: the scheme seed `S`, the master seed `S₀`, R0Stage's
  `k`- and `k'`-slots `κ`, `κ'`): the families `r0Kk`, `r0K'k`, `r0Hk`, `seedKk` and the non-first
  labels `r0Bk`, with their multiplicities over `RK` (`2^-256` per `S`-keyed or `S₀`-keyed
  `k`-cell, `|J| G / |Z|` per randomizer-base rate on a `PermGood π G`, `|J| / |Z|` per
  randomizer-base capacity and per non-first label; `r0Eps`). Capacities go through `capOf`
  (`gCap`), proved over abstract types. On R0Stage's good set the table's randomizer-base and seed
  `k`-cells, its non-first labels and its first labels' bases are these at R0Stage's coordinates
  `rkOf` (`r0Good_subsets`, `mem_r0B_iff`, `valueAt_inr_eq_r0Coord`).
* **The bounds** (`uavg_spongeMass_le_xmssR0`, `uavg_readMass_le_xmssR0`): in the shapes of
  Security's `hybSponge`, `hybRead`, with the never-revealed part `RK × W`; at Keccak's sizes
  `r0Eps_le_keccak` (`2^-219`) and `revTerm_le_keccak` (`2 · lifetime · |J| / |Z| ≤ 2^-190`).
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v w

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid

/-! ## Masses over a coordinate the run ignores -/

section count

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg}

/-- An indicator sum over a family is at most the count of a weaker condition. -/
theorem sum_indicator_le_of_imp {K α : Type*} [Fintype K] (Sk : K → Set α) (a : α)
    (T : K → Set α) (h : ∀ k, a ∈ Sk k → a ∈ T k) :
    ∑ k, (Sk k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a :=
  Finset.sum_le_sum fun k _ ↦ by
    by_cases ha : a ∈ Sk k
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (h k ha)]
    · rw [Set.indicator_of_notMem ha]
      exact zero_le

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- **Per call, over a coordinate the run ignores**: when every cell lies in the hidden sets `H k`
for at most `ε |K|` of the `k`, the port masses add up over `k` to at most `ε |K|` times the
trace. -/
theorem sum_portMass_le_count (Q : (recHwSpec X Z S M').Port → Prop) [DecidablePred Q]
    {K : Type} [Fintype K] (Hh : K → Set Z) (Hk Hk' : K → Set X) (ε : ℝ≥0∞)
    (hh : ∀ z, ∑ k, (Hh k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ ε * Fintype.card K)
    (hk : ∀ y, ∑ k, (Hk k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ ε * Fintype.card K)
    (hk' : ∀ y, ∑ k, (Hk' k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ ε * Fintype.card K)
    (i : (recHwSpec X Z S M').Port)
    {σ : Matrix ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M')))
      ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M'))) ℂ} (hσ : σ.PosSemidef) :
    ∑ k, portMass Q (Hh k) (Hk k) (Hk' k) i σ ≤
      (ε * Fintype.card K) * (if Q i then ENNReal.ofReal σ.trace.re else 0) := by
  by_cases hQ : Q i
  · simp only [portMass, hQ, ↓reduceIte]
    rw [Finset.sum_congr rfl fun k _ ↦ congrFun (congrFun (extWeight_hiddenMass_eq
      (t := recSpec S M') (Hh k) (Hk k) (Hk' k)) i) σ]
    refine sum_diagMass_le (fun k ↦ extHidSet (Hh k) (Hk k) (Hk' k) i) _ (fun a ↦ ?_) hσ
    rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | T
    · exact (sum_indicator_le_of_imp _ a (fun k ↦ {b | b.1.1 ∈ Hh k}) fun _ hb ↦ hb.1).trans
        (hh a.1.1)
    · exact (sum_indicator_le_of_imp _ a (fun k ↦ {b | b.1.1 ∈ Hk k}) fun _ hb ↦ hb.1).trans
        (hk a.1.1)
    · exact (sum_indicator_le_of_imp _ a (fun k ↦ {b | b.1.1 ∈ Hk' k}) fun _ hb ↦ hb.1).trans
        (hk' a.1.1)
    · exact (sum_indicator_le_of_imp _ a (fun k ↦ {_b | z ∈ Hh k}) fun _ hb ↦ hb.1).trans
        (le_of_eq_of_le (Finset.sum_congr rfl fun k _ ↦ by
          by_cases h : z ∈ Hh k <;> simp [h]) (hh z))
    · exact (sum_indicator_le_of_imp _ a (fun k ↦ {_b | y ∈ Hk k}) fun _ hb ↦ hb.1).trans
        (le_of_eq_of_le (Finset.sum_congr rfl fun k _ ↦ by
          by_cases h : y ∈ Hk k <;> simp [h]) (hk y))
    · exact (sum_indicator_le_of_imp _ a (fun k ↦ {_b | y ∈ Hk' k}) fun _ hb ↦ hb.1).trans
        (le_of_eq_of_le (Finset.sum_congr rfl fun k _ ↦ by
          by_cases h : y ∈ Hk' k <;> simp [h]) (hk' y))
    · exact (Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _).le.trans
        zero_le
    · exact (Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _).le.trans
        zero_le
  · simp only [portMass, hQ, ↓reduceIte, Finset.sum_const_zero, mul_zero, le_refl]

/-- **The total masses over a coordinate the run ignores**: with at most `N` calls of the ports
`Q`, the total port masses of the hidden sets `H k` add up over `k` to at most `ε |K| N` times the
trace. -/
theorem sum_totalWeight_portMass_le_count (Q : (recHwSpec X Z S M').Port → Prop)
    [DecidablePred Q] (m₀ : Finset S × M') (x : QuantumComp Λ (recHwSpec X Z S M') Xf A)
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M'))) (A × QReg.of (HwReg X Z (Finset S × M')))
      ℂ} (hρ : ρ.PosSemidef) {K : Type} [Fintype K] (Hh : K → Set Z) (Hk Hk' : K → Set X)
    (ε : ℝ≥0∞)
    (hh : ∀ z, ∑ k, (Hh k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ ε * Fintype.card K)
    (hk : ∀ y, ∑ k, (Hk k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ ε * Fintype.card K)
    (hk' : ∀ y, ∑ k, (Hk' k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ ε * Fintype.card K)
    {N : ℕ} (hN : IFreeM.IsChargeBound x (portCharge fun i ↦ if Q i then 1 else 0) N) :
    ∑ k, (runtimeR m₀).totalWeight I (portMass Q (Hh k) (Hk k) (Hk' k)) x ρ ≤
      (ε * Fintype.card K) * (N * ENNReal.ofReal ρ.trace.re) := by
  rw [← totalWeight_fintype_sum (runtimeR m₀) I (fun k ↦ portMass Q (Hh k) (Hk k) (Hk' k)) x ρ]
  refine (totalWeight_le_totalWeight (runtimeR m₀) I
    (w' := fun i σ ↦ (ε * Fintype.card K) * (if Q i then ENNReal.ofReal σ.trace.re else 0))
    (fun i σ hσ ↦ sum_portMass_le_count Q Hh Hk Hk' ε hh hk hk' i hσ) x hρ).trans
    ((totalWeight_const_mul_weight (runtimeR m₀) I (ε * Fintype.card K)
      (fun i σ ↦ if Q i then ENNReal.ofReal σ.trace.re else 0) x ρ).trans_le ?_)
  exact mul_le_mul_of_nonneg_left (totalWeight_trace_le_of_isChargeBound' (runtimeR m₀) I Q x hN hρ)
    zero_le

end count

/-! ## The averaged bound with the mismatch and a never-revealed part -/

section r0avg

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The averaged total hidden mass at the ports `Q`, with the mismatch.**

The table, padded by `E`, is mapped by `e` into public data `P`, hidden values `V = HPos → Digest`
and a never-revealed part `K`, injectively on the good set `G`. On `G` the game at the table is
the template game at the public datum `pubP p` realized at hidden values agreeing with the
coordinate `v` off the set `B p k` (`hgame`; for leanXMSS `B` is the non-first labels' randomizer
bases), and the table's hidden sets lie in sets of `(p, v)` (with sources of weight `κ` on the
invariant `Inv`) united with sets of `(p, k)` (each cell in them for at most `εK |K|` of the `k`).
Every path records at most `R` coordinates of `J ⊇ B p k`, each coordinate in `B p k` for at most
`εB |K|` of the `k`. With at most `N` calls of the ports `Q`, the averaged total hidden mass is at
most `N (κ + εK + R εB)` plus `N` times the bad fraction. -/
theorem uavg_totalWeight_portMass_le_r0 (Q : (recHwSpec X Z HPos M).Port → Prop) [DecidablePred Q]
    (A : Adversary (X × Z)) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    {E P K : Type} [Fintype E] [Nonempty E] [Fintype P] [Fintype K]
    (e : HonestTable × E → P × ((HPos → Digest) × K)) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × K) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (B : P → K → Finset HPos)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ B (e t).1 (e t).2.2) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (Hhv : P → (HPos → Digest) → Set Z) (Hkv Hk'v : P → (HPos → Digest) → Set X)
    (Hhk : P → K → Set Z) (Hkk Hk'k : P → K → Set X)
    (hsub : ∀ t, G t →
      Hh t.1 ⊆ Hhv (e t).1 (e t).2.1 ∪ Hhk (e t).1 (e t).2.2 ∧
      Hk t.1 ⊆ Hkv (e t).1 (e t).2.1 ∪ Hkk (e t).1 (e t).2.2 ∧
      Hk' t.1 ⊆ Hk'v (e t).1 (e t).2.1 ∪ Hk'k (e t).1 (e t).2.2)
    (Inv : P → (HPos → Digest) → HwReg X Z (Finset HPos × M) → Prop)
    (hinv : ∀ p v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (Inv p v)) (realizeT v (gameT M upd (pubP p) A)) ρ)
    (κ : ℝ≥0∞)
    (src : ∀ p, Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (Inv p) (Hhv p) (Hkv p)
      (Hk'v p) κ)
    (εK : ℝ≥0∞)
    (hcH : ∀ p z, ∑ k, (Hhk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ εK * Fintype.card K)
    (hcK : ∀ p y, ∑ k, (Hkk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card K)
    (hcK' : ∀ p y, ∑ k, (Hk'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card K)
    (J : Finset HPos) (hBJ : ∀ p k, B p k ⊆ J) (εB : ℝ≥0∞)
    (hεB : ∀ p, ∀ s ∈ J,
      ((Finset.univ.filter fun k ↦ s ∈ B p k).card : ℝ≥0∞) ≤ εB * Fintype.card K)
    {R : ℕ} (hR : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A)) (portCharge (candCharge X Z M J)) R)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if Q i then 1 else 0) N) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hh L) (Hk L) (Hk' L)) (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      N * (κ + εK + R * εB) + N * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬G t).card) := by
  have hbound : ∀ (pub : Pub) (v : HPos → Digest) (Hh₀ : Set Z) (Hk₀ Hk'₀ : Set X),
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (portMass Q Hh₀ Hk₀ Hk'₀)
        (realizeT v (gameT M upd pub A)) ρ ≤ N :=
    fun pub v Hh₀ Hk₀ Hk'₀ ↦ (totalWeight_portMass_le _ Q m₀ Hh₀ Hk₀ Hk'₀ _ hρ (hN pub v)).trans
      ((mul_le_mul_of_nonneg_left hρ1 zero_le).trans_eq (mul_one _))
  refine (uavg_le_of_injOn e G hinj hcard _
    (fun p w ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass Q (Hhv p w.1) (Hkv p w.1) (Hk'v p w.1)) (realizeT w.1 (gameT M upd (pubP p) A)) ρ +
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass Q (Hhk p w.2) (Hkk p w.2) (Hk'k p w.2)) (realizeT w.1 (gameT M upd (pubP p) A)) ρ +
      N * revW m₀ LocalSig.Interp.instruments (B p w.2) (realizeT w.1 (gameT M upd (pubP p) A)) ρ)
    (fun t ht ↦ ?_) N (fun t _ ↦ hbound _ _ _ _ _) (N * (κ + εK + R * εB)) fun p ↦ ?_).trans
    le_rfl
  · obtain ⟨v, hv, hgeq⟩ := hgame t ht
    obtain ⟨h1, h2, h3⟩ := hsub t ht
    rw [hgeq]
    refine (totalWeight_portMass_le_mismatch m₀ LocalSig.Interp.instruments
      (gameT M upd (pubP (e t).1) A) (disc_gameT M upd _ A ∅) (keepsLab_gameT upd _ A) ρ hρ hs
      (B (e t).1 (e t).2.2) (Finset.disjoint_empty_left _) Q (Hh t.1) (Hk t.1) (Hk' t.1) hv
      (hN _ v)).trans (add_le_add ?_ le_rfl)
    exact (totalWeight_portMass_mono _ Q m₀ h1 h2 h3 _ hρ).trans
      (totalWeight_portMass_union_le _ Q m₀ _ _ _ _ _ _ _ hρ)
  · have hpath : ∑ v : HPos → Digest, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass Q (Hhv p v) (Hkv p v) (Hk'v p v)) (realizeT v (gameT M upd (pubP p) A)) ρ ≤
        κ * N * Fintype.card (HPos → Digest) := by
      refine (sum_totalWeight_portMass_runtimeR_le_inv LocalSig.Interp.instruments Q m₀
        (fun r ↦ r.2.2.1) (fun v ↦ realizeT v (gameT M upd (pubP p) A)) (fun _ ↦ ρ) (fun _ ↦ hρ)
        (fun j ↦ viewByOn_gameT M upd (pubP p) A m₀ ρ j) (Inv p) (hinv p) (Hhv p) (Hkv p)
        (Hk'v p) κ (src p) (fun v ↦ hN (pubP p) v)).trans ?_
      calc κ * (N * ∑ _v : HPos → Digest, ENNReal.ofReal ρ.trace.re)
          ≤ κ * (N * ∑ _v : HPos → Digest, (1 : ℝ≥0∞)) := by gcongr
        _ = κ * N * Fintype.card (HPos → Digest) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_assoc]
    have hK : ∀ v : HPos → Digest, ∑ k, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass Q (Hhk p k) (Hkk p k) (Hk'k p k)) (realizeT v (gameT M upd (pubP p) A)) ρ ≤
        εK * N * Fintype.card K := fun v ↦
      (sum_totalWeight_portMass_le_count LocalSig.Interp.instruments Q m₀ _ hρ (Hhk p) (Hkk p)
        (Hk'k p) εK (hcH p) (hcK p) (hcK' p) (hN _ v)).trans
        (by calc (εK * Fintype.card K) * (N * ENNReal.ofReal ρ.trace.re)
              ≤ (εK * Fintype.card K) * (N * 1) := by gcongr
            _ = εK * N * Fintype.card K := by ring)
    have hrev : ∀ v : HPos → Digest, ∑ k, revW m₀ LocalSig.Interp.instruments (B p k)
        (realizeT v (gameT M upd (pubP p) A)) ρ ≤ R * εB * Fintype.card K := fun v ↦
      (sum_revW_le m₀ LocalSig.Interp.instruments _ hρ (B p) J (hBJ p) εB (hεB p) (hR _ v)).trans
        (by calc (Fintype.card K : ℝ≥0∞) * (R * εB * ENNReal.ofReal ρ.trace.re)
              ≤ Fintype.card K * (R * εB * 1) := by gcongr
            _ = R * εB * Fintype.card K := by ring)
    rw [Fintype.sum_prod_type]
    calc ∑ v : HPos → Digest, ∑ k : K,
          ((runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass Q (Hhv p (v, k).1) (Hkv p (v, k).1) (Hk'v p (v, k).1))
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ +
          (runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass Q (Hhk p (v, k).2) (Hkk p (v, k).2) (Hk'k p (v, k).2))
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ +
          N * revW m₀ LocalSig.Interp.instruments (B p (v, k).2)
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ)
        ≤ ∑ v : HPos → Digest, (Fintype.card K * (runtimeR m₀).totalWeight
            LocalSig.Interp.instruments (portMass Q (Hhv p v) (Hkv p v) (Hk'v p v))
            (realizeT v (gameT M upd (pubP p) A)) ρ +
          (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))) := by
          refine Finset.sum_le_sum fun v _ ↦ ?_
          dsimp only
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, add_assoc]
          exact add_le_add le_rfl (add_le_add (hK v) (mul_le_mul_of_nonneg_left (hrev v) zero_le))
      _ = Fintype.card K * ∑ v : HPos → Digest, (runtimeR m₀).totalWeight
            LocalSig.Interp.instruments (portMass Q (Hhv p v) (Hkv p v) (Hk'v p v))
            (realizeT v (gameT M upd (pubP p) A)) ρ +
          Fintype.card (HPos → Digest) * (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))
          := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
      _ ≤ Fintype.card K * (κ * N * Fintype.card (HPos → Digest)) +
          Fintype.card (HPos → Digest) * (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))
          := by gcongr
      _ = N * (κ + εK + R * εB) * Fintype.card ((HPos → Digest) × K) := by
          rw [Fintype.card_prod, Nat.cast_mul]
          ring

end r0avg

/-! ## Counting over the never-revealed part, over abstract types -/

section countK

/-- Indicator sums of a union are at most the sums of the parts. -/
theorem sum_indicator_union_le {K α : Type*} [Fintype K] (S T : K → Set α) (a : α) :
    ∑ k, (S k ∪ T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤
      ∑ k, (S k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a +
        ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  by_cases hS : a ∈ S k
  · rw [Set.indicator_of_mem (Set.mem_union_left _ hS), Set.indicator_of_mem hS]
    exact le_self_add
  · by_cases hT : a ∈ T k
    · rw [Set.indicator_of_mem (Set.mem_union_right _ hT), Set.indicator_of_mem hT]
      exact le_add_self
    · rw [Set.indicator_of_notMem (fun h ↦ h.elim hS hT)]
      exact zero_le

/-- A count of a filter as an indicator sum. -/
theorem card_filter_eq_sum_indicator {K : Type*} [Fintype K] (p : K → Prop) [DecidablePred p] :
    ((Finset.univ.filter p).card : ℝ≥0∞) = ∑ k, ({k | p k} : Set K).indicator (fun _ ↦ 1) k := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases h : p k <;> simp [h]

/-- A multiplicity bound survives a pad coordinate. -/
theorem sum_indicator_pad_le {K W α : Type*} [Fintype K] [Fintype W] (S : K → Set α) (a : α)
    (ε : ℝ≥0∞) (h : ∑ k, (S k).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ ε * Fintype.card K) :
    ∑ kw : K × W, (S kw.1).indicator (fun _ ↦ (1 : ℝ≥0∞)) a ≤ ε * Fintype.card (K × W) := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fintype.card_prod, Nat.cast_mul, mul_comm, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h zero_le

/-- A filter count survives a pad coordinate. -/
theorem card_filter_pad {K W : Type*} [Fintype K] [Fintype W] (p : K → Prop) [DecidablePred p] :
    ((Finset.univ.filter fun kw : K × W ↦ p kw.1).card : ℝ≥0∞) =
      (Finset.univ.filter p).card * Fintype.card W := by
  rw [← Finset.univ_product_univ, Finset.filter_product_left p, Finset.card_product,
    Finset.card_univ, Nat.cast_mul]

/-- `d s ≤ c N` gives `s ≤ (c / d) N`. -/
theorem le_div_mul_of_mul_le {s c N d : ℝ≥0∞} (hd0 : d ≠ 0) (hdt : d ≠ ⊤) (h : d * s ≤ c * N) :
    s ≤ c / d * N :=
  calc s = d⁻¹ * (d * s) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hd0 hdt, one_mul]
    _ ≤ d⁻¹ * (c * N) := mul_le_mul_of_nonneg_left h zero_le
    _ = c / d * N := by rw [div_eq_mul_inv]; ring

/-- Two terms with a common factor, bounded termwise and swapped. -/
theorem add_mul_le_add_mul {x y u v N : ℝ≥0∞} (hx : x ≤ v) (hy : y ≤ u) :
    x * N + y * N ≤ (u + v) * N := by
  rw [add_mul, add_comm (u * N)]
  exact add_le_add (mul_le_mul_of_nonneg_right hx zero_le) (mul_le_mul_of_nonneg_right hy zero_le)

/-- **One coordinate of a uniform function**: summing a function of `κ a` over all `κ`. -/
theorem card_mul_sum_apply {J β : Type*} [Fintype J] [DecidableEq J] [Fintype β] (a : J)
    (f : β → ℝ≥0∞) :
    (Fintype.card β : ℝ≥0∞) * ∑ κ : J → β, f (κ a) = (∑ z, f z) * Fintype.card (J → β) := by
  rw [Fintype.sum_equiv (Equiv.piSplitAt a fun _ : J ↦ β) (fun κ ↦ f (κ a)) (fun p ↦ f p.1)
    (fun _ ↦ rfl), Fintype.sum_prod_type, Fintype.card_congr (Equiv.piSplitAt a fun _ : J ↦ β),
    Fintype.card_prod]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
  rw [← Finset.mul_sum]
  ring

/-- **One coordinate of a uniform function, fixed by the others**: the `κ` whose `κ a` is a
function of the other coordinates are a `1 / |β|` fraction. -/
theorem card_mul_sum_indicator_apply_eq {J β : Type*} [Fintype J] [DecidableEq J] [Fintype β]
    (a : J) (g : ({j // j ≠ a} → β) → β) :
    (Fintype.card β : ℝ≥0∞) *
        ∑ κ : J → β, ({κ | κ a = g fun j ↦ κ j} : Set (J → β)).indicator (fun _ ↦ 1) κ =
      Fintype.card (J → β) := by
  classical
  rw [Fintype.sum_equiv (Equiv.piSplitAt a fun _ : J ↦ β) _
    (fun p ↦ if p.1 = g p.2 then (1 : ℝ≥0∞) else 0) fun κ ↦ by
      by_cases h : κ a = g fun j ↦ κ j
      · rw [Set.indicator_of_mem (show κ ∈ {κ : J → β | κ a = g fun j ↦ κ j} from h)]
        simp only [Equiv.piSplitAt_apply]
        exact (ite_eq_left_of_eq_true _ _ (eq_true h)).symm
      · rw [Set.indicator_of_notMem (show κ ∉ {κ : J → β | κ a = g fun j ↦ κ j} from h)]
        simp only [Equiv.piSplitAt_apply]
        exact (ite_eq_right_of_eq_false _ _ (eq_false h)).symm,
    Fintype.sum_prod_type_right]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [Fintype.card_congr (Equiv.piSplitAt a fun _ : J ↦ β), Fintype.card_prod, Nat.cast_mul]

/-- **Four coordinates, the last one counted**: per value of the first three, the last one
meets the condition for at most a `c / d` fraction. -/
theorem card_mul_sum_four_le {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (d c : ℝ≥0∞) (f : A × B × C × D → ℝ≥0∞)
    (hf : ∀ s b κ, d * ∑ κ', f (s, b, κ, κ') ≤ c * Fintype.card D) :
    d * ∑ k, f k ≤ c * Fintype.card (A × B × C × D) :=
  calc d * ∑ k, f k = ∑ s, ∑ b, ∑ κ, d * ∑ κ', f (s, b, κ, κ') := by
        simp only [Fintype.sum_prod_type, Finset.mul_sum]
    _ ≤ ∑ _s : A, ∑ _b : B, ∑ _κ : C, c * Fintype.card D :=
        Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun b _ ↦ Finset.sum_le_sum fun κ _ ↦
          hf s b κ
    _ = c * Fintype.card (A × B × C × D) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
          Nat.cast_mul]
        ring

/-- **Four coordinates, the third one counted.** -/
theorem card_mul_sum_four_le' {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (d c : ℝ≥0∞) (f : A × B × C × D → ℝ≥0∞)
    (hf : ∀ s b κ', d * ∑ κ, f (s, b, κ, κ') ≤ c * Fintype.card C) :
    d * ∑ k, f k ≤ c * Fintype.card (A × B × C × D) :=
  calc d * ∑ k, f k = ∑ s, ∑ b, ∑ κ', d * ∑ κ, f (s, b, κ, κ') := by
        simp only [Fintype.sum_prod_type, Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun b _ ↦ Finset.sum_comm
    _ ≤ ∑ _s : A, ∑ _b : B, ∑ _κ' : D, c * Fintype.card C :=
        Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun b _ ↦ Finset.sum_le_sum fun κ' _ ↦
          hf s b κ'
    _ = c * Fintype.card (A × B × C × D) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
          Nat.cast_mul]
        ring

/-- A point in some set of a family indexed by `J` is counted by the sum over `J`. -/
theorem indicator_le_sum_of_exists {J K α : Type*} [Fintype J] (T : Set α) (x : α)
    (F : J → Set K) (k : K) (h : x ∈ T → ∃ a, k ∈ F a) :
    T.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ ∑ a, (F a).indicator (fun _ ↦ (1 : ℝ≥0∞)) k := by
  by_cases hx : x ∈ T
  · obtain ⟨a, ha⟩ := h hx
    rw [Set.indicator_of_mem hx]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun a ↦
      (F a).indicator (fun _ ↦ (1 : ℝ≥0∞)) k) (fun _ _ ↦ zero_le) (Finset.mem_univ a))
    rw [Set.indicator_of_mem ha]
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

/-- **Two seeds**: when a point lies in the sets `T k` only if it lies in `f` of the first seed or
in `g` of the second, each seed hit once, the point weighs at most `2 / |A|`. -/
theorem sum_indicator_two_le {A C D α : Type*} [Fintype A] [Nonempty A] [Fintype C] [Fintype D]
    (T : A × A × C × D → Set α) (f g : A → Set α) (x : α)
    (hT : ∀ k, x ∈ T k → x ∈ f k.1 ∪ g k.2.1)
    (hf : ∑ s, (f s).indicator (fun _ ↦ (1 : ℝ≥0∞)) x = 1)
    (hg : ∑ s, (g s).indicator (fun _ ↦ (1 : ℝ≥0∞)) x = 1) :
    ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      2 * (Fintype.card A : ℝ≥0∞)⁻¹ * Fintype.card (A × A × C × D) := by
  have h1 : ∑ k : A × A × C × D, (f k.1).indicator (fun _ ↦ (1 : ℝ≥0∞)) x =
      Fintype.card (A × C × D) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, hf, mul_one]
  have h2 : ∑ k : A × A × C × D, (g k.2.1).indicator (fun _ ↦ (1 : ℝ≥0∞)) x =
      Fintype.card (A × C × D) := by
    calc ∑ k : A × A × C × D, (g k.2.1).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
        = ∑ _s : A, ∑ s₀ : A, (Fintype.card (C × D) : ℝ≥0∞) *
            (g s₀).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun _ _ ↦ ?_
          rw [Fintype.sum_prod_type]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = Fintype.card (A × C × D) := by
          simp only [← Finset.mul_sum, hg, mul_one, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
          ring
  have hc : (Fintype.card (A × A × C × D) : ℝ≥0∞) =
      Fintype.card A * Fintype.card (A × C × D) := by
    rw [Fintype.card_prod A, Nat.cast_mul]
  calc ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
      ≤ ∑ k : A × A × C × D, (f k.1 ∪ g k.2.1).indicator (fun _ ↦ (1 : ℝ≥0∞)) x :=
        sum_indicator_le_of_imp _ x _ hT
    _ ≤ _ := sum_indicator_union_le _ _ x
    _ = 2 * Fintype.card (A × C × D) := by rw [h1, h2, two_mul]
    _ = 2 * (Fintype.card A : ℝ≥0∞)⁻¹ * Fintype.card (A × A × C × D) := by
        rw [hc, mul_assoc, ← mul_assoc _ (Fintype.card A : ℝ≥0∞),
          ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _), one_mul]

/-- **A uniform slot `κ`**: when a point lies in `T k` only if some label's slot `κ a` lies in a
set `F a s` of weight at most `c`, the point weighs at most `|J| c / |β|`. -/
theorem card_mul_sum_slot_le {A B J β D α : Type*} [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq J] [Fintype β] [Fintype D] (T : A × B × (J → β) × D → Set α) (x : α)
    (F : J → A → Set β) (c : ℝ≥0∞) (hT : ∀ k, x ∈ T k → ∃ a, k.2.2.1 a ∈ F a k.1)
    (hF : ∀ a s, ∑ w, (F a s).indicator (fun _ ↦ (1 : ℝ≥0∞)) w ≤ c) :
    (Fintype.card β : ℝ≥0∞) * ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      Fintype.card J * c * Fintype.card (A × B × (J → β) × D) :=
  calc (Fintype.card β : ℝ≥0∞) * ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
      ≤ Fintype.card β * ∑ k : A × B × (J → β) × D, ∑ a,
          (F a k.1).indicator (fun _ ↦ (1 : ℝ≥0∞)) (k.2.2.1 a) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ (indicator_le_sum_of_exists _ x
          (fun a ↦ {κ : J → β | κ a ∈ F a k.1}) k.2.2.1 (hT k)).trans_eq
            (Finset.sum_congr rfl fun a _ ↦ by
              by_cases h : k.2.2.1 a ∈ F a k.1
              · rw [Set.indicator_of_mem (show k.2.2.1 ∈ {κ : J → β | κ a ∈ F a k.1} from h),
                  Set.indicator_of_mem h]
              · rw [Set.indicator_of_notMem (show k.2.2.1 ∉ {κ : J → β | κ a ∈ F a k.1} from h),
                  Set.indicator_of_notMem h])) zero_le
    _ = ∑ a, Fintype.card β * ∑ k : A × B × (J → β) × D,
          (F a k.1).indicator (fun _ ↦ (1 : ℝ≥0∞)) (k.2.2.1 a) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _a : J, c * Fintype.card (A × B × (J → β) × D) :=
        Finset.sum_le_sum fun a _ ↦ card_mul_sum_four_le' _ _ _ fun s _ _ ↦
          le_of_eq_of_le (card_mul_sum_apply a fun w ↦ (F a s).indicator (fun _ ↦ 1) w)
            (mul_le_mul_of_nonneg_right (hF a s) zero_le)
    _ = Fintype.card J * c * Fintype.card (A × B × (J → β) × D) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- **A uniform last slot `κ'`**: when a point lies in `T k` only if some label's slot `κ' a` lies
in a set `F a s κ` of weight at most `c`, the point weighs at most `|J| c / |β|`. -/
theorem card_mul_sum_slot_le' {A B C J β α : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype J] [DecidableEq J] [Fintype β] (T : A × B × C × (J → β) → Set α) (x : α)
    (F : J → A → C → Set β) (c : ℝ≥0∞) (hT : ∀ k, x ∈ T k → ∃ a, k.2.2.2 a ∈ F a k.1 k.2.2.1)
    (hF : ∀ a s κ, ∑ w, (F a s κ).indicator (fun _ ↦ (1 : ℝ≥0∞)) w ≤ c) :
    (Fintype.card β : ℝ≥0∞) * ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      Fintype.card J * c * Fintype.card (A × B × C × (J → β)) :=
  calc (Fintype.card β : ℝ≥0∞) * ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x
      ≤ Fintype.card β * ∑ k : A × B × C × (J → β), ∑ a,
          (F a k.1 k.2.2.1).indicator (fun _ ↦ (1 : ℝ≥0∞)) (k.2.2.2 a) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ (indicator_le_sum_of_exists _ x
          (fun a ↦ {κ : J → β | κ a ∈ F a k.1 k.2.2.1}) k.2.2.2 (hT k)).trans_eq
            (Finset.sum_congr rfl fun a _ ↦ by
              by_cases h : k.2.2.2 a ∈ F a k.1 k.2.2.1
              · rw [Set.indicator_of_mem
                  (show k.2.2.2 ∈ {κ : J → β | κ a ∈ F a k.1 k.2.2.1} from h),
                  Set.indicator_of_mem h]
              · rw [Set.indicator_of_notMem
                  (show k.2.2.2 ∉ {κ : J → β | κ a ∈ F a k.1 k.2.2.1} from h),
                  Set.indicator_of_notMem h])) zero_le
    _ = ∑ a, Fintype.card β * ∑ k : A × B × C × (J → β),
          (F a k.1 k.2.2.1).indicator (fun _ ↦ (1 : ℝ≥0∞)) (k.2.2.2 a) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _a : J, c * Fintype.card (A × B × C × (J → β)) :=
        Finset.sum_le_sum fun a _ ↦ card_mul_sum_four_le _ _ _ fun s _ κ ↦
          le_of_eq_of_le (card_mul_sum_apply a fun w ↦ (F a s κ).indicator (fun _ ↦ 1) w)
            (mul_le_mul_of_nonneg_right (hF a s κ) zero_le)
    _ = Fintype.card J * c * Fintype.card (A × B × C × (J → β)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- **A label's last slot fixed by another label's**: when `P k` holds only if `κ' a` is a function
of the first three coordinates and of `κ' b` for some `b ≠ a`, it holds for at most a `|J| / |β|`
fraction. -/
theorem card_mul_sum_slot_eq_le {A B C J β : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype J] [DecidableEq J] [Fintype β] (a : J) (P : A × B × C × (J → β) → Prop)
    (h : J → A → B → C → β → β)
    (hP : ∀ k, P k → ∃ b, b ≠ a ∧ k.2.2.2 a = h b k.1 k.2.1 k.2.2.1 (k.2.2.2 b)) :
    (Fintype.card β : ℝ≥0∞) * ∑ k, ({k | P k} : Set (A × B × C × (J → β))).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) k ≤
      Fintype.card J * Fintype.card (A × B × C × (J → β)) :=
  calc (Fintype.card β : ℝ≥0∞) * ∑ k, ({k | P k} : Set (A × B × C × (J → β))).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) k
      ≤ Fintype.card β * ∑ k : A × B × C × (J → β), ∑ b,
          ({k | b ≠ a ∧ k.2.2.2 a = h b k.1 k.2.1 k.2.2.1 (k.2.2.2 b)} :
            Set (A × B × C × (J → β))).indicator (fun _ ↦ (1 : ℝ≥0∞)) k :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦
          indicator_le_sum_of_exists _ k _ k (hP k)) zero_le
    _ = ∑ b, Fintype.card β * ∑ k : A × B × C × (J → β),
          ({k | b ≠ a ∧ k.2.2.2 a = h b k.1 k.2.1 k.2.2.1 (k.2.2.2 b)} :
            Set (A × B × C × (J → β))).indicator (fun _ ↦ (1 : ℝ≥0∞)) k := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _b : J, (1 : ℝ≥0∞) * Fintype.card (A × B × C × (J → β)) := by
        refine Finset.sum_le_sum fun b _ ↦ ?_
        by_cases hba : b = a
        · rw [Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem (fun hk ↦ hk.1 hba) _,
            mul_zero]
          exact zero_le
        · refine card_mul_sum_four_le _ _ _ fun s t c₀ ↦ le_of_eq ?_
          rw [one_mul, ← card_mul_sum_indicator_apply_eq a fun r ↦ h b s t c₀ (r ⟨b, hba⟩)]
          refine congrArg _ (Finset.sum_congr rfl fun κ' _ ↦ ?_)
          by_cases hk : κ' a = h b s t c₀ (κ' b)
          · rw [Set.indicator_of_mem (show (s, t, c₀, κ') ∈
                ({k | b ≠ a ∧ k.2.2.2 a = h b k.1 k.2.1 k.2.2.1 (k.2.2.2 b)} :
                  Set (A × B × C × (J → β))) from ⟨hba, hk⟩),
              Set.indicator_of_mem (show κ' ∈
                ({κ | κ a = h b s t c₀ (κ b)} : Set (J → β)) from hk)]
          · rw [Set.indicator_of_notMem (show (s, t, c₀, κ') ∉
                ({k | b ≠ a ∧ k.2.2.2 a = h b k.1 k.2.1 k.2.2.1 (k.2.2.2 b)} :
                  Set (A × B × C × (J → β))) from fun hm ↦ hk hm.2),
              Set.indicator_of_notMem (show κ' ∉
                ({κ | κ a = h b s t c₀ (κ b)} : Set (J → β)) from hk)]
    _ = Fintype.card J * Fintype.card (A × B × C × (J → β)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]

end countK

/-! ## One-block capacities with constant keys, over abstract types

Capacities written through `capOf` (generic in the group), so the concrete instances are those of
R0Stage's `coinCellH` (no instance diamond at Keccak's sizes for the kernel). -/

section capConst

variable {X' Z' : Type} [Fintype Z'] [DecidableEq Z'] [AddCommGroup Z']

/-- The value of the `k'`-key that puts a one-block capacity at `z`. -/
def capSolve (π : Equiv.Perm (X' × Z')) (b : X') (c z : Z') : Z' :=
  z - (π (b, c)).2

omit [Fintype Z'] [DecidableEq Z'] in
theorem eq_capSolve {π : Equiv.Perm (X' × Z')} {b : X'} {c w z : Z'}
    (h : capOf (fun _ ↦ c) (fun _ ↦ w) π b = z) : w = capSolve π b c z := by
  unfold capOf at h
  unfold capSolve
  rw [← h, add_sub_cancel_left]

/-- **A one-block capacity hits a point once** as its `k'`-value ranges over the capacities. -/
theorem sum_indicator_capOf_eq_one (π : Equiv.Perm (X' × Z')) (b : X') (c z : Z') :
    ∑ w : Z', ({w | capOf (fun _ ↦ c) (fun _ ↦ w) π b = z} : Set Z').indicator
      (fun _ ↦ (1 : ℝ≥0∞)) w = 1 := by
  rw [← card_filter_eq_sum_indicator]
  have : (Finset.univ.filter fun w : Z' ↦ capOf (fun _ ↦ c) (fun _ ↦ w) π b = z) =
      {capSolve π b c z} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨eq_capSolve, fun h ↦ ?_⟩
    rw [h]
    unfold capOf capSolve
    exact add_sub_cancel _ _
  rw [this, Finset.card_singleton, Nat.cast_one]

variable {S S₀ J : Type} [Fintype S] [Fintype S₀] [Fintype J] [DecidableEq J]

/-- A label's one-block capacity at the slots `k = (S, S₀, κ, κ')`: first block `cell a S`, `k`-
value `κ a`, `k'`-value `κ' a`. -/
def gCap (π : Equiv.Perm (X' × Z')) (cell : J → S → X') (k : S × S₀ × (J → Z') × (J → Z'))
    (a : J) : Z' :=
  capOf (fun _ ↦ k.2.2.1 a) (fun _ ↦ k.2.2.2 a) π (cell a k.1)

/-- **The labels' capacities over uniform `k'`-slots**: a point is some label's capacity for at
most a `|J| / |Z'|` fraction of the slots. -/
theorem sum_indicator_range_gCap_le (π : Equiv.Perm (X' × Z')) (cell : J → S → X') (z : Z') :
    ∑ k : S × S₀ × (J → Z') × (J → Z'), (Set.range (gCap π cell k)).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      (Fintype.card J : ℝ≥0∞) / Fintype.card Z' *
        Fintype.card (S × S₀ × (J → Z') × (J → Z')) :=
  le_div_mul_of_mul_le (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
    ((card_mul_sum_slot_le' (fun k ↦ Set.range (gCap π cell k)) z
      (fun a s κ ↦ {w | capOf (fun _ ↦ κ a) (fun _ ↦ w) π (cell a s) = z}) 1 (fun _ hk ↦ hk)
      fun _ _ _ ↦ (sum_indicator_capOf_eq_one π _ _ z).le).trans_eq (by rw [mul_one]))

omit [DecidableEq Z'] in
/-- **A label is not first** (a label of smaller rank has its capacity) for at most a `|J| / |Z'|`
fraction of the slots: its `k'`-slot is uniform given the others. -/
theorem sum_indicator_notFirst_le (π : Equiv.Perm (X' × Z')) (cell : J → S → X') (ord : J ↪ ℕ)
    (a : J) :
    ∑ k : S × S₀ × (J → Z') × (J → Z'),
        ({k | ∃ b, ord b < ord a ∧ gCap π cell k b = gCap π cell k a} :
          Set (S × S₀ × (J → Z') × (J → Z'))).indicator (fun _ ↦ (1 : ℝ≥0∞)) k ≤
      (Fintype.card J : ℝ≥0∞) / Fintype.card Z' *
        Fintype.card (S × S₀ × (J → Z') × (J → Z')) :=
  le_div_mul_of_mul_le (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
    (card_mul_sum_slot_eq_le a _
      (fun b s _ κ w ↦ capSolve π (cell a s) (κ a) (capOf (fun _ ↦ κ b) (fun _ ↦ w) π (cell b s)))
      fun _ hk ↦ by
        obtain ⟨b, hb, he⟩ := hk
        exact ⟨b, fun h ↦ (lt_irrefl _) (h ▸ hb), eq_capSolve he.symm⟩)

end capConst

/-! ## leanXMSS's never-revealed part and its hidden families -/

section r0sets

open HashSig LeanXmss

/-- **The never-revealed part**: the scheme seed `S`, the master seed `S₀`, and R0Stage's
randomizer-base `k`-slots `κ` and `k'`-slots `κ'`. -/
abbrev RK : Type := MasterSeed × MasterSeed × (RLabel → Z) × (RLabel → Z)

/-- The randomizer-base `k`-cells at the never-revealed part: the labels' `S`-keyed first blocks. -/
def r0Kk (P : PublicParameter) (k : RK) : Set X :=
  Set.range fun a : RLabel ↦ R0.rCell a P k.1

/-- The seed paths' `k`-cells at the never-revealed part: the master seed's derivation
(`S₀`-keyed) and the parameter's and the chain starts' (`S`-keyed). -/
def seedKk (P : PublicParameter) (k : RK) : Set X :=
  Set.range (hidCell P k.1 k.2.1)

/-- The randomizer-base capacity of a label at the never-revealed part. -/
def r0Cap (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK) (a : RLabel) : Z :=
  gCap π (fun a S ↦ R0.rCell a P S) k a

/-- The randomizer-base `k'`-cells (rates) at the never-revealed part, on a good permutation. -/
def r0K'k (G : ℕ) (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK) : Set X :=
  {x | PermGood π G ∧ ∃ a : RLabel, (π (R0.rCell a P k.1, k.2.2.1 a)).1 = x}

/-- The randomizer-base `h`-cells (capacities) at the never-revealed part. -/
def r0Hk (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK) : Set Z :=
  Set.range (r0Cap π P k)

open scoped Classical in
/-- **The non-first labels** at the never-revealed part, as hidden coordinates: a label of smaller
rank has the same randomizer-base capacity. Irreducible: membership does not unfold to the
enumeration of the labels. -/
@[irreducible]
noncomputable def r0Bk (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK) : Finset HPos :=
  (Finset.univ.filter fun a : RLabel ↦
    ∃ b, R0.rOrd b < R0.rOrd a ∧ r0Cap π P k b = r0Cap π P k a).map Function.Embedding.inr

theorem mem_r0Bk {π : Equiv.Perm (X × Z)} {P : PublicParameter} {k : RK} {s : HPos} :
    s ∈ r0Bk π P k ↔
      ∃ a, s = .inr a ∧ ∃ b, R0.rOrd b < R0.rOrd a ∧ r0Cap π P k b = r0Cap π P k a := by
  unfold r0Bk
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.inr_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, rfl, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨a, ha, rfl⟩

/-- All randomizer-base coordinates. Irreducible, as `r0Bk`. -/
@[irreducible]
def rJ : Finset HPos :=
  Finset.univ.map Function.Embedding.inr

theorem inr_mem_rJ (a : RLabel) : (Sum.inr a : HPos) ∈ rJ := by
  unfold rJ
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.inr_apply]
  exact ⟨a, rfl⟩

theorem r0Bk_subset (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK) : r0Bk π P k ⊆ rJ :=
  fun s hs ↦ by
    obtain ⟨a, rfl, -⟩ := mem_r0Bk.mp hs
    exact inr_mem_rJ a

/-! ### Multiplicities over the never-revealed part -/

/-- **The seed-keyed `k`-cells**: a cell is a randomizer-base or seed path's `k`-cell for at most a
`2 / |MasterSeed|` fraction of the never-revealed part (the cell names `S` or `S₀`). -/
theorem sum_indicator_kCells_le (P : PublicParameter) (x : X) :
    ∑ k : RK, (r0Kk P k ∪ seedKk P k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      2 * (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ * Fintype.card RK :=
  sum_indicator_two_le (fun k : RK ↦ r0Kk P k ∪ seedKk P k) seedKeyCells seedCells x
    (fun k hk ↦ by
      rcases hk with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl (firstBlock_thInput_mem_seedKeyCells _ _ _ _)
      · cases b with
        | none => exact Or.inr (firstBlock_seedInput_mem_seedCells _)
        | some c => exact Or.inl (skCell_mem_seedKeyCells _ _ c))
    (sum_indicator_seedKeyCells x) (sum_indicator_seedCells x)

/-- **The randomizer-base rates**: on a `PermGood π G`, a cell is a label's rate for at most a
`|J| G / |Z|` fraction of the never-revealed part (the `k`-slot is uniform). -/
theorem sum_indicator_r0K'k_le (G : ℕ) (π : Equiv.Perm (X × Z)) (P : PublicParameter) (x : X) :
    ∑ k : RK, (r0K'k G π P k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      (Fintype.card RLabel : ℝ≥0∞) * G / Fintype.card Z * Fintype.card RK := by
  by_cases hG : PermGood π G
  · refine le_div_mul_of_mul_le (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _) (card_mul_sum_slot_le (fun k : RK ↦ r0K'k G π P k) x
        (fun a s ↦ {w | (π (R0.rCell a P s, w)).1 = x}) G (fun k hk ↦ hk.2) fun a s ↦ ?_)
    rw [← card_filter_eq_sum_indicator]
    exact_mod_cast hG.rate _ x
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem
      (fun h ↦ hG h.1) _) zero_le

/-- **The randomizer-base capacities**: a capacity is a label's for at most a `|J| / |Z|` fraction
of the never-revealed part (the `k'`-slot is uniform). -/
theorem sum_indicator_r0Hk_le (π : Equiv.Perm (X × Z)) (P : PublicParameter) (z : Z) :
    ∑ k : RK, (r0Hk π P k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      (Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z * Fintype.card RK :=
  sum_indicator_range_gCap_le π (fun a S ↦ R0.rCell a P S) z

/-- **The non-first labels**: a label is non-first for at most a `|J| / |Z|` fraction of the
never-revealed part (its `k'`-slot is uniform given the other labels'). -/
theorem card_filter_r0Bk_le (π : Equiv.Perm (X × Z)) (P : PublicParameter) (s : HPos) :
    ((Finset.univ.filter fun k : RK ↦ s ∈ r0Bk π P k).card : ℝ≥0∞) ≤
      (Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z * Fintype.card RK := by
  rw [card_filter_eq_sum_indicator]
  rcases s with q | a
  · rw [Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem (fun h ↦ by
      obtain ⟨a, ha, -⟩ := mem_r0Bk.mp (Eq.mp (Set.mem_ofPred_eq (x := k)
        (p := fun k : RK ↦ (Sum.inl q : HPos) ∈ r0Bk π P k)) h)
      exact Sum.inl_ne_inr ha) _]
    exact zero_le
  · refine le_trans (Finset.sum_le_sum fun k _ ↦ Set.indicator_le_indicator_of_subset
      (fun k hk ↦ ?_) (fun _ ↦ zero_le) k)
      (sum_indicator_notFirst_le π (fun a S ↦ R0.rCell a P S) R0.rOrd a)
    obtain ⟨a', ha', b, hb, he⟩ := mem_r0Bk.mp (Eq.mp (Set.mem_ofPred_eq (x := k)
      (p := fun k : RK ↦ (Sum.inr a : HPos) ∈ r0Bk π P k)) hk)
    obtain rfl := Sum.inr_injective ha'
    exact Eq.mpr Set.mem_ofPred_eq ⟨b, hb, he⟩

end r0sets

/-! ## The table's seed and randomizer-base cells, `covers`, and R0Stage's coordinates -/

section table

open HashSig LeanXmss

/-- The randomizer-base paths' `k`-cells of a table: the labels' first blocks. -/
def r0K (L : HonestTable) : Set X :=
  Set.range (coinCellK R0.rCell L)

/-- The randomizer-base paths' `k'`-cells of a table: the rates of the labels' first blocks. -/
def r0K' (L : HonestTable) : Set X :=
  Set.range (coinCellK' R0.rCell L)

/-- The randomizer-base paths' `h`-cells of a table: the capacities of the labels' first blocks. -/
def r0H (L : HonestTable) : Set Z :=
  Set.range (coinCellH R0.rCell L)

/-- The seed paths' `k`-cells of a table: the master seed's derivation, the parameter's and the
chain starts' first blocks (one block each). -/
def seedK (L : HonestTable) : Set X :=
  Set.range (hidCell L.param L.seed L.masterSeed)

/-- The seed paths' `k'`-cells of a table. -/
def seedK' (L : HonestTable) : Set X :=
  Set.range fun b ↦ rateOf L.keys.2.1 L.perm (hidCell L.param L.seed L.masterSeed b)

/-- The seed paths' `h`-cells of a table. -/
def seedH (L : HonestTable) : Set Z :=
  Set.range fun b ↦ capOf L.keys.2.1 L.keys.2.2 L.perm (hidCell L.param L.seed L.masterSeed b)

/-- **`covers`, widened**: a table whose cells are path cells or cells of further sets is covered
by the path cells united with those sets. -/
theorem covers_of_progs_or (W : Hw X Z) (L : HonestTable) (Eh : Set Z) (Ek Ek' : Set X)
    (hh : ∀ z, W.1 z ≠ none → (∃ a, HwProg.programH z a ∈ pathProgs L) ∨ z ∈ Eh)
    (hk : ∀ x, W.2.1 x ≠ none → (∃ a, HwProg.programK x a ∈ pathProgs L) ∨ x ∈ Ek)
    (hk' : ∀ x, W.2.2 x ≠ none → (∃ a, HwProg.programK' x a ∈ pathProgs L) ∨ x ∈ Ek') :
    Covers W (pathH L ∪ Eh) (pathK L ∪ Ek) (pathK' L ∪ Ek') :=
  ⟨hh, hk, hk'⟩

/-- **`covers` for the full table** (r0-design, section 5): a table whose cells are cells of the
honest paths, of the seed paths or of the randomizer-base paths is covered by
`pathH ∪ seedH ∪ r0H`, `pathK ∪ seedK ∪ r0K`, `pathK' ∪ seedK' ∪ r0K'`. -/
theorem covers_r0 (W : Hw X Z) (L : HonestTable)
    (hh : ∀ z, W.1 z ≠ none →
      (∃ a, HwProg.programH z a ∈ pathProgs L) ∨ z ∈ seedH L ∨ z ∈ r0H L)
    (hk : ∀ x, W.2.1 x ≠ none →
      (∃ a, HwProg.programK x a ∈ pathProgs L) ∨ x ∈ seedK L ∨ x ∈ r0K L)
    (hk' : ∀ x, W.2.2 x ≠ none →
      (∃ a, HwProg.programK' x a ∈ pathProgs L) ∨ x ∈ seedK' L ∨ x ∈ r0K' L) :
    Covers W (pathH L ∪ seedH L ∪ r0H L) (pathK L ∪ seedK L ∪ r0K L)
      (pathK' L ∪ seedK' L ∪ r0K' L) :=
  ⟨fun z hz ↦ (hh z hz).elim (fun h ↦ Or.inl (Or.inl h)) fun h ↦
      h.elim (fun h ↦ Or.inl (Or.inr h)) Or.inr,
    fun x hx ↦ (hk x hx).elim (fun h ↦ Or.inl (Or.inl h)) fun h ↦
      h.elim (fun h ↦ Or.inl (Or.inr h)) Or.inr,
    fun x hx ↦ (hk' x hx).elim (fun h ↦ Or.inl (Or.inl h)) fun h ↦
      h.elim (fun h ↦ Or.inl (Or.inr h)) Or.inr⟩

/-- **R0Stage's coordinates as the never-revealed part**: the scheme seed, the master seed, and the
`k`- and `k'`-slots of `r0Split`. -/
noncomputable def rkOf (θ : CTab RLabel) : RK :=
  ((r0Split R0.rCell R0.rOrd θ).2, θ.1.1.masterSeed, (r0Split R0.rCell R0.rOrd θ).1.2.1,
    (r0Split R0.rCell R0.rOrd θ).1.2.2.1)

variable {ι : Type} {β : ι → Type}
  {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
  {θ : CTab RLabel}

/-- On R0Stage's good set, a label's randomizer-base capacity is `r0Cap` at the coordinates. -/
theorem coinCellH_eq_r0Cap (hθ : θ ∈ r0Good R0.rCell R0.rOrd Q) (a : RLabel) :
    coinCellH R0.rCell θ.1.1 a = r0Cap θ.1.1.perm θ.1.1.param (rkOf θ) a := by
  obtain ⟨-, h1, h2, -, -⟩ := r0Split_coords R0.rCell_injective hθ
  have hS := r0Split_snd R0.rCell R0.rOrd θ
  show _ = capOf (fun _ ↦ (r0Split R0.rCell R0.rOrd θ).1.2.1 a)
    (fun _ ↦ (r0Split R0.rCell R0.rOrd θ).1.2.2.1 a) θ.1.1.perm
    (R0.rCell a θ.1.1.param (r0Split R0.rCell R0.rOrd θ).2)
  rw [h1 a, h2 a, hS]
  rfl

/-- **The table's randomizer-base and seed cells on R0Stage's good set** are the never-revealed
families at R0Stage's coordinates (the rates on a `PermGood π G`). -/
theorem r0Good_subsets (G : ℕ) (hθ : θ ∈ r0Good R0.rCell R0.rOrd Q)
    (hG : PermGood θ.1.1.perm G) :
    r0H θ.1.1 ⊆ r0Hk θ.1.1.perm θ.1.1.param (rkOf θ) ∧
      r0K θ.1.1 ⊆ r0Kk θ.1.1.param (rkOf θ) ∧
      r0K' θ.1.1 ⊆ r0K'k G θ.1.1.perm θ.1.1.param (rkOf θ) ∧
      seedK θ.1.1 ⊆ seedKk θ.1.1.param (rkOf θ) := by
  obtain ⟨-, h1, -, -, -⟩ := r0Split_coords R0.rCell_injective hθ
  have hS := r0Split_snd R0.rCell R0.rOrd θ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨a, (coinCellH_eq_r0Cap hθ a).symm⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    show R0.rCell a θ.1.1.param (r0Split R0.rCell R0.rOrd θ).2 = _
    rw [hS]
    rfl
  · rintro _ ⟨a, rfl⟩
    refine ⟨hG, a, ?_⟩
    show (θ.1.1.perm (R0.rCell a θ.1.1.param (r0Split R0.rCell R0.rOrd θ).2,
      (r0Split R0.rCell R0.rOrd θ).1.2.1 a)).1 = _
    rw [h1 a, hS]
    rfl
  · rintro _ ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    show hidCell θ.1.1.param (r0Split R0.rCell R0.rOrd θ).2 θ.1.1.masterSeed b = _
    rw [hS]

/-- **The non-first labels on R0Stage's good set** are `r0Bk` at the coordinates. -/
theorem mem_r0B_iff (hθ : θ ∈ r0Good R0.rCell R0.rOrd Q) (a : RLabel) :
    a ∈ r0B R0.rCell R0.rOrd θ.1.1 ↔
      (Sum.inr a : HPos) ∈ r0Bk θ.1.1.perm θ.1.1.param (rkOf θ) := by
  rw [mem_r0Bk]
  show (∃ b, R0.rOrd b < R0.rOrd a ∧ coinCellH R0.rCell θ.1.1 b = coinCellH R0.rCell θ.1.1 a) ↔ _
  simp only [coinCellH_eq_r0Cap hθ]
  constructor
  · rintro ⟨b, hb, he⟩
    exact ⟨a, rfl, b, hb, he⟩
  · rintro ⟨a', ha, b, hb, he⟩
    obtain rfl := Sum.inr_injective ha
    exact ⟨b, hb, he⟩

/-- **The randomizer bases of the first labels are R0Stage's coordinates** (`r0Coord`), so the
table's hidden values and the coordinates agree off the non-first labels. -/
theorem valueAt_inr_eq_r0Coord (hθ : θ ∈ r0Good R0.rCell R0.rOrd Q) (a : RLabel)
    (ha : (Sum.inr a : HPos) ∉ r0Bk θ.1.1.perm θ.1.1.param (rkOf θ)) :
    valueAt θ.1.1 (.inr a) = r0Coord (r0Split R0.rCell R0.rOrd θ).1 a := by
  rw [valueAt_inr]
  have h := R0.randomizerBase_eq_r0Coord hθ a fun h ↦ ha ((mem_r0B_iff hθ a).mp h)
  cases a <;> exact h

end table

/-! ## The recorded randomizer bases (`hR`): two per signing request -/

section cand

open HashSig LeanXmss Common Common.SufCma

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

theorem inl_notMem_rJ (p : ValPos) : (Sum.inl p : HPos) ∉ rJ := by
  unfold rJ
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.inr_apply]
  exact fun ⟨_, h⟩ ↦ Sum.inr_ne_inl h

theorem card_inlSet_inter_rJ (T : Finset ValPos) : (inlSet T ∩ rJ).card = 0 := by
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun s hs ↦ ?_)
  obtain ⟨hs₁, hs₂⟩ := Finset.mem_inter.mp hs
  unfold inlSet at hs₁
  obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hs₁
  exact inl_notMem_rJ p hs₂

theorem card_singleton_inl_inter_rJ (p : ValPos) : (({.inl p} : Finset HPos) ∩ rJ).card = 0 :=
  Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun s hs ↦ by
    obtain ⟨hs₁, hs₂⟩ := Finset.mem_inter.mp hs
    rw [Finset.mem_singleton.mp hs₁] at hs₂
    exact inl_notMem_rJ p hs₂)

theorem card_singleton_inter_rJ_le (s : HPos) : (({s} : Finset HPos) ∩ rJ).card ≤ 1 :=
  (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton s)

variable (M) in
/-- The template charge counting the randomizer-base coordinates a reveal records. -/
def tCand : (XSpec M).Port → ℕ
  | .inl _ => 0
  | .inr T => (T ∩ rJ).card

omit [Fintype M] [DecidableEq M] in
theorem isChargeBound_realizeT_cand (v : HPos → Digest) {A : QReg}
    {y : QuantumComp L (XSpec M) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tCand M)) n) :
    IFreeM.IsChargeBound (realizeT v y) (portCharge (candCharge X Z M rJ)) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens v) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (candCharge X Z M rJ) s
      ((tmplLens v).toFunA s cmd)) = portCharge (tCand M) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem isChargeBound_readLift_cand {A : QReg} {y : QuantumComp L (hwReadSpec X Z M) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (rdCharge M 0 0)) n) :
    IFreeM.IsChargeBound (readLift goodAll y) (portCharge (tCand M)) n := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodAll) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (tCand M) s
      ((readLens goodAll).toFunA s cmd)) = portCharge (rdCharge M 0 0) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem chg_revealThen_cand {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tCand M)) n) :
    IFreeM.IsChargeBound (revealThen goodAll T k) (portCharge (tCand M))
      ((T ∩ rJ).card + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr
    ⟨Nat.le_add_right _ n, fun r ↦ ?_⟩
  simp only [tCand, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk r) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progThen_cand {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) {n : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (tCand M)) n) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (tCand M)) n := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.zero_le n, fun r ↦ ?_⟩
  simp only [tCand, Nat.sub_zero]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progPorts_cand (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    IFreeM.IsChargeBound (progPorts M B ps) (portCharge (tCand M)) 0 := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact chg_progThen_cand p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem chg_progSlots_cand (pub : Pub) (B : QReg) (ss : List Slot) :
    IFreeM.IsChargeBound (progSlots M pub B ss) (portCharge (tCand M)) 0 := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact FreeM₂.isChargeBound_bind (n₁ := 0) (chg_progPorts_cand B _) fun _ ↦ ih

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature records one randomizer base.** -/
theorem chg_signLayerT_cand (pub : Pub) (B : QReg) (lab : RLabel) :
    IFreeM.IsChargeBound (signLayerT M upd pub B lab) (portCharge (tCand M)) 1 := by
  unfold signLayerT
  refine IFreeM.IsChargeBound.mono (chg_revealThen_cand (n := 0) _ _ fun _ ↦ ?_)
    (by rw [Nat.add_zero]; exact card_singleton_inter_rJ_le _)
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_readLift_cand
    (IFreeM.IsChargeBound.mono (chg_grindR 0 0 upd pub B lab.layer lab.key
      (RLabel.length_msg_le lab) _ _ _) (by simp))) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · trivial
  · refine IFreeM.IsChargeBound.mono (chg_revealThen_cand (n := 0) _ _ fun r ↦
      FreeM₂.isChargeBound_bind (n₂ := 0) (chg_progSlots_cand pub B _) fun _ ↦ trivial) ?_
    rw [card_inlSet_inter_rJ]

omit [Fintype M] [DecidableEq M] in
/-- **A signature records two randomizer bases.** -/
theorem chg_signT_cand (pub : Pub) (B : QReg) (r : SigningRequest) :
    IFreeM.IsChargeBound (signT M upd pub B r) (portCharge (tCand M)) 2 := by
  unfold signT
  refine FreeM₂.isChargeBound_bind (n₁ := 1) (n₂ := 1) (chg_signLayerT_cand upd pub B _)
    fun t ↦ ?_
  rcases t with _ | ⟨bottom, f⟩
  · trivial
  · refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
      (chg_signLayerT_cand upd pub B _) fun t ↦ ?_) le_rfl
    rcases t with _ | ⟨top, _⟩ <;> trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenger's recorded randomizer bases per command: two per signing request. -/
theorem chg_challengeT_cand (pub : Pub) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    IFreeM.IsChargeBound (challengeT M upd pub A cmd) (portCharge (tCand M))
      (advCharge 0 2 A cmd) := by
  rcases cmd with o | ⟨p | r, E, ℓ⟩
  · refine IFreeM.IsChargeBound.mono (isChargeBound_readLift_cand (isChargeBound_simulate 0 0
      _ (q := 0) ((QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial))) ?_
    simp [advCharge, cmdCharge]
  · refine IFreeM.IsChargeBound.mono (isChargeBound_readLift_cand (isChargeBound_simulate 0 0
      _ (q := 1) ((QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ trivial⟩))) ?_
    simp only [advCharge, cmdCharge, permCharge, signCharge]
    omega
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (FreeM₂.isChargeBound_bind
      (n₁ := 0) (chg_act _ _ 0) fun _ ↦ chg_signT_cand upd pub _ r) fun _ _ ↦
        IFreeM.isChargeBound_pure _ 0) ?_
    simp only [advCharge, cmdCharge, permCharge, signCharge]
    omega

omit [Fintype M] [DecidableEq M] in
/-- **`hR`**: the realized game records at most `2 · lifetime` randomizer-base coordinates, for an
adversary making at most `lifetime` signing requests on every path. -/
theorem hR_gameT (A : Adversary (X × Z)) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (pub : Pub) (v : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pub A)) (portCharge (candCharge X Z M rJ))
      (2 * lifetime) := by
  refine isChargeBound_realizeT_cand v ?_
  refine IFreeM.IsChargeBound.mono (chg_revealThen_cand _ _ fun r₀ ↦ ?_)
    (le_of_eq (by rw [card_singleton_inl_inter_rJ, Nat.zero_add]))
  have hx := IFreeM.IsChargeBound.add
    ((isChargeBound_withSignLog (hperm ⟨extendVals r₀.1 rootPos, pub.param⟩)).mul 0)
    ((isChargeBound_withSignLog (hsign ⟨extendVals r₀.1 rootPos, pub.param⟩)).mul 2)
  have hh : ∀ s (cmd : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))).A s),
      IFreeM.IsChargeBound (challengeT M upd pub s cmd) (portCharge (tCand M))
        (advCharge 0 2 s cmd) :=
    chg_challengeT_cand upd pub
  have hc := IFreeM.IsChargeBound.substitute (challengeT M upd pub) hh hx
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0) hc fun run ↦ ?_)
    (by omega)
  have hv := chg_readsProgram (M := M) 0 0 pub.perm (QReg.of Unit)
    (verify_cost' ⟨extendVals r₀.1 rootPos, pub.param⟩ run.1)
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (isChargeBound_readLift_cand (IFreeM.IsChargeBound.mono (chg_map _ Prod.fst hv) (by simp)))
    fun _ ↦ trivial

end cand

/-! ## The bounds for leanXMSS -/

section xmssR0

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The per-call multiplicity of the never-revealed families**: `2 / |MasterSeed|` for the `S`-
and `S₀`-keyed `k`-cells, `|J| G / |Z|` for the randomizer-base rates, `|J| / |Z|` for the
randomizer-base capacities. -/
noncomputable def r0Eps (G : ℕ) : ℝ≥0∞ :=
  2 * (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ + (Fintype.card RLabel : ℝ≥0∞) * G / Fintype.card Z +
    (Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z

/-- **The averaged total hidden mass at the ports `Q` for leanXMSS's full table** (path, seed and
randomizer-base cells), at most `N (2^-128 + εA + r0Eps G + R |J| / |Z|)` plus `N` times the bad
fraction.

Data and hypotheses left: the reparametrization `e` of the padded table into public data `P`,
hidden values and the never-revealed part `RK × W` (injective on the good set `G`, `hcard`), the
public datum `pubP` with its parameter `parP` and permutation `permP`; on `G`: the game at the
table is the template game at `pubP` realized at hidden values agreeing with the coordinate off
the non-first labels (`hgame`), the honest paths' cells are the template's hidden cells at the
coordinate (`hpath`), and the randomizer-base and seed cells are the never-revealed families
(`hr0`, from `r0Good_subsets`; `hseed`). The seed paths' `k'`- and `h`-cells (`seedK'k`, `seedHk`)
have multiplicity `εA` (`hA`, `hA'`); every path records at most `R` randomizer-base coordinates
(`hR`; `2 · lifetime` by `hR_gameT`); at most `N` calls of the ports `Q` (`hN`). The sources
(`sourcesSlotInv`), the invariant
(`hinv_gameT`), the reads keeping the label (`keepsLab_gameT`) and the multiplicities of the
randomizer-base families and of the `S`-, `S₀`-keyed `k`-cells are discharged. -/
theorem uavg_totalWeight_portMass_le_xmssR0 (Q : (recHwSpec X Z HPos M).Port → Prop)
    [DecidablePred Q] (hQ : ∀ c, ¬Q (.inl (.inr c))) (A : Adversary (X × Z))
    (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    {E P W : Type} [Fintype E] [Nonempty E] [Fintype P] [Fintype W]
    (e : HonestTable × E → P × ((HPos → Digest) × (RK × W))) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × (RK × W)) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (parP : P → PublicParameter) (permP : P → Equiv.Perm (X × Z)) (Gπ : ℕ)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permP (e t).1) (parP (e t).1) (e t).2.2.1) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (hpath : ∀ t, G t →
      pathH t.1 ⊆ hidH (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK t.1 ⊆ hidK (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK' t.1 ⊆ hidK' (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)))
    (hr0 : ∀ t, G t →
      r0H t.1 ⊆ r0Hk (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      r0K t.1 ⊆ r0Kk (parP (e t).1) (e t).2.2.1 ∧
      r0K' t.1 ⊆ r0K'k Gπ (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      seedK t.1 ⊆ seedKk (parP (e t).1) (e t).2.2.1)
    (seedHk : P → RK × W → Set Z) (seedK'k : P → RK × W → Set X) (εA : ℝ≥0∞)
    (hseed : ∀ t, G t → seedH t.1 ⊆ seedHk (e t).1 (e t).2.2 ∧
      seedK' t.1 ⊆ seedK'k (e t).1 (e t).2.2)
    (hA : ∀ p z, ∑ k, (seedHk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εA * Fintype.card (RK × W))
    (hA' : ∀ p y, ∑ k, (seedK'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εA * Fintype.card (RK × W))
    {R : ℕ} (hR : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A)) (portCharge (candCharge X Z M rJ)) R)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if Q i then 1 else 0) N) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass Q (pathH L ∪ seedH L ∪ r0H L) (pathK L ∪ seedK L ∪ r0K L)
        (pathK' L ∪ seedK' L ∪ r0K' L)) (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      N * ((2 ^ 128 : ℝ≥0∞)⁻¹ + (εA + r0Eps Gπ) +
          R * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) +
        N * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun t ↦ ¬G t).card) := by
  have e1 : (Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z ≤ r0Eps Gπ := le_add_self
  have e2 : 2 * (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ ≤ εA + r0Eps Gπ :=
    (le_self_add.trans le_self_add).trans le_add_self
  have e3 : (Fintype.card RLabel : ℝ≥0∞) * Gπ / Fintype.card Z ≤ r0Eps Gπ :=
    le_add_self.trans le_self_add
  have h := uavg_totalWeight_portMass_le_r0 upd Q A m₀ ρ hρ hρ1 hs
    (fun L ↦ pathH L ∪ seedH L ∪ r0H L) (fun L ↦ pathK L ∪ seedK L ∪ r0K L)
    (fun L ↦ pathK' L ∪ seedK' L ∪ r0K' L) e G hinj hcard pubP
    (fun p k ↦ r0Bk (permP p) (parP p) k.1) hgame
    (fun p v ↦ hidH (pubP p) fun q ↦ v (.inl q)) (fun p v ↦ hidK (pubP p) fun q ↦ v (.inl q))
    (fun p v ↦ hidK' (pubP p) fun q ↦ v (.inl q))
    (fun p k ↦ r0Hk (permP p) (parP p) k.1 ∪ seedHk p k)
    (fun p k ↦ r0Kk (parP p) k.1 ∪ seedKk (parP p) k.1)
    (fun p k ↦ r0K'k Gπ (permP p) (parP p) k.1 ∪ seedK'k p k)
    (fun t ht ↦ by
      obtain ⟨p1, p2, p3⟩ := hpath t ht
      obtain ⟨r1, r2, r3, r4⟩ := hr0 t ht
      obtain ⟨s1, s2⟩ := hseed t ht
      refine ⟨?_, ?_, ?_⟩
      · rintro z ((hz | hz) | hz)
        exacts [Or.inl (p1 hz), Or.inr (Or.inr (s1 hz)), Or.inr (Or.inl (r1 hz))]
      · rintro x ((hx | hx) | hx)
        exacts [Or.inl (p2 hx), Or.inr (Or.inr (r4 hx)), Or.inr (Or.inl (r2 hx))]
      · rintro x ((hx | hx) | hx)
        exacts [Or.inl (p3 hx), Or.inr (Or.inr (s2 hx)), Or.inr (Or.inl (r3 hx))])
    (fun p v ↦ SlotInv M (pubP p) v) (hinv_gameT upd pubP hQ m₀ A ρ hs) _
    (fun p ↦ sourcesSlotInv M (pubP p)) (εA + r0Eps Gπ)
    (fun p z ↦ (sum_indicator_union_le _ _ z).trans <| (add_le_add (sum_indicator_pad_le
      (fun k : RK ↦ r0Hk (permP p) (parP p) k) z _ (sum_indicator_r0Hk_le _ _ z)) (hA p z)).trans
      (add_mul_le_add_mul e1 le_rfl))
    (fun p y ↦ (sum_indicator_pad_le (fun k : RK ↦ r0Kk (parP p) k ∪ seedKk (parP p) k) y _
      (sum_indicator_kCells_le _ y)).trans (mul_le_mul_of_nonneg_right e2 zero_le))
    (fun p y ↦ (sum_indicator_union_le _ _ y).trans <| (add_le_add (sum_indicator_pad_le
      (fun k : RK ↦ r0K'k Gπ (permP p) (parP p) k) y _ (sum_indicator_r0K'k_le _ _ _ y))
      (hA' p y)).trans (add_mul_le_add_mul e3 le_rfl))
    rJ (fun p k ↦ r0Bk_subset _ _ _) ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)
    (fun p s _ ↦ le_of_eq_of_le (card_filter_pad (W := W)
      (fun k : RK ↦ s ∈ r0Bk (permP p) (parP p) k))
      ((mul_le_mul_of_nonneg_right (card_filter_r0Bk_le _ _ s) zero_le).trans_eq
        (by rw [mul_assoc, ← Nat.cast_mul, ← Fintype.card_prod]))) hR hN
  rwa [card_digest_inv] at h

/-- **`hybSponge` for leanXMSS's full table**: the averaged total hidden mass at the sponge ports,
for an adversary with at most `q` permutation calls and `lifetime` signing requests, is at most
`6q (2^-128 + εA + r0Eps G + 2 lifetime |J| / |Z|)` plus `6q` times the bad fraction. -/
theorem uavg_spongeMass_le_xmssR0 (A : Adversary (X × Z)) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    {E P W : Type} [Fintype E] [Nonempty E] [Fintype P] [Fintype W]
    (e : HonestTable × E → P × ((HPos → Digest) × (RK × W))) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × (RK × W)) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (parP : P → PublicParameter) (permP : P → Equiv.Perm (X × Z)) (Gπ : ℕ)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permP (e t).1) (parP (e t).1) (e t).2.2.1) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (hpath : ∀ t, G t →
      pathH t.1 ⊆ hidH (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK t.1 ⊆ hidK (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK' t.1 ⊆ hidK' (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)))
    (hr0 : ∀ t, G t →
      r0H t.1 ⊆ r0Hk (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      r0K t.1 ⊆ r0Kk (parP (e t).1) (e t).2.2.1 ∧
      r0K' t.1 ⊆ r0K'k Gπ (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      seedK t.1 ⊆ seedKk (parP (e t).1) (e t).2.2.1)
    (seedHk : P → RK × W → Set Z) (seedK'k : P → RK × W → Set X) (εA : ℝ≥0∞)
    (hseed : ∀ t, G t → seedH t.1 ⊆ seedHk (e t).1 (e t).2.2 ∧
      seedK' t.1 ⊆ seedK'k (e t).1 (e t).2.2)
    (hA : ∀ p z, ∑ k, (seedHk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εA * Fintype.card (RK × W))
    (hA' : ∀ p y, ∑ k, (seedK'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εA * Fintype.card (RK × W)) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (spongeMass (pathH L ∪ seedH L ∪ r0H L) (pathK L ∪ seedK L ∪ r0K L)
        (pathK' L ∪ seedK' L ∪ r0K' L)) (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      ((6 * q : ℕ) : ℝ≥0∞) * ((2 ^ 128 : ℝ≥0∞)⁻¹ + (εA + r0Eps Gπ) +
          ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) +
        ((6 * q : ℕ) : ℝ≥0∞) * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun t ↦ ¬G t).card) := by
  have hc : (fun i ↦ if extCls X Z (Finset HPos × M) (recSpec HPos M) i then 0 else 1) =
      fun i ↦ if extCls X Z (Finset HPos × M) (recSpec HPos M) i = false then 1 else 0 :=
    funext fun i ↦ by cases extCls X Z (Finset HPos × M) (recSpec HPos M) i <;> rfl
  exact uavg_totalWeight_portMass_le_xmssR0 upd
    (fun i ↦ extCls X Z (Finset HPos × M) (recSpec HPos M) i = false)
    (fun _ h ↦ Bool.noConfusion h) A m₀ ρ hρ hρ1 hs e G hinj hcard pubP parP permP Gπ hgame
    hpath hr0 seedHk seedK'k εA hseed hA hA' (hR_gameT upd A hperm hsign) fun pub v ↦ by
      rw [← hc]
      exact hN_sponge upd A hperm hsign pub v

/-- **`hybRead` for leanXMSS's full table**: the averaged total hidden mass at the read ports is
at most `clsCap (2^-128 + εA + r0Eps G + 2 lifetime |J| / |Z|)` plus `clsCap` times the bad
fraction, with `clsCap = 3 (signBlocks · lifetime + verifyBlocks) + 2 progCap` (GameTCalls'
`hN_readRec`). -/
theorem uavg_readMass_le_xmssR0 (A : Adversary (X × Z)) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    {E P W : Type} [Fintype E] [Nonempty E] [Fintype P] [Fintype W]
    (e : HonestTable × E → P × ((HPos → Digest) × (RK × W))) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × (RK × W)) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (parP : P → PublicParameter) (permP : P → Equiv.Perm (X × Z)) (Gπ : ℕ)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permP (e t).1) (parP (e t).1) (e t).2.2.1) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (hpath : ∀ t, G t →
      pathH t.1 ⊆ hidH (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK t.1 ⊆ hidK (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK' t.1 ⊆ hidK' (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)))
    (hr0 : ∀ t, G t →
      r0H t.1 ⊆ r0Hk (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      r0K t.1 ⊆ r0Kk (parP (e t).1) (e t).2.2.1 ∧
      r0K' t.1 ⊆ r0K'k Gπ (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      seedK t.1 ⊆ seedKk (parP (e t).1) (e t).2.2.1)
    (seedHk : P → RK × W → Set Z) (seedK'k : P → RK × W → Set X) (εA : ℝ≥0∞)
    (hseed : ∀ t, G t → seedH t.1 ⊆ seedHk (e t).1 (e t).2.2 ∧
      seedK' t.1 ⊆ seedK'k (e t).1 (e t).2.2)
    (hA : ∀ p z, ∑ k, (seedHk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εA * Fintype.card (RK × W))
    (hA' : ∀ p y, ∑ k, (seedK'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εA * Fintype.card (RK × W)) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (readMass (pathH L ∪ seedH L ∪ r0H L) (pathK L ∪ seedK L ∪ r0K L)
        (pathK' L ∪ seedK' L ∪ r0K' L)) (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      ((3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap : ℕ) : ℝ≥0∞) *
          ((2 ^ 128 : ℝ≥0∞)⁻¹ + (εA + r0Eps Gπ) +
            ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) +
        ((3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap : ℕ) : ℝ≥0∞) *
          ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
            (Finset.univ.filter fun t ↦ ¬G t).card) := by
  simp only [readMass_eq_portMass]
  exact uavg_totalWeight_portMass_le_xmssR0 upd (fun i ↦ readRecPort M i = true)
    (fun c ↦ readRecPort_prog c) A m₀ ρ hρ hρ1 hs e G hinj hcard pubP parP permP Gπ hgame hpath
    hr0 seedHk seedK'k εA hseed hA hA' (hR_gameT upd A hperm hsign)
    (hN_readRec upd A hperm hsign)

end xmssR0

/-! ## The constants at Keccak's sizes -/

section keccak

open HashSig LeanXmss

set_option exponentiation.threshold 4096 in
/-- The randomizer-base labels (Template's `RLabel`, whose `Fintype` instance is this file's). -/
theorem card_tmplRLabel : Fintype.card RLabel = 2 ^ 288 + 2 ^ 160 := by
  simp only [RLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, R0.card_bitVec_eq]
  norm_num [lifetime, layerCount, layerHeight, digestBits]

set_option exponentiation.threshold 4096 in
/-- **The never-revealed families at Keccak's sizes** (`G = 18`): `r0Eps 18 ≤ 2^-219`
(`2 · 2^-256 + 19 |J| / |Z|`, `|J| = 2^288 + 2^160`). -/
theorem r0Eps_le_keccak : r0Eps 18 ≤ ENNReal.ofReal (1 / 2 ^ 219) := by
  have h1 : 2 * (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ =
      ((2 : ℕ) : ℝ≥0∞) / (Fintype.card MasterSeed : ℕ) := by
    rw [div_eq_mul_inv, Nat.cast_ofNat]
  have h2 : (Fintype.card RLabel : ℝ≥0∞) * ((18 : ℕ) : ℝ≥0∞) / Fintype.card Z =
      ((Fintype.card RLabel * 18 : ℕ) : ℝ≥0∞) / Fintype.card Z := by
    rw [Nat.cast_mul]
  unfold r0Eps
  rw [h1, h2, R0.natCast_div_eq_ofReal _ _ Fintype.card_pos,
    R0.natCast_div_eq_ofReal _ _ Fintype.card_pos, R0.natCast_div_eq_ofReal _ _ Fintype.card_pos,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [card_masterSeed, card_tmplRLabel, R0.card_cap]
  push_cast
  norm_num

set_option exponentiation.threshold 4096 in
/-- **The mismatch term at Keccak's sizes**: with `R = 2 · lifetime` recorded randomizer bases,
`R |J| / |Z| ≤ 2^-190`. -/
theorem revTerm_le_keccak :
    ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z) ≤
      ENNReal.ofReal (1 / 2 ^ 190) := by
  rw [← mul_div_assoc, ← Nat.cast_mul, R0.natCast_div_eq_ofReal _ _ Fintype.card_pos]
  apply ENNReal.ofReal_le_ofReal
  rw [card_tmplRLabel, R0.card_cap]
  push_cast
  norm_num [lifetime, layerCount, layerHeight]

end keccak

end Quantum.Xmss.Assembly

end
