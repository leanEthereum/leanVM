module

public import Quantum.Qrom.CellEvent
public import Quantum.Qrom.Regroup
public import Quantum.Qrom.Sphincs.Slots
public import Quantum.Sphincs.CoverStream

@[expose] public section

/-!
# The FORS coverage event on the regrouped `H_msg` cells

After regrouping (`Quantum.Qrom.Regroup` with `hmsgRoute`) the oracle is a uniform function
`F : HashDomain → Y × Y`, `Y = HashOutput`, and the cell `x₀ = p ‖ BE_32(0)` of an `H_msg` prefix
`p` holds both digest calls: call 0 in the first component, call 1 in the second
(`regroup_messageDigestInput`). The FORS view of the cell is `pairView (F x₀)`, the statement's
`digestView` of the two calls (`pairCalls`).

* `card_fiber_pairView`: every view has `2^246` pairs. `card_covPairs`: the pairs covered by `S`
  number `2^246 · coverMass S`, so their fraction is exactly `price S` (`covFrac_eq`).
* **Cov** (`covTgt S`, `CovBad S`): a call-0 `H_msg` cell that is not hardwired hits when its pair
  is covered by `S`. Graded-bound hypotheses: `upClosed_slice_covBad`, `not_mem_covBad_start`,
  `freshBound_slice_covBad` (fresh fraction `price S`). Hardwiring any cell flips nothing
  (`not_mem_covBad_programH`, `flipCost_programH_covBad_eq_zero`), nor does reading a cell
  without a target (`not_mem_covBad_readH`). More disclosures, more hits (`covBad_mono`).
* **S★** (`starCover d`, the disclosures of a stream `d` of pairs): its mean price at
  `signatureLimit` entries is at most `rhoCov / 2^128`, `rhoCov = 1.4726`
  (`uavg_price_starCover_le`, from `Quantum.Sphincs.Coverage`'s certificate).
* **Minkowski over S★**: with the per-call instability `ε = 2^-128 + price S★` (the largest
  fresh fraction is at most the sum), the mean of `(a + √(c ε))²` is at most
  `(a + √(c (2^-128 + rhoCov / 2^128)))²` (`uavg_sq_add_sqrt_starCover_le`, by Jensen
  `uavg_sq_add_rpow_le`); `uavg_sq_add_sqrt_starCover_table_le` averages over a table holding
  the stream at injective positions (`uavg_comp_restrict`).
-/

open Finset
open scoped ENNReal ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (View Disclosures Covered coverMass price card_covered revealed digestView
  messageDigestInput card_fiber_digestView streamCover card_digestPair digestCall_cases
  digestCall_one_ne_zero covered_mono rhoCov uavg_price_stream_le uavg_comp_equiv)
open Quantum.Xmss.Hybrid (uavg uavg_sqrt_le uavg_add uavg_const_mul)

namespace Quantum.Qrom.Sphincs

open Quantum.Sponge

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/-! ## The two digest calls in one cell -/

section pairs

variable {Y : Type}

/-- The outputs of the two `H_msg` calls held by a regrouped cell: call 0 in the first component,
call 1 in the second. -/
def pairCalls (ω : Y × Y) : DigestCall → Y :=
  fun i ↦ if i = 0 then ω.1 else ω.2

theorem pairCalls_zero (ω : Y × Y) : pairCalls ω 0 = ω.1 :=
  ite_eq_left rfl

theorem pairCalls_one (ω : Y × Y) : pairCalls ω 1 = ω.2 :=
  ite_eq_right digestCall_one_ne_zero

/-- A pair is the outputs of the two calls. -/
def pairCallsEquiv : (Y × Y) ≃ (DigestCall → Y) where
  toFun := pairCalls
  invFun o := (o 0, o 1)
  left_inv ω := by
    change (pairCalls ω 0, pairCalls ω 1) = ω
    rw [pairCalls_zero, pairCalls_one]
  right_inv o := by
    funext i
    rcases digestCall_cases i with rfl | rfl
    · exact pairCalls_zero _
    · exact pairCalls_one _

/-- **The regrouped digest calls**: against `regroup hmsgRoute F`, the two `H_msg` calls of a
prefix answer the pair `F (x 0)` of the call-0 cell. -/
theorem regroup_messageDigestInput (F : Qrom.HashDomain → Y × Y) (randomizer : Randomizer)
    (publicSeed : PublicParameter) (root : Digest) (message : Message)
    {x : DigestCall → Qrom.HashDomain}
    (hx : ∀ i, encodeInput (messageDigestInput randomizer publicSeed root message i) = some (x i))
    (i : DigestCall) : regroup hmsgRoute F (x i) = pairCalls (F (x 0)) i := by
  rcases digestCall_cases i with rfl | rfl
  · rw [pairCalls_zero]
    refine regroup_apply_of_fixed (hmsgRoute_of_ne ?_) F
    rw [hmsgCall_of_encodeInput_eq_some (hx 0), hmsgCallOf_messageDigestInput]
    exact fun h ↦ digestCall_one_ne_zero (Option.some_injective _ h).symm
  · rw [pairCalls_one]
    exact regroup_apply_of_second (hmsgRoute_messageDigestInput _ _ _ _ (hx 0) (hx 1)) F

end pairs

/-! ## Views and the price -/

/-- The FORS view of a regrouped pair, as the statement reads it from the two calls. -/
def pairView (ω : HashOutput × HashOutput) : View :=
  digestView (pairCalls ω)

/-- The view of the regrouped digest calls of a prefix is that of its call-0 cell's pair. -/
theorem digestView_regroup (F : Qrom.HashDomain → HashOutput × HashOutput)
    (randomizer : Randomizer) (publicSeed : PublicParameter) (root : Digest) (message : Message)
    {x : DigestCall → Qrom.HashDomain}
    (hx : ∀ i, encodeInput (messageDigestInput randomizer publicSeed root message i) = some (x i)) :
    digestView (fun i ↦ regroup hmsgRoute F (x i)) = pairView (F (x 0)) :=
  congrArg digestView (funext (regroup_messageDigestInput F randomizer publicSeed root message hx))

theorem card_pair : Fintype.card (HashOutput × HashOutput) = 2 ^ 246 * 2 ^ 266 :=
  (Fintype.card_congr pairCallsEquiv).trans card_digestPair

/-- **Each view has `2^246` pairs.** -/
theorem card_fiber_pairView (w : View) :
    #(univ.filter fun ω : HashOutput × HashOutput ↦ pairView ω = w) = 2 ^ 246 := by
  rw [← card_fiber_digestView w]
  exact card_equiv pairCallsEquiv fun ω ↦ by
    simp only [mem_filter, mem_univ, true_and]
    rfl

/-- The pairs whose view is covered by `S`: `2^246` per covered view. -/
theorem card_covPairs (S : Disclosures) :
    #(univ.filter fun ω : HashOutput × HashOutput ↦ Covered S (pairView ω)) =
      2 ^ 246 * coverMass S := by
  have hfib : ∀ w ∈ univ.filter (Covered S),
      #((univ.filter fun ω : HashOutput × HashOutput ↦ Covered S (pairView ω)).filter
        fun ω ↦ pairView ω = w) = 2 ^ 246 := by
    intro w hw
    rw [← card_fiber_pairView w]
    refine congrArg card (Finset.ext fun ω ↦ ?_)
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨And.right, fun h ↦ ⟨h ▸ (mem_filter.1 hw).2, h⟩⟩
  rw [card_eq_sum_card_fiberwise (f := pairView) (t := univ.filter (Covered S))
      fun ω hω ↦ mem_filter.2 ⟨mem_univ _, (mem_filter.1 hω).2⟩,
    sum_congr rfl hfib, sum_const, smul_eq_mul, card_covered]
  exact Nat.mul_comm _ _

/-- **The fraction of covered pairs is the price** of the disclosures. -/
theorem covFrac_eq (S : Disclosures) :
    (#(univ.filter fun ω : HashOutput × HashOutput ↦ Covered S (pairView ω)) : ℝ≥0∞) /
      Fintype.card (HashOutput × HashOutput) = ENNReal.ofReal (price S) := by
  have hp : ((price S : ℚ) : ℝ) = (coverMass S : ℝ) / 2 ^ 266 := by
    rw [price]
    push_cast
    rfl
  rw [card_covPairs, card_pair, Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_div_mul_left _ _ (by positivity) (ENNReal.natCast_ne_top _), hp,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]

/-! ## The Cov event -/

section event

variable {M : Type}

/-- **The Cov target**: a call-0 `H_msg` cell that is not hardwired is hit when its pair of
outputs has a FORS view covered by `S`; the other cells have no target. -/
def covTgt (S : Disclosures) (W : Hw (HashOutput × HashOutput) Qrom.HashDomain) (_m : M)
    (x : Qrom.HashDomain) : Set (HashOutput × HashOutput) :=
  {ω | hmsgCall x = some 0 ∧ W.1 x = none ∧ Covered S (pairView ω)}

theorem mem_covTgt {S : Disclosures} {W : Hw (HashOutput × HashOutput) Qrom.HashDomain} {m : M}
    {x : Qrom.HashDomain} {ω : HashOutput × HashOutput} :
    ω ∈ covTgt S W m x ↔ hmsgCall x = some 0 ∧ W.1 x = none ∧ Covered S (pairView ω) :=
  Iff.rfl

/-- **The Cov event**: some recorded call-0 `H_msg` cell, not hardwired, has a covered pair. -/
abbrev CovBad (S : Disclosures) : Set (RomReg Qrom.HashDomain (HashOutput × HashOutput) M) :=
  CellTargetBad (covTgt S)

variable {S : Disclosures}

theorem mem_covBad_iff {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) M} :
    s ∈ CovBad S ↔ ∃ x ω, unionH s x = some ω ∧ hmsgCall x = some 0 ∧ s.2.1.1 x = none ∧
      Covered S (pairView ω) :=
  Iff.rfl

/-- More disclosures, more hits. -/
theorem covBad_mono {T : Disclosures} (h : S ≤ T) :
    (CovBad S : Set (RomReg Qrom.HashDomain (HashOutput × HashOutput) M)) ⊆ CovBad T :=
  fun _ ⟨x, ω, hx, hω⟩ ↦ ⟨x, ω, hx, hω.1, hω.2.1, covered_mono h hω.2.2⟩

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_covBad (W : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m : M) :
    UpClosed (slice (CovBad S) W m) :=
  upClosed_slice_cellTargetBad W m

/-- **The start is outside the event**: hardwired cells have no target. -/
theorem not_mem_covBad_start (W₀ : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m₀ : M) :
    (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
      RomReg Qrom.HashDomain (HashOutput × HashOutput) M) ∉ CovBad S :=
  not_mem_cellTargetBad_start W₀ m₀ fun _ y hx hy ↦
    Option.some_ne_none y (hx.symm.trans (mem_covTgt.1 hy).2.1)

open scoped Classical in
/-- The targets of a cell are covered pairs: a fraction at most `price S`. -/
theorem card_covTgt_div_le (W : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m : M)
    (x : Qrom.HashDomain) :
    ((univ.filter fun ω ↦ ω ∈ covTgt S W m x).card : ℝ≥0∞) /
      Fintype.card (HashOutput × HashOutput) ≤ ENNReal.ofReal (price S) := by
  rw [← covFrac_eq S]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 (card_le_card fun ω hω ↦ ?_)) _
  exact mem_filter.2 ⟨mem_univ _, (mem_covTgt.1 (mem_filter.1 hω).2).2.2⟩

/-- **The fresh bound of every slice**: a fresh cell enters the event with probability at most
`price S`, a fresh `k`, `k'` cell never. -/
theorem freshBound_slice_covBad (W : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m : M)
    (t : ℕ) : FreshBound (slice (CovBad S) W m) t (ENNReal.ofReal (price S)) := by
  classical
  exact freshBound_slice_cellTargetBad W m (fun x _ ↦ card_covTgt_div_le W m x) t

/-- Hardwiring `z` leaves the targets of the other cells. -/
theorem mem_covTgt_update_of_ne {W : Hw (HashOutput × HashOutput) Qrom.HashDomain} {m : M}
    {z x : Qrom.HashDomain} (hx : x ≠ z) (v : HashOutput × HashOutput)
    {ω : HashOutput × HashOutput} (h : ω ∈ covTgt S (Function.update W.1 z (some v), W.2) m x) :
    ω ∈ covTgt S W m x :=
  ⟨h.1, (Function.update_of_ne hx (some v) W.1).symm.trans h.2.1, h.2.2⟩

/-- A hardwired cell has no target. -/
theorem not_mem_covTgt_update_self (W : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m : M)
    (z : Qrom.HashDomain) (v ω : HashOutput × HashOutput) :
    ω ∉ covTgt S (Function.update W.1 z (some v), W.2) m z := fun h ↦
  Option.some_ne_none v ((Function.update_self z (some v) W.1).symm.trans h.2.1)

/-- **Hardwiring a cell flips nothing.** -/
theorem not_mem_covBad_programH {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) M}
    (hs : s ∉ CovBad S) (z : Qrom.HashDomain) (v : HashOutput × HashOutput) :
    progMap (.programH z v) s ∉ CovBad S :=
  not_mem_cellTargetBad_programH hs z v (fun _ hx _ h ↦ mem_covTgt_update_of_ne hx v h)
    (not_mem_covTgt_update_self s.2.1 s.2.2 z v v)

/-- **Programming cost zero**, for every cell and value. -/
theorem flipCost_programH_covBad_eq_zero [Fintype M] [DecidableEq M] (z : Qrom.HashDomain)
    (v : HashOutput × HashOutput)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) M)
      (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) M) ℂ} (hσ : σ.PosSemidef) :
    flipCost (CovBad S) (hwProgKraus (.programH z v)) 0 σ = 0 :=
  flipCost_programH_cellTargetBad_eq_zero z v hσ fun q _ _ ↦
    ⟨fun _ hx _ h ↦ mem_covTgt_update_of_ne hx v h,
      not_mem_covTgt_update_self q.2.2.1 q.2.2.2 z v v⟩

/-- **Reading a cell without a target flips nothing** (a cell other than a call-0 `H_msg` cell,
or a hardwired one), whatever the memory after the read. -/
theorem not_mem_covBad_readH {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) M}
    (hs : s ∉ CovBad S) {z : Qrom.HashDomain} (hz : hmsgCall z ≠ some 0 ∨ s.2.1.1 z ≠ none)
    (m' : M) (u : Option (HashOutput × HashOutput)) :
    ((Function.update s.1.1 z u, s.1.2), s.2.1, m') ∉ CovBad S :=
  not_mem_cellTargetBad_readH hs m'
    (Set.eq_empty_iff_forall_notMem.2 fun _ h ↦ hz.elim (· h.1) (· h.2.1))
    (fun _ _ _ h ↦ h) u

end event

/-! ## S★: the disclosures of the stream -/

/-- **S★**: the static disclosures of a stream of regrouped pairs. -/
def starCover {n : ℕ} (d : Fin n → HashOutput × HashOutput) : Disclosures :=
  revealed fun j ↦ pairView (d j)

theorem starCover_eq_streamCover {n : ℕ} (d : Fin n → HashOutput × HashOutput) :
    starCover d = streamCover fun j ↦ pairCalls (d j) :=
  rfl

/-- **The mean price of S★** over uniform streams of `signatureLimit` pairs is at most
`rhoCov / 2^128`. -/
theorem uavg_price_starCover_le :
    uavg (fun d : Fin signatureLimit → HashOutput × HashOutput ↦
        ENNReal.ofReal (price (starCover d))) ≤ ENNReal.ofReal (rhoCov / 2 ^ 128) :=
  (uavg_comp_equiv (Equiv.arrowCongr (Equiv.refl (Fin signatureLimit)) pairCallsEquiv)
    fun d ↦ ENNReal.ofReal (price (streamCover d))).le.trans uavg_price_stream_le

/-! ## Averages: Jensen and Minkowski over S★ -/

section average

theorem rpow_inv_two_sq (x : ℝ≥0∞) : (x ^ (2⁻¹ : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

variable {Θ : Type*} [Fintype Θ]

theorem uavg_const_le (c : ℝ≥0∞) : uavg (fun _ : Θ ↦ c) ≤ c := by
  unfold uavg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
  by_cases h : Fintype.card Θ = 0
  · simp [h]
  · rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr h) (ENNReal.natCast_ne_top _), one_mul]

/-- **Jensen for `(a + √f)²`**: the average is at most `(a + √(E f))²`. -/
theorem uavg_sq_add_rpow_le (a : ℝ≥0∞) (f : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ (a + f θ ^ (2⁻¹ : ℝ)) ^ 2) ≤ (a + uavg f ^ (2⁻¹ : ℝ)) ^ 2 := by
  have e : ∀ b : ℝ≥0∞, (a + b ^ (2⁻¹ : ℝ)) ^ 2 = a ^ 2 + 2 * a * b ^ (2⁻¹ : ℝ) + b := fun b ↦ by
    rw [add_sq, rpow_inv_two_sq]
  simp only [e]
  rw [uavg_add, uavg_add, uavg_const_mul]
  refine add_le_add (add_le_add (uavg_const_le _) ?_) le_rfl
  gcongr
  exact uavg_sqrt_le f

/-- Averaging over a product a function of the first factor averages over the first factor. -/
theorem uavg_comp_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] (g : A → ℝ≥0∞) :
    uavg (fun p : A × B ↦ g p.1) = uavg g := by
  have h := sum_inv_card_smul_fst (B := B) g
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  exact h

/-- **Restriction to injective positions**: averaging over tables `P → V` a function of the
entries at the injective positions `e` averages over those entries. -/
theorem uavg_comp_restrict {ι P V : Type*} [Fintype ι] [DecidableEq ι] [Fintype P]
    [DecidableEq P] [Fintype V] [Nonempty V] (e : ι → P) (he : Function.Injective e)
    (g : (ι → V) → ℝ≥0∞) :
    uavg (fun θ : P → V ↦ g fun i ↦ θ (e i)) = uavg g := by
  classical
  let Φ : (P → V) ≃ (ι → V) × ({p // p ∉ Set.range e} → V) :=
    (Equiv.piEquivPiSubtypeProd (· ∈ Set.range e) fun _ ↦ V).trans
      (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective e he).symm (Equiv.refl V))
        (Equiv.refl _))
  have hΦ : ∀ θ, (Φ θ).1 = fun i ↦ θ (e i) := fun _ ↦ rfl
  calc uavg (fun θ : P → V ↦ g fun i ↦ θ (e i))
      = uavg (fun θ ↦ (fun p : (ι → V) × ({p // p ∉ Set.range e} → V) ↦ g p.1) (Φ θ)) := by
        simp only [hΦ]
    _ = uavg (fun p : (ι → V) × ({p // p ∉ Set.range e} → V) ↦ g p.1) :=
        uavg_comp_equiv Φ fun p ↦ g p.1
    _ = uavg g := uavg_comp_fst g

/-- **Minkowski over S★**: with the per-call instability `2^-128 + price S★`, the mean over
uniform streams of `(a + √(c ε))²` is at most `(a + √(c (2^-128 + rhoCov / 2^128)))²`. -/
theorem uavg_sq_add_sqrt_starCover_le (a c : ℝ≥0∞) :
    uavg (fun d : Fin signatureLimit → HashOutput × HashOutput ↦
        (a + (c * ((2 ^ 128)⁻¹ + ENNReal.ofReal (price (starCover d)))) ^ (2⁻¹ : ℝ)) ^ 2) ≤
      (a + (c * ((2 ^ 128)⁻¹ + ENNReal.ofReal (rhoCov / 2 ^ 128))) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (uavg_sq_add_rpow_le a _).trans (pow_le_pow_left₀ zero_le
    (add_le_add le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num : (0 : ℝ) ≤ 2⁻¹))) 2)
  rw [uavg_const_mul, uavg_add]
  gcongr
  · exact uavg_const_le _
  · exact uavg_price_starCover_le

/-- **Minkowski over S★, on a table** holding the stream at the injective positions `pos`. -/
theorem uavg_sq_add_sqrt_starCover_table_le {P : Type*} [Fintype P] [DecidableEq P]
    (pos : Fin signatureLimit → P) (hpos : Function.Injective pos) (a c : ℝ≥0∞) :
    uavg (fun θ : P → HashOutput × HashOutput ↦
        (a + (c * ((2 ^ 128)⁻¹ + ENNReal.ofReal (price (starCover fun j ↦ θ (pos j))))) ^
          (2⁻¹ : ℝ)) ^ 2) ≤
      (a + (c * ((2 ^ 128)⁻¹ + ENNReal.ofReal (rhoCov / 2 ^ 128))) ^ (2⁻¹ : ℝ)) ^ 2 :=
  (uavg_comp_restrict pos hpos fun d ↦
    (a + (c * ((2 ^ 128)⁻¹ + ENNReal.ofReal (price (starCover d)))) ^ (2⁻¹ : ℝ)) ^ 2).trans_le
    (uavg_sq_add_sqrt_starCover_le a c)

end average

end Quantum.Qrom.Sphincs

end
