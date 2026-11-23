module

public import Quantum.Sphincs.Assembly.EndReads
public import Quantum.Xmss.Assembly.EventSqrt

@[expose] public section

/-!
# leanSPHINCS's event bound with the verification's reads graded like sponge calls

The event bound of the canonical game `gameR pol A p v` at template data `(p, v)` (contract C4),
with the event `Bad (evData p v) progCap`: the challenge prefix keeps its classical prices (a
bound `(advTerm v q + √T)²` on the prefix's event weight, from the prefix's classical cost `T`),
the verification's `3 verifyBlocks` reads are graded like sponge calls (leanXMSS's
`rpow_inv_two_eventWeight_keepReads_le`, ReadCost's square-root form):
`ew(gameR) ≤ (advTerm v q + verTerm v q + √(T + verLin v q))²` (`ewR_le_sqrt_sph`).

* **The verification's calls** (`chg_verifyT_nonKeep_sph`, `chg_verifyT_one_sph`): only reads
  that keep the memory, at most `3 verifyBlocks` of them (Charges' `verify_hashBlocks`).
* **The verification's fresh bound** (`verEps v q`): Events' rate of the slices of `Bad` below
  `progCap + 6q + clsCap + 3 verifyBlocks + 1` entries, the Struct and Enc rate (`2^960` values of
  an `h` cell per target) plus the coverage rate (`2^838 coverMass S★(v)`): the verification's
  two `H_msg` reads are priced like any read, at `2^16 price S★(v)` (`verEps_le`, Events'
  `freshRate_le`), so `verEps v q ≤ 2^-128 + 2 capRate + 2^16 price S★(v)`.
* `verTerm v q = 3 verifyBlocks √(verEps v q)`, `verLin v q = 3 verifyBlocks (verEps v q + 2/|X| +
  2/|Z|)`; `advTerm v q = ∑_{n < 6q} √(6 advEps v n)` (the shape of leanXMSS's
  `eventWeight_runtimeR_le` at GameR's `advEps`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Message)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT tmplLens readLens liftRead
  chg_readsProgram chg_map sChg_simulateQ_keep isChargeBound_mono_charge nonKeep nonKeepRd
  keepUpd_liftRead nonKeep_le_one keepCost rpow_inv_two_eventWeight_keepReads_le
  querySupportedOn_runtimeR_step' noBot_runtimeR eventWeight_eq_tsum_run₂ eventWeight_bind₂
  tsum_rpow_inv_two_ite rpow_inv_two_add_le_of_le_sq pow_two_rpow_inv_two extCls)

namespace Quantum.Sphincs.Assembly

/-! ## The verification's reads keep the memory -/

section verifyCharges

variable {M : Type} [Fintype M] [DecidableEq M]

set_option synthInstance.maxSize 2000 in
omit [Fintype M] [DecidableEq M] in
/-- **The verification calls only reads that keep the memory.** -/
theorem chg_verifyT_nonKeep_sph (pub : Pub) (v : (s : HPos) → XD s)
    (x : PublicKey × (Forgery × SignLog Message (Option Signature))) :
    IFreeM.IsChargeBound (realizeT v (verifyT M pub x)) (portCharge (nonKeep X Z HPos M)) 0 := by
  unfold verifyT
  refine IFreeM.IsChargeBound.mapLens (tmplLens v) ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ ↦ trivial
  refine IFreeM.IsChargeBound.mapLens (readLens goodAll) ?_
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    (chg_map _ Prod.fst (sChg_simulateQ_keep (M := M) pub.perm (QReg.of Unit) _ []))
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show nonKeep X Z HPos M (.inl (.inl (.inr (liftRead c)))) ≤ nonKeepRd M (.inr c)
    by_cases hc : c.KeepsMem
    · have h0 : nonKeep X Z HPos M (.inl (.inl (.inr (liftRead c)))) = 0 := by
        simp only [nonKeep, keepUpd_liftRead (S := HPos) c hc, ↓reduceIte]
      omega
    · have h1 : nonKeepRd M (.inr c) = 1 := by simp only [nonKeepRd, hc, ↓reduceIte]
      have h2 := nonKeep_le_one (X := X) (Z := Z) (S := HPos) (M := M)
        (.inl (.inl (.inr (liftRead c))))
      omega

set_option synthInstance.maxSize 2000 in
omit [Fintype M] [DecidableEq M] in
/-- **The verification's calls**: at most `3 verifyBlocks`. -/
theorem chg_verifyT_one_sph (pub : Pub) (v : (s : HPos) → XD s)
    (x : PublicKey × (Forgery × SignLog Message (Option Signature))) :
    IFreeM.IsChargeBound (realizeT v (verifyT M pub x)) (portCharge fun _ ↦ 1)
      (3 * verifyBlocks) := by
  have he : rCharge M 1 1 1 1 = fun _ ↦ 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  have hv := chg_readsProgram (M := M) 1 1 pub.perm (QReg.of Unit) (verify_hashBlocks x.1 x.2.1)
  have hb : IFreeM.IsChargeBound (verifyT M pub x) (portCharge (tCharge M 1 1 1 1))
      (3 * verifyBlocks) := by
    unfold verifyT
    exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
      (isChargeBound_readLift 1 1 1 1 (chg_map _ Prod.fst hv)) fun _ ↦ trivial) (by omega)
  have h := isChargeBound_realizeT 1 1 1 1 v hb
  rwa [he] at h

end verifyCharges

/-! ## The constants of the verification -/

section constants

/-- **The fresh bound of the verification's reads** at the hidden values `v`: Events' rate of the
slices of `Bad` below `progCap + 6q + clsCap + 3 verifyBlocks + 1` entries (the prefix's calls,
then the verification's): Struct and Enc (`2^960` values of an `h` cell per target) and coverage
(`2^838 coverMass S★(v)`), at `PermGood π 18`. -/
noncomputable def verEps (v : (s : HPos) → XD s) (q : ℕ) : ℝ≥0∞ :=
  preimageRateBound (X := X) (Z := Z) (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1)) 18
      (2 ^ 960) +
    preimageRateBound (X := X) (Z := Z) (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1)) 18
      (2 ^ 838 * coverMass (coverOf v))

/-- **The verification term**: `3 verifyBlocks · √verEps`, the verification's reads graded like
sponge calls. -/
noncomputable def verTerm (v : (s : HPos) → XD s) (q : ℕ) : ℝ≥0∞ :=
  ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * verEps v q ^ (2⁻¹ : ℝ)

/-- **The verification's linear term**: `3 verifyBlocks (verEps + 2/|X| + 2/|Z|)`, the empty-cell
and recorded-cell terms of its reads. -/
noncomputable def verLin (v : (s : HPos) → XD s) (q : ℕ) : ℝ≥0∞ :=
  ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps v q)

/-- **The adversary term of the event bound**: `∑_{n < 6q} √(6 advEps v n)` (GameR's fresh bound of
the `n`-th adversary call). -/
noncomputable def advTerm (v : (s : HPos) → XD s) (q : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range (6 * q), (6 * advEps v n) ^ (2⁻¹ : ℝ)

theorem verEps_ne_top (v : (s : HPos) → XD s) (q : ℕ) : verEps v q ≠ ⊤ :=
  ENNReal.add_ne_top.mpr ⟨preimageRateBound_ne_top _ _ _, preimageRateBound_ne_top _ _ _⟩

/-- **The verification's reads at `2^16 price S★(v)`**: `verEps v q ≤ 2^-128 + 2 capRate +
2^16 price S★(v)` (Events' `freshRate_le`), the coverage rate pricing the verification's two
`H_msg` reads like the adversary's calls. -/
theorem verEps_le (v : (s : HPos) → XD s) (q : ℕ) :
    verEps v q ≤ (2 ^ 128)⁻¹ + 2 * capRate (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1)) 18 +
      ENNReal.ofReal ((2 ^ 16 * price (coverOf v) : ℚ) : ℝ) :=
  freshRate_le _ _ _

end constants

/-! ## The canonical game -/

section game

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

set_option synthInstance.maxSize 2000 in
/-- **The prefix's calls**: at most `6q + clsCap`. -/
theorem calls_prefixR_sph (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (prefixR pol A p v) (portCharge fun _ ↦ 1) (6 * q + clsCap) := by
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    ((advCalls_prefixR hperm hsign pol p v).add (clsCalls_prefixR hperm hsign pol p v))
  rcases a with o | ⟨i, E, ℓ⟩
  · exact le_rfl
  · show 1 ≤ (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0)
    split_ifs <;> omega

set_option synthInstance.maxSize 2000 in
/-- **The event bound over the whole game for an event with the verification's fresh bound**: for
an event `B` with up-closed slices and the fresh bound `verEps v q` below
`6q + clsCap + 3 verifyBlocks + 1` further entries, if the challenge prefix's event weight is at
most `(advTerm v q + √T)²`, then the game's is at most
`(advTerm v q + verTerm v q + √(T + verLin v q))²`. -/
theorem ewR_le_sqrt_of_fresh (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (B : Set (HwReg X Z (Mem HPos))) [DecidablePred (· ∈ B)] (hup : ∀ W m, UpClosed (slice B W m))
    (hε : ∀ W m, FreshBound (slice B W m) (6 * q + clsCap + 3 * verifyBlocks + 1) (verEps v q))
    {T : ℝ≥0∞}
    (hpreT : (runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v) initR ≤
      (advTerm v q + T ^ (2⁻¹ : ℝ)) ^ 2) :
    (runtimeR m0R).eventWeight .instruments (hwProjector B) (gameR pol A p v) initR ≤
      (advTerm v q + verTerm v q + (T + verLin v q) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hρa := fun a ↦ ((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).posSemidef_branch_apply
    a initR_posSemidef
  have hinit : QuerySupportedOn
      (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ dbGrade m.2.1)
      (Set.Iic 0) initR := by
    intro m m' hm
    change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty X Z, m0R) : HwReg X Z (Mem HPos))).matrix) m m' ≠ 0 at hm
    simp only [SubState.matrix_basis] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
    · exact False.elim (h rfl)
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1)
    (fun _ ↦ 1) (fun i r t σ hσ ↦ querySupportedOn_runtimeR_step' m0R i r t σ hσ) .instruments
    (calls_prefixR_sph hperm hsign pol p v) hinit ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR m0R .instruments (prefixR pol A p v)
    (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le B hup m0R
    (N := 6 * q + clsCap + 3 * verifyBlocks) (verEps_ne_top v q) hε .instruments
    (realizeT v (verifyT Selections p a))
    (chg_verifyT_one_sph p v a) (chg_verifyT_nonKeep_sph p v a)
    (t := 0 + (6 * q + clsCap)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a
      initR).trace.re ≤ 1 :=
    (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).isCPTNIFamily.tsum_ofReal_trace_re_le
      initR_posSemidef).trans (ENNReal.ofReal_le_one.mpr
        ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m0R).init).trace_re_le_one)
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0R) .instruments (hwProjector B)
    (prefixR pol A p v) initR
  have hm : ∑' j, (∑' a, (if j < 3 * verifyBlocks then verEps v q else 0) *
      ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a
        initR).trace.re) ^ (2⁻¹ : ℝ) ≤ verTerm v q := by
    calc _ ≤ ∑' j, ((if j < 3 * verifyBlocks then verEps v q else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTerm v q := by
          unfold verTerm
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector B)
      (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a initR) +
      ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps v q) *
        ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a
          initR).trace.re) ≤
      (runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v) initR +
        verLin v q := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps v q) * _
        ≤ ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps v q) * 1 := by gcongr
      _ = verLin v q := mul_one _
  have hpre' : ((runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v)
      initR + verLin v q) ^ (2⁻¹ : ℝ) ≤ advTerm v q + (T + verLin v q) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := advTerm v q ^ 2) (δ := 0) (C := verLin v q)
      (b := T) (a := (runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v)
        initR) (by
          rw [pow_two_rpow_inv_two, add_zero, add_comm]
          exact hpreT)
    rwa [pow_two_rpow_inv_two, zero_add] at h
  have hew : (runtimeR m0R).eventWeight .instruments (hwProjector B) (gameR pol A p v) initR =
      ∑' a, (runtimeR m0R).eventWeight .instruments (hwProjector B)
        (realizeT v (verifyT Selections p a))
        (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a initR) := by
    rw [gameR_eq]
    exact eventWeight_bind₂ (runtimeR m0R) .instruments (hwProjector B) (prefixR pol A p v) _
      initR_posSemidef
  have hfin : (runtimeR m0R).eventWeight .instruments (hwProjector B) (gameR pol A p v) initR ^
      (2⁻¹ : ℝ) ≤ advTerm v q + verTerm v q + (T + verLin v q) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v) initR +
          verLin v q) ^ (2⁻¹ : ℝ) + verTerm v q :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ advTerm v q + (T + verLin v q) ^ (2⁻¹ : ℝ) + verTerm v q := add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

set_option synthInstance.maxSize 2000 in
/-- **The event bound over the whole game, the verification's reads graded like sponge calls**
(`ewR_le_sqrt_of_fresh` at `Bad (evData p v) progCap`, Events' `freshBound_slice_bad`): for
`PermGood π 18`, if the challenge prefix's event weight is at most `(advTerm v q + √T)²` (its
classical cost `T`), then the game's is at most
`(advTerm v q + verTerm v q + √(T + verLin v q))²`: each of the `3 verifyBlocks` verification reads
costs `√(verEps v q)` in the square root (the `H_msg` reads at `2^16 price S★(v)`, `verEps_le`)
plus its linear terms (`verLin`). -/
theorem ewR_le_sqrt_sph (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    [DecidablePred (· ∈ Bad (S := HPos) (evData p v) progCap)] (hπ : PermGood p.perm 18)
    {T : ℝ≥0∞}
    (hpreT : (runtimeR m0R).eventWeight .instruments
      (hwProjector (Bad (S := HPos) (evData p v) progCap)) (prefixR pol A p v) initR ≤
        (advTerm v q + T ^ (2⁻¹ : ℝ)) ^ 2) :
    (runtimeR m0R).eventWeight .instruments (hwProjector (Bad (S := HPos) (evData p v) progCap))
        (gameR pol A p v) initR ≤
      (advTerm v q + verTerm v q + (T + verLin v q) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hε : ∀ W m, FreshBound (slice (Bad (S := HPos) (evData p v) progCap) W m)
      (6 * q + clsCap + 3 * verifyBlocks + 1) (verEps v q) := fun W m ↦
    freshBound_slice_bad hπ _ W m
  exact ewR_le_sqrt_of_fresh hperm hsign pol p v (Bad (S := HPos) (evData p v) progCap)
    (fun W m ↦ upClosed_slice_bad W m) hε hpreT

end game

end Quantum.Sphincs.Assembly

end
