module

public import Quantum.Xmss.Assembly.CostRun
public import Quantum.Xmss.Hybrid.GradedMasked
public import Quantum.Xmss.Assembly.EncPotential

@[expose] public section

/-!
# The codeword-recorded mass of the randomizer trials, averaged over the table

Security's `restMass` in EncPotential's restated shape: the codeword-recorded mass `cwRecW` of the
trials' selecting reads (the read cell recorded in the database, not hardwired, with a value that
selects the trial's unselected key), summed along the challenge prefix (`cwRecPre`), averaged over
the good tables.

* **The prefix congruence** (`realizeT_prefixT_congr`, `realizeT_prefixT_keys`, `hpre_r0E`):
  GameCongr's and ReparamR0's game congruences for the challenge prefix.
* **The mass as a diagonal mass** (`cwSet`, `cwWt_eq_diagMass`): at a trial's read port the states
  whose read cell is codeword-recorded for the trial's unselected key; nothing elsewhere.
* **The average** (`uavg_cwRecPre_le`, `uavg_cwRecPre_le_add`): ReparamR0's reparametrization
  `r0E` on its good set `r0G treeQ 18` (Masses' `uavg_le_of_injOn`), Mismatch's
  `totalWeight_le_mismatch` for the non-first labels (`2 lifetime |J| / |Z| ≤ 2^-190` per read
  call), the bad fraction `2^-174` (`r0G_frac_le_keccak`) at most `clsCap` per table
  (`cwRecPre_le_clsCap`): the average is at most `τ + cwJunk` with `cwJunk ≤ 2^-107`
  (`cwJunk_le`), given the per-public-datum bound `CwRecView A τ` (summed over the hidden values,
  which carry every label's randomizer base). `CwRecView` is the remaining lemma.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The prefix congruence -/

section congr

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The prefix congruence** (`realizeT_gameT_congr` for the challenge prefix). -/
theorem realizeT_prefixT_congr (A : Adversary (X × Z)) {pub pub' : Pub} {v v' : HPos → Digest}
    (hP : pub.param = pub'.param) (hπ : pub.perm = pub'.perm)
    (hroot : v (.inl rootPos) = v' (.inl rootPos))
    (hlab : ∀ lab : RLabel, v (.inr lab) = v' (.inr lab))
    (hneed : ∀ (l : Layer) (e : KeyIndex) (x : Encoding), e.val < keyCount l →
      ∀ q ∈ layerNeed l e x, v (.inl q) = v' (.inl q))
    (hslot : ∀ (l : Layer) (e : KeyIndex) (x : Encoding) (s : Slot), e.val < keyCount l →
      s ∈ layerSlots l e x → SlotPortsAgree pub pub' v s) :
    realizeT v (prefixT M upd pub A) = realizeT v' (prefixT M upd pub' A) := by
  obtain ⟨P, π, t⟩ := pub
  obtain ⟨P', π', t'⟩ := pub'
  obtain rfl : P = P' := hP
  obtain rfl : π = π' := hπ
  refine realizeT_revealThen_congr _ (fun s hs ↦ by rw [Finset.mem_singleton.mp hs]; exact hroot)
    fun r₀ ↦ ?_
  exact realizeT_bind₂_congr (realizeT_challengedT_congr upd hlab hneed hslot _) fun _ ↦ rfl

/-- **The prefix at the reparametrized datum** (`realizeT_gameT_keys` for the challenge prefix). -/
theorem realizeT_prefixT_keys (A : Adversary (X × Z)) (L : HonestTable) (θ : RTab)
    (hθ : XGood θ) (hP : θ.2.1 = L.param) (hπ : θ.2.2.1 = L.perm)
    (hu : ∀ l e i, θ.1.2 (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      KeysAt (pubOf L) (xPub θ.2 θ.1.1) s (valuePos L) j)
    (v : HPos → Digest) (hinl : ∀ q, v (.inl q) = xVal θ.2 θ.1.1 θ.1.2 q)
    (hinr : ∀ lab, v (.inr lab) = valueAt L (.inr lab)) :
    realizeT (valueAt L) (prefixT M upd (pubOf L) A) =
      realizeT v (prefixT M upd (xPub θ.2 (fwd xmssFix xO θ).1.1) A) := by
  obtain ⟨⟨h, u⟩, w⟩ := θ
  refine realizeT_prefixT_congr upd A hP.symm hπ.symm ?_ (fun lab ↦ (hinr lab).symm) ?_
    fun l e x s he hs ↦ slotPortsAgree_keys L hθ hP hπ hu hav he hs
  · rw [hinl]
    exact (xVal_eq_valuePos_keys' L hP hπ hu hav _ (Or.inl inPos_rootPos)).symm
  · intro l e x he q hq
    rw [hinl]
    exact (xVal_eq_valuePos_keys' L hP hπ hu hav q (layerNeed_good he hq)).symm

variable {ι : Type} {β : ι → Type}
  {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)} {G : ℕ}

/-- **`hgame` for the prefix** (`hgame_r0E`): on the good set, the prefix at the table is the
template prefix at the public datum, realized at hidden values agreeing with `r0E`'s off the
non-first labels. -/
theorem hpre_r0E (A : Adversary (X × Z)) (hQ : HashesSlots Q) {t : HonestTable × RE}
    (ht : r0G Q G t) :
    ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permR (r0E t).1) (parR (r0E t).1) (r0E t).2.2.1) v (r0E t).2.1 ∧
      realizeT (valueAt t.1) (prefixT M upd (pubOf t.1) A) =
        realizeT v (prefixT M upd (pubR (r0E t).1) A) :=
  ⟨Sum.elim (fun q ↦ (r0E t).2.1 (.inl q)) fun lab ↦ valueAt t.1 (.inr lab),
    agree_univ_sdiff fun s hs ↦ by
      rcases s with q | lab
      · rfl
      · exact (r0E_inr_eq ht lab hs).symm,
    realizeT_prefixT_keys upd A t.1 (r0Phi t).1.1 ht.2.2.1 (r0G_param ht) (r0Phi_perm t)
      (r0G_start ht) (r0G_keys hQ ht) _ (fun _ ↦ rfl) fun _ ↦ rfl⟩

end congr

/-! ## The codeword-recorded mass -/

section mass

/-- The codeword-recorded mass of the trials' selecting reads, summed along the challenge prefix
(EncPotential's `cwRecW`, the restated `restMass` integrand; Security's `prefixCost` with these
costs). -/
noncomputable def cwRecPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (cwRecW Prod.snd trialUpd)
    fun _ _ ↦ 0)) (prefixR A L) initR

/-- The codeword-recorded mass along the template prefix at the public datum `pub`, realized at
the hidden values `v`. -/
noncomputable def cwRecT (A : Adversary (X × Z)) (pub : Pub) (v : HPos → Digest) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (cwRecW Prod.snd trialUpd)
    fun _ _ ↦ 0)) (realizeT v (prefixT Selections cwUpd pub A)) initR

theorem cwRecPre_eq (A : Adversary (X × Z)) (L : HonestTable) :
    cwRecPre A L = cwRecT A (pubOf L) (valueAt L) :=
  rfl

/-- **The remaining bound**: for every public datum of ReparamR0's reparametrization, the
codeword-recorded mass of the template prefix, summed over the hidden values (every position's
digest and every label's randomizer base), is at most `τ` per hidden value. -/
def CwRecView (A : Adversary (X × Z)) (τ : ℝ≥0∞) : Prop :=
  ∀ p : RP, ∑ v : HPos → Digest, cwRecT A (pubR p) v ≤ τ * Fintype.card (HPos → Digest)

/-- The register states whose read cell `z` of the trial `t` is codeword-recorded for its
unselected key: not hardwired, the key unselected, recorded with a selecting value. -/
def CwRec (z : Z) (t : TrialPt) (s : HwReg X Z Mem) : Prop :=
  s.2.1.1 z = none ∧ s.2.2.2 t.l t.e = none ∧
    ∃ v, s.1.1 z = some v ∧ Codeword.Valid (trunc128 (t.xi + v))

/-- **The codeword-recorded states per port**: at a trial's read port, `CwRec` at its cell and
trial; nothing at the other ports. -/
def cwSet : ∀ i : (recHwSpec X Z HPos Selections).Port,
    Set ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
  | .inl (.inl (.inr c)) => {q : Unit × HwReg X Z Mem | IsTrial trialUpd c ∧
      CwRec (trialOf trialUpd c).1 (trialOf trialUpd c).2 q.2}
  | _ => ∅

/-- A real sum of the diagonal over a predicate is the diagonal mass of its set, when the
diagonal is nonnegative. -/
theorem ofReal_sum_ite_eq_diagMass {n : Type} [Fintype n] (S : Set n) (P : n → Prop)
    {_ : DecidablePred P} (hS : ∀ q, q ∈ S ↔ P q) (σ : Matrix n n ℂ)
    (hre : ∀ q, 0 ≤ (σ q q).re) :
    ENNReal.ofReal (∑ q, if P q then (σ q q).re else 0) = diagMass S σ := by
  unfold diagMass
  rw [ENNReal.ofReal_sum_of_nonneg fun q _ ↦ by split_ifs; exacts [hre q, le_rfl]]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hq : P q
  · rw [ite_eq_left hq, Set.indicator_of_mem ((hS q).2 hq)]
  · rw [ite_eq_right hq, Set.indicator_of_notMem (fun h ↦ hq ((hS q).1 h)), ENNReal.ofReal_zero]

/-- The codeword-recorded mass of a port is the diagonal mass of `cwSet` on positive semidefinite
inputs. -/
theorem cwWt_eq_diagMass (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ) (hσ : σ.PosSemidef) :
    extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0) i σ = diagMass (cwSet i) σ := by
  have h0 : ∀ (S : Set ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))),
      S = ∅ → diagMass S σ = 0 := fun S hS ↦ by
    subst hS
    exact Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _
  rcases i with ((p | c) | c) | T
  · exact (h0 _ rfl).symm
  · have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    show cwRecW Prod.snd trialUpd c σ = diagMass (cwSet (.inl (.inl (.inr c)))) σ
    by_cases ht : IsTrial trialUpd c
    · simp only [cwRecW, ht, ↓reduceIte]
      exact ofReal_sum_ite_eq_diagMass (n := Unit × HwReg X Z Mem)
        {q | IsTrial trialUpd c ∧ CwRec (trialOf trialUpd c).1 (trialOf trialUpd c).2 q.2}
        (fun q ↦ CwRec (trialOf trialUpd c).1 (trialOf trialUpd c).2 q.2)
        (fun _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨ht, h⟩⟩) σ hre
    · simp only [cwRecW, ht, ↓reduceIte]
      exact (Finset.sum_eq_zero fun q _ ↦ Set.indicator_of_notMem (fun h ↦ ht h.1) _).symm
  · exact (h0 _ rfl).symm
  · exact (h0 _ rfl).symm

/-- The codeword-recorded mass of a port is at most its trace at the read ports. -/
theorem cwWt_le_trace (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ) (hσ : σ.PosSemidef) :
    extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0) i σ ≤
      extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
        fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ := by
  rcases i with ((p | c) | c) | T
  · exact le_rfl
  · have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    show cwRecW Prod.snd trialUpd c σ ≤ ENNReal.ofReal σ.trace.re
    unfold cwRecW
    split_ifs
    · refine ENNReal.ofReal_le_ofReal ?_
      rw [Matrix.trace, Complex.re_sum]
      refine Finset.sum_le_sum fun q _ ↦ ?_
      split_ifs
      · exact le_rfl
      · exact hre q
    · exact zero_le
  · exact zero_le
  · exact le_rfl

/-- The codeword-recorded diagonal mass along the realized template prefix. -/
noncomputable def cwDiagT (A : Adversary (X × Z)) (pub : Pub) (v : HPos → Digest) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (fun i ↦ diagMass (cwSet i))
    (realizeT v (prefixT Selections cwUpd pub A)) initR

theorem cwDiagT_eq (A : Adversary (X × Z)) (pub : Pub) (v : HPos → Digest) :
    cwDiagT A pub v = cwRecT A pub v :=
  le_antisymm
    (totalWeight_le_totalWeight _ _ (fun i σ hσ ↦ (cwWt_eq_diagMass i σ hσ).ge) _ initR_posSemidef)
    (totalWeight_le_totalWeight _ _ (fun i σ hσ ↦ (cwWt_eq_diagMass i σ hσ).le) _ initR_posSemidef)

/-- The extra terms of the average: the non-first labels' mismatch `2^-190` and the bad fraction
`2^-174`, at most `clsCap` each. -/
noncomputable def cwJunk : ℝ≥0∞ :=
  (clsCap : ℝ≥0∞) * (ENNReal.ofReal (1 / 2 ^ 190) + ENNReal.ofReal (1 / 2 ^ 174))

set_option exponentiation.threshold 4096 in
/-- **The extra terms at Keccak's sizes**: `cwJunk ≤ 2^-107` (`clsCap < 2^67`). -/
theorem cwJunk_le : cwJunk ≤ ENNReal.ofReal (1 / 2 ^ 107) := by
  unfold cwJunk
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [clsCap, verifyBlocks_eq, signBlocks_eq, progCap_eq]
  norm_num [lifetime, layerCount, layerHeight]

/-- Collecting the per-datum terms (over abstract cardinalities). -/
theorem cards_add_mul_eq (a b t n c : ℝ≥0∞) :
    b * (t * a) + a * (n * (b * c)) = (t + n * c) * (a * b) := by
  ring

end mass

/-! ## The average over the table -/

section avg

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

omit hperm hsign in
/-- A charge bound of the realized game holds for its realized prefix. -/
theorem chg_prefixT_of_gameT {pub : Pub} {v : HPos → Digest}
    {c : (s : QReg) → (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (recHwSpec X Z HPos Selections)).A s → ℕ} {n : ℕ}
    (h : IFreeM.IsChargeBound (realizeT v (gameT Selections cwUpd pub A)) c n) :
    IFreeM.IsChargeBound (realizeT v (prefixT Selections cwUpd pub A)) c n := by
  rw [gameT_eq_prefixT_bind, realizeT_bind₂] at h
  exact isChargeBound_of_bind₂ h

/-- At most `clsCap` per table: the codeword-recorded mass of a call is at most its trace. -/
theorem cwRecPre_le_clsCap (L : HonestTable) : cwRecPre A L ≤ clsCap :=
  (totalWeight_le_totalWeight (runtimeR m0R) .instruments (fun i σ hσ ↦ cwWt_le_trace i σ hσ)
    (prefixR A L) initR_posSemidef).trans
    (totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L))

/-- The read and record calls of the realized template prefix: at most `clsCap`. -/
theorem hN_readRec_prefixT (pub : Pub) (v : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (prefixT Selections cwUpd pub A))
      (portCharge fun i ↦ if readRecPort Selections i = true then 1 else 0) clsCap :=
  chg_prefixT_of_gameT (hN_readRec cwUpd A hperm hsign pub v)

/-- The randomizer-base records of the realized template prefix: at most `2 lifetime`. -/
theorem hR_prefixT (pub : Pub) (v : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (prefixT Selections cwUpd pub A))
      (portCharge (candCharge X Z Selections rJ)) (2 * lifetime) :=
  chg_prefixT_of_gameT (hR_gameT cwUpd A hperm hsign pub v)

open scoped Classical in
/-- **The averaged codeword-recorded mass** over all tables: at most `τ + cwJunk`, given the
per-public-datum bound `CwRecView A τ`. ReparamR0's `r0E` on `r0G treeQ 18` (`hpre_r0E`), Mismatch
for the non-first labels, the bad fraction at `clsCap` per table. -/
theorem uavg_cwRecPre_all_le {τ : ℝ≥0∞} (hview : CwRecView A τ) :
    uavg (cwRecPre A) ≤ τ + cwJunk := by
  set N : ℕ := clsCap
  set ε : ℝ≥0∞ := (Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z
  set g : RP → (HPos → Digest) × (RK × RW) → ℝ≥0∞ := fun p w ↦
    cwDiagT A (pubR p) w.1 + N * revW m0R .instruments
      (r0Bk (permR p) (parR p) w.2.1) (realizeT w.1 (prefixT Selections cwUpd (pubR p) A)) initR
  have hQ : ∀ i : (recHwSpec X Z HPos Selections).Port, ¬ readRecPort Selections i = true →
      cwSet i = ∅ := fun i hi ↦ by
    rcases i with ((p | c) | c) | T
    · rfl
    · exact absurd rfl hi
    · rfl
    · rfl
  have hfg : ∀ t, r0G treeQ 18 t → cwRecPre A t.1 ≤ g (r0E t).1 (r0E t).2 := fun t ht ↦ by
    obtain ⟨v, hv, hgeq⟩ := hpre_r0E cwUpd A hashesSlots_treeQ ht
    calc cwRecPre A t.1 = cwDiagT A (pubOf t.1) (valueAt t.1) :=
          (cwDiagT_eq _ _ _).symm
      _ = (runtimeR m0R).totalWeight .instruments (fun i ↦ diagMass (cwSet i))
          (realizeT v (prefixT Selections cwUpd (pubR (r0E t).1) A)) initR := by
          rw [cwDiagT, hgeq]
      _ ≤ _ := totalWeight_le_mismatch m0R .instruments
          (prefixT Selections cwUpd (pubR (r0E t).1) A)
          (disc_prefixT Selections cwUpd _ A ∅) (keepsLab_prefixT cwUpd _ A) initR
          initR_posSemidef (Hybrid.querySupportedOn_initR m0R _) _
          (Finset.disjoint_empty_left _) (fun i ↦ readRecPort Selections i = true) cwSet hQ hv
          (hN_readRec_prefixT hperm hsign _ v)
  have hrev : ∀ p (v : HPos → Digest), ∑ k : RK × RW, revW m0R .instruments
      (r0Bk (permR p) (parR p) k.1) (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR ≤
      Fintype.card (RK × RW) * (((2 * lifetime : ℕ) : ℝ≥0∞) * ε) := fun p v ↦
    (sum_revW_le m0R .instruments _ initR_posSemidef (fun k : RK × RW ↦ r0Bk (permR p) (parR p) k.1)
      rJ (fun k ↦ r0Bk_subset _ _ _) ε
      (fun s _ ↦ le_of_eq_of_le (card_filter_pad (W := RW)
        (fun k : RK ↦ s ∈ r0Bk (permR p) (parR p) k))
        ((mul_le_mul_of_nonneg_right (card_filter_r0Bk_le _ _ s) zero_le).trans_eq
          (by rw [mul_assoc, ← Nat.cast_mul, ← Fintype.card_prod])))
      (hR_prefixT hperm hsign _ v)).trans
      (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left ofReal_trace_initR_le_one
        zero_le).trans_eq (mul_one _)) zero_le)
  have hg : ∀ p, ∑ w, g p w ≤ (τ + N * (((2 * lifetime : ℕ) : ℝ≥0∞) * ε)) *
      Fintype.card ((HPos → Digest) × (RK × RW)) := fun p ↦ by
    have hv : ∑ v : HPos → Digest, cwDiagT A (pubR p) v ≤
        τ * Fintype.card (HPos → Digest) := by
      simp only [cwDiagT_eq]
      exact hview p
    rw [Fintype.sum_prod_type]
    calc ∑ v : HPos → Digest, ∑ k : RK × RW, g p (v, k)
        = ∑ v : HPos → Digest, (Fintype.card (RK × RW) * cwDiagT A (pubR p) v +
            N * ∑ k : RK × RW, revW m0R .instruments (r0Bk (permR p) (parR p) k.1)
              (realizeT v (prefixT Selections cwUpd (pubR p) A)) initR) := by
          refine Finset.sum_congr rfl fun v _ ↦ ?_
          dsimp only [g]
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Finset.mul_sum]
      _ ≤ ∑ v : HPos → Digest, (Fintype.card (RK × RW) * cwDiagT A (pubR p) v +
            N * (Fintype.card (RK × RW) * (((2 * lifetime : ℕ) : ℝ≥0∞) * ε))) :=
          Finset.sum_le_sum fun v _ ↦ add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (hrev p v) zero_le)
      _ = Fintype.card (RK × RW) * ∑ v : HPos → Digest, cwDiagT A (pubR p) v +
            Fintype.card (HPos → Digest) *
              (N * (Fintype.card (RK × RW) * (((2 * lifetime : ℕ) : ℝ≥0∞) * ε))) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
      _ ≤ Fintype.card (RK × RW) * (τ * Fintype.card (HPos → Digest)) +
            Fintype.card (HPos → Digest) *
              (N * (Fintype.card (RK × RW) * (((2 * lifetime : ℕ) : ℝ≥0∞) * ε))) :=
          add_le_add (mul_le_mul_of_nonneg_left hv zero_le) le_rfl
      _ = (τ + N * (((2 * lifetime : ℕ) : ℝ≥0∞) * ε)) *
            Fintype.card ((HPos → Digest) × (RK × RW)) := by
          rw [Fintype.card_prod (HPos → Digest) (RK × RW),
            Nat.cast_mul (Fintype.card (HPos → Digest))]
          exact cards_add_mul_eq _ _ _ _ _
  have h := uavg_le_of_injOn r0E (r0G treeQ 18) (r0E_injOn treeQ 18) card_r0E_le (cwRecPre A) g
    hfg (clsCap : ℝ≥0∞) (fun t _ ↦ cwRecPre_le_clsCap hperm hsign t.1) _ hg
  refine h.trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  unfold cwJunk
  rw [mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_left revTerm_le_keccak zero_le)
    (mul_le_mul_of_nonneg_left r0G_frac_le_keccak zero_le)

/-- **The restated `restMass`**: the codeword-recorded mass of the challenge prefix, averaged over
the tables of any good set (Security's `GoodL`), is at most `τ + cwJunk`, given the
per-public-datum bound `CwRecView A τ`. -/
theorem uavg_cwRecPre_le (good : HonestTable → Prop) [DecidablePred good] {τ : ℝ≥0∞}
    (hview : CwRecView A τ) :
    uavg (fun L ↦ if good L then cwRecPre A L else 0) ≤ τ + cwJunk :=
  (uavg_mono fun L ↦ by
    split_ifs
    · exact le_rfl
    · exact zero_le).trans (uavg_cwRecPre_all_le hperm hsign hview)

/-- **`restMass` with the numeric extra term**: at most `τ + 2^-107` (at Security's target
`τ = massCap q`). -/
theorem uavg_cwRecPre_le_add (good : HonestTable → Prop) [DecidablePred good] {τ : ℝ≥0∞}
    (hview : CwRecView A τ) :
    uavg (fun L ↦ if good L then cwRecPre A L else 0) ≤ τ + ENNReal.ofReal (1 / 2 ^ 107) :=
  (uavg_cwRecPre_le hperm hsign good hview).trans (add_le_add le_rfl cwJunk_le)

end avg

end Quantum.Xmss.Assembly

end
