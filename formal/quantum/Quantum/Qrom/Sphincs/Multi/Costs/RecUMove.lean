module

public import Quantum.Qrom.Sphincs.Multi.Costs.RecUModes
public import Quantum.Qrom.Sphincs.Multi.Costs.Defs

@[expose] public section

/-!
# The `n`-user recorded unselected weights, moved onto the reveals that start the searches

The `n`-user analog of `Quantum.Qrom.Sphincs.Costs.RecUMove`. The recorded unselected weight
`recUWtSN` at the read of trial `j` of user `i`'s search (the read cell recorded, the key
unselected) is moved to the reveal that starts the search: between that reveal and the read only
the search's earlier reads happen, at other cells, and they can only select keys. The moded
potential (CwRec's `totalWeight_le_modedP`) in the search of user `i`'s `K` on `m` before trial `j`
is the mass of the later trials' sets `RecTrialSN`.

* `RecTrialSN`, `trialSetSN`: a trial recorded with the key unselected, the trials still to come
  in a mode.
* **`recUPreSN_le_revQWSN`**: `recUPreSN A θ` is at most the reveal charges `revQWSN θ`.
* **`recUPreSN_le_split`**: the reveal charges split into the first reveals (`firstQWSN θ`: the
  coordinate unrevealed, the trial cell recorded) and the repeated reveals with the key unselected
  (`reRevQWSN`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (diagMass setProj)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR liftRead extWeight ModedP
  totalWeight_le_modedP cw_sum_pot_setProj_le cw_sum_pot_setProj_keep cw_clsKraus_ne_zero
  cw_readKrausH_ne_zero potential_setProj eq_of_recKraus_ne_zero totalWeight_le_add recKraus
  sum_recKraus)

attribute [local irreducible] sphincsRom Fin.fintype

/- Instance search for the register's memory exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-! ## The trials of a search -/

/-- **Trial `J` of user `i`'s search of `K` on `m` recorded, with the key unselected.** -/
def RecTrialSN (P : Fin n → PublicParameter) (i : Fin n) (K : Key) (m : Digest) (J : ℕ) :
    Set (RRegSN n (SelMemN n)) :=
  {s | s.1.1 (trialCell (P i) K m J) ≠ none ∧ s.2.2.2 i K = none}

/-- **The trials still to come in a mode**: trial `J` at or after the current trial. -/
def trialSetSN (P : Fin n → PublicParameter) : ModeSN n → ℕ → Set (RRegSN n (SelMemN n))
  | .grd _ i K m j, J => if j ≤ J then RecTrialSN P i K m J else ∅
  | .rest _, _ => ∅

theorem setProj_trialSetSN_rest (P : Fin n → PublicParameter) (ks : Finset (Fin n × Key))
    (J : ℕ) : setProj (trialSetSN P (.rest ks) J) =
      (0 : Matrix (RRegSN n (SelMemN n)) (RRegSN n (SelMemN n)) ℂ) := by
  show setProj (∅ : Set (RRegSN n (SelMemN n))) = 0
  ext a b
  simp [setProj]

/-- A trial read never unselects a key. -/
theorem cwUpdN_eq_noneSN {i i' : Fin n} {K K' : Key} {z : HashDomain} {m : SelMemN n}
    {o : Option PairOut} (h : cwUpdN i' K' z m o i K = none) : m i K = none := by
  by_cases hi : i = i'
  · subst hi
    rw [cwUpdN, Function.update_self] at h
    exact cwUpd_eq_noneU h
  · rwa [cwUpdN, Function.update_of_ne hi] at h

/-! ## Potentials of trial sets along the ports -/

/-- A nonzero entry of a read of the `h`-cell `z`: the other `h`-cells kept. -/
theorem readKrausH_ne_zero_cellsSN (z : HashDomain) (upd : QMemSN n → Option PairOut → QMemSN n)
    (r : Option PairOut × QMemSN n) {s' s : RRegSN n (SelMemN n)}
    (h : readKrausH z upd r s' s ≠ 0) (x : HashDomain) (hx : x ≠ z) : s'.1.1 x = s.1.1 x := by
  obtain ⟨-, -, hR⟩ := cw_clsKraus_ne_zero h
  rw [kroneckerMap_apply] at hR
  exact cellRead_apply_ne_zero (left_ne_zero_of_mul hR) x hx

theorem readKrausH_ne_zero_memSN (z : HashDomain) (upd : QMemSN n → Option PairOut → QMemSN n)
    (r : Option PairOut × QMemSN n) {s' s : RRegSN n (SelMemN n)}
    (h : readKrausH z upd r s' s ≠ 0) : s.2.2 = r.2 ∧ s'.2.2 = upd r.2 r.1 :=
  ⟨(cw_readKrausH_ne_zero z upd r h).2.2.1, (cw_readKrausH_ne_zero z upd r h).2.2.2⟩

open scoped Classical in
/-- **A trial read keeps another trial's set, up to selecting keys.** -/
theorem sum_pot_recTrialSN_readH_le (P : Fin n → PublicParameter) (i : Fin n) (K : Key)
    (m : Digest) (J : ℕ) {z : HashDomain} (hz : z ≠ trialCell (P i) K m J) (κ : UKeyS n)
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ r : Option PairOut × QMemSN n, potential (setProj (RecTrialSN P i K m J))
        (MatrixMap.conj (hwReadKraus (trialReadSN z κ) r) σ) ≤
      potential (setProj (RecTrialSN P i K m J)) σ := by
  set u := trialUpdSN z κ
  refine cw_sum_pot_setProj_le (fun r ↦ hwReadKraus (.readH z u) r) (sum_hwReadKraus _) _ _
    (fun r ↦ if (u r.2 r.1).2 i K = none then 1 else 0) (fun r ↦ by split_ifs <;> norm_num)
    (fun r s' a h ↦ ?_) (fun r s' a a' ha ha' ↦ ?_) hσ
  · obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
    have hc := readKrausH_ne_zero_cellsSN z u r hK _ hz.symm
    obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_memSN z u r hK
    by_cases hU : (u r.2 r.1).2 i K = none
    · have hU' : a.2.2.2.2 i K = none := by
        rw [hm]
        exact cwUpdN_eq_noneSN (i' := κ.1) (K' := κ.2) (z := z) (o := r.1) hU
      have hiff : s'.2 ∈ RecTrialSN P i K m J ↔ a.2 ∈ RecTrialSN P i K m J := by
        show (s'.2.1.1 _ ≠ none ∧ s'.2.2.2.2 i K = none) ↔
          (a.2.1.1 _ ≠ none ∧ a.2.2.2.2 i K = none)
        rw [hc, hm']
        exact ⟨fun h ↦ ⟨h.1, hU'⟩, fun h ↦ ⟨h.1, hU⟩⟩
      rw [ite_eq_left hU, one_mul]
      by_cases ha : a.2 ∈ RecTrialSN P i K m J
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hiff.2 ha), Pi.one_apply,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (mt hiff.1 ha)]
    · rw [ite_eq_right hU, zero_mul]
      refine Set.indicator_of_notMem (fun hs ↦ hU ?_) _
      have h2 := hs.2
      rwa [hm'] at h2
  · obtain ⟨-, hKa⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) ha
    obtain ⟨-, hKb⟩ :=
      one_kronecker_ne_zero (a := a'.1) (a' := s'.1) (b := a'.2) (b' := s'.2) ha'
    have hca := readKrausH_ne_zero_cellsSN z u r hKa _ hz.symm
    have hcb := readKrausH_ne_zero_cellsSN z u r hKb _ hz.symm
    have hma := (readKrausH_ne_zero_memSN z u r hKa).1
    have hmb := (readKrausH_ne_zero_memSN z u r hKb).1
    have hiff : a.2 ∈ RecTrialSN P i K m J ↔ a'.2 ∈ RecTrialSN P i K m J := by
      show (a.2.1.1 _ ≠ none ∧ a.2.2.2.2 i K = none) ↔
        (a'.2.1.1 _ ≠ none ∧ a'.2.2.2.2 i K = none)
      rw [← hca, ← hcb, hma, hmb]
    by_cases h' : a.2 ∈ RecTrialSN P i K m J
    · rw [Set.indicator_of_mem h', Set.indicator_of_mem (hiff.1 h'), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (mt hiff.2 h')]

/-- A record keeps every trial set. -/
theorem sum_pot_recTrialSN_rec_le (P : Fin n → PublicParameter) (i : Fin n) (K : Key)
    (m : Digest) (J : ℕ) (T : Finset (TPosN n))
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ mm : QMemSN n, potential (setProj (RecTrialSN P i K m J))
        (MatrixMap.conj (recKraus (X := PairOut) (Z := HashDomain) T mm) σ) ≤
      potential (setProj (RecTrialSN P i K m J)) σ :=
  cw_sum_pot_setProj_keep _ (sum_recKraus T) _ (fun mm s' a h ↦ by
    rw [eq_of_recKraus_ne_zero (u := a.1) (u' := s'.1) (s := a.2) (s' := s'.2) h]
    rfl) hσ

/-! ## The reveal charges and the moded potential -/

/-- **The reveal charges** at the hidden values `θ`: at a reveal of user `i`'s key coordinate,
the masses of the key's trials on its value under `parQSN θ i` recorded with the key
unselected. -/
noncomputable def revQWSN (θ : TValsN n) : ∀ x : (RSpecSN n (SelMemN n)).Port,
    Matrix ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n)) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match keyOfTSN T with
    | some (i, K) => ∑ J : Fin encodingAttemptLimit, diagMass {q : Unit × RRegSN n (SelMemN n) |
        q.2 ∈ RecTrialSN (parQSN θ) i K ((tabOf (userOf θ i)).valuePos (msgPos K)) J} σ
    | none => 0
  | _, _ => 0

theorem trialWSN_recUWtSN_eq (P : Fin n → PublicParameter) (i : Fin n) (K : Key) (m : Digest)
    (j : ℕ) {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    trialWSN recUWtSN (trialReadSN (trialCell (P i) K m j) (i, K)) σ =
      potential (setProj (RecTrialSN P i K m j)) σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [trialWSN_trialReadSN, potential_setProj _ hσ, diagMass,
    ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by unfold recUWtSN; split_ifs <;> norm_num)
      (hre q)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hiff : (q.2.1.1 (trialCell (P i) K m j) ≠ none ∧ memAtS q.2 (i, K) = none) ↔
      q ∈ {q : Unit × RRegSN n (SelMemN n) | q.2 ∈ RecTrialSN P i K m j} :=
    Iff.rfl
  by_cases h : q.2.1.1 (trialCell (P i) K m j) ≠ none ∧ memAtS q.2 (i, K) = none
  · rw [show recUWtSN (trialCell (P i) K m j) (i, K) q.2 = 1 from ite_eq_left h, one_mul,
      Set.indicator_of_mem (hiff.1 h)]
  · rw [show recUWtSN (trialCell (P i) K m j) (i, K) q.2 = 0 from ite_eq_right h,
      zero_mul, ENNReal.ofReal_zero, Set.indicator_of_notMem (mt hiff.2 h)]

theorem sum_pot_trialSetSN_split (P : Fin n → PublicParameter) (ks : Finset (Fin n × Key))
    (i : Fin n) (K : Key) (m : Digest) {j : ℕ} (hj : j < encodingAttemptLimit)
    (τ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ) :
    ∑ J : Fin encodingAttemptLimit, potential (setProj (trialSetSN P (.grd ks i K m j) J.val)) τ =
      potential (setProj (RecTrialSN P i K m j)) τ +
        ∑ J : Fin encodingAttemptLimit,
          potential (setProj (trialSetSN P (.grd ks i K m (j + 1)) J.val)) τ := by
  have h : ∀ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetSN P (.grd ks i K m j) J.val)) τ =
        (if J = ⟨j, hj⟩ then potential (setProj (RecTrialSN P i K m j)) τ else 0) +
          potential (setProj (trialSetSN P (.grd ks i K m (j + 1)) J.val)) τ := fun J ↦ by
    by_cases hJ : J = ⟨j, hj⟩
    · subst hJ
      show potential (setProj (if j ≤ j then RecTrialSN P i K m j else ∅)) τ =
        (if (⟨j, hj⟩ : Fin encodingAttemptLimit) = ⟨j, hj⟩ then _ else 0) +
          potential (setProj (if j + 1 ≤ j then RecTrialSN P i K m j else ∅)) τ
      rw [ite_eq_left le_rfl, ite_eq_left rfl, ite_eq_right (by omega), potential_setProj_emptyU,
        add_zero]
    · show potential (setProj (if j ≤ J.val then RecTrialSN P i K m J.val else ∅)) τ =
        (if J = ⟨j, hj⟩ then _ else 0) +
          potential (setProj (if j + 1 ≤ J.val then RecTrialSN P i K m J.val else ∅)) τ
      have hne : J.val ≠ j := fun h' ↦ hJ (Fin.ext h')
      rw [ite_eq_right hJ, zero_add]
      by_cases h1 : j + 1 ≤ J.val
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  rw [Finset.sum_congr rfl fun J _ ↦ h J, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- **A trial read on the trial sets**: its recorded unselected weight plus the later trials'
masses after it are at most the trials' masses before it. -/
theorem readH_stepSN (P : Fin n → PublicParameter) (ks : Finset (Fin n × Key)) (i : Fin n)
    (K : Key) (m : Digest) {j : ℕ} (hj : j < encodingAttemptLimit)
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    trialWSN recUWtSN (trialReadSN (trialCell (P i) K m j) (i, K)) σ +
        ∑' r : Option PairOut × QMemSN n, ∑ J : Fin encodingAttemptLimit,
          potential (setProj (trialSetSN P (srchRdNxSN (.grd ks i K m j)
            (trialReadSN (trialCell (P i) K m j) (i, K)) r) J.val))
            (MatrixMap.conj (hwReadKraus (trialReadSN (trialCell (P i) K m j) (i, K)) r) σ) ≤
      ∑ J : Fin encodingAttemptLimit,
        potential (setProj (trialSetSN P (.grd ks i K m j) J.val)) σ := by
  rw [sum_pot_trialSetSN_split P ks i K m hj, trialWSN_recUWtSN_eq P i K m j hσ, tsum_fintype]
  refine add_le_add le_rfl ?_
  set z := trialCell (P i) K m j
  have hmono : ∀ (r : Option PairOut × QMemSN n) (J : Fin encodingAttemptLimit),
      potential (setProj (trialSetSN P (srchRdNxSN (.grd ks i K m j) (trialReadSN z (i, K)) r)
          J.val)) (MatrixMap.conj (hwReadKraus (trialReadSN z (i, K)) r) σ) ≤
      potential (setProj (trialSetSN P (.grd ks i K m (j + 1)) J.val))
        (MatrixMap.conj (hwReadKraus (trialReadSN z (i, K)) r) σ) := fun r J ↦ by
    show potential (setProj (trialSetSN P
      (decNxSN ks i K m j (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1))) J.val)) _ ≤ _
    generalize TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = dd
    cases dd with
    | some _ => exact le_of_eq_of_le (potential_setProj_emptyU _) zero_le
    | none => exact le_rfl
  refine (Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun J _ ↦ hmono r J).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun J _ ↦ ?_
  show ∑ r : Option PairOut × QMemSN n, potential (setProj
      (if j + 1 ≤ J.val then RecTrialSN P i K m J.val else ∅)) _ ≤
    potential (setProj (if j + 1 ≤ J.val then RecTrialSN P i K m J.val else ∅)) σ
  split_ifs with hJ
  · refine sum_pot_recTrialSN_readH_le P i K m J.val (fun h ↦ ?_) (i, K) hσ
    have := (trialCell_injU hj J.isLt h).2
    omega
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun r _ ↦ potential_setProj_emptyU _) zero_le

/-- **The step of the moded potential**: the recorded unselected weight of a trial read plus the
later trials' masses after it are at most the trials' masses before it; a reveal of a key's
coordinate charges its trials' masses. -/
theorem revQWSN_step (θ : TValsN n) (μ : ModeSN n) (x : (RSpecSN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n)) ℂ) (hσ : σ.PosSemidef)
    (hok : srchOkZSN (parQSN θ) μ x) :
    extWeight (D := RDSN n) (hwCost (trialWSN recUWtSN) fun _ _ ↦ 0) x σ +
        ∑' r, ∑ J : Fin encodingAttemptLimit,
          potential (setProj (trialSetSN (parQSN θ) (srchNxZSN θ μ x r) J.val))
            (((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step x).branch r σ) ≤
      ∑ J : Fin encodingAttemptLimit, potential (setProj (trialSetSN (parQSN θ) μ J.val)) σ +
        revQWSN θ x σ := by
  rcases x with ((p | c) | c) | T
  · show (0 : ℝ≥0∞) + ∑' r, ∑ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetSN (parQSN θ) (.rest μ.ks) J.val)) _ ≤ _
    refine le_of_eq_of_le ?_ zero_le
    rw [zero_add]
    exact ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦
      potential_setProj_emptyU _
  · rcases μ with ks | ⟨ks, i, K, m, j⟩
    · exact hok.elim
    have hb : ∀ r, ((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step
        (.inl (.inl (.inr c)))).branch r σ = MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun
        (spongeHardwiredRuntime_step_read (hwEmpty PairOut HashDomain) m0SN c r) σ
    rw [show revQWSN θ (.inl (.inl (.inr c))) σ = 0 from rfl, add_zero]
    refine (add_le_add le_rfl (le_of_eq (tsum_congr fun r ↦ congrArg (fun τ ↦
      ∑ J : Fin encodingAttemptLimit, potential (setProj (trialSetSN (parQSN θ)
        (srchRdNxSN (.grd ks i K m j) c r) J.val)) τ) (hb r)))).trans ?_
    show trialWSN recUWtSN c σ + ∑' r : c.Result, ∑ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetSN (parQSN θ) (srchRdNxSN (.grd ks i K m j) c r) J.val))
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      ∑ J : Fin encodingAttemptLimit,
        potential (setProj (trialSetSN (parQSN θ) (.grd ks i K m j) J.val)) σ
    obtain ⟨hj, rfl⟩ := hok
    exact readH_stepSN (parQSN θ) ks i K m hj hσ
  · show (0 : ℝ≥0∞) + ∑' r, ∑ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetSN (parQSN θ) (.rest μ.ks) J.val)) _ ≤ _
    refine le_of_eq_of_le ?_ zero_le
    rw [zero_add]
    exact ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦
      potential_setProj_emptyU _
  · show (0 : ℝ≥0∞) + ∑' mm, ∑ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetSN (parQSN θ)
        (revNxSN μ T fun i K ↦ (tabOf (userOf θ i)).valuePos (msgPos K)) J.val))
        (MatrixMap.conj (recKraus (X := PairOut) (Z := HashDomain) T mm) σ) ≤ _
    rw [zero_add]
    rcases hT : keyOfTSN T with _ | ⟨i, K⟩
    · rw [revNxSN_none μ hT]
      exact le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun mm ↦ Finset.sum_eq_zero fun J _ ↦
        potential_setProj_emptyU _) zero_le
    · have hn : revNxSN μ T (fun i K ↦ (tabOf (userOf θ i)).valuePos (msgPos K)) =
          .grd (insert (i, K) μ.ks) i K ((tabOf (userOf θ i)).valuePos (msgPos K)) 0 := by
        unfold revNxSN
        rw [hT]
      rw [hn]
      refine le_add_left ?_
      show _ ≤ (match keyOfTSN T with
        | some (i, K) => ∑ J : Fin encodingAttemptLimit,
            diagMass {q : Unit × RRegSN n (SelMemN n) |
              q.2 ∈ RecTrialSN (parQSN θ) i K ((tabOf (userOf θ i)).valuePos (msgPos K)) J} σ
        | none => 0)
      rw [hT, tsum_fintype, Finset.sum_comm]
      refine Finset.sum_le_sum fun J _ ↦ ?_
      show ∑ mm : QMemSN n, potential (setProj (if 0 ≤ J.val then
        RecTrialSN (parQSN θ) i K ((tabOf (userOf θ i)).valuePos (msgPos K)) J.val else ∅))
          (MatrixMap.conj (recKraus (X := PairOut) (Z := HashDomain) T mm) σ) ≤
        diagMass {q : Unit × RRegSN n (SelMemN n) |
          q.2 ∈ RecTrialSN (parQSN θ) i K ((tabOf (userOf θ i)).valuePos (msgPos K)) J.val} σ
      rw [ite_eq_left (Nat.zero_le _)]
      exact (sum_pot_recTrialSN_rec_le _ _ _ _ _ T hσ).trans_eq (potential_setProj _ hσ)

/-- **The recorded unselected weights are at most the reveal charges.** -/
theorem recUPreSN_le_revQWSN (A : MuAdversaryS n) (θ : TValsN n) :
    recUPreSN A θ ≤ (runtimeR (m0SN (n := n))).totalWeight .instruments (revQWSN θ)
      (prefixQSN (strPolN n) A θ) initQSN := by
  refine (totalWeight_le_modedP (runtimeR (m0SN (n := n))) .instruments
    (Zp := RRegSN n (SelMemN n))
    (fun μ (J : Fin encodingAttemptLimit) ↦ setProj (trialSetSN (parQSN θ) μ J.val))
    (extWeight (hwCost (trialWSN recUWtSN) fun _ _ ↦ 0)) (revQWSN θ)
    (fun μ x σ hσ hok ↦ revQWSN_step θ μ x σ hσ hok) (prefixQSN (strPolN n) A θ) (.rest ∅)
    (modedP_prefixQSN (fun _ ↦ noVal_strPol) A θ) initQSN_posSemidef).trans (le_of_eq ?_)
  rw [Finset.sum_eq_zero fun j _ ↦ potential_of_eq_zeroU
    (setProj_trialSetSN_rest (parQSN θ) ∅ j.val) initQSN, zero_add]

/-! ## First and repeated reveals -/

/-- **The first-reveal charges** at the hidden values `θ`: at a reveal of user `i`'s key
coordinate not yet revealed, the masses of the key's recorded trial cells on its value under
`parQSN θ i`. -/
noncomputable def firstQWSN (θ : TValsN n) : ∀ x : (RSpecSN n (SelMemN n)).Port,
    Matrix ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n)) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match keyOfTSN T with
    | some (i, K) => ∑ J : Fin encodingAttemptLimit, diagMass {q : Unit × RRegSN n (SelMemN n) |
        (i, vcoord (msgPos K)) ∉ q.2.2.2.1 ∧
          q.2.1.1 (trialCell (parQSN θ i) K ((tabOf (userOf θ i)).valuePos (msgPos K)) J) ≠
            none} σ
    | none => 0
  | _, _ => 0

theorem revQWSN_le (θ : TValsN n) (x : (RSpecSN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n)) ℂ) :
    revQWSN θ x σ ≤ 1 * firstQWSN θ x σ + 1 * reRevQWSN x σ := by
  rw [one_mul, one_mul]
  rcases x with ((p | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · show (match keyOfTSN T with
        | some (i, K) => ∑ J : Fin encodingAttemptLimit,
            diagMass {q : Unit × RRegSN n (SelMemN n) |
              q.2 ∈ RecTrialSN (parQSN θ) i K ((tabOf (userOf θ i)).valuePos (msgPos K)) J} σ
        | none => 0) ≤ (match keyOfTSN T with
        | some (i, K) => ∑ J : Fin encodingAttemptLimit,
            diagMass {q : Unit × RRegSN n (SelMemN n) | (i, vcoord (msgPos K)) ∉ q.2.2.2.1 ∧
              q.2.1.1 (trialCell (parQSN θ i) K ((tabOf (userOf θ i)).valuePos (msgPos K)) J) ≠
                none} σ
        | none => 0) + (match keyOfTSN T with
        | some (i, K) => (encodingAttemptLimit : ℝ≥0∞) *
            diagMass {q : Unit × RRegSN n (SelMemN n) | ReRevQSN i K q.2} σ
        | none => 0)
    rcases keyOfTSN T with _ | ⟨i, K⟩
    · exact zero_le
    · have hN : (encodingAttemptLimit : ℝ≥0∞) *
          diagMass {q : Unit × RRegSN n (SelMemN n) | ReRevQSN i K q.2} σ =
          ∑ _J : Fin encodingAttemptLimit,
            diagMass {q : Unit × RRegSN n (SelMemN n) | ReRevQSN i K q.2} σ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only
      rw [hN, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun J _ ↦ diagMass_le_add_of_subsetU (fun q hq ↦ ?_) σ
      by_cases hl : (i, vcoord (msgPos K)) ∈ q.2.2.2.1
      · exact .inr ⟨hl, hq.2⟩
      · exact .inl ⟨hl, hq.1⟩

/-- **The reveal charges split into the first and the repeated reveals.** -/
theorem recUPreSN_le_split (A : MuAdversaryS n) (θ : TValsN n) :
    recUPreSN A θ ≤
      (runtimeR (m0SN (n := n))).totalWeight .instruments (firstQWSN θ)
          (prefixQSN (strPolN n) A θ) initQSN +
        (runtimeR (m0SN (n := n))).totalWeight .instruments reRevQWSN
          (prefixQSN (strPolN n) A θ) initQSN := by
  refine (recUPreSN_le_revQWSN A θ).trans ((totalWeight_le_add (runtimeR (m0SN (n := n)))
    .instruments _ _ _ 1 1 (fun x σ _ ↦ revQWSN_le θ x σ) (prefixQSN (strPolN n) A θ)
    initQSN_posSemidef).trans_eq ?_)
  rw [one_mul, one_mul]

end Quantum.Qrom.Sphincs.Multi

end
