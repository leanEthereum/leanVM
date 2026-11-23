module

public import Quantum.Qrom.Sphincs.Costs.RecUModes

@[expose] public section

/-!
# The recorded unselected weights, moved onto the reveals that start the searches

The recorded unselected weight `recUWt` at the read of trial `j` of a search (the read cell
recorded, the key unselected) is moved to the reveal that starts the search: between that reveal
and the read only the search's earlier reads happen, at other cells, and they can only select the
key. The moded potential (CwRec's `totalWeight_le_modedP`) in the search of `K` on `m` before
trial `j` is the mass of the later trials' sets `RecTrialU`.

* `RecTrialU`, `trialSetU`: a trial recorded with the key unselected, the trials still to come in
  a mode.
* **`recUPre_le_revQW`**: `recUPre pol A θ` is at most the reveal charges `revQWU θ` (at a reveal
  of a key's coordinate, the masses of its recorded trials with the key unselected).
* **`recUPre_le_split`**: the reveal charges split into the first reveals (`firstQWU θ`: the
  coordinate unrevealed, the trial cell recorded) and the repeated reveals with the key unselected
  (`reRevQWU`: `2^32` times the mass of `ReRevU K`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

universe u v w

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (diagMass setProj)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR liftRead extWeight ModedP
  totalWeight_le_modedP cw_sum_pot_setProj_le cw_sum_pot_setProj_keep cw_clsKraus_ne_zero
  potential_setProj eq_of_recKraus_ne_zero totalWeight_le_add recKraus sum_recKraus)

attribute [local irreducible] sphincsRom Fin.fintype

/- Instance search for the register's decidable equality exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The trials of a search -/

/-- **Trial `J` of the search of `K` on `m` recorded, with the key unselected.** -/
def RecTrialU (P : PublicParameter) (K : Key) (m : Digest) (J : ℕ) : Set RegQ :=
  {s | s.1.1 (trialCell P K m J) ≠ none ∧ s.2.2.2 K = none}

/-- **The trials still to come in a mode**: trial `J` at or after the current trial. -/
def trialSetU (P : PublicParameter) : ModeU → ℕ → Set RegQ
  | .grd _ K m j, J => if j ≤ J then RecTrialU P K m J else ∅
  | .rest _, _ => ∅

/-- A trial read never unselects a key. -/
theorem cwUpd_eq_noneU {K K' : Key} {z : Qrom.HashDomain} {m : SelMem} {o : Option PairOut}
    (h : cwUpd K z m o K' = none) : m K' = none := by
  rcases o with _ | ω
  · exact h
  · rcases cwUpd_some K z m ω with h' | h'
    · rwa [h'] at h
    · rw [h'] at h
      unfold cwSel at h
      split_ifs at h
      · unfold SelMem.select at h
        by_cases hK : K' = K
        · subst hK
          rw [Function.update_self] at h
          exact absurd h (Option.some_ne_none _)
        · rwa [Function.update_of_ne hK] at h
      · exact h

/-- **An encoding cell names its value and trial**, below `2^32` trials. -/
theorem trialCell_injU {P : PublicParameter} {K : Key} {m m' : Digest} {i j : ℕ}
    (hi : i < encodingAttemptLimit) (hj : j < encodingAttemptLimit)
    (h : trialCell P K m i = trialCell P K m' j) : m = m' ∧ i = j := by
  have h1 := cell_injective ⟨0, 0, P⟩ 0 (s := .enc K.1 K.2.1 K.2.2)
    (s' := .enc K.1 K.2.1 K.2.2) trivial trivial h
  have h2 : ((m, BitVec.ofNat counterBits i) : Digest × EncodingCounter) =
      (m', BitVec.ofNat counterBits j) := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
  refine ⟨congrArg Prod.fst h2, ?_⟩
  have h4 := congrArg BitVec.toNat (congrArg Prod.snd h2)
  have hN : encodingAttemptLimit = 2 ^ counterBits := rfl
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hN ▸ hi),
    Nat.mod_eq_of_lt (hN ▸ hj)] at h4
  exact h4

/-! ## Potentials of trial sets along the ports -/

theorem potential_setProj_emptyU {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (τ : Matrix (A × D) (A × D) ℂ) : potential (setProj (∅ : Set D)) τ = 0 := by
  rw [potential_eq]
  simp [setProj]

theorem potential_of_eq_zeroU {A Z D : Type} [Fintype A] [DecidableEq A] [Fintype Z] [Fintype D]
    {K : Matrix Z D ℂ} (hK : K = 0) (τ : Matrix (A × D) (A × D) ℂ) : potential K τ = 0 := by
  subst hK
  rw [potential_eq]
  simp

theorem setProj_trialSet_restU (P : PublicParameter) (ks : Finset Key) (J : ℕ) :
    setProj (trialSetU P (.rest ks) J) = (0 : Matrix RegQ RegQ ℂ) := by
  show setProj (∅ : Set RegQ) = 0
  ext a b
  simp [setProj]

/-- A nonzero entry of a read of the `h`-cell `z`: the other `h`-cells kept. -/
theorem readKrausH_ne_zero_cellsU (z : Qrom.HashDomain) (upd : QMem → Option PairOut → QMem)
    (r : Option PairOut × QMem) {s' s : RegQ} (h : readKrausH z upd r s' s ≠ 0)
    (x : Qrom.HashDomain) (hx : x ≠ z) : s'.1.1 x = s.1.1 x := by
  obtain ⟨-, -, hR⟩ := cw_clsKraus_ne_zero h
  rw [kroneckerMap_apply] at hR
  exact cellRead_apply_ne_zero (left_ne_zero_of_mul hR) x hx

theorem readKrausH_ne_zero_memU (z : Qrom.HashDomain) (upd : QMem → Option PairOut → QMem)
    (r : Option PairOut × QMem) {s' s : RegQ} (h : readKrausH z upd r s' s ≠ 0) :
    s.2.2 = r.2 ∧ s'.2.2 = upd r.2 r.1 :=
  ⟨(Quantum.Xmss.Assembly.cw_readKrausH_ne_zero z upd r h).2.2.1,
    (Quantum.Xmss.Assembly.cw_readKrausH_ne_zero z upd r h).2.2.2⟩

open scoped Classical in
/-- **A trial read keeps another trial's set, up to selecting the key.** -/
theorem sum_pot_recTrial_readHU (P : PublicParameter) (K : Key) (m : Digest) (J : ℕ)
    {z : Qrom.HashDomain} (hz : z ≠ trialCell P K m J) (K' : Key)
    {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef) :
    ∑ r : Option PairOut × QMem, potential (setProj (RecTrialU P K m J))
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K' z)) r) σ) ≤
      potential (setProj (RecTrialU P K m J)) σ := by
  set u := trialUpdQ K' z
  refine cw_sum_pot_setProj_le (fun r ↦ hwReadKraus (.readH z u) r) (sum_hwReadKraus _) _ _
    (fun r ↦ if (u r.2 r.1).2 K = none then 1 else 0) (fun r ↦ by split_ifs <;> norm_num)
    (fun r s' a h ↦ ?_) (fun r s' a a' ha ha' ↦ ?_) hσ
  · obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
    have hc := readKrausH_ne_zero_cellsU z u r hK _ hz.symm
    obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_memU z u r hK
    by_cases hU : (u r.2 r.1).2 K = none
    · have hU' : a.2.2.2.2 K = none := by
        rw [hm]
        exact cwUpd_eq_noneU hU
      have hiff : s'.2 ∈ RecTrialU P K m J ↔ a.2 ∈ RecTrialU P K m J := by
        show (s'.2.1.1 _ ≠ none ∧ s'.2.2.2.2 K = none) ↔ (a.2.1.1 _ ≠ none ∧ a.2.2.2.2 K = none)
        rw [hc, hm']
        exact ⟨fun h ↦ ⟨h.1, hU'⟩, fun h ↦ ⟨h.1, hU⟩⟩
      rw [ite_eq_left hU, one_mul]
      by_cases ha : a.2 ∈ RecTrialU P K m J
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
    have hca := readKrausH_ne_zero_cellsU z u r hKa _ hz.symm
    have hcb := readKrausH_ne_zero_cellsU z u r hKb _ hz.symm
    have hma := (readKrausH_ne_zero_memU z u r hKa).1
    have hmb := (readKrausH_ne_zero_memU z u r hKb).1
    have hiff : a.2 ∈ RecTrialU P K m J ↔ a'.2 ∈ RecTrialU P K m J := by
      show (a.2.1.1 _ ≠ none ∧ a.2.2.2.2 K = none) ↔ (a'.2.1.1 _ ≠ none ∧ a'.2.2.2.2 K = none)
      rw [← hca, ← hcb, hma, hmb]
    by_cases h' : a.2 ∈ RecTrialU P K m J
    · rw [Set.indicator_of_mem h', Set.indicator_of_mem (hiff.1 h'), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (mt hiff.2 h')]

/-- A record keeps every trial set. -/
theorem sum_pot_recTrial_recU (P : PublicParameter) (K : Key) (m : Digest) (J : ℕ)
    (T : Finset TPos) {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef) :
    ∑ mm : QMem, potential (setProj (RecTrialU P K m J))
        (MatrixMap.conj (recKraus (X := PairOut) (Z := Qrom.HashDomain) T mm) σ) ≤
      potential (setProj (RecTrialU P K m J)) σ :=
  cw_sum_pot_setProj_keep _ (sum_recKraus T) _ (fun mm s' a h ↦ by
    rw [eq_of_recKraus_ne_zero (u := a.1) (u' := s'.1) (s := a.2) (s' := s'.2) h]
    rfl) hσ

/-! ## The reveal charges and the moded potential -/

/-- **The reveal charges** at the hidden values `θ`: at a reveal of a key's coordinate, the masses
of the key's trials on its value recorded with the key unselected. -/
noncomputable def revQWU (θ : TVals) :
    ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
      Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
        ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match keyOfTU T with
    | some K => ∑ J : Fin encodingAttemptLimit, diagMass {q : Unit × RegQ |
        q.2 ∈ RecTrialU (tabOf θ).publicSeed K ((tabOf θ).valuePos (msgPos K)) J} σ
    | none => 0
  | _, _ => 0

theorem trialW_recUWt_eqU (θ : TVals) (K : Key) (m : Digest) (j : ℕ)
    {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef) :
    trialW (pkQ θ) recUWt (.readH (trialCell (tabOf θ).publicSeed K m j)
        (trialUpdQ K (trialCell (tabOf θ).publicSeed K m j))) σ =
      potential (setProj (RecTrialU (tabOf θ).publicSeed K m j)) σ := by
  classical
  have hz : slotOf (pkQ θ) (trialCell (tabOf θ).publicSeed K m j) =
      some (.enc K.1 K.2.1 K.2.2) :=
    slotOf_trialCell (pkQ θ) K m j
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [← trialRead_eq, trialW_trialRead _ hz, potential_setProj _ hσ, diagMass,
    ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by unfold recUWt; split_ifs <;> norm_num)
      (hre q)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hiff : (q.2.1.1 (trialCell (tabOf θ).publicSeed K m j) ≠ none ∧ q.2.2.2.2 K = none) ↔
      q ∈ {q : Unit × RegQ | q.2 ∈ RecTrialU (tabOf θ).publicSeed K m j} :=
    Iff.rfl
  by_cases h : q.2.1.1 (trialCell (tabOf θ).publicSeed K m j) ≠ none ∧ q.2.2.2.2 K = none
  · rw [show recUWt (trialCell (tabOf θ).publicSeed K m j) K q.2 = 1 from ite_eq_left h,
      one_mul, Set.indicator_of_mem (hiff.1 h)]
  · rw [show recUWt (trialCell (tabOf θ).publicSeed K m j) K q.2 = 0 from ite_eq_right h,
      zero_mul, ENNReal.ofReal_zero, Set.indicator_of_notMem (mt hiff.2 h)]

theorem sum_pot_trialSet_splitU (P : PublicParameter) (ks : Finset Key) (K : Key) (m : Digest)
    {j : ℕ} (hj : j < encodingAttemptLimit) (τ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ) :
    ∑ J : Fin encodingAttemptLimit, potential (setProj (trialSetU P (.grd ks K m j) J.val)) τ =
      potential (setProj (RecTrialU P K m j)) τ +
        ∑ J : Fin encodingAttemptLimit,
          potential (setProj (trialSetU P (.grd ks K m (j + 1)) J.val)) τ := by
  have h : ∀ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetU P (.grd ks K m j) J.val)) τ =
        (if J = ⟨j, hj⟩ then potential (setProj (RecTrialU P K m j)) τ else 0) +
          potential (setProj (trialSetU P (.grd ks K m (j + 1)) J.val)) τ := fun J ↦ by
    by_cases hJ : J = ⟨j, hj⟩
    · subst hJ
      show potential (setProj (if j ≤ j then RecTrialU P K m j else ∅)) τ =
        (if (⟨j, hj⟩ : Fin encodingAttemptLimit) = ⟨j, hj⟩ then _ else 0) +
          potential (setProj (if j + 1 ≤ j then RecTrialU P K m j else ∅)) τ
      rw [ite_eq_left le_rfl, ite_eq_left rfl, ite_eq_right (by omega), potential_setProj_emptyU,
        add_zero]
    · have hne : J.val ≠ j := fun h' ↦ hJ (Fin.ext h')
      show potential (setProj (if j ≤ J.val then RecTrialU P K m J.val else ∅)) τ =
        (if J = ⟨j, hj⟩ then _ else 0) +
          potential (setProj (if j + 1 ≤ J.val then RecTrialU P K m J.val else ∅)) τ
      rw [ite_eq_right hJ, zero_add]
      by_cases h1 : j + 1 ≤ J.val
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  rw [Finset.sum_congr rfl fun J _ ↦ h J, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- **A trial read on the trial sets**: its recorded unselected weight plus the later trials'
masses after it are at most the trials' masses before it. -/
theorem readH_stepU (θ : TVals) (ks : Finset Key) (K : Key) (m : Digest) {j : ℕ}
    (hj : j < encodingAttemptLimit) {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ}
    (hσ : σ.PosSemidef) :
    trialW (pkQ θ) recUWt (.readH (trialCell (tabOf θ).publicSeed K m j)
        (trialUpdQ K (trialCell (tabOf θ).publicSeed K m j))) σ +
      ∑' r : Option PairOut × QMem, ∑ J : Fin encodingAttemptLimit,
        potential (setProj (trialSetU (tabOf θ).publicSeed (srchRdNxU (.grd ks K m j)
          (.readH (trialCell (tabOf θ).publicSeed K m j)
            (trialUpdQ K (trialCell (tabOf θ).publicSeed K m j))) r) J.val))
          (MatrixMap.conj (hwReadKraus (.readH (trialCell (tabOf θ).publicSeed K m j)
            (trialUpdQ K (trialCell (tabOf θ).publicSeed K m j))) r) σ) ≤
      ∑ J : Fin encodingAttemptLimit,
        potential (setProj (trialSetU (tabOf θ).publicSeed (.grd ks K m j) J.val)) σ := by
  set P := (tabOf θ).publicSeed
  set z := trialCell P K m j with hzdef
  rw [sum_pot_trialSet_splitU P ks K m hj, trialW_recUWt_eqU θ K m j hσ, tsum_fintype]
  refine add_le_add le_rfl ?_
  have hmono : ∀ (r : Option PairOut × QMem) (J : Fin encodingAttemptLimit),
      potential (setProj (trialSetU P (srchRdNxU (.grd ks K m j) (.readH z (trialUpdQ K z)) r)
          J.val)) (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ) ≤
      potential (setProj (trialSetU P (.grd ks K m (j + 1)) J.val))
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ) := fun r J ↦ by
    show potential (setProj (trialSetU P
      (decNxU ks K m j (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1))) J.val)) _ ≤ _
    generalize TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = dd
    cases dd with
    | some _ => exact le_of_eq_of_le (potential_setProj_emptyU _) zero_le
    | none => exact le_rfl
  refine (Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun J _ ↦ hmono r J).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun J _ ↦ ?_
  show ∑ r : Option PairOut × QMem, potential (setProj
      (if j + 1 ≤ J.val then RecTrialU P K m J.val else ∅)) _ ≤
    potential (setProj (if j + 1 ≤ J.val then RecTrialU P K m J.val else ∅)) σ
  split_ifs with hJ
  · refine sum_pot_recTrial_readHU P K m J.val (fun h ↦ ?_) K hσ
    have := (trialCell_injU hj J.isLt h).2
    omega
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun r _ ↦ potential_setProj_emptyU _) zero_le

/-- **The step of the moded potential**: the recorded unselected weight of a trial read plus the
later trials' masses after it are at most the trials' masses before it; a reveal of a key's
coordinate charges its trials' masses. -/
theorem revQW_stepU (θ : TVals) (μ : ModeU)
    (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ) (hσ : σ.PosSemidef)
    (hok : srchOkZ θ μ i) :
    extWeight (hwCost (trialW (pkQ θ) recUWt) fun _ _ ↦ 0) i σ +
        ∑' r, ∑ J : Fin encodingAttemptLimit,
          potential (setProj (trialSetU (tabOf θ).publicSeed (srchNxZ θ μ i r) J.val))
            (((runtimeR m0Q).step i).branch r σ) ≤
      ∑ J : Fin encodingAttemptLimit,
          potential (setProj (trialSetU (tabOf θ).publicSeed μ J.val)) σ +
        revQWU θ i σ := by
  rcases i with ((p | c) | c) | T
  · show (0 : ℝ≥0∞) + ∑' r, ∑ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetU (tabOf θ).publicSeed (.rest μ.ks) J.val)) _ ≤ _
    refine le_of_eq_of_le ?_ zero_le
    rw [zero_add]
    exact ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦
      potential_setProj_emptyU _
  · rcases μ with ks | ⟨ks, K, m, j⟩
    · exact hok.elim
    have hb : ∀ r, ((runtimeR m0Q).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦ LinearMap.congr_fun
          (spongeHardwiredRuntime_step_read (hwEmpty PairOut Qrom.HashDomain) m0Q c r) σ
    rw [show revQWU θ (.inl (.inl (.inr c))) σ = 0 from rfl, add_zero]
    refine (add_le_add le_rfl (le_of_eq (tsum_congr fun r ↦ congrArg (fun τ ↦
      ∑ J : Fin encodingAttemptLimit, potential (setProj (trialSetU (tabOf θ).publicSeed
        (srchRdNxU (.grd ks K m j) c r) J.val)) τ) (hb r)))).trans ?_
    show trialW (pkQ θ) recUWt c σ + ∑' r : c.Result, ∑ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetU (tabOf θ).publicSeed (srchRdNxU (.grd ks K m j) c r) J.val))
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      ∑ J : Fin encodingAttemptLimit,
        potential (setProj (trialSetU (tabOf θ).publicSeed (.grd ks K m j) J.val)) σ
    obtain ⟨hj, rfl⟩ := hok
    rw [trialRead_eq]
    exact readH_stepU θ ks K m hj hσ
  · show (0 : ℝ≥0∞) + ∑' r, ∑ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetU (tabOf θ).publicSeed (.rest μ.ks) J.val)) _ ≤ _
    refine le_of_eq_of_le ?_ zero_le
    rw [zero_add]
    exact ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦
      potential_setProj_emptyU _
  · show (0 : ℝ≥0∞) + ∑' mm, ∑ J : Fin encodingAttemptLimit,
      potential (setProj (trialSetU (tabOf θ).publicSeed
        (revNxU μ T fun K ↦ (tabOf θ).valuePos (msgPos K)) J.val))
        (MatrixMap.conj (recKraus (X := PairOut) (Z := Qrom.HashDomain) T mm) σ) ≤ _
    rw [zero_add]
    rcases hT : keyOfTU T with _ | K
    · rw [revNxU_none μ hT]
      exact le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun mm ↦ Finset.sum_eq_zero fun J _ ↦
        potential_setProj_emptyU _) zero_le
    · have hn : revNxU μ T (fun K ↦ (tabOf θ).valuePos (msgPos K)) =
          .grd (insert K μ.ks) K ((tabOf θ).valuePos (msgPos K)) 0 := by
        unfold revNxU
        rw [hT]
      rw [hn]
      refine le_add_left ?_
      show _ ≤ (match keyOfTU T with
        | some K => ∑ J : Fin encodingAttemptLimit, diagMass {q : Unit × RegQ |
            q.2 ∈ RecTrialU (tabOf θ).publicSeed K ((tabOf θ).valuePos (msgPos K)) J} σ
        | none => 0)
      rw [hT, tsum_fintype, Finset.sum_comm]
      refine Finset.sum_le_sum fun J _ ↦ ?_
      show ∑ mm : QMem, potential (setProj (if 0 ≤ J.val then
        RecTrialU (tabOf θ).publicSeed K ((tabOf θ).valuePos (msgPos K)) J.val else ∅))
          (MatrixMap.conj (recKraus (X := PairOut) (Z := Qrom.HashDomain) T mm) σ) ≤
        diagMass {q : Unit × RegQ |
          q.2 ∈ RecTrialU (tabOf θ).publicSeed K ((tabOf θ).valuePos (msgPos K)) J.val} σ
      rw [ite_eq_left (Nat.zero_le _)]
      exact (sum_pot_recTrial_recU _ _ _ _ T hσ).trans_eq (potential_setProj _ hσ)

/-- **The recorded unselected weights are at most the reveal charges.** -/
theorem recUPre_le_revQW {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversary) (θ : TVals) :
    recUPre pol A θ ≤
      (runtimeR m0Q).totalWeight .instruments (revQWU θ) (prefixQ pol A θ) initQ := by
  refine (totalWeight_le_modedP (runtimeR m0Q) .instruments (Zp := RegQ)
    (fun μ (J : Fin encodingAttemptLimit) ↦ setProj (trialSetU (tabOf θ).publicSeed μ J.val))
    (extWeight (hwCost (trialW (pkQ θ) recUWt) fun _ _ ↦ 0)) (revQWU θ)
    (fun μ i σ hσ hok ↦ revQW_stepU θ μ i σ hσ hok) (prefixQ pol A θ) (.rest ∅)
    (modedP_prefixQ hpol A θ) initQ_posSemidef).trans (le_of_eq ?_)
  rw [Finset.sum_eq_zero fun j _ ↦ potential_of_eq_zeroU
    (setProj_trialSet_restU (tabOf θ).publicSeed ∅ j.val) initQ, zero_add]

/-! ## First and repeated reveals -/

/-- **The first-reveal charges** at the hidden values `θ`: at a reveal of a key's coordinate not
yet revealed, the masses of the key's recorded trial cells on its value. -/
noncomputable def firstQWU (θ : TVals) :
    ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
      Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
        ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match keyOfTU T with
    | some K => ∑ J : Fin encodingAttemptLimit, diagMass {q : Unit × RegQ |
        vcoord (msgPos K) ∉ q.2.2.2.1 ∧ q.2.1.1 (trialCell (tabOf θ).publicSeed K
          ((tabOf θ).valuePos (msgPos K)) J) ≠ none} σ
    | none => 0
  | _, _ => 0

/-- **A repeated reveal of `K`'s coordinate with `K` unselected.** -/
def ReRevU (K : Key) (s : RegQ) : Prop :=
  vcoord (msgPos K) ∈ s.2.2.1 ∧ s.2.2.2 K = none

open scoped Classical in
/-- **The repeated-reveal charges**: at a reveal of a key's coordinate, `2^32` times the mass of
`ReRevU K`; nothing elsewhere. -/
noncomputable def reRevQWU : ∀ i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port,
    Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match keyOfTU T with
    | some K => (encodingAttemptLimit : ℝ≥0∞) * diagMass {q : Unit × RegQ | ReRevU K q.2} σ
    | none => 0
  | _, _ => 0

theorem diagMass_le_add_of_subsetU {α : Type} [Fintype α] {S B C : Set α}
    (h : S ⊆ B ∪ C) (σ : Matrix α α ℂ) : diagMass S σ ≤ diagMass B σ + diagMass C σ := by
  classical
  simp only [diagMass]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  by_cases ha : a ∈ S
  · rcases h ha with hb | hc
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb]
      exact le_self_add
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem hc]
      exact le_add_self
  · rw [Set.indicator_of_notMem ha]
    exact zero_le

theorem revQW_leU (θ : TVals) (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RD) ℂ) :
    revQWU θ i σ ≤ 1 * firstQWU θ i σ + 1 * reRevQWU i σ := by
  rw [one_mul, one_mul]
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · show (match keyOfTU T with
        | some K => ∑ J : Fin encodingAttemptLimit, diagMass {q : Unit × RegQ |
            q.2 ∈ RecTrialU (tabOf θ).publicSeed K ((tabOf θ).valuePos (msgPos K)) J} σ
        | none => 0) ≤ (match keyOfTU T with
        | some K => ∑ J : Fin encodingAttemptLimit, diagMass {q : Unit × RegQ |
            vcoord (msgPos K) ∉ q.2.2.2.1 ∧ q.2.1.1 (trialCell (tabOf θ).publicSeed K
              ((tabOf θ).valuePos (msgPos K)) J) ≠ none} σ
        | none => 0) + (match keyOfTU T with
        | some K => (encodingAttemptLimit : ℝ≥0∞) *
            diagMass {q : Unit × RegQ | ReRevU K q.2} σ
        | none => 0)
    rcases keyOfTU T with _ | K
    · exact zero_le
    · have hN : (encodingAttemptLimit : ℝ≥0∞) * diagMass {q : Unit × RegQ | ReRevU K q.2} σ =
          ∑ _J : Fin encodingAttemptLimit, diagMass {q : Unit × RegQ | ReRevU K q.2} σ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only
      rw [hN, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun J _ ↦ diagMass_le_add_of_subsetU (fun q hq ↦ ?_) σ
      by_cases hl : vcoord (msgPos K) ∈ q.2.2.2.1
      · exact .inr ⟨hl, hq.2⟩
      · exact .inl ⟨hl, hq.1⟩

/-- **The reveal charges split into the first and the repeated reveals.** -/
theorem recUPre_le_split {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversary) (θ : TVals) :
    recUPre pol A θ ≤
      (runtimeR m0Q).totalWeight .instruments (firstQWU θ) (prefixQ pol A θ) initQ +
        (runtimeR m0Q).totalWeight .instruments reRevQWU (prefixQ pol A θ) initQ := by
  refine (recUPre_le_revQW hpol A θ).trans ((totalWeight_le_add (runtimeR m0Q) .instruments _ _ _
    1 1 (fun i σ _ ↦ revQW_leU θ i σ) (prefixQ pol A θ) initQ_posSemidef).trans_eq ?_)
  rw [one_mul, one_mul]

end Quantum.Qrom.Sphincs

end
