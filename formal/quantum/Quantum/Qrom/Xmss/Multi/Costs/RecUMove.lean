module

public import Quantum.Qrom.Xmss.Multi.Costs.RecUModes

@[expose] public section

/-!
# The `n`-user recorded unselected weights, moved onto the reveals of the randomizer bases

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.RecUMove`. The recorded unselected weight
`recUWtN` at the read of trial `j` of user `i`'s search (the read cell recorded, the key unselected)
is moved to the reveal that starts the search: between that reveal and the read only the search's
earlier reads happen, at other cells, and they can only select the key. The moded potential
(CwRec's `totalWeight_le_modedP`) in the search of user `i`'s `rnd` from `b` before trial `j` is the
mass of the later trials' sets `RecTrialN`.

* `RecTrialN`, `trialSetN`: a trial recorded with the key unselected, the trials still to come in
  a mode.
* **`recUPreN_le_revQWN`** (from `totalWeight_recU_le_revQWN`, any moded program): `recUPreN A θ`
  is at most the reveal charges `revQWN (parQN θ) θ`.
* **`recUPreN_le_split`**: the reveal charges split into the first reveals (`firstQWN θ`:
  `(i, loC rnd)` unrevealed, the trial recorded) and the repeated reveals with the key unselected
  (`reRevQWN`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (diagMass setProj)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight ModedP cw_sum_pot_setProj_le
  cw_sum_pot_setProj_keep cw_clsKraus_ne_zero cw_readKrausH_ne_zero potential_setProj
  eq_of_recKraus_ne_zero totalWeight_le_add recKraus sum_recKraus)

attribute [local irreducible] xmssRom

/- Instance search for the register's memory exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-! ## The trials of a search -/

/-- **Trial `j` of user `i`'s search recorded with the key unselected.** -/
def RecTrialN (P : Fin n → PublicParameter) (i : Fin n) (rnd : Pos) (b : Randomizer) (j : ℕ) :
    Set (RRegN n (SelMemN n)) :=
  {s | s.1.1 (rndCell (P i) rnd b j) ≠ none ∧ RndU rnd (s.2.2.2 i)}

/-- **The trials still to come in a mode**: trial `J` at or after the current trial. -/
def trialSetN (P : Fin n → PublicParameter) : SrchModeN n → ℕ → Set (RRegN n (SelMemN n))
  | .grd i rnd b j, J => if j ≤ J then RecTrialN P i rnd b J else ∅
  | .free, _ => ∅

theorem setProj_trialSetN_free (P : Fin n → PublicParameter) (J : ℕ) :
    setProj (trialSetN P .free J) = (0 : Matrix (RRegN n (SelMemN n)) (RRegN n (SelMemN n)) ℂ) := by
  show setProj (∅ : Set (RRegN n (SelMemN n))) = 0
  ext a b
  simp [setProj]

theorem rndU_of_cwUpdN {rnd : Pos} {i i' : Fin n} {l : Layer} {e : KeyIndex} {z : HashDomain}
    {m : SelMemN n} {o : Option HashOutput} (h : RndU rnd (cwUpdN i' l e z m o i)) :
    RndU rnd (m i) := by
  by_cases hi : i = i'
  · subst hi
    rw [cwUpdN, Function.update_self] at h
    exact rndU_of_cwUpd h
  · rwa [cwUpdN, Function.update_of_ne hi] at h

/-! ## Potentials of trial sets along the ports -/

/-- A nonzero entry of a read of the `h`-cell `z`: the other `h`-cells kept. -/
theorem readKrausH_ne_zero_cellsN (z : HashDomain)
    (upd : QMemN n → Option HashOutput → QMemN n) (r : Option HashOutput × QMemN n)
    {s' s : RRegN n (SelMemN n)} (h : readKrausH z upd r s' s ≠ 0) (x : HashDomain)
    (hx : x ≠ z) : s'.1.1 x = s.1.1 x := by
  obtain ⟨-, -, hR⟩ := cw_clsKraus_ne_zero h
  rw [kroneckerMap_apply] at hR
  exact cellRead_apply_ne_zero (left_ne_zero_of_mul hR) x hx

theorem readKrausH_ne_zero_memN (z : HashDomain) (upd : QMemN n → Option HashOutput → QMemN n)
    (r : Option HashOutput × QMemN n) {s' s : RRegN n (SelMemN n)}
    (h : readKrausH z upd r s' s ≠ 0) : s.2.2 = r.2 ∧ s'.2.2 = upd r.2 r.1 :=
  ⟨(cw_readKrausH_ne_zero z upd r h).2.2.1, (cw_readKrausH_ne_zero z upd r h).2.2.2⟩

open scoped Classical in
/-- **A trial read keeps a later trial's set, up to selecting the key.** -/
theorem sum_pot_recTrialN_readH_le (P : Fin n → PublicParameter) (i : Fin n) (rnd : Pos)
    (b : Randomizer) (J : ℕ) {z : HashDomain} (hz : z ≠ rndCell (P i) rnd b J) (κ : UKey n)
    {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ r : Option HashOutput × QMemN n, potential (setProj (RecTrialN P i rnd b J))
        (MatrixMap.conj (hwReadKraus (trialReadN z κ) r) σ) ≤
      potential (setProj (RecTrialN P i rnd b J)) σ := by
  set u := trialUpdN z κ
  refine cw_sum_pot_setProj_le (fun r ↦ hwReadKraus (.readH z u) r) (sum_hwReadKraus _) _ _
    (fun r ↦ if RndU rnd ((u r.2 r.1).2 i) then 1 else 0) (fun r ↦ by split_ifs <;> norm_num)
    (fun r s' a h ↦ ?_) (fun r s' a a' ha ha' ↦ ?_) hσ
  · obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
    have hc := readKrausH_ne_zero_cellsN z u r hK _ hz.symm
    obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_memN z u r hK
    by_cases hU : RndU rnd ((u r.2 r.1).2 i)
    · have hU' : RndU rnd (a.2.2.2.2 i) := by
        rw [hm]
        exact rndU_of_cwUpdN (i' := κ.1) (l := κ.2.1) (e := κ.2.2) (z := z) (o := r.1) hU
      have hiff : s'.2 ∈ RecTrialN P i rnd b J ↔ a.2 ∈ RecTrialN P i rnd b J := by
        show (s'.2.1.1 _ ≠ none ∧ RndU rnd (s'.2.2.2.2 i)) ↔
          (a.2.1.1 _ ≠ none ∧ RndU rnd (a.2.2.2.2 i))
        rw [hc, hm']
        exact ⟨fun h ↦ ⟨h.1, hU'⟩, fun h ↦ ⟨h.1, hU⟩⟩
      rw [ite_eq_left hU, one_mul]
      by_cases ha : a.2 ∈ RecTrialN P i rnd b J
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hiff.2 ha), Pi.one_apply,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (mt hiff.1 ha)]
    · rw [ite_eq_right hU, zero_mul]
      refine Set.indicator_of_notMem (fun hs ↦ hU ?_) _
      have h2 := hs.2
      rwa [hm'] at h2
  · obtain ⟨-, hKa⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) ha
    obtain ⟨-, hKb⟩ := one_kronecker_ne_zero (a := a'.1) (a' := s'.1) (b := a'.2) (b' := s'.2) ha'
    have hca := readKrausH_ne_zero_cellsN z u r hKa _ hz.symm
    have hcb := readKrausH_ne_zero_cellsN z u r hKb _ hz.symm
    have hma := (readKrausH_ne_zero_memN z u r hKa).1
    have hmb := (readKrausH_ne_zero_memN z u r hKb).1
    have hiff : a.2 ∈ RecTrialN P i rnd b J ↔ a'.2 ∈ RecTrialN P i rnd b J := by
      show (a.2.1.1 _ ≠ none ∧ RndU rnd (a.2.2.2.2 i)) ↔
        (a'.2.1.1 _ ≠ none ∧ RndU rnd (a'.2.2.2.2 i))
      rw [← hca, ← hcb, hma, hmb]
    by_cases h' : a.2 ∈ RecTrialN P i rnd b J
    · rw [Set.indicator_of_mem h', Set.indicator_of_mem (hiff.1 h'), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (mt hiff.2 h')]

/-- A record keeps every trial set. -/
theorem sum_pot_recTrialN_rec_le (P : Fin n → PublicParameter) (i : Fin n) (rnd : Pos)
    (b : Randomizer) (J : ℕ) (T : Finset (HPosN n))
    {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ m : QMemN n, potential (setProj (RecTrialN P i rnd b J))
        (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T m) σ) ≤
      potential (setProj (RecTrialN P i rnd b J)) σ :=
  cw_sum_pot_setProj_keep _ (sum_recKraus T) _ (fun m s' a h ↦ by
    rw [eq_of_recKraus_ne_zero (u := a.1) (u' := s'.1) (s := a.2) (s' := s'.2) h]
    rfl) hσ

/-! ## The reveal charges and the moded potential -/

/-- **The reveal charges** under the parameters `P`: at a reveal of one randomizer base
`atU i {loC rnd}`, the masses of the trials of user `i`'s search of `rnd` from `θ (i, loC rnd)`
recorded with the key unselected. -/
noncomputable def revQWN (P : Fin n → PublicParameter) (θ : HPosN n → Digest) :
    ∀ x : (RSpecN n (SelMemN n)).Port,
      Matrix ((RSpecN n (SelMemN n)).In x × RRegN n (SelMemN n))
        ((RSpecN n (SelMemN n)).In x × RRegN n (SelMemN n)) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match rndOfTN T with
    | some (i, rnd) => ∑ J : Fin randomizerAttemptLimit,
        diagMass {q : Unit × RRegN n (SelMemN n) | q.2 ∈ RecTrialN P i rnd (θ (i, loC rnd)) J} σ
    | none => 0
  | _, _ => 0

theorem trialWN_recUWtN_eq {P : Fin n → PublicParameter} {i : Fin n} {rnd : Pos} {l : Layer}
    {e : KeyIndex} {msg : MsgBytes} (hr : rndLab rnd = some (l, e, msg)) (b : Randomizer)
    (j : ℕ) {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    trialWN recUWtN (trialReadN (trialCell (P i) l e msg b j) (i, l, e)) σ =
      potential (setProj (RecTrialN P i rnd b j)) σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [trialWN_trialReadN, potential_setProj _ hσ, diagMass,
    ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by unfold recUWtN; split_ifs <;> norm_num)
      (hre q)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hiff : (q.2.1.1 (trialCell (P i) l e msg b j) ≠ none ∧ memAt q.2 (i, l, e) = none) ↔
      q ∈ {q : Unit × RRegN n (SelMemN n) | q.2 ∈ RecTrialN P i rnd b j} := by
    show _ ↔ q.2.1.1 (rndCell (P i) rnd b j) ≠ none ∧ RndU rnd (q.2.2.2.2 i)
    rw [rndCell_eq hr, rndU_iff hr]
    rfl
  by_cases h : q.2.1.1 (trialCell (P i) l e msg b j) ≠ none ∧ memAt q.2 (i, l, e) = none
  · rw [show recUWtN (trialCell (P i) l e msg b j) (i, l, e) q.2 = 1 from ite_eq_left h, one_mul,
      Set.indicator_of_mem (hiff.1 h)]
  · rw [show recUWtN (trialCell (P i) l e msg b j) (i, l, e) q.2 = 0 from ite_eq_right h,
      zero_mul, ENNReal.ofReal_zero, Set.indicator_of_notMem (mt hiff.2 h)]

theorem sum_pot_trialSetN_split (P : Fin n → PublicParameter) (i : Fin n) (rnd : Pos)
    (b : Randomizer) {j : ℕ} (hj : j < randomizerAttemptLimit)
    (τ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ) :
    ∑ J : Fin randomizerAttemptLimit,
        potential (setProj (trialSetN P (.grd i rnd b j) J.val)) τ =
      potential (setProj (RecTrialN P i rnd b j)) τ +
        ∑ J : Fin randomizerAttemptLimit,
          potential (setProj (trialSetN P (.grd i rnd b (j + 1)) J.val)) τ := by
  have h : ∀ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSetN P (.grd i rnd b j) J.val)) τ =
        (if J = ⟨j, hj⟩ then potential (setProj (RecTrialN P i rnd b j)) τ else 0) +
          potential (setProj (trialSetN P (.grd i rnd b (j + 1)) J.val)) τ := fun J ↦ by
    by_cases hJ : J = ⟨j, hj⟩
    · subst hJ
      show potential (setProj (if j ≤ j then RecTrialN P i rnd b j else ∅)) τ =
        (if (⟨j, hj⟩ : Fin randomizerAttemptLimit) = ⟨j, hj⟩ then _ else 0) +
          potential (setProj (if j + 1 ≤ j then RecTrialN P i rnd b j else ∅)) τ
      rw [ite_eq_left le_rfl, ite_eq_left rfl, ite_eq_right (by omega), potential_setProj_empty,
        add_zero]
    · have hne : J.val ≠ j := fun h' ↦ hJ (Fin.ext h')
      show potential (setProj (if j ≤ J.val then RecTrialN P i rnd b J.val else ∅)) τ =
        (if J = ⟨j, hj⟩ then _ else 0) +
          potential (setProj (if j + 1 ≤ J.val then RecTrialN P i rnd b J.val else ∅)) τ
      rw [ite_eq_right hJ, zero_add]
      by_cases h1 : j + 1 ≤ J.val
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  rw [Finset.sum_congr rfl fun J _ ↦ h J, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- **A trial read on the trial sets**: its recorded unselected weight plus the later trials'
masses after it are at most the trials' masses before it. -/
theorem readH_stepN (P : Fin n → PublicParameter) {i : Fin n} {rnd : Pos} {l : Layer}
    {e : KeyIndex} {msg : MsgBytes} (hr : rndLab rnd = some (l, e, msg)) (b : Randomizer)
    {j : ℕ} (hj : j < randomizerAttemptLimit)
    {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) :
    trialWN recUWtN (trialReadN (trialCell (P i) l e msg b j) (i, l, e)) σ +
        ∑' r : Option HashOutput × QMemN n, ∑ J : Fin randomizerAttemptLimit,
          potential (setProj (trialSetN P (srchRdNxN (.grd i rnd b j)
            (trialReadN (trialCell (P i) l e msg b j) (i, l, e)) r) J.val))
            (MatrixMap.conj (hwReadKraus (trialReadN (trialCell (P i) l e msg b j) (i, l, e)) r)
              σ) ≤
      ∑ J : Fin randomizerAttemptLimit,
        potential (setProj (trialSetN P (.grd i rnd b j) J.val)) σ := by
  rw [sum_pot_trialSetN_split P i rnd b hj, trialWN_recUWtN_eq hr b j hσ, tsum_fintype]
  refine add_le_add le_rfl ?_
  have hmono : ∀ (r : Option HashOutput × QMemN n) (J : Fin randomizerAttemptLimit),
      potential (setProj (trialSetN P (srchRdNxN (.grd i rnd b j)
          (trialReadN (trialCell (P i) l e msg b j) (i, l, e)) r) J.val))
        (MatrixMap.conj (hwReadKraus (trialReadN (trialCell (P i) l e msg b j) (i, l, e)) r)
          σ) ≤
      potential (setProj (trialSetN P (.grd i rnd b (j + 1)) J.val))
        (MatrixMap.conj (hwReadKraus (trialReadN (trialCell (P i) l e msg b j) (i, l, e)) r)
          σ) := fun r J ↦ by
    show potential (setProj (trialSetN P
      (match Codeword.decode (truncateHash (r.1.getD 0)) with
        | some _ => SrchModeN.free
        | none => SrchModeN.grd i rnd b (j + 1)) J.val)) _ ≤ _
    split
    · rw [show trialSetN P SrchModeN.free J.val = ∅ from rfl, potential_setProj_empty]
      exact zero_le
    · exact le_rfl
  refine (Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun J _ ↦ hmono r J).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun J _ ↦ ?_
  show ∑ r : Option HashOutput × QMemN n, potential (setProj
      (if j + 1 ≤ J.val then RecTrialN P i rnd b J.val else ∅)) _ ≤
    potential (setProj (if j + 1 ≤ J.val then RecTrialN P i rnd b J.val else ∅)) σ
  split_ifs with hJ
  · refine sum_pot_recTrialN_readH_le P i rnd b J.val (fun h ↦ ?_) (i, l, e) hσ
    rw [rndCell_eq hr] at h
    have := trialCell_injective_trial hj J.isLt h
    omega
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun r _ ↦ potential_setProj_empty _) zero_le

/-- **The step of the moded potential**: the recorded unselected weight of a trial read plus the
later trials' masses after it are at most the trials' masses before it; a reveal of a randomizer
base charges its trials' masses. -/
theorem revQWN_step (P : Fin n → PublicParameter) (θ : HPosN n → Digest) (μ : SrchModeN n)
    (x : (RSpecN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecN n (SelMemN n)).In x × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In x × RRegN n (SelMemN n)) ℂ) (hσ : σ.PosSemidef)
    (hok : srchOkZN P μ x) :
    extWeight (D := QReg.of (RRegN n (SelMemN n))) (hwCost (trialWN recUWtN) fun _ _ ↦ 0) x σ +
        ∑' r, ∑ J : Fin randomizerAttemptLimit,
          potential (setProj (trialSetN P (srchNxZN θ μ x r) J.val))
            (((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step x).branch r σ) ≤
      ∑ J : Fin randomizerAttemptLimit, potential (setProj (trialSetN P μ J.val)) σ +
        revQWN P θ x σ := by
  rcases x with ((p | c) | c) | T
  · show (0 : ℝ≥0∞) + ∑' r, ∑ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSetN P .free J.val)) _ ≤ _
    refine le_of_eq_of_le ?_ zero_le
    rw [zero_add]
    exact ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦
      potential_setProj_empty _
  · rcases μ with _ | ⟨i, rnd, b, j⟩
    · exact hok.elim
    have hb : ∀ r, ((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step
        (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦ LinearMap.congr_fun
          (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain) m0N c r) σ
    rw [show revQWN P θ (.inl (.inl (.inr c))) σ = 0 from rfl, add_zero]
    refine (add_le_add le_rfl (le_of_eq (tsum_congr fun r ↦ congrArg (fun τ ↦
      ∑ J : Fin randomizerAttemptLimit, potential (setProj (trialSetN P
        (srchRdNxN (.grd i rnd b j) c r) J.val)) τ) (hb r)))).trans ?_
    show trialWN recUWtN c σ + ∑' r : c.Result, ∑ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSetN P (srchRdNxN (.grd i rnd b j) c r) J.val))
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      ∑ J : Fin randomizerAttemptLimit,
        potential (setProj (trialSetN P (.grd i rnd b j) J.val)) σ
    obtain ⟨hj, l, e, msg, hr, rfl⟩ := hok
    exact readH_stepN P hr b hj hσ
  · show (0 : ℝ≥0∞) + ∑' r, ∑ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSetN P .free J.val)) _ ≤ _
    refine le_of_eq_of_le ?_ zero_le
    rw [zero_add]
    exact ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦
      potential_setProj_empty _
  · show (0 : ℝ≥0∞) + ∑' m, ∑ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSetN P (revNxQN T fun i rnd ↦ θ (i, loC rnd)) J.val))
        (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T m) σ) ≤ _
    rw [zero_add]
    rcases hT : rndOfTN T with _ | ⟨i, rnd⟩
    · have hn : revNxQN T (fun i rnd ↦ θ (i, loC rnd)) = .free := by
        unfold revNxQN
        rw [hT]
      rw [hn]
      exact le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun m ↦ Finset.sum_eq_zero fun J _ ↦
        potential_setProj_empty _) zero_le
    · have hn : revNxQN T (fun i rnd ↦ θ (i, loC rnd)) = .grd i rnd (θ (i, loC rnd)) 0 := by
        unfold revNxQN
        rw [hT]
      rw [hn]
      refine le_add_left ?_
      show _ ≤ (match rndOfTN T with
        | some (i, rnd) => ∑ J : Fin randomizerAttemptLimit,
            diagMass {q : Unit × RRegN n (SelMemN n) |
              q.2 ∈ RecTrialN P i rnd (θ (i, loC rnd)) J} σ
        | none => 0)
      rw [hT, tsum_fintype, Finset.sum_comm]
      refine Finset.sum_le_sum fun J _ ↦ ?_
      show ∑ m : QMemN n, potential (setProj (if 0 ≤ J.val then
        RecTrialN P i rnd (θ (i, loC rnd)) J.val else ∅))
          (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T m) σ) ≤
        diagMass {q : Unit × RRegN n (SelMemN n) |
          q.2 ∈ RecTrialN P i rnd (θ (i, loC rnd)) J.val} σ
      rw [ite_eq_left (Nat.zero_le _)]
      exact (sum_pot_recTrialN_rec_le _ _ _ _ _ T hσ).trans_eq (potential_setProj _ hσ)

/-- The move for a moded program at the parameters `P`. -/
theorem totalWeight_recU_le_revQWN {Ω : QReg → Type} (P : Fin n → PublicParameter)
    (θ : HPosN n → Digest) {fin : (Σ u, Ω u) → SrchModeN n → Prop}
    (x : QuantumComp LocalSig.instruments.{0} (RSpecN n (SelMemN n)) Ω (QReg.of Unit))
    (hx : ModedP (srchOkZN P) (srchNxZN θ) fin .free x) :
    (runtimeR (m0N (n := n))).totalWeight .instruments
        (extWeight (hwCost (trialWN recUWtN) fun _ _ ↦ 0)) x initQN ≤
      (runtimeR (m0N (n := n))).totalWeight .instruments (revQWN P θ) x initQN :=
  totalWeight_le_modedP_zero (runtimeR (m0N (n := n))) .instruments
    (Zp := RRegN n (SelMemN n))
    (fun μ (J : Fin randomizerAttemptLimit) ↦ setProj (trialSetN P μ J.val))
    (extWeight (hwCost (trialWN recUWtN) fun _ _ ↦ 0)) (revQWN P θ)
    (fun μ x σ hσ hok ↦ revQWN_step P θ μ x σ hσ hok) x .free hx initQN_posSemidef
    fun j ↦ setProj_trialSetN_free P j.val

/-- **The recorded unselected weights are at most the reveal charges.** -/
theorem recUPreN_le_revQWN (A : MuAdversary n) (θ : HPosN n → Digest) :
    recUPreN A θ ≤ (runtimeR (m0N (n := n))).totalWeight .instruments (revQWN (parQN θ) θ)
      (prefixQN A θ) initQN :=
  totalWeight_recU_le_revQWN (parQN θ) θ (prefixQN A θ) (modedP_prefixQN A θ)

/-! ## First and repeated reveals -/

/-- **The first-reveal charges**: at a reveal of `atU i {loC rnd}` with `(i, loC rnd)`
unrevealed, the masses of the recorded trial cells of user `i`'s search of `rnd` under
`parQN θ i`. -/
noncomputable def firstQWN (θ : HPosN n → Digest) : ∀ x : (RSpecN n (SelMemN n)).Port,
    Matrix ((RSpecN n (SelMemN n)).In x × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In x × RRegN n (SelMemN n)) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match rndOfTN T with
    | some (i, rnd) => ∑ J : Fin randomizerAttemptLimit,
        diagMass {q : Unit × RRegN n (SelMemN n) | (i, loC rnd) ∉ q.2.2.2.1 ∧
          q.2.1.1 (rndCell (parQN θ i) rnd (θ (i, loC rnd)) J) ≠ none} σ
    | none => 0
  | _, _ => 0

theorem revQWN_le (θ : HPosN n → Digest) (x : (RSpecN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecN n (SelMemN n)).In x × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In x × RRegN n (SelMemN n)) ℂ) :
    revQWN (parQN θ) θ x σ ≤ 1 * firstQWN θ x σ + 1 * reRevQWN x σ := by
  rw [one_mul, one_mul]
  rcases x with ((p | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · show (match rndOfTN T with
        | some (i, rnd) => ∑ J : Fin randomizerAttemptLimit,
            diagMass {q : Unit × RRegN n (SelMemN n) |
              q.2 ∈ RecTrialN (parQN θ) i rnd (θ (i, loC rnd)) J} σ
        | none => 0) ≤ (match rndOfTN T with
        | some (i, rnd) => ∑ J : Fin randomizerAttemptLimit,
            diagMass {q : Unit × RRegN n (SelMemN n) | (i, loC rnd) ∉ q.2.2.2.1 ∧
              q.2.1.1 (rndCell (parQN θ i) rnd (θ (i, loC rnd)) J) ≠ none} σ
        | none => 0) + (match rndOfTN T with
        | some (i, rnd) => (randomizerAttemptLimit : ℝ≥0∞) *
            diagMass {q : Unit × RRegN n (SelMemN n) | ReRevQN rnd i q.2} σ
        | none => 0)
    rcases hT : rndOfTN T with _ | ⟨i, rnd⟩
    · exact zero_le
    · obtain ⟨⟨l, e, msg⟩, hr⟩ := Option.isSome_iff_exists.mp (rndOfTN_spec hT).1
      have hN : (randomizerAttemptLimit : ℝ≥0∞) *
          diagMass {q : Unit × RRegN n (SelMemN n) | ReRevQN rnd i q.2} σ =
          ∑ _J : Fin randomizerAttemptLimit,
            diagMass {q : Unit × RRegN n (SelMemN n) | ReRevQN rnd i q.2} σ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only
      rw [hN, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun J _ ↦ diagMass_le_add_of_subset (fun q hq ↦ ?_) σ
      by_cases hl : (i, loC rnd) ∈ q.2.2.2.1
      · exact .inr ⟨hl, l, e, msg, hr, (rndU_iff hr _).mp hq.2⟩
      · exact .inl ⟨hl, hq.1⟩

/-- **The reveal charges split into the first and the repeated reveals.** -/
theorem recUPreN_le_split (A : MuAdversary n) (θ : HPosN n → Digest) :
    recUPreN A θ ≤
      (runtimeR (m0N (n := n))).totalWeight .instruments (firstQWN θ) (prefixQN A θ) initQN +
        (runtimeR (m0N (n := n))).totalWeight .instruments reRevQWN (prefixQN A θ) initQN := by
  refine (recUPreN_le_revQWN A θ).trans ((totalWeight_le_add (runtimeR (m0N (n := n)))
    .instruments _ _ _ 1 1 (fun x σ _ ↦ revQWN_le θ x σ) (prefixQN A θ)
    initQN_posSemidef).trans_eq ?_)
  rw [one_mul, one_mul]

end Quantum.Qrom.Xmss.Multi

end
