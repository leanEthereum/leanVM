module

public import Quantum.Qrom.Xmss.Costs.RecUModes

@[expose] public section

/-!
# The recorded unselected weights, moved onto the reveals of the randomizer bases

The recorded unselected weight `recUWt` at the read of trial `j` of a search (the read cell
recorded, the key unselected) is moved to the reveal that starts the search: between that reveal
and the read only the search's earlier reads happen, at other cells, and they can only select the
key. The moded potential (CwRec's `totalWeight_le_modedP`) in the search of `rnd` from `b` before
trial `j` is the mass of the later trials' sets `RecTrial`.

* `rndCell`, `RndU`, `RecTrial`, `trialSet`: the trial cells of a search, its key unselected, a
  trial recorded with the key unselected, the trials still to come in a mode.
* **`recUPre_le_revQW`** (from `totalWeight_recU_le_revQW`, any moded program): `recUPre A θ` is
  at most the reveal charges `revQW (θ paramC) θ` (at a reveal of `{loC rnd}`, the masses of the
  recorded trials of `rnd` with the key unselected).
* **`recUPre_le_split`**: the reveal charges split into the first reveals
  (`firstQW (θ paramC) θ`: `loC rnd` unrevealed, the trial recorded) and the repeated reveals with
  the key unselected (`reRevQW`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (diagMass setProj conjTranspose_setProj totalWeight_le_totalWeight)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR liftRead extWeight sumWeight
  totalWeight_le_modedP cw_sum_pot_setProj_le cw_sum_pot_setProj_keep cw_clsKraus_ne_zero
  potential_setProj eq_of_recKraus_ne_zero totalWeight_le_add recKraus sum_recKraus)

attribute [local irreducible] xmssRom

/-! ## The trials of a search -/

/-- **The cell of trial `j`** of the search of the randomizer position `rnd` from `b`. -/
def rndCell (P : PublicParameter) (rnd : Pos) (b : Randomizer) (j : ℕ) : HashDomain :=
  match rndLab rnd with
  | some k => trialCell P k.1 k.2.1 k.2.2 b j
  | none => 0

/-- The key of the search of `rnd` is unselected. -/
def RndU (rnd : Pos) (m : SelMem) : Prop :=
  match rndLab rnd with
  | some k => m k.1 k.2.1 = none
  | none => False

/-- **Trial `j` recorded with the key unselected.** -/
def RecTrial (P : PublicParameter) (rnd : Pos) (b : Randomizer) (j : ℕ) : Set (RReg SelMem) :=
  {s | s.1.1 (rndCell P rnd b j) ≠ none ∧ RndU rnd s.2.2.2}

/-- **The trials still to come in a mode**: trial `J` at or after the current trial. -/
def trialSet (P : PublicParameter) : SrchMode → ℕ → Set (RReg SelMem)
  | .grd rnd b j, J => if j ≤ J then RecTrial P rnd b J else ∅
  | .free, _ => ∅

theorem rndCell_eq {P : PublicParameter} {rnd : Pos} {l : Layer} {e : KeyIndex} {msg : MsgBytes}
    (hr : rndLab rnd = some (l, e, msg)) (b : Randomizer) (j : ℕ) :
    rndCell P rnd b j = trialCell P l e msg b j := by
  unfold rndCell
  rw [hr]

theorem rndU_iff {rnd : Pos} {l : Layer} {e : KeyIndex} {msg : MsgBytes}
    (hr : rndLab rnd = some (l, e, msg)) (m : SelMem) : RndU rnd m ↔ m l e = none := by
  unfold RndU
  rw [hr]

theorem cwUpd_eq_none_q {l l' : Layer} {e e' : KeyIndex} {z : HashDomain} {m : SelMem}
    {o : Option HashOutput} (h : cwUpd l e z m o l' e' = none) : m l' e' = none := by
  rcases o with _ | v
  · exact h
  · by_cases hm : m l e = none
    · rw [cwUpd_some_of_none l e z hm v] at h
      unfold cwSel at h
      split_ifs at h
      · unfold SelMem.select at h
        by_cases hl : l' = l
        · subst hl
          rw [Function.update_self] at h
          by_cases he : e' = e
          · subst he
            rw [Function.update_self] at h
            exact absurd h (Option.some_ne_none _)
          · rwa [Function.update_of_ne he] at h
        · rwa [Function.update_of_ne hl] at h
      · exact h
    · rw [cwUpd_of_ne_none hm] at h
      exact h

theorem rndU_of_cwUpd {rnd : Pos} {l : Layer} {e : KeyIndex} {z : HashDomain} {m : SelMem}
    {o : Option HashOutput} (h : RndU rnd (cwUpd l e z m o)) : RndU rnd m := by
  unfold RndU at h ⊢
  generalize rndLab rnd = o at h ⊢
  rcases o with _ | k
  · exact h
  · exact cwUpd_eq_none_q h

theorem trialCell_injective_trial {P : PublicParameter} {l : Layer} {e : KeyIndex}
    {msg : MsgBytes} {b : Randomizer} {i j : ℕ} (hi : i < randomizerAttemptLimit)
    (hj : j < randomizerAttemptLimit) (h : trialCell P l e msg b i = trialCell P l e msg b j) :
    i = j := by
  have h1 := cell_injective P (s := .msg l e) (s' := .msg l e) trivial trivial h
  have h2 : (b + BitVec.ofNat digestBits i) = b + BitVec.ofNat digestBits j :=
    congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h1).2)
  have h3 : BitVec.ofNat digestBits i = BitVec.ofNat digestBits j := add_left_cancel h2
  have h4 := congrArg BitVec.toNat h3
  have hN : randomizerAttemptLimit ≤ 2 ^ digestBits := by
    unfold randomizerAttemptLimit digestBits
    norm_num
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hi.trans_le hN),
    Nat.mod_eq_of_lt (hj.trans_le hN)] at h4
  exact h4

/-! ## Potentials of trial sets along the ports -/

theorem potential_setProj_empty {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (τ : Matrix (A × D) (A × D) ℂ) : potential (setProj (∅ : Set D)) τ = 0 := by
  rw [potential_eq]
  simp [setProj]

theorem potential_of_eq_zero {A Z D : Type} [Fintype A] [DecidableEq A] [Fintype Z] [Fintype D]
    {K : Matrix Z D ℂ} (hK : K = 0) (τ : Matrix (A × D) (A × D) ℂ) : potential K τ = 0 := by
  subst hK
  rw [potential_eq]
  simp

theorem setProj_trialSet_free (P : PublicParameter) (J : ℕ) :
    setProj (trialSet P .free J) = (0 : Matrix (RReg SelMem) (RReg SelMem) ℂ) := by
  show setProj (∅ : Set (RReg SelMem)) = 0
  ext a b
  simp [setProj]

/-- A nonzero entry of a read of the `h`-cell `z`: the other `h`-cells kept. -/
theorem readKrausH_ne_zero_cells (z : HashDomain) (upd : QMem → Option HashOutput → QMem)
    (r : Option HashOutput × QMem) {s' s : RReg SelMem} (h : readKrausH z upd r s' s ≠ 0)
    (x : HashDomain) (hx : x ≠ z) : s'.1.1 x = s.1.1 x := by
  obtain ⟨-, -, hR⟩ := cw_clsKraus_ne_zero h
  rw [kroneckerMap_apply] at hR
  exact cellRead_apply_ne_zero (left_ne_zero_of_mul hR) x hx

theorem readKrausH_ne_zero_mem (z : HashDomain) (upd : QMem → Option HashOutput → QMem)
    (r : Option HashOutput × QMem) {s' s : RReg SelMem} (h : readKrausH z upd r s' s ≠ 0) :
    s.2.2 = r.2 ∧ s'.2.2 = upd r.2 r.1 :=
  ⟨(Quantum.Xmss.Assembly.cw_readKrausH_ne_zero z upd r h).2.2.1,
    (Quantum.Xmss.Assembly.cw_readKrausH_ne_zero z upd r h).2.2.2⟩

open scoped Classical in
/-- **A trial read keeps a later trial's set, up to selecting the key.** -/
theorem sum_pot_recTrial_readH_le (P : PublicParameter) (rnd : Pos) (b : Randomizer) (J : ℕ)
    {z : HashDomain} (hz : z ≠ rndCell P rnd b J) (l : Layer) (e : KeyIndex)
    {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ} (hσ : σ.PosSemidef) :
    ∑ r : Option HashOutput × QMem, potential (setProj (RecTrial P rnd b J))
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ) ≤
      potential (setProj (RecTrial P rnd b J)) σ := by
  set u := trialUpdQ l e z
  refine cw_sum_pot_setProj_le (fun r ↦ hwReadKraus (.readH z u) r) (sum_hwReadKraus _) _ _
    (fun r ↦ if RndU rnd (u r.2 r.1).2 then 1 else 0) (fun r ↦ by split_ifs <;> norm_num)
    (fun r s' a h ↦ ?_) (fun r s' a a' ha ha' ↦ ?_) hσ
  · obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
    have hc := readKrausH_ne_zero_cells z u r hK _ hz.symm
    obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_mem z u r hK
    by_cases hU : RndU rnd (u r.2 r.1).2
    · have hU' : RndU rnd a.2.2.2.2 := by
        rw [hm]
        exact rndU_of_cwUpd hU
      have hiff : s'.2 ∈ RecTrial P rnd b J ↔ a.2 ∈ RecTrial P rnd b J := by
        show (s'.2.1.1 _ ≠ none ∧ RndU rnd s'.2.2.2.2) ↔ (a.2.1.1 _ ≠ none ∧ RndU rnd a.2.2.2.2)
        rw [hc, hm']
        exact ⟨fun h ↦ ⟨h.1, hU'⟩, fun h ↦ ⟨h.1, hU⟩⟩
      rw [ite_eq_left hU, one_mul]
      by_cases ha : a.2 ∈ RecTrial P rnd b J
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hiff.2 ha), Pi.one_apply,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (mt hiff.1 ha)]
    · rw [ite_eq_right hU, zero_mul]
      refine Set.indicator_of_notMem (fun hs ↦ hU ?_) _
      have h2 := hs.2
      rwa [hm'] at h2
  · obtain ⟨-, hKa⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) ha
    obtain ⟨-, hKb⟩ := one_kronecker_ne_zero (a := a'.1) (a' := s'.1) (b := a'.2) (b' := s'.2) ha'
    have hca := readKrausH_ne_zero_cells z u r hKa _ hz.symm
    have hcb := readKrausH_ne_zero_cells z u r hKb _ hz.symm
    have hma := (readKrausH_ne_zero_mem z u r hKa).1
    have hmb := (readKrausH_ne_zero_mem z u r hKb).1
    have hiff : a.2 ∈ RecTrial P rnd b J ↔ a'.2 ∈ RecTrial P rnd b J := by
      show (a.2.1.1 _ ≠ none ∧ RndU rnd a.2.2.2.2) ↔ (a'.2.1.1 _ ≠ none ∧ RndU rnd a'.2.2.2.2)
      rw [← hca, ← hcb, hma, hmb]
    by_cases h' : a.2 ∈ RecTrial P rnd b J
    · rw [Set.indicator_of_mem h', Set.indicator_of_mem (hiff.1 h'), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (mt hiff.2 h')]

/-- A record keeps every trial set. -/
theorem sum_pot_recTrial_rec_le (P : PublicParameter) (rnd : Pos) (b : Randomizer) (J : ℕ)
    (T : Finset HPos) {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ m : QMem, potential (setProj (RecTrial P rnd b J))
        (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T m) σ) ≤
      potential (setProj (RecTrial P rnd b J)) σ :=
  cw_sum_pot_setProj_keep _ (sum_recKraus T) _ (fun m s' a h ↦ by
    rw [eq_of_recKraus_ne_zero (u := a.1) (u' := s'.1) (s := a.2) (s' := s'.2) h]
    rfl) hσ

/-! ## The reveal charges and the moded potential -/

/-- **The reveal charges** under the parameter `P`: at a reveal of one randomizer base
`{loC rnd}`, the masses of the trials of `rnd`'s search from `θ (loC rnd)` recorded with the key
unselected. -/
noncomputable def revQW (P : PublicParameter) (θ : HPos → Digest) : ∀ i : (RSpec SelMem).Port,
    Matrix ((RSpec SelMem).In i × RD) ((RSpec SelMem).In i × RD) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match rndOfT T with
    | some rnd => ∑ J : Fin randomizerAttemptLimit,
        diagMass {q : Unit × RReg SelMem | q.2 ∈ RecTrial P rnd (θ (loC rnd)) J} σ
    | none => 0
  | _, _ => 0

theorem trialW_recUWt_eq {P : PublicParameter} {rnd : Pos} {l : Layer} {e : KeyIndex}
    {msg : MsgBytes} (hr : rndLab rnd = some (l, e, msg)) (b : Randomizer) (j : ℕ)
    {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ} (hσ : σ.PosSemidef) :
    trialW recUWt (.readH (trialCell P l e msg b j) (trialUpdQ l e (trialCell P l e msg b j)))
      σ = potential (setProj (RecTrial P rnd b j)) σ := by
  classical
  have hz : slotOf (trialCell P l e msg b j) = some (.msg l e) :=
    slotOf_cell P (s := .msg l e) trivial _
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [← trialRead_eq, trialW_trialRead _ hz, potential_setProj _ hσ, diagMass,
    ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by unfold recUWt; split_ifs <;> norm_num)
      (hre q)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hiff : (q.2.1.1 (trialCell P l e msg b j) ≠ none ∧ q.2.2.2.2 l e = none) ↔
      q ∈ {q : Unit × RReg SelMem | q.2 ∈ RecTrial P rnd b j} := by
    show _ ↔ q.2.1.1 (rndCell P rnd b j) ≠ none ∧ RndU rnd q.2.2.2.2
    rw [rndCell_eq hr, rndU_iff hr]
  by_cases h : q.2.1.1 (trialCell P l e msg b j) ≠ none ∧ q.2.2.2.2 l e = none
  · rw [show recUWt (trialCell P l e msg b j) l e q.2 = 1 from ite_eq_left h, one_mul,
      Set.indicator_of_mem (hiff.1 h)]
  · rw [show recUWt (trialCell P l e msg b j) l e q.2 = 0 from ite_eq_right h, zero_mul,
      ENNReal.ofReal_zero, Set.indicator_of_notMem (mt hiff.2 h)]

theorem sum_pot_trialSet_split (P : PublicParameter) (rnd : Pos) (b : Randomizer) {j : ℕ}
    (hj : j < randomizerAttemptLimit)
    (τ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ) :
    ∑ J : Fin randomizerAttemptLimit, potential (setProj (trialSet P (.grd rnd b j) J.val)) τ =
      potential (setProj (RecTrial P rnd b j)) τ +
        ∑ J : Fin randomizerAttemptLimit,
          potential (setProj (trialSet P (.grd rnd b (j + 1)) J.val)) τ := by
  have h : ∀ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSet P (.grd rnd b j) J.val)) τ =
        (if J = ⟨j, hj⟩ then potential (setProj (RecTrial P rnd b j)) τ else 0) +
          potential (setProj (trialSet P (.grd rnd b (j + 1)) J.val)) τ := fun J ↦ by
    by_cases hJ : J = ⟨j, hj⟩
    · subst hJ
      show potential (setProj (if j ≤ j then RecTrial P rnd b j else ∅)) τ =
        (if (⟨j, hj⟩ : Fin randomizerAttemptLimit) = ⟨j, hj⟩ then _ else 0) +
          potential (setProj (if j + 1 ≤ j then RecTrial P rnd b j else ∅)) τ
      rw [ite_eq_left le_rfl, ite_eq_left rfl, ite_eq_right (by omega), potential_setProj_empty,
        add_zero]
    · have hne : J.val ≠ j := fun h' ↦ hJ (Fin.ext h')
      show potential (setProj (if j ≤ J.val then RecTrial P rnd b J.val else ∅)) τ =
        (if J = ⟨j, hj⟩ then _ else 0) +
          potential (setProj (if j + 1 ≤ J.val then RecTrial P rnd b J.val else ∅)) τ
      rw [ite_eq_right hJ, zero_add]
      by_cases h1 : j + 1 ≤ J.val
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  rw [Finset.sum_congr rfl fun J _ ↦ h J, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- **A trial read on the trial sets**: its recorded unselected weight plus the later trials'
masses after it are at most the trials' masses before it. -/
theorem readH_step (P : PublicParameter) {rnd : Pos} {l : Layer} {e : KeyIndex}
    {msg : MsgBytes} (hr : rndLab rnd = some (l, e, msg)) (b : Randomizer) {j : ℕ}
    (hj : j < randomizerAttemptLimit)
    {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ} (hσ : σ.PosSemidef) :
    trialW recUWt (.readH (trialCell P l e msg b j) (trialUpdQ l e (trialCell P l e msg b j)))
        σ + ∑' r : Option HashOutput × QMem, ∑ J : Fin randomizerAttemptLimit,
          potential (setProj (trialSet P (srchRdNx (.grd rnd b j)
            (.readH (trialCell P l e msg b j) (trialUpdQ l e (trialCell P l e msg b j))) r)
              J.val))
            (MatrixMap.conj (hwReadKraus (.readH (trialCell P l e msg b j)
              (trialUpdQ l e (trialCell P l e msg b j))) r) σ) ≤
      ∑ J : Fin randomizerAttemptLimit,
        potential (setProj (trialSet P (.grd rnd b j) J.val)) σ := by
  rw [sum_pot_trialSet_split P rnd b hj, trialW_recUWt_eq hr b j hσ, tsum_fintype]
  refine add_le_add le_rfl ?_
  have hmono : ∀ (r : Option HashOutput × QMem) (J : Fin randomizerAttemptLimit),
      potential (setProj (trialSet P (srchRdNx (.grd rnd b j)
          (.readH (trialCell P l e msg b j) (trialUpdQ l e (trialCell P l e msg b j))) r) J.val))
        (MatrixMap.conj (hwReadKraus (.readH (trialCell P l e msg b j)
          (trialUpdQ l e (trialCell P l e msg b j))) r) σ) ≤
      potential (setProj (trialSet P (.grd rnd b (j + 1)) J.val))
        (MatrixMap.conj (hwReadKraus (.readH (trialCell P l e msg b j)
          (trialUpdQ l e (trialCell P l e msg b j))) r) σ) := fun r J ↦ by
    show potential (setProj (trialSet P
      (match Codeword.decode (truncateHash (r.1.getD 0)) with
        | some _ => SrchMode.free
        | none => SrchMode.grd rnd b (j + 1)) J.val)) _ ≤ _
    split
    · rw [show trialSet P SrchMode.free J.val = ∅ from rfl, potential_setProj_empty]
      exact zero_le
    · exact le_rfl
  refine (Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun J _ ↦ hmono r J).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun J _ ↦ ?_
  show ∑ r : Option HashOutput × QMem, potential (setProj
      (if j + 1 ≤ J.val then RecTrial P rnd b J.val else ∅)) _ ≤
    potential (setProj (if j + 1 ≤ J.val then RecTrial P rnd b J.val else ∅)) σ
  split_ifs with hJ
  · refine sum_pot_recTrial_readH_le P rnd b J.val (fun h ↦ ?_) l e hσ
    rw [rndCell_eq hr] at h
    have := trialCell_injective_trial hj J.isLt h
    omega
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun r _ ↦ potential_setProj_empty _) zero_le

/-- **The step of the moded potential**: the recorded unselected weight of a trial read plus the
later trials' masses after it are at most the trials' masses before it; a reveal of a randomizer
base charges its trials' masses. -/
theorem revQW_step (P : PublicParameter) (θ : HPos → Digest) (μ : SrchMode)
    (i : (RSpec SelMem).Port)
    (σ : Matrix ((RSpec SelMem).In i × RD) ((RSpec SelMem).In i × RD) ℂ) (hσ : σ.PosSemidef)
    (hok : srchOkZ P μ i) :
    extWeight (hwCost (trialW recUWt) fun _ _ ↦ 0) i σ +
        ∑' r, ∑ J : Fin randomizerAttemptLimit,
          potential (setProj (trialSet P (srchNxZ θ μ i r) J.val))
            (((runtimeR m0Q).step i).branch r σ) ≤
      ∑ J : Fin randomizerAttemptLimit, potential (setProj (trialSet P μ J.val)) σ +
        revQW P θ i σ := by
  rcases i with ((p | c) | c) | T
  · show (0 : ℝ≥0∞) + ∑' r, ∑ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSet P .free J.val)) _ ≤ _
    refine le_of_eq_of_le ?_ zero_le
    rw [zero_add]
    exact ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦
      potential_setProj_empty _
  · rcases μ with _ | ⟨rnd, b, j⟩
    · exact hok.elim
    have hb : ∀ r, ((runtimeR m0Q).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦ LinearMap.congr_fun
          (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain) m0Q c r) σ
    rw [show revQW P θ (.inl (.inl (.inr c))) σ = 0 from rfl, add_zero]
    refine (add_le_add le_rfl (le_of_eq (tsum_congr fun r ↦ congrArg (fun τ ↦
      ∑ J : Fin randomizerAttemptLimit, potential (setProj (trialSet P
        (srchRdNx (.grd rnd b j) c r) J.val)) τ) (hb r)))).trans ?_
    show trialW recUWt c σ + ∑' r : c.Result, ∑ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSet P (srchRdNx (.grd rnd b j) c r) J.val))
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      ∑ J : Fin randomizerAttemptLimit, potential (setProj (trialSet P (.grd rnd b j) J.val)) σ
    obtain ⟨hj, l, e, msg, hr, rfl⟩ := hok
    rw [trialRead_eq]
    exact readH_step P hr b hj hσ
  · show (0 : ℝ≥0∞) + ∑' r, ∑ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSet P .free J.val)) _ ≤ _
    refine le_of_eq_of_le ?_ zero_le
    rw [zero_add]
    exact ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦
      potential_setProj_empty _
  · show (0 : ℝ≥0∞) + ∑' m, ∑ J : Fin randomizerAttemptLimit,
      potential (setProj (trialSet P (revNxQ T fun rnd ↦ θ (loC rnd)) J.val))
        (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T m) σ) ≤ _
    rw [zero_add]
    rcases hT : rndOfT T with _ | rnd
    · have hn : revNxQ T (fun rnd ↦ θ (loC rnd)) = .free := by
        unfold revNxQ
        rw [hT]
      rw [hn]
      exact le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun m ↦ Finset.sum_eq_zero fun J _ ↦
        potential_setProj_empty _) zero_le
    · have hn : revNxQ T (fun rnd ↦ θ (loC rnd)) = .grd rnd (θ (loC rnd)) 0 := by
        unfold revNxQ
        rw [hT]
      rw [hn]
      refine le_add_left ?_
      show _ ≤ (match rndOfT T with
        | some rnd => ∑ J : Fin randomizerAttemptLimit,
            diagMass {q : Unit × RReg SelMem | q.2 ∈ RecTrial P rnd (θ (loC rnd)) J} σ
        | none => 0)
      rw [hT, tsum_fintype, Finset.sum_comm]
      refine Finset.sum_le_sum fun J _ ↦ ?_
      show ∑ m : QMem, potential (setProj (if 0 ≤ J.val then
        RecTrial P rnd (θ (loC rnd)) J.val else ∅))
          (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T m) σ) ≤
        diagMass {q : Unit × RReg SelMem | q.2 ∈ RecTrial P rnd (θ (loC rnd)) J.val} σ
      rw [ite_eq_left (Nat.zero_le _)]
      exact (sum_pot_recTrial_rec_le _ _ _ _ T hσ).trans_eq (potential_setProj _ hσ)

/-- **`totalWeight_le_modedP` from a mode without potential.** -/
theorem totalWeight_le_modedP_zero {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}}
    {Ω : QReg → Type w} {Mode : Type} {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode} (R : QuantumRuntime spec)
    (I : L.Interp) {Zp J : Type} [Fintype Zp] [Fintype J]
    (Kp : Mode → J → Matrix Zp R.D ℂ)
    (w c : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (h : ∀ μ i σ, σ.PosSemidef → ok μ i →
      w i σ + ∑' r, ∑ j, potential (Kp (nx μ i r) j) ((R.step i).branch r σ) ≤
        ∑ j, potential (Kp μ j) σ + c i σ)
    {fin : (Σ u, Ω u) → Mode → Prop} {A : QReg} (x : QuantumComp L spec Ω A) (μ : Mode)
    (hx : Quantum.Xmss.Assembly.ModedP ok nx fin μ x) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) (h0 : ∀ j, Kp μ j = 0) :
    R.totalWeight I w x ρ ≤ R.totalWeight I c x ρ := by
  refine (totalWeight_le_modedP R I Kp w c h x μ hx hρ).trans (le_of_eq ?_)
  rw [Finset.sum_eq_zero fun j _ ↦ potential_of_eq_zero (h0 j) ρ, zero_add]

/-- The move for a moded program at the parameter `P`. -/
theorem totalWeight_recU_le_revQW {Ω : QReg → Type} (P : PublicParameter)
    (θ : HPos → Digest) {fin : (Σ u, Ω u) → SrchMode → Prop}
    (x : QuantumComp LocalSig.instruments.{0} (RSpec SelMem) Ω (QReg.of Unit))
    (hx : Quantum.Xmss.Assembly.ModedP (srchOkZ P) (srchNxZ θ) fin .free x) :
    (runtimeR m0Q).totalWeight .instruments (extWeight (hwCost (trialW recUWt) fun _ _ ↦ 0))
        x initQ ≤
      (runtimeR m0Q).totalWeight .instruments (revQW P θ) x initQ := by
  exact totalWeight_le_modedP_zero (runtimeR m0Q) .instruments (Zp := RReg SelMem)
    (fun μ (J : Fin randomizerAttemptLimit) ↦ setProj (trialSet P μ J.val))
    (extWeight (hwCost (trialW recUWt) fun _ _ ↦ 0)) (revQW P θ)
    (fun μ i σ hσ hok ↦ revQW_step P θ μ i σ hσ hok) x .free hx initQ_posSemidef
    fun j ↦ setProj_trialSet_free P j.val

/-- **The recorded unselected weights are at most the reveal charges.** -/
theorem recUPre_le_revQW (A : Adversary) (θ : HPos → Digest) :
    recUPre A θ ≤
      (runtimeR m0Q).totalWeight .instruments (revQW (θ paramC) θ) (prefixQ A θ) initQ :=
  totalWeight_recU_le_revQW (θ paramC) θ (prefixQ A θ) (modedP_prefixQ A θ)

/-! ## First and repeated reveals -/

/-- **The first-reveal charges** under the parameter `P`: at a reveal of `{loC rnd}` with
`loC rnd` unrevealed, the masses of the recorded trial cells of `rnd`'s search. -/
noncomputable def firstQW (P : PublicParameter) (θ : HPos → Digest) :
    ∀ i : (RSpec SelMem).Port,
      Matrix ((RSpec SelMem).In i × RD) ((RSpec SelMem).In i × RD) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match rndOfT T with
    | some rnd => ∑ J : Fin randomizerAttemptLimit,
        diagMass {q : Unit × RReg SelMem | loC rnd ∉ q.2.2.2.1 ∧
          q.2.1.1 (rndCell P rnd (θ (loC rnd)) J) ≠ none} σ
    | none => 0
  | _, _ => 0

theorem diagMass_le_add_of_subset {α : Type} [Fintype α] {S B C : Set α}
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

theorem revQW_le (P : PublicParameter) (θ : HPos → Digest) (i : (RSpec SelMem).Port)
    (σ : Matrix ((RSpec SelMem).In i × RD) ((RSpec SelMem).In i × RD) ℂ) :
    revQW P θ i σ ≤ 1 * firstQW P θ i σ + 1 * reRevQW i σ := by
  rw [one_mul, one_mul]
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · show (match rndOfT T with
        | some rnd => ∑ J : Fin randomizerAttemptLimit,
            diagMass {q : Unit × RReg SelMem | q.2 ∈ RecTrial P rnd (θ (loC rnd)) J} σ
        | none => 0) ≤ (match rndOfT T with
        | some rnd => ∑ J : Fin randomizerAttemptLimit,
            diagMass {q : Unit × RReg SelMem | loC rnd ∉ q.2.2.2.1 ∧
              q.2.1.1 (rndCell P rnd (θ (loC rnd)) J) ≠ none} σ
        | none => 0) + (match rndOfT T with
        | some rnd => (randomizerAttemptLimit : ℝ≥0∞) *
            diagMass {q : Unit × RReg SelMem | ReRevQ rnd q.2} σ
        | none => 0)
    rcases hT : rndOfT T with _ | rnd
    · exact zero_le
    · obtain ⟨⟨l, e, msg⟩, hr⟩ := Option.isSome_iff_exists.mp (rndOfT_spec hT).1
      have hN : (randomizerAttemptLimit : ℝ≥0∞) *
          diagMass {q : Unit × RReg SelMem | ReRevQ rnd q.2} σ =
          ∑ _J : Fin randomizerAttemptLimit,
            diagMass {q : Unit × RReg SelMem | ReRevQ rnd q.2} σ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only
      rw [hN, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun J _ ↦ diagMass_le_add_of_subset (fun q hq ↦ ?_) σ
      by_cases hl : loC rnd ∈ q.2.2.2.1
      · refine .inr ⟨hl, l, e, msg, hr, ?_⟩
        exact (rndU_iff hr _).mp hq.2
      · exact .inl ⟨hl, hq.1⟩

/-- **The reveal charges split into the first and the repeated reveals.** -/
theorem recUPre_le_split (A : Adversary) (θ : HPos → Digest) :
    recUPre A θ ≤
      (runtimeR m0Q).totalWeight .instruments (firstQW (θ paramC) θ) (prefixQ A θ) initQ +
        (runtimeR m0Q).totalWeight .instruments reRevQW (prefixQ A θ) initQ := by
  refine (recUPre_le_revQW A θ).trans ((totalWeight_le_add (runtimeR m0Q) .instruments _ _ _ 1 1
    (fun i σ _ ↦ revQW_le (θ paramC) θ i σ) (prefixQ A θ) initQ_posSemidef).trans_eq ?_)
  rw [one_mul, one_mul]

end Quantum.Qrom.Xmss

end
