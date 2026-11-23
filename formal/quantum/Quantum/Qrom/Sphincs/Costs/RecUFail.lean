module

public import Quantum.Qrom.Sphincs.Costs.RecUMove
public import Quantum.Qrom.Xmss.Costs.RecUFail

@[expose] public section

/-!
# The repeated reveals of an unselected key: the failed searches

The charge `reRevQWU` of the challenge prefix (a reveal of a key's coordinate already revealed,
the key still unselected) adds up to at most `K · 2^-200` with `K` classical calls
(`totalWeight_reRevQW_le`), as leanXMSS's `Costs/RecUFail`.

* **The invariant in the decompressed basis** (`FInvF`, `fInvF_step`, `init_fInvF`): no empty
  cell, no hardwired encoding cell, the started keys' coordinates revealed, the mode's value the
  key's signed value, and every key of the signatures whose coordinate is revealed and which is
  unselected has every trial already run on a digest that is no codeword (`RunFail`), on the
  decompressed `h`-database. A reveal outside a search adds coordinates of started keys only
  (`RevOkU`); the trial cells are encoding cells, which the prefix never hardwires.
* **The repeated reveals** (`reRevQW_le_charge`): a repeated reveal with the key unselected lies
  in the database event `failSetF θ` (some key fails all `2^32` trials of its one search), whose
  decompressed projector commutes with every called port (the programs hardwire cells off the
  encoding slots only, `hwFixF θ`); CwReFail's `totalWeight_charge_potential_le` and
  `potential_hwDecProj_init`.
* **Counting** (`frac_failDbF_le`): at most `|Key| (1 - ρ_c)^(2^32)` of the tables fail some
  search, `ρ_c ≥ 2^-14`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (diagMass totalWeight_const_mul_weight progUpdate)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR NoBot decR liftAns noBot_init
  forallQueries_dec_moded runtimeR_commute_hwDecProj totalWeight_charge_potential_le
  diagMass_le_potential_hwDecProj potential_hwDecProj_init natCast_pow_sub_div_le_exp hwOfSets
  hwOfSets_fst PortCw extCls totalWeight_le_of_forallQueries)

attribute [local irreducible] sphincsRom Fin.fintype

/- Instance search for the register's decidable equality exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## Selections -/

/-- A trial read of a codeword digest leaves its key selected. -/
theorem cwUpd_ne_noneF {K : Key} {z : Qrom.HashDomain} {mem : SelMem} {w : PairOut}
    (hv : Quantum.Sphincs.Codeword.Valid (pairDigest w)) : cwUpd K z mem (some w) K ≠ none := by
  by_cases hm : mem K = none
  · rw [cwUpd_some_of_none K z hm w]
    unfold cwSel
    rw [ite_eq_left hv, SelMem.select_self]
    exact Option.some_ne_none _
  · rw [cwUpd_of_ne_none hm]
    exact hm

/-! ## The invariant of the failed searches -/

section inv

variable (θ : TVals)

/-- The trials of `K` already run in the mode `μ`: those before the current trial of its search,
all of them otherwise. -/
def doneF : ModeU → Key → ℕ
  | .rest _, _ => encodingAttemptLimit
  | .grd _ K' _ j, K => if K' = K then j else encodingAttemptLimit

theorem doneF_of_rest {μ : ModeU} (h : μ.Rest) (K : Key) :
    doneF μ K = encodingAttemptLimit := by
  rcases μ with ks | ⟨ks, K', m, j⟩
  · rfl
  · have hj : j = encodingAttemptLimit := h
    subst hj
    show (if K' = K then encodingAttemptLimit else encodingAttemptLimit) = _
    split_ifs <;> rfl

/-- The pair of trial `j` of the search of `K` (under `PK.seed`, on the value `K` signs), on the
databases `D`. -/
def trialValF (K : Key) (j : ℕ) (D : DbReg PairOut Qrom.HashDomain) : PairOut :=
  (D.1 (trialCell (tabOf θ).publicSeed K ((tabOf θ).valuePos (msgPos K)) j)).getD 0

/-- The mode's search runs on the value its key signs. -/
def ModeOkF : ModeU → Prop
  | .rest _ => True
  | .grd _ K m _ => m = (tabOf θ).valuePos (msgPos K)

/-- **The trials already run failed**: every key of the signatures whose coordinate is revealed
and which is unselected has its trials already run on digests that are no codewords. -/
def RunFail (μ : ModeU) (s : RegQ) : Prop :=
  ∀ K, InRangeU K → vcoord (msgPos K) ∈ s.2.2.1 → s.2.2.2 K = none →
    ∀ j < doneF μ K, ¬ Quantum.Sphincs.Codeword.Valid (pairDigest (trialValF θ K j s.1))

/-- **The invariant of the failed searches**, in the decompressed basis. -/
def FInvF (μ : ModeU) : Set RegQ :=
  {s | NoBot s ∧ EncFree (pkQ θ) s ∧ (∀ K ∈ μ.ks, vcoord (msgPos K) ∈ s.2.2.1) ∧
    ModeOkF θ μ ∧ RunFail θ μ s}

theorem fInvF_rest {μ : ModeU} (hμ : μ.Rest) {s : RegQ} (hs : s ∈ FInvF θ μ) :
    s ∈ FInvF θ (.rest μ.ks) :=
  ⟨hs.1, hs.2.1, hs.2.2.1, trivial, fun K hK hl hu j hj ↦
    hs.2.2.2.2 K hK hl hu j (by rw [doneF_of_rest hμ K]; exact hj)⟩

/-- **A record**: a reveal of a key's coordinate starts its search with no trial run; another
reveal adds only coordinates of started keys. -/
theorem fInvF_rec {μ : ModeU} (hμ : μ.Rest) {T : Finset TPos}
    (hT : keyOfTU T = none → RevOkU μ.ks T) {s : RegQ} (hs : s ∈ FInvF θ μ) :
    ((s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) : RegQ) ∈
      FInvF θ (revNxU μ T fun K ↦ (tabOf θ).valuePos (msgPos K)) := by
  obtain ⟨hnb, hef, hks, -, hl⟩ := hs
  rcases hk : keyOfTU T with _ | K₀
  · rw [revNxU_none μ hk]
    have hok := hT hk
    refine ⟨hnb, hef, fun K hK ↦ Finset.mem_union_left _ (hks K hK), trivial,
      fun K hK hlab hu j hj ↦ ?_⟩
    have hl1 : vcoord (msgPos K) ∈ s.2.2.1 := by
      rcases Finset.mem_union.mp hlab with h | h
      · exact h
      · exact hks K (hok K hK h)
    exact hl K hK hl1 hu j (hj.trans_eq (doneF_of_rest hμ K).symm)
  · obtain ⟨hK₀, rfl⟩ := keyOfTU_spec hk
    rw [revNxU_sing μ hK₀]
    refine ⟨hnb, hef, fun K hK ↦ ?_, rfl, fun K hK hlab hu j hj ↦ ?_⟩
    · rcases Finset.mem_insert.mp hK with rfl | h
      · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · exact Finset.mem_union_left _ (hks K h)
    · by_cases he : K₀ = K
      · subst he
        have hd : ∀ m, doneF (.grd (insert K₀ μ.ks) K₀ m 0) K₀ = 0 := fun _ ↦ ite_eq_left rfl
        exact absurd (hj.trans_eq (hd _)) (Nat.not_lt_zero j)
      · have hd : ∀ m, doneF (.grd (insert K₀ μ.ks) K₀ m 0) K = encodingAttemptLimit :=
          fun _ ↦ ite_eq_right he
        have hl1 : vcoord (msgPos K) ∈ s.2.2.1 := by
          rcases Finset.mem_union.mp hlab with h | h
          · exact h
          · exact absurd (vcoord_msgPos_injU hK₀ hK (Finset.mem_singleton.mp h).symm) he
        exact hl K hK hl1 hu j ((hj.trans_eq (hd _)).trans_eq (doneF_of_rest hμ K).symm)

/-- **A program of a cell off the encoding slots** keeps the invariant: the trial cells keep their
database values. -/
theorem fInvF_prog {μ : ModeU} (hμ : μ.Rest) {z : Qrom.HashDomain} {a : PairOut}
    (hz : ∀ K : Key, slotOf (pkQ θ) z ≠ some (.enc K.1 K.2.1 K.2.2)) {s s' : RegQ}
    (hs : s ∈ FInvF θ μ) (hp : ProgRelS z a s s') : s' ∈ FInvF θ (.rest μ.ks) := by
  obtain ⟨hnb, hef, hks, -, hl⟩ := hs
  obtain ⟨h2, hnb', h1⟩ := hp
  have hm : s'.2.2 = s.2.2 := (congrArg Prod.snd h2 :)
  have hw : s'.2.1 = progUpdate (.programH z a) s.2.1 := (congrArg Prod.fst h2 :)
  refine ⟨hnb' hnb, fun x hx K ↦ ?_, fun K hK ↦ by rw [hm]; exact hks K hK, trivial,
    fun K hK hlab hu j hj ↦ ?_⟩
  · rw [hw] at hx
    have hx' : (Function.update s.2.1.1 z (some a) x).isSome := hx
    by_cases hxz : x = z
    · subst hxz
      exact hz K
    · rw [Function.update_of_ne hxz] at hx'
      exact hef x hx' K
  · rw [hm] at hlab hu
    have hc : trialValF θ K j s'.1 = trialValF θ K j s.1 := by
      unfold trialValF
      exact congrArg (fun o : Option PairOut ↦ o.getD 0) (h1 _ fun he ↦ hz K (by
        rw [← he]
        exact slotOf_trialCell (pkQ θ) K _ j))
    rw [hc]
    exact hl K hK hlab hu j (hj.trans_eq (doneF_of_rest hμ K).symm)

/-- **The read of a trial**: a codeword digest selects the key and ends the search; otherwise the
trial failed. -/
theorem fInvF_read {ks : Finset Key} {K : Key} {m : Digest} {j : ℕ} {s : RegQ}
    (hs : s ∈ FInvF θ (.grd ks K m j)) (r : Option PairOut × QMem)
    (hrs : r = liftAns s (.readH (trialCell (tabOf θ).publicSeed K m j)
      (cwUpd K (trialCell (tabOf θ).publicSeed K m j)))) :
    readFinS s (trialCell (tabOf θ).publicSeed K m j)
        (cwUpd K (trialCell (tabOf θ).publicSeed K m j)) ∈
      FInvF θ (decNxU ks K m j (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1))) := by
  set z := trialCell (tabOf θ).publicSeed K m j with hzdef
  obtain ⟨hnb, hef, hks, hm, hl⟩ := hs
  have hm' : m = (tabOf θ).valuePos (msgPos K) := hm
  have hzs : slotOf (pkQ θ) z = some (.enc K.1 K.2.1 K.2.2) := slotOf_trialCell (pkQ θ) K m j
  have hw0 : s.2.1.1 z = none := by
    by_contra h
    exact hef z (Option.ne_none_iff_isSome.mp h) K hzs
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hnb.1 z)
  have hv : (hwView s.2.1 s.1).1 z = some w := by
    show (s.2.1.1 z).or (s.1.1 z) = some w
    rw [hw0, hw]
    rfl
  have hr1 : r.1 = some w := by
    rw [hrs]
    exact hv
  have hfin : readFinS s z (cwUpd K z) =
      (s.1, s.2.1, (s.2.2.1, cwUpd K z s.2.2.2 (some w))) := by
    unfold readFinS
    rw [hv]
  rw [hfin, hr1]
  have hu : ∀ K', cwUpd K z s.2.2.2 (some w) K' = none → s.2.2.2 K' = none :=
    fun _ h ↦ cwUpd_eq_noneU h
  have hval : trialValF θ K j s.1 = w := by
    unfold trialValF
    rw [← hm', ← hzdef, hw]
    rfl
  generalize hd : TargetSum.decodeDigest (truncateHash ((some w).getD 0).1) = d
  have hd' : TargetSum.decodeDigest (pairDigest w) = d := hd
  rcases d with _ | x
  · show _ ∈ FInvF θ (.grd ks K m (j + 1))
    refine ⟨hnb, hef, hks, hm, fun K' hK' hlab hu' j' hj' ↦ ?_⟩
    by_cases hne : K = K'
    · subst hne
      have h1 : doneF (.grd ks K m (j + 1)) K = j + 1 := ite_eq_left rfl
      rw [h1] at hj'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · have h0 : doneF (.grd ks K m j) K = j := ite_eq_left rfl
        exact hl K hK' hlab (hu K hu') j' (hj'.trans_eq h0.symm)
      · show ¬ Quantum.Sphincs.Codeword.Valid (pairDigest (trialValF θ K j' s.1))
        rw [hval]
        exact Quantum.Sphincs.Codeword.decode_eq_none_iff.mp hd'
    · have h1 : doneF (.grd ks K m (j + 1)) K' = doneF (.grd ks K m j) K' := by
        show (if K = K' then j + 1 else encodingAttemptLimit) =
          (if K = K' then j else encodingAttemptLimit)
        rw [ite_eq_right hne, ite_eq_right hne]
      exact hl K' hK' hlab (hu K' hu') j' (hj'.trans_eq h1)
  · show _ ∈ FInvF θ (.rest ks)
    refine ⟨hnb, hef, hks, trivial, fun K' hK' hlab hu' j' hj' ↦ ?_⟩
    have hvld := Quantum.Sphincs.Codeword.valid_of_decode hd'
    have hne : K ≠ K' := by
      rintro rfl
      exact cwUpd_ne_noneF hvld hu'
    have h1 : doneF (.grd ks K m j) K' = encodingAttemptLimit := ite_eq_right hne
    exact hl K' hK' hlab (hu K' hu') j' (hj'.trans_eq h1.symm)

/-- **Every allowed call keeps the invariant**, in the decompressed basis. -/
theorem fInvF_step (μ : ModeU) (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (r : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Result i)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ) ℂ)
    (hok : srchOkZ θ μ i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ ↦
      m.2) (FInvF θ μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Out i × RegQ ↦ m.2)
      (FInvF θ (srchNxZ θ μ i r))
      (((decR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · exact (decR_sponge_suppS m0Q i r _ σ hσ).mono fun s hs ↦ fInvF_rest θ hok hs
  · rcases μ with ks | ⟨ks, K, m, j⟩
    · exact hok.elim
    · obtain ⟨-, rfl⟩ := hok
      refine (decR_readH_suppS m0Q (trialCell (tabOf θ).publicSeed K m j)
        (cwUpd K (trialCell (tabOf θ).publicSeed K m j)) r _ σ hσ).mono fun s' hs' ↦ ?_
      obtain ⟨s, hs, hrs, rfl⟩ := hs'
      exact fInvF_read θ hs r hrs
  · obtain ⟨hμ, z, a, rfl, hz⟩ := hok
    refine (decR_progH_suppS m0Q z a r _ σ hσ).mono fun s' hs' ↦ ?_
    obtain ⟨s, hs, hp⟩ := hs'
    exact fInvF_prog θ hμ hz hs hp
  · refine (decR_rec_suppS m0Q T r _ σ hσ).mono fun s' hs' ↦ ?_
    obtain ⟨s, hs, -, rfl⟩ := hs'
    exact fInvF_rec θ hok.1 hok.2 hs

/-- The initial register in the decompressed basis: no empty cell, nothing hardwired, nothing
revealed. -/
theorem init_fInvF :
    QuerySupportedOn (fun m : QReg.of Unit × RegQ ↦ m.2) (FInvF θ (.rest ∅))
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain QMem) initQ) := by
  have hnb := noBot_init (X := PairOut) (Z := Qrom.HashDomain) m0Q
    ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
  have h0 : QuerySupportedOn (fun m : QReg.of Unit × RegQ ↦ m.2)
      {s | s.2 = (hwEmpty PairOut Qrom.HashDomain, m0Q)} initQ := by
    intro m m' hm
    change (((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      (SubState.basis (((Database.empty, Database.empty, Database.empty),
        hwEmpty PairOut Qrom.HashDomain, m0Q) : RegQ)).matrix) m m' ≠ 0 at hm
    rw [kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [SubState.matrix_basis, Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨(congrArg Prod.snd he.1).symm, (congrArg Prod.snd he.2).symm⟩
    · exact absurd rfl h
  have h1 := QuerySupportedOn.conj h0
    (K := (1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      compressReg PairOut Qrom.HashDomain QMem)
    (q' := fun m : QReg.of Unit × RegQ ↦ m.2)
    (S' := {s | s.2 = (hwEmpty PairOut Qrom.HashDomain, m0Q)})
    fun m' m hK hm ↦ by
      have hK' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
      rw [compressReg, kroneckerMap_apply] at hK'
      have he : m'.2.2 = m.2.2 := by
        by_contra hne
        exact right_ne_zero_of_mul hK' (Matrix.one_apply_ne hne)
      show m'.2.2 = _
      rw [he]
      exact hm
  have hmem : ∀ s : RegQ, NoBot s → s.2 = (hwEmpty PairOut Qrom.HashDomain, m0Q) →
      s ∈ FInvF θ (.rest ∅) := fun s hs he ↦ by
    refine ⟨hs, fun x hx ↦ ?_, fun K hK ↦ absurd hK (Finset.notMem_empty _), trivial,
      fun _ _ hl _ _ _ ↦ ?_⟩
    · rw [he] at hx
      exact absurd hx (by simp [hwEmpty])
    · rw [he] at hl
      exact absurd hl (Finset.notMem_empty _)
  intro a b hab
  exact ⟨hmem _ (hnb a b hab).1 (h1 a b hab).1, hmem _ (hnb a b hab).2 (h1 a b hab).2⟩

end inv

/-! ## The failure event -/

section fail

variable (θ : TVals)

/-- **Some search fails on the databases**: a key all of whose `2^32` trials (on the value it
signs) read pairs whose digests are no codewords. -/
def FailDbF (D : DbReg PairOut Qrom.HashDomain) : Prop :=
  ∃ K : Key, ∀ j < encodingAttemptLimit,
    ¬ Quantum.Sphincs.Codeword.Valid (pairDigest (trialValF θ K j D))

/-- The registers whose databases fail a search. -/
def failSetF : Set RegQ := {s | FailDbF θ s.1}

/-- `failSetF`, decided classically. -/
noncomputable instance instDecidableFailSetFS : DecidablePred (· ∈ failSetF θ) :=
  Classical.decPred _

/-- The static hardwiring off the trial cells: every `h`-cell off the encoding slots under
`pkQ θ`, every `k`, `k'` cell. -/
noncomputable def hwFixF : Hw PairOut Qrom.HashDomain :=
  hwOfSets {z : Qrom.HashDomain | ∀ K : Key, slotOf (pkQ θ) z ≠ some (.enc K.1 K.2.1 K.2.2)}
    Set.univ Set.univ

theorem hwFixF_trial (K : Key) (m : Digest) (j : ℕ) :
    (hwFixF θ).1 (trialCell (tabOf θ).publicSeed K m j) = none := by
  by_contra h
  exact (hwOfSets_fst.mp h) K (slotOf_trialCell (pkQ θ) K m j)

/-- `FailDbF` reads the trial cells only, off `hwFixF θ`. -/
theorem offHw_failDbF : OffHw (hwFixF θ) (FailDbF θ) := by
  intro D D' h1 _ _
  have hc : ∀ K j, trialValF θ K j D = trialValF θ K j D' := fun K j ↦ by
    unfold trialValF
    exact congrArg (fun o : Option PairOut ↦ o.getD 0) (h1 _ (hwFixF_trial θ K _ j))
  exact ⟨fun ⟨K, h⟩ ↦ ⟨K, fun j hj ↦ by rw [← hc]; exact h j hj⟩,
    fun ⟨K, h⟩ ↦ ⟨K, fun j hj ↦ by rw [hc]; exact h j hj⟩⟩

variable {θ}

theorem portCw_of_srchOkZ {μ : ModeU} {i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port}
    (h : srchOkZ θ μ i) : PortCw (S := TPos) (M := SelMem) (hwFixF θ) i := by
  rcases i with ((p | c) | c) | T
  · trivial
  · trivial
  · obtain ⟨-, z, a, rfl, hz⟩ := h
    exact hwOfSets_fst.mpr hz
  · trivial

/-- **A repeated reveal with the key unselected is in the failure event**: at a record call
allowed by a rest mode, on the invariant, a revealed key of the signatures that is unselected has
run all its trials. -/
theorem reRevQW_le_charge (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ) ℂ)
    (hσ : σ.PosSemidef)
    (h : ∃ μ, srchOkZ θ μ i ∧
      QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ ↦
        m.2) (FInvF θ μ)
        (MatrixMap.conj ((1 : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i)
          ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain QMem) σ)) :
    reRevQWU i σ ≤ (encodingAttemptLimit : ℝ≥0∞) *
      (((if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0 : ℕ) :
        ℝ≥0∞) * potential (hwDecProj (failSetF θ)) σ) := by
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · obtain ⟨μ, ⟨hrest, -⟩, hS⟩ := h
    rcases hT : keyOfTU T with _ | K
    · simp only [reRevQWU, hT]
      exact zero_le
    · simp only [reRevQWU, hT]
      have h1 : ((if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) (.inr T) then 1
          else 0 : ℕ) : ℝ≥0∞) = 1 := by simp [extCls]
      rw [h1, one_mul]
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hK := (keyOfTU_spec hT).1
      classical
      exact diagMass_le_potential_hwDecProj (fun b : Hw PairOut Qrom.HashDomain × QMem ↦
        vcoord (msgPos K) ∈ b.2.1 ∧ b.2.2 K = none) (failSetF θ) _ hσ hS fun s hs hP ↦
          ⟨K, fun j hj ↦ hs.2.2.2.2 K hK hP.1 hP.2 j
            (hj.trans_eq (doneF_of_rest hrest K).symm)⟩

end fail

/-! ## Counting the failed searches -/

section count

/-- The trial cells of the search of a key on the value it signs. -/
def failCellF (θ : TVals) (K : Key) (j : ℕ) : Qrom.HashDomain :=
  trialCell (tabOf θ).publicSeed K ((tabOf θ).valuePos (msgPos K)) j

theorem card_key_leF : Fintype.card Key ≤ 2 ^ 38 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num [layerCount, indexBits, layerHeight, topLayer]

/-- **All `N` trials fail** (over an abstract type): the values failing a test of fraction at
least `ρ`, to the power `N`, are at most `exp (-ρ N)` of all. -/
theorem pow_card_not_div_le_expF {α : Type} [Fintype α] [Nonempty α] (p : α → Prop)
    [DecidablePred p] (N : ℕ) (ρ : ℝ)
    (hρ : ρ ≤ ((Finset.univ.filter p).card : ℝ) / Fintype.card α) :
    (((Finset.univ.filter fun a ↦ ¬ p a).card ^ N : ℕ) : ℝ≥0∞) /
      ((Fintype.card α ^ N : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-(ρ * N))) := by
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ) p
  rw [Finset.card_univ] at hsum
  have hg : (Finset.univ.filter fun a ↦ ¬ p a).card =
      Fintype.card α - (Finset.univ.filter p).card := by omega
  rw [hg]
  exact natCast_pow_sub_div_le_exp _ _ N (by omega) Fintype.card_pos ρ hρ

/-- Distinct trials of a key's search read distinct cells. -/
theorem failCellF_inj (θ : TVals) (K : Key) :
    ∀ a < encodingAttemptLimit, ∀ b < encodingAttemptLimit,
      failCellF θ K a = failCellF θ K b → a = b :=
  fun _ ha _ hb h ↦ (trialCell_injU ha hb h).2

open scoped Classical in
/-- **The failure fraction**: `|Key| · (1 - ρ_c)^(2^32)` over the tables. -/
theorem frac_failDbF_le (θ : TVals) :
    ((Finset.univ.filter fun t ↦ FailDbF θ (ofFunDbs t)).card : ℝ≥0∞) /
      Fintype.card ((Qrom.HashDomain → PairOut) × (PairOut → Qrom.HashDomain) ×
        (PairOut → Qrom.HashDomain)) ≤
      Fintype.card Key * ((((Finset.univ.filter fun ω : PairOut ↦
        ¬ Quantum.Sphincs.Codeword.Valid (pairDigest ω)).card ^ encodingAttemptLimit : ℕ) :
          ℝ≥0∞) / ((Fintype.card PairOut ^ encodingAttemptLimit : ℕ) : ℝ≥0∞)) :=
  Quantum.Qrom.Xmss.frac_union_fail_le (failCellF θ)
    (fun ω : PairOut ↦ ¬ Quantum.Sphincs.Codeword.Valid (pairDigest ω))
    encodingAttemptLimit (failCellF_inj θ) _ fun _ ht ↦ ht

end count

/-! ## The bound -/

set_option exponentiation.threshold 4096 in
/-- `2^32` trials at codeword fraction `2^-14` all fail with probability at most `2^-2048`. -/
theorem exp_neg_trialsF :
    Real.exp (-((2 ^ 14 : ℝ)⁻¹ * (encodingAttemptLimit : ℝ))) ≤ 1 / 2 ^ 2048 := by
  have h1 : (2 ^ 14 : ℝ)⁻¹ * (encodingAttemptLimit : ℝ) = 262144 := by
    norm_num [encodingAttemptLimit]
  rw [h1, Real.exp_neg, one_div]
  refine inv_anti₀ (by positivity) ?_
  calc (2 : ℝ) ^ 2048 ≤ Real.exp 1 ^ 2048 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
    _ = Real.exp 2048 := by
        rw [← Real.exp_nat_mul]
        norm_num
    _ ≤ Real.exp 262144 := Real.exp_le_exp.mpr (by norm_num)

set_option exponentiation.threshold 4096 in
/-- The numbers: `2^32 · 2^38 · 2^-2048 ≤ 2^-200`. -/
theorem reRev_numbersF :
    (encodingAttemptLimit : ℝ≥0∞) * (((2 ^ 38 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 2048)) ≤
      (2 ^ 200 : ℝ≥0∞)⁻¹ := by
  rw [show (encodingAttemptLimit : ℝ≥0∞) = ENNReal.ofReal (2 ^ 32) by
      rw [encodingAttemptLimit, Nat.cast_pow, Nat.cast_ofNat, ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    show (2 ^ 200 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ 200) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

/-- The codeword pairs are at least a fraction `2^-14`. -/
theorem inv_two_pow_14_le_codewordF : (2 ^ 14 : ℝ)⁻¹ ≤ ((Finset.univ.filter fun ω : PairOut ↦
    Quantum.Sphincs.Codeword.Valid (pairDigest ω)).card : ℝ) / Fintype.card PairOut := by
  rw [card_codeword_pair_div]
  exact Quantum.Sphincs.inv_two_pow_14_le_rhoCw

/-- All `N` trials of a search fail on at most `exp (-2^-14 N)` of the tables. -/
theorem pow_not_codeword_div_le_expF (N : ℕ) :
    (((Finset.univ.filter fun ω : PairOut ↦
      ¬ Quantum.Sphincs.Codeword.Valid (pairDigest ω)).card ^ N : ℕ) : ℝ≥0∞) /
        ((Fintype.card PairOut ^ N : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (-((2 ^ 14 : ℝ)⁻¹ * N))) :=
  pow_card_not_div_le_expF (fun ω : PairOut ↦ Quantum.Sphincs.Codeword.Valid (pairDigest ω))
    N _ inv_two_pow_14_le_codewordF

/-- All `2^32` trials of a search fail on at most `2^-2048` of the tables. -/
theorem pow_not_codeword_div_leF :
    (((Finset.univ.filter fun ω : PairOut ↦
      ¬ Quantum.Sphincs.Codeword.Valid (pairDigest ω)).card ^ encodingAttemptLimit : ℕ) :
        ℝ≥0∞) / ((Fintype.card PairOut ^ encodingAttemptLimit : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 2 ^ 2048) :=
  (pow_not_codeword_div_le_expF encodingAttemptLimit).trans
    (ENNReal.ofReal_le_ofReal exp_neg_trialsF)

open scoped Classical in
/-- **The initial potential of the failure event**: at most `2^38 · 2^-2048`. -/
theorem potential_failSetF_le (θ : TVals) :
    potential (hwDecProj (failSetF θ)) initQ ≤
      ((2 ^ 38 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 2048) := by
  have h3 : potential (hwDecProj (failSetF θ)) initQ ≤
      ((Finset.univ.filter fun t ↦ FailDbF θ (ofFunDbs t)).card : ℝ≥0∞) /
        Fintype.card ((Qrom.HashDomain → PairOut) × (PairOut → Qrom.HashDomain) ×
          (PairOut → Qrom.HashDomain)) := by
    refine (le_of_eq (potential_hwDecProj_init m0Q (failSetF θ) (FailDbF θ) (fun _ ↦ Iff.rfl)
      ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
      (SubState.basis _).posSemidef)).trans ?_
    exact (mul_le_mul' (ENNReal.ofReal_le_one.mpr (SubState.basis _).trace_re_le_one)
      le_rfl).trans_eq (one_mul _)
  exact (h3.trans (frac_failDbF_le θ)).trans
    (mul_le_mul' (Nat.cast_le.mpr card_key_leF) pow_not_codeword_div_leF)

/-- **The repeated-reveal charges of the challenge prefix**: with at most `K` classical calls, at
most `K · 2^-200`. -/
theorem totalWeight_reRevQW_le {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversary)
    (θ : TVals) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K) :
    (runtimeR m0Q).totalWeight .instruments reRevQWU (prefixQ pol A θ) initQ ≤
      K * (2 ^ 200 : ℝ≥0∞)⁻¹ := by
  have hq := forallQueries_dec_moded m0Q (FInvF θ)
    (fun μ i r σ hok hσ ↦ fInvF_step θ μ i r σ hok hσ) LocalSig.Interp.instruments
    (prefixQ pol A θ) (.rest ∅) (modedP_prefixQ hpol A θ) (init_fInvF θ)
  have h1 := totalWeight_le_of_forallQueries (runtimeR m0Q) .instruments
    (fun i σ ↦ ∃ μ, srchOkZ θ μ i ∧
      QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i × RegQ ↦
        m.2) (FInvF θ μ)
        (MatrixMap.conj ((1 : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i)
          ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain QMem) σ)) (fun _ _ _ h ↦ h)
    (w' := fun i σ ↦ (encodingAttemptLimit : ℝ≥0∞) *
      (((if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0 : ℕ) :
        ℝ≥0∞) * potential (hwDecProj (failSetF θ)) σ))
    (fun i σ hσ hok ↦ reRevQW_le_charge i σ hσ hok) (prefixQ pol A θ) initQ_posSemidef hq
  have h1' := h1.trans_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments
    (encodingAttemptLimit : ℝ≥0∞) (fun i σ ↦
      ((if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0 : ℕ) :
        ℝ≥0∞) * potential (hwDecProj (failSetF θ)) σ) (prefixQ pol A θ) initQ)
  have h2 := totalWeight_charge_potential_le (runtimeR m0Q) .instruments
    (hwDecProj (failSetF θ))
    (fun i ↦ if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0)
    (PortCw (S := TPos) (M := SelMem) (hwFixF θ))
    (fun i hi r ↦ runtimeR_commute_hwDecProj m0Q (offHw_failDbF θ) (failSetF θ)
      (fun _ ↦ Iff.rfl) i hi r)
    (fun _ _ _ h ↦ portCw_of_srchOkZ h.choose_spec.1) (prefixQ pol A θ) hK initQ_posSemidef hq
  have h5 := potential_failSetF_le θ
  calc (runtimeR m0Q).totalWeight .instruments reRevQWU (prefixQ pol A θ) initQ
      ≤ (encodingAttemptLimit : ℝ≥0∞) * (K * potential (hwDecProj (failSetF θ)) initQ) :=
        h1'.trans (mul_le_mul_of_nonneg_left h2 zero_le)
    _ ≤ (encodingAttemptLimit : ℝ≥0∞) * (K * (((2 ^ 38 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (1 / 2 ^ 2048))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 zero_le) zero_le
    _ = K * ((encodingAttemptLimit : ℝ≥0∞) * (((2 ^ 38 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (1 / 2 ^ 2048))) := mul_left_comm _ _ _
    _ ≤ K * (2 ^ 200 : ℝ≥0∞)⁻¹ := mul_le_mul_of_nonneg_left reRev_numbersF zero_le

end Quantum.Qrom.Sphincs

end
