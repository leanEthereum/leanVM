module

public import Quantum.Qrom.Sphincs.Multi.Costs.Defs
public import Quantum.Qrom.Sphincs.Multi.Costs.RecUModes
public import Quantum.Qrom.Sphincs.Costs.RecUFail

@[expose] public section

/-!
# The repeated reveals of an unselected key of `n` users: the failed searches

The `n`-user analog of `Quantum.Qrom.Sphincs.Costs.RecUFail`, in the shape of leanXMSS's
`Multi/Costs/RecUFail`. The charge `reRevQWSN` of the challenge prefix (a reveal of a user's key
coordinate already revealed, the key still unselected) adds up to at most `K · 2^-1000` with `K`
classical calls and `n ≤ 2^128` users (`totalWeight_reRevQWSN_le`).

* **The invariant in the decompressed basis** (`FInvFSN`, `fInvFSN_step`, `init_fInvFSN`): no
  empty cell, no hardwired encoding cell of any user, the started keys' coordinates revealed, the
  mode's value the key's signed value, and every user's key whose coordinate is revealed and
  which is unselected has every trial already run on a digest that is no codeword (`RunFailSN`).
* **The repeated reveals**: a repeated reveal with the key unselected lies in the database event
  `failSetFSN θ` (some user's key fails all `2^32` trials of its one search), whose decompressed
  projector commutes with every called port (the programs hardwire cells off every user's
  encoding slots only, `hwFixFSN θ`).
* **Counting** (`frac_failDbFSN_le`): at most `n |Key| (1 - ρ_c)^(2^32)` of the tables fail some
  search, `ρ_c ≥ 2^-14`; with `n ≤ 2^128`, `2^32 · n · 2^38 · 2^-2048 ≤ 2^-1000`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (diagMass totalWeight_const_mul_weight progUpdate)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR NoBot decR liftAns noBot_init
  forallQueries_dec_moded runtimeR_commute_hwDecProj totalWeight_charge_potential_le
  diagMass_le_potential_hwDecProj potential_hwDecProj_init hwOfSets hwOfSets_fst PortCw extCls
  totalWeight_le_of_forallQueries)

attribute [local irreducible] sphincsRom Fin.fintype

/- Instance search for the register's decidable equality exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-! ## Selections -/

/-- A trial read never unselects a key. -/
theorem cwUpdN_eq_noneFSN {i i' : Fin n} {K K' : Key} {z : Qrom.HashDomain} {m : SelMemN n}
    {o : Option PairOut} (h : cwUpdN i K z m o i' K' = none) : m i' K' = none := by
  by_cases hi : i' = i
  · subst hi
    rw [cwUpdN, Function.update_self] at h
    exact cwUpd_eq_noneU h
  · rwa [cwUpdN, Function.update_of_ne hi] at h

/-- A trial read of a codeword digest leaves its key selected. -/
theorem cwUpdN_ne_noneFSN {i : Fin n} {K : Key} {z : Qrom.HashDomain} {m : SelMemN n}
    {w : PairOut} (hv : Quantum.Sphincs.Codeword.Valid (pairDigest w)) :
    cwUpdN i K z m (some w) i K ≠ none := by
  rw [cwUpdN, Function.update_self]
  exact cwUpd_ne_noneF hv

/-! ## The invariant of the failed searches -/

section inv

variable (θ : TValsN n)

/-- The trials of user `i`'s key `K` already run in the mode `μ`: those before the current trial
of its search, all of them otherwise. -/
def doneFSN : ModeSN n → Fin n → Key → ℕ
  | .rest _, _, _ => encodingAttemptLimit
  | .grd _ i K _ j, i', K' => if i = i' ∧ K = K' then j else encodingAttemptLimit

theorem doneFSN_of_rest {μ : ModeSN n} (h : μ.Rest) (i : Fin n) (K : Key) :
    doneFSN μ i K = encodingAttemptLimit := by
  rcases μ with ks | ⟨ks, i', K', m, j⟩
  · rfl
  · have hj : j = encodingAttemptLimit := h
    subst hj
    show (if i' = i ∧ K' = K then encodingAttemptLimit else encodingAttemptLimit) = _
    split_ifs <;> rfl

/-- The mode's search runs on the value its key signs. -/
def ModeOkFSN : ModeSN n → Prop
  | .rest _ => True
  | .grd _ i K m _ => m = (tabOf (userOf θ i)).valuePos (msgPos K)

/-- **The trials already run failed**: every user's key of the signatures whose coordinate is
revealed and which is unselected has its trials already run on digests that are no codewords. -/
def RunFailSN (μ : ModeSN n) (s : RRegSN n (SelMemN n)) : Prop :=
  ∀ i K, InRangeU K → (i, vcoord (msgPos K)) ∈ s.2.2.1 → s.2.2.2 i K = none →
    ∀ j < doneFSN μ i K,
      ¬ Quantum.Sphincs.Codeword.Valid (pairDigest (trialValF (userOf θ i) K j s.1))

/-- **The invariant of the failed searches**, in the decompressed basis. -/
def FInvFSN (μ : ModeSN n) : Set (RRegSN n (SelMemN n)) :=
  {s | NoBot s ∧ EncFreeSN (pkQN θ) s ∧ (∀ k ∈ μ.ks, (k.1, vcoord (msgPos k.2)) ∈ s.2.2.1) ∧
    ModeOkFSN θ μ ∧ RunFailSN θ μ s}

variable {θ}

theorem fInvFSN_rest {μ : ModeSN n} (hμ : μ.Rest) {s : RRegSN n (SelMemN n)}
    (hs : s ∈ FInvFSN θ μ) : s ∈ FInvFSN θ (.rest μ.ks) :=
  ⟨hs.1, hs.2.1, hs.2.2.1, trivial, fun i K hK hl hu j hj ↦
    hs.2.2.2.2 i K hK hl hu j (by rw [doneFSN_of_rest hμ i K]; exact hj)⟩

/-- **A record**: a reveal of a user's key coordinate starts its search with no trial run;
another reveal adds only coordinates of started keys. -/
theorem fInvFSN_rec {μ : ModeSN n} (hμ : μ.Rest) {T : Finset (TPosN n)}
    (hT : keyOfTSN T = none → RevOkSN μ.ks T) {s : RRegSN n (SelMemN n)}
    (hs : s ∈ FInvFSN θ μ) :
    ((s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) : RRegSN n (SelMemN n)) ∈
      FInvFSN θ (revNxSN μ T fun i K ↦ (tabOf (userOf θ i)).valuePos (msgPos K)) := by
  obtain ⟨hnb, hef, hks, -, hl⟩ := hs
  rcases hk : keyOfTSN T with _ | ⟨i₀, K₀⟩
  · rw [revNxSN_none μ hk]
    have hok := hT hk
    refine ⟨hnb, hef, fun k hk' ↦ Finset.mem_union_left _ (hks k hk'), trivial,
      fun i K hK hlab hu j hj ↦ ?_⟩
    have hl1 : (i, vcoord (msgPos K)) ∈ s.2.2.1 := by
      rcases Finset.mem_union.mp hlab with h | h
      · exact h
      · exact hks (i, K) (hok i K hK h)
    exact hl i K hK hl1 hu j (hj.trans_eq (doneFSN_of_rest hμ i K).symm)
  · obtain ⟨hK₀, rfl⟩ := keyOfTSN_spec hk
    rw [revNxSN_atU μ hK₀ i₀]
    refine ⟨hnb, hef, fun k hk' ↦ ?_, rfl, fun i K hK hlab hu j hj ↦ ?_⟩
    · rcases Finset.mem_insert.mp hk' with rfl | h
      · exact Finset.mem_union_right _ (mk_mem_atU _ (Finset.mem_singleton_self _))
      · exact Finset.mem_union_left _ (hks k h)
    · by_cases he : i₀ = i ∧ K₀ = K
      · obtain ⟨rfl, rfl⟩ := he
        have hd : ∀ m, doneFSN (.grd (insert (i₀, K₀) μ.ks) i₀ K₀ m 0) i₀ K₀ = 0 :=
          fun _ ↦ ite_eq_left ⟨rfl, rfl⟩
        exact absurd (hj.trans_eq (hd _)) (Nat.not_lt_zero j)
      · have hd : ∀ m, doneFSN (.grd (insert (i₀, K₀) μ.ks) i₀ K₀ m 0) i K =
            encodingAttemptLimit := fun _ ↦ ite_eq_right he
        have hl1 : (i, vcoord (msgPos K)) ∈ s.2.2.1 := by
          rcases Finset.mem_union.mp hlab with h | h
          · exact h
          · obtain ⟨h1, h2⟩ := mem_atU_iff.mp h
            exact absurd ⟨h1.symm, vcoord_msgPos_injU hK₀ hK (Finset.mem_singleton.mp h2).symm⟩
              he
        exact hl i K hK hl1 hu j ((hj.trans_eq (hd _)).trans_eq (doneFSN_of_rest hμ i K).symm)

/-- **A program of a cell off every user's encoding slots** keeps the invariant: the trial cells
keep their database values. -/
theorem fInvFSN_prog {μ : ModeSN n} (hμ : μ.Rest) {z : Qrom.HashDomain} {a : PairOut}
    (hz : ∀ (i : Fin n) (K : Key), slotOf (pkQN θ i) z ≠ some (.enc K.1 K.2.1 K.2.2))
    {s s' : RRegSN n (SelMemN n)} (hs : s ∈ FInvFSN θ μ) (hp : ProgRelHSN z a s s') :
    s' ∈ FInvFSN θ (.rest μ.ks) := by
  obtain ⟨hnb, hef, hks, -, hl⟩ := hs
  obtain ⟨h2, hnb', h1⟩ := hp
  have hm : s'.2.2 = s.2.2 := (congrArg Prod.snd h2 :)
  have hw : s'.2.1 = progUpdate (.programH z a) s.2.1 := (congrArg Prod.fst h2 :)
  refine ⟨hnb' hnb, fun x hx i K ↦ ?_, fun k hk ↦ by rw [hm]; exact hks k hk, trivial,
    fun i K hK hlab hu j hj ↦ ?_⟩
  · rw [hw] at hx
    have hx' : (Function.update s.2.1.1 z (some a) x).isSome := hx
    by_cases hxz : x = z
    · subst hxz
      exact hz i K
    · rw [Function.update_of_ne hxz] at hx'
      exact hef x hx' i K
  · rw [hm] at hlab hu
    have hc : trialValF (userOf θ i) K j s'.1 = trialValF (userOf θ i) K j s.1 := by
      unfold trialValF
      exact congrArg (fun o : Option PairOut ↦ o.getD 0) (h1 _ fun he ↦ hz i K (by
        rw [← he]
        exact slotOf_trialCell (pkQN θ i) K _ j))
    rw [hc]
    exact hl i K hK hlab hu j (hj.trans_eq (doneFSN_of_rest hμ i K).symm)

/-- **The read of a trial**: a codeword digest selects the key and ends the search; otherwise the
trial failed. -/
theorem fInvFSN_read {ks : Finset (UKeyS n)} {i : Fin n} {K : Key} {m : Digest} {j : ℕ}
    {s : RRegSN n (SelMemN n)} (hs : s ∈ FInvFSN θ (.grd ks i K m j))
    (r : Option PairOut × QMemSN n)
    (hrs : r = liftAns s (.readH (trialCell (tabOf (userOf θ i)).publicSeed K m j)
      (cwUpdN i K (trialCell (tabOf (userOf θ i)).publicSeed K m j)))) :
    readFinHSN s (trialCell (tabOf (userOf θ i)).publicSeed K m j)
        (cwUpdN i K (trialCell (tabOf (userOf θ i)).publicSeed K m j)) ∈
      FInvFSN θ (decNxSN ks i K m j (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1))) := by
  set z := trialCell (tabOf (userOf θ i)).publicSeed K m j with hzdef
  obtain ⟨hnb, hef, hks, hm, hl⟩ := hs
  have hm' : m = (tabOf (userOf θ i)).valuePos (msgPos K) := hm
  have hzs : slotOf (pkQN θ i) z = some (.enc K.1 K.2.1 K.2.2) :=
    slotOf_trialCell (pkQN θ i) K m j
  have hw0 : s.2.1.1 z = none := by
    by_contra h
    exact hef z (Option.ne_none_iff_isSome.mp h) i K hzs
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hnb.1 z)
  have hv : (hwView s.2.1 s.1).1 z = some w := by
    show (s.2.1.1 z).or (s.1.1 z) = some w
    rw [hw0, hw]
    rfl
  have hr1 : r.1 = some w := by
    rw [hrs]
    exact hv
  have hfin : readFinHSN s z (cwUpdN i K z) =
      (s.1, s.2.1, (s.2.2.1, cwUpdN i K z s.2.2.2 (some w))) := by
    unfold readFinHSN
    rw [hv]
  rw [hfin, hr1]
  have hu : ∀ i' K', cwUpdN i K z s.2.2.2 (some w) i' K' = none → s.2.2.2 i' K' = none :=
    fun _ _ h ↦ cwUpdN_eq_noneFSN h
  have hval : trialValF (userOf θ i) K j s.1 = w := by
    unfold trialValF
    rw [← hm', ← hzdef, hw]
    rfl
  generalize hd : TargetSum.decodeDigest (truncateHash ((some w).getD 0).1) = d
  have hd' : TargetSum.decodeDigest (pairDigest w) = d := hd
  rcases d with _ | x
  · show _ ∈ FInvFSN θ (.grd ks i K m (j + 1))
    refine ⟨hnb, hef, hks, hm, fun i' K' hK' hlab hu' j' hj' ↦ ?_⟩
    by_cases hne : i = i' ∧ K = K'
    · obtain ⟨rfl, rfl⟩ := hne
      have h1 : doneFSN (.grd ks i K m (j + 1)) i K = j + 1 := ite_eq_left ⟨rfl, rfl⟩
      rw [h1] at hj'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · have h0 : doneFSN (.grd ks i K m j) i K = j := ite_eq_left ⟨rfl, rfl⟩
        exact hl i K hK' hlab (hu i K hu') j' (hj'.trans_eq h0.symm)
      · show ¬ Quantum.Sphincs.Codeword.Valid (pairDigest (trialValF (userOf θ i) K j' s.1))
        rw [hval]
        exact Quantum.Sphincs.Codeword.decode_eq_none_iff.mp hd'
    · have h1 : doneFSN (.grd ks i K m (j + 1)) i' K' = doneFSN (.grd ks i K m j) i' K' := by
        show (if i = i' ∧ K = K' then j + 1 else encodingAttemptLimit) =
          (if i = i' ∧ K = K' then j else encodingAttemptLimit)
        rw [ite_eq_right hne, ite_eq_right hne]
      exact hl i' K' hK' hlab (hu i' K' hu') j' (hj'.trans_eq h1)
  · show _ ∈ FInvFSN θ (.rest ks)
    refine ⟨hnb, hef, hks, trivial, fun i' K' hK' hlab hu' j' hj' ↦ ?_⟩
    have hvld := Quantum.Sphincs.Codeword.valid_of_decode hd'
    have hne : ¬ (i = i' ∧ K = K') := by
      rintro ⟨rfl, rfl⟩
      exact cwUpdN_ne_noneFSN hvld hu'
    have h1 : doneFSN (.grd ks i K m j) i' K' = encodingAttemptLimit := ite_eq_right hne
    exact hl i' K' hK' hlab (hu i' K' hu') j' (hj'.trans_eq h1.symm)

/-- **Every allowed call keeps the invariant**, in the decompressed basis. -/
theorem fInvFSN_step (μ : ModeSN n) (x : (RSpecSN n (SelMemN n)).Port)
    (r : (RSpecSN n (SelMemN n)).Result x)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n)) ℂ)
    (hok : srchOkZSN (parQSN θ) μ x)
    (hσ : QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n) ↦ m.2)
      (FInvFSN θ μ) σ) :
    QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).Out x × RRegSN n (SelMemN n) ↦ m.2)
      (FInvFSN θ (srchNxZSN θ μ x r))
      (((decR (X := PairOut) (Z := Qrom.HashDomain) (m0SN (n := n))).step x).branch r σ) := by
  rcases x with ((p | c) | c) | T
  · exact (decR_sponge_suppSN m0SN p r _ σ hσ).mono fun s hs ↦ fInvFSN_rest hok hs
  · rcases μ with ks | ⟨ks, i, K, m, j⟩
    · exact hok.elim
    · obtain ⟨-, rfl⟩ := hok
      refine (decR_readH_suppSN m0SN (trialCell (tabOf (userOf θ i)).publicSeed K m j)
        (cwUpdN i K (trialCell (tabOf (userOf θ i)).publicSeed K m j)) r _ σ hσ).mono
          fun s' hs' ↦ ?_
      obtain ⟨s, hs, hrs, rfl⟩ := hs'
      exact fInvFSN_read hs r hrs
  · obtain ⟨hμ, z, a, rfl, hz⟩ := hok
    refine (decR_progH_suppSN m0SN z a r _ σ hσ).mono fun s' hs' ↦ ?_
    obtain ⟨s, hs, hp⟩ := hs'
    exact fInvFSN_prog hμ (fun i ↦ hz (pkQN θ i)) hs hp
  · refine (decR_rec_suppSN m0SN T r _ σ hσ).mono fun s' hs' ↦ ?_
    obtain ⟨s, hs, -, rfl⟩ := hs'
    exact fInvFSN_rec hok.1 hok.2 hs

variable (θ) in
/-- The initial register in the decompressed basis: no empty cell, nothing hardwired, nothing
revealed. -/
theorem init_fInvFSN :
    QuerySupportedOn (fun m : QReg.of Unit × RRegSN n (SelMemN n) ↦ m.2) (FInvFSN θ (.rest ∅))
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (QMemSN n)) initQSN) := by
  have hnb := noBot_init (X := PairOut) (Z := Qrom.HashDomain) (m0SN (n := n))
    ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
  have h0 : QuerySupportedOn (fun m : QReg.of Unit × RRegSN n (SelMemN n) ↦ m.2)
      {s | s.2 = (hwEmpty PairOut Qrom.HashDomain, m0SN)} initQSN := by
    intro m m' hm
    change (((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      (SubState.basis (((Database.empty, Database.empty, Database.empty),
        hwEmpty PairOut Qrom.HashDomain, m0SN) : RRegSN n (SelMemN n))).matrix) m m' ≠ 0 at hm
    rw [kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [SubState.matrix_basis, Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨(congrArg Prod.snd he.1).symm, (congrArg Prod.snd he.2).symm⟩
    · exact absurd rfl h
  have h1 := QuerySupportedOn.conj h0
    (K := (1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      compressReg PairOut Qrom.HashDomain (QMemSN n))
    (q' := fun m : QReg.of Unit × RRegSN n (SelMemN n) ↦ m.2)
    (S' := {s | s.2 = (hwEmpty PairOut Qrom.HashDomain, m0SN)})
    fun m' m hK hm ↦ by
      have hK' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
      rw [compressReg, kroneckerMap_apply] at hK'
      have he : m'.2.2 = m.2.2 := by
        by_contra hne
        exact right_ne_zero_of_mul hK' (Matrix.one_apply_ne hne)
      show m'.2.2 = _
      rw [he]
      exact hm
  have hmem : ∀ s : RRegSN n (SelMemN n), NoBot s →
      s.2 = (hwEmpty PairOut Qrom.HashDomain, m0SN) → s ∈ FInvFSN θ (.rest ∅) :=
    fun s hs he ↦ by
      refine ⟨hs, fun x hx ↦ ?_, fun k hk ↦ absurd hk (Finset.notMem_empty _), trivial,
        fun _ _ _ hl _ _ _ ↦ ?_⟩
      · rw [he] at hx
        exact absurd hx (by simp [hwEmpty])
      · rw [he] at hl
        exact absurd hl (Finset.notMem_empty _)
  intro a b hab
  exact ⟨hmem _ (hnb a b hab).1 (h1 a b hab).1, hmem _ (hnb a b hab).2 (h1 a b hab).2⟩

end inv

/-! ## The failure event -/

section fail

variable (θ : TValsN n)

/-- **Some search fails on the databases**: some user's key all of whose `2^32` trials (on the
value it signs) read pairs whose digests are no codewords. -/
def FailDbFSN (D : DbReg PairOut Qrom.HashDomain) : Prop :=
  ∃ i, FailDbF (userOf θ i) D

/-- The registers whose databases fail a search. -/
def failSetFSN : Set (RRegSN n (SelMemN n)) := {s | FailDbFSN θ s.1}

/-- `failSetFSN`, decided classically. -/
noncomputable instance instDecidableFailSetFSN : DecidablePred (· ∈ failSetFSN θ) :=
  Classical.decPred _

/-- The static hardwiring off the trial cells: every `h`-cell off every user's encoding slots,
every `k`, `k'` cell. -/
noncomputable def hwFixFSN : Hw PairOut Qrom.HashDomain :=
  hwOfSets {z : Qrom.HashDomain | ∀ (i : Fin n) (K : Key),
    slotOf (pkQN θ i) z ≠ some (.enc K.1 K.2.1 K.2.2)} Set.univ Set.univ

theorem hwFixFSN_trial (i : Fin n) (K : Key) (m : Digest) (j : ℕ) :
    (hwFixFSN θ).1 (trialCell (tabOf (userOf θ i)).publicSeed K m j) = none := by
  by_contra h
  exact (hwOfSets_fst.mp h) i K (slotOf_trialCell (pkQN θ i) K m j)

/-- `FailDbFSN` reads the trial cells only, off `hwFixFSN θ`. -/
theorem offHw_failDbFSN : OffHw (hwFixFSN θ) (FailDbFSN θ) := by
  intro D D' h1 _ _
  have hc : ∀ i K j, trialValF (userOf θ i) K j D = trialValF (userOf θ i) K j D' :=
    fun i K j ↦ by
      unfold trialValF
      exact congrArg (fun o : Option PairOut ↦ o.getD 0) (h1 _ (hwFixFSN_trial θ i K _ j))
  exact ⟨fun ⟨i, K, h⟩ ↦ ⟨i, K, fun j hj ↦ by rw [← hc]; exact h j hj⟩,
    fun ⟨i, K, h⟩ ↦ ⟨i, K, fun j hj ↦ by rw [hc]; exact h j hj⟩⟩

variable {θ}

theorem portCw_of_srchOkZSN {μ : ModeSN n} {x : (RSpecSN n (SelMemN n)).Port}
    (h : srchOkZSN (parQSN θ) μ x) :
    PortCw (S := TPosN n) (M := SelMemN n) (hwFixFSN θ) x := by
  rcases x with ((p | c) | c) | T
  · trivial
  · trivial
  · obtain ⟨-, z, a, rfl, hz⟩ := h
    exact hwOfSets_fst.mpr fun i ↦ hz (pkQN θ i)
  · trivial

/-- **A repeated reveal with the key unselected is in the failure event**: at a record call
allowed by a rest mode, on the invariant, a revealed user's key of the signatures that is
unselected has run all its trials. -/
theorem reRevQWSN_le_charge (x : (RSpecSN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n)) ℂ)
    (hσ : σ.PosSemidef)
    (h : ∃ μ, srchOkZSN (parQSN θ) μ x ∧
      QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n) ↦ m.2)
        (FInvFSN θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpecSN n (SelMemN n)).In x)
          ((RSpecSN n (SelMemN n)).In x) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain (QMemSN n)) σ)) :
    reRevQWSN x σ ≤ (encodingAttemptLimit : ℝ≥0∞) *
      (((if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) x then 1
        else 0 : ℕ) : ℝ≥0∞) * potential (hwDecProj (failSetFSN θ)) σ) := by
  rcases x with ((p | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · obtain ⟨μ, ⟨hrest, -⟩, hS⟩ := h
    rcases hT : keyOfTSN T with _ | ⟨i, K⟩
    · simp only [reRevQWSN, hT]
      exact zero_le
    · simp only [reRevQWSN, hT]
      have h1 : ((if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n))
          (.inr T) then 1 else 0 : ℕ) : ℝ≥0∞) = 1 := by simp [extCls]
      rw [h1, one_mul]
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hK := (keyOfTSN_spec hT).1
      classical
      exact diagMass_le_potential_hwDecProj (fun b : Hw PairOut Qrom.HashDomain × QMemSN n ↦
        (i, vcoord (msgPos K)) ∈ b.2.1 ∧ b.2.2 i K = none) (failSetFSN θ) _ hσ hS
          fun s hs hP ↦ ⟨i, K, fun j hj ↦ hs.2.2.2.2 i K hK hP.1 hP.2 j
            (hj.trans_eq (doneFSN_of_rest hrest i K).symm)⟩

end fail

/-! ## Counting the failed searches -/

section count

/-- The trial cells of the search of user `i`'s key on the value it signs. -/
def failCellFSN (θ : TValsN n) (k : Fin n × Key) (j : ℕ) : Qrom.HashDomain :=
  failCellF (userOf θ k.1) k.2 j

theorem card_userKey_leFSN : Fintype.card (Fin n × Key) ≤ n * 2 ^ 38 := by
  rw [Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_left n card_key_leF

open scoped Classical in
/-- **The failure fraction**: `n |Key| · (1 - ρ_c)^(2^32)` over the tables. -/
theorem frac_failDbFSN_le (θ : TValsN n) :
    ((Finset.univ.filter fun t ↦ FailDbFSN θ (ofFunDbs t)).card : ℝ≥0∞) /
      Fintype.card ((Qrom.HashDomain → PairOut) × (PairOut → Qrom.HashDomain) ×
        (PairOut → Qrom.HashDomain)) ≤
      Fintype.card (Fin n × Key) * ((((Finset.univ.filter fun ω : PairOut ↦
        ¬ Quantum.Sphincs.Codeword.Valid (pairDigest ω)).card ^ encodingAttemptLimit : ℕ) :
          ℝ≥0∞) / ((Fintype.card PairOut ^ encodingAttemptLimit : ℕ) : ℝ≥0∞)) :=
  Quantum.Qrom.Xmss.frac_union_fail_le (failCellFSN θ)
    (fun ω : PairOut ↦ ¬ Quantum.Sphincs.Codeword.Valid (pairDigest ω))
    encodingAttemptLimit (fun k ↦ failCellF_inj (userOf θ k.1) k.2) _
    fun _ ⟨i, K, ht⟩ ↦ ⟨(i, K), ht⟩

end count

/-! ## The bound -/

set_option exponentiation.threshold 4096 in
/-- The numbers: `2^32 · n · 2^38 · 2^-2048 ≤ 2^-1000` for `n ≤ 2^128`. -/
theorem reRevSN_numbers_le (hn : n ≤ 2 ^ 128) :
    (encodingAttemptLimit : ℝ≥0∞) * (((n * 2 ^ 38 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (1 / 2 ^ 2048)) ≤ (2 ^ 1000 : ℝ≥0∞)⁻¹ := by
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Nat.mul_le_mul_right (2 ^ 38) hn)) zero_le) zero_le) ?_
  rw [show (encodingAttemptLimit : ℝ≥0∞) = ENNReal.ofReal (2 ^ 32) by
      rw [encodingAttemptLimit, Nat.cast_pow, Nat.cast_ofNat, ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    show (2 ^ 1000 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ 1000) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

open scoped Classical in
/-- **The initial potential of the failure event**: at most `n · 2^38 · 2^-2048`. -/
theorem potential_failSetFSN_le (θ : TValsN n) :
    potential (hwDecProj (failSetFSN θ)) (initQSN (n := n)) ≤
      ((n * 2 ^ 38 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 2048) := by
  have h3 : potential (hwDecProj (failSetFSN θ)) (initQSN (n := n)) ≤
      ((Finset.univ.filter fun t ↦ FailDbFSN θ (ofFunDbs t)).card : ℝ≥0∞) /
        Fintype.card ((Qrom.HashDomain → PairOut) × (PairOut → Qrom.HashDomain) ×
          (PairOut → Qrom.HashDomain)) := by
    refine (le_of_eq (potential_hwDecProj_init (m0SN (n := n)) (failSetFSN θ) (FailDbFSN θ)
      (fun _ ↦ Iff.rfl) ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
      (SubState.basis _).posSemidef)).trans ?_
    exact (mul_le_mul' (ENNReal.ofReal_le_one.mpr (SubState.basis _).trace_re_le_one)
      le_rfl).trans_eq (one_mul _)
  exact (h3.trans (frac_failDbFSN_le θ)).trans
    (mul_le_mul' (Nat.cast_le.mpr card_userKey_leFSN) pow_not_codeword_div_leF)

/-- **The repeated-reveal charges of the `n`-user challenge prefix**: with at most `K` classical
calls and `n ≤ 2^128` users, at most `K · 2^-1000`. -/
theorem totalWeight_reRevQWSN_le (A : MuAdversaryS n) (θ : TValsN n) (hn : n ≤ 2 ^ 128)
    {K : ℕ} (hK : IFreeM.IsChargeBound (prefixQSN (strPolN n) A θ) (portCharge fun x ↦
      if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) x then 1
        else 0) K) :
    (runtimeR (m0SN (n := n))).totalWeight .instruments reRevQWSN (prefixQSN (strPolN n) A θ)
      initQSN ≤ K * (2 ^ 1000 : ℝ≥0∞)⁻¹ := by
  have hq := forallQueries_dec_moded (m0SN (n := n)) (FInvFSN θ)
    (fun μ x r σ hok hσ ↦ fInvFSN_step μ x r σ hok hσ) LocalSig.Interp.instruments
    (prefixQSN (strPolN n) A θ) (.rest ∅) (modedP_prefixQSN (fun _ ↦ noVal_strPol) A θ)
    (init_fInvFSN θ)
  have h1 := totalWeight_le_of_forallQueries (runtimeR (m0SN (n := n))) .instruments
    (fun x σ ↦ ∃ μ, srchOkZSN (parQSN θ) μ x ∧
      QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n) ↦ m.2)
        (FInvFSN θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpecSN n (SelMemN n)).In x)
          ((RSpecSN n (SelMemN n)).In x) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain (QMemSN n)) σ)) (fun _ _ _ h ↦ h)
    (w' := fun x σ ↦ (encodingAttemptLimit : ℝ≥0∞) *
      (((if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) x then 1
        else 0 : ℕ) : ℝ≥0∞) * potential (hwDecProj (failSetFSN θ)) σ))
    (fun x σ hσ hok ↦ reRevQWSN_le_charge x σ hσ hok) (prefixQSN (strPolN n) A θ)
    initQSN_posSemidef hq
  have h1' := h1.trans_eq (totalWeight_const_mul_weight (runtimeR (m0SN (n := n))) .instruments
    (encodingAttemptLimit : ℝ≥0∞) (fun x σ ↦
      ((if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) x then 1
        else 0 : ℕ) : ℝ≥0∞) * potential (hwDecProj (failSetFSN θ)) σ)
    (prefixQSN (strPolN n) A θ) initQSN)
  have h2 := totalWeight_charge_potential_le (runtimeR (m0SN (n := n))) .instruments
    (hwDecProj (failSetFSN θ))
    (fun x ↦ if extCls PairOut Qrom.HashDomain (QMemSN n) (recSpec (TPosN n) (SelMemN n)) x
      then 1 else 0)
    (PortCw (S := TPosN n) (M := SelMemN n) (hwFixFSN θ))
    (fun x hx r ↦ runtimeR_commute_hwDecProj (m0SN (n := n)) (offHw_failDbFSN θ)
      (failSetFSN θ) (fun _ ↦ Iff.rfl) x hx r)
    (fun _ _ _ h ↦ portCw_of_srchOkZSN h.choose_spec.1) (prefixQSN (strPolN n) A θ) hK
    initQSN_posSemidef hq
  have h5 := potential_failSetFSN_le θ
  calc (runtimeR (m0SN (n := n))).totalWeight .instruments reRevQWSN
        (prefixQSN (strPolN n) A θ) initQSN
      ≤ (encodingAttemptLimit : ℝ≥0∞) * (K * potential (hwDecProj (failSetFSN θ)) initQSN) :=
        h1'.trans (mul_le_mul_of_nonneg_left h2 zero_le)
    _ ≤ (encodingAttemptLimit : ℝ≥0∞) * (K * (((n * 2 ^ 38 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (1 / 2 ^ 2048))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 zero_le) zero_le
    _ = K * ((encodingAttemptLimit : ℝ≥0∞) * (((n * 2 ^ 38 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (1 / 2 ^ 2048))) := mul_left_comm _ _ _
    _ ≤ K * (2 ^ 1000 : ℝ≥0∞)⁻¹ := mul_le_mul_of_nonneg_left (reRevSN_numbers_le hn) zero_le

end Quantum.Qrom.Sphincs.Multi

end
