module

public import Quantum.Qrom.Xmss.Multi.Costs.RecUModes
public import Quantum.Qrom.Xmss.Costs.RecUFail

@[expose] public section

/-!
# The repeated reveals of an unselected key of `n` users: the failed searches

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.RecUFail`. The charge `reRevQWN` of the
challenge prefix (a reveal of a user's randomizer base already revealed, its key still
unselected) adds up to at most `K · 2^-1000` with `K` classical calls and `n ≤ 2^128` users
(`totalWeight_reRevQWN_le`).

* **The invariant in the decompressed basis** (`FInvFN`, `fInvFN_step`, `init_fInvFN`): no empty
  cell, no hardwired message cell, the mode's base is the hidden one, and every revealed
  randomizer position `(i, loC rnd)` whose key `(i, l, e)` is unselected has every trial already
  run on a digest that is no codeword (`RunFailN`), on the decompressed `h`-database.
* **The repeated reveals** (`reRevQWN_le_charge`): a repeated reveal with the key unselected lies
  in the database event `failSetFN` (some user's randomizer position fails all `2^32` trials),
  whose decompressed projector commutes with every called port (the programs hardwire
  non-message cells only, `hwFixF`).
* **Counting** (`frac_failDbFN_le`): at most `n (2^288 + 2^160) (1 - ρ_c)^(2^32)` of the tables
  fail some search.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (diagMass totalWeight_const_mul_weight progUpdate)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR NoBot decR liftAns noBot_init
  forallQueries_dec_moded runtimeR_commute_hwDecProj totalWeight_charge_potential_le
  diagMass_le_potential_hwDecProj potential_hwDecProj_init natCast_pow_sub_div_le_exp
  exp_neg_trials_le PortCw extCls totalWeight_le_of_forallQueries)

attribute [local irreducible] xmssRom

variable {n : ℕ}

/-! ## Selections -/

/-- A trial read never unselects a key. -/
theorem cwUpdN_eq_noneF {i i' : Fin n} {l l' : Layer} {e e' : KeyIndex} {z : HashDomain}
    {m : SelMemN n} {o : Option HashOutput} (h : cwUpdN i l e z m o i' l' e' = none) :
    m i' l' e' = none := by
  by_cases hi : i' = i
  · subst hi
    rw [cwUpdN, Function.update_self] at h
    exact cwUpd_eq_noneF h
  · rwa [cwUpdN, Function.update_of_ne hi] at h

/-- A trial read of a codeword digest leaves its key selected. -/
theorem cwUpdN_ne_noneF {i : Fin n} {l : Layer} {e : KeyIndex} {z : HashDomain} {m : SelMemN n}
    {w : HashOutput} (hv : Codeword.Valid (truncateHash w)) :
    cwUpdN i l e z m (some w) i l e ≠ none := by
  rw [cwUpdN, Function.update_self]
  exact cwUpd_ne_noneF hv

theorem hwNone_of_msgFreeFN {s : RRegN n (SelMemN n)} (hM : MsgFreeN s) {z : HashDomain}
    {l : Layer} {e : KeyIndex} (hz : slotOf z = some (.msg l e)) : s.2.1.1 z = none := by
  by_contra h
  exact hM z (Option.ne_none_iff_isSome.mp h) l e hz

/-! ## The invariant of the failed searches -/

section inv

variable (P : Fin n → PublicParameter) (θ : HPosN n → Digest)

/-- The trials of user `i`'s `rnd` already run in the mode `μ`: those before the current trial
of its search, all of them otherwise. -/
def doneFN : SrchModeN n → Fin n → Pos → ℕ
  | .free, _, _ => randomizerAttemptLimit
  | .grd i r _ j, i', rnd => if i = i' ∧ r = rnd then j else randomizerAttemptLimit

theorem doneFN_of_rest {μ : SrchModeN n} (h : μ.Rest) (i : Fin n) (rnd : Pos) :
    doneFN μ i rnd = randomizerAttemptLimit := by
  rcases μ with _ | ⟨i', r, b, j⟩
  · rfl
  · have hj : j = randomizerAttemptLimit := h
    subst hj
    show (if i' = i ∧ r = rnd then randomizerAttemptLimit else randomizerAttemptLimit) = _
    split_ifs <;> rfl

/-- The `h`-value of trial `j` of the search of user `i`'s `rnd` (key `(l, e)`, message `msg`,
parameter `P i`) from its hidden base, on the databases `D`. -/
def trialValFN (i : Fin n) (l : Layer) (e : KeyIndex) (msg : MsgBytes) (rnd : Pos) (j : ℕ)
    (D : DbReg HashOutput HashDomain) : HashOutput :=
  (D.1 (trialCell (P i) l e msg (θ (i, loC rnd)) j)).getD 0

/-- The mode's search runs from the hidden base. -/
def ModeOkFN : SrchModeN n → Prop
  | .free => True
  | .grd i rnd b _ => b = θ (i, loC rnd)

/-- **The trials already run failed**: every revealed randomizer position whose key is unselected
has its trials already run on digests that are no codewords. -/
def RunFailN (μ : SrchModeN n) (s : RRegN n (SelMemN n)) : Prop :=
  ∀ i rnd l e msg, rndLab rnd = some (l, e, msg) → (i, loC rnd) ∈ s.2.2.1 →
    s.2.2.2 i l e = none →
      ∀ j < doneFN μ i rnd, ¬ Codeword.Valid (truncateHash (trialValFN P θ i l e msg rnd j s.1))

/-- **The invariant of the failed searches**, in the decompressed basis. -/
def FInvFN (μ : SrchModeN n) : Set (RRegN n (SelMemN n)) :=
  {s | NoBot s ∧ MsgFreeN s ∧ ModeOkFN θ μ ∧ RunFailN P θ μ s}

variable {P θ}

theorem fInvFN_free_of_rest {μ : SrchModeN n} (hμ : μ.Rest) {s : RRegN n (SelMemN n)}
    (hs : s ∈ FInvFN P θ μ) : s ∈ FInvFN P θ .free :=
  ⟨hs.1, hs.2.1, trivial, fun i rnd l e msg hr hl hu j hj ↦
    hs.2.2.2 i rnd l e msg hr hl hu j (by rw [doneFN_of_rest hμ i rnd]; exact hj)⟩

/-- **A record**: a reveal of one randomizer base starts its search with no trial run; a reveal
of no randomizer base reveals no randomizer position. -/
theorem fInvFN_rec {μ : SrchModeN n} (hμ : μ.Rest) {T : Finset (HPosN n)} (hT : RevOkQN T)
    {s : RRegN n (SelMemN n)} (hs : s ∈ FInvFN P θ μ) :
    ((s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) : RRegN n (SelMemN n)) ∈
      FInvFN P θ (revNxQN T fun i rnd ↦ θ (i, loC rnd)) := by
  obtain ⟨hnb, hmf, -, hl⟩ := hs
  rcases hT with ⟨i₀, rnd₀, hr₀, rfl⟩ | hT
  · rw [revNxQN_atU hr₀ i₀]
    refine ⟨hnb, hmf, rfl, fun i rnd l e msg hr hlab hu j hj ↦ ?_⟩
    by_cases he : i₀ = i ∧ rnd₀ = rnd
    · obtain ⟨rfl, rfl⟩ := he
      have hd : doneFN (.grd i₀ rnd₀ (θ (i₀, loC rnd₀)) 0) i₀ rnd₀ = 0 :=
        ite_eq_left ⟨rfl, rfl⟩
      rw [hd] at hj
      exact absurd hj (Nat.not_lt_zero j)
    · have hd : doneFN (.grd i₀ rnd₀ (θ (i₀, loC rnd₀)) 0) i rnd = randomizerAttemptLimit :=
        ite_eq_right he
      have hl1 : (i, loC rnd) ∈ s.2.2.1 := by
        rcases Finset.mem_union.mp hlab with h | h
        · exact h
        · obtain ⟨h1, h2⟩ := mem_atU.mp h
          exact absurd ⟨h1.symm, (loC_injective (Finset.mem_singleton.mp h2)).symm⟩ he
      exact hl i rnd l e msg hr hl1 hu j (by rw [doneFN_of_rest hμ i rnd, ← hd]; exact hj)
  · rw [revNxQN_none hT]
    refine ⟨hnb, hmf, trivial, fun i rnd l e msg hr hlab hu j hj ↦ ?_⟩
    have hl1 : (i, loC rnd) ∈ s.2.2.1 := by
      rcases Finset.mem_union.mp hlab with h | h
      · exact h
      · exact absurd (rndC_loC (by rw [hr]; rfl)) (hT _ h)
    exact hl i rnd l e msg hr hl1 hu j (by rw [doneFN_of_rest hμ i rnd]; exact hj)

/-- **A program of a non-message cell** keeps the invariant: the trial cells keep their
database values. -/
theorem fInvFN_prog {μ : SrchModeN n} (hμ : μ.Rest) {z : HashDomain} {a : HashOutput}
    (hz : ∀ l e, slotOf z ≠ some (.msg l e)) {s s' : RRegN n (SelMemN n)}
    (hs : s ∈ FInvFN P θ μ) (hp : ProgRelHN z a s s') : s' ∈ FInvFN P θ .free := by
  obtain ⟨hnb, hmf, -, hl⟩ := hs
  obtain ⟨h2, hnb', h1⟩ := hp
  have hm : s'.2.2 = s.2.2 := (congrArg Prod.snd h2 :)
  have hw : s'.2.1 = progUpdate (.programH z a) s.2.1 := (congrArg Prod.fst h2 :)
  refine ⟨hnb' hnb, fun x hx l e ↦ ?_, trivial, fun i rnd l e msg hr hlab hu j hj ↦ ?_⟩
  · rw [hw] at hx
    have hx' : (Function.update s.2.1.1 z (some a) x).isSome := hx
    by_cases hxz : x = z
    · subst hxz
      exact hz l e
    · rw [Function.update_of_ne hxz] at hx'
      exact hmf x hx' l e
  · rw [hm] at hlab hu
    have hc : trialValFN P θ i l e msg rnd j s'.1 = trialValFN P θ i l e msg rnd j s.1 := by
      unfold trialValFN
      exact congrArg (fun o : Option HashOutput ↦ o.getD 0)
        (h1 (trialCell (P i) l e msg (θ (i, loC rnd)) j) fun he ↦
          hz l e (he ▸ slotOf_trialCellF (P i) l e msg (θ (i, loC rnd)) j))
    rw [hc]
    exact hl i rnd l e msg hr hlab hu j (by rw [doneFN_of_rest hμ i rnd]; exact hj)

theorem srchRdNxN_trial_some {i : Fin n} {rnd : Pos} {b : Randomizer} {j : ℕ} {z : HashDomain}
    {κ : UKey n} {r : Option HashOutput × QMemN n} {x : Encoding}
    (h : Codeword.decode (truncateHash (r.1.getD 0)) = some x) :
    srchRdNxN (.grd i rnd b j) (trialReadN z κ) r = .free := by
  show (match Codeword.decode (truncateHash (r.1.getD 0)) with
    | some _ => SrchModeN.free
    | none => SrchModeN.grd i rnd b (j + 1)) = _
  rw [h]

theorem srchRdNxN_trial_none {i : Fin n} {rnd : Pos} {b : Randomizer} {j : ℕ} {z : HashDomain}
    {κ : UKey n} {r : Option HashOutput × QMemN n}
    (h : Codeword.decode (truncateHash (r.1.getD 0)) = none) :
    srchRdNxN (.grd i rnd b j) (trialReadN z κ) r = .grd i rnd b (j + 1) := by
  show (match Codeword.decode (truncateHash (r.1.getD 0)) with
    | some _ => SrchModeN.free
    | none => SrchModeN.grd i rnd b (j + 1)) = _
  rw [h]

/-- **The read of a trial**: a codeword digest selects the key and ends the search; otherwise the
trial failed. -/
theorem fInvFN_read {i : Fin n} {rnd : Pos} {b : Randomizer} {j : ℕ} {l : Layer} {e : KeyIndex}
    {msg : MsgBytes} (hr : rndLab rnd = some (l, e, msg)) {s : RRegN n (SelMemN n)}
    (hs : s ∈ FInvFN P θ (.grd i rnd b j)) (r : Option HashOutput × QMemN n)
    (hrs : r = liftAns s (.readH (trialCell (P i) l e msg b j)
      (cwUpdN i l e (trialCell (P i) l e msg b j)))) :
    readFinHN s (trialCell (P i) l e msg b j) (cwUpdN i l e (trialCell (P i) l e msg b j)) ∈
      FInvFN P θ (srchRdNxN (.grd i rnd b j) (trialReadN (trialCell (P i) l e msg b j) (i, l, e))
        r) := by
  set z := trialCell (P i) l e msg b j with hzdef
  obtain ⟨hnb, hmf, hb, hl⟩ := hs
  have hb' : b = θ (i, loC rnd) := hb
  have hzm : slotOf z = some (.msg l e) := slotOf_trialCellF _ l e msg b j
  have hw0 : s.2.1.1 z = none := hwNone_of_msgFreeFN hmf hzm
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hnb.1 z)
  have hv : (hwView s.2.1 s.1).1 z = some w := by
    show (s.2.1.1 z).or (s.1.1 z) = some w
    rw [hw0, hw]
    rfl
  have hr1 : r.1 = some w := by
    rw [hrs]
    exact hv
  have hfin : readFinHN s z (cwUpdN i l e z) =
      (s.1, s.2.1, (s.2.2.1, cwUpdN i l e z s.2.2.2 (some w))) := by
    unfold readFinHN
    rw [hv]
  rw [hfin]
  have hu : ∀ i' l' e', cwUpdN i l e z s.2.2.2 (some w) i' l' e' = none →
      s.2.2.2 i' l' e' = none :=
    fun _ _ _ h ↦ cwUpdN_eq_noneF h
  have hrj : r.1.getD 0 = w := by rw [hr1]; rfl
  rcases hd : Codeword.decode (truncateHash w) with _ | x
  · rw [srchRdNxN_trial_none (by rw [hrj]; exact hd)]
    refine ⟨hnb, hmf, hb, fun i' rnd' l' e' msg' hr' hlab hu' j' hj' ↦ ?_⟩
    by_cases hne : i = i' ∧ rnd = rnd'
    · obtain ⟨rfl, rfl⟩ := hne
      rw [hr] at hr'
      obtain ⟨rfl, rfl, rfl⟩ : l = l' ∧ e = e' ∧ msg = msg' := by
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hr')
        exact ⟨h1, Prod.mk.inj h2⟩
      have h1 : doneFN (.grd i rnd b (j + 1)) i rnd = j + 1 := ite_eq_left ⟨rfl, rfl⟩
      rw [h1] at hj'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · have h0 : doneFN (.grd i rnd b j) i rnd = j := ite_eq_left ⟨rfl, rfl⟩
        exact hl i rnd l e msg hr hlab (hu i l e hu') j' (by rw [h0]; exact hj')
      · have hval : trialValFN P θ i l e msg rnd j' s.1 = w := by
          unfold trialValFN
          rw [← hb', ← hzdef, hw]
          rfl
        show ¬ Codeword.Valid (truncateHash (trialValFN P θ i l e msg rnd j' s.1))
        rw [hval]
        exact not_valid_of_decode hd
    · have h1 : doneFN (.grd i rnd b (j + 1)) i' rnd' = doneFN (.grd i rnd b j) i' rnd' := by
        show (if i = i' ∧ rnd = rnd' then j + 1 else randomizerAttemptLimit) =
          (if i = i' ∧ rnd = rnd' then j else randomizerAttemptLimit)
        rw [ite_eq_right hne, ite_eq_right hne]
      exact hl i' rnd' l' e' msg' hr' hlab (hu i' l' e' hu') j' (by rw [← h1]; exact hj')
  · rw [srchRdNxN_trial_some (by rw [hrj]; exact hd)]
    refine ⟨hnb, hmf, trivial, fun i' rnd' l' e' msg' hr' hlab hu' j' hj' ↦ ?_⟩
    have hvld := valid_of_decode hd
    have hne : ¬ (i = i' ∧ rnd = rnd') := by
      rintro ⟨rfl, rfl⟩
      rw [hr] at hr'
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hr')
      obtain ⟨h3, -⟩ := Prod.mk.inj h2
      subst h1 h3
      exact cwUpdN_ne_noneF hvld hu'
    have h1 : doneFN (.grd i rnd b j) i' rnd' = randomizerAttemptLimit := ite_eq_right hne
    exact hl i' rnd' l' e' msg' hr' hlab (hu i' l' e' hu') j' (by rw [h1]; exact hj')

/-- **Every allowed call keeps the invariant**, in the decompressed basis. -/
theorem fInvFN_step (μ : SrchModeN n) (i : (RSpecN n (SelMemN n)).Port)
    (r : (RSpecN n (SelMemN n)).Result i)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) ℂ)
    (hok : srchOkZN P μ i)
    (hσ : QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦ m.2)
      (FInvFN P θ μ) σ) :
    QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).Out i × RRegN n (SelMemN n) ↦ m.2)
      (FInvFN P θ (srchNxZN θ μ i r))
      (((decR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step i).branch r σ) := by
  rcases i with ((p | c) | c) | T
  · exact (decR_sponge_suppN m0N p r _ σ hσ).mono fun s hs ↦ fInvFN_free_of_rest hok hs
  · rcases μ with _ | ⟨i, rnd, b, j⟩
    · exact hok.elim
    · obtain ⟨-, l, e, msg, hr, rfl⟩ := hok
      refine (decR_readH_suppN m0N (trialCell (P i) l e msg b j)
        (cwUpdN i l e (trialCell (P i) l e msg b j)) r _ σ hσ).mono fun s' hs' ↦ ?_
      obtain ⟨s, hs, hrs, rfl⟩ := hs'
      exact fInvFN_read hr hs r hrs
  · obtain ⟨hμ, z, a, rfl, hz⟩ := hok
    refine (decR_progH_suppN m0N z a r _ σ hσ).mono fun s' hs' ↦ ?_
    obtain ⟨s, hs, hp⟩ := hs'
    exact fInvFN_prog hμ hz hs hp
  · refine (decR_rec_suppN m0N T r _ σ hσ).mono fun s' hs' ↦ ?_
    obtain ⟨s, hs, -, rfl⟩ := hs'
    exact fInvFN_rec hok.1 hok.2 hs

variable (P θ) in
set_option synthInstance.maxSize 2000 in
/-- The initial register in the decompressed basis: no empty cell, nothing hardwired, nothing
revealed. -/
theorem init_fInvFN :
    QuerySupportedOn (fun m : QReg.of Unit × RRegN n (SelMemN n) ↦ m.2) (FInvFN P θ .free)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (QMemN n)) initQN) := by
  have hnb := noBot_init (X := HashOutput) (Z := HashDomain) (m0N (n := n))
    ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
  have h0 : QuerySupportedOn (fun m : QReg.of Unit × RRegN n (SelMemN n) ↦ m.2)
      {s | s.2 = (hwEmpty HashOutput HashDomain, m0N)} initQN := by
    intro m m' hm
    change (((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      (SubState.basis (((Database.empty, Database.empty, Database.empty),
        hwEmpty HashOutput HashDomain, m0N) : RRegN n (SelMemN n))).matrix) m m' ≠ 0 at hm
    rw [kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [SubState.matrix_basis, Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨(congrArg Prod.snd he.1).symm, (congrArg Prod.snd he.2).symm⟩
    · exact absurd rfl h
  have h1 := QuerySupportedOn.conj h0
    (K := (1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      compressReg HashOutput HashDomain (QMemN n))
    (q' := fun m : QReg.of Unit × RRegN n (SelMemN n) ↦ m.2)
    (S' := {s | s.2 = (hwEmpty HashOutput HashDomain, m0N)})
    fun m' m hK hm ↦ by
      have hK' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
      rw [compressReg, kroneckerMap_apply] at hK'
      have he : m'.2.2 = m.2.2 := by
        by_contra hne
        exact right_ne_zero_of_mul hK' (Matrix.one_apply_ne hne)
      show m'.2.2 = _
      rw [he]
      exact hm
  have hmem : ∀ s : RRegN n (SelMemN n), NoBot s →
      s.2 = (hwEmpty HashOutput HashDomain, m0N) → s ∈ FInvFN P θ .free := fun s hs he ↦ by
    refine ⟨hs, fun x hx ↦ ?_, trivial, fun _ _ _ _ _ _ hl _ _ _ ↦ ?_⟩
    · rw [he] at hx
      exact absurd hx (by simp [hwEmpty])
    · rw [he] at hl
      exact absurd hl (Finset.notMem_empty _)
  intro a b hab
  exact ⟨hmem _ (hnb a b hab).1 (h1 a b hab).1, hmem _ (hnb a b hab).2 (h1 a b hab).2⟩

end inv

/-! ## The failure event -/

section fail

variable (P : Fin n → PublicParameter) (θ : HPosN n → Digest)

/-- **Some search fails on the databases**: a user's randomizer position all of whose `2^32`
trials from its hidden base read digests that are no codewords. -/
def FailDbFN (D : DbReg HashOutput HashDomain) : Prop :=
  ∃ i rnd l e msg, rndLab rnd = some (l, e, msg) ∧
    ∀ j < randomizerAttemptLimit,
      ¬ Codeword.Valid (truncateHash (trialValFN P θ i l e msg rnd j D))

/-- The registers whose databases fail a search. -/
def failSetFN : Set (RRegN n (SelMemN n)) := {s | FailDbFN P θ s.1}

/-- `failSetFN`, decided classically. -/
noncomputable instance instDecidableFailSetFN : DecidablePred (· ∈ failSetFN P θ) :=
  Classical.decPred _

/-- `FailDbFN` reads the trial cells only, off `hwFixF`. -/
theorem offHw_failDbFN : OffHw hwFixF (FailDbFN P θ) := by
  intro D D' h1 _ _
  have hc : ∀ i l e msg rnd j,
      trialValFN P θ i l e msg rnd j D = trialValFN P θ i l e msg rnd j D' :=
    fun i l e msg rnd j ↦ by
      unfold trialValFN
      exact congrArg (fun o : Option HashOutput ↦ o.getD 0)
        (h1 (trialCell (P i) l e msg (θ (i, loC rnd)) j) (hwFixF_trial _ l e msg _ j))
  exact ⟨fun ⟨i, rnd, l, e, msg, hr, h⟩ ↦ ⟨i, rnd, l, e, msg, hr, fun j hj ↦ by
      rw [← hc]
      exact h j hj⟩,
    fun ⟨i, rnd, l, e, msg, hr, h⟩ ↦ ⟨i, rnd, l, e, msg, hr, fun j hj ↦ by
      rw [hc]
      exact h j hj⟩⟩

variable {P θ}

theorem portCw_of_srchOkZN {μ : SrchModeN n} {i : (RSpecN n (SelMemN n)).Port}
    (h : srchOkZN P μ i) : PortCw (S := HPosN n) (M := SelMemN n) hwFixF i := by
  rcases i with ((p | c) | c) | T
  · trivial
  · trivial
  · obtain ⟨-, z, a, rfl, hz⟩ := h
    exact Quantum.Xmss.Assembly.hwOfSets_fst.mpr hz
  · trivial

/-- **A repeated reveal with the key unselected is in the failure event**: at a record call
allowed by a rest mode, on the invariant, a revealed randomizer position with its key unselected
has run all its trials. -/
theorem reRevQWN_le_charge (i : (RSpecN n (SelMemN n)).Port)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n))
      ((RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n)) ℂ)
    (hσ : σ.PosSemidef)
    (h : ∃ μ, srchOkZN P μ i ∧
      QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦ m.2)
        (FInvFN P θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpecN n (SelMemN n)).In i)
          ((RSpecN n (SelMemN n)).In i) ℂ) ⊗ₖ compressReg HashOutput HashDomain (QMemN n)) σ)) :
    reRevQWN i σ ≤ (randomizerAttemptLimit : ℝ≥0∞) *
      (((if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1
        else 0 : ℕ) : ℝ≥0∞) * potential (hwDecProj (failSetFN P θ)) σ) := by
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · obtain ⟨μ, ⟨hrest, -⟩, hS⟩ := h
    rcases hT : rndOfTN T with _ | ⟨i, rnd⟩
    · simp only [reRevQWN, hT]
      exact zero_le
    · simp only [reRevQWN, hT]
      have h1 : ((if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n))
          (.inr T) then 1 else 0 : ℕ) : ℝ≥0∞) = 1 := by simp [extCls]
      rw [h1, one_mul]
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      classical
      exact diagMass_le_potential_hwDecProj (fun b : Hw HashOutput HashDomain × QMemN n ↦
        (i, loC rnd) ∈ b.2.1 ∧ ∃ l e msg, rndLab rnd = some (l, e, msg) ∧ b.2.2 i l e = none)
        (failSetFN P θ) _ hσ hS fun s hs hP ↦ by
          obtain ⟨l, e, msg, hr, hu⟩ := hP.2
          exact ⟨i, rnd, l, e, msg, hr, fun j hj ↦ hs.2.2.2 i rnd l e msg hr hP.1 hu j
            (by rw [doneFN_of_rest hrest i rnd]; exact hj)⟩

end fail

/-! ## Counting the failed searches -/

section count

/-- The trial cells of the search of user `i`'s randomizer position from its hidden base, under
the parameter `P i`. -/
def failCellFN (P : Fin n → PublicParameter) (θ : HPosN n → Digest) :
    Fin n × RndIdxF → ℕ → HashDomain
  | (i, .inl p), j => trialCell (P i) bottomLayer p.1 (messageBytes p.2)
      (θ (i, loC (.rndBottom p.1 p.2))) j
  | (i, .inr p), j => trialCell (P i) topLayer p.1 (rootBytes p.2)
      (θ (i, loC (.rndTop p.1 p.2))) j

theorem card_rndIdxFN :
    Fintype.card (Fin n × RndIdxF) = n * (2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128) := by
  rw [Fintype.card_prod, Fintype.card_fin, card_rndIdxF]

/-- Distinct trials of a randomizer position's search read distinct cells. -/
theorem failCellFN_inj (P : Fin n → PublicParameter) (θ : HPosN n → Digest)
    (k : Fin n × RndIdxF) :
    ∀ a < randomizerAttemptLimit, ∀ b < randomizerAttemptLimit,
      failCellFN P θ k a = failCellFN P θ k b → a = b := by
  intro a ha b hb h
  rcases k with ⟨i, p | p⟩
  · exact trialCell_injF _ _ _ _ _ ha hb h
  · exact trialCell_injF _ _ _ _ _ ha hb h

/-- A failing database fails all the trials of one user's randomizer position. -/
theorem failDbFN_cover (P : Fin n → PublicParameter) (θ : HPosN n → Digest)
    (D : DbReg HashOutput HashDomain) (hD : FailDbFN P θ D) :
    ∃ k : Fin n × RndIdxF, ∀ j < randomizerAttemptLimit,
      ¬ Codeword.Valid (truncateHash ((D.1 (failCellFN P θ k j)).getD 0)) := by
  obtain ⟨i, rnd, l, e, msg, hr, h⟩ := hD
  cases rnd with
  | rndBottom k m =>
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hr)
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    subst h1 h3 h4
    exact ⟨(i, .inl (k, m)), fun j hj ↦ h j hj⟩
  | rndTop k d =>
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hr)
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    subst h1 h3 h4
    exact ⟨(i, .inr (k, d)), fun j hj ↦ h j hj⟩
  | seed | param | prf | chain | leaf | node => cases hr

open scoped Classical in
/-- **The failure fraction**: `n |rnd| · (1 - ρ_c)^(2^32)` over the tables, the codeword values
a fraction `ρ_c` of the trial cell's values. -/
theorem frac_failDbFN_le (P : Fin n → PublicParameter) (θ : HPosN n → Digest) :
    ((Finset.univ.filter fun t ↦ FailDbFN P θ (ofFunDbs t)).card : ℝ≥0∞) /
      Fintype.card ((HashDomain → HashOutput) × (HashOutput → HashDomain) ×
        (HashOutput → HashDomain)) ≤
      Fintype.card (Fin n × RndIdxF) * ((((Finset.univ.filter fun y : HashOutput ↦
        ¬ Codeword.Valid (truncateHash y)).card ^ randomizerAttemptLimit : ℕ) : ℝ≥0∞) /
          ((Fintype.card HashOutput ^ randomizerAttemptLimit : ℕ) : ℝ≥0∞)) :=
  frac_union_fail_le (failCellFN P θ) (fun y : HashOutput ↦ ¬ Codeword.Valid (truncateHash y))
    randomizerAttemptLimit (failCellFN_inj P θ) _ fun t ht ↦ failDbFN_cover P θ (ofFunDbs t) ht

end count

/-! ## The bound -/

set_option exponentiation.threshold 4096 in
/-- The numbers: `2^32 n (2^288 + 2^160) 2^-2048 ≤ 2^-1000` for `n ≤ 2^128`. -/
theorem reRevN_numbers_le (hn : n ≤ 2 ^ 128) :
    (randomizerAttemptLimit : ℝ≥0∞) * (((n * (2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128) : ℕ) :
      ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 2048)) ≤ (2 ^ 1000 : ℝ≥0∞)⁻¹ := by
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Nat.mul_le_mul_right (2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128) hn)) zero_le)
    zero_le) ?_
  rw [show (randomizerAttemptLimit : ℝ≥0∞) = ENNReal.ofReal (2 ^ 32) by
      rw [randomizerAttemptLimit, Nat.cast_pow, Nat.cast_ofNat, ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    show (2 ^ 1000 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ 1000) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

/-- **The repeated-reveal charges of the `n`-user challenge prefix**: with at most `K` classical
calls and `n ≤ 2^128` users, at most `K · 2^-1000`. -/
theorem totalWeight_reRevQWN_le (A : MuAdversary n) (θ : HPosN n → Digest) (hn : n ≤ 2 ^ 128)
    {K : ℕ} (hK : IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1
        else 0) K) :
    (runtimeR (m0N (n := n))).totalWeight .instruments reRevQWN (prefixQN A θ) initQN ≤
      K * (2 ^ 1000 : ℝ≥0∞)⁻¹ := by
  classical
  have hq := forallQueries_dec_moded (m0N (n := n)) (FInvFN (parQN θ) θ)
    (fun μ i r σ hok hσ ↦ fInvFN_step μ i r σ hok hσ) LocalSig.Interp.instruments
    (prefixQN A θ) .free (modedP_prefixQN A θ) (init_fInvFN (parQN θ) θ)
  have h1 := totalWeight_le_of_forallQueries (runtimeR (m0N (n := n))) .instruments
    (fun i σ ↦ ∃ μ, srchOkZN (parQN θ) μ i ∧
      QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦ m.2)
        (FInvFN (parQN θ) θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpecN n (SelMemN n)).In i)
          ((RSpecN n (SelMemN n)).In i) ℂ) ⊗ₖ compressReg HashOutput HashDomain (QMemN n)) σ))
    (fun _ _ _ h ↦ h)
    (w' := fun i σ ↦ (randomizerAttemptLimit : ℝ≥0∞) *
      (((if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1
        else 0 : ℕ) : ℝ≥0∞) * potential (hwDecProj (failSetFN (parQN θ) θ)) σ))
    (fun i σ hσ hok ↦ reRevQWN_le_charge i σ hσ hok) (prefixQN A θ) initQN_posSemidef hq
  have h1' := h1.trans_eq (totalWeight_const_mul_weight (runtimeR (m0N (n := n))) .instruments
    (randomizerAttemptLimit : ℝ≥0∞) (fun i σ ↦
      ((if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1
        else 0 : ℕ) : ℝ≥0∞) * potential (hwDecProj (failSetFN (parQN θ) θ)) σ)
    (prefixQN A θ) initQN)
  have h2 := totalWeight_charge_potential_le (runtimeR (m0N (n := n))) .instruments
    (hwDecProj (failSetFN (parQN θ) θ))
    (fun i ↦ if extCls HashOutput HashDomain (QMemN n) (recSpec (HPosN n) (SelMemN n)) i then 1
      else 0)
    (PortCw (S := HPosN n) (M := SelMemN n) hwFixF)
    (fun i hi r ↦ runtimeR_commute_hwDecProj (m0N (n := n)) (offHw_failDbFN (parQN θ) θ)
      (failSetFN (parQN θ) θ) (fun _ ↦ Iff.rfl) i hi r)
    (fun _ _ _ h ↦ portCw_of_srchOkZN h.choose_spec.1) (prefixQN A θ) hK initQN_posSemidef hq
  have h3 : potential (hwDecProj (failSetFN (parQN θ) θ)) initQN ≤
      ((Finset.univ.filter fun t ↦ FailDbFN (parQN θ) θ (ofFunDbs t)).card : ℝ≥0∞) /
        Fintype.card ((HashDomain → HashOutput) × (HashOutput → HashDomain) ×
          (HashOutput → HashDomain)) := by
    refine (le_of_eq (potential_hwDecProj_init (m0N (n := n)) (failSetFN (parQN θ) θ)
      (FailDbFN (parQN θ) θ) (fun _ ↦ Iff.rfl)
      ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
      (SubState.basis _).posSemidef)).trans ?_
    exact (mul_le_mul' (ENNReal.ofReal_le_one.mpr (SubState.basis _).trace_re_le_one)
      le_rfl).trans_eq (one_mul _)
  have hcb : Quantum.Xmss.cwCount * 2 ^ 128 ≤ Fintype.card HashOutput := by
    rw [← card_codeword_truncateHash]
    exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have hρ : (2 ^ 21 : ℝ)⁻¹ ≤ ((Quantum.Xmss.cwCount * 2 ^ 128 : ℕ) : ℝ) /
      Fintype.card HashOutput := by
    rw [← card_codeword_truncateHash, card_codeword_div_card_hashOutput]
    exact Quantum.Xmss.inv_two_pow_21_le_rhoCw
  have h4 := (natCast_pow_sub_div_le_exp (Fintype.card HashOutput)
    (Quantum.Xmss.cwCount * 2 ^ 128) randomizerAttemptLimit hcb Fintype.card_pos _ hρ).trans
    (ENNReal.ofReal_le_ofReal exp_neg_trials_le)
  have h5 : potential (hwDecProj (failSetFN (parQN θ) θ)) initQN ≤
      ((n * (2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (1 / 2 ^ 2048) := by
    refine (h3.trans (frac_failDbFN_le (parQN θ) θ)).trans ?_
    rw [card_not_codewordF, card_rndIdxFN]
    exact mul_le_mul_of_nonneg_left h4 zero_le
  calc (runtimeR (m0N (n := n))).totalWeight .instruments reRevQWN (prefixQN A θ) initQN
      ≤ (randomizerAttemptLimit : ℝ≥0∞) *
          (K * potential (hwDecProj (failSetFN (parQN θ) θ)) initQN) :=
        h1'.trans (mul_le_mul_of_nonneg_left h2 zero_le)
    _ ≤ (randomizerAttemptLimit : ℝ≥0∞) * (K * (((n * (2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128) :
        ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 2048))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 zero_le) zero_le
    _ = K * ((randomizerAttemptLimit : ℝ≥0∞) * (((n * (2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128) :
        ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 2048))) := mul_left_comm _ _ _
    _ ≤ K * (2 ^ 1000 : ℝ≥0∞)⁻¹ := mul_le_mul_of_nonneg_left (reRevN_numbers_le hn) zero_le

end Quantum.Qrom.Xmss.Multi

end
