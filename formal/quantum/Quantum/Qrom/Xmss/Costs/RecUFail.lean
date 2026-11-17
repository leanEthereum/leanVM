module

public import Quantum.Qrom.Xmss.Costs.RecUModes

@[expose] public section

/-!
# The repeated reveals of an unselected key: the failed searches

The charge `reRevQW` of the challenge prefix (a reveal of a randomizer base already revealed,
its key still unselected) adds up to at most `K · 2^-1000` with `K` classical calls
(`totalWeight_reRevQW_le`), as QRPM's `CwReFail`.

* **The invariant in the decompressed basis** (`FInvF`, `fInvF_step`, `init_fInvF`): no empty
  cell, no hardwired message cell, the mode's base is the hidden one, and every revealed
  randomizer position whose key is unselected has every trial already run on a digest that is no
  codeword (`RunFail`), on the decompressed `h`-database. The trial cells are message cells, which
  the prefix never hardwires.
* **The repeated reveals** (`reRevQW_le_charge`): a repeated reveal with the key unselected lies
  in the database event `failSetF` (some randomizer position fails all `2^32` trials), whose
  decompressed projector commutes with every called port (the programs hardwire non-message cells
  only, `hwFixF`); CwReFail's `totalWeight_charge_potential_le` and `potential_hwDecProj_init`.
* **Counting** (`frac_union_fail_le`, `frac_failDbF_le`): at most
  `(2^288 + 2^160) (1 - ρ_c)^(2^32)` of the tables fail some search.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (diagMass totalWeight_const_mul_weight progUpdate)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR NoBot decR liftAns noBot_init
  forallQueries_dec_moded runtimeR_commute_hwDecProj totalWeight_charge_potential_le
  diagMass_le_potential_hwDecProj potential_hwDecProj_init pow_mul_sum_all_le
  natCast_pow_sub_div_le_exp exp_neg_trials_le hwOfSets hwOfSets_fst PortCw extCls
  totalWeight_le_of_forallQueries)

attribute [local irreducible] xmssRom

/-! ## Selections -/

theorem select_eq_noneF {m : SelMem} {l l' : Layer} {e e' : KeyIndex} {c : HashDomain}
    {d : Digest} (h : m.select l e c d l' e' = none) : m l' e' = none := by
  unfold SelMem.select at h
  by_cases hl : l' = l
  · subst hl
    rw [Function.update_self] at h
    by_cases he : e' = e
    · subst he
      rw [Function.update_self] at h
      exact absurd h (Option.some_ne_none _)
    · rwa [Function.update_of_ne he] at h
  · rwa [Function.update_of_ne hl] at h

/-- A trial read never unselects a key. -/
theorem cwUpd_eq_noneF {l l' : Layer} {e e' : KeyIndex} {z : HashDomain} {m : SelMem}
    {o : Option HashOutput} (h : cwUpd l e z m o l' e' = none) : m l' e' = none := by
  rcases o with _ | w
  · exact h
  · rcases cwUpd_some l e z m w with h' | h'
    · rwa [h'] at h
    · rw [h'] at h
      unfold cwSel at h
      split_ifs at h
      · exact select_eq_noneF h
      · exact h

/-- A trial read of a codeword digest leaves its key selected. -/
theorem cwUpd_ne_noneF {l : Layer} {e : KeyIndex} {z : HashDomain} {m : SelMem} {w : HashOutput}
    (hv : Codeword.Valid (truncateHash w)) : cwUpd l e z m (some w) l e ≠ none := by
  by_cases hm : m l e = none
  · rw [cwUpd_some_of_none l e z hm w]
    unfold cwSel
    rw [ite_eq_left hv, SelMem.select_self]
    exact Option.some_ne_none _
  · rw [cwUpd_of_ne_none hm]
    exact hm

theorem slotOf_trialCellF (P : PublicParameter) (l : Layer) (e : KeyIndex) (msg : MsgBytes)
    (b : Randomizer) (j : ℕ) : slotOf (trialCell P l e msg b j) = some (.msg l e) :=
  slotOf_cell P (show Addressable (.msg l e) from trivial) _

/-- Distinct trials of a search read distinct cells. -/
theorem trialCell_injF (P : PublicParameter) (l : Layer) (e : KeyIndex) (msg : MsgBytes)
    (b : Randomizer) {j j' : ℕ} (hj : j < randomizerAttemptLimit)
    (hj' : j' < randomizerAttemptLimit) (h : trialCell P l e msg b j = trialCell P l e msg b j') :
    j = j' := by
  have h1 := cell_injective P (s := .msg l e) (s' := .msg l e) trivial trivial h
  have h2 : ((msg, b + BitVec.ofNat digestBits j) : MsgBytes × Randomizer) =
      (msg, b + BitVec.ofNat digestBits j') := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
  have h3 : BitVec.ofNat digestBits j = BitVec.ofNat digestBits j' :=
    add_left_cancel (congrArg Prod.snd h2)
  have h4 := congrArg BitVec.toNat h3
  have hN : randomizerAttemptLimit < 2 ^ digestBits := by
    simp [randomizerAttemptLimit, digestBits]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hj.trans hN),
    Nat.mod_eq_of_lt (hj'.trans hN)] at h4
  exact h4

theorem hwNone_of_msgFreeF {s : RReg SelMem} (hM : MsgFree s) {z : HashDomain} {l : Layer}
    {e : KeyIndex} (hz : slotOf z = some (.msg l e)) : s.2.1.1 z = none := by
  by_contra h
  exact hM z (Option.ne_none_iff_isSome.mp h) l e hz

/-! ## The invariant of the failed searches -/

section inv

variable (θ : HPos → Digest)

/-- The trials of `rnd` already run in the mode `μ`: those before the current trial of its search,
all of them otherwise. -/
def doneF : SrchMode → Pos → ℕ
  | .free, _ => randomizerAttemptLimit
  | .grd r _ j, rnd => if r = rnd then j else randomizerAttemptLimit

theorem doneF_of_rest {μ : SrchMode} (h : μ.Rest) (rnd : Pos) :
    doneF μ rnd = randomizerAttemptLimit := by
  rcases μ with _ | ⟨r, b, j⟩
  · rfl
  · have hj : j = randomizerAttemptLimit := h
    subst hj
    show (if r = rnd then randomizerAttemptLimit else randomizerAttemptLimit) = _
    split_ifs <;> rfl

/-- The `h`-value of trial `j` of the search of `rnd` (key `(l, e)`, message `msg`) from its
hidden base, on the databases `D`. -/
def trialValF (l : Layer) (e : KeyIndex) (msg : MsgBytes) (rnd : Pos) (j : ℕ)
    (D : DbReg HashOutput HashDomain) : HashOutput :=
  (D.1 (trialCell (θ paramC) l e msg (θ (loC rnd)) j)).getD 0

/-- The mode's search runs from the hidden base. -/
def ModeOkF : SrchMode → Prop
  | .free => True
  | .grd rnd b _ => b = θ (loC rnd)

/-- **The trials already run failed**: every revealed randomizer position whose key is unselected
has its trials already run on digests that are no codewords. -/
def RunFail (μ : SrchMode) (s : RReg SelMem) : Prop :=
  ∀ rnd l e msg, rndLab rnd = some (l, e, msg) → loC rnd ∈ s.2.2.1 → s.2.2.2 l e = none →
    ∀ j < doneF μ rnd, ¬ Codeword.Valid (truncateHash (trialValF θ l e msg rnd j s.1))

/-- **The invariant of the failed searches**, in the decompressed basis. -/
def FInvF (μ : SrchMode) : Set (RReg SelMem) :=
  {s | NoBot s ∧ MsgFree s ∧ ModeOkF θ μ ∧ RunFail θ μ s}

variable {θ}

theorem fInvF_free_of_rest {μ : SrchMode} (hμ : μ.Rest) {s : RReg SelMem}
    (hs : s ∈ FInvF θ μ) : s ∈ FInvF θ .free :=
  ⟨hs.1, hs.2.1, trivial, fun rnd l e msg hr hl hu j hj ↦
    hs.2.2.2 rnd l e msg hr hl hu j (by rw [doneF_of_rest hμ rnd]; exact hj)⟩

/-- **A record**: a reveal of one randomizer base starts its search with no trial run; a reveal
of no randomizer base reveals no randomizer position. -/
theorem fInvF_rec {μ : SrchMode} (hμ : μ.Rest) {T : Finset HPos} (hT : RevOkQ T)
    {s : RReg SelMem} (hs : s ∈ FInvF θ μ) :
    ((s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) : RReg SelMem) ∈
      FInvF θ (revNxQ T fun rnd ↦ θ (loC rnd)) := by
  obtain ⟨hnb, hmf, -, hl⟩ := hs
  rcases hT with ⟨rnd₀, hr₀, rfl⟩ | hT
  · rw [revNxQ_loC hr₀]
    refine ⟨hnb, hmf, rfl, fun rnd l e msg hr hlab hu j hj ↦ ?_⟩
    by_cases he : rnd₀ = rnd
    · subst he
      have hd : doneF (.grd rnd₀ (θ (loC rnd₀)) 0) rnd₀ = 0 := ite_eq_left rfl
      rw [hd] at hj
      exact absurd hj (Nat.not_lt_zero j)
    · have hd : doneF (.grd rnd₀ (θ (loC rnd₀)) 0) rnd = randomizerAttemptLimit :=
        ite_eq_right he
      have hl1 : loC rnd ∈ s.2.2.1 := by
        rcases Finset.mem_union.mp hlab with h | h
        · exact h
        · exact absurd (loC_injective (Finset.mem_singleton.mp h)).symm he
      exact hl rnd l e msg hr hl1 hu j (by rw [doneF_of_rest hμ rnd, ← hd]; exact hj)
  · rw [revNxQ_none hT]
    refine ⟨hnb, hmf, trivial, fun rnd l e msg hr hlab hu j hj ↦ ?_⟩
    have hl1 : loC rnd ∈ s.2.2.1 := by
      rcases Finset.mem_union.mp hlab with h | h
      · exact h
      · exact absurd (rndC_loC (by rw [hr]; rfl)) (hT _ h)
    exact hl rnd l e msg hr hl1 hu j (by rw [doneF_of_rest hμ rnd]; exact hj)

/-- **A program of a non-message cell** keeps the invariant: the trial cells keep their
database values. -/
theorem fInvF_prog {μ : SrchMode} (hμ : μ.Rest) {z : HashDomain} {a : HashOutput}
    (hz : ∀ l e, slotOf z ≠ some (.msg l e)) {s s' : RReg SelMem} (hs : s ∈ FInvF θ μ)
    (hp : ProgRelH z a s s') : s' ∈ FInvF θ .free := by
  obtain ⟨hnb, hmf, -, hl⟩ := hs
  obtain ⟨h2, hnb', h1⟩ := hp
  have hm : s'.2.2 = s.2.2 := (congrArg Prod.snd h2 :)
  have hw : s'.2.1 = progUpdate (.programH z a) s.2.1 := (congrArg Prod.fst h2 :)
  refine ⟨hnb' hnb, fun x hx l e ↦ ?_, trivial, fun rnd l e msg hr hlab hu j hj ↦ ?_⟩
  · rw [hw] at hx
    have hx' : (Function.update s.2.1.1 z (some a) x).isSome := hx
    by_cases hxz : x = z
    · subst hxz
      exact hz l e
    · rw [Function.update_of_ne hxz] at hx'
      exact hmf x hx' l e
  · rw [hm] at hlab hu
    have hc : trialValF θ l e msg rnd j s'.1 = trialValF θ l e msg rnd j s.1 := by
      unfold trialValF
      exact congrArg (fun o : Option HashOutput ↦ o.getD 0)
        (h1 (trialCell (θ paramC) l e msg (θ (loC rnd)) j) fun he ↦
          hz l e (he ▸ slotOf_trialCellF (θ paramC) l e msg (θ (loC rnd)) j))
    rw [hc]
    exact hl rnd l e msg hr hlab hu j (by rw [doneF_of_rest hμ rnd]; exact hj)

theorem srchRdNx_trial_some {rnd : Pos} {b : Randomizer} {j : ℕ} {z : HashDomain} {l : Layer}
    {e : KeyIndex} {r : Option HashOutput × QMem} {x : Encoding}
    (h : Codeword.decode (truncateHash (r.1.getD 0)) = some x) :
    srchRdNx (.grd rnd b j) (trialRead z l e) r = .free := by
  show (match Codeword.decode (truncateHash (r.1.getD 0)) with
    | some _ => SrchMode.free
    | none => SrchMode.grd rnd b (j + 1)) = _
  rw [h]

theorem srchRdNx_trial_none {rnd : Pos} {b : Randomizer} {j : ℕ} {z : HashDomain} {l : Layer}
    {e : KeyIndex} {r : Option HashOutput × QMem}
    (h : Codeword.decode (truncateHash (r.1.getD 0)) = none) :
    srchRdNx (.grd rnd b j) (trialRead z l e) r = .grd rnd b (j + 1) := by
  show (match Codeword.decode (truncateHash (r.1.getD 0)) with
    | some _ => SrchMode.free
    | none => SrchMode.grd rnd b (j + 1)) = _
  rw [h]

/-- **The read of a trial**: a codeword digest selects the key and ends the search; otherwise the
trial failed. -/
theorem fInvF_read {rnd : Pos} {b : Randomizer} {j : ℕ} {l : Layer} {e : KeyIndex}
    {msg : MsgBytes} (hr : rndLab rnd = some (l, e, msg)) {s : RReg SelMem}
    (hs : s ∈ FInvF θ (.grd rnd b j)) (r : Option HashOutput × QMem)
    (hrs : r = liftAns s (.readH (trialCell (θ paramC) l e msg b j)
      (cwUpd l e (trialCell (θ paramC) l e msg b j)))) :
    readFinH s (trialCell (θ paramC) l e msg b j) (cwUpd l e (trialCell (θ paramC) l e msg b j)) ∈
      FInvF θ (srchRdNx (.grd rnd b j) (trialRead (trialCell (θ paramC) l e msg b j) l e) r) := by
  set z := trialCell (θ paramC) l e msg b j with hzdef
  obtain ⟨hnb, hmf, hb, hl⟩ := hs
  have hb' : b = θ (loC rnd) := hb
  have hzm : slotOf z = some (.msg l e) := slotOf_trialCellF _ l e msg b j
  have hw0 : s.2.1.1 z = none := hwNone_of_msgFreeF hmf hzm
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hnb.1 z)
  have hv : (hwView s.2.1 s.1).1 z = some w := by
    show (s.2.1.1 z).or (s.1.1 z) = some w
    rw [hw0, hw]
    rfl
  have hr1 : r.1 = some w := by
    rw [hrs]
    exact hv
  have hfin : readFinH s z (cwUpd l e z) =
      (s.1, s.2.1, (s.2.2.1, cwUpd l e z s.2.2.2 (some w))) := by
    unfold readFinH
    rw [hv]
  rw [hfin]
  have hu : ∀ l' e', cwUpd l e z s.2.2.2 (some w) l' e' = none → s.2.2.2 l' e' = none :=
    fun _ _ h ↦ cwUpd_eq_noneF h
  have hrj : r.1.getD 0 = w := by rw [hr1]; rfl
  rcases hd : Codeword.decode (truncateHash w) with _ | x
  · rw [srchRdNx_trial_none (by rw [hrj]; exact hd)]
    refine ⟨hnb, hmf, hb, fun rnd' l' e' msg' hr' hlab hu' j' hj' ↦ ?_⟩
    by_cases hne : rnd = rnd'
    · subst hne
      rw [hr] at hr'
      obtain ⟨rfl, rfl, rfl⟩ : l = l' ∧ e = e' ∧ msg = msg' := by
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hr')
        exact ⟨h1, Prod.mk.inj h2⟩
      have h1 : doneF (.grd rnd b (j + 1)) rnd = j + 1 := ite_eq_left rfl
      rw [h1] at hj'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · have h0 : doneF (.grd rnd b j) rnd = j := ite_eq_left rfl
        exact hl rnd l e msg hr hlab (hu l e hu') j' (by rw [h0]; exact hj')
      · have hval : trialValF θ l e msg rnd j' s.1 = w := by
          unfold trialValF
          rw [← hb', ← hzdef, hw]
          rfl
        show ¬ Codeword.Valid (truncateHash (trialValF θ l e msg rnd j' s.1))
        rw [hval]
        exact not_valid_of_decode hd
    · have h1 : doneF (.grd rnd b (j + 1)) rnd' = doneF (.grd rnd b j) rnd' := by
        show (if rnd = rnd' then j + 1 else randomizerAttemptLimit) =
          (if rnd = rnd' then j else randomizerAttemptLimit)
        rw [ite_eq_right hne, ite_eq_right hne]
      exact hl rnd' l' e' msg' hr' hlab (hu l' e' hu') j' (by rw [← h1]; exact hj')
  · rw [srchRdNx_trial_some (by rw [hrj]; exact hd)]
    refine ⟨hnb, hmf, trivial, fun rnd' l' e' msg' hr' hlab hu' j' hj' ↦ ?_⟩
    have hvld := valid_of_decode hd
    have hne : rnd ≠ rnd' := by
      rintro rfl
      rw [hr] at hr'
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hr')
      obtain ⟨h3, -⟩ := Prod.mk.inj h2
      subst h1 h3
      exact cwUpd_ne_noneF hvld hu'
    have h1 : doneF (.grd rnd b j) rnd' = randomizerAttemptLimit := ite_eq_right hne
    exact hl rnd' l' e' msg' hr' hlab (hu l' e' hu') j' (by rw [h1]; exact hj')

/-- **Every allowed call keeps the invariant**, in the decompressed basis. -/
theorem fInvF_step (μ : SrchMode) (i : (RSpec SelMem).Port) (r : (RSpec SelMem).Result i)
    (σ : Matrix ((RSpec SelMem).In i × RReg SelMem) ((RSpec SelMem).In i × RReg SelMem) ℂ)
    (hok : srchOkZ (θ paramC) μ i)
    (hσ : QuerySupportedOn (fun m : (RSpec SelMem).In i × RReg SelMem ↦ m.2) (FInvF θ μ) σ) :
    QuerySupportedOn (fun m : (RSpec SelMem).Out i × RReg SelMem ↦ m.2)
      (FInvF θ (srchNxZ θ μ i r))
      (((decR (X := HashOutput) (Z := HashDomain) m0Q).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · exact (decR_sponge_supp m0Q i r _ σ hσ).mono fun s hs ↦ fInvF_free_of_rest hok hs
  · rcases μ with _ | ⟨rnd, b, j⟩
    · exact hok.elim
    · obtain ⟨-, l, e, msg, hr, rfl⟩ := hok
      refine (decR_readH_supp m0Q (trialCell (θ paramC) l e msg b j)
        (cwUpd l e (trialCell (θ paramC) l e msg b j)) r _ σ hσ).mono fun s' hs' ↦ ?_
      obtain ⟨s, hs, hrs, rfl⟩ := hs'
      exact fInvF_read hr hs r hrs
  · obtain ⟨hμ, z, a, rfl, hz⟩ := hok
    refine (decR_progH_supp m0Q z a r _ σ hσ).mono fun s' hs' ↦ ?_
    obtain ⟨s, hs, hp⟩ := hs'
    exact fInvF_prog hμ hz hs hp
  · refine (decR_rec_supp m0Q T r _ σ hσ).mono fun s' hs' ↦ ?_
    obtain ⟨s, hs, -, rfl⟩ := hs'
    exact fInvF_rec hok.1 hok.2 hs

variable (θ) in
/-- The initial register in the decompressed basis: no empty cell, nothing hardwired, nothing
revealed. -/
theorem init_fInvF :
    QuerySupportedOn (fun m : QReg.of Unit × RReg SelMem ↦ m.2) (FInvF θ .free)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain QMem) initQ) := by
  have hnb := noBot_init (X := HashOutput) (Z := HashDomain) m0Q
    ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
  have h0 : QuerySupportedOn (fun m : QReg.of Unit × RReg SelMem ↦ m.2)
      {s | s.2 = (hwEmpty HashOutput HashDomain, m0Q)} initQ := by
    intro m m' hm
    change (((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      (SubState.basis (((Database.empty, Database.empty, Database.empty),
        hwEmpty HashOutput HashDomain, m0Q) : RReg SelMem)).matrix) m m' ≠ 0 at hm
    rw [kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [SubState.matrix_basis, Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨(congrArg Prod.snd he.1).symm, (congrArg Prod.snd he.2).symm⟩
    · exact absurd rfl h
  have h1 := QuerySupportedOn.conj h0
    (K := (1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg HashOutput HashDomain QMem)
    (q' := fun m : QReg.of Unit × RReg SelMem ↦ m.2)
    (S' := {s | s.2 = (hwEmpty HashOutput HashDomain, m0Q)})
    fun m' m hK hm ↦ by
      have hK' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
      rw [compressReg, kroneckerMap_apply] at hK'
      have he : m'.2.2 = m.2.2 := by
        by_contra hne
        exact right_ne_zero_of_mul hK' (Matrix.one_apply_ne hne)
      show m'.2.2 = _
      rw [he]
      exact hm
  have hmem : ∀ s : RReg SelMem, NoBot s → s.2 = (hwEmpty HashOutput HashDomain, m0Q) →
      s ∈ FInvF θ .free := fun s hs he ↦ by
    refine ⟨hs, fun x hx ↦ ?_, trivial, fun rnd _ _ _ _ hl _ _ _ ↦ ?_⟩
    · rw [he] at hx
      exact absurd hx (by simp [hwEmpty])
    · rw [he] at hl
      exact absurd hl (Finset.notMem_empty _)
  intro a b hab
  exact ⟨hmem _ (hnb a b hab).1 (h1 a b hab).1, hmem _ (hnb a b hab).2 (h1 a b hab).2⟩

end inv

/-! ## The failure event -/

section fail

variable (θ : HPos → Digest)

/-- **Some search fails on the databases**: a randomizer position all of whose `2^32` trials from
its hidden base read digests that are no codewords. -/
def FailDbF (D : DbReg HashOutput HashDomain) : Prop :=
  ∃ rnd l e msg, rndLab rnd = some (l, e, msg) ∧
    ∀ j < randomizerAttemptLimit, ¬ Codeword.Valid (truncateHash (trialValF θ l e msg rnd j D))

/-- The registers whose databases fail a search. -/
def failSetF : Set (RReg SelMem) := {s | FailDbF θ s.1}

/-- `failSetF`, decided classically. -/
noncomputable instance instDecidableFailSetF : DecidablePred (· ∈ failSetF θ) :=
  Classical.decPred _

/-- The static hardwiring off the trial cells: every non-message `h`-cell, every `k`, `k'` cell. -/
noncomputable def hwFixF : Hw HashOutput HashDomain :=
  hwOfSets {z : HashDomain | ∀ l e, slotOf z ≠ some (.msg l e)} Set.univ Set.univ

theorem hwFixF_trial (P : PublicParameter) (l : Layer) (e : KeyIndex) (msg : MsgBytes)
    (b : Randomizer) (j : ℕ) : hwFixF.1 (trialCell P l e msg b j) = none := by
  by_contra h
  exact (hwOfSets_fst.mp h) l e (slotOf_trialCellF P l e msg b j)

/-- `FailDbF` reads the trial cells only, off `hwFixF`. -/
theorem offHw_failDbF : OffHw hwFixF (FailDbF θ) := by
  intro D D' h1 _ _
  have hc : ∀ l e msg rnd j, trialValF θ l e msg rnd j D = trialValF θ l e msg rnd j D' :=
    fun l e msg rnd j ↦ by
      unfold trialValF
      exact congrArg (fun o : Option HashOutput ↦ o.getD 0)
        (h1 (trialCell (θ paramC) l e msg (θ (loC rnd)) j) (hwFixF_trial _ l e msg _ j))
  exact ⟨fun ⟨rnd, l, e, msg, hr, h⟩ ↦ ⟨rnd, l, e, msg, hr, fun j hj ↦ by
      rw [← hc]
      exact h j hj⟩,
    fun ⟨rnd, l, e, msg, hr, h⟩ ↦ ⟨rnd, l, e, msg, hr, fun j hj ↦ by
      rw [hc]
      exact h j hj⟩⟩

variable {θ}

theorem portCw_of_srchOkZ {μ : SrchMode} {i : (RSpec SelMem).Port}
    (h : srchOkZ (θ paramC) μ i) : PortCw (S := HPos) (M := SelMem) hwFixF i := by
  rcases i with ((p | c) | c) | T
  · trivial
  · trivial
  · obtain ⟨-, z, a, rfl, hz⟩ := h
    exact hwOfSets_fst.mpr hz
  · trivial

/-- **A repeated reveal with the key unselected is in the failure event**: at a record call
allowed by a rest mode, on the invariant, a revealed randomizer position with its key unselected
has run all its trials. -/
theorem reRevQW_le_charge (i : (RSpec SelMem).Port)
    (σ : Matrix ((RSpec SelMem).In i × RReg SelMem) ((RSpec SelMem).In i × RReg SelMem) ℂ)
    (hσ : σ.PosSemidef)
    (h : ∃ μ, srchOkZ (θ paramC) μ i ∧
      QuerySupportedOn (fun m : (RSpec SelMem).In i × RReg SelMem ↦ m.2) (FInvF θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpec SelMem).In i) ((RSpec SelMem).In i) ℂ) ⊗ₖ
          compressReg HashOutput HashDomain QMem) σ)) :
    reRevQW i σ ≤ (randomizerAttemptLimit : ℝ≥0∞) *
      (((if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0 : ℕ) :
        ℝ≥0∞) * potential (hwDecProj (failSetF θ)) σ) := by
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · obtain ⟨μ, ⟨hrest, -⟩, hS⟩ := h
    rcases hT : rndOfT T with _ | rnd
    · simp only [reRevQW, hT]
      exact zero_le
    · simp only [reRevQW, hT]
      have h1 : ((if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) (.inr T) then 1
          else 0 : ℕ) : ℝ≥0∞) = 1 := by simp [extCls]
      rw [h1, one_mul]
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      classical
      exact diagMass_le_potential_hwDecProj (fun b : Hw HashOutput HashDomain × QMem ↦
        loC rnd ∈ b.2.1 ∧ ∃ l e msg, rndLab rnd = some (l, e, msg) ∧ b.2.2 l e = none)
        (failSetF θ) _ hσ hS fun s hs hP ↦ by
          obtain ⟨l, e, msg, hr, hu⟩ := hP.2
          exact ⟨rnd, l, e, msg, hr, fun j hj ↦ hs.2.2.2 rnd l e msg hr hP.1 hu j
            (by rw [doneF_of_rest hrest rnd]; exact hj)⟩

end fail

/-! ## Counting the failed searches -/

section count

/-- **A union of all-fail events at distinct points**: if every `F`-function fails, for some
index `i`, the test `G` at `N` distinct points `z i j`, at most `|ι| (g / |B|)^N` of the
functions are in `F` (`g` values pass `G`). -/
theorem frac_union_fail_le {ι A B C : Type} [Fintype ι] [Fintype A] [DecidableEq A] [Fintype B]
    [Nonempty B] [Fintype C] [Nonempty C] (z : ι → ℕ → A) (G : B → Prop) [DecidablePred G]
    (N : ℕ) (hz : ∀ i, ∀ a < N, ∀ b < N, z i a = z i b → a = b)
    (F : (A → B) × C → Prop) [DecidablePred F]
    (hF : ∀ t, F t → ∃ i, ∀ j < N, G (t.1 (z i j))) :
    ((Finset.univ.filter F).card : ℝ≥0∞) / Fintype.card ((A → B) × C) ≤
      Fintype.card ι * ((((Finset.univ.filter G).card ^ N : ℕ) : ℝ≥0∞) /
        ((Fintype.card B ^ N : ℕ) : ℝ≥0∞)) := by
  set g := (Finset.univ.filter G).card
  set n := Fintype.card (A → B)
  set S : ι → ℕ := fun i ↦ ∑ f : A → B, (if ∀ j < N, G (f (z i j)) then 1 else 0) with hSdef
  have hS : ∀ i, Fintype.card B ^ N * S i ≤ g ^ N * n := fun i ↦
    pow_mul_sum_all_le (z i) (fun _ ↦ G) g (fun _ ↦ by
      rw [Finset.sum_boole]
      exact le_rfl) N (hz i)
  have hcard : (Finset.univ.filter F).card ≤ ∑ i, S i * Fintype.card C := by
    rw [Finset.card_filter]
    calc ∑ t, (if F t then 1 else 0)
        ≤ ∑ t : (A → B) × C, ∑ i, (if ∀ j < N, G (t.1 (z i j)) then 1 else 0) :=
          Finset.sum_le_sum fun t _ ↦ by
            split_ifs with h
            · obtain ⟨i, hi⟩ := hF t h
              exact le_trans (by rw [ite_eq_left hi]) (Finset.single_le_sum
                (f := fun i ↦ if ∀ j < N, G (t.1 (z i j)) then 1 else 0)
                (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))
            · exact Nat.zero_le _
      _ = ∑ i, ∑ t : (A → B) × C, (if ∀ j < N, G (t.1 (z i j)) then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ i, S i * Fintype.card C := Finset.sum_congr rfl fun i _ ↦ by
          rw [Fintype.sum_prod_type]
          simp only [hSdef, Finset.sum_mul]
          refine Finset.sum_congr rfl fun f _ ↦ ?_
          exact (Finset.sum_const_nat (m := if ∀ j < N, G (f (z i j)) then 1 else 0)
            fun _ _ ↦ rfl).trans (by rw [Finset.card_univ (α := C), Nat.mul_comm])
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc0 : (Fintype.card C : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB0 : ((Fintype.card B ^ N : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ Fintype.card_ne_zero)
  have hdiv : ∀ i, (S i : ℝ≥0∞) / n ≤ ((g ^ N : ℕ) : ℝ≥0∞) / ((Fintype.card B ^ N : ℕ) : ℝ≥0∞) :=
    fun i ↦ calc (S i : ℝ≥0∞) / n
        = (((Fintype.card B ^ N : ℕ) : ℝ≥0∞) * S i) / (((Fintype.card B ^ N : ℕ) : ℝ≥0∞) * n) :=
          (ENNReal.mul_div_mul_left _ _ hB0 (ENNReal.natCast_ne_top _)).symm
      _ ≤ (((g ^ N : ℕ) : ℝ≥0∞) * n) / (((Fintype.card B ^ N : ℕ) : ℝ≥0∞) * n) :=
          ENNReal.div_le_div_right (by exact_mod_cast hS i) _
      _ = ((g ^ N : ℕ) : ℝ≥0∞) / ((Fintype.card B ^ N : ℕ) : ℝ≥0∞) :=
          ENNReal.mul_div_mul_right _ _ hn0 (ENNReal.natCast_ne_top _)
  rw [Fintype.card_prod]
  calc ((Finset.univ.filter F).card : ℝ≥0∞) / ((n * Fintype.card C : ℕ) : ℝ≥0∞)
      ≤ ((∑ i, S i * Fintype.card C : ℕ) : ℝ≥0∞) / ((n * Fintype.card C : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hcard) _
    _ = ∑ i, (S i : ℝ≥0∞) / n := by
        rw [Nat.cast_sum, ENNReal.div_eq_inv_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← ENNReal.div_eq_inv_mul, Nat.cast_mul, Nat.cast_mul,
          ENNReal.mul_div_mul_right _ _ hc0 (ENNReal.natCast_ne_top _)]
    _ ≤ ∑ _i : ι, ((g ^ N : ℕ) : ℝ≥0∞) / ((Fintype.card B ^ N : ℕ) : ℝ≥0∞) :=
        Finset.sum_le_sum fun i _ ↦ hdiv i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The randomizer positions: bottom (key, message), top (key, root). -/
abbrev RndIdxF : Type := (KeyIndex × Message) ⊕ (KeyIndex × Digest)

/-- The trial cells of the search of a randomizer position from its hidden base. -/
def failCellF (θ : HPos → Digest) : RndIdxF → ℕ → HashDomain
  | .inl p, j => trialCell (θ paramC) bottomLayer p.1 (messageBytes p.2)
      (θ (loC (.rndBottom p.1 p.2))) j
  | .inr p, j => trialCell (θ paramC) topLayer p.1 (rootBytes p.2) (θ (loC (.rndTop p.1 p.2))) j

theorem card_rndIdxF : Fintype.card RndIdxF = 2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128 := by
  simp only [RndIdxF, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Quantum.Xmss.Hybrid.R0.card_bitVec_eq]
  norm_num [lifetime, layerCount, layerHeight, digestBits]

/-- The elements failing a test number the rest. -/
theorem sub_card_filterF {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter fun a ↦ ¬ p a).card = Fintype.card α - (Finset.univ.filter p).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) p
  rw [Finset.card_univ] at h
  omega

/-- The values of a cell truncating to no codeword. -/
theorem card_not_codewordF :
    (Finset.univ.filter fun y : HashOutput ↦ ¬ Codeword.Valid (truncateHash y)).card =
      Fintype.card HashOutput - Quantum.Xmss.cwCount * 2 ^ 128 := by
  rw [← card_codeword_truncateHash]
  exact sub_card_filterF _

/-- Distinct trials of a randomizer position's search read distinct cells. -/
theorem failCellF_inj (θ : HPos → Digest) (i : RndIdxF) :
    ∀ a < randomizerAttemptLimit, ∀ b < randomizerAttemptLimit,
      failCellF θ i a = failCellF θ i b → a = b := by
  intro a ha b hb h
  rcases i with p | p
  · exact trialCell_injF _ _ _ _ _ ha hb h
  · exact trialCell_injF _ _ _ _ _ ha hb h

/-- A failing database fails all the trials of one randomizer position. -/
theorem failDbF_cover (θ : HPos → Digest) (D : DbReg HashOutput HashDomain)
    (hD : FailDbF θ D) : ∃ i : RndIdxF, ∀ j < randomizerAttemptLimit,
      ¬ Codeword.Valid (truncateHash ((D.1 (failCellF θ i j)).getD 0)) := by
  obtain ⟨rnd, l, e, msg, hr, h⟩ := hD
  cases rnd with
  | rndBottom k m =>
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hr)
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    subst h1 h3 h4
    exact ⟨.inl (k, m), fun j hj ↦ h j hj⟩
  | rndTop k d =>
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hr)
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    subst h1 h3 h4
    exact ⟨.inr (k, d), fun j hj ↦ h j hj⟩
  | seed | param | prf | chain | leaf | node => cases hr

open scoped Classical in
/-- **The failure fraction**: `|rnd| · (1 - ρ_c)^(2^32)` over the tables, the codeword values a
fraction `ρ_c` of the trial cell's values. -/
theorem frac_failDbF_le (θ : HPos → Digest) :
    ((Finset.univ.filter fun t ↦ FailDbF θ (ofFunDbs t)).card : ℝ≥0∞) /
      Fintype.card ((HashDomain → HashOutput) × (HashOutput → HashDomain) ×
        (HashOutput → HashDomain)) ≤
      Fintype.card RndIdxF * ((((Finset.univ.filter fun y : HashOutput ↦
        ¬ Codeword.Valid (truncateHash y)).card ^ randomizerAttemptLimit : ℕ) : ℝ≥0∞) /
          ((Fintype.card HashOutput ^ randomizerAttemptLimit : ℕ) : ℝ≥0∞)) :=
  frac_union_fail_le (failCellF θ) (fun y : HashOutput ↦ ¬ Codeword.Valid (truncateHash y))
    randomizerAttemptLimit (failCellF_inj θ) _ fun t ht ↦ failDbF_cover θ (ofFunDbs t) ht

end count

/-! ## The bound -/

set_option exponentiation.threshold 4096 in
/-- The numbers: `2^32 (2^288 + 2^160) 2^-2048 ≤ 2^-1000`. -/
theorem reRev_numbers_le :
    (randomizerAttemptLimit : ℝ≥0∞) * (((2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (1 / 2 ^ 2048)) ≤ (2 ^ 1000 : ℝ≥0∞)⁻¹ := by
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

/-- **The repeated-reveal charges of the challenge prefix**: with at most `K` classical calls, at
most `K · 2^-1000`. -/
theorem totalWeight_reRevQW_le (A : Adversary) (θ : HPos → Digest) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K) :
    (runtimeR m0Q).totalWeight .instruments reRevQW (prefixQ A θ) initQ ≤
      K * (2 ^ 1000 : ℝ≥0∞)⁻¹ := by
  classical
  have hq := forallQueries_dec_moded m0Q (FInvF θ)
    (fun μ i r σ hok hσ ↦ fInvF_step μ i r σ hok hσ) LocalSig.Interp.instruments
    (prefixQ A θ) .free (modedP_prefixQ A θ) (init_fInvF θ)
  have h1 := totalWeight_le_of_forallQueries (runtimeR m0Q) .instruments
    (fun i σ ↦ ∃ μ, srchOkZ (θ paramC) μ i ∧
      QuerySupportedOn (fun m : (RSpec SelMem).In i × RReg SelMem ↦ m.2) (FInvF θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpec SelMem).In i) ((RSpec SelMem).In i) ℂ) ⊗ₖ
          compressReg HashOutput HashDomain QMem) σ)) (fun _ _ _ h ↦ h)
    (w' := fun i σ ↦ (randomizerAttemptLimit : ℝ≥0∞) *
      (((if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0 : ℕ) :
        ℝ≥0∞) * potential (hwDecProj (failSetF θ)) σ))
    (fun i σ hσ hok ↦ reRevQW_le_charge i σ hσ hok) (prefixQ A θ) initQ_posSemidef hq
  have h1' := h1.trans_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments
    (randomizerAttemptLimit : ℝ≥0∞) (fun i σ ↦
      ((if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0 : ℕ) :
        ℝ≥0∞) * potential (hwDecProj (failSetF θ)) σ) (prefixQ A θ) initQ)
  have h2 := totalWeight_charge_potential_le (runtimeR m0Q) .instruments
    (hwDecProj (failSetF θ))
    (fun i ↦ if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0)
    (PortCw (S := HPos) (M := SelMem) hwFixF)
    (fun i hi r ↦ runtimeR_commute_hwDecProj m0Q (offHw_failDbF θ) (failSetF θ)
      (fun _ ↦ Iff.rfl) i hi r)
    (fun _ _ _ h ↦ portCw_of_srchOkZ h.choose_spec.1) (prefixQ A θ) hK initQ_posSemidef hq
  have h3 : potential (hwDecProj (failSetF θ)) initQ ≤
      ((Finset.univ.filter fun t ↦ FailDbF θ (ofFunDbs t)).card : ℝ≥0∞) /
        Fintype.card ((HashDomain → HashOutput) × (HashOutput → HashDomain) ×
          (HashOutput → HashDomain)) := by
    refine (le_of_eq (potential_hwDecProj_init m0Q (failSetF θ) (FailDbF θ) (fun _ ↦ Iff.rfl)
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
  have h5 : potential (hwDecProj (failSetF θ)) initQ ≤
      ((2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 2048) := by
    refine (h3.trans (frac_failDbF_le θ)).trans ?_
    rw [card_not_codewordF, card_rndIdxF]
    exact mul_le_mul_of_nonneg_left h4 zero_le
  calc (runtimeR m0Q).totalWeight .instruments reRevQW (prefixQ A θ) initQ
      ≤ (randomizerAttemptLimit : ℝ≥0∞) * (K * potential (hwDecProj (failSetF θ)) initQ) :=
        h1'.trans (mul_le_mul_of_nonneg_left h2 zero_le)
    _ ≤ (randomizerAttemptLimit : ℝ≥0∞) * (K * (((2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128 : ℕ) :
        ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 2048))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 zero_le) zero_le
    _ = K * ((randomizerAttemptLimit : ℝ≥0∞) * (((2 ^ 32 * 2 ^ 256 + 2 ^ 32 * 2 ^ 128 : ℕ) :
        ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 2048))) := mul_left_comm _ _ _
    _ ≤ K * (2 ^ 1000 : ℝ≥0∞)⁻¹ := mul_le_mul_of_nonneg_left reRev_numbers_le zero_le

end Quantum.Qrom.Xmss

end
