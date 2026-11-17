module

public import Quantum.Qrom.Sphincs.Multi.Costs.Ports
public import Quantum.Qrom.Sphincs.Costs.EncRead

@[expose] public section

/-!
# The Enc potential of the `n`-user runtime 2 at one port

The `n`-user analog of `Quantum.Qrom.Sphincs` `Costs/EncRead`. The potential `encPotQSN pk` is the
number of codeword cells at the encoding slots of the unselected keys of all users, each cell
counted for its owner (`encCwCountN`); it is label free and `0` at the empty register.

* **Splitting at a read cell** (`encPotQSN_split`): at an encoding cell `z` of key `K` of its
  owner `i`, `encPotQSN` is the part of the other keys (`encOtherQSN`, kept by a trial read of
  `z`: `encOtherQSN_keep`), the unselected count of the key off `z` (`offCwQSN`) and the indicator
  of `z` holding a codeword pair with the key unselected (`cellQSN`).
* **A trial read** (`trialReadSN_drop`, `trialReadSN_potential_le`): as for one user, the count
  off `z` survives with the codeword fraction `ρ_c ≥ 2^-14` (`unselRead_dropQSN`), and the cell
  `z` costs re-compression and the recorded mass of the unselected key (`cellFlipQSN_le`).
* **The other ports**: a sponge call changes one database cell, which has at most one owner and
  one slot (`oneCellLipschitz_encPotQSN`); a program off the owners' encoding slots keeps the
  potential (`encPotQSN_progMap`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key Slot)
open Quantum.Xmss.Assembly (OffCell sqrtDiag re_sqrtDiag_conj_apply readKrausH_ne_zero_rest
  potential_diagPot_sqrt)
open Quantum.Qrom.Xmss (cellOutCount cellOutCount_congr cellOutCount_eq_off_add
  cellOutCount_le_card readKrausH_memQ splitH'_symm_cellG cellNoBot_sqrtDiagG dW_conj_sqrtDiagG
  posSemidef_sqrtDiag_conjG)

attribute [local irreducible] sphincsRom

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/- Instance search for the register with its trivial public register exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ} {pk : Fin n → PublicKey}

/-! ## Facts about the selections and the cells -/

/-- A trial read of key `(i, K)` keeps the selections of the other keys. -/
theorem cwUpdN_apply_key_of_ne {i : Fin n} {K : Key} (z : HashDomain) (m : SelMemN n)
    (o : Option PairOut) {κ : UKeyS n} (h : κ ≠ (i, K)) :
    cwUpdN i K z m o κ.1 κ.2 = m κ.1 κ.2 := by
  obtain ⟨j, K'⟩ := κ
  by_cases hj : j = i
  · subst hj
    have hK : K' ≠ K := fun hK ↦ h (by rw [hK])
    show cwUpdN j K z m o j K' = m j K'
    rw [cwUpdN, Function.update_self]
    exact cwUpd_apply_of_neE z (m j) o hK
  · exact congrFun (cwUpdN_apply_of_ne K z m o hj) K'

theorem trialUpdSN_unsel_iff {z : HashDomain} {i : Fin n} {K : Key} {m : QMemSN n}
    (hm : m.2 i K = none) (v : PairOut) :
    (trialUpdSN z (i, K) m (some v)).2 i K = none ↔
      ¬ Quantum.Sphincs.Codeword.Valid (pairDigest v) := by
  show cwUpdN i K z m.2 (some v) i K = none ↔ _
  rw [cwUpdN_some_of_none i K z hm v]
  exact cwSelN_eq_none_iff hm z v

theorem trialUpdSN_keep {z : HashDomain} {i : Fin n} {K : Key} {m : QMemSN n}
    (hm : m.2 i K ≠ none) (o : Option PairOut) : (trialUpdSN z (i, K) m o).2 i K ≠ none := by
  show cwUpdN i K z m.2 o i K ≠ none
  rw [cwUpdN, Function.update_self, cwUpd_of_ne_none hm]
  exact hm

/-- **An exempt cell is at no encoding slot of its owner.** -/
theorem not_enc_of_exemptCellSN {hon : Fin n → HonestCells} {z : HashDomain}
    (hz : ExemptCellN pk hon z) (i : Fin n) (K : Key) :
    ¬(ownerS pk z = some i ∧ slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2)) :=
  fun h ↦ not_enc_of_exemptCellE (hz i h.1) K h.2

theorem hw_none_of_encFreeSN {s : RRegSN n (SelMemN n)} (hM : EncFreeSN pk s)
    {x : HashDomain} {i : Fin n} {K : Key} (hx : slotOf (pk i) x = some (.enc K.1 K.2.1 K.2.2)) :
    s.2.1.1 x = none := by
  by_contra h
  exact hM x (Option.ne_none_iff_isSome.mp h) i K hx

/-! ## The potential -/

variable (pk) in
/-- **The Enc potential**: the codeword cells at the encoding slots of the unselected keys, each
cell counted for its owner. -/
noncomputable def encPotQSN (s : RRegSN n (SelMemN n)) : ℝ :=
  ∑ κ : UKeyS n, if memAtS s κ = none then (encCwCountN pk (unionH s) κ.1 κ.2 : ℝ) else 0

theorem encPotQSN_nonneg (s : RRegSN n (SelMemN n)) : 0 ≤ encPotQSN pk s :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity

variable (pk) in
/-- The potential of the keys other than `κ₀`. -/
noncomputable def encOtherQSN (κ₀ : UKeyS n) (s : RRegSN n (SelMemN n)) : ℝ :=
  ∑ κ ∈ Finset.univ.erase κ₀, if memAtS s κ = none then
    (encCwCountN pk (unionH s) κ.1 κ.2 : ℝ) else 0

variable (pk) in
/-- The codeword cells of user `i` at the encoding slot of key `K` other than `z`. -/
noncomputable def offCwQSN (z : HashDomain) (i : Fin n) (K : Key) (s : RRegSN n (SelMemN n)) :
    ℕ :=
  cellOutCount (unionH s)
    (fun x ↦ x ≠ z ∧ (ownerS pk x = some i ∧ slotOf (pk i) x = some (.enc K.1 K.2.1 K.2.2)))
    fun y ↦ Quantum.Sphincs.Codeword.Valid (pairDigest y)

/-- The cell `z` holds a codeword pair. -/
def CellCwQSN (z : HashDomain) (s : RRegSN n (SelMemN n)) : Prop :=
  ∃ y, unionH s z = some y ∧ Quantum.Sphincs.Codeword.Valid (pairDigest y)

/-- The states whose key `(i, K)` is unselected. -/
def unselQSN (i : Fin n) (K : Key) : Set (Unit × RRegSN n (SelMemN n)) :=
  {q | q.2.2.2.2 i K = none}

instance instDecidablePredUnselQSN (i : Fin n) (K : Key) :
    DecidablePred (· ∈ unselQSN i K) :=
  fun q ↦ inferInstanceAs (Decidable (q.2.2.2.2 i K = none))

/-- The states whose key `(i, K)` is unselected with a codeword pair at the cell `z`. -/
def cellQSN (z : HashDomain) (i : Fin n) (K : Key) : Set (Unit × RRegSN n (SelMemN n)) :=
  {q | q.2.2.2.2 i K = none ∧ CellCwQSN z q.2}

noncomputable instance instDecidablePredCellQSN (z : HashDomain) (i : Fin n) (K : Key) :
    DecidablePred (· ∈ cellQSN z i K) :=
  Classical.decPred _

theorem ind_unselQSN {i : Fin n} {K : Key} (q : Unit × RRegSN n (SelMemN n)) :
    ind (unselQSN i K) q = if q.2.2.2.2 i K = none then 1 else 0 :=
  rfl

variable {z : HashDomain} {i : Fin n} {K : Key}

open scoped Classical in
/-- The codeword cells of the key of `z` are those off `z` and the cell `z`. -/
theorem encCwCountN_eq_off_add (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2))
    (ho : ownerS pk z = some i) (s : RRegSN n (SelMemN n)) :
    (encCwCountN pk (unionH s) i K : ℝ) = offCwQSN pk z i K s +
      if CellCwQSN z s then 1 else 0 := by
  have h := cellOutCount_eq_off_add (unionH s)
    (fun x ↦ ownerS pk x = some i ∧ slotOf (pk i) x = some (.enc K.1 K.2.1 K.2.2))
    (fun y ↦ Quantum.Sphincs.Codeword.Valid (pairDigest y)) z
  change encCwCountN pk (unionH s) i K = offCwQSN pk z i K s + _ at h
  rw [h, Nat.cast_add]
  by_cases hc : CellCwQSN z s
  · rw [ite_eq_left ⟨⟨ho, hz⟩, hc⟩, ite_eq_left hc, Nat.cast_one]
  · rw [ite_eq_right fun h' ↦ hc h'.2, ite_eq_right hc, Nat.cast_zero]

/-- **The potential split at an encoding cell of its owner.** -/
theorem encPotQSN_split (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2))
    (ho : ownerS pk z = some i) (q : Unit × RRegSN n (SelMemN n)) :
    encPotQSN pk q.2 = encOtherQSN pk (i, K) q.2 + ind (unselQSN i K) q * offCwQSN pk z i K q.2 +
      ind (cellQSN z i K) q := by
  unfold encPotQSN encOtherQSN
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (i, K))]
  rw [ind_unselQSN]
  unfold ind
  by_cases hu : q.2.2.2.2 i K = none
  · have hu' : memAtS q.2 (i, K) = none := hu
    rw [ite_eq_left hu', ite_eq_left hu, encCwCountN_eq_off_add hz ho]
    by_cases hc : CellCwQSN z q.2
    · rw [ite_eq_left hc, ite_eq_left (show q ∈ cellQSN z i K from ⟨hu, hc⟩)]
      ring
    · rw [ite_eq_right hc, ite_eq_right (show q ∉ cellQSN z i K from fun h ↦ hc h.2)]
      ring
  · have hu' : ¬ memAtS q.2 (i, K) = none := hu
    rw [ite_eq_right hu', ite_eq_right hu,
      ite_eq_right (show q ∉ cellQSN z i K from fun h ↦ hu h.1)]
    ring

/-- The potential sees only the union view and the selections. -/
theorem encPotQSN_congr {s s' : RRegSN n (SelMemN n)} (hU : unionH s' = unionH s)
    (hm : s'.2.2.2 = s.2.2.2) : encPotQSN pk s' = encPotQSN pk s := by
  unfold encPotQSN memAtS
  rw [hU, hm]

/-- **Off the owners' encoding slots the potential sees nothing**: states agreeing off a cell `z`
that is no encoding-slot cell of its owner, with the same selections, have the same potential. -/
theorem encPotQSN_eq_of_off
    (hno : ∀ (i : Fin n) (K : Key),
      ¬(ownerS pk z = some i ∧ slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2)))
    {s s' : RRegSN n (SelMemN n)} (hU : ∀ x, x ≠ z → unionH s' x = unionH s x)
    (hm : s'.2.2.2 = s.2.2.2) : encPotQSN pk s' = encPotQSN pk s := by
  unfold encPotQSN
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  have hc : encCwCountN pk (unionH s') κ.1 κ.2 = encCwCountN pk (unionH s) κ.1 κ.2 :=
    cellOutCount_congr (D := HashDomain) (Y := PairOut)
      (P := fun x ↦ ownerS pk x = some κ.1 ∧
        slotOf (pk κ.1) x = some (.enc κ.2.1 κ.2.2.1 κ.2.2.2)) _
      fun x hx ↦ hU x fun hxz ↦ hno κ.1 κ.2 (hxz ▸ hx)
  unfold memAtS
  rw [hm, hc]

/-- The count off `z` does not see `z`. -/
theorem offCwQSN_congr {s s' : RRegSN n (SelMemN n)}
    (hU : ∀ x, x ≠ z → unionH s' x = unionH s x) :
    offCwQSN pk z i K s' = offCwQSN pk z i K s :=
  cellOutCount_congr _ fun x hx ↦ hU x hx.1

theorem unionH_congr_offSN {s s' : RRegSN n (SelMemN n)} (h1 : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b)
    (h3 : s'.2.1 = s.2.1) (x : HashDomain) (hx : x ≠ z) : unionH s' x = unionH s x := by
  rw [unionH_apply, unionH_apply, h3, h1 x hx]

/-- The count off `z` is a weight off the cell `z`. -/
theorem offCwQSN_offCell :
    OffCell z (fun s : RRegSN n (SelMemN n) ↦ (offCwQSN pk z i K s : ℝ)) := fun _ _ h1 _ h3 ↦
  congrArg Nat.cast (offCwQSN_congr (unionH_congr_offSN h1 h3))

/-- The potential of the other keys does not see `z` nor the selection of `(i, K)`. -/
theorem encOtherQSN_congr (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2))
    (ho : ownerS pk z = some i) {s s' : RRegSN n (SelMemN n)}
    (hU : ∀ x, x ≠ z → unionH s' x = unionH s x)
    (hm : ∀ κ : UKeyS n, κ ≠ (i, K) → memAtS s' κ = memAtS s κ) :
    encOtherQSN pk (i, K) s' = encOtherQSN pk (i, K) s := by
  unfold encOtherQSN
  refine Finset.sum_congr rfl fun κ hκ ↦ ?_
  have hκ' := Finset.ne_of_mem_erase hκ
  have hc : encCwCountN pk (unionH s') κ.1 κ.2 = encCwCountN pk (unionH s) κ.1 κ.2 :=
    cellOutCount_congr (D := HashDomain) (Y := PairOut)
      (P := fun x ↦ ownerS pk x = some κ.1 ∧
        slotOf (pk κ.1) x = some (.enc κ.2.1 κ.2.2.1 κ.2.2.2)) _
      fun x hx ↦ hU x fun hxz ↦ by
        subst hxz
        have hi := Option.some.inj (hx.1.symm.trans ho)
        obtain ⟨j, K'⟩ := κ
        dsimp only at hi hx
        subst hi
        obtain ⟨h1, h2, h3⟩ := Slot.enc.inj (Option.some.inj (hx.2.symm.trans hz))
        exact hκ' (Prod.ext rfl (Prod.ext h1 (Prod.ext h2 h3)))
  rw [hm κ hκ', hc]

/-- **A trial read keeps the potential of the other keys.** -/
theorem encOtherQSN_keep (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2))
    (ho : ownerS pk z = some i) (r : Option PairOut × QMemSN n)
    (a a' : Unit × RRegSN n (SelMemN n))
    (h : hwReadKraus (.readH z (trialUpdSN z (i, K))) r a' a ≠ 0) :
    encOtherQSN pk (i, K) a'.2 = encOtherQSN pk (i, K) a.2 := by
  obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
  obtain ⟨h1, -, h3⟩ := readKrausH_ne_zero_rest z (trialUpdSN z (i, K)) r h'
  obtain ⟨hm1, hm2⟩ := readKrausH_memQ z (trialUpdSN z (i, K)) r h'
  refine encOtherQSN_congr hz ho (unionH_congr_offSN h1 h3) fun κ hκ ↦ ?_
  unfold memAtS
  rw [hm2, hm1]
  exact cwUpdN_apply_key_of_ne z _ _ hκ

/-! ## The other ports -/

/-- **A sponge call changes the potential by at most one** (one database cell, of at most one
owner and slot). -/
theorem oneCellLipschitz_encPotQSN (pk : Fin n → PublicKey) :
    OneCellLipschitz (X := PairOut) (Z := HashDomain) (M := QMemSN n) (encPotQSN pk) where
  h D b x v := by
    set s : RRegSN n (SelMemN n) := (D, b)
    set s' : RRegSN n (SelMemN n) := ((Function.update D.1 x v, D.2.1, D.2.2), b)
    have hU : ∀ y, y ≠ x → unionH s' y = unionH s y := fun y hy ↦ by
      rw [unionH_apply, unionH_apply]
      show (b.1.1 y).or (Function.update D.1 x v y) = (b.1.1 y).or (D.1 y)
      rw [Function.update_of_ne hy]
    by_cases hx : ∃ (i : Fin n) (K : Key),
        ownerS pk x = some i ∧ slotOf (pk i) x = some (.enc K.1 K.2.1 K.2.2)
    · obtain ⟨i, K, ho, hx⟩ := hx
      have h1 := encPotQSN_split hx ho ((), s)
      have h2 := encPotQSN_split hx ho ((), s')
      have hA : encOtherQSN pk (i, K) s' = encOtherQSN pk (i, K) s :=
        encOtherQSN_congr hx ho hU fun _ _ ↦ rfl
      have hn : offCwQSN pk x i K s' = offCwQSN pk x i K s := offCwQSN_congr hU
      have hu : ind (unselQSN i K) ((), s') = ind (unselQSN i K) ((), s) := rfl
      have hc1 := ind_le_one (cellQSN x i K) ((), s')
      have hc0 := ind_nonneg (cellQSN x i K) ((), s)
      change encPotQSN pk s' ≤ encPotQSN pk s + 1
      rw [h1, h2, hA, hn, hu]
      linarith
    · exact (encPotQSN_eq_of_off (fun i K h ↦ hx ⟨i, K, h⟩) hU rfl).le.trans
        (le_add_of_nonneg_right zero_le_one)
  k D b x v := (encPotQSN_congr (s := (D, b)) rfl rfl).le.trans
    (le_add_of_nonneg_right zero_le_one)
  k' D b x v := (encPotQSN_congr (s := (D, b)) rfl rfl).le.trans
    (le_add_of_nonneg_right zero_le_one)

/-- **A program of a cell at no encoding slot of its owner keeps the potential.** -/
theorem encPotQSN_progMap
    (hno : ∀ (i : Fin n) (K : Key),
      ¬(ownerS pk z = some i ∧ slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2)))
    (a : PairOut) (s : RRegSN n (SelMemN n)) :
    encPotQSN pk (progMap (.programH z a) s) = encPotQSN pk s := by
  refine encPotQSN_eq_of_off hno (fun x hx ↦ ?_) rfl
  rw [unionH_apply, unionH_apply]
  show (Function.update s.2.1.1 z (some a) x).or (Function.update s.1.1 z none x) =
    (s.2.1.1 x).or (s.1.1 x)
  rw [Function.update_of_ne hx, Function.update_of_ne hx]

/-! ## The count off the read cell at a trial read -/

/-- **The flip values of the unselected-key event** at a rest: the key unselected and the digest
a codeword. -/
def CwFlipQSN (i : Fin n) (K : Key) (z : HashDomain) (y : PairOut)
    (r : RestH PairOut (QMemSN n) z) : Prop :=
  (memH z r).2 i K = none ∧ Quantum.Sphincs.Codeword.Valid (pairDigest y)

noncomputable instance instDecidableCwFlipQSN (i : Fin n) (K : Key) (z : HashDomain)
    (y : PairOut) (r : RestH PairOut (QMemSN n) z) : Decidable (CwFlipQSN i K z y r) :=
  Classical.propDecidable _

/-- The states a trial read selects from: the cell empty, the key unselected. -/
def EmptyUnselQSN (z : HashDomain) (i : Fin n) (K : Key) (s : RRegSN n (SelMemN n)) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z = none ∧ s.2.2.2 i K = none

noncomputable instance instDecidablePredEmptyUnselQSN (z : HashDomain) (i : Fin n) (K : Key) :
    DecidablePred (EmptyUnselQSN (n := n) z i K) :=
  Classical.decPred _

/-- The states whose read cell is recorded with a codeword pair, the key unselected. -/
def CwRecQSN (z : HashDomain) (i : Fin n) (K : Key) (s : RRegSN n (SelMemN n)) : Prop :=
  s.2.1.1 z = none ∧ s.2.2.2 i K = none ∧
    ∃ v, s.1.1 z = some v ∧ Quantum.Sphincs.Codeword.Valid (pairDigest v)

noncomputable instance instDecidablePredCwRecQSN (z : HashDomain) (i : Fin n) (K : Key) :
    DecidablePred (CwRecQSN (n := n) z i K) :=
  Classical.decPred _

theorem ind_unselQSN_symm (a : Option PairOut) (r : RestH PairOut (QMemSN n) z) :
    ind (unselQSN i K) ((splitH' z).symm (a, r)) = if (memH z r).2 i K = none then 1 else 0 :=
  rfl

/-- The weight of a recorded outcome against the unselected-key event. -/
theorem gw_unselQSN (y : PairOut) (r : RestH PairOut (QMemSN n) z) :
    gw (splitH' z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K) (some y) r =
      if (trialUpdSN z (i, K) (memH z r) (some y)).2 i K = none then 1 else 0 := by
  unfold gw
  have h : ∀ a : Option PairOut, ind (unselQSN i K)
      ((splitH' z).symm (a, tauH z (trialUpdSN z (i, K)) (some y) r)) =
      if (trialUpdSN z (i, K) (memH z r) (some y)).2 i K = none then 1 else 0 := fun a ↦ rfl
  simp only [h]
  rw [← Finset.sum_mul, sum_cr_sq, one_mul]

/-- **The diagonal cost of the unselected-key event**: `-ρ_c` on an empty, not hardwired cell
with the key unselected, at most `0` elsewhere. -/
theorem fd_unselQSN_le (q : Unit × RRegSN n (SelMemN n)) :
    fd (splitH' z) (actH z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K)
        (phiH z (trialUpdSN z (i, K))) q ≤
      -(Quantum.Sphincs.rhoCw * if EmptyUnselQSN z i K q.2 then 1 else 0) := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  unfold fd
  by_cases ha : actH z (splitH' z q).2
  · have ha' : q.2.2.1.1 z = none := ha
    rw [ite_eq_left ha, ind_unselQSN]
    rcases hc : (splitH' z q).1 with _ | y
    · have hc' : q.2.1.1 z = none := hc
      show (∑ y, gw (splitH' z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K) (some y)
          (splitH' z q).2) / Fintype.card PairOut - _ ≤ _
      simp only [gw_unselQSN, hmem]
      by_cases hm : q.2.2.2.2 i K = none
      · have hsum : (∑ y : PairOut, if (trialUpdSN z (i, K) q.2.2.2 (some y)).2 i K = none then
            (1 : ℝ) else 0) = Fintype.card PairOut -
              ((Finset.univ.filter fun v : PairOut ↦
                Quantum.Sphincs.Codeword.Valid (pairDigest v)).card : ℝ) := by
          rw [Finset.sum_congr rfl fun y _ ↦ if_congr (trialUpdSN_unsel_iff hm y) rfl rfl,
            Finset.sum_boole, Finset.filter_not, Finset.card_sdiff_of_subset
              (Finset.subset_univ _), Finset.card_univ, Nat.cast_sub (Finset.card_le_univ _)]
        have hN : (0 : ℝ) < Fintype.card PairOut := Nat.cast_pos.2 Fintype.card_pos
        have hE : EmptyUnselQSN z i K q.2 := ⟨ha', hc', hm⟩
        rw [hsum, sub_div, div_self hN.ne', card_codeword_pair_div, ite_eq_left hm,
          ite_eq_left hE]
        linarith
      · have h0 : ∀ y : PairOut, (trialUpdSN z (i, K) q.2.2.2 (some y)).2 i K ≠ none :=
          fun y ↦ trialUpdSN_keep hm _
        have hR : (if EmptyUnselQSN z i K q.2 then (1 : ℝ) else 0) = 0 :=
          ite_eq_right fun h ↦ hm h.2.2
        rw [hR, mul_zero, neg_zero, ite_eq_right hm]
        simp only [h0, ↓reduceIte, Finset.sum_const_zero, zero_div, sub_zero, le_refl]
    · have hc' : q.2.1.1 z ≠ none := by
        rw [← splitH'_apply_fst, hc]; exact Option.some_ne_none y
      show gw (splitH' z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K) (some y)
        (splitH' z q).2 - _ ≤ _
      have hR : (if EmptyUnselQSN z i K q.2 then (1 : ℝ) else 0) = 0 :=
        ite_eq_right fun h ↦ hc' h.2.1
      rw [hR, mul_zero, neg_zero, gw_unselQSN, hmem]
      by_cases hm : q.2.2.2.2 i K = none
      · rw [ite_eq_left hm]
        split_ifs <;> norm_num
      · rw [ite_eq_right hm, ite_eq_right (trialUpdSN_keep hm _), sub_zero]
  · have ha' : q.2.2.1.1 z ≠ none := ha
    have hR : (if EmptyUnselQSN z i K q.2 then (1 : ℝ) else 0) = 0 :=
      ite_eq_right fun h ↦ ha' h.1
    rw [ite_eq_right ha, ind_unselQSN, ind_unselQSN, hR, mul_zero, neg_zero]
    show (if (trialUpdSN z (i, K) q.2.2.2 (q.2.2.1.1 z)).2 i K = none then (1 : ℝ) else 0) - _ ≤ 0
    by_cases hm : q.2.2.2.2 i K = none
    · rw [ite_eq_left hm]
      split_ifs <;> norm_num
    · rw [ite_eq_right hm, ite_eq_right (trialUpdSN_keep hm _), sub_zero]

/-- **The empty-to-recorded weight of the unselected-key event** with the reference `q0`: `ρ_c`
on an empty, not hardwired cell with the key unselected, `0` elsewhere. -/
theorem ew_unselQSN_le (q : Unit × RRegSN n (SelMemN n)) :
    ew (splitH' z) (actH z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K)
        (q0 (splitH' z) (unselQSN i K)) q ≤
      Quantum.Sphincs.rhoCw * if EmptyUnselQSN z i K q.2 then 1 else 0 := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  unfold ew
  split_ifs with h1 h2 h2
  · have hN : (0 : ℝ) < Fintype.card PairOut := Nat.cast_pos.2 Fintype.card_pos
    have hq0 : q0 (splitH' z) (unselQSN i K) (splitH' z q).2 = 1 := by
      unfold q0
      rw [ind_unselQSN_symm, hmem, ite_eq_left h2.2.2]
    have hterm : ∀ y : PairOut, xv (splitH' z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K)
        (q0 (splitH' z) (unselQSN i K)) (some y) (splitH' z q).2 ^ 2 =
        (if Quantum.Sphincs.Codeword.Valid (pairDigest y) then 1 else 0) /
          Fintype.card PairOut :=
      fun y ↦ by
        have hsq : ((if ¬ Quantum.Sphincs.Codeword.Valid (pairDigest y) then (1 : ℝ) else 0) -
            1) ^ 2 = if Quantum.Sphincs.Codeword.Valid (pairDigest y) then 1 else 0 := by
          split_ifs <;> norm_num
        show ((gw (splitH' z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K) (some y)
          (splitH' z q).2 - q0 (splitH' z) (unselQSN i K) (splitH' z q).2) /
            Real.sqrt (Fintype.card PairOut)) ^ 2 = _
        rw [hq0, gw_unselQSN, hmem, if_congr (trialUpdSN_unsel_iff h2.2.2 y) rfl rfl, div_pow,
          Real.sq_sqrt hN.le, hsq]
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, ← Finset.sum_div, Finset.sum_boole,
      card_codeword_pair_div, mul_one]
  · have hm : q.2.2.2.2 i K ≠ none := fun hm ↦
      h2 (And.intro h1.1 (And.intro h1.2 hm) : EmptyUnselQSN z i K q.2)
    have hq0 : q0 (splitH' z) (unselQSN i K) (splitH' z q).2 = 0 := by
      unfold q0
      rw [ind_unselQSN_symm, hmem, ite_eq_right hm]
    have hterm : ∀ y : PairOut, xv (splitH' z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K)
        (q0 (splitH' z) (unselQSN i K)) (some y) (splitH' z q).2 ^ 2 = 0 := fun y ↦ by
      show ((gw (splitH' z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K) (some y)
        (splitH' z q).2 - q0 (splitH' z) (unselQSN i K) (splitH' z q).2) /
          Real.sqrt (Fintype.card PairOut)) ^ 2 = _
      rw [hq0, gw_unselQSN, hmem, ite_eq_right (trialUpdSN_keep hm (some y)), sub_self,
        zero_div]
      exact zero_pow two_ne_zero
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, Finset.sum_const_zero, mul_zero]
  · exact absurd ⟨h2.1, h2.2.1⟩ h1
  · rw [mul_zero]

/-- The cross term's support: the recorded cells of the flip values are codeword-recorded for
the unselected key. -/
theorem pd_cwFlipQSN_le (q : Unit × RRegSN n (SelMemN n)) :
    pd (splitH' z) (actH z) (CwFlipQSN i K z) q ≤ if CwRecQSN z i K q.2 then 1 else 0 := by
  classical
  unfold pd
  split_ifs with h1 h2
  · rcases hc : (splitH' z q).1 with _ | y
    · simp
    · simp only [Option.elim_some]
      split_ifs <;> norm_num
  · rcases hc : (splitH' z q).1 with _ | y
    · simp
    · simp only [Option.elim_some]
      split_ifs with h3
      · exfalso
        have hc' : q.2.1.1 z = some y := hc
        exact h2 (And.intro h1 (And.intro h3.1 ⟨y, hc', h3.2⟩) : CwRecQSN z i K q.2)
      · exact le_rfl
  · norm_num
  · exact le_rfl

/-- Off the flip values a recorded outcome weighs the reference weight `q0`. -/
theorem gw_eq_q0_of_not_cwFlipQSN (r : RestH PairOut (QMemSN n) z) (y : PairOut)
    (hy : ¬ CwFlipQSN i K z y r) :
    gw (splitH' z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K) (some y) r =
      q0 (splitH' z) (unselQSN i K) r := by
  unfold q0
  rw [gw_unselQSN, ind_unselQSN_symm]
  by_cases hm : (memH z r).2 i K = none
  · rw [ite_eq_left hm, ite_eq_left ((trialUpdSN_unsel_iff hm y).2 fun hv ↦ hy ⟨hm, hv⟩)]
  · rw [ite_eq_right hm, ite_eq_right (trialUpdSN_keep hm _)]

/-- The unselected `w`-weighted mass is the event weight of `W σ W`. -/
theorem re_trace_indProj_sqrtDiagQSN {w : RRegSN n (SelMemN n) → ℝ} (hw0 : ∀ s, 0 ≤ w s)
    (σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ) :
    (indProj (unselQSN i K) * (sqrtDiag w * σ * sqrtDiag w)).trace.re =
      dW (fun q ↦ ind (unselQSN i K) q * w q.2) σ := by
  rw [indProj, re_trace_diagonal_mul]
  unfold dW
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [re_sqrtDiag_conj_apply hw0]
  exact (mul_assoc _ _ _).symm

/-- The unselected `w`-weighted mass after a trial read: the mass before plus the flip of the
unselected-key event on `W σ W`. -/
theorem unsel_post_eqQSN {w : RRegSN n (SelMemN n) → ℝ} (hw0 : ∀ s, 0 ≤ w s) (hw : OffCell z w)
    (σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ) :
    ∑ r : Option PairOut × QMemSN n, dW (fun q ↦ ind (unselQSN i K) q * w q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r) σ) =
      dW (fun q ↦ ind (unselQSN i K) q * w q.2) σ +
        (flipOp (fun r : Option PairOut × QMemSN n ↦
          hwReadKraus (.readH z (trialUpdSN z (i, K))) r)
          (unselQSN i K) * (sqrtDiag w * σ * sqrtDiag w)).trace.re := by
  have h1 : ∀ r, dW (fun q ↦ ind (unselQSN i K) q * w q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r) σ) =
      dW (fun q ↦ ind (unselQSN i K) q)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r)
          (sqrtDiag w * σ * sqrtDiag w)) :=
    fun r ↦ (dW_conj_sqrtDiagG z (trialUpdSN z (i, K)) hw0 hw
      (fun q ↦ ind (unselQSN i K) q) r σ).symm
  have hsumeq : (∑ r : Option PairOut × QMemSN n,
      (hwReadKraus (.readH z (trialUpdSN z (i, K))) r)ᴴ *
        diagonal (fun q ↦ ((ind (unselQSN i K) q : ℝ) : ℂ)) *
          hwReadKraus (.readH z (trialUpdSN z (i, K))) r) =
      flipOp (fun r : Option PairOut × QMemSN n ↦ hwReadKraus (.readH z (trialUpdSN z (i, K))) r)
        (unselQSN i K) + indProj (unselQSN i K) := by
    rw [flipOp, sub_add_cancel]
    rfl
  rw [Finset.sum_congr rfl fun r _ ↦ h1 r, sum_dW_conj, hsumeq, Matrix.add_mul,
    Matrix.trace_add, Complex.add_re, add_comm, re_trace_indProj_sqrtDiagQSN hw0 σ]

/-- **The flip of the unselected-key event at a trial read, `w`-weighted**: at most
`-ρ_c e + 2 √(ρ_c e p)`, `e` the `w`-weighted `EmptyUnselQSN` mass and `p` the `w`-weighted
`CwRecQSN` mass. -/
theorem unselFlipQSN_le {w : RRegSN n (SelMemN n) → ℝ} (hw0 : ∀ s, 0 ≤ w s) (hw : OffCell z w)
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option PairOut × QMemSN n ↦
        hwReadKraus (.readH z (trialUpdSN z (i, K))) r)
        (unselQSN i K) * (sqrtDiag w * σ * sqrtDiag w)).trace.re ≤
      -(Quantum.Sphincs.rhoCw *
          ∑ q, (if EmptyUnselQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re)) +
        2 * √(Quantum.Sphincs.rhoCw *
          (∑ q, (if EmptyUnselQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re)) *
            ∑ q, (if CwRecQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re)) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hτ : (sqrtDiag w * σ * sqrtDiag w).PosSemidef := posSemidef_sqrtDiag_conjG w hσ
  have hdiag : ∀ q, ((sqrtDiag w * σ * sqrtDiag w) q q).re = w q.2 * (σ q q).re :=
    re_sqrtDiag_conj_apply hw0 σ
  have hwσ : ∀ q, 0 ≤ w q.2 * (σ q q).re := fun q ↦ mul_nonneg (hw0 _) (hre q)
  have hF := re_trace_flipOp_le (unselQSN i K) (cellRead_readH z (trialUpdSN z (i, K)))
    (clsOff_readH z (trialUpdSN z (i, K))) (q0 (splitH' z) (unselQSN i K)) (CwFlipQSN i K z)
    (fun r _ y hy ↦ gw_eq_q0_of_not_cwFlipQSN r y hy) hτ (cellNoBot_sqrtDiagG hw hnb)
  have he : 0 ≤ ∑ q, (if EmptyUnselQSN z i K q.2 then (1 : ℝ) else 0) * (w q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hwσ q)
  have hfd : ∑ s, fd (splitH' z) (actH z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K)
      (phiH z (trialUpdSN z (i, K))) s * ((sqrtDiag w * σ * sqrtDiag w) s s).re ≤
      -(Quantum.Sphincs.rhoCw *
        ∑ q, (if EmptyUnselQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (fd_unselQSN_le q) (hwσ q)).trans_eq (by ring)
  have hew : ∑ s, ew (splitH' z) (actH z) (tauH z (trialUpdSN z (i, K))) (unselQSN i K)
      (q0 (splitH' z) (unselQSN i K)) s * ((sqrtDiag w * σ * sqrtDiag w) s s).re ≤
      Quantum.Sphincs.rhoCw *
        ∑ q, (if EmptyUnselQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (ew_unselQSN_le q) (hwσ q)).trans_eq (by ring)
  have hpd : ∑ s, pd (splitH' z) (actH z) (CwFlipQSN i K z) s *
      ((sqrtDiag w * σ * sqrtDiag w) s s).re ≤
      ∑ q, (if CwRecQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re) :=
    Finset.sum_le_sum fun q _ ↦ by
      rw [hdiag]
      exact mul_le_mul_of_nonneg_right (pd_cwFlipQSN_le q) (hwσ q)
  have hP0 : 0 ≤ ∑ s, pd (splitH' z) (actH z) (CwFlipQSN i K z) s *
      ((sqrtDiag w * σ * sqrtDiag w) s s).re :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      rcases pd_mem (e := splitH' z) (act := actH z) (CwFlipQSN i K z) q with h | h <;>
        simp only [h, le_refl, zero_le_one]) (by rw [hdiag]; exact hwσ q)
  refine hF.trans (add_le_add hfd (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
  rw [← Real.sqrt_mul' _ hP0]
  exact Real.sqrt_le_sqrt (mul_le_mul hew hpd hP0 (mul_nonneg rhoCw_nonnegE he))

/-- **The unselected count off the read cell at a trial read**: `2^-15 e` plus the
`w`-weighted unselected mass after the read is at most the one before plus `3 p`. -/
theorem unselRead_dropQSN {w : RRegSN n (SelMemN n) → ℝ} (hw0 : ∀ s, 0 ≤ w s)
    (hw : OffCell z w)
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 15 : ℝ)⁻¹ * (∑ q, (if EmptyUnselQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re)) +
      ∑ r : Option PairOut × QMemSN n, dW (fun q ↦ ind (unselQSN i K) q * w q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r) σ) ≤
    dW (fun q ↦ ind (unselQSN i K) q * w q.2) σ +
      3 * ∑ q, (if CwRecQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hwσ : ∀ q, 0 ≤ w q.2 * (σ q q).re := fun q ↦ mul_nonneg (hw0 _) (hre q)
  refine drop_of_surviveE (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num)
    (hwσ q)) (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hwσ q))
    Quantum.Sphincs.inv_two_pow_14_le_rhoCw ?_
  rw [unsel_post_eqQSN hw0 hw σ]
  have h := unselFlipQSN_le (i := i) (K := K) hw0 hw hσ hnb
  have hp : 0 ≤ ∑ q, (if CwRecQSN z i K q.2 then (1 : ℝ) else 0) * (w q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hwσ q)
  linarith

/-! ## The read cell at a trial read -/

/-- The outcome states of a trial read are outside `cellQSN`: a codeword pair selects the key. -/
theorem not_mem_cellQSN_out {r : RestH PairOut (QMemSN n) z} (hr : actH z r) (y : PairOut) :
    (splitH' z).symm (some y, tauH z (trialUpdSN z (i, K)) (some y) r) ∉ cellQSN z i K := by
  rintro ⟨hu, y', hy', hcw⟩
  have hw : ((splitH' z).symm (some y, tauH z (trialUpdSN z (i, K)) (some y) r)).2.2.1.1 z =
      none := hr
  rw [unionH_apply, hw, splitH'_symm_cellG] at hy'
  obtain rfl := Option.some.inj hy'
  have hu' : (trialUpdSN z (i, K) (memH z r) (some y)).2 i K = none := hu
  by_cases hm : (memH z r).2 i K = none
  · exact (trialUpdSN_unsel_iff hm y).1 hu' hcw
  · exact trialUpdSN_keep hm _ hu'

/-- The classical move of a hardwired cell leaves `cellQSN`. -/
theorem not_mem_cellQSN_phiH (q : Unit × RRegSN n (SelMemN n)) (hq : q.2.2.1.1 z ≠ none) :
    phiH z (trialUpdSN z (i, K)) q ∉ cellQSN z i K := by
  rintro ⟨hu, y', hy', hcw⟩
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hq
  have hy2 : (q.2.2.1.1 z).or (q.2.1.1 z) = some y' := hy'
  rw [hw] at hy2
  obtain rfl := Option.some.inj hy2
  have hu' : (trialUpdSN z (i, K) q.2.2.2 (some w)).2 i K = none := by
    have h := hu
    change (trialUpdSN z (i, K) q.2.2.2 (q.2.2.1.1 z)).2 i K = none at h
    rwa [hw] at h
  by_cases hm : q.2.2.2.2 i K = none
  · exact (trialUpdSN_unsel_iff hm w).1 hu' hcw
  · exact trialUpdSN_keep hm _ hu'

/-- **The read cell after a trial read**: the flip into `cellQSN` is at most `2/|Y| + 4/|Y|²` per
unit of trace plus the recorded mass of the unselected key at the cell. -/
theorem cellFlipQSN_le
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option PairOut × QMemSN n ↦
        hwReadKraus (.readH z (trialUpdSN z (i, K))) r)
        (cellQSN z i K) * σ).trace.re ≤
      ∑ q, ((2 / (Fintype.card PairOut : ℝ) + (2 / (Fintype.card PairOut : ℝ)) ^ 2) +
        (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i K = none then 1 else 0)) *
          (σ q q).re := by
  classical
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set DU : PairOut → RestH PairOut (QMemSN n) z → Prop := fun _ r ↦ (memH z r).2 i K = none
  have hD : ∀ r, actH z r → ∀ y, ¬ DU y r →
      gw (splitH' z) (tauH z (trialUpdSN z (i, K))) (cellQSN z i K) (some y) r = 0 := by
    intro r _ y hy
    unfold gw
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [ind_eq_zero_of_not_mem (cellQSN z i K) fun h ↦ trialUpdSN_keep hy (some y) h.1,
      mul_zero]
  have hF := re_trace_flipOp_le (cellQSN z i K) (cellRead_readH z (trialUpdSN z (i, K)))
    (clsOff_readH z (trialUpdSN z (i, K))) (fun _ ↦ 0) DU hD hσ hnb
  set N : ℝ := (Fintype.card PairOut : ℝ)
  set E := ∑ s, ew (splitH' z) (actH z) (tauH z (trialUpdSN z (i, K))) (cellQSN z i K)
    (fun _ ↦ 0) s * (σ s s).re
  set p := ∑ s, pd (splitH' z) (actH z) DU s * (σ s s).re
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ ↦ mul_nonneg (by
    unfold ew
    split_ifs
    · exact Finset.sum_nonneg fun y _ ↦ sq_nonneg _
    · exact le_rfl) (hre s)
  have hp : 0 ≤ p := Finset.sum_nonneg fun s _ ↦ mul_nonneg (by
    rcases pd_mem (e := splitH' z) (act := actH z) DU s with h0 | h0 <;> rw [h0]; norm_num)
    (hre s)
  have hsq : 2 * (√E * √p) ≤ E + p := by
    nlinarith [sq_nonneg (√E - √p), Real.sq_sqrt hE, Real.sq_sqrt hp]
  have hgw : ∀ s : Unit × RRegSN n (SelMemN n), actH z (splitH' z s).2 → ∀ y,
      gw (splitH' z) (tauH z (trialUpdSN z (i, K))) (cellQSN z i K) (some y)
        (splitH' z s).2 ≤ 2 / N :=
    fun s ha y ↦ gw_some_le_two_div (cellQSN z i K)
      (ind_eq_zero_of_not_mem (cellQSN z i K) (not_mem_cellQSN_out ha y))
  have hpt : ∀ s, fd (splitH' z) (actH z) (tauH z (trialUpdSN z (i, K))) (cellQSN z i K)
      (phiH z (trialUpdSN z (i, K))) s + ew (splitH' z) (actH z)
        (tauH z (trialUpdSN z (i, K))) (cellQSN z i K) (fun _ ↦ 0) s ≤
        2 / N + (2 / N) ^ 2 := fun s ↦ by
    refine add_le_add ?_ ?_
    · unfold fd
      split_ifs with ha
      · exact (sub_le_self _ (ind_nonneg _ s)).trans (gdiag_le_of _ (hgw s ha) _)
      · rw [ind_eq_zero_of_not_mem (cellQSN z i K) (not_mem_cellQSN_phiH s ha), zero_sub]
        exact (neg_nonpos.2 (ind_nonneg _ s)).trans (by positivity)
    · by_cases ha : actH z (splitH' z s).2
      · exact ew_zero_le_of _ (hgw s ha)
      · unfold ew
        rw [ite_eq_right fun h' ↦ ha h'.1]
        positivity
  have hpd : ∀ s : Unit × RRegSN n (SelMemN n), pd (splitH' z) (actH z) DU s ≤
      if s.2.2.1.1 z = none ∧ s.2.1.1 z ≠ none ∧ s.2.2.2.2 i K = none then 1 else 0 := by
    intro s
    unfold pd
    split_ifs with h1 h2
    · rcases hc : (splitH' z s).1 with _ | y
      · simp
      · simp only [Option.elim_some]
        split_ifs <;> norm_num
    · rcases hc : (splitH' z s).1 with _ | y
      · simp
      · simp only [Option.elim_some]
        split_ifs with h3
        · exfalso
          have hc' : s.2.1.1 z = some y := hc
          exact h2 ⟨h1, by rw [hc']; exact Option.some_ne_none y, h3⟩
        · exact le_rfl
    · norm_num
    · exact le_rfl
  calc _ ≤ ∑ s, fd (splitH' z) (actH z) (tauH z (trialUpdSN z (i, K))) (cellQSN z i K)
        (phiH z (trialUpdSN z (i, K))) s * (σ s s).re + (E + p) :=
        hF.trans (add_le_add le_rfl hsq)
    _ = ∑ s, (fd (splitH' z) (actH z) (tauH z (trialUpdSN z (i, K))) (cellQSN z i K)
          (phiH z (trialUpdSN z (i, K))) s + ew (splitH' z) (actH z)
            (tauH z (trialUpdSN z (i, K))) (cellQSN z i K) (fun _ ↦ 0) s +
              pd (splitH' z) (actH z) DU s) * (σ s s).re := by
        simp only [E, p, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right
        (add_le_add (hpt s) (hpd s)) (hre s)

/-! ## A trial read -/

/-- **The database count of the codeword cells off `z`** at a recorded read cell of a
`EncFreeSN` register: one less than the recorded cells, at most. -/
theorem offCwQSN_add_one_le {s : RRegSN n (SelMemN n)} (hM : EncFreeSN pk s)
    (hD : s.1.1 z ≠ none) : offCwQSN pk z i K s + 1 ≤ s.1.1.size := by
  have h1 : offCwQSN pk z i K s ≤
      (Finset.univ.filter fun x ↦ x ≠ z ∧ (s.1.1 x).isSome).card := by
    refine cellOutCount_le_card _ fun x y hx hy ↦ ⟨hx.1, ?_⟩
    have hw : s.2.1.1 x = none := hw_none_of_encFreeSN hM hx.2.2
    rw [unionH_apply, hw] at hy
    change s.1.1 x = some y at hy
    rw [hy]
    rfl
  have h2 := card_filter_eq_off_add (fun x ↦ (s.1.1 x).isSome) z
  rw [ite_eq_left (Option.ne_none_iff_isSome.mp hD)] at h2
  have h3 : s.1.1.size = (Finset.univ.filter fun x ↦ (s.1.1 x).isSome).card := rfl
  omega

open scoped Classical in
/-- **A trial read on the potential, in `ℝ`**: on states supported on `EncFreeSN` registers of
database grade at most `G`, with no decompressed `⊥` at the cell, `2^-15 encWtSN` plus the
potential after the read is at most the potential before plus `4 G recUWtSN + 2^-510 tr σ`. -/
theorem trialReadSN_drop (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2))
    (ho : ownerS pk z = some i) {G : ℕ}
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ)
    (hinv : ∀ q, σ q q ≠ 0 → EncFreeSN pk q.2 ∧ dbGrade q.2.1 ≤ G) :
    (2 ^ 15 : ℝ)⁻¹ * (∑ q, encWtSN pk z (i, K) q.2 * (σ q q).re) +
        ∑ r : Option PairOut × QMemSN n, dW (fun q ↦ encPotQSN pk q.2)
          (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r) σ) ≤
      dW (fun q ↦ encPotQSN pk q.2) σ + 4 * G * (∑ q, recUWtSN z (i, K) q.2 * (σ q q).re) +
        (2 ^ 510 : ℝ)⁻¹ * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set w : RRegSN n (SelMemN n) → ℝ := fun s ↦ (offCwQSN pk z i K s : ℝ)
  have hw0 : ∀ s, 0 ≤ w s := fun s ↦ Nat.cast_nonneg _
  have hsplit : (fun q : Unit × RRegSN n (SelMemN n) ↦ encPotQSN pk q.2) = fun q ↦
      (fun q ↦ encOtherQSN pk (i, K) q.2 + ind (unselQSN i K) q * w q.2) q +
        ind (cellQSN z i K) q :=
    funext fun q ↦ encPotQSN_split hz ho q
  have hdW : ∀ τ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ,
      dW (fun q ↦ encPotQSN pk q.2) τ = dW (fun q ↦ encOtherQSN pk (i, K) q.2) τ +
        dW (fun q ↦ ind (unselQSN i K) q * w q.2) τ + dW (ind (cellQSN z i K)) τ :=
    fun τ ↦ by rw [hsplit, dW_add, dW_add]
  simp only [hdW, Finset.sum_add_distrib]
  -- The other keys keep their part.
  have hA : ∑ r : Option PairOut × QMemSN n, dW (fun q ↦ encOtherQSN pk (i, K) q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r) σ) =
      dW (fun q ↦ encOtherQSN pk (i, K) q.2) σ :=
    sum_dW_conj_of_keep (fun r : Option PairOut × QMemSN n ↦
      hwReadKraus (.readH z (trialUpdSN z (i, K))) r) _ (encOtherQSN_keep hz ho)
      (sum_readKrausH z (trialUpdSN z (i, K))) σ
  -- The count off the cell.
  have hB := unselRead_dropQSN (i := i) (K := K) hw0 offCwQSN_offCell hσ hnb
  -- The cell itself.
  have hCeq : ∑ r : Option PairOut × QMemSN n, dW (ind (cellQSN z i K))
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r) σ) =
      dW (ind (cellQSN z i K)) σ + (flipOp (fun r : Option PairOut × QMemSN n ↦
        hwReadKraus (.readH z (trialUpdSN z (i, K))) r) (cellQSN z i K) * σ).trace.re := by
    rw [sum_dW_conj, dW_eq_trace, flipOp, indProj, Matrix.sub_mul, Matrix.trace_sub,
      Complex.sub_re]
    ring
  have hC := cellFlipQSN_le (i := i) (K := K) hσ hnb
  -- The Enc weight is the weight of the empty reads.
  have hEnc : ∑ q, encWtSN pk z (i, K) q.2 * (σ q q).re =
      ∑ q, (if EmptyUnselQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re) := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp [h0]
    have hW : q.2.2.1.1 z = none := hw_none_of_encFreeSN (hinv q h0).1 hz
    unfold encWtSN
    dsimp only
    by_cases hE : q.2.1.1 z = none ∧ memAtS q.2 (i, K) = none
    · have hc : ¬ CellCwQSN z q.2 := by
        rintro ⟨y, hy, -⟩
        rw [unionH_apply, hW, hE.1] at hy
        cases hy
      rw [ite_eq_left hE, ite_eq_left (show EmptyUnselQSN z i K q.2 from ⟨hW, hE⟩),
        encCwCountN_eq_off_add hz ho, ite_eq_right hc, add_zero, one_mul]
    · rw [ite_eq_right hE, ite_eq_right fun h ↦ hE ⟨h.2.1, h.2.2⟩]
      ring
  -- The recorded charges.
  have hRec : 3 * (∑ q, (if CwRecQSN z i K q.2 then 1 else 0) * (w q.2 * (σ q q).re)) +
      ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i K = none then 1 else 0) *
        (σ q q).re ≤ 4 * G * (∑ q, recUWtSN z (i, K) q.2 * (σ q q).re) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp [h0]
    obtain ⟨hM, hG⟩ := hinv q h0
    by_cases hR : q.2.1.1 z ≠ none ∧ q.2.2.2.2 i K = none
    · have hU : recUWtSN z (i, K) q.2 = 1 := ite_eq_left hR
      have hsz := offCwQSN_add_one_le (pk := pk) (i := i) (K := K) hM hR.1
      have hgr : Database.size q.2.1.1 ≤ G := (le_max_left _ _).trans hG
      have hwG : w q.2 + 1 ≤ G := by
        show (offCwQSN pk z i K q.2 : ℝ) + 1 ≤ G
        exact_mod_cast hsz.trans hgr
      have h1 : (if CwRecQSN z i K q.2 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have h2 : (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i K = none then
          (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      rw [hU]
      have hw := hw0 q.2
      have hq := hre q
      have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
      have h3 : 3 * ((if CwRecQSN z i K q.2 then (1 : ℝ) else 0) * (w q.2 * (σ q q).re)) ≤
          3 * (w q.2 * (σ q q).re) := by
        have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hw hq)
        linarith
      have h4 := mul_le_mul_of_nonneg_right h2 hq
      have h5 : (3 * w q.2 + 1) * (σ q q).re ≤ 4 * G * (σ q q).re :=
        mul_le_mul_of_nonneg_right (by linarith) hq
      linarith
    · have hc : ¬ CwRecQSN z i K q.2 := fun h ↦ hR ⟨by
        obtain ⟨v, hv, -⟩ := h.2.2
        rw [hv]
        exact Option.some_ne_none v, h.2.1⟩
      rw [ite_eq_right hc, ite_eq_right fun h ↦ hR ⟨h.2.1, h.2.2⟩]
      have hU0 : 0 ≤ recUWtSN z (i, K) q.2 := by
        unfold recUWtSN
        exact ite_nonneg zero_le_one le_rfl
      simp only [zero_mul, mul_zero, add_zero]
      exact mul_nonneg (by positivity) (mul_nonneg hU0 (hre q))
  -- The re-compression term.
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have hCsum : ∑ q, ((2 / (Fintype.card PairOut : ℝ) +
      (2 / (Fintype.card PairOut : ℝ)) ^ 2) +
        (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i K = none then 1 else 0)) *
          (σ q q).re = (2 / (Fintype.card PairOut : ℝ) +
            (2 / (Fintype.card PairOut : ℝ)) ^ 2) * σ.trace.re +
        ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i K = none then 1 else 0) *
          (σ q q).re := by
    rw [htr, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ ↦ by ring
  have htr0 : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have hδt := mul_le_mul_of_nonneg_right recompress_leE htr0
  rw [hEnc]
  rw [hCsum] at hC
  generalize (2 ^ 510 : ℝ)⁻¹ = ε at hδt ⊢
  linarith

/-- **A trial read on the potential**: the port condition of the joint potential argument, in
`ℝ≥0∞`. -/
theorem trialReadSN_potential_le (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2))
    (ho : ownerS pk z = some i) {G : ℕ}
    {σ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ)
    (hinv : ∀ q, σ q q ≠ 0 → EncFreeSN pk q.2 ∧ dbGrade q.2.1 ≤ G) :
    (2 ^ 15 : ℝ≥0∞)⁻¹ * trialWSN (encWtSN pk) (trialReadSN z (i, K)) σ +
        ∑' r, potential (diagPot fun s ↦ √(encPotQSN pk s))
          (MatrixMap.conj (hwReadKraus (trialReadSN z (i, K)) r) σ) ≤
      potential (diagPot fun s ↦ √(encPotQSN pk s)) σ +
        (4 * (G : ℝ≥0∞) * trialWSN recUWtSN (trialReadSN z (i, K)) σ +
          (2 ^ 510 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hpot : ∀ τ : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ,
      potential (diagPot fun s ↦ √(encPotQSN pk s)) τ =
        ENNReal.ofReal (dW (fun q ↦ encPotQSN pk q.2) τ) :=
    fun τ ↦ potential_diagPot_sqrt encPotQSN_nonneg τ
  have hpost : ∀ r, 0 ≤ dW (fun q : Unit × RRegSN n (SelMemN n) ↦ encPotQSN pk q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r) σ) := fun r ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPotQSN_nonneg q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  have hE0 : 0 ≤ ∑ q, encWtSN pk z (i, K) q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
    mul_nonneg (by unfold encWtSN; split_ifs <;> positivity) (hre q)
  have hU0 : 0 ≤ ∑ q, recUWtSN z (i, K) q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
    mul_nonneg (by unfold recUWtSN; split_ifs <;> norm_num) (hre q)
  have hP0 : 0 ≤ dW (fun q : Unit × RRegSN n (SelMemN n) ↦ encPotQSN pk q.2) σ :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPotQSN_nonneg q.2) (hre q)
  have htr0 : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have key := trialReadSN_drop hz ho hσ hnb hinv
  rw [trialWSN_trialReadSN, trialWSN_trialReadSN, hpot]
  simp only [trialReadSN]
  simp only [hpot]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hpost r]
  calc (2 ^ 15 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ q, encWtSN pk z (i, K) q.2 * (σ q q).re) +
        ENNReal.ofReal (∑ r : Option PairOut × QMemSN n, dW (fun q ↦ encPotQSN pk q.2)
          (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r) σ))
      = ENNReal.ofReal ((2 ^ 15 : ℝ)⁻¹ * (∑ q, encWtSN pk z (i, K) q.2 * (σ q q).re) +
          ∑ r : Option PairOut × QMemSN n, dW (fun q ↦ encPotQSN pk q.2)
            (MatrixMap.conj (hwReadKraus (.readH z (trialUpdSN z (i, K))) r) σ)) := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun r _ ↦ hpost r),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (dW (fun q ↦ encPotQSN pk q.2) σ +
          4 * G * (∑ q, recUWtSN z (i, K) q.2 * (σ q q).re) +
            (2 ^ 510 : ℝ)⁻¹ * σ.trace.re) :=
        ENNReal.ofReal_le_ofReal key
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add hP0 (by positivity), add_assoc,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
          ENNReal.ofReal_ofNat]

end Quantum.Qrom.Sphincs.Multi

end
