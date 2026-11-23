module

public import Quantum.Qrom.Xmss.Multi.Costs.Ports
public import Quantum.Qrom.Xmss.Costs.EncRead

@[expose] public section

/-!
# The Enc potential of the `n`-user runtime 2 at one port

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.EncRead`. The potential `encPotQN P` is the number
of codeword cells at the message slots of the unselected keys of all users, each cell counted for
its owner under `P` (`msgCwCountN`); it is label free and `0` at the empty register.

* **Splitting at a read cell** (`encPotQN_split`): at a cell `z` of key `(i, l, e)` (message slot
  `(l, e)`, owner `i`), `encPotQN` is the part of the other keys (`encOtherQN`, kept by a trial
  read of `z`: `encOtherQN_keep`), the unselected count of the key off `z` (`offCwQN`) and the
  indicator of `z` holding a codeword output with the key unselected (`cellSN`).
* **A trial read** (`trialReadN_drop`, `trialReadN_potential_le`): as for one user, the count off
  `z` survives with the codeword fraction `ρ_c ≥ 2^-21` (`unselRead_dropQN`), and the cell `z`
  costs re-compression and the recorded mass of the unselected key (`cellFlipN_le`).
* **The other ports**: a sponge call changes one database cell, which has at most one owner and
  one slot (`oneCellLipschitz_encPotQN`); a program off the message slots keeps the potential
  (`encPotQN_progMap`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss (Slot)
open Quantum.Xmss.Assembly (OffCell sqrtDiag re_sqrtDiag_conj_apply readKrausH_ne_zero_rest
  drop_of_survive potential_diagPot_sqrt)
open Quantum.Qrom.MultiUser (ownerOf)

attribute [local irreducible] xmssRom

/- Instance search for the register with its trivial public register exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ} {P : Fin n → PublicParameter}

/-! ## Facts about the selections and the cells -/

theorem trialUpdN_unsel_iff {z : HashDomain} {i : Fin n} {l : Layer} {e : KeyIndex}
    {m : QMemN n} (hm : m.2 i l e = none) (v : HashOutput) :
    (trialUpdN z (i, l, e) m (some v)).2 i l e = none ↔ ¬ Codeword.Valid (truncateHash v) := by
  show cwUpdN i l e z m.2 (some v) i l e = none ↔ _
  rw [cwUpdN_some_of_none i l e z hm v]
  exact cwSelN_eq_none_iff hm z v

theorem trialUpdN_keep {z : HashDomain} {i : Fin n} {l : Layer} {e : KeyIndex} {m : QMemN n}
    (hm : m.2 i l e ≠ none) (o : Option HashOutput) :
    (trialUpdN z (i, l, e) m o).2 i l e ≠ none := by
  show cwUpdN i l e z m.2 o i l e ≠ none
  rw [cwUpdN, Function.update_self, cwUpd_of_ne_none hm]
  exact hm

theorem hw_none_of_msgFreeN {s : RRegN n (SelMemN n)} (hM : MsgFreeN s) {x : HashDomain}
    {l : Layer} {e : KeyIndex} (hx : slotOf x = some (.msg l e)) : s.2.1.1 x = none := by
  by_contra h
  exact hM x (Option.ne_none_iff_isSome.mp h) l e hx

/-! ## The potential -/

/-- **The Enc potential**: the codeword cells at the message slots of the unselected keys, each
cell counted for its owner. -/
noncomputable def encPotQN (P : Fin n → PublicParameter) (s : RRegN n (SelMemN n)) : ℝ :=
  ∑ κ : UKey n, if memAt s κ = none then (msgCwCountN P (unionH s) κ.1 κ.2.1 κ.2.2 : ℝ) else 0

theorem encPotQN_nonneg (P : Fin n → PublicParameter) (s : RRegN n (SelMemN n)) :
    0 ≤ encPotQN P s :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity

/-- The potential of the keys other than `κ₀`. -/
noncomputable def encOtherQN (P : Fin n → PublicParameter) (κ₀ : UKey n)
    (s : RRegN n (SelMemN n)) : ℝ :=
  ∑ κ ∈ Finset.univ.erase κ₀, if memAt s κ = none then
    (msgCwCountN P (unionH s) κ.1 κ.2.1 κ.2.2 : ℝ) else 0

/-- The codeword cells of user `i` at the message slot of key `(l, e)` other than `z`. -/
noncomputable def offCwQN (P : Fin n → PublicParameter) (z : HashDomain) (i : Fin n) (l : Layer)
    (e : KeyIndex) (s : RRegN n (SelMemN n)) : ℕ :=
  cellOutCount (unionH s)
    (fun x ↦ x ≠ z ∧ (ownerOf P prefixOf x = some i ∧ slotOf x = some (.msg l e)))
    fun y ↦ Codeword.Valid (truncateHash y)

/-- The cell `z` holds a codeword output. -/
def CellCwQN (z : HashDomain) (s : RRegN n (SelMemN n)) : Prop :=
  ∃ y, unionH s z = some y ∧ Codeword.Valid (truncateHash y)

/-- The states whose key `(i, l, e)` is unselected. -/
def unselSN (i : Fin n) (l : Layer) (e : KeyIndex) : Set (Unit × RRegN n (SelMemN n)) :=
  {q | q.2.2.2.2 i l e = none}

instance instDecidablePredUnselSN (i : Fin n) (l : Layer) (e : KeyIndex) :
    DecidablePred (· ∈ unselSN i l e) :=
  fun q ↦ inferInstanceAs (Decidable (q.2.2.2.2 i l e = none))

/-- The states whose key `(i, l, e)` is unselected with a codeword output at the cell `z`. -/
def cellSN (z : HashDomain) (i : Fin n) (l : Layer) (e : KeyIndex) :
    Set (Unit × RRegN n (SelMemN n)) :=
  {q | q.2.2.2.2 i l e = none ∧ CellCwQN z q.2}

noncomputable instance instDecidablePredCellSN (z : HashDomain) (i : Fin n) (l : Layer)
    (e : KeyIndex) : DecidablePred (· ∈ cellSN z i l e) :=
  Classical.decPred _

theorem ind_unselSN {i : Fin n} {l : Layer} {e : KeyIndex} (q : Unit × RRegN n (SelMemN n)) :
    ind (unselSN i l e) q = if q.2.2.2.2 i l e = none then 1 else 0 :=
  rfl

variable {z : HashDomain} {i : Fin n} {l : Layer} {e : KeyIndex}

open scoped Classical in
/-- The codeword cells of the key of `z` are those off `z` and the cell `z`. -/
theorem msgCwCountN_eq_off_add (hz : slotOf z = some (.msg l e))
    (ho : ownerOf P prefixOf z = some i) (s : RRegN n (SelMemN n)) :
    (msgCwCountN P (unionH s) i l e : ℝ) = offCwQN P z i l e s +
      if CellCwQN z s then 1 else 0 := by
  have h := cellOutCount_eq_off_add (unionH s)
    (fun x ↦ ownerOf P prefixOf x = some i ∧ slotOf x = some (.msg l e))
    (fun y ↦ Codeword.Valid (truncateHash y)) z
  change msgCwCountN P (unionH s) i l e = offCwQN P z i l e s + _ at h
  rw [h, Nat.cast_add]
  by_cases hc : CellCwQN z s
  · rw [ite_eq_left ⟨⟨ho, hz⟩, hc⟩, ite_eq_left hc, Nat.cast_one]
  · rw [ite_eq_right fun h' ↦ hc h'.2, ite_eq_right hc, Nat.cast_zero]

/-- **The potential split at a message-digest cell of its owner.** -/
theorem encPotQN_split (hz : slotOf z = some (.msg l e)) (ho : ownerOf P prefixOf z = some i)
    (q : Unit × RRegN n (SelMemN n)) :
    encPotQN P q.2 = encOtherQN P (i, l, e) q.2 + ind (unselSN i l e) q * offCwQN P z i l e q.2 +
      ind (cellSN z i l e) q := by
  unfold encPotQN encOtherQN
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (i, l, e))]
  dsimp only
  rw [ind_unselSN]
  unfold ind
  by_cases hu : q.2.2.2.2 i l e = none
  · have hu' : memAt q.2 (i, l, e) = none := hu
    rw [ite_eq_left hu', ite_eq_left hu, msgCwCountN_eq_off_add hz ho]
    by_cases hc : CellCwQN z q.2
    · rw [ite_eq_left hc, ite_eq_left (show q ∈ cellSN z i l e from ⟨hu, hc⟩)]
      ring
    · rw [ite_eq_right hc, ite_eq_right (show q ∉ cellSN z i l e from fun h ↦ hc h.2)]
      ring
  · have hu' : ¬ memAt q.2 (i, l, e) = none := hu
    rw [ite_eq_right hu', ite_eq_right hu,
      ite_eq_right (show q ∉ cellSN z i l e from fun h ↦ hu h.1)]
    ring

/-- The potential sees only the union view and the selections. -/
theorem encPotQN_congr {s s' : RRegN n (SelMemN n)} (hU : unionH s' = unionH s)
    (hm : s'.2.2.2 = s.2.2.2) : encPotQN P s' = encPotQN P s := by
  unfold encPotQN memAt
  rw [hU, hm]

/-- **Off the message slots the potential sees nothing**: states agreeing off a cell `z` that is
no message-slot cell of an owner, with the same selections, have the same potential. -/
theorem encPotQN_eq_of_off
    (hno : ∀ i l e, ¬(ownerOf P prefixOf z = some i ∧ slotOf z = some (.msg l e)))
    {s s' : RRegN n (SelMemN n)} (hU : ∀ x, x ≠ z → unionH s' x = unionH s x)
    (hm : s'.2.2.2 = s.2.2.2) : encPotQN P s' = encPotQN P s := by
  unfold encPotQN
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  have hc : msgCwCountN P (unionH s') κ.1 κ.2.1 κ.2.2 =
      msgCwCountN P (unionH s) κ.1 κ.2.1 κ.2.2 :=
    cellOutCount_congr (D := HashDomain) (Y := HashOutput)
      (P := fun x ↦ ownerOf P prefixOf x = some κ.1 ∧ slotOf x = some (.msg κ.2.1 κ.2.2)) _
      fun x hx ↦ hU x fun hxz ↦ hno κ.1 κ.2.1 κ.2.2 (hxz ▸ hx)
  unfold memAt
  rw [hm, hc]

/-- The count off `z` does not see `z`. -/
theorem offCwQN_congr {s s' : RRegN n (SelMemN n)}
    (hU : ∀ x, x ≠ z → unionH s' x = unionH s x) :
    offCwQN P z i l e s' = offCwQN P z i l e s :=
  cellOutCount_congr _ fun x hx ↦ hU x hx.1

theorem unionH_congr_offN {s s' : RRegN n (SelMemN n)} (h1 : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b)
    (h3 : s'.2.1 = s.2.1) (x : HashDomain) (hx : x ≠ z) : unionH s' x = unionH s x := by
  rw [unionH_apply, unionH_apply, h3, h1 x hx]

/-- The count off `z` is a weight off the cell `z`. -/
theorem offCwQN_offCell :
    OffCell z (fun s : RRegN n (SelMemN n) ↦ (offCwQN P z i l e s : ℝ)) := fun _ _ h1 _ h3 ↦
  congrArg Nat.cast (offCwQN_congr (unionH_congr_offN h1 h3))

/-- The potential of the other keys does not see `z` nor the selection of `(i, l, e)`. -/
theorem encOtherQN_congr (hz : slotOf z = some (.msg l e)) (ho : ownerOf P prefixOf z = some i)
    {s s' : RRegN n (SelMemN n)} (hU : ∀ x, x ≠ z → unionH s' x = unionH s x)
    (hm : ∀ κ : UKey n, κ ≠ (i, l, e) → memAt s' κ = memAt s κ) :
    encOtherQN P (i, l, e) s' = encOtherQN P (i, l, e) s := by
  unfold encOtherQN
  refine Finset.sum_congr rfl fun κ hκ ↦ ?_
  have hκ' := Finset.ne_of_mem_erase hκ
  have hc : msgCwCountN P (unionH s') κ.1 κ.2.1 κ.2.2 =
      msgCwCountN P (unionH s) κ.1 κ.2.1 κ.2.2 :=
    cellOutCount_congr (D := HashDomain) (Y := HashOutput)
      (P := fun x ↦ ownerOf P prefixOf x = some κ.1 ∧ slotOf x = some (.msg κ.2.1 κ.2.2)) _
      fun x hx ↦ hU x fun hxz ↦ by
        subst hxz
        have hi := Option.some.inj (hx.1.symm.trans ho)
        obtain ⟨h1, h2⟩ := Slot.msg.inj (Option.some.inj (hx.2.symm.trans hz))
        exact hκ' (Prod.ext hi (Prod.ext h1 h2))
  rw [hm κ hκ', hc]

/-- **A trial read keeps the potential of the other keys.** -/
theorem encOtherQN_keep (hz : slotOf z = some (.msg l e)) (ho : ownerOf P prefixOf z = some i)
    (r : Option HashOutput × QMemN n) (a a' : Unit × RRegN n (SelMemN n))
    (h : hwReadKraus (.readH z (trialUpdN z (i, l, e))) r a' a ≠ 0) :
    encOtherQN P (i, l, e) a'.2 = encOtherQN P (i, l, e) a.2 := by
  obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
  obtain ⟨h1, -, h3⟩ := readKrausH_ne_zero_rest z (trialUpdN z (i, l, e)) r h'
  obtain ⟨hm1, hm2⟩ := readKrausH_memQ z (trialUpdN z (i, l, e)) r h'
  refine encOtherQN_congr hz ho (unionH_congr_offN h1 h3) fun κ hκ ↦ ?_
  unfold memAt
  rw [hm2, hm1]
  exact cwUpdN_apply_of_ne i l e z _ _ fun h ↦ hκ (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))

/-! ## The other ports -/

/-- **A sponge call changes the potential by at most one** (one database cell, of at most one
owner and slot). -/
theorem oneCellLipschitz_encPotQN (P : Fin n → PublicParameter) :
    OneCellLipschitz (X := HashOutput) (Z := HashDomain) (M := QMemN n) (encPotQN P) where
  h D b x v := by
    set s : RRegN n (SelMemN n) := (D, b)
    set s' : RRegN n (SelMemN n) := ((Function.update D.1 x v, D.2.1, D.2.2), b)
    have hU : ∀ y, y ≠ x → unionH s' y = unionH s y := fun y hy ↦ by
      rw [unionH_apply, unionH_apply]
      show (b.1.1 y).or (Function.update D.1 x v y) = (b.1.1 y).or (D.1 y)
      rw [Function.update_of_ne hy]
    by_cases hx : ∃ i l e, ownerOf P prefixOf x = some i ∧ slotOf x = some (.msg l e)
    · obtain ⟨i, l, e, ho, hx⟩ := hx
      have h1 := encPotQN_split hx ho ((), s)
      have h2 := encPotQN_split hx ho ((), s')
      have hA : encOtherQN P (i, l, e) s' = encOtherQN P (i, l, e) s :=
        encOtherQN_congr hx ho hU fun _ _ ↦ rfl
      have hn : offCwQN P x i l e s' = offCwQN P x i l e s := offCwQN_congr hU
      have hu : ind (unselSN i l e) ((), s') = ind (unselSN i l e) ((), s) := rfl
      have hc1 := ind_le_one (cellSN x i l e) ((), s')
      have hc0 := ind_nonneg (cellSN x i l e) ((), s)
      change encPotQN P s' ≤ encPotQN P s + 1
      rw [h1, h2, hA, hn, hu]
      linarith
    · exact (encPotQN_eq_of_off (fun i l e h ↦ hx ⟨i, l, e, h⟩) hU rfl).le.trans
        (le_add_of_nonneg_right zero_le_one)
  k D b x v := (encPotQN_congr (s := (D, b)) rfl rfl).le.trans
    (le_add_of_nonneg_right zero_le_one)
  k' D b x v := (encPotQN_congr (s := (D, b)) rfl rfl).le.trans
    (le_add_of_nonneg_right zero_le_one)

/-- **A program of a cell at no message slot keeps the potential.** -/
theorem encPotQN_progMap (hno : ∀ l e, slotOf z ≠ some (.msg l e)) (a : HashOutput)
    (s : RRegN n (SelMemN n)) : encPotQN P (progMap (.programH z a) s) = encPotQN P s := by
  refine encPotQN_eq_of_off (fun _ l e h ↦ hno l e h.2) (fun x hx ↦ ?_) rfl
  rw [unionH_apply, unionH_apply]
  show (Function.update s.2.1.1 z (some a) x).or (Function.update s.1.1 z none x) =
    (s.2.1.1 x).or (s.1.1 x)
  rw [Function.update_of_ne hx, Function.update_of_ne hx]

/-! ## The count off the read cell at a trial read -/

/-- **The flip values of the unselected-key event** at a rest: the key unselected and the digest
a codeword. -/
def CwFlipQN (i : Fin n) (l : Layer) (e : KeyIndex) (z : HashDomain) (y : HashOutput)
    (r : RestH HashOutput (QMemN n) z) : Prop :=
  (memH z r).2 i l e = none ∧ Codeword.Valid (truncateHash y)

noncomputable instance instDecidableCwFlipQN (i : Fin n) (l : Layer) (e : KeyIndex)
    (z : HashDomain) (y : HashOutput) (r : RestH HashOutput (QMemN n) z) :
    Decidable (CwFlipQN i l e z y r) :=
  Classical.propDecidable _

/-- The states a trial read selects from: the cell empty, the key unselected. -/
def EmptyUnselQN (z : HashDomain) (i : Fin n) (l : Layer) (e : KeyIndex)
    (s : RRegN n (SelMemN n)) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z = none ∧ s.2.2.2 i l e = none

noncomputable instance instDecidablePredEmptyUnselQN (z : HashDomain) (i : Fin n) (l : Layer)
    (e : KeyIndex) : DecidablePred (EmptyUnselQN (n := n) z i l e) :=
  Classical.decPred _

/-- The states whose read cell is recorded with a codeword output, the key unselected. -/
def CwRecQN (z : HashDomain) (i : Fin n) (l : Layer) (e : KeyIndex)
    (s : RRegN n (SelMemN n)) : Prop :=
  s.2.1.1 z = none ∧ s.2.2.2 i l e = none ∧
    ∃ v, s.1.1 z = some v ∧ Codeword.Valid (truncateHash v)

noncomputable instance instDecidablePredCwRecQN (z : HashDomain) (i : Fin n) (l : Layer)
    (e : KeyIndex) : DecidablePred (CwRecQN (n := n) z i l e) :=
  Classical.decPred _

theorem ind_unselSN_symm (a : Option HashOutput) (r : RestH HashOutput (QMemN n) z) :
    ind (unselSN i l e) ((splitH' z).symm (a, r)) =
      if (memH z r).2 i l e = none then 1 else 0 :=
  rfl

/-- The weight of a recorded outcome against the unselected-key event. -/
theorem gw_unselSN (y : HashOutput) (r : RestH HashOutput (QMemN n) z) :
    gw (splitH' z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e) (some y) r =
      if (trialUpdN z (i, l, e) (memH z r) (some y)).2 i l e = none then 1 else 0 := by
  unfold gw
  have h : ∀ a : Option HashOutput, ind (unselSN i l e)
      ((splitH' z).symm (a, tauH z (trialUpdN z (i, l, e)) (some y) r)) =
      if (trialUpdN z (i, l, e) (memH z r) (some y)).2 i l e = none then 1 else 0 := fun a ↦ rfl
  simp only [h]
  rw [← Finset.sum_mul, sum_cr_sq, one_mul]

/-- **The diagonal cost of the unselected-key event**: `-ρ_c` on an empty, not hardwired cell
with the key unselected, at most `0` elsewhere. -/
theorem fd_unselSN_le (q : Unit × RRegN n (SelMemN n)) :
    fd (splitH' z) (actH z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e)
        (phiH z (trialUpdN z (i, l, e))) q ≤
      -(Quantum.Xmss.rhoCw * if EmptyUnselQN z i l e q.2 then 1 else 0) := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  unfold fd
  by_cases ha : actH z (splitH' z q).2
  · have ha' : q.2.2.1.1 z = none := ha
    rw [ite_eq_left ha, ind_unselSN]
    rcases hc : (splitH' z q).1 with _ | y
    · have hc' : q.2.1.1 z = none := hc
      show (∑ y, gw (splitH' z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e) (some y)
          (splitH' z q).2) / Fintype.card HashOutput - _ ≤ _
      simp only [gw_unselSN, hmem]
      by_cases hm : q.2.2.2.2 i l e = none
      · have hsum : (∑ y : HashOutput, if (trialUpdN z (i, l, e) q.2.2.2 (some y)).2 i l e =
            none then (1 : ℝ) else 0) = Fintype.card HashOutput -
              ((Finset.univ.filter fun v : HashOutput ↦
                Codeword.Valid (truncateHash v)).card : ℝ) := by
          rw [Finset.sum_congr rfl fun y _ ↦ if_congr (trialUpdN_unsel_iff hm y) rfl rfl,
            Finset.sum_boole, Finset.filter_not, Finset.card_sdiff_of_subset
              (Finset.subset_univ _), Finset.card_univ, Nat.cast_sub (Finset.card_le_univ _)]
        have hN : (0 : ℝ) < Fintype.card HashOutput := Nat.cast_pos.2 Fintype.card_pos
        have hE : EmptyUnselQN z i l e q.2 := ⟨ha', hc', hm⟩
        rw [hsum, sub_div, div_self hN.ne', card_codeword_div_card_hashOutput, ite_eq_left hm,
          ite_eq_left hE]
        linarith
      · have h0 : ∀ y : HashOutput, (trialUpdN z (i, l, e) q.2.2.2 (some y)).2 i l e ≠ none :=
          fun y ↦ trialUpdN_keep hm _
        have hR : (if EmptyUnselQN z i l e q.2 then (1 : ℝ) else 0) = 0 :=
          ite_eq_right fun h ↦ hm h.2.2
        rw [hR, mul_zero, neg_zero, ite_eq_right hm]
        simp only [h0, ↓reduceIte, Finset.sum_const_zero, zero_div, sub_zero, le_refl]
    · have hc' : q.2.1.1 z ≠ none := by
        rw [← splitH'_apply_fst, hc]; exact Option.some_ne_none y
      show gw (splitH' z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e) (some y)
        (splitH' z q).2 - _ ≤ _
      have hR : (if EmptyUnselQN z i l e q.2 then (1 : ℝ) else 0) = 0 :=
        ite_eq_right fun h ↦ hc' h.2.1
      rw [hR, mul_zero, neg_zero, gw_unselSN, hmem]
      by_cases hm : q.2.2.2.2 i l e = none
      · rw [ite_eq_left hm]
        split_ifs <;> norm_num
      · rw [ite_eq_right hm, ite_eq_right (trialUpdN_keep hm _), sub_zero]
  · have ha' : q.2.2.1.1 z ≠ none := ha
    have hR : (if EmptyUnselQN z i l e q.2 then (1 : ℝ) else 0) = 0 :=
      ite_eq_right fun h ↦ ha' h.1
    rw [ite_eq_right ha, ind_unselSN, ind_unselSN, hR, mul_zero, neg_zero]
    show (if (trialUpdN z (i, l, e) q.2.2.2 (q.2.2.1.1 z)).2 i l e = none then (1 : ℝ)
      else 0) - _ ≤ 0
    by_cases hm : q.2.2.2.2 i l e = none
    · rw [ite_eq_left hm]
      split_ifs <;> norm_num
    · rw [ite_eq_right hm, ite_eq_right (trialUpdN_keep hm _), sub_zero]

/-- **The empty-to-recorded weight of the unselected-key event** with the reference `q0`: `ρ_c`
on an empty, not hardwired cell with the key unselected, `0` elsewhere. -/
theorem ew_unselSN_le (q : Unit × RRegN n (SelMemN n)) :
    ew (splitH' z) (actH z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e)
        (q0 (splitH' z) (unselSN i l e)) q ≤
      Quantum.Xmss.rhoCw * if EmptyUnselQN z i l e q.2 then 1 else 0 := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  unfold ew
  split_ifs with h1 h2 h2
  · have hN : (0 : ℝ) < Fintype.card HashOutput := Nat.cast_pos.2 Fintype.card_pos
    have hq0 : q0 (splitH' z) (unselSN i l e) (splitH' z q).2 = 1 := by
      unfold q0
      rw [ind_unselSN_symm, hmem, ite_eq_left h2.2.2]
    have hterm : ∀ y : HashOutput, xv (splitH' z) (tauH z (trialUpdN z (i, l, e)))
        (unselSN i l e) (q0 (splitH' z) (unselSN i l e)) (some y) (splitH' z q).2 ^ 2 =
        (if Codeword.Valid (truncateHash y) then 1 else 0) / Fintype.card HashOutput :=
      fun y ↦ by
        have hsq : ((if ¬ Codeword.Valid (truncateHash y) then (1 : ℝ) else 0) - 1) ^ 2 =
            if Codeword.Valid (truncateHash y) then 1 else 0 := by
          split_ifs <;> norm_num
        show ((gw (splitH' z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e) (some y)
          (splitH' z q).2 - q0 (splitH' z) (unselSN i l e) (splitH' z q).2) /
            Real.sqrt (Fintype.card HashOutput)) ^ 2 = _
        rw [hq0, gw_unselSN, hmem, if_congr (trialUpdN_unsel_iff h2.2.2 y) rfl rfl, div_pow,
          Real.sq_sqrt hN.le, hsq]
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, ← Finset.sum_div, Finset.sum_boole,
      card_codeword_div_card_hashOutput, mul_one]
  · have hm : q.2.2.2.2 i l e ≠ none := fun hm ↦
      h2 (And.intro h1.1 (And.intro h1.2 hm) : EmptyUnselQN z i l e q.2)
    have hq0 : q0 (splitH' z) (unselSN i l e) (splitH' z q).2 = 0 := by
      unfold q0
      rw [ind_unselSN_symm, hmem, ite_eq_right hm]
    have hterm : ∀ y : HashOutput, xv (splitH' z) (tauH z (trialUpdN z (i, l, e)))
        (unselSN i l e) (q0 (splitH' z) (unselSN i l e)) (some y) (splitH' z q).2 ^ 2 = 0 :=
      fun y ↦ by
        show ((gw (splitH' z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e) (some y)
          (splitH' z q).2 - q0 (splitH' z) (unselSN i l e) (splitH' z q).2) /
            Real.sqrt (Fintype.card HashOutput)) ^ 2 = _
        rw [hq0, gw_unselSN, hmem, ite_eq_right (trialUpdN_keep hm (some y)), sub_self,
          zero_div]
        exact zero_pow two_ne_zero
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, Finset.sum_const_zero, mul_zero]
  · exact absurd ⟨h2.1, h2.2.1⟩ h1
  · rw [mul_zero]

/-- The cross term's support: the recorded cells of the flip values are codeword-recorded for
the unselected key. -/
theorem pd_cwFlipQN_le (q : Unit × RRegN n (SelMemN n)) :
    pd (splitH' z) (actH z) (CwFlipQN i l e z) q ≤ if CwRecQN z i l e q.2 then 1 else 0 := by
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
        exact h2 (And.intro h1 (And.intro h3.1 ⟨y, hc', h3.2⟩) : CwRecQN z i l e q.2)
      · exact le_rfl
  · norm_num
  · exact le_rfl

/-- Off the flip values a recorded outcome weighs the reference weight `q0`. -/
theorem gw_eq_q0_of_not_cwFlipQN (r : RestH HashOutput (QMemN n) z) (y : HashOutput)
    (hy : ¬ CwFlipQN i l e z y r) :
    gw (splitH' z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e) (some y) r =
      q0 (splitH' z) (unselSN i l e) r := by
  unfold q0
  rw [gw_unselSN, ind_unselSN_symm]
  by_cases hm : (memH z r).2 i l e = none
  · rw [ite_eq_left hm, ite_eq_left ((trialUpdN_unsel_iff hm y).2 fun hv ↦ hy ⟨hm, hv⟩)]
  · rw [ite_eq_right hm, ite_eq_right (trialUpdN_keep hm _)]

/-- The unselected `w`-weighted mass is the event weight of `N σ N`. -/
theorem re_trace_indProj_sqrtDiagQN {w : RRegN n (SelMemN n) → ℝ} (hw0 : ∀ s, 0 ≤ w s)
    (σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ) :
    (indProj (unselSN i l e) * (sqrtDiag w * σ * sqrtDiag w)).trace.re =
      dW (fun q ↦ ind (unselSN i l e) q * w q.2) σ := by
  rw [indProj, re_trace_diagonal_mul]
  unfold dW
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [re_sqrtDiag_conj_apply hw0]
  exact (mul_assoc _ _ _).symm

/-- The unselected `w`-weighted mass after a trial read: the mass before plus the flip of the
unselected-key event on `N σ N`. -/
theorem unsel_post_eqQN {w : RRegN n (SelMemN n) → ℝ} (hw0 : ∀ s, 0 ≤ w s) (hw : OffCell z w)
    (σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ) :
    ∑ r : Option HashOutput × QMemN n, dW (fun q ↦ ind (unselSN i l e) q * w q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) σ) =
      dW (fun q ↦ ind (unselSN i l e) q * w q.2) σ +
        (flipOp (fun r : Option HashOutput × QMemN n ↦
          hwReadKraus (.readH z (trialUpdN z (i, l, e))) r)
          (unselSN i l e) * (sqrtDiag w * σ * sqrtDiag w)).trace.re := by
  have h1 : ∀ r, dW (fun q ↦ ind (unselSN i l e) q * w q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) σ) =
      dW (fun q ↦ ind (unselSN i l e) q)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r)
          (sqrtDiag w * σ * sqrtDiag w)) :=
    fun r ↦ (dW_conj_sqrtDiagG z (trialUpdN z (i, l, e)) hw0 hw
      (fun q ↦ ind (unselSN i l e) q) r σ).symm
  have hsumeq : (∑ r : Option HashOutput × QMemN n,
      (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r)ᴴ *
        diagonal (fun q ↦ ((ind (unselSN i l e) q : ℝ) : ℂ)) *
          hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) =
      flipOp (fun r : Option HashOutput × QMemN n ↦
        hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) (unselSN i l e) +
        indProj (unselSN i l e) := by
    rw [flipOp, sub_add_cancel]
    rfl
  rw [Finset.sum_congr rfl fun r _ ↦ h1 r, sum_dW_conj, hsumeq, Matrix.add_mul,
    Matrix.trace_add, Complex.add_re, add_comm, re_trace_indProj_sqrtDiagQN hw0 σ]

/-- **The flip of the unselected-key event at a trial read, `w`-weighted**: at most
`-ρ_c e + 2 √(ρ_c e p)`, `e` the `w`-weighted `EmptyUnselQN` mass and `p` the `w`-weighted
`CwRecQN` mass. -/
theorem unselFlipQN_le {w : RRegN n (SelMemN n) → ℝ} (hw0 : ∀ s, 0 ≤ w s) (hw : OffCell z w)
    {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option HashOutput × QMemN n ↦
        hwReadKraus (.readH z (trialUpdN z (i, l, e))) r)
        (unselSN i l e) * (sqrtDiag w * σ * sqrtDiag w)).trace.re ≤
      -(Quantum.Xmss.rhoCw *
          ∑ q, (if EmptyUnselQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re)) +
        2 * √(Quantum.Xmss.rhoCw *
          (∑ q, (if EmptyUnselQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re)) *
            ∑ q, (if CwRecQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re)) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hτ : (sqrtDiag w * σ * sqrtDiag w).PosSemidef := posSemidef_sqrtDiag_conjG w hσ
  have hdiag : ∀ q, ((sqrtDiag w * σ * sqrtDiag w) q q).re = w q.2 * (σ q q).re :=
    re_sqrtDiag_conj_apply hw0 σ
  have hwσ : ∀ q, 0 ≤ w q.2 * (σ q q).re := fun q ↦ mul_nonneg (hw0 _) (hre q)
  have hF := re_trace_flipOp_le (unselSN i l e) (cellRead_readH z (trialUpdN z (i, l, e)))
    (clsOff_readH z (trialUpdN z (i, l, e))) (q0 (splitH' z) (unselSN i l e))
    (CwFlipQN i l e z) (fun r _ y hy ↦ gw_eq_q0_of_not_cwFlipQN r y hy) hτ
    (cellNoBot_sqrtDiagG hw hnb)
  have he : 0 ≤ ∑ q, (if EmptyUnselQN z i l e q.2 then (1 : ℝ) else 0) * (w q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hwσ q)
  have hρ : 0 ≤ Quantum.Xmss.rhoCw :=
    le_trans (by positivity) Quantum.Xmss.inv_two_pow_21_le_rhoCw
  have hfd : ∑ s, fd (splitH' z) (actH z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e)
      (phiH z (trialUpdN z (i, l, e))) s * ((sqrtDiag w * σ * sqrtDiag w) s s).re ≤
      -(Quantum.Xmss.rhoCw *
        ∑ q, (if EmptyUnselQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (fd_unselSN_le q) (hwσ q)).trans_eq (by ring)
  have hew : ∑ s, ew (splitH' z) (actH z) (tauH z (trialUpdN z (i, l, e))) (unselSN i l e)
      (q0 (splitH' z) (unselSN i l e)) s * ((sqrtDiag w * σ * sqrtDiag w) s s).re ≤
      Quantum.Xmss.rhoCw *
        ∑ q, (if EmptyUnselQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (ew_unselSN_le q) (hwσ q)).trans_eq (by ring)
  have hpd : ∑ s, pd (splitH' z) (actH z) (CwFlipQN i l e z) s *
      ((sqrtDiag w * σ * sqrtDiag w) s s).re ≤
      ∑ q, (if CwRecQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re) :=
    Finset.sum_le_sum fun q _ ↦ by
      rw [hdiag]
      exact mul_le_mul_of_nonneg_right (pd_cwFlipQN_le q) (hwσ q)
  have hP0 : 0 ≤ ∑ s, pd (splitH' z) (actH z) (CwFlipQN i l e z) s *
      ((sqrtDiag w * σ * sqrtDiag w) s s).re :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      rcases pd_mem (e := splitH' z) (act := actH z) (CwFlipQN i l e z) q with h | h <;>
        simp only [h, le_refl, zero_le_one]) (by rw [hdiag]; exact hwσ q)
  refine hF.trans (add_le_add hfd (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
  rw [← Real.sqrt_mul' _ hP0]
  exact Real.sqrt_le_sqrt (mul_le_mul hew hpd hP0 (mul_nonneg hρ he))

/-- **The unselected count off the read cell at a trial read**: `2^-22 e` plus the
`w`-weighted unselected mass after the read is at most the one before plus `3 p`. -/
theorem unselRead_dropQN {w : RRegN n (SelMemN n) → ℝ} (hw0 : ∀ s, 0 ≤ w s) (hw : OffCell z w)
    {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 22 : ℝ)⁻¹ * (∑ q, (if EmptyUnselQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re)) +
      ∑ r : Option HashOutput × QMemN n, dW (fun q ↦ ind (unselSN i l e) q * w q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) σ) ≤
    dW (fun q ↦ ind (unselSN i l e) q * w q.2) σ +
      3 * ∑ q, (if CwRecQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hwσ : ∀ q, 0 ≤ w q.2 * (σ q q).re := fun q ↦ mul_nonneg (hw0 _) (hre q)
  refine drop_of_survive (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num)
    (hwσ q)) (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hwσ q))
    Quantum.Xmss.inv_two_pow_21_le_rhoCw ?_
  rw [unsel_post_eqQN hw0 hw σ]
  have h := unselFlipQN_le (i := i) (l := l) (e := e) hw0 hw hσ hnb
  have hp : 0 ≤ ∑ q, (if CwRecQN z i l e q.2 then (1 : ℝ) else 0) * (w q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hwσ q)
  linarith

/-! ## The read cell at a trial read -/

/-- The outcome states of a trial read are outside `cellSN`: a codeword output selects the
key. -/
theorem not_mem_cellSN_out {r : RestH HashOutput (QMemN n) z} (hr : actH z r) (y : HashOutput) :
    (splitH' z).symm (some y, tauH z (trialUpdN z (i, l, e)) (some y) r) ∉ cellSN z i l e := by
  rintro ⟨hu, y', hy', hcw⟩
  have hw : ((splitH' z).symm (some y, tauH z (trialUpdN z (i, l, e)) (some y) r)).2.2.1.1 z =
      none := hr
  rw [unionH_apply, hw, splitH'_symm_cellG] at hy'
  obtain rfl := Option.some.inj hy'
  have hu' : (trialUpdN z (i, l, e) (memH z r) (some y)).2 i l e = none := hu
  by_cases hm : (memH z r).2 i l e = none
  · exact (trialUpdN_unsel_iff hm y).1 hu' hcw
  · exact trialUpdN_keep hm _ hu'

/-- The classical move of a hardwired cell leaves `cellSN`. -/
theorem not_mem_cellSN_phiH (q : Unit × RRegN n (SelMemN n)) (hq : q.2.2.1.1 z ≠ none) :
    phiH z (trialUpdN z (i, l, e)) q ∉ cellSN z i l e := by
  rintro ⟨hu, y', hy', hcw⟩
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hq
  have hy2 : (q.2.2.1.1 z).or (q.2.1.1 z) = some y' := hy'
  rw [hw] at hy2
  obtain rfl := Option.some.inj hy2
  have hu' : (trialUpdN z (i, l, e) q.2.2.2 (some w)).2 i l e = none := by
    have h := hu
    change (trialUpdN z (i, l, e) q.2.2.2 (q.2.2.1.1 z)).2 i l e = none at h
    rwa [hw] at h
  by_cases hm : q.2.2.2.2 i l e = none
  · exact (trialUpdN_unsel_iff hm w).1 hu' hcw
  · exact trialUpdN_keep hm _ hu'

/-- **The read cell after a trial read**: the flip into `cellSN` is at most `2/|Y| + 4/|Y|²` per
unit of trace plus the recorded mass of the unselected key at the cell. -/
theorem cellFlipN_le {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option HashOutput × QMemN n ↦
        hwReadKraus (.readH z (trialUpdN z (i, l, e))) r)
        (cellSN z i l e) * σ).trace.re ≤
      ∑ q, ((2 / (Fintype.card HashOutput : ℝ) + (2 / (Fintype.card HashOutput : ℝ)) ^ 2) +
        (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i l e = none then 1 else 0)) *
          (σ q q).re := by
  classical
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set DU : HashOutput → RestH HashOutput (QMemN n) z → Prop := fun _ r ↦
    (memH z r).2 i l e = none
  have hD : ∀ r, actH z r → ∀ y, ¬ DU y r →
      gw (splitH' z) (tauH z (trialUpdN z (i, l, e))) (cellSN z i l e) (some y) r = 0 := by
    intro r _ y hy
    unfold gw
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [ind_eq_zero_of_not_mem (cellSN z i l e) fun h ↦ trialUpdN_keep hy (some y) h.1,
      mul_zero]
  have hF := re_trace_flipOp_le (cellSN z i l e) (cellRead_readH z (trialUpdN z (i, l, e)))
    (clsOff_readH z (trialUpdN z (i, l, e))) (fun _ ↦ 0) DU hD hσ hnb
  set N : ℝ := (Fintype.card HashOutput : ℝ)
  set E := ∑ s, ew (splitH' z) (actH z) (tauH z (trialUpdN z (i, l, e))) (cellSN z i l e)
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
  have hgw : ∀ s : Unit × RRegN n (SelMemN n), actH z (splitH' z s).2 → ∀ y,
      gw (splitH' z) (tauH z (trialUpdN z (i, l, e))) (cellSN z i l e) (some y)
        (splitH' z s).2 ≤ 2 / N :=
    fun s ha y ↦ gw_some_le_two_div (cellSN z i l e)
      (ind_eq_zero_of_not_mem (cellSN z i l e) (not_mem_cellSN_out ha y))
  have hpt : ∀ s, fd (splitH' z) (actH z) (tauH z (trialUpdN z (i, l, e))) (cellSN z i l e)
      (phiH z (trialUpdN z (i, l, e))) s + ew (splitH' z) (actH z)
        (tauH z (trialUpdN z (i, l, e))) (cellSN z i l e) (fun _ ↦ 0) s ≤
        2 / N + (2 / N) ^ 2 := fun s ↦ by
    refine add_le_add ?_ ?_
    · unfold fd
      split_ifs with ha
      · exact (sub_le_self _ (ind_nonneg _ s)).trans (gdiag_le_of _ (hgw s ha) _)
      · rw [ind_eq_zero_of_not_mem (cellSN z i l e) (not_mem_cellSN_phiH s ha), zero_sub]
        exact (neg_nonpos.2 (ind_nonneg _ s)).trans (by positivity)
    · by_cases ha : actH z (splitH' z s).2
      · exact ew_zero_le_of _ (hgw s ha)
      · unfold ew
        rw [ite_eq_right fun h' ↦ ha h'.1]
        positivity
  have hpd : ∀ s : Unit × RRegN n (SelMemN n), pd (splitH' z) (actH z) DU s ≤
      if s.2.2.1.1 z = none ∧ s.2.1.1 z ≠ none ∧ s.2.2.2.2 i l e = none then 1 else 0 := by
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
  calc _ ≤ ∑ s, fd (splitH' z) (actH z) (tauH z (trialUpdN z (i, l, e))) (cellSN z i l e)
        (phiH z (trialUpdN z (i, l, e))) s * (σ s s).re + (E + p) :=
        hF.trans (add_le_add le_rfl hsq)
    _ = ∑ s, (fd (splitH' z) (actH z) (tauH z (trialUpdN z (i, l, e))) (cellSN z i l e)
          (phiH z (trialUpdN z (i, l, e))) s + ew (splitH' z) (actH z)
            (tauH z (trialUpdN z (i, l, e))) (cellSN z i l e) (fun _ ↦ 0) s +
              pd (splitH' z) (actH z) DU s) * (σ s s).re := by
        simp only [E, p, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right
        (add_le_add (hpt s) (hpd s)) (hre s)

/-! ## A trial read -/

/-- **The database count of the codeword cells off `z`** at a recorded read cell of a
`MsgFreeN` register: one less than the recorded cells, at most. -/
theorem offCwQN_add_one_le {s : RRegN n (SelMemN n)} (hM : MsgFreeN s)
    (hD : s.1.1 z ≠ none) : offCwQN P z i l e s + 1 ≤ s.1.1.size := by
  have h1 : offCwQN P z i l e s ≤
      (Finset.univ.filter fun x ↦ x ≠ z ∧ (s.1.1 x).isSome).card := by
    refine cellOutCount_le_card _ fun x y hx hy ↦ ⟨hx.1, ?_⟩
    have hw : s.2.1.1 x = none := hw_none_of_msgFreeN hM hx.2.2
    rw [unionH_apply, hw] at hy
    change s.1.1 x = some y at hy
    rw [hy]
    rfl
  have h2 := card_filter_eq_off_add (fun x ↦ (s.1.1 x).isSome) z
  rw [ite_eq_left (Option.ne_none_iff_isSome.mp hD)] at h2
  have h3 : s.1.1.size = (Finset.univ.filter fun x ↦ (s.1.1 x).isSome).card := rfl
  omega

open scoped Classical in
/-- **A trial read on the potential, in `ℝ`**: on states supported on `MsgFreeN` registers of
database grade at most `G`, with no decompressed `⊥` at the cell, `2^-22 encWtN` plus the
potential after the read is at most the potential before plus `4 G recUWtN + 2^-250 tr σ`. -/
theorem trialReadN_drop (hz : slotOf z = some (.msg l e)) (ho : ownerOf P prefixOf z = some i)
    {G : ℕ} {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ)
    (hinv : ∀ q, σ q q ≠ 0 → MsgFreeN q.2 ∧ dbGrade q.2.1 ≤ G) :
    (2 ^ 22 : ℝ)⁻¹ * (∑ q, encWtN P z (i, l, e) q.2 * (σ q q).re) +
        ∑ r : Option HashOutput × QMemN n, dW (fun q ↦ encPotQN P q.2)
          (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) σ) ≤
      dW (fun q ↦ encPotQN P q.2) σ + 4 * G * (∑ q, recUWtN z (i, l, e) q.2 * (σ q q).re) +
        (2 ^ 250 : ℝ)⁻¹ * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set w : RRegN n (SelMemN n) → ℝ := fun s ↦ (offCwQN P z i l e s : ℝ)
  have hw0 : ∀ s, 0 ≤ w s := fun s ↦ Nat.cast_nonneg _
  have hsplit : (fun q : Unit × RRegN n (SelMemN n) ↦ encPotQN P q.2) = fun q ↦
      (fun q ↦ encOtherQN P (i, l, e) q.2 + ind (unselSN i l e) q * w q.2) q +
        ind (cellSN z i l e) q :=
    funext fun q ↦ encPotQN_split hz ho q
  have hdW : ∀ τ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ,
      dW (fun q ↦ encPotQN P q.2) τ = dW (fun q ↦ encOtherQN P (i, l, e) q.2) τ +
        dW (fun q ↦ ind (unselSN i l e) q * w q.2) τ + dW (ind (cellSN z i l e)) τ :=
    fun τ ↦ by rw [hsplit, dW_add, dW_add]
  simp only [hdW, Finset.sum_add_distrib]
  -- The other keys keep their part.
  have hA : ∑ r : Option HashOutput × QMemN n, dW (fun q ↦ encOtherQN P (i, l, e) q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) σ) =
      dW (fun q ↦ encOtherQN P (i, l, e) q.2) σ :=
    sum_dW_conj_of_keep (fun r : Option HashOutput × QMemN n ↦
      hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) _ (encOtherQN_keep hz ho)
      (sum_readKrausH z (trialUpdN z (i, l, e))) σ
  -- The count off the cell.
  have hB := unselRead_dropQN (i := i) (l := l) (e := e) hw0 offCwQN_offCell hσ hnb
  -- The cell itself.
  have hCeq : ∑ r : Option HashOutput × QMemN n, dW (ind (cellSN z i l e))
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) σ) =
      dW (ind (cellSN z i l e)) σ + (flipOp (fun r : Option HashOutput × QMemN n ↦
        hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) (cellSN z i l e) * σ).trace.re := by
    rw [sum_dW_conj, dW_eq_trace, flipOp, indProj, Matrix.sub_mul, Matrix.trace_sub,
      Complex.sub_re]
    ring
  have hC := cellFlipN_le (i := i) (l := l) (e := e) hσ hnb
  -- The Enc weight is the weight of the empty reads.
  have hEnc : ∑ q, encWtN P z (i, l, e) q.2 * (σ q q).re =
      ∑ q, (if EmptyUnselQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re) := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp [h0]
    have hW : q.2.2.1.1 z = none := hw_none_of_msgFreeN (hinv q h0).1 hz
    unfold encWtN
    dsimp only
    by_cases hE : q.2.1.1 z = none ∧ memAt q.2 (i, l, e) = none
    · have hc : ¬ CellCwQN z q.2 := by
        rintro ⟨y, hy, -⟩
        rw [unionH_apply, hW, hE.1] at hy
        cases hy
      rw [ite_eq_left hE, ite_eq_left (show EmptyUnselQN z i l e q.2 from ⟨hW, hE⟩),
        msgCwCountN_eq_off_add hz ho, ite_eq_right hc, add_zero, one_mul]
    · rw [ite_eq_right hE, ite_eq_right fun h ↦ hE ⟨h.2.1, h.2.2⟩]
      ring
  -- The recorded charges.
  have hRec : 3 * (∑ q, (if CwRecQN z i l e q.2 then 1 else 0) * (w q.2 * (σ q q).re)) +
      ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i l e = none then 1 else 0) *
        (σ q q).re ≤ 4 * G * (∑ q, recUWtN z (i, l, e) q.2 * (σ q q).re) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp [h0]
    obtain ⟨hM, hG⟩ := hinv q h0
    by_cases hR : q.2.1.1 z ≠ none ∧ q.2.2.2.2 i l e = none
    · have hU : recUWtN z (i, l, e) q.2 = 1 := ite_eq_left hR
      have hsz := offCwQN_add_one_le (P := P) (i := i) (l := l) (e := e) hM hR.1
      have hgr : Database.size q.2.1.1 ≤ G := (le_max_left _ _).trans hG
      have hwG : w q.2 + 1 ≤ G := by
        show (offCwQN P z i l e q.2 : ℝ) + 1 ≤ G
        exact_mod_cast hsz.trans hgr
      have h1 : (if CwRecQN z i l e q.2 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have h2 : (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i l e = none then
          (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      rw [hU]
      have hw := hw0 q.2
      have hq := hre q
      have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
      have h3 : 3 * ((if CwRecQN z i l e q.2 then (1 : ℝ) else 0) * (w q.2 * (σ q q).re)) ≤
          3 * (w q.2 * (σ q q).re) := by
        have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hw hq)
        linarith
      have h4 := mul_le_mul_of_nonneg_right h2 hq
      have h5 : (3 * w q.2 + 1) * (σ q q).re ≤ 4 * G * (σ q q).re :=
        mul_le_mul_of_nonneg_right (by linarith) hq
      linarith
    · have hc : ¬ CwRecQN z i l e q.2 := fun h ↦ hR ⟨by
        obtain ⟨v, hv, -⟩ := h.2.2
        rw [hv]
        exact Option.some_ne_none v, h.2.1⟩
      rw [ite_eq_right hc, ite_eq_right fun h ↦ hR ⟨h.2.1, h.2.2⟩]
      have hU0 : 0 ≤ recUWtN z (i, l, e) q.2 := by
        unfold recUWtN
        exact ite_nonneg zero_le_one le_rfl
      simp only [zero_mul, mul_zero, add_zero]
      exact mul_nonneg (by positivity) (mul_nonneg hU0 (hre q))
  -- The re-compression term.
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have hδ : 2 / (Fintype.card HashOutput : ℝ) + (2 / (Fintype.card HashOutput : ℝ)) ^ 2 ≤
      (2 ^ 250 : ℝ)⁻¹ := by
    have hN : (Fintype.card HashOutput : ℝ) = 2 ^ 256 := by
      rw [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat]
    rw [hN]
    norm_num
  have hCsum : ∑ q, ((2 / (Fintype.card HashOutput : ℝ) +
      (2 / (Fintype.card HashOutput : ℝ)) ^ 2) +
        (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i l e = none then 1 else 0)) *
          (σ q q).re = (2 / (Fintype.card HashOutput : ℝ) +
            (2 / (Fintype.card HashOutput : ℝ)) ^ 2) * σ.trace.re +
        ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 i l e = none then 1 else 0) *
          (σ q q).re := by
    rw [htr, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ ↦ by ring
  have htr0 : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have hδt := mul_le_mul_of_nonneg_right hδ htr0
  rw [hEnc]
  rw [hCsum] at hC
  linarith

/-- **A trial read on the potential**: the port condition of the joint potential argument, in
`ℝ≥0∞`. -/
theorem trialReadN_potential_le (hz : slotOf z = some (.msg l e))
    (ho : ownerOf P prefixOf z = some i) {G : ℕ}
    {σ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ)
    (hinv : ∀ q, σ q q ≠ 0 → MsgFreeN q.2 ∧ dbGrade q.2.1 ≤ G) :
    (2 ^ 22 : ℝ≥0∞)⁻¹ * trialWN (encWtN P) (trialReadN z (i, l, e)) σ +
        ∑' r, potential (diagPot fun s ↦ √(encPotQN P s))
          (MatrixMap.conj (hwReadKraus (trialReadN z (i, l, e)) r) σ) ≤
      potential (diagPot fun s ↦ √(encPotQN P s)) σ +
        (4 * (G : ℝ≥0∞) * trialWN recUWtN (trialReadN z (i, l, e)) σ +
          (2 ^ 250 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hpot : ∀ τ : Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ,
      potential (diagPot fun s ↦ √(encPotQN P s)) τ =
        ENNReal.ofReal (dW (fun q ↦ encPotQN P q.2) τ) :=
    fun τ ↦ potential_diagPot_sqrt (encPotQN_nonneg P) τ
  have hpost : ∀ r, 0 ≤ dW (fun q : Unit × RRegN n (SelMemN n) ↦ encPotQN P q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) σ) := fun r ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPotQN_nonneg P q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  have hE0 : 0 ≤ ∑ q, encWtN P z (i, l, e) q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
    mul_nonneg (by unfold encWtN; split_ifs <;> positivity) (hre q)
  have hU0 : 0 ≤ ∑ q, recUWtN z (i, l, e) q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
    mul_nonneg (by unfold recUWtN; split_ifs <;> norm_num) (hre q)
  have hP0 : 0 ≤ dW (fun q : Unit × RRegN n (SelMemN n) ↦ encPotQN P q.2) σ :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPotQN_nonneg P q.2) (hre q)
  have htr0 : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have key := trialReadN_drop hz ho hσ hnb hinv
  rw [trialWN_trialReadN, trialWN_trialReadN, hpot, trialReadN_eq]
  simp only [hpot]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hpost r]
  calc (2 ^ 22 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ q, encWtN P z (i, l, e) q.2 * (σ q q).re) +
        ENNReal.ofReal (∑ r : Option HashOutput × QMemN n, dW (fun q ↦ encPotQN P q.2)
          (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) σ))
      = ENNReal.ofReal ((2 ^ 22 : ℝ)⁻¹ * (∑ q, encWtN P z (i, l, e) q.2 * (σ q q).re) +
          ∑ r : Option HashOutput × QMemN n, dW (fun q ↦ encPotQN P q.2)
            (MatrixMap.conj (hwReadKraus (.readH z (trialUpdN z (i, l, e))) r) σ)) := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun r _ ↦ hpost r),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (dW (fun q ↦ encPotQN P q.2) σ +
          4 * G * (∑ q, recUWtN z (i, l, e) q.2 * (σ q q).re) +
            (2 ^ 250 : ℝ)⁻¹ * σ.trace.re) :=
        ENNReal.ofReal_le_ofReal key
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add hP0 (by positivity), add_assoc,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
          ENNReal.ofReal_ofNat]

end Quantum.Qrom.Xmss.Multi

end
