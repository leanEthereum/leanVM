module

public import Quantum.Qrom.Sphincs.Costs.Ports
public import Quantum.Qrom.Xmss.Costs.EncRead

@[expose] public section

/-!
# The Enc potential of leanSPHINCS's runtime 2 at one port

The Enc weights of the challenge prefix (`encPre`) are bounded by a diagonal potential argument
(CostJoint): the potential `encPotQ pk` is the number of codeword cells at the encoding slots of
the unselected keys (`encCwCount`), at the public key `pk`, label free and `0` at the empty
register. This file proves the port conditions (the leanSPHINCS counterpart of
`Quantum.Qrom.Xmss` `Costs/EncRead`).

* **Splitting at a read cell** (`encPotQ_split`): at an encoding cell `z` of key `K`, `encPotQ`
  is the part of the other keys (`encOtherE`, kept by a trial read of `z`: `encOtherE_keep`), the
  unselected count of the key off `z` (`offCwE`, which does not see `z`) and the indicator of `z`
  holding a codeword pair with the key unselected (`cellSE`).
* **A trial read** (`trialRead_dropE`, `trialRead_potential_leE`): on a state supported on
  `EncFree` registers of database grade at most `G`, with no decompressed `⊥` at the cell,
  `2^-15 encWt` plus the potential after the read is at most the potential before plus
  `4 G recUWt + 2^-510 tr σ`. The count off `z` survives with the codeword fraction
  `ρ_c ≥ 2^-14` (`unselRead_dropE`, the cross term only on the codeword-recorded cells of the
  unselected key); the cell `z` after the read costs re-compression and the recorded mass of the
  unselected key (`cellFlip_leE`).
* **The other ports**: a sponge call changes one database cell, so `encPotQ` is one-cell
  Lipschitz (`oneCellLipschitz_encPotQ`); a program of an exempt cell (never at an encoding slot,
  `not_enc_of_exemptCellE`) keeps it (`encPotQ_progMap`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key Slot)
open Quantum.Xmss.Assembly (OffCell sqrtDiag sqrtDiag_conjTranspose sqrtDiag_mul_readH
  re_sqrtDiag_conj_apply readKrausH_ne_zero_rest potential_diagPot_sqrt)
open Quantum.Qrom.Xmss (cellOutCount cellOutCount_congr cellOutCount_eq_off_add
  cellOutCount_le_card readKrausH_memQ splitH'_symm_cellG cellNoBot_sqrtDiagG dW_conj_sqrtDiagG
  posSemidef_sqrtDiag_conjG)

attribute [local irreducible] sphincsRom

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/- Instance search for the register with its trivial public register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The codeword fraction -/

/-- **A survival bound as a drop**: for a codeword rate `ρ ≥ 2^-14`, the survival bound
`A ≤ w - ρ e + p + 2 √(ρ e p)` gives `2^-15 e + A ≤ w + 3 p` (`2 √(ρ e p) ≤ ρ e / 2 + 2 p`). -/
theorem drop_of_surviveE {A w e p ρ : ℝ} (he : 0 ≤ e) (hp : 0 ≤ p) (hρ : (2 ^ 14 : ℝ)⁻¹ ≤ ρ)
    (h : A ≤ w - ρ * e + p + 2 * √(ρ * e * p)) : (2 ^ 15 : ℝ)⁻¹ * e + A ≤ w + 3 * p := by
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hρe : 0 ≤ ρ * e := mul_nonneg hρ0 he
  have hsq : 2 * √(ρ * e * p) ≤ ρ * e / 2 + 2 * p := by
    rw [Real.sqrt_mul hρe]
    have h1 := Real.sq_sqrt hρe
    have h2 := Real.sq_sqrt hp
    nlinarith [sq_nonneg (√(ρ * e) - 2 * √p)]
  have h15 : (2 ^ 15 : ℝ)⁻¹ * e ≤ ρ / 2 * e := by
    refine mul_le_mul_of_nonneg_right ?_ he
    have : (2 ^ 15 : ℝ)⁻¹ = (2 ^ 14 : ℝ)⁻¹ / 2 := by norm_num
    rw [this]
    linarith
  nlinarith

theorem rhoCw_nonnegE : 0 ≤ Quantum.Sphincs.rhoCw :=
  le_trans (by positivity) Quantum.Sphincs.inv_two_pow_14_le_rhoCw

/-! ## Facts about the selections and the cells -/

variable {pk : PublicKey}

theorem trialUpdQ_sndE (K : Key) (z : Qrom.HashDomain) (m : QMem) (o : Option PairOut) :
    (trialUpdQ K z m o).2 = cwUpd K z m.2 o :=
  rfl

/-- A trial read keeps the selections of the other keys. -/
theorem cwUpd_apply_of_neE {K K' : Key} (z : Qrom.HashDomain) (m : SelMem) (o : Option PairOut)
    (h : K' ≠ K) : cwUpd K z m o K' = m K' := by
  cases o with
  | none => rfl
  | some v =>
    rcases cwUpd_some K z m v with h' | h' <;> rw [h']
    unfold cwSel
    split_ifs
    · exact SelMem.select_of_ne m z _ h
    · rfl

theorem trialUpdQ_unsel_iffE {z : Qrom.HashDomain} {K : Key} {m : QMem} (hm : m.2 K = none)
    (v : PairOut) :
    (trialUpdQ K z m (some v)).2 K = none ↔
      ¬ Quantum.Sphincs.Codeword.Valid (pairDigest v) := by
  rw [trialUpdQ_sndE, cwUpd_some_of_none K z hm v]
  exact cwSel_eq_none_iff hm z v

theorem trialUpdQ_keepE {z : Qrom.HashDomain} {K : Key} {m : QMem} (hm : m.2 K ≠ none)
    (o : Option PairOut) : (trialUpdQ K z m o).2 K ≠ none := by
  rw [trialUpdQ_sndE, cwUpd_of_ne_none hm]
  exact hm

/-- **An exempt cell is not at an encoding slot**: there a selection at another cell gives it a
target. -/
theorem not_enc_of_exemptCellE {hon : HonestCells} {z : Qrom.HashDomain}
    (hz : ExemptCell pk hon z) (K : Key) : slotOf pk z ≠ some (.enc K.1 K.2.1 K.2.2) := by
  intro hs
  obtain ⟨c, hc⟩ := Quantum.Qrom.Xmss.exists_ne_hashDomain z
  have h := hz (fun _ ↦ some (0 : PairOut)) (fun _ ↦ some (c, pairDigest 0)) rfl
  rw [tgtDigest, hs, Option.bind_some, slotDigest_enc, Option.bind_some, ite_eq_right hc] at h
  cases h

theorem hw_none_of_encFreeE {s : RegQ} (hM : EncFree pk s) {x : Qrom.HashDomain} {K : Key}
    (hx : slotOf pk x = some (.enc K.1 K.2.1 K.2.2)) : s.2.1.1 x = none := by
  by_contra h
  exact hM x (Option.ne_none_iff_isSome.mp h) K hx

/-! ## The potential -/

variable (pk) in
/-- **The Enc potential**: the codeword cells at the encoding slots of the unselected keys. -/
noncomputable def encPotQ (s : RegQ) : ℝ :=
  ∑ K : Key, if s.2.2.2 K = none then (encCwCount pk (unionH s) K : ℝ) else 0

theorem encPotQ_nonneg (s : RegQ) : 0 ≤ encPotQ pk s :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity

variable (pk) in
/-- The potential of the keys other than `K₀`. -/
noncomputable def encOtherE (K₀ : Key) (s : RegQ) : ℝ :=
  ∑ K ∈ Finset.univ.erase K₀, if s.2.2.2 K = none then (encCwCount pk (unionH s) K : ℝ) else 0

variable (pk) in
/-- The codeword cells at the encoding slot of key `K` other than `z`. -/
noncomputable def offCwE (z : Qrom.HashDomain) (K : Key) (s : RegQ) : ℕ :=
  cellOutCount (unionH s) (fun x ↦ x ≠ z ∧ slotOf pk x = some (.enc K.1 K.2.1 K.2.2))
    fun y ↦ Quantum.Sphincs.Codeword.Valid (pairDigest y)

/-- The cell `z` holds a codeword pair. -/
def CellCwE (z : Qrom.HashDomain) (s : RegQ) : Prop :=
  ∃ y, unionH s z = some y ∧ Quantum.Sphincs.Codeword.Valid (pairDigest y)

/-- The states whose key `K` is unselected. -/
def unselSE (K : Key) : Set (Unit × RegQ) := {q | q.2.2.2.2 K = none}

instance instDecidablePredUnselSE (K : Key) : DecidablePred (· ∈ unselSE K) :=
  fun q ↦ inferInstanceAs (Decidable (q.2.2.2.2 K = none))

/-- The states whose key `K` is unselected with a codeword pair at the cell `z`. -/
def cellSE (z : Qrom.HashDomain) (K : Key) : Set (Unit × RegQ) :=
  {q | q.2.2.2.2 K = none ∧ CellCwE z q.2}

noncomputable instance instDecidablePredCellSE (z : Qrom.HashDomain) (K : Key) :
    DecidablePred (· ∈ cellSE z K) :=
  Classical.decPred _

theorem ind_unselSE {K : Key} (q : Unit × RegQ) :
    ind (unselSE K) q = if q.2.2.2.2 K = none then 1 else 0 :=
  rfl

variable {z : Qrom.HashDomain} {K : Key}

open scoped Classical in
/-- The codeword cells of the key of `z` are those off `z` and the cell `z`. -/
theorem encCwCount_eq_off_addE (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) (s : RegQ) :
    (encCwCount pk (unionH s) K : ℝ) = offCwE pk z K s + if CellCwE z s then 1 else 0 := by
  have h := cellOutCount_eq_off_add (unionH s)
    (fun x ↦ slotOf pk x = some (.enc K.1 K.2.1 K.2.2))
    (fun y ↦ Quantum.Sphincs.Codeword.Valid (pairDigest y)) z
  change encCwCount pk (unionH s) K = offCwE pk z K s + _ at h
  rw [h, Nat.cast_add]
  by_cases hc : CellCwE z s
  · rw [ite_eq_left ⟨hz, hc⟩, ite_eq_left hc, Nat.cast_one]
  · rw [ite_eq_right fun h' ↦ hc h'.2, ite_eq_right hc, Nat.cast_zero]

/-- **The potential split at an encoding cell.** -/
theorem encPotQ_split (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) (q : Unit × RegQ) :
    encPotQ pk q.2 = encOtherE pk K q.2 + ind (unselSE K) q * offCwE pk z K q.2 +
      ind (cellSE z K) q := by
  unfold encPotQ encOtherE
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ K)]
  rw [ind_unselSE]
  unfold ind
  by_cases hu : q.2.2.2.2 K = none
  · rw [ite_eq_left hu, ite_eq_left hu, encCwCount_eq_off_addE hz]
    by_cases hc : CellCwE z q.2
    · rw [ite_eq_left hc, ite_eq_left (show q ∈ cellSE z K from ⟨hu, hc⟩)]
      ring
    · rw [ite_eq_right hc, ite_eq_right (show q ∉ cellSE z K from fun h ↦ hc h.2)]
      ring
  · rw [ite_eq_right hu, ite_eq_right hu,
      ite_eq_right (show q ∉ cellSE z K from fun h ↦ hu h.1)]
    ring

/-- The potential sees only the union view and the selections. -/
theorem encPotQ_congr {s s' : RegQ} (hU : unionH s' = unionH s) (hm : s'.2.2.2 = s.2.2.2) :
    encPotQ pk s' = encPotQ pk s := by
  unfold encPotQ
  rw [hU, hm]

/-- **Off the encoding slots the potential sees nothing**: states agreeing off a cell `z` at no
encoding slot, with the same selections, have the same potential. -/
theorem encPotQ_eq_of_off (hno : ∀ K : Key, slotOf pk z ≠ some (.enc K.1 K.2.1 K.2.2))
    {s s' : RegQ} (hU : ∀ x, x ≠ z → unionH s' x = unionH s x) (hm : s'.2.2.2 = s.2.2.2) :
    encPotQ pk s' = encPotQ pk s := by
  unfold encPotQ
  refine Finset.sum_congr rfl fun K' _ ↦ ?_
  have hc : encCwCount pk (unionH s') K' = encCwCount pk (unionH s) K' :=
    cellOutCount_congr (P := fun x ↦ slotOf pk x = some (.enc K'.1 K'.2.1 K'.2.2)) _ fun x hx ↦
      hU x fun hxz ↦ hno K' (hxz ▸ hx)
  rw [hm, hc]

/-- The count off `z` does not see `z`. -/
theorem offCwE_congr {s s' : RegQ} (hU : ∀ x, x ≠ z → unionH s' x = unionH s x) :
    offCwE pk z K s' = offCwE pk z K s :=
  cellOutCount_congr _ fun x hx ↦ hU x hx.1

theorem unionH_congr_offE {s s' : RegQ} (h1 : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b)
    (h3 : s'.2.1 = s.2.1) (x : Qrom.HashDomain) (hx : x ≠ z) : unionH s' x = unionH s x := by
  rw [unionH_apply, unionH_apply, h3, h1 x hx]

/-- The count off `z` is a weight off the cell `z`. -/
theorem offCwE_offCell : OffCell z (fun s : RegQ ↦ (offCwE pk z K s : ℝ)) :=
  fun _ _ h1 _ h3 ↦ congrArg Nat.cast (offCwE_congr (unionH_congr_offE h1 h3))

/-- The potential of the other keys does not see `z` nor the selection of `K`. -/
theorem encOtherE_congr (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) {s s' : RegQ}
    (hU : ∀ x, x ≠ z → unionH s' x = unionH s x)
    (hm : ∀ K' : Key, K' ≠ K → s'.2.2.2 K' = s.2.2.2 K') :
    encOtherE pk K s' = encOtherE pk K s := by
  unfold encOtherE
  refine Finset.sum_congr rfl fun K' hk ↦ ?_
  have hk' := Finset.ne_of_mem_erase hk
  have hc : encCwCount pk (unionH s') K' = encCwCount pk (unionH s) K' :=
    cellOutCount_congr (P := fun x ↦ slotOf pk x = some (.enc K'.1 K'.2.1 K'.2.2)) _ fun x hx ↦
      hU x fun hxz ↦ by
        subst hxz
        obtain ⟨h1, h2, h3⟩ := Slot.enc.inj (Option.some.inj (hx.symm.trans hz))
        exact hk' (Prod.ext h1 (Prod.ext h2 h3))
  rw [hm K' hk', hc]

/-- **A trial read keeps the potential of the other keys.** -/
theorem encOtherE_keep (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2))
    (r : Option PairOut × QMem) (a a' : Unit × RegQ)
    (h : hwReadKraus (.readH z (trialUpdQ K z)) r a' a ≠ 0) :
    encOtherE pk K a'.2 = encOtherE pk K a.2 := by
  obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
  obtain ⟨h1, -, h3⟩ := readKrausH_ne_zero_rest z (trialUpdQ K z) r h'
  obtain ⟨hm1, hm2⟩ := readKrausH_memQ z (trialUpdQ K z) r h'
  refine encOtherE_congr hz (unionH_congr_offE h1 h3) fun K' hk ↦ ?_
  rw [hm2, hm1, trialUpdQ_sndE]
  exact cwUpd_apply_of_neE z _ _ hk

/-! ## The other ports -/

/-- **A sponge call changes the potential by at most one** (one database cell). -/
theorem oneCellLipschitz_encPotQ :
    OneCellLipschitz (X := PairOut) (Z := Qrom.HashDomain) (M := QMem) (encPotQ pk) where
  h D b x v := by
    set s : RegQ := (D, b)
    set s' : RegQ := ((Function.update D.1 x v, D.2.1, D.2.2), b)
    have hU : ∀ y, y ≠ x → unionH s' y = unionH s y := fun y hy ↦ by
      rw [unionH_apply, unionH_apply]
      show (b.1.1 y).or (Function.update D.1 x v y) = (b.1.1 y).or (D.1 y)
      rw [Function.update_of_ne hy]
    by_cases hx : ∃ K : Key, slotOf pk x = some (.enc K.1 K.2.1 K.2.2)
    · obtain ⟨K, hx⟩ := hx
      have h1 := encPotQ_split hx ((), s)
      have h2 := encPotQ_split hx ((), s')
      have hA : encOtherE pk K s' = encOtherE pk K s := encOtherE_congr hx hU fun _ _ ↦ rfl
      have hn : offCwE pk x K s' = offCwE pk x K s := offCwE_congr hU
      have hu : ind (unselSE K) ((), s') = ind (unselSE K) ((), s) := rfl
      have hc1 := ind_le_one (cellSE x K) ((), s')
      have hc0 := ind_nonneg (cellSE x K) ((), s)
      change encPotQ pk s' ≤ encPotQ pk s + 1
      rw [h1, h2, hA, hn, hu]
      linarith
    · simp only [not_exists] at hx
      exact (encPotQ_eq_of_off hx hU rfl).le.trans (le_add_of_nonneg_right zero_le_one)
  k D b x v := (encPotQ_congr (s := (D, b)) rfl rfl).le.trans
    (le_add_of_nonneg_right zero_le_one)
  k' D b x v := (encPotQ_congr (s := (D, b)) rfl rfl).le.trans
    (le_add_of_nonneg_right zero_le_one)

/-- **A program of a cell at no encoding slot keeps the potential.** -/
theorem encPotQ_progMap (hno : ∀ K : Key, slotOf pk z ≠ some (.enc K.1 K.2.1 K.2.2))
    (a : PairOut) (s : RegQ) : encPotQ pk (progMap (.programH z a) s) = encPotQ pk s := by
  refine encPotQ_eq_of_off hno (fun x hx ↦ ?_) rfl
  rw [unionH_apply, unionH_apply]
  show (Function.update s.2.1.1 z (some a) x).or (Function.update s.1.1 z none x) =
    (s.2.1.1 x).or (s.1.1 x)
  rw [Function.update_of_ne hx, Function.update_of_ne hx]

/-! ## The count off the read cell at a trial read -/

/-- **The flip values of the unselected-key event** at a rest: the key unselected and the digest
a codeword. -/
def CwFlipE (K : Key) (z : Qrom.HashDomain) (y : PairOut) (r : RestH PairOut QMem z) : Prop :=
  (memH z r).2 K = none ∧ Quantum.Sphincs.Codeword.Valid (pairDigest y)

noncomputable instance instDecidableCwFlipE (K : Key) (z : Qrom.HashDomain) (y : PairOut)
    (r : RestH PairOut QMem z) : Decidable (CwFlipE K z y r) :=
  Classical.propDecidable _

/-- The states a trial read selects from: the cell empty, the key unselected. -/
def EmptyUnselE (z : Qrom.HashDomain) (K : Key) (s : RegQ) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z = none ∧ s.2.2.2 K = none

noncomputable instance instDecidablePredEmptyUnselE (z : Qrom.HashDomain) (K : Key) :
    DecidablePred (EmptyUnselE z K) :=
  Classical.decPred _

/-- The states whose read cell is recorded with a codeword pair, the key unselected. -/
def CwRecE (z : Qrom.HashDomain) (K : Key) (s : RegQ) : Prop :=
  s.2.1.1 z = none ∧ s.2.2.2 K = none ∧
    ∃ v, s.1.1 z = some v ∧ Quantum.Sphincs.Codeword.Valid (pairDigest v)

noncomputable instance instDecidablePredCwRecE (z : Qrom.HashDomain) (K : Key) :
    DecidablePred (CwRecE z K) :=
  Classical.decPred _

theorem ind_unselSE_symm (a : Option PairOut) (r : RestH PairOut QMem z) :
    ind (unselSE K) ((splitH' z).symm (a, r)) = if (memH z r).2 K = none then 1 else 0 :=
  rfl

/-- The weight of a recorded outcome against the unselected-key event. -/
theorem gw_unselSE (y : PairOut) (r : RestH PairOut QMem z) :
    gw (splitH' z) (tauH z (trialUpdQ K z)) (unselSE K) (some y) r =
      if (trialUpdQ K z (memH z r) (some y)).2 K = none then 1 else 0 := by
  unfold gw
  have h : ∀ a : Option PairOut, ind (unselSE K)
      ((splitH' z).symm (a, tauH z (trialUpdQ K z) (some y) r)) =
      if (trialUpdQ K z (memH z r) (some y)).2 K = none then 1 else 0 := fun a ↦ rfl
  simp only [h]
  rw [← Finset.sum_mul, sum_cr_sq, one_mul]

/-- **The diagonal cost of the unselected-key event**: `-ρ_c` on an empty, not hardwired cell
with the key unselected, at most `0` elsewhere. -/
theorem fd_unselSE_le (q : Unit × RegQ) :
    fd (splitH' z) (actH z) (tauH z (trialUpdQ K z)) (unselSE K) (phiH z (trialUpdQ K z)) q ≤
      -(Quantum.Sphincs.rhoCw * if EmptyUnselE z K q.2 then 1 else 0) := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  unfold fd
  by_cases ha : actH z (splitH' z q).2
  · have ha' : q.2.2.1.1 z = none := ha
    rw [ite_eq_left ha, ind_unselSE]
    rcases hc : (splitH' z q).1 with _ | y
    · have hc' : q.2.1.1 z = none := hc
      show (∑ y, gw (splitH' z) (tauH z (trialUpdQ K z)) (unselSE K) (some y)
          (splitH' z q).2) / Fintype.card PairOut - _ ≤ _
      simp only [gw_unselSE, hmem]
      by_cases hm : q.2.2.2.2 K = none
      · have hsum : (∑ y : PairOut, if (trialUpdQ K z q.2.2.2 (some y)).2 K = none then
            (1 : ℝ) else 0) = Fintype.card PairOut -
              ((Finset.univ.filter fun v : PairOut ↦
                Quantum.Sphincs.Codeword.Valid (pairDigest v)).card : ℝ) := by
          rw [Finset.sum_congr rfl fun y _ ↦ if_congr (trialUpdQ_unsel_iffE hm y) rfl rfl,
            Finset.sum_boole, Finset.filter_not, Finset.card_sdiff_of_subset
              (Finset.subset_univ _), Finset.card_univ, Nat.cast_sub (Finset.card_le_univ _)]
        have hN : (0 : ℝ) < Fintype.card PairOut := Nat.cast_pos.2 Fintype.card_pos
        have hE : EmptyUnselE z K q.2 := ⟨ha', hc', hm⟩
        rw [hsum, sub_div, div_self hN.ne', card_codeword_pair_div, ite_eq_left hm,
          ite_eq_left hE]
        linarith
      · have h0 : ∀ y : PairOut, (trialUpdQ K z q.2.2.2 (some y)).2 K ≠ none :=
          fun y ↦ trialUpdQ_keepE hm _
        have hR : (if EmptyUnselE z K q.2 then (1 : ℝ) else 0) = 0 :=
          ite_eq_right fun h ↦ hm h.2.2
        rw [hR, mul_zero, neg_zero, ite_eq_right hm]
        simp only [h0, ↓reduceIte, Finset.sum_const_zero, zero_div, sub_zero, le_refl]
    · have hc' : q.2.1.1 z ≠ none := by
        rw [← splitH'_apply_fst, hc]; exact Option.some_ne_none y
      show gw (splitH' z) (tauH z (trialUpdQ K z)) (unselSE K) (some y) (splitH' z q).2 - _ ≤ _
      have hR : (if EmptyUnselE z K q.2 then (1 : ℝ) else 0) = 0 :=
        ite_eq_right fun h ↦ hc' h.2.1
      rw [hR, mul_zero, neg_zero, gw_unselSE, hmem]
      by_cases hm : q.2.2.2.2 K = none
      · rw [ite_eq_left hm]
        split_ifs <;> norm_num
      · rw [ite_eq_right hm, ite_eq_right (trialUpdQ_keepE hm _), sub_zero]
  · have ha' : q.2.2.1.1 z ≠ none := ha
    have hR : (if EmptyUnselE z K q.2 then (1 : ℝ) else 0) = 0 :=
      ite_eq_right fun h ↦ ha' h.1
    rw [ite_eq_right ha, ind_unselSE, ind_unselSE, hR, mul_zero, neg_zero]
    show (if (trialUpdQ K z q.2.2.2 (q.2.2.1.1 z)).2 K = none then (1 : ℝ) else 0) - _ ≤ 0
    by_cases hm : q.2.2.2.2 K = none
    · rw [ite_eq_left hm]
      split_ifs <;> norm_num
    · rw [ite_eq_right hm, ite_eq_right (trialUpdQ_keepE hm _), sub_zero]

/-- **The empty-to-recorded weight of the unselected-key event** with the reference `q0`: `ρ_c`
on an empty, not hardwired cell with the key unselected, `0` elsewhere. -/
theorem ew_unselSE_le (q : Unit × RegQ) :
    ew (splitH' z) (actH z) (tauH z (trialUpdQ K z)) (unselSE K) (q0 (splitH' z) (unselSE K)) q ≤
      Quantum.Sphincs.rhoCw * if EmptyUnselE z K q.2 then 1 else 0 := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  unfold ew
  split_ifs with h1 h2 h2
  · have hN : (0 : ℝ) < Fintype.card PairOut := Nat.cast_pos.2 Fintype.card_pos
    have hq0 : q0 (splitH' z) (unselSE K) (splitH' z q).2 = 1 := by
      unfold q0
      rw [ind_unselSE_symm, hmem, ite_eq_left h2.2.2]
    have hterm : ∀ y : PairOut, xv (splitH' z) (tauH z (trialUpdQ K z)) (unselSE K)
        (q0 (splitH' z) (unselSE K)) (some y) (splitH' z q).2 ^ 2 =
        (if Quantum.Sphincs.Codeword.Valid (pairDigest y) then 1 else 0) /
          Fintype.card PairOut :=
      fun y ↦ by
        have hsq : ((if ¬ Quantum.Sphincs.Codeword.Valid (pairDigest y) then (1 : ℝ) else 0) -
            1) ^ 2 = if Quantum.Sphincs.Codeword.Valid (pairDigest y) then 1 else 0 := by
          split_ifs <;> norm_num
        show ((gw (splitH' z) (tauH z (trialUpdQ K z)) (unselSE K) (some y)
          (splitH' z q).2 - q0 (splitH' z) (unselSE K) (splitH' z q).2) /
            Real.sqrt (Fintype.card PairOut)) ^ 2 = _
        rw [hq0, gw_unselSE, hmem, if_congr (trialUpdQ_unsel_iffE h2.2.2 y) rfl rfl, div_pow,
          Real.sq_sqrt hN.le, hsq]
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, ← Finset.sum_div, Finset.sum_boole,
      card_codeword_pair_div, mul_one]
  · have hm : q.2.2.2.2 K ≠ none := fun hm ↦
      h2 (And.intro h1.1 (And.intro h1.2 hm) : EmptyUnselE z K q.2)
    have hq0 : q0 (splitH' z) (unselSE K) (splitH' z q).2 = 0 := by
      unfold q0
      rw [ind_unselSE_symm, hmem, ite_eq_right hm]
    have hterm : ∀ y : PairOut, xv (splitH' z) (tauH z (trialUpdQ K z)) (unselSE K)
        (q0 (splitH' z) (unselSE K)) (some y) (splitH' z q).2 ^ 2 = 0 := fun y ↦ by
      show ((gw (splitH' z) (tauH z (trialUpdQ K z)) (unselSE K) (some y)
        (splitH' z q).2 - q0 (splitH' z) (unselSE K) (splitH' z q).2) /
          Real.sqrt (Fintype.card PairOut)) ^ 2 = _
      rw [hq0, gw_unselSE, hmem, ite_eq_right (trialUpdQ_keepE hm (some y)), sub_self, zero_div]
      exact zero_pow two_ne_zero
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, Finset.sum_const_zero, mul_zero]
  · exact absurd ⟨h2.1, h2.2.1⟩ h1
  · rw [mul_zero]

/-- The cross term's support: the recorded cells of the flip values are codeword-recorded for
the unselected key. -/
theorem pd_cwFlipE_le (q : Unit × RegQ) :
    pd (splitH' z) (actH z) (CwFlipE K z) q ≤ if CwRecE z K q.2 then 1 else 0 := by
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
        exact h2 (And.intro h1 (And.intro h3.1 ⟨y, hc', h3.2⟩) : CwRecE z K q.2)
      · exact le_rfl
  · norm_num
  · exact le_rfl

/-- Off the flip values a recorded outcome weighs the reference weight `q0`. -/
theorem gw_eq_q0_of_not_cwFlipE (r : RestH PairOut QMem z) (y : PairOut)
    (hy : ¬ CwFlipE K z y r) :
    gw (splitH' z) (tauH z (trialUpdQ K z)) (unselSE K) (some y) r =
      q0 (splitH' z) (unselSE K) r := by
  unfold q0
  rw [gw_unselSE, ind_unselSE_symm]
  by_cases hm : (memH z r).2 K = none
  · rw [ite_eq_left hm, ite_eq_left ((trialUpdQ_unsel_iffE hm y).2 fun hv ↦ hy ⟨hm, hv⟩)]
  · rw [ite_eq_right hm, ite_eq_right (trialUpdQ_keepE hm _)]

/-- The unselected `n`-weighted mass is the event weight of `N σ N`. -/
theorem re_trace_indProj_sqrtDiagE {n : RegQ → ℝ} (hn0 : ∀ s, 0 ≤ n s)
    (σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ) :
    (indProj (unselSE K) * (sqrtDiag n * σ * sqrtDiag n)).trace.re =
      dW (fun q ↦ ind (unselSE K) q * n q.2) σ := by
  rw [indProj, re_trace_diagonal_mul]
  unfold dW
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [re_sqrtDiag_conj_apply hn0]
  exact (mul_assoc _ _ _).symm

/-- The unselected `n`-weighted mass after a trial read: the mass before plus the flip of the
unselected-key event on `N σ N`. -/
theorem unsel_post_eqE {n : RegQ → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    (σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ) :
    ∑ r : Option PairOut × QMem, dW (fun q ↦ ind (unselSE K) q * n q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ) =
      dW (fun q ↦ ind (unselSE K) q * n q.2) σ +
        (flipOp (fun r : Option PairOut × QMem ↦ hwReadKraus (.readH z (trialUpdQ K z)) r)
          (unselSE K) * (sqrtDiag n * σ * sqrtDiag n)).trace.re := by
  have h1 : ∀ r, dW (fun q ↦ ind (unselSE K) q * n q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ) =
      dW (fun q ↦ ind (unselSE K) q)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r)
          (sqrtDiag n * σ * sqrtDiag n)) :=
    fun r ↦ (dW_conj_sqrtDiagG z (trialUpdQ K z) hn0 hn (fun q ↦ ind (unselSE K) q) r σ).symm
  have hsumeq : (∑ r : Option PairOut × QMem,
      (hwReadKraus (.readH z (trialUpdQ K z)) r)ᴴ *
        diagonal (fun q ↦ ((ind (unselSE K) q : ℝ) : ℂ)) *
          hwReadKraus (.readH z (trialUpdQ K z)) r) =
      flipOp (fun r : Option PairOut × QMem ↦ hwReadKraus (.readH z (trialUpdQ K z)) r)
        (unselSE K) + indProj (unselSE K) := by
    rw [flipOp, sub_add_cancel]
    rfl
  rw [Finset.sum_congr rfl fun r _ ↦ h1 r, sum_dW_conj, hsumeq, Matrix.add_mul,
    Matrix.trace_add, Complex.add_re, add_comm, re_trace_indProj_sqrtDiagE hn0 σ]

/-- **The flip of the unselected-key event at a trial read, `n`-weighted**: at most
`-ρ_c e + 2 √(ρ_c e p)`, `e` the `n`-weighted `EmptyUnselE` mass and `p` the `n`-weighted `CwRecE`
mass. -/
theorem unselFlip_leE {n : RegQ → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option PairOut × QMem ↦ hwReadKraus (.readH z (trialUpdQ K z)) r)
        (unselSE K) * (sqrtDiag n * σ * sqrtDiag n)).trace.re ≤
      -(Quantum.Sphincs.rhoCw *
          ∑ q, (if EmptyUnselE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re)) +
        2 * √(Quantum.Sphincs.rhoCw *
          (∑ q, (if EmptyUnselE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re)) *
            ∑ q, (if CwRecE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re)) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hτ : (sqrtDiag n * σ * sqrtDiag n).PosSemidef := posSemidef_sqrtDiag_conjG n hσ
  have hdiag : ∀ q, ((sqrtDiag n * σ * sqrtDiag n) q q).re = n q.2 * (σ q q).re :=
    re_sqrtDiag_conj_apply hn0 σ
  have hnσ : ∀ q, 0 ≤ n q.2 * (σ q q).re := fun q ↦ mul_nonneg (hn0 _) (hre q)
  have hF := re_trace_flipOp_le (unselSE K) (cellRead_readH z (trialUpdQ K z))
    (clsOff_readH z (trialUpdQ K z)) (q0 (splitH' z) (unselSE K)) (CwFlipE K z)
    (fun r _ y hy ↦ gw_eq_q0_of_not_cwFlipE r y hy) hτ (cellNoBot_sqrtDiagG hn hnb)
  have he : 0 ≤ ∑ q, (if EmptyUnselE z K q.2 then (1 : ℝ) else 0) * (n q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hnσ q)
  have hfd : ∑ s, fd (splitH' z) (actH z) (tauH z (trialUpdQ K z)) (unselSE K)
      (phiH z (trialUpdQ K z)) s * ((sqrtDiag n * σ * sqrtDiag n) s s).re ≤
      -(Quantum.Sphincs.rhoCw *
        ∑ q, (if EmptyUnselE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (fd_unselSE_le q) (hnσ q)).trans_eq (by ring)
  have hew : ∑ s, ew (splitH' z) (actH z) (tauH z (trialUpdQ K z)) (unselSE K)
      (q0 (splitH' z) (unselSE K)) s * ((sqrtDiag n * σ * sqrtDiag n) s s).re ≤
      Quantum.Sphincs.rhoCw *
        ∑ q, (if EmptyUnselE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (ew_unselSE_le q) (hnσ q)).trans_eq (by ring)
  have hpd : ∑ s, pd (splitH' z) (actH z) (CwFlipE K z) s *
      ((sqrtDiag n * σ * sqrtDiag n) s s).re ≤
      ∑ q, (if CwRecE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re) :=
    Finset.sum_le_sum fun q _ ↦ by
      rw [hdiag]
      exact mul_le_mul_of_nonneg_right (pd_cwFlipE_le q) (hnσ q)
  have hP0 : 0 ≤ ∑ s, pd (splitH' z) (actH z) (CwFlipE K z) s *
      ((sqrtDiag n * σ * sqrtDiag n) s s).re :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      rcases pd_mem (e := splitH' z) (act := actH z) (CwFlipE K z) q with h | h <;>
        simp only [h, le_refl, zero_le_one]) (by rw [hdiag]; exact hnσ q)
  refine hF.trans (add_le_add hfd (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
  rw [← Real.sqrt_mul' _ hP0]
  exact Real.sqrt_le_sqrt (mul_le_mul hew hpd hP0 (mul_nonneg rhoCw_nonnegE he))

/-- **The unselected count off the read cell at a trial read**: `2^-15 e` plus the
`n`-weighted unselected mass after the read is at most the one before plus `3 p`. -/
theorem unselRead_dropE {n : RegQ → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 15 : ℝ)⁻¹ * (∑ q, (if EmptyUnselE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re)) +
      ∑ r : Option PairOut × QMem, dW (fun q ↦ ind (unselSE K) q * n q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ) ≤
    dW (fun q ↦ ind (unselSE K) q * n q.2) σ +
      3 * ∑ q, (if CwRecE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hnσ : ∀ q, 0 ≤ n q.2 * (σ q q).re := fun q ↦ mul_nonneg (hn0 _) (hre q)
  refine drop_of_surviveE (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num)
    (hnσ q)) (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hnσ q))
    Quantum.Sphincs.inv_two_pow_14_le_rhoCw ?_
  rw [unsel_post_eqE hn0 hn σ]
  have h := unselFlip_leE (K := K) hn0 hn hσ hnb
  have hp : 0 ≤ ∑ q, (if CwRecE z K q.2 then (1 : ℝ) else 0) * (n q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hnσ q)
  linarith

/-! ## The read cell at a trial read -/

/-- The outcome states of a trial read are outside `cellSE`: a codeword pair selects the key. -/
theorem not_mem_cellSE_out {r : RestH PairOut QMem z} (hr : actH z r) (y : PairOut) :
    (splitH' z).symm (some y, tauH z (trialUpdQ K z) (some y) r) ∉ cellSE z K := by
  rintro ⟨hu, y', hy', hcw⟩
  have hw : ((splitH' z).symm (some y, tauH z (trialUpdQ K z) (some y) r)).2.2.1.1 z = none :=
    hr
  rw [unionH_apply, hw, splitH'_symm_cellG] at hy'
  obtain rfl := Option.some.inj hy'
  have hu' : (trialUpdQ K z (memH z r) (some y)).2 K = none := hu
  by_cases hm : (memH z r).2 K = none
  · exact (trialUpdQ_unsel_iffE hm y).1 hu' hcw
  · exact trialUpdQ_keepE hm _ hu'

/-- The classical move of a hardwired cell leaves `cellSE`. -/
theorem not_mem_cellSE_phiH (q : Unit × RegQ) (hq : q.2.2.1.1 z ≠ none) :
    phiH z (trialUpdQ K z) q ∉ cellSE z K := by
  rintro ⟨hu, y', hy', hcw⟩
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hq
  have hy2 : (q.2.2.1.1 z).or (q.2.1.1 z) = some y' := hy'
  rw [hw] at hy2
  obtain rfl := Option.some.inj hy2
  have hu' : (trialUpdQ K z q.2.2.2 (some w)).2 K = none := by
    have h := hu
    change (trialUpdQ K z q.2.2.2 (q.2.2.1.1 z)).2 K = none at h
    rwa [hw] at h
  by_cases hm : q.2.2.2.2 K = none
  · exact (trialUpdQ_unsel_iffE hm w).1 hu' hcw
  · exact trialUpdQ_keepE hm _ hu'

/-- **The read cell after a trial read**: the flip into `cellSE` is at most `2/|Y| + 4/|Y|²` per
unit of trace plus the recorded mass of the unselected key at the cell. -/
theorem cellFlip_leE {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option PairOut × QMem ↦ hwReadKraus (.readH z (trialUpdQ K z)) r)
        (cellSE z K) * σ).trace.re ≤
      ∑ q, ((2 / (Fintype.card PairOut : ℝ) + (2 / (Fintype.card PairOut : ℝ)) ^ 2) +
        (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 K = none then 1 else 0)) *
          (σ q q).re := by
  classical
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set DU : PairOut → RestH PairOut QMem z → Prop := fun _ r ↦ (memH z r).2 K = none
  have hD : ∀ r, actH z r → ∀ y, ¬ DU y r →
      gw (splitH' z) (tauH z (trialUpdQ K z)) (cellSE z K) (some y) r = 0 := by
    intro r _ y hy
    unfold gw
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [ind_eq_zero_of_not_mem (cellSE z K) fun h ↦ trialUpdQ_keepE hy (some y) h.1, mul_zero]
  have hF := re_trace_flipOp_le (cellSE z K) (cellRead_readH z (trialUpdQ K z))
    (clsOff_readH z (trialUpdQ K z)) (fun _ ↦ 0) DU hD hσ hnb
  set N : ℝ := (Fintype.card PairOut : ℝ)
  set E := ∑ s, ew (splitH' z) (actH z) (tauH z (trialUpdQ K z)) (cellSE z K)
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
  have hgw : ∀ s : Unit × RegQ, actH z (splitH' z s).2 → ∀ y,
      gw (splitH' z) (tauH z (trialUpdQ K z)) (cellSE z K) (some y) (splitH' z s).2 ≤ 2 / N :=
    fun s ha y ↦ gw_some_le_two_div (cellSE z K)
      (ind_eq_zero_of_not_mem (cellSE z K) (not_mem_cellSE_out ha y))
  have hpt : ∀ s, fd (splitH' z) (actH z) (tauH z (trialUpdQ K z)) (cellSE z K)
      (phiH z (trialUpdQ K z)) s + ew (splitH' z) (actH z) (tauH z (trialUpdQ K z))
        (cellSE z K) (fun _ ↦ 0) s ≤ 2 / N + (2 / N) ^ 2 := fun s ↦ by
    refine add_le_add ?_ ?_
    · unfold fd
      split_ifs with ha
      · exact (sub_le_self _ (ind_nonneg _ s)).trans (gdiag_le_of _ (hgw s ha) _)
      · rw [ind_eq_zero_of_not_mem (cellSE z K) (not_mem_cellSE_phiH s ha), zero_sub]
        exact (neg_nonpos.2 (ind_nonneg _ s)).trans (by positivity)
    · by_cases ha : actH z (splitH' z s).2
      · exact ew_zero_le_of _ (hgw s ha)
      · unfold ew
        rw [ite_eq_right fun h' ↦ ha h'.1]
        positivity
  have hpd : ∀ s : Unit × RegQ, pd (splitH' z) (actH z) DU s ≤
      if s.2.2.1.1 z = none ∧ s.2.1.1 z ≠ none ∧ s.2.2.2.2 K = none then 1 else 0 := by
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
  calc _ ≤ ∑ s, fd (splitH' z) (actH z) (tauH z (trialUpdQ K z)) (cellSE z K)
        (phiH z (trialUpdQ K z)) s * (σ s s).re + (E + p) :=
        hF.trans (add_le_add le_rfl hsq)
    _ = ∑ s, (fd (splitH' z) (actH z) (tauH z (trialUpdQ K z)) (cellSE z K)
          (phiH z (trialUpdQ K z)) s + ew (splitH' z) (actH z) (tauH z (trialUpdQ K z))
            (cellSE z K) (fun _ ↦ 0) s + pd (splitH' z) (actH z) DU s) * (σ s s).re := by
        simp only [E, p, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right
        (add_le_add (hpt s) (hpd s)) (hre s)

/-! ## A trial read -/

/-- **The database count of the codeword cells off `z`** at a recorded read cell of an
`EncFree` register: one less than the recorded cells, at most. -/
theorem offCwE_add_one_le {s : RegQ} (hM : EncFree pk s) (hD : s.1.1 z ≠ none) :
    offCwE pk z K s + 1 ≤ s.1.1.size := by
  have h1 : offCwE pk z K s ≤ (Finset.univ.filter fun x ↦ x ≠ z ∧ (s.1.1 x).isSome).card := by
    refine cellOutCount_le_card _ fun x y hx hy ↦ ⟨hx.1, ?_⟩
    have hw : s.2.1.1 x = none := hw_none_of_encFreeE hM hx.2
    rw [unionH_apply, hw] at hy
    change s.1.1 x = some y at hy
    rw [hy]
    rfl
  have h2 := card_filter_eq_off_add (fun x ↦ (s.1.1 x).isSome) z
  rw [ite_eq_left (Option.ne_none_iff_isSome.mp hD)] at h2
  have h3 : s.1.1.size = (Finset.univ.filter fun x ↦ (s.1.1 x).isSome).card := rfl
  omega

/-- The re-compression term of a trial read: `2/|Y × Y| + 4/|Y × Y|² ≤ 2^-510`. -/
theorem recompress_leE :
    2 / (Fintype.card PairOut : ℝ) + (2 / (Fintype.card PairOut : ℝ)) ^ 2 ≤ (2 ^ 510 : ℝ)⁻¹ := by
  have hN : (Fintype.card PairOut : ℝ) = 2 ^ 2 * 2 ^ 510 := by
    rw [← pow_add, Fintype.card_prod, Quantum.Qrom.Xmss.card_hashOutput, ← pow_add,
      Nat.cast_pow, Nat.cast_ofNat]
  have hu0 : (0 : ℝ) ≤ (2 ^ 510 : ℝ)⁻¹ := by positivity
  have hu1 : (2 ^ 510 : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [hN, div_eq_mul_inv, mul_inv]
  generalize (2 ^ 510 : ℝ)⁻¹ = u at hu0 hu1 ⊢
  have huu : u * u ≤ u := mul_le_of_le_one_left hu0 hu1
  nlinarith

open scoped Classical in
/-- **A trial read on the potential, in `ℝ`**: on states supported on `EncFree` registers of
database grade at most `G`, with no decompressed `⊥` at the cell, `2^-15 encWt` plus the potential
after the read is at most the potential before plus `4 G recUWt + 2^-510 tr σ`. -/
theorem trialRead_dropE (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) {G : ℕ}
    {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ)
    (hinv : ∀ q, σ q q ≠ 0 → EncFree pk q.2 ∧ dbGrade q.2.1 ≤ G) :
    (2 ^ 15 : ℝ)⁻¹ * (∑ q, encWt pk z K q.2 * (σ q q).re) +
        ∑ r : Option PairOut × QMem, dW (fun q ↦ encPotQ pk q.2)
          (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ) ≤
      dW (fun q ↦ encPotQ pk q.2) σ + 4 * G * (∑ q, recUWt z K q.2 * (σ q q).re) +
        (2 ^ 510 : ℝ)⁻¹ * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set n : RegQ → ℝ := fun s ↦ (offCwE pk z K s : ℝ)
  have hn0 : ∀ s, 0 ≤ n s := fun s ↦ Nat.cast_nonneg _
  have hsplit : (fun q : Unit × RegQ ↦ encPotQ pk q.2) = fun q ↦
      (fun q ↦ encOtherE pk K q.2 + ind (unselSE K) q * n q.2) q + ind (cellSE z K) q :=
    funext fun q ↦ encPotQ_split hz q
  have hdW : ∀ τ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ,
      dW (fun q ↦ encPotQ pk q.2) τ = dW (fun q ↦ encOtherE pk K q.2) τ +
        dW (fun q ↦ ind (unselSE K) q * n q.2) τ + dW (ind (cellSE z K)) τ := fun τ ↦ by
    rw [hsplit, dW_add, dW_add]
  simp only [hdW, Finset.sum_add_distrib]
  -- The other keys keep their part.
  have hA : ∑ r : Option PairOut × QMem, dW (fun q ↦ encOtherE pk K q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ) =
      dW (fun q ↦ encOtherE pk K q.2) σ :=
    sum_dW_conj_of_keep (fun r : Option PairOut × QMem ↦
      hwReadKraus (.readH z (trialUpdQ K z)) r) _ (encOtherE_keep hz)
      (sum_readKrausH z (trialUpdQ K z)) σ
  -- The count off the cell.
  have hB := unselRead_dropE (K := K) hn0 offCwE_offCell hσ hnb
  -- The cell itself.
  have hCeq : ∑ r : Option PairOut × QMem, dW (ind (cellSE z K))
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ) =
      dW (ind (cellSE z K)) σ + (flipOp (fun r : Option PairOut × QMem ↦
        hwReadKraus (.readH z (trialUpdQ K z)) r) (cellSE z K) * σ).trace.re := by
    rw [sum_dW_conj, dW_eq_trace, flipOp, indProj, Matrix.sub_mul, Matrix.trace_sub,
      Complex.sub_re]
    ring
  have hC := cellFlip_leE (K := K) hσ hnb
  -- The Enc weight is the weight of the empty reads.
  have hEnc : ∑ q, encWt pk z K q.2 * (σ q q).re =
      ∑ q, (if EmptyUnselE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re) := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp [h0]
    have hW : q.2.2.1.1 z = none := hw_none_of_encFreeE (hinv q h0).1 hz
    unfold encWt
    by_cases hE : q.2.1.1 z = none ∧ q.2.2.2.2 K = none
    · have hc : ¬ CellCwE z q.2 := by
        rintro ⟨y, hy, -⟩
        rw [unionH_apply, hW, hE.1] at hy
        cases hy
      rw [ite_eq_left hE, ite_eq_left (show EmptyUnselE z K q.2 from ⟨hW, hE⟩),
        encCwCount_eq_off_addE hz, ite_eq_right hc, add_zero, one_mul]
    · rw [ite_eq_right hE, ite_eq_right fun h ↦ hE ⟨h.2.1, h.2.2⟩]
      ring
  -- The recorded charges.
  have hRec : 3 * (∑ q, (if CwRecE z K q.2 then 1 else 0) * (n q.2 * (σ q q).re)) +
      ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 K = none then 1 else 0) *
        (σ q q).re ≤ 4 * G * (∑ q, recUWt z K q.2 * (σ q q).re) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp [h0]
    obtain ⟨hM, hG⟩ := hinv q h0
    by_cases hR : q.2.1.1 z ≠ none ∧ q.2.2.2.2 K = none
    · have hU : recUWt z K q.2 = 1 := ite_eq_left hR
      have hsz := offCwE_add_one_le (K := K) hM hR.1
      have hgr : Database.size q.2.1.1 ≤ G := (le_max_left _ _).trans hG
      have hnG : n q.2 + 1 ≤ G := by
        show (offCwE pk z K q.2 : ℝ) + 1 ≤ G
        exact_mod_cast hsz.trans hgr
      have h1 : (if CwRecE z K q.2 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have h2 : (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 K = none then (1 : ℝ)
          else 0) ≤ 1 := by split_ifs <;> norm_num
      rw [hU]
      have hn := hn0 q.2
      have hq := hre q
      have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
      have h3 : 3 * ((if CwRecE z K q.2 then (1 : ℝ) else 0) * (n q.2 * (σ q q).re)) ≤
          3 * (n q.2 * (σ q q).re) := by
        have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hn hq)
        linarith
      have h4 := mul_le_mul_of_nonneg_right h2 hq
      have h5 : (3 * n q.2 + 1) * (σ q q).re ≤ 4 * G * (σ q q).re :=
        mul_le_mul_of_nonneg_right (by linarith) hq
      linarith
    · have hc : ¬ CwRecE z K q.2 := fun h ↦ hR ⟨by
        obtain ⟨v, hv, -⟩ := h.2.2
        rw [hv]
        exact Option.some_ne_none v, h.2.1⟩
      rw [ite_eq_right hc, ite_eq_right fun h ↦ hR ⟨h.2.1, h.2.2⟩]
      have hU0 : 0 ≤ recUWt z K q.2 := by
        unfold recUWt
        exact ite_nonneg zero_le_one le_rfl
      simp only [zero_mul, mul_zero, add_zero]
      exact mul_nonneg (by positivity) (mul_nonneg hU0 (hre q))
  -- The re-compression term.
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  have hCsum : ∑ q, ((2 / (Fintype.card PairOut : ℝ) +
      (2 / (Fintype.card PairOut : ℝ)) ^ 2) +
        (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 K = none then 1 else 0)) *
          (σ q q).re = (2 / (Fintype.card PairOut : ℝ) +
            (2 / (Fintype.card PairOut : ℝ)) ^ 2) * σ.trace.re +
        ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 K = none then 1 else 0) *
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
theorem trialRead_potential_leE (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)) {G : ℕ}
    {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ)
    (hinv : ∀ q, σ q q ≠ 0 → EncFree pk q.2 ∧ dbGrade q.2.1 ≤ G) :
    (2 ^ 15 : ℝ≥0∞)⁻¹ * trialW pk (encWt pk) (trialRead z K) σ +
        ∑' r, potential (diagPot fun s ↦ √(encPotQ pk s))
          (MatrixMap.conj (hwReadKraus (trialRead z K) r) σ) ≤
      potential (diagPot fun s ↦ √(encPotQ pk s)) σ +
        (4 * (G : ℝ≥0∞) * trialW pk recUWt (trialRead z K) σ +
          (2 ^ 510 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hpot : ∀ τ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ,
      potential (diagPot fun s ↦ √(encPotQ pk s)) τ =
        ENNReal.ofReal (dW (fun q ↦ encPotQ pk q.2) τ) :=
    fun τ ↦ potential_diagPot_sqrt encPotQ_nonneg τ
  have hpost : ∀ r, 0 ≤ dW (fun q : Unit × RegQ ↦ encPotQ pk q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ) := fun r ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPotQ_nonneg q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  have hE0 : 0 ≤ ∑ q, encWt pk z K q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
    mul_nonneg (by unfold encWt; split_ifs <;> positivity) (hre q)
  have hU0 : 0 ≤ ∑ q, recUWt z K q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
    mul_nonneg (by unfold recUWt; split_ifs <;> norm_num) (hre q)
  have hP0 : 0 ≤ dW (fun q : Unit × RegQ ↦ encPotQ pk q.2) σ :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPotQ_nonneg q.2) (hre q)
  have htr0 : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have key := trialRead_dropE hz hσ hnb hinv
  rw [trialW_trialRead _ hz, trialW_trialRead _ hz, hpot, trialRead_eq]
  simp only [hpot]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hpost r]
  calc (2 ^ 15 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ q, encWt pk z K q.2 * (σ q q).re) +
        ENNReal.ofReal (∑ r : Option PairOut × QMem, dW (fun q ↦ encPotQ pk q.2)
          (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ))
      = ENNReal.ofReal ((2 ^ 15 : ℝ)⁻¹ * (∑ q, encWt pk z K q.2 * (σ q q).re) +
          ∑ r : Option PairOut × QMem, dW (fun q ↦ encPotQ pk q.2)
            (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ K z)) r) σ)) := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun r _ ↦ hpost r),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (dW (fun q ↦ encPotQ pk q.2) σ +
          4 * G * (∑ q, recUWt z K q.2 * (σ q q).re) + (2 ^ 510 : ℝ)⁻¹ * σ.trace.re) :=
        ENNReal.ofReal_le_ofReal key
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add hP0 (by positivity), add_assoc,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
          ENNReal.ofReal_ofNat]

end Quantum.Qrom.Sphincs

end
