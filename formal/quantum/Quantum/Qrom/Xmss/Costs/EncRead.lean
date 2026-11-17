module

public import Quantum.Qrom.Xmss.Costs.Ports

@[expose] public section

/-!
# The Enc potential of runtime 2 at one port

The Enc weights of the challenge prefix (`encPre`) are bounded by a diagonal potential argument
(CostJoint): the potential `encPotQ` is the number of codeword cells at the message slots of the
unselected keys (`msgCwCount`), label free and `0` at the empty register. This file proves the
port conditions.

* **Splitting at a read cell** (`encPotQ_split`): at a message-digest cell `z` of key `(l, e)`,
  `encPotQ` is the part of the other keys (`encOtherQ`, kept by a trial read of `z`:
  `encOtherQ_keep`), the unselected count of the key off `z` (`offCwQ`, which does not see `z`)
  and the indicator of `z` holding a codeword output with the key unselected (`cellS`).
* **A trial read** (`trialRead_drop`, `trialRead_potential_le`): on a state supported on
  `MsgFree` registers of database grade at most `G`, with no decompressed `⊥` at the cell,
  `2^-22 encWt` plus the potential after the read is at most the potential before plus
  `4 G recUWt + 2^-250 tr σ`. The count off `z` survives with the codeword fraction
  `ρ_c ≥ 2^-21` (`unselRead_dropQ`, the cross term only on the codeword-recorded cells of the
  unselected key); the cell `z` after the read costs re-compression and the recorded mass of the
  unselected key (`cellFlip_le`).
* **The other ports**: a sponge call changes one database cell, so `encPotQ` is one-cell
  Lipschitz (`oneCellLipschitz_encPotQ`); a program of an exempt cell (never at a message slot,
  `not_msg_of_exemptCell`) keeps it (`encPotQ_progMap`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss (Slot)
open Quantum.Xmss.Assembly (OffCell sqrtDiag sqrtDiag_conjTranspose sqrtDiag_mul_readH
  re_sqrtDiag_conj_apply readKrausH_ne_zero_rest drop_of_survive potential_diagPot_sqrt)

attribute [local irreducible] xmssRom

/- Instance search for the register with its trivial public register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## Counts of cells -/

section Generic

variable {D Y : Type} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]

omit [DecidableEq D] [Fintype Y] [DecidableEq Y] in
/-- A count does not see the cells outside its predicate. -/
theorem cellOutCount_congr {U U' : D → Option Y} {P : D → Prop} (Qo : Y → Prop)
    (h : ∀ x, P x → U' x = U x) : cellOutCount U' P Qo = cellOutCount U P Qo := by
  unfold cellOutCount
  refine congrArg Finset.card (Finset.ext fun x ↦ ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_right fun hx ↦ by rw [h x hx]

omit [Fintype Y] [DecidableEq Y] in
open scoped Classical in
/-- A count is the count off a cell `a` plus the cell `a`. -/
theorem cellOutCount_eq_off_add (U : D → Option Y) (P : D → Prop) (Qo : Y → Prop) (a : D) :
    cellOutCount U P Qo = cellOutCount U (fun x ↦ x ≠ a ∧ P x) Qo +
      if P a ∧ ∃ y, U a = some y ∧ Qo y then 1 else 0 := by
  unfold cellOutCount
  convert card_filter_eq_off_add (fun x ↦ P x ∧ ∃ y, U x = some y ∧ Qo y) a using 3
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]

omit [DecidableEq D] [Fintype Y] [DecidableEq Y] in
/-- A count is at most the cells of a predicate holding at its counted cells. -/
theorem cellOutCount_le_card {U : D → Option Y} {P : D → Prop} {Qo : Y → Prop}
    (S : D → Prop) [DecidablePred S] (h : ∀ x y, P x → U x = some y → S x) :
    cellOutCount U P Qo ≤ (Finset.univ.filter S).card := by
  unfold cellOutCount
  refine Finset.card_le_card fun x hx ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨hP, y, hy, -⟩ := hx
  exact h x y hP hy

end Generic

/-! ## Facts about the selections and the cells -/

/-- A trial read keeps the selections of the other keys. -/
theorem cwUpd_apply_of_ne {l l' : Layer} {e e' : KeyIndex} (z : HashDomain) (m : SelMem)
    (o : Option HashOutput) (h : ¬(l' = l ∧ e' = e)) : cwUpd l e z m o l' e' = m l' e' := by
  cases o with
  | none => rfl
  | some v =>
    show (if m l e = none then cwSel m l e z v else m) l' e' = m l' e'
    split_ifs
    · unfold cwSel
      split_ifs
      · exact SelMem.select_of_ne m z _ h
      · rfl
    · rfl

theorem trialUpdQ_unsel_iff {z : HashDomain} {l : Layer} {e : KeyIndex} {m : QMem}
    (hm : m.2 l e = none) (v : HashOutput) :
    (trialUpdQ l e z m (some v)).2 l e = none ↔ ¬ Codeword.Valid (truncateHash v) := by
  show cwUpd l e z m.2 (some v) l e = none ↔ _
  rw [cwUpd_some_of_none l e z hm v]
  exact cwSel_eq_none_iff hm z v

theorem trialUpdQ_keep {z : HashDomain} {l : Layer} {e : KeyIndex} {m : QMem}
    (hm : m.2 l e ≠ none) (o : Option HashOutput) : (trialUpdQ l e z m o).2 l e ≠ none := by
  show cwUpd l e z m.2 o l e ≠ none
  rw [cwUpd_of_ne_none hm]
  exact hm

/-- `HashDomain` has a second element. -/
theorem exists_ne_hashDomain (z : HashDomain) : ∃ c : HashDomain, c ≠ z := by
  have hi : 0 < maxLen := by unfold maxLen; norm_num
  refine ⟨(z.1, fun j ↦ if z.2 j = 0 then 1 else 0), fun h ↦ ?_⟩
  have h2 := congrFun (congrArg Prod.snd h) ⟨0, hi⟩
  dsimp only at h2
  split_ifs at h2 with h0
  · rw [h0] at h2
    exact absurd h2 (by decide)
  · exact h0 h2.symm

/-- **An exempt cell is not at a message slot**: there a selection at another cell gives it a
target. -/
theorem not_msg_of_exemptCell {hon : HonestCells} {z : HashDomain} (hz : ExemptCell hon z)
    (l : Layer) (e : KeyIndex) : slotOf z ≠ some (.msg l e) := by
  intro hs
  obtain ⟨c, hc⟩ := exists_ne_hashDomain z
  have h := hz (fun _ ↦ some 0) (fun _ _ ↦ some (c, 0)) rfl
  simp [tgtDigest, hs, slotDigest_msg, hc] at h

theorem hw_none_of_msgFree {s : RReg SelMem} (hM : MsgFree s) {x : HashDomain} {l : Layer}
    {e : KeyIndex} (hx : slotOf x = some (.msg l e)) : s.2.1.1 x = none := by
  by_contra h
  exact hM x (Option.ne_none_iff_isSome.mp h) l e hx

/-! ## The potential -/

/-- **The Enc potential**: the codeword cells at the message slots of the unselected keys. -/
noncomputable def encPotQ (s : RReg SelMem) : ℝ :=
  ∑ k : Layer × KeyIndex, if s.2.2.2 k.1 k.2 = none then (msgCwCount (unionH s) k.1 k.2 : ℝ)
    else 0

theorem encPotQ_nonneg (s : RReg SelMem) : 0 ≤ encPotQ s :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity

/-- The potential of the keys other than `k₀`. -/
noncomputable def encOtherQ (k₀ : Layer × KeyIndex) (s : RReg SelMem) : ℝ :=
  ∑ k ∈ Finset.univ.erase k₀, if s.2.2.2 k.1 k.2 = none then
    (msgCwCount (unionH s) k.1 k.2 : ℝ) else 0

/-- The codeword cells at the message slot of key `(l, e)` other than `z`. -/
noncomputable def offCwQ (z : HashDomain) (l : Layer) (e : KeyIndex) (s : RReg SelMem) : ℕ :=
  cellOutCount (unionH s) (fun x ↦ x ≠ z ∧ slotOf x = some (.msg l e))
    fun y ↦ Codeword.Valid (truncateHash y)

/-- The cell `z` holds a codeword output. -/
def CellCwQ (z : HashDomain) (s : RReg SelMem) : Prop :=
  ∃ y, unionH s z = some y ∧ Codeword.Valid (truncateHash y)

/-- The states whose key `(l, e)` is unselected. -/
def unselS (l : Layer) (e : KeyIndex) : Set (Unit × RReg SelMem) := {q | q.2.2.2.2 l e = none}

instance instDecidablePredUnselS (l : Layer) (e : KeyIndex) :
    DecidablePred (· ∈ unselS l e) :=
  fun q ↦ inferInstanceAs (Decidable (q.2.2.2.2 l e = none))

/-- The states whose key `(l, e)` is unselected with a codeword output at the cell `z`. -/
def cellS (z : HashDomain) (l : Layer) (e : KeyIndex) : Set (Unit × RReg SelMem) :=
  {q | q.2.2.2.2 l e = none ∧ CellCwQ z q.2}

noncomputable instance instDecidablePredCellS (z : HashDomain) (l : Layer) (e : KeyIndex) :
    DecidablePred (· ∈ cellS z l e) :=
  Classical.decPred _

theorem ind_unselS {l : Layer} {e : KeyIndex} (q : Unit × RReg SelMem) :
    ind (unselS l e) q = if q.2.2.2.2 l e = none then 1 else 0 :=
  rfl

variable {z : HashDomain} {l : Layer} {e : KeyIndex}

open scoped Classical in
/-- The codeword cells of the key of `z` are those off `z` and the cell `z`. -/
theorem msgCwCount_eq_off_add (hz : slotOf z = some (.msg l e)) (s : RReg SelMem) :
    (msgCwCount (unionH s) l e : ℝ) = offCwQ z l e s + if CellCwQ z s then 1 else 0 := by
  have h := cellOutCount_eq_off_add (unionH s) (fun x ↦ slotOf x = some (.msg l e))
    (fun y ↦ Codeword.Valid (truncateHash y)) z
  change msgCwCount (unionH s) l e = offCwQ z l e s + _ at h
  rw [h, Nat.cast_add]
  by_cases hc : CellCwQ z s
  · rw [ite_eq_left ⟨hz, hc⟩, ite_eq_left hc, Nat.cast_one]
  · rw [ite_eq_right fun h' ↦ hc h'.2, ite_eq_right hc, Nat.cast_zero]

/-- **The potential split at a message-digest cell.** -/
theorem encPotQ_split (hz : slotOf z = some (.msg l e)) (q : Unit × RReg SelMem) :
    encPotQ q.2 = encOtherQ (l, e) q.2 + ind (unselS l e) q * offCwQ z l e q.2 +
      ind (cellS z l e) q := by
  unfold encPotQ encOtherQ
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (l, e))]
  dsimp only
  rw [ind_unselS]
  unfold ind
  by_cases hu : q.2.2.2.2 l e = none
  · rw [ite_eq_left hu, ite_eq_left hu, msgCwCount_eq_off_add hz]
    by_cases hc : CellCwQ z q.2
    · rw [ite_eq_left hc, ite_eq_left (show q ∈ cellS z l e from ⟨hu, hc⟩)]
      ring
    · rw [ite_eq_right hc, ite_eq_right (show q ∉ cellS z l e from fun h ↦ hc h.2)]
      ring
  · rw [ite_eq_right hu, ite_eq_right hu,
      ite_eq_right (show q ∉ cellS z l e from fun h ↦ hu h.1)]
    ring

/-- The potential sees only the union view and the selections. -/
theorem encPotQ_congr {s s' : RReg SelMem} (hU : unionH s' = unionH s)
    (hm : s'.2.2.2 = s.2.2.2) : encPotQ s' = encPotQ s := by
  unfold encPotQ
  rw [hU, hm]

/-- **Off the message slots the potential sees nothing**: states agreeing off a cell `z` at no
message slot, with the same selections, have the same potential. -/
theorem encPotQ_eq_of_off (hno : ∀ l e, slotOf z ≠ some (.msg l e)) {s s' : RReg SelMem}
    (hU : ∀ x, x ≠ z → unionH s' x = unionH s x) (hm : s'.2.2.2 = s.2.2.2) :
    encPotQ s' = encPotQ s := by
  unfold encPotQ
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hc : msgCwCount (unionH s') k.1 k.2 = msgCwCount (unionH s) k.1 k.2 :=
    cellOutCount_congr (P := fun x ↦ slotOf x = some (.msg k.1 k.2)) _ fun x hx ↦
      hU x fun hxz ↦ hno k.1 k.2 (hxz ▸ hx)
  rw [hm, hc]

/-- The count off `z` does not see `z`. -/
theorem offCwQ_congr {s s' : RReg SelMem} (hU : ∀ x, x ≠ z → unionH s' x = unionH s x) :
    offCwQ z l e s' = offCwQ z l e s :=
  cellOutCount_congr _ fun x hx ↦ hU x hx.1

theorem unionH_congr_off {s s' : RReg SelMem} (h1 : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b)
    (h3 : s'.2.1 = s.2.1) (x : HashDomain) (hx : x ≠ z) : unionH s' x = unionH s x := by
  rw [unionH_apply, unionH_apply, h3, h1 x hx]

/-- The count off `z` is a weight off the cell `z`. -/
theorem offCwQ_offCell :
    OffCell z (fun s : RReg SelMem ↦ (offCwQ z l e s : ℝ)) := fun _ _ h1 _ h3 ↦
  congrArg Nat.cast (offCwQ_congr (unionH_congr_off h1 h3))

/-- The potential of the other keys does not see `z` nor the selection of `(l, e)`. -/
theorem encOtherQ_congr (hz : slotOf z = some (.msg l e)) {s s' : RReg SelMem}
    (hU : ∀ x, x ≠ z → unionH s' x = unionH s x)
    (hm : ∀ k : Layer × KeyIndex, k ≠ (l, e) → s'.2.2.2 k.1 k.2 = s.2.2.2 k.1 k.2) :
    encOtherQ (l, e) s' = encOtherQ (l, e) s := by
  unfold encOtherQ
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.ne_of_mem_erase hk
  have hc : msgCwCount (unionH s') k.1 k.2 = msgCwCount (unionH s) k.1 k.2 :=
    cellOutCount_congr (P := fun x ↦ slotOf x = some (.msg k.1 k.2)) _ fun x hx ↦
      hU x fun hxz ↦ by
        subst hxz
        obtain ⟨h1, h2⟩ := Slot.msg.inj (Option.some.inj (hx.symm.trans hz))
        exact hk' (Prod.ext h1 h2)
  rw [hm k hk', hc]

section readKraus

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

omit [Fintype M] in
/-- A nonzero entry of a read of `h` accepts the memory `r.2` and moves it to `upd r.2 r.1`. -/
theorem readKrausH_memQ (z : Z) (upd : M → Option X → M) (r : Option X × M)
    {s' s : HwReg X Z M} (h : readKrausH z upd r s' s ≠ 0) :
    s.2.2 = r.2 ∧ s'.2.2 = upd r.2 r.1 := by
  rw [readKrausH, clsKraus_apply] at h
  split_ifs at h with hc
  · exact ⟨hc.1, by rw [hc.2]⟩
  · exact absurd rfl h

end readKraus

/-- **A trial read keeps the potential of the other keys.** -/
theorem encOtherQ_keep (hz : slotOf z = some (.msg l e)) (r : Option HashOutput × QMem)
    (a a' : Unit × RReg SelMem)
    (h : hwReadKraus (.readH z (trialUpdQ l e z)) r a' a ≠ 0) :
    encOtherQ (l, e) a'.2 = encOtherQ (l, e) a.2 := by
  obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
  obtain ⟨h1, -, h3⟩ := readKrausH_ne_zero_rest z (trialUpdQ l e z) r h'
  obtain ⟨hm1, hm2⟩ := readKrausH_memQ z (trialUpdQ l e z) r h'
  refine encOtherQ_congr hz (unionH_congr_off h1 h3) fun k hk ↦ ?_
  rw [hm2, hm1]
  exact cwUpd_apply_of_ne z _ _ fun h ↦ hk (Prod.ext h.1 h.2)

/-! ## The other ports -/

/-- **A sponge call changes the potential by at most one** (one database cell). -/
theorem oneCellLipschitz_encPotQ :
    OneCellLipschitz (X := HashOutput) (Z := HashDomain) (M := QMem) encPotQ where
  h D b x v := by
    set s : RReg SelMem := (D, b)
    set s' : RReg SelMem := ((Function.update D.1 x v, D.2.1, D.2.2), b)
    have hU : ∀ y, y ≠ x → unionH s' y = unionH s y := fun y hy ↦ by
      rw [unionH_apply, unionH_apply]
      show (b.1.1 y).or (Function.update D.1 x v y) = (b.1.1 y).or (D.1 y)
      rw [Function.update_of_ne hy]
    by_cases hx : ∃ l e, slotOf x = some (.msg l e)
    · obtain ⟨l, e, hx⟩ := hx
      have h1 := encPotQ_split hx ((), s)
      have h2 := encPotQ_split hx ((), s')
      have hA : encOtherQ (l, e) s' = encOtherQ (l, e) s := encOtherQ_congr hx hU fun _ _ ↦ rfl
      have hn : offCwQ x l e s' = offCwQ x l e s := offCwQ_congr hU
      have hu : ind (unselS l e) ((), s') = ind (unselS l e) ((), s) := rfl
      have hc1 := ind_le_one (cellS x l e) ((), s')
      have hc0 := ind_nonneg (cellS x l e) ((), s)
      change encPotQ s' ≤ encPotQ s + 1
      rw [h1, h2, hA, hn, hu]
      linarith
    · simp only [not_exists] at hx
      exact (encPotQ_eq_of_off hx hU rfl).le.trans (le_add_of_nonneg_right zero_le_one)
  k D b x v := (encPotQ_congr (s := (D, b)) rfl rfl).le.trans
    (le_add_of_nonneg_right zero_le_one)
  k' D b x v := (encPotQ_congr (s := (D, b)) rfl rfl).le.trans
    (le_add_of_nonneg_right zero_le_one)

/-- **A program of a cell at no message slot keeps the potential.** -/
theorem encPotQ_progMap (hno : ∀ l e, slotOf z ≠ some (.msg l e)) (a : HashOutput)
    (s : RReg SelMem) : encPotQ (progMap (.programH z a) s) = encPotQ s := by
  refine encPotQ_eq_of_off hno (fun x hx ↦ ?_) rfl
  rw [unionH_apply, unionH_apply]
  show (Function.update s.2.1.1 z (some a) x).or (Function.update s.1.1 z none x) =
    (s.2.1.1 x).or (s.1.1 x)
  rw [Function.update_of_ne hx, Function.update_of_ne hx]

/-! ## The count off the read cell at a trial read -/

section offCell

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

omit [Fintype X] [DecidableEq X] [Fintype Z] [Fintype M] [DecidableEq M] in
/-- A state rebuilt from a rest agrees with the rest off the read cell, whatever the cell. -/
theorem splitH'_symm_offG (z : Z) (o o' : Option X) (r : RestH X M z) :
    (∀ b, b ≠ z → ((splitH' z).symm (o, r)).2.1.1 b = ((splitH' z).symm (o', r)).2.1.1 b) ∧
      ((splitH' z).symm (o, r)).2.1.2 = ((splitH' z).symm (o', r)).2.1.2 ∧
      ((splitH' z).symm (o, r)).2.2.1 = ((splitH' z).symm (o', r)).2.2.1 := by
  refine ⟨fun b hb ↦ ?_, rfl, rfl⟩
  simp [splitH', hb]

omit [Fintype X] [DecidableEq X] [Fintype Z] [Fintype M] [DecidableEq M] in
theorem splitH'_symm_cellG (z : Z) (o : Option X) (r : RestH X M z) :
    ((splitH' z).symm (o, r)).2.1.1 z = o := by
  simp [splitH']

/-- No decompressed `⊥` survives a diagonal weight off the read cell. -/
theorem cellNoBot_sqrtDiagG {z : Z} {n : HwReg X Z M → ℝ} (hn : OffCell z n)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    CellNoBot (splitH' z) (actH z) (sqrtDiag n * σ * sqrtDiag n) := by
  intro r hr t
  have hc : ∀ y : X, n ((splitH' z).symm (some y, r)).2 = n ((splitH' z).symm (none, r)).2 :=
    fun y ↦ by
      obtain ⟨h1, h2, h3⟩ := splitH'_symm_offG z (some y) none r
      exact hn _ _ h1 h2 h3
  simp only [sqrtDiag, mul_diagonal, diagonal_mul]
  rw [Finset.sum_congr rfl fun y _ ↦ by rw [hc y], ← Finset.sum_mul, ← Finset.mul_sum,
    hnb r hr t, mul_zero, zero_mul]

/-- The read of `N σ N` against `f` is the read of `σ` against `f · n`, `N = sqrtDiag n`. -/
theorem dW_conj_sqrtDiagG (z : Z) (upd : M → Option X → M) {n : HwReg X Z M → ℝ}
    (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n) (f : Unit × HwReg X Z M → ℝ) (r : Option X × M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    dW f (MatrixMap.conj (hwReadKraus (.readH z upd) r) (sqrtDiag n * σ * sqrtDiag n)) =
      dW (fun q ↦ f q * n q.2) (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ) := by
  set N := sqrtDiag n
  set K := hwReadKraus (.readH z upd) r
  have hc : N * K = K * N := sqrtDiag_mul_readH z upd hn r
  have hc' : N * Kᴴ = Kᴴ * N := by
    have := congrArg conjTranspose hc
    simp only [conjTranspose_mul, N, sqrtDiag_conjTranspose] at this
    exact this.symm
  have heq : K * (N * σ * N) * Kᴴ = N * (K * σ * Kᴴ) * N := by
    calc K * (N * σ * N) * Kᴴ = (K * N) * σ * (N * Kᴴ) := by simp only [Matrix.mul_assoc]
      _ = (N * K) * σ * (Kᴴ * N) := by rw [hc, hc']
      _ = N * (K * σ * Kᴴ) * N := by simp only [Matrix.mul_assoc]
  rw [MatrixMap.conj_apply, MatrixMap.conj_apply, heq]
  unfold dW
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [re_sqrtDiag_conj_apply hn0]
  exact (mul_assoc _ _ _).symm

theorem posSemidef_sqrtDiag_conjG (n : HwReg X Z M → ℝ)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    (sqrtDiag n * σ * sqrtDiag n).PosSemidef := by
  have := hσ.mul_mul_conjTranspose_same (sqrtDiag n)
  rwa [sqrtDiag_conjTranspose] at this

end offCell

/-- **The flip values of the unselected-key event** at a rest: the key unselected and the digest
a codeword. -/
def CwFlipQ (l : Layer) (e : KeyIndex) (z : HashDomain) (y : HashOutput)
    (r : RestH HashOutput QMem z) : Prop :=
  (memH z r).2 l e = none ∧ Codeword.Valid (truncateHash y)

noncomputable instance instDecidableCwFlipQ (l : Layer) (e : KeyIndex) (z : HashDomain)
    (y : HashOutput) (r : RestH HashOutput QMem z) : Decidable (CwFlipQ l e z y r) :=
  Classical.propDecidable _

/-- The states a trial read selects from: the cell empty, the key unselected. -/
def EmptyUnselQ (z : HashDomain) (l : Layer) (e : KeyIndex) (s : RReg SelMem) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z = none ∧ s.2.2.2 l e = none

noncomputable instance instDecidablePredEmptyUnselQ (z : HashDomain) (l : Layer)
    (e : KeyIndex) : DecidablePred (EmptyUnselQ z l e) :=
  Classical.decPred _

/-- The states whose read cell is recorded with a codeword output, the key unselected. -/
def CwRecQ (z : HashDomain) (l : Layer) (e : KeyIndex) (s : RReg SelMem) : Prop :=
  s.2.1.1 z = none ∧ s.2.2.2 l e = none ∧
    ∃ v, s.1.1 z = some v ∧ Codeword.Valid (truncateHash v)

noncomputable instance instDecidablePredCwRecQ (z : HashDomain) (l : Layer) (e : KeyIndex) :
    DecidablePred (CwRecQ z l e) :=
  Classical.decPred _

theorem ind_unselS_symm (a : Option HashOutput) (r : RestH HashOutput QMem z) :
    ind (unselS l e) ((splitH' z).symm (a, r)) = if (memH z r).2 l e = none then 1 else 0 :=
  rfl

/-- The weight of a recorded outcome against the unselected-key event. -/
theorem gw_unselS (y : HashOutput) (r : RestH HashOutput QMem z) :
    gw (splitH' z) (tauH z (trialUpdQ l e z)) (unselS l e) (some y) r =
      if (trialUpdQ l e z (memH z r) (some y)).2 l e = none then 1 else 0 := by
  unfold gw
  have h : ∀ a : Option HashOutput, ind (unselS l e)
      ((splitH' z).symm (a, tauH z (trialUpdQ l e z) (some y) r)) =
      if (trialUpdQ l e z (memH z r) (some y)).2 l e = none then 1 else 0 := fun a ↦ rfl
  simp only [h]
  rw [← Finset.sum_mul, sum_cr_sq, one_mul]

/-- **The diagonal cost of the unselected-key event**: `-ρ_c` on an empty, not hardwired cell
with the key unselected, at most `0` elsewhere. -/
theorem fd_unselS_le (q : Unit × RReg SelMem) :
    fd (splitH' z) (actH z) (tauH z (trialUpdQ l e z)) (unselS l e) (phiH z (trialUpdQ l e z)) q ≤
      -(Quantum.Xmss.rhoCw * if EmptyUnselQ z l e q.2 then 1 else 0) := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  unfold fd
  by_cases ha : actH z (splitH' z q).2
  · have ha' : q.2.2.1.1 z = none := ha
    rw [ite_eq_left ha, ind_unselS]
    rcases hc : (splitH' z q).1 with _ | y
    · have hc' : q.2.1.1 z = none := hc
      show (∑ y, gw (splitH' z) (tauH z (trialUpdQ l e z)) (unselS l e) (some y)
          (splitH' z q).2) / Fintype.card HashOutput - _ ≤ _
      simp only [gw_unselS, hmem]
      by_cases hm : q.2.2.2.2 l e = none
      · have hsum : (∑ y : HashOutput, if (trialUpdQ l e z q.2.2.2 (some y)).2 l e = none then
            (1 : ℝ) else 0) = Fintype.card HashOutput -
              ((Finset.univ.filter fun v : HashOutput ↦
                Codeword.Valid (truncateHash v)).card : ℝ) := by
          rw [Finset.sum_congr rfl fun y _ ↦ if_congr (trialUpdQ_unsel_iff hm y) rfl rfl,
            Finset.sum_boole, Finset.filter_not, Finset.card_sdiff_of_subset
              (Finset.subset_univ _), Finset.card_univ, Nat.cast_sub (Finset.card_le_univ _)]
        have hN : (0 : ℝ) < Fintype.card HashOutput := Nat.cast_pos.2 Fintype.card_pos
        have hE : EmptyUnselQ z l e q.2 := ⟨ha', hc', hm⟩
        rw [hsum, sub_div, div_self hN.ne', card_codeword_div_card_hashOutput, ite_eq_left hm,
          ite_eq_left hE]
        linarith
      · have h0 : ∀ y : HashOutput, (trialUpdQ l e z q.2.2.2 (some y)).2 l e ≠ none :=
          fun y ↦ trialUpdQ_keep hm _
        have hR : (if EmptyUnselQ z l e q.2 then (1 : ℝ) else 0) = 0 :=
          ite_eq_right fun h ↦ hm h.2.2
        rw [hR, mul_zero, neg_zero, ite_eq_right hm]
        simp only [h0, ↓reduceIte, Finset.sum_const_zero, zero_div, sub_zero, le_refl]
    · have hc' : q.2.1.1 z ≠ none := by
        rw [← splitH'_apply_fst, hc]; exact Option.some_ne_none y
      show gw (splitH' z) (tauH z (trialUpdQ l e z)) (unselS l e) (some y) (splitH' z q).2 - _ ≤ _
      have hR : (if EmptyUnselQ z l e q.2 then (1 : ℝ) else 0) = 0 :=
        ite_eq_right fun h ↦ hc' h.2.1
      rw [hR, mul_zero, neg_zero, gw_unselS, hmem]
      by_cases hm : q.2.2.2.2 l e = none
      · rw [ite_eq_left hm]
        split_ifs <;> norm_num
      · rw [ite_eq_right hm, ite_eq_right (trialUpdQ_keep hm _), sub_zero]
  · have ha' : q.2.2.1.1 z ≠ none := ha
    have hR : (if EmptyUnselQ z l e q.2 then (1 : ℝ) else 0) = 0 :=
      ite_eq_right fun h ↦ ha' h.1
    rw [ite_eq_right ha, ind_unselS, ind_unselS, hR, mul_zero, neg_zero]
    show (if (trialUpdQ l e z q.2.2.2 (q.2.2.1.1 z)).2 l e = none then (1 : ℝ) else 0) - _ ≤ 0
    by_cases hm : q.2.2.2.2 l e = none
    · rw [ite_eq_left hm]
      split_ifs <;> norm_num
    · rw [ite_eq_right hm, ite_eq_right (trialUpdQ_keep hm _), sub_zero]

/-- **The empty-to-recorded weight of the unselected-key event** with the reference `q0`: `ρ_c`
on an empty, not hardwired cell with the key unselected, `0` elsewhere. -/
theorem ew_unselS_le (q : Unit × RReg SelMem) :
    ew (splitH' z) (actH z) (tauH z (trialUpdQ l e z)) (unselS l e)
        (q0 (splitH' z) (unselS l e)) q ≤
      Quantum.Xmss.rhoCw * if EmptyUnselQ z l e q.2 then 1 else 0 := by
  have hmem : memH z (splitH' z q).2 = q.2.2.2 := rfl
  have hρ : 0 ≤ Quantum.Xmss.rhoCw :=
    le_trans (by positivity) Quantum.Xmss.inv_two_pow_21_le_rhoCw
  unfold ew
  split_ifs with h1 h2 h2
  · have hN : (0 : ℝ) < Fintype.card HashOutput := Nat.cast_pos.2 Fintype.card_pos
    have hq0 : q0 (splitH' z) (unselS l e) (splitH' z q).2 = 1 := by
      unfold q0
      rw [ind_unselS_symm, hmem, ite_eq_left h2.2.2]
    have hterm : ∀ y : HashOutput, xv (splitH' z) (tauH z (trialUpdQ l e z)) (unselS l e)
        (q0 (splitH' z) (unselS l e)) (some y) (splitH' z q).2 ^ 2 =
        (if Codeword.Valid (truncateHash y) then 1 else 0) / Fintype.card HashOutput :=
      fun y ↦ by
        have hsq : ((if ¬ Codeword.Valid (truncateHash y) then (1 : ℝ) else 0) - 1) ^ 2 =
            if Codeword.Valid (truncateHash y) then 1 else 0 := by
          split_ifs <;> norm_num
        show ((gw (splitH' z) (tauH z (trialUpdQ l e z)) (unselS l e) (some y)
          (splitH' z q).2 - q0 (splitH' z) (unselS l e) (splitH' z q).2) /
            Real.sqrt (Fintype.card HashOutput)) ^ 2 = _
        rw [hq0, gw_unselS, hmem, if_congr (trialUpdQ_unsel_iff h2.2.2 y) rfl rfl, div_pow,
          Real.sq_sqrt hN.le, hsq]
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, ← Finset.sum_div, Finset.sum_boole,
      card_codeword_div_card_hashOutput, mul_one]
  · have hm : q.2.2.2.2 l e ≠ none := fun hm ↦
      h2 (And.intro h1.1 (And.intro h1.2 hm) : EmptyUnselQ z l e q.2)
    have hq0 : q0 (splitH' z) (unselS l e) (splitH' z q).2 = 0 := by
      unfold q0
      rw [ind_unselS_symm, hmem, ite_eq_right hm]
    have hterm : ∀ y : HashOutput, xv (splitH' z) (tauH z (trialUpdQ l e z)) (unselS l e)
        (q0 (splitH' z) (unselS l e)) (some y) (splitH' z q).2 ^ 2 = 0 := fun y ↦ by
      show ((gw (splitH' z) (tauH z (trialUpdQ l e z)) (unselS l e) (some y)
        (splitH' z q).2 - q0 (splitH' z) (unselS l e) (splitH' z q).2) /
          Real.sqrt (Fintype.card HashOutput)) ^ 2 = _
      rw [hq0, gw_unselS, hmem, ite_eq_right (trialUpdQ_keep hm (some y)), sub_self, zero_div]
      exact zero_pow two_ne_zero
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, Finset.sum_const_zero, mul_zero]
  · exact absurd ⟨h2.1, h2.2.1⟩ h1
  · rw [mul_zero]

/-- The cross term's support: the recorded cells of the flip values are codeword-recorded for
the unselected key. -/
theorem pd_cwFlipQ_le (q : Unit × RReg SelMem) :
    pd (splitH' z) (actH z) (CwFlipQ l e z) q ≤ if CwRecQ z l e q.2 then 1 else 0 := by
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
        exact h2 (And.intro h1 (And.intro h3.1 ⟨y, hc', h3.2⟩) : CwRecQ z l e q.2)
      · exact le_rfl
  · norm_num
  · exact le_rfl

/-- Off the flip values a recorded outcome weighs the reference weight `q0`. -/
theorem gw_eq_q0_of_not_cwFlipQ (r : RestH HashOutput QMem z) (y : HashOutput)
    (hy : ¬ CwFlipQ l e z y r) :
    gw (splitH' z) (tauH z (trialUpdQ l e z)) (unselS l e) (some y) r =
      q0 (splitH' z) (unselS l e) r := by
  unfold q0
  rw [gw_unselS, ind_unselS_symm]
  by_cases hm : (memH z r).2 l e = none
  · rw [ite_eq_left hm, ite_eq_left ((trialUpdQ_unsel_iff hm y).2 fun hv ↦ hy ⟨hm, hv⟩)]
  · rw [ite_eq_right hm, ite_eq_right (trialUpdQ_keep hm _)]

/-- The unselected `n`-weighted mass is the event weight of `N σ N`. -/
theorem re_trace_indProj_sqrtDiagQ {n : RReg SelMem → ℝ} (hn0 : ∀ s, 0 ≤ n s)
    (σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ) :
    (indProj (unselS l e) * (sqrtDiag n * σ * sqrtDiag n)).trace.re =
      dW (fun q ↦ ind (unselS l e) q * n q.2) σ := by
  rw [indProj, re_trace_diagonal_mul]
  unfold dW
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [re_sqrtDiag_conj_apply hn0]
  exact (mul_assoc _ _ _).symm

/-- The unselected `n`-weighted mass after a trial read: the mass before plus the flip of the
unselected-key event on `N σ N`. -/
theorem unsel_post_eqQ {n : RReg SelMem → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    (σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ) :
    ∑ r : Option HashOutput × QMem, dW (fun q ↦ ind (unselS l e) q * n q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ) =
      dW (fun q ↦ ind (unselS l e) q * n q.2) σ +
        (flipOp (fun r : Option HashOutput × QMem ↦ hwReadKraus (.readH z (trialUpdQ l e z)) r)
          (unselS l e) * (sqrtDiag n * σ * sqrtDiag n)).trace.re := by
  have h1 : ∀ r, dW (fun q ↦ ind (unselS l e) q * n q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ) =
      dW (fun q ↦ ind (unselS l e) q)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r)
          (sqrtDiag n * σ * sqrtDiag n)) :=
    fun r ↦ (dW_conj_sqrtDiagG z (trialUpdQ l e z) hn0 hn (fun q ↦ ind (unselS l e) q) r σ).symm
  have hsumeq : (∑ r : Option HashOutput × QMem,
      (hwReadKraus (.readH z (trialUpdQ l e z)) r)ᴴ *
        diagonal (fun q ↦ ((ind (unselS l e) q : ℝ) : ℂ)) *
          hwReadKraus (.readH z (trialUpdQ l e z)) r) =
      flipOp (fun r : Option HashOutput × QMem ↦ hwReadKraus (.readH z (trialUpdQ l e z)) r)
        (unselS l e) + indProj (unselS l e) := by
    rw [flipOp, sub_add_cancel]
    rfl
  rw [Finset.sum_congr rfl fun r _ ↦ h1 r, sum_dW_conj, hsumeq, Matrix.add_mul,
    Matrix.trace_add, Complex.add_re, add_comm, re_trace_indProj_sqrtDiagQ hn0 σ]

/-- **The flip of the unselected-key event at a trial read, `n`-weighted**: at most
`-ρ_c e + 2 √(ρ_c e p)`, `e` the `n`-weighted `EmptyUnselQ` mass and `p` the `n`-weighted `CwRecQ`
mass. -/
theorem unselFlipQ_le {n : RReg SelMem → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option HashOutput × QMem ↦ hwReadKraus (.readH z (trialUpdQ l e z)) r)
        (unselS l e) * (sqrtDiag n * σ * sqrtDiag n)).trace.re ≤
      -(Quantum.Xmss.rhoCw *
          ∑ q, (if EmptyUnselQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re)) +
        2 * √(Quantum.Xmss.rhoCw *
          (∑ q, (if EmptyUnselQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re)) *
            ∑ q, (if CwRecQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re)) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hτ : (sqrtDiag n * σ * sqrtDiag n).PosSemidef := posSemidef_sqrtDiag_conjG n hσ
  have hdiag : ∀ q, ((sqrtDiag n * σ * sqrtDiag n) q q).re = n q.2 * (σ q q).re :=
    re_sqrtDiag_conj_apply hn0 σ
  have hnσ : ∀ q, 0 ≤ n q.2 * (σ q q).re := fun q ↦ mul_nonneg (hn0 _) (hre q)
  have hF := re_trace_flipOp_le (unselS l e) (cellRead_readH z (trialUpdQ l e z))
    (clsOff_readH z (trialUpdQ l e z)) (q0 (splitH' z) (unselS l e)) (CwFlipQ l e z)
    (fun r _ y hy ↦ gw_eq_q0_of_not_cwFlipQ r y hy) hτ (cellNoBot_sqrtDiagG hn hnb)
  have he : 0 ≤ ∑ q, (if EmptyUnselQ z l e q.2 then (1 : ℝ) else 0) * (n q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hnσ q)
  have hρ : 0 ≤ Quantum.Xmss.rhoCw :=
    le_trans (by positivity) Quantum.Xmss.inv_two_pow_21_le_rhoCw
  have hfd : ∑ s, fd (splitH' z) (actH z) (tauH z (trialUpdQ l e z)) (unselS l e)
      (phiH z (trialUpdQ l e z)) s * ((sqrtDiag n * σ * sqrtDiag n) s s).re ≤
      -(Quantum.Xmss.rhoCw *
        ∑ q, (if EmptyUnselQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (fd_unselS_le q) (hnσ q)).trans_eq (by ring)
  have hew : ∑ s, ew (splitH' z) (actH z) (tauH z (trialUpdQ l e z)) (unselS l e)
      (q0 (splitH' z) (unselS l e)) s * ((sqrtDiag n * σ * sqrtDiag n) s s).re ≤
      Quantum.Xmss.rhoCw *
        ∑ q, (if EmptyUnselQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [hdiag]
    exact (mul_le_mul_of_nonneg_right (ew_unselS_le q) (hnσ q)).trans_eq (by ring)
  have hpd : ∑ s, pd (splitH' z) (actH z) (CwFlipQ l e z) s *
      ((sqrtDiag n * σ * sqrtDiag n) s s).re ≤
      ∑ q, (if CwRecQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re) :=
    Finset.sum_le_sum fun q _ ↦ by
      rw [hdiag]
      exact mul_le_mul_of_nonneg_right (pd_cwFlipQ_le q) (hnσ q)
  have hP0 : 0 ≤ ∑ s, pd (splitH' z) (actH z) (CwFlipQ l e z) s *
      ((sqrtDiag n * σ * sqrtDiag n) s s).re :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by
      rcases pd_mem (e := splitH' z) (act := actH z) (CwFlipQ l e z) q with h | h <;>
        simp only [h, le_refl, zero_le_one]) (by rw [hdiag]; exact hnσ q)
  refine hF.trans (add_le_add hfd (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
  rw [← Real.sqrt_mul' _ hP0]
  exact Real.sqrt_le_sqrt (mul_le_mul hew hpd hP0 (mul_nonneg hρ he))

/-- **The unselected count off the read cell at a trial read**: `2^-22 e` plus the
`n`-weighted unselected mass after the read is at most the one before plus `3 p`. -/
theorem unselRead_dropQ {n : RReg SelMem → ℝ} (hn0 : ∀ s, 0 ≤ n s) (hn : OffCell z n)
    {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 22 : ℝ)⁻¹ * (∑ q, (if EmptyUnselQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re)) +
      ∑ r : Option HashOutput × QMem, dW (fun q ↦ ind (unselS l e) q * n q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ) ≤
    dW (fun q ↦ ind (unselS l e) q * n q.2) σ +
      3 * ∑ q, (if CwRecQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hnσ : ∀ q, 0 ≤ n q.2 * (σ q q).re := fun q ↦ mul_nonneg (hn0 _) (hre q)
  refine drop_of_survive (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num)
    (hnσ q)) (Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hnσ q))
    Quantum.Xmss.inv_two_pow_21_le_rhoCw ?_
  rw [unsel_post_eqQ hn0 hn σ]
  have h := unselFlipQ_le (l := l) (e := e) hn0 hn hσ hnb
  have hp : 0 ≤ ∑ q, (if CwRecQ z l e q.2 then (1 : ℝ) else 0) * (n q.2 * (σ q q).re) :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hnσ q)
  linarith

/-! ## The read cell at a trial read -/

/-- The outcome states of a trial read are outside `cellS`: a codeword output selects the key. -/
theorem not_mem_cellS_out {r : RestH HashOutput QMem z} (hr : actH z r) (y : HashOutput) :
    (splitH' z).symm (some y, tauH z (trialUpdQ l e z) (some y) r) ∉ cellS z l e := by
  rintro ⟨hu, y', hy', hcw⟩
  have hw : ((splitH' z).symm (some y, tauH z (trialUpdQ l e z) (some y) r)).2.2.1.1 z = none :=
    hr
  rw [unionH_apply, hw, splitH'_symm_cellG] at hy'
  obtain rfl := Option.some.inj hy'
  have hu' : (trialUpdQ l e z (memH z r) (some y)).2 l e = none := hu
  by_cases hm : (memH z r).2 l e = none
  · exact (trialUpdQ_unsel_iff hm y).1 hu' hcw
  · exact trialUpdQ_keep hm _ hu'

/-- The classical move of a hardwired cell leaves `cellS`. -/
theorem not_mem_cellS_phiH (q : Unit × RReg SelMem) (hq : q.2.2.1.1 z ≠ none) :
    phiH z (trialUpdQ l e z) q ∉ cellS z l e := by
  rintro ⟨hu, y', hy', hcw⟩
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hq
  have hy2 : (q.2.2.1.1 z).or (q.2.1.1 z) = some y' := hy'
  rw [hw] at hy2
  obtain rfl := Option.some.inj hy2
  have hu' : (trialUpdQ l e z q.2.2.2 (some w)).2 l e = none := by
    have h := hu
    change (trialUpdQ l e z q.2.2.2 (q.2.2.1.1 z)).2 l e = none at h
    rwa [hw] at h
  by_cases hm : q.2.2.2.2 l e = none
  · exact (trialUpdQ_unsel_iff hm w).1 hu' hcw
  · exact trialUpdQ_keep hm _ hu'

/-- **The read cell after a trial read**: the flip into `cellS` is at most `2/|Y| + 4/|Y|²` per
unit of trace plus the recorded mass of the unselected key at the cell. -/
theorem cellFlip_le {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ}
    (hσ : σ.PosSemidef) (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (flipOp (fun r : Option HashOutput × QMem ↦ hwReadKraus (.readH z (trialUpdQ l e z)) r)
        (cellS z l e) * σ).trace.re ≤
      ∑ q, ((2 / (Fintype.card HashOutput : ℝ) + (2 / (Fintype.card HashOutput : ℝ)) ^ 2) +
        (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 l e = none then 1 else 0)) *
          (σ q q).re := by
  classical
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set DU : HashOutput → RestH HashOutput QMem z → Prop := fun _ r ↦ (memH z r).2 l e = none
  have hD : ∀ r, actH z r → ∀ y, ¬ DU y r →
      gw (splitH' z) (tauH z (trialUpdQ l e z)) (cellS z l e) (some y) r = 0 := by
    intro r _ y hy
    unfold gw
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [ind_eq_zero_of_not_mem (cellS z l e) fun h ↦ trialUpdQ_keep hy (some y) h.1, mul_zero]
  have hF := re_trace_flipOp_le (cellS z l e) (cellRead_readH z (trialUpdQ l e z))
    (clsOff_readH z (trialUpdQ l e z)) (fun _ ↦ 0) DU hD hσ hnb
  set N : ℝ := (Fintype.card HashOutput : ℝ)
  set E := ∑ s, ew (splitH' z) (actH z) (tauH z (trialUpdQ l e z)) (cellS z l e)
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
  have hgw : ∀ s : Unit × RReg SelMem, actH z (splitH' z s).2 → ∀ y,
      gw (splitH' z) (tauH z (trialUpdQ l e z)) (cellS z l e) (some y) (splitH' z s).2 ≤ 2 / N :=
    fun s ha y ↦ gw_some_le_two_div (cellS z l e)
      (ind_eq_zero_of_not_mem (cellS z l e) (not_mem_cellS_out ha y))
  have hpt : ∀ s, fd (splitH' z) (actH z) (tauH z (trialUpdQ l e z)) (cellS z l e)
      (phiH z (trialUpdQ l e z)) s + ew (splitH' z) (actH z) (tauH z (trialUpdQ l e z))
        (cellS z l e) (fun _ ↦ 0) s ≤ 2 / N + (2 / N) ^ 2 := fun s ↦ by
    refine add_le_add ?_ ?_
    · unfold fd
      split_ifs with ha
      · exact (sub_le_self _ (ind_nonneg _ s)).trans (gdiag_le_of _ (hgw s ha) _)
      · rw [ind_eq_zero_of_not_mem (cellS z l e) (not_mem_cellS_phiH s ha), zero_sub]
        exact (neg_nonpos.2 (ind_nonneg _ s)).trans (by positivity)
    · by_cases ha : actH z (splitH' z s).2
      · exact ew_zero_le_of _ (hgw s ha)
      · unfold ew
        rw [ite_eq_right fun h' ↦ ha h'.1]
        positivity
  have hpd : ∀ s : Unit × RReg SelMem, pd (splitH' z) (actH z) DU s ≤
      if s.2.2.1.1 z = none ∧ s.2.1.1 z ≠ none ∧ s.2.2.2.2 l e = none then 1 else 0 := by
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
  calc _ ≤ ∑ s, fd (splitH' z) (actH z) (tauH z (trialUpdQ l e z)) (cellS z l e)
        (phiH z (trialUpdQ l e z)) s * (σ s s).re + (E + p) :=
        hF.trans (add_le_add le_rfl hsq)
    _ = ∑ s, (fd (splitH' z) (actH z) (tauH z (trialUpdQ l e z)) (cellS z l e)
          (phiH z (trialUpdQ l e z)) s + ew (splitH' z) (actH z) (tauH z (trialUpdQ l e z))
            (cellS z l e) (fun _ ↦ 0) s + pd (splitH' z) (actH z) DU s) * (σ s s).re := by
        simp only [E, p, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right
        (add_le_add (hpt s) (hpd s)) (hre s)

/-! ## A trial read -/

/-- **The database count of the codeword cells off `z`** at a recorded read cell of a
`MsgFree` register: one less than the recorded cells, at most. -/
theorem offCwQ_add_one_le {s : RReg SelMem} (hM : MsgFree s)
    (hD : s.1.1 z ≠ none) : offCwQ z l e s + 1 ≤ s.1.1.size := by
  have h1 : offCwQ z l e s ≤ (Finset.univ.filter fun x ↦ x ≠ z ∧ (s.1.1 x).isSome).card := by
    refine cellOutCount_le_card _ fun x y hx hy ↦ ⟨hx.1, ?_⟩
    have hw : s.2.1.1 x = none := hw_none_of_msgFree hM hx.2
    rw [unionH_apply, hw] at hy
    change s.1.1 x = some y at hy
    rw [hy]
    rfl
  have h2 := card_filter_eq_off_add (fun x ↦ (s.1.1 x).isSome) z
  rw [ite_eq_left (Option.ne_none_iff_isSome.mp hD)] at h2
  have h3 : s.1.1.size = (Finset.univ.filter fun x ↦ (s.1.1 x).isSome).card := rfl
  omega

open scoped Classical in
/-- **A trial read on the potential, in `ℝ`**: on states supported on `MsgFree` registers of
database grade at most `G`, with no decompressed `⊥` at the cell, `2^-22 encWt` plus the potential
after the read is at most the potential before plus `4 G recUWt + 2^-250 tr σ`. -/
theorem trialRead_drop (hz : slotOf z = some (.msg l e)) {G : ℕ}
    {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ)
    (hinv : ∀ q, σ q q ≠ 0 → MsgFree q.2 ∧ dbGrade q.2.1 ≤ G) :
    (2 ^ 22 : ℝ)⁻¹ * (∑ q, encWt z l e q.2 * (σ q q).re) +
        ∑ r : Option HashOutput × QMem, dW (fun q ↦ encPotQ q.2)
          (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ) ≤
      dW (fun q ↦ encPotQ q.2) σ + 4 * G * (∑ q, recUWt z l e q.2 * (σ q q).re) +
        (2 ^ 250 : ℝ)⁻¹ * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set n : RReg SelMem → ℝ := fun s ↦ (offCwQ z l e s : ℝ)
  have hn0 : ∀ s, 0 ≤ n s := fun s ↦ Nat.cast_nonneg _
  have hsplit : (fun q : Unit × RReg SelMem ↦ encPotQ q.2) = fun q ↦
      (fun q ↦ encOtherQ (l, e) q.2 + ind (unselS l e) q * n q.2) q + ind (cellS z l e) q :=
    funext fun q ↦ encPotQ_split hz q
  have hdW : ∀ τ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ,
      dW (fun q ↦ encPotQ q.2) τ = dW (fun q ↦ encOtherQ (l, e) q.2) τ +
        dW (fun q ↦ ind (unselS l e) q * n q.2) τ + dW (ind (cellS z l e)) τ := fun τ ↦ by
    rw [hsplit, dW_add, dW_add]
  simp only [hdW, Finset.sum_add_distrib]
  -- The other keys keep their part.
  have hA : ∑ r : Option HashOutput × QMem, dW (fun q ↦ encOtherQ (l, e) q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ) =
      dW (fun q ↦ encOtherQ (l, e) q.2) σ :=
    sum_dW_conj_of_keep (fun r : Option HashOutput × QMem ↦
      hwReadKraus (.readH z (trialUpdQ l e z)) r) _ (encOtherQ_keep hz)
      (sum_readKrausH z (trialUpdQ l e z)) σ
  -- The count off the cell.
  have hB := unselRead_dropQ (l := l) (e := e) hn0 offCwQ_offCell hσ hnb
  -- The cell itself.
  have hCeq : ∑ r : Option HashOutput × QMem, dW (ind (cellS z l e))
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ) =
      dW (ind (cellS z l e)) σ + (flipOp (fun r : Option HashOutput × QMem ↦
        hwReadKraus (.readH z (trialUpdQ l e z)) r) (cellS z l e) * σ).trace.re := by
    rw [sum_dW_conj, dW_eq_trace, flipOp, indProj, Matrix.sub_mul, Matrix.trace_sub,
      Complex.sub_re]
    ring
  have hC := cellFlip_le (l := l) (e := e) hσ hnb
  -- The Enc weight is the weight of the empty reads.
  have hEnc : ∑ q, encWt z l e q.2 * (σ q q).re =
      ∑ q, (if EmptyUnselQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re) := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp [h0]
    have hW : q.2.2.1.1 z = none := hw_none_of_msgFree (hinv q h0).1 hz
    unfold encWt
    by_cases hE : q.2.1.1 z = none ∧ q.2.2.2.2 l e = none
    · have hc : ¬ CellCwQ z q.2 := by
        rintro ⟨y, hy, -⟩
        rw [unionH_apply, hW, hE.1] at hy
        cases hy
      rw [ite_eq_left hE, ite_eq_left (show EmptyUnselQ z l e q.2 from ⟨hW, hE⟩),
        msgCwCount_eq_off_add hz, ite_eq_right hc, add_zero, one_mul]
    · rw [ite_eq_right hE, ite_eq_right fun h ↦ hE ⟨h.2.1, h.2.2⟩]
      ring
  -- The recorded charges.
  have hRec : 3 * (∑ q, (if CwRecQ z l e q.2 then 1 else 0) * (n q.2 * (σ q q).re)) +
      ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 l e = none then 1 else 0) *
        (σ q q).re ≤ 4 * G * (∑ q, recUWt z l e q.2 * (σ q q).re) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · simp [h0]
    obtain ⟨hM, hG⟩ := hinv q h0
    by_cases hR : q.2.1.1 z ≠ none ∧ q.2.2.2.2 l e = none
    · have hU : recUWt z l e q.2 = 1 := ite_eq_left hR
      have hsz := offCwQ_add_one_le (l := l) (e := e) hM hR.1
      have hgr : Database.size q.2.1.1 ≤ G := (le_max_left _ _).trans hG
      have hnG : n q.2 + 1 ≤ G := by
        show (offCwQ z l e q.2 : ℝ) + 1 ≤ G
        exact_mod_cast hsz.trans hgr
      have h1 : (if CwRecQ z l e q.2 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have h2 : (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 l e = none then (1 : ℝ)
          else 0) ≤ 1 := by split_ifs <;> norm_num
      rw [hU]
      have hn := hn0 q.2
      have hq := hre q
      have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
      have h3 : 3 * ((if CwRecQ z l e q.2 then (1 : ℝ) else 0) * (n q.2 * (σ q q).re)) ≤
          3 * (n q.2 * (σ q q).re) := by
        have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hn hq)
        linarith
      have h4 := mul_le_mul_of_nonneg_right h2 hq
      have h5 : (3 * n q.2 + 1) * (σ q q).re ≤ 4 * G * (σ q q).re :=
        mul_le_mul_of_nonneg_right (by linarith) hq
      linarith
    · have hc : ¬ CwRecQ z l e q.2 := fun h ↦ hR ⟨by
        obtain ⟨v, hv, -⟩ := h.2.2
        rw [hv]
        exact Option.some_ne_none v, h.2.1⟩
      rw [ite_eq_right hc, ite_eq_right fun h ↦ hR ⟨h.2.1, h.2.2⟩]
      have hU0 : 0 ≤ recUWt z l e q.2 := by
        unfold recUWt
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
        (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 l e = none then 1 else 0)) *
          (σ q q).re = (2 / (Fintype.card HashOutput : ℝ) +
            (2 / (Fintype.card HashOutput : ℝ)) ^ 2) * σ.trace.re +
        ∑ q, (if q.2.2.1.1 z = none ∧ q.2.1.1 z ≠ none ∧ q.2.2.2.2 l e = none then 1 else 0) *
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
theorem trialRead_potential_le (hz : slotOf z = some (.msg l e)) {G : ℕ}
    {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ)
    (hinv : ∀ q, σ q q ≠ 0 → MsgFree q.2 ∧ dbGrade q.2.1 ≤ G) :
    (2 ^ 22 : ℝ≥0∞)⁻¹ * trialW encWt (trialRead z l e) σ +
        ∑' r, potential (diagPot fun s ↦ √(encPotQ s))
          (MatrixMap.conj (hwReadKraus (trialRead z l e) r) σ) ≤
      potential (diagPot fun s ↦ √(encPotQ s)) σ +
        (4 * (G : ℝ≥0∞) * trialW recUWt (trialRead z l e) σ +
          (2 ^ 250 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hpot : ∀ τ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ,
      potential (diagPot fun s ↦ √(encPotQ s)) τ =
        ENNReal.ofReal (dW (fun q ↦ encPotQ q.2) τ) :=
    fun τ ↦ potential_diagPot_sqrt encPotQ_nonneg τ
  have hpost : ∀ r, 0 ≤ dW (fun q : Unit × RReg SelMem ↦ encPotQ q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ) := fun r ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPotQ_nonneg q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  have hE0 : 0 ≤ ∑ q, encWt z l e q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
    mul_nonneg (by unfold encWt; split_ifs <;> positivity) (hre q)
  have hU0 : 0 ≤ ∑ q, recUWt z l e q.2 * (σ q q).re := Finset.sum_nonneg fun q _ ↦
    mul_nonneg (by unfold recUWt; split_ifs <;> norm_num) (hre q)
  have hP0 : 0 ≤ dW (fun q : Unit × RReg SelMem ↦ encPotQ q.2) σ :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPotQ_nonneg q.2) (hre q)
  have htr0 : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have key := trialRead_drop hz hσ hnb hinv
  rw [trialW_trialRead _ hz, trialW_trialRead _ hz, hpot, trialRead_eq]
  simp only [hpot]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hpost r]
  calc (2 ^ 22 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ q, encWt z l e q.2 * (σ q q).re) +
        ENNReal.ofReal (∑ r : Option HashOutput × QMem, dW (fun q ↦ encPotQ q.2)
          (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ))
      = ENNReal.ofReal ((2 ^ 22 : ℝ)⁻¹ * (∑ q, encWt z l e q.2 * (σ q q).re) +
          ∑ r : Option HashOutput × QMem, dW (fun q ↦ encPotQ q.2)
            (MatrixMap.conj (hwReadKraus (.readH z (trialUpdQ l e z)) r) σ)) := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun r _ ↦ hpost r),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (dW (fun q ↦ encPotQ q.2) σ +
          4 * G * (∑ q, recUWt z l e q.2 * (σ q q).re) + (2 ^ 250 : ℝ)⁻¹ * σ.trace.re) :=
        ENNReal.ofReal_le_ofReal key
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add hP0 (by positivity), add_assoc,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
          ENNReal.ofReal_ofNat]

end Quantum.Qrom.Xmss

end
