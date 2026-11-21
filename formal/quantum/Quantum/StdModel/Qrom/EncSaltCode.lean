module

public import Quantum.StdModel.Qrom.EncSaltCodeRead
public import Quantum.StdModel.Qrom.EncSaltBound

@[expose] public section

/-!
# EncTCR$ in the QROM: the cost of an answer with codeword partners

`ansCost` (`EncSaltFirst`) charges every trial cell of a grind as a possible collision partner of
a later trial, `2F · limit² / N` per answer. A new record needs a codeword value, so it can only
collide with a cell of its class holding a codeword truncation (`codeP`); an earlier trial's cell
was read with a non-codeword outcome, and after the read holds another value with weight
`O(1/N)` only, or its recorded content before the read (`EncSaltCodeRead`).

* **The cost of a trial read** (`readLin_uSel_le_code`): on an empty cell of a class without a
  record, `2F/N` per other cell of the class holding a codeword truncation.
* **Stage potentials** (`Pt`): at stage `c`, the weight of trial `c'` counts the partners off the
  trials `[c, c')` (`gW`); the read of trial `c` pays `κc c = 2F/N` per later trial, at rate `1/N`
  on an empty cell and fully on a recorded one.
* **The cost of an answer** (`totalWeight_answer_le_code`, `ansBound_ansCode`):
  `ansCode = limit · ((2 + 2/N) · #{r | cell (M, r) recorded} / |Salt| +
  (2F · #{recorded cells of the class} + 2F + 2 + 2F · limit/N) / N)`, and
  `ansCode ≤ lamS · cntY + c0C` with `c0C = limit · (2F + 2 + ε)/N`, `ε = 2F · limit / N`
  (`ansCode_le_cntY`).
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom.EncSalt.Code

open Quantum QuantumRuntime Quantum.Sponge Quantum.Qrom HashSig Props

/-! ## The cost of a trial read with codeword partners -/

section cost

open Tcr (Mem BadR tgt Recordless SameCls IsG GSep tgt_eq_empty_of_recordless card_tgt_le
  badR_record_iff)

variable {Par Tw Msg Salt Dig : Type} {e : SaltEnc Par Tw Msg Salt Dig}

variable (e) in
/-- The cell `y` holds (hardwired or in the database) a value truncating to a codeword. -/
def CodeAt (s : RomReg HashDomain HashOutput Mem) (y : HashDomain) : Prop :=
  ∃ w, unionH s y = some w ∧ e.isCode (e.hash.trunc w) = true

variable (e) in
open scoped Classical in
/-- **The codeword partners of `x` off `E`**: the other cells of its class off `E` holding a
codeword truncation. -/
noncomputable def codeP (x : HashDomain) (E : Finset HashDomain)
    (s : RomReg HashDomain HashOutput Mem) : ℕ :=
  (Finset.univ.filter fun y ↦ SameCls e.hash G y x ∧ y ≠ x ∧ y ∉ E ∧ CodeAt e s y).card

variable (e) in
/-- **The codeword truncations a new record at `x` must avoid**: those of the other cells of its
class holding a codeword truncation, and of the judge's read at the class. -/
theorem exists_truncSet_code (x : HashDomain) (s : RomReg HashDomain HashOutput Mem) :
    ∃ T : Finset Dig, T.card ≤ codeP e x ∅ s + 1 ∧
      (∀ y w, SameCls e.hash G y x → y ≠ x → unionH s y = some w →
        e.isCode (e.hash.trunc w) = true → e.hash.trunc w ∈ T) ∧
      (∀ z' w, s.2.2.slot = some (z', w) → SameCls e.hash G z' x → e.hash.trunc w ∈ T) := by
  classical
  refine ⟨(Finset.univ.filter fun y ↦ SameCls e.hash G y x ∧ y ≠ x ∧
      y ∉ (∅ : Finset HashDomain) ∧ CodeAt e s y).image
      (fun y ↦ e.hash.trunc ((unionH s y).getD 0)) ∪
    (s.2.2.slot.elim ∅ fun p ↦ if SameCls e.hash G p.1 x then {e.hash.trunc p.2} else ∅),
    ?_, fun y w hyx hne hy hc ↦ ?_, fun z' w hsl hzx ↦ ?_⟩
  · refine (Finset.card_union_le _ _).trans (add_le_add (Finset.card_image_le.trans ?_) ?_)
    · unfold codeP
      exact le_of_eq (congrArg Finset.card (Finset.filter_congr fun _ _ ↦ Iff.rfl))
    · exact card_optionElim_le (α := HashDomain × HashOutput) (β := Dig) _
        (fun p ↦ SameCls e.hash G p.1 x) fun p ↦ e.hash.trunc p.2
  · rw [Finset.mem_union, Finset.mem_image]
    refine Or.inl ⟨y, ?_, by rw [hy]; rfl⟩
    rw [Finset.mem_filter]
    exact ⟨by simp, hyx, hne, Finset.notMem_empty y, w, hy, hc⟩
  · rw [Finset.mem_union, hsl]
    simp [hzx]

/-- The read of `x` from `s` moves the memory with the answers' policy, and keeps the event,
unless the outcome records a class without a record with a truncation in `T`, `T` holding the
codeword truncations of the class. -/
theorem badR_uSel_or_code (hs : GSep e.hash G) {x : HashDomain}
    (s : RomReg HashDomain HashOutput Mem) {T : Finset Dig}
    (hT1 : ∀ y w, SameCls e.hash G y x → y ≠ x → unionH s y = some w →
      e.isCode (e.hash.trunc w) = true → e.hash.trunc w ∈ T)
    (hT2 : ∀ z' w, s.2.2.slot = some (z', w) → SameCls e.hash G z' x → e.hash.trunc w ∈ T)
    (v : HashOutput) (hv : ¬ (Recordless e.hash G s.2.2 x ∧ e.hash.trunc v ∈ T)) :
    ((s.1, s.2.1, uSel e x s.2.2 (some v)) : RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔
      s ∈ BadR e.hash G := by
  classical
  by_cases hrec : IsG e.hash G x ∧ Recordless e.hash G s.2.2 x ∧
      ∃ v', some v = some v' ∧ e.isCode (e.hash.trunc v') = true
  · have hTv : e.hash.trunc v ∉ T := fun h ↦ hv ⟨hrec.2.1, h⟩
    obtain ⟨v', hv', hcv⟩ := hrec.2.2
    rw [Option.some_inj] at hv'
    subst hv'
    refine badR_record_new hs hrec.2.1 (v := v) ?_ rfl (fun y w hyx hne hy h ↦ ?_)
      fun z' w hsl hzx h ↦ ?_
    · rw [uSel_recs, ite_eq_left hrec]
      rfl
    · exact hTv (h ▸ hT1 y w hyx hne hy (by rw [h]; exact hcv))
    · exact hTv (h ▸ hT2 z' w hsl hzx)
  · refine badR_congr_mem (s := s) ?_ rfl
    rw [uSel_recs, ite_eq_right hrec]

/-- The values counted by `rdCnt` and `hFlip` at the empty cell `x`: in the target of `x`, or
recording a class without a record with a truncation in `T`. -/
theorem rd_or_flip_imp_code (hs : GSep e.hash G) {x : HashDomain}
    (q : Unit × RomReg HashDomain HashOutput Mem) (hw : q.2.2.1.1 x = none)
    (hd : q.2.1.1 x = none) {T : Finset Dig}
    (hT1 : ∀ y w, SameCls e.hash G y x → y ≠ x → unionH q.2 y = some w →
      e.isCode (e.hash.trunc w) = true → e.hash.trunc w ∈ T)
    (hT2 : ∀ z' w, q.2.2.2.slot = some (z', w) → SameCls e.hash G z' x → e.hash.trunc w ∈ T)
    (v : HashOutput) :
    (¬ ((((Function.update q.2.1.1 x (some v), q.2.1.2), q.2.2.1, uSel e x q.2.2.2 (some v)) :
        RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔ q.2 ∈ BadR e.hash G) ∨
      hFlip (BadR e.hash G) x (uSel e x) q v) →
    v ∈ tgt e.hash G q.2.2.1 q.2.2.2 x ∨
      (Recordless e.hash G q.2.2.2 x ∧ e.hash.trunc v ∈ T) := by
  intro h
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnt, hnr⟩ := hcon
  have hrd : ∀ a : Option HashOutput,
      ((((Function.update q.2.1.1 x a, q.2.1.2), q.2.2.1, uSel e x q.2.2.2 (some v)) :
        RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔
        (((Function.update q.2.1.1 x a, q.2.1.2), q.2.2.1, q.2.2.2) :
          RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G) := fun a ↦ by
    have hu : ∀ y, y ≠ x →
        unionH (((Function.update q.2.1.1 x a, q.2.1.2), q.2.2.1, q.2.2.2) :
          RomReg HashDomain HashOutput Mem) y = unionH q.2 y := fun y hy ↦ by
      change (q.2.2.1.1 y).or (Function.update q.2.1.1 x a y) = (q.2.2.1.1 y).or (q.2.1.1 y)
      rw [Function.update_of_ne hy]
    exact badR_uSel_or_code hs (((Function.update q.2.1.1 x a, q.2.1.2), q.2.2.1, q.2.2.2) :
        RomReg HashDomain HashOutput Mem)
      (fun y w hyx hne hy hc ↦ hT1 y w hyx hne ((hu y hne).symm.trans hy) hc) hT2 v hnr
  have hrec : ((((Function.update q.2.1.1 x (some v), q.2.1.2), q.2.2) :
      RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔ q.2 ∈ BadR e.hash G) :=
    badR_record_iff hw hnt none hd (Or.inl rfl)
  rcases h with h | h | ⟨a, h⟩
  · exact h ((hrd (some v)).trans hrec)
  · exact h hrec
  · exact h (hrd a)

open scoped Classical in
/-- A count of the values counted by `rdCnt` or `hFlip`: `F (codeP + 1)` at a class without a
record, `F` at a class with one. -/
theorem card_rd_le_code (hs : GSep e.hash G) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) {x : HashDomain}
    (q : Unit × RomReg HashDomain HashOutput Mem) (hw : q.2.2.1.1 x = none)
    (hd : q.2.1.1 x = none) (P : HashOutput → Prop) {_ : DecidablePred P}
    (hP : ∀ v, P v → ¬ ((((Function.update q.2.1.1 x (some v), q.2.1.2), q.2.2.1,
        uSel e x q.2.2.2 (some v)) : RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔
          q.2 ∈ BadR e.hash G) ∨ hFlip (BadR e.hash G) x (uSel e x) q v) :
    ((Finset.univ.filter P).card : ℝ) ≤
      if Recordless e.hash G q.2.2.2 x then F * (codeP e x ∅ q.2 + 1) else F := by
  classical
  obtain ⟨T, hTc, hT1, hT2⟩ := exists_truncSet_code e x q.2
  have himp := fun v hv ↦ rd_or_flip_imp_code hs q hw hd hT1 hT2 v (hP v hv)
  split_ifs with hr
  · have h := card_filter_le_of_trunc e.hash.trunc hF T P fun v hv ↦ ((himp v hv).resolve_left
      (by rw [tgt_eq_empty_of_recordless hr]; exact Set.notMem_empty v)).2
    exact_mod_cast h.trans (Nat.mul_le_mul_left F hTc)
  · have h := (Finset.card_le_card (Finset.monotone_filter_right (s := Finset.univ)
      (p := P) (q := fun v ↦ v ∈ tgt e.hash G q.2.2.1 q.2.2.2 x) fun v _ hv ↦
        ((himp v hv).resolve_right fun h ↦ hr h.1))).trans (card_tgt_le hF _ _ _)
    exact_mod_cast h

open scoped Classical in
/-- **The cost of a trial read with codeword partners**, linearized: `2 + 2/N` on a recorded or
hardwired cell; on an empty cell `(2F + 2)/N`, plus `2F/N` per other cell of its class holding a
codeword truncation if the class has no record. -/
theorem readLin_uSel_le_code (hs : GSep e.hash G) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) (x : HashDomain)
    (q : Unit × RomReg HashDomain HashOutput Mem) :
    readLin (BadR e.hash G) x (uSel e x) q ≤
      (2 + 2 / (Fintype.card HashOutput : ℝ)) *
          (if q.2.2.1.1 x = none ∧ q.2.1.1 x = none then 0 else 1) +
        ((if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * codeP e x ∅ q.2 else 0) +
          2 * F + 2) / Fintype.card HashOutput := by
  have hN : (0 : ℝ) < Fintype.card HashOutput := Nat.cast_pos.2 Fintype.card_pos
  have hpd := pd_flip_le_readH (BadR e.hash G) x (uSel e x) q
  have hR : 0 ≤ (if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * codeP e x ∅ q.2
      else 0) := by split_ifs <;> positivity
  have hcls : ∀ o, (if hCls (BadR e.hash G) (uSel e x) o q then (1 : ℝ) else 0) ≤ 1 :=
    fun o ↦ by split_ifs <;> norm_num
  have h2N : 0 ≤ 2 / (Fintype.card HashOutput : ℝ) := by positivity
  unfold readLin
  by_cases hw : q.2.2.1.1 x = none
  · by_cases hd : q.2.1.1 x = none
    · rw [ite_eq_left hw, ite_eq_left hd, ite_eq_left ⟨hw, hd⟩, ite_eq_left ⟨hw, hd⟩,
        mul_zero, zero_add]
      rw [ite_eq_right fun h ↦ h.2 hd] at hpd
      have h1 : (rdCnt (BadR e.hash G) x (uSel e x) q : ℝ) ≤ _ :=
        card_rd_le_code hs hF q hw hd _ fun v hv ↦ Or.inl hv
      have h2 : ((Finset.univ.filter (hFlip (BadR e.hash G) x (uSel e x) q)).card : ℝ) ≤ _ :=
        card_rd_le_code hs hF q hw hd _ fun v hv ↦ Or.inr hv
      have key : (rdCnt (BadR e.hash G) x (uSel e x) q : ℝ) +
          (Finset.univ.filter (hFlip (BadR e.hash G) x (uSel e x) q)).card ≤
          (if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * codeP e x ∅ q.2 else 0) +
            2 * F := by
        split_ifs at h1 h2 ⊢
        · push_cast at h1 h2
          nlinarith
        · linarith
      refine le_trans (add_le_add le_rfl hpd) ?_
      rw [add_zero, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith [key]) hN.le
    · have hn : ¬ (q.2.2.1.1 x = none ∧ q.2.1.1 x = none) := fun h ↦ hd h.2
      rw [ite_eq_left hw, ite_eq_right hd, ite_eq_right hn, ite_eq_right hn, mul_one, add_zero]
      rw [ite_eq_left (show q.2.2.1.1 x = none ∧ q.2.1.1 x ≠ none from ⟨hw, hd⟩)] at hpd
      have h3 := hcls (q.2.1.1 x)
      have h4 : 0 ≤ ((if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * codeP e x ∅ q.2
          else 0) + 2 * F + 2) / Fintype.card HashOutput := by positivity
      linarith
  · have hn : ¬ (q.2.2.1.1 x = none ∧ q.2.1.1 x = none) := fun h ↦ hw h.1
    have hn' : ¬ (q.2.2.1.1 x = none ∧ q.2.1.1 x ≠ none) := fun h ↦ hw h.1
    rw [ite_eq_right hw, ite_eq_right hn, ite_eq_right hn, mul_one, add_zero]
    rw [ite_eq_right hn'] at hpd
    have h3 := hcls (q.2.2.1.1 x)
    have h4 : 0 ≤ ((if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * codeP e x ∅ q.2
        else 0) + 2 * F + 2) / Fintype.card HashOutput := by positivity
    nlinarith

end cost

/-! ## The stage potentials of a grind -/

section stages

open Quantum.Qrom HashSig Props OracleComp OracleSpec
open Quantum.Xmss.Hybrid (runtime2)
open Tcr (Mem Recordless SameCls GSep GCell gCell_unique)

variable {Par Tw Msg Salt Dig : Type} {e : SaltEnc Par Tw Msg Salt Dig}

variable (e) in
/-- The cells of the trials `[c₀, c₁)` of a grind from the base `r0`. -/
noncomputable def Eset (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c₀ c₁ : ℕ) :
    Finset HashDomain :=
  (Finset.Ico c₀ c₁).image fun c ↦ cell e P t (M, e.shift r0 c)

theorem Eset_self (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c : ℕ) :
    Eset e P t M r0 c c = ∅ := by
  simp [Eset]

variable (e) in
open scoped Classical in
/-- **The weight of trial `c'` at stage `c₀`**: the cost of its read, its cell's partners counted
off the trials `[c₀, c')`. -/
noncomputable def gW (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c₀ c' : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : ℝ :=
  (2 + 2 / (Fintype.card HashOutput : ℝ)) *
      (if s.2.1.1 (cell e P t (M, e.shift r0 c')) = none ∧
        s.1.1 (cell e P t (M, e.shift r0 c')) = none then 0 else 1) +
    ((if Recordless e.hash G s.2.2 (cell e P t (M, e.shift r0 c')) then
      2 * (F : ℝ) * codeP e (cell e P t (M, e.shift r0 c')) (Eset e P t M r0 c₀ c') s else 0) +
      2 * F + 2) / Fintype.card HashOutput

variable (e) in
/-- **The slack of the read of trial `c`**: `2F/N` per later trial. -/
noncomputable def κc (F c : ℕ) : ℝ :=
  2 * F * ((Finset.Ico (c + 1) e.limit).card : ℝ) / Fintype.card HashOutput

variable (e) in
/-- The weight of trial `c'` at stage `c₀`, with the slack of its read. -/
noncomputable def termW (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c₀ c' : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : ℝ :=
  gW e F P t M r0 c₀ c' s + (κc e F c' / Fintype.card HashOutput +
    if s.1.1 (cell e P t (M, e.shift r0 c')) = none then 0 else κc e F c')

variable (e) in
/-- **The potential of stage `c`** of a grind: the trials `[c, limit)`. -/
noncomputable def Pt (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : ℝ :=
  ∑ c' ∈ Finset.Ico c e.limit, termW e F P t M r0 c c' s

variable (e) in
/-- The potential of stage `c` past trial `c`. -/
noncomputable def Hc (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : ℝ :=
  ∑ c' ∈ Finset.Ico (c + 1) e.limit, termW e F P t M r0 c c' s

theorem κc_nonneg (F c : ℕ) : 0 ≤ κc e F c := by
  unfold κc
  positivity

open scoped Classical in
theorem gW_nonneg (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c₀ c' : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : 0 ≤ gW e F P t M r0 c₀ c' s := by
  unfold gW
  have : 0 ≤ (if Recordless e.hash G s.2.2 (cell e P t (M, e.shift r0 c')) then
      2 * (F : ℝ) * codeP e (cell e P t (M, e.shift r0 c')) (Eset e P t M r0 c₀ c') s
        else 0) := by split_ifs <;> positivity
  split_ifs <;> positivity

theorem termW_nonneg (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c₀ c' : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : 0 ≤ termW e F P t M r0 c₀ c' s := by
  unfold termW
  have h0 : 0 ≤ (if s.1.1 (cell e P t (M, e.shift r0 c')) = none then 0 else κc e F c') := by
    split_ifs
    · exact le_rfl
    · exact κc_nonneg F c'
  exact add_nonneg (gW_nonneg F P t M r0 c₀ c' s)
    (add_nonneg (div_nonneg (κc_nonneg F c') (Nat.cast_nonneg _)) h0)

theorem Pt_nonneg (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : 0 ≤ Pt e F P t M r0 c s :=
  Finset.sum_nonneg fun _ _ ↦ termW_nonneg F P t M r0 c _ s

theorem Hc_nonneg (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : 0 ≤ Hc e F P t M r0 c s :=
  Finset.sum_nonneg fun _ _ ↦ termW_nonneg F P t M r0 c _ s

/-- **A stage potential splits** into the trial's weight, the slack of its read and the rest. -/
theorem Pt_split (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) {c : ℕ} (hc : c < e.limit)
    (s : HwReg HashOutput HashDomain Mem) :
    gW e F P t M r0 c c s + (Hc e F P t M r0 c s + κc e F c / Fintype.card HashOutput +
      if s.1.1 (cell e P t (M, e.shift r0 c)) = none then 0 else κc e F c) ≤
      Pt e F P t M r0 c s := by
  unfold Pt Hc
  rw [Finset.sum_eq_sum_Ico_succ_bot hc, termW]
  apply le_of_eq
  ring

open scoped Classical in
/-- The read of a trial costs at most its weight at its stage. -/
theorem dSΦ_trial_le_code (hs : GSep e.hash G) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) (P : Par) (t : Tw)
    (M : Msg) (r0 : Salt) (c : ℕ)
    (σ : Matrix ((hwSpec HashOutput HashDomain Mem).In
        (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
          (upd e .answer (cell e P t (M, e.shift r0 c)))))) × HwReg HashOutput HashDomain Mem)
        ((hwSpec HashOutput HashDomain Mem).In
          (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
            (upd e .answer (cell e P t (M, e.shift r0 c)))))) ×
              HwReg HashOutput HashDomain Mem) ℂ) (hσ : σ.PosSemidef) :
    ENNReal.ofReal (dSΦ e (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
        (upd e .answer (cell e P t (M, e.shift r0 c)))))) σ).trace.re ≤
      ENNReal.ofReal (∑ q, gW e F P t M r0 c c q.2 * (σ q q).re) := by
  rw [dSΦ, re_trace_conj_wPot (dSf_nonneg e _)]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_
    (Complex.nonneg_iff.1 hσ.diag_nonneg).1)
  simp only [dSf]
  by_cases hu : upd e .answer (cell e P t (M, e.shift r0 c)) =
      Tcr.uRed (cell e P t (M, e.shift r0 c)) ∨
      upd e .answer (cell e P t (M, e.shift r0 c)) = Tcr.uJudge (cell e P t (M, e.shift r0 c))
  · rw [ite_eq_left hu]
    exact gW_nonneg F P t M r0 c c q.2
  · rw [ite_eq_right hu]
    refine (readLin_uSel_le_code hs hF (cell e P t (M, e.shift r0 c)) q).trans (le_of_eq ?_)
    unfold gW
    rw [Eset_self]

/-- A filter whose elements other than `a` satisfy `Q` is at most the `Q`-filter and one. -/
theorem card_filter_le_insert {α : Type} [Fintype α] [DecidableEq α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (a : α) (h : ∀ y, P y → y ≠ a → Q y) :
    ((Finset.univ.filter P).card : ℝ) ≤ (Finset.univ.filter Q).card + 1 := by
  have hsub : Finset.univ.filter P ⊆ insert a (Finset.univ.filter Q) := fun y hy ↦ by
    by_cases hya : y = a
    · exact Finset.mem_insert.2 (Or.inl hya)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, h y (Finset.mem_filter.1 hy).2 hya⟩)
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

open scoped Classical in
/-- **The read of trial `c` moves the partners of a later trial** only through the cell of
trial `c`, which the later stage counts. -/
theorem codeP_move (P : Par) (t : Tw) (M : Msg) (r0 : Salt) {c c' : ℕ}
    (s s' : HwReg HashOutput HashDomain Mem) (hw : s'.2.1 = s.2.1)
    (hd : ∀ y, y ≠ cell e P t (M, e.shift r0 c) → s'.1.1 y = s.1.1 y) :
    (codeP e (cell e P t (M, e.shift r0 c')) (Eset e P t M r0 (c + 1) c') s' : ℝ) ≤
      codeP e (cell e P t (M, e.shift r0 c')) (Eset e P t M r0 c c') s +
        if CodeAt e s' (cell e P t (M, e.shift r0 c)) then 1 else 0 := by
  have hmem : ∀ y, y ≠ cell e P t (M, e.shift r0 c) →
      (SameCls e.hash G y (cell e P t (M, e.shift r0 c')) ∧ y ≠ cell e P t (M, e.shift r0 c') ∧
        y ∉ Eset e P t M r0 (c + 1) c' ∧ CodeAt e s' y) →
      (SameCls e.hash G y (cell e P t (M, e.shift r0 c')) ∧ y ≠ cell e P t (M, e.shift r0 c') ∧
        y ∉ Eset e P t M r0 c c' ∧ CodeAt e s y) := by
    rintro y hyx ⟨h1, h2, h3, w, hw', hc⟩
    refine ⟨h1, h2, fun hE ↦ h3 ?_, w, ?_, hc⟩
    · rw [Eset, Finset.mem_image] at hE ⊢
      obtain ⟨c'', hc'', hy⟩ := hE
      rw [Finset.mem_Ico] at hc''
      refine ⟨c'', Finset.mem_Ico.2 ⟨?_, hc''.2⟩, hy⟩
      by_contra hlt
      have hcc : c'' = c := by omega
      subst hcc
      exact hyx hy.symm
    · rw [← hw']
      change (s.2.1.1 y).or (s.1.1 y) = (s'.2.1.1 y).or (s'.1.1 y)
      rw [hw, hd y hyx]
  unfold codeP
  by_cases hx : CodeAt e s' (cell e P t (M, e.shift r0 c))
  · rw [ite_eq_left hx]
    exact card_filter_le_insert _ _ (cell e P t (M, e.shift r0 c)) fun y hy hyx ↦ hmem y hyx hy
  · rw [ite_eq_right hx, add_zero]
    exact_mod_cast card_filter_mono' _ _ fun y hy ↦
      hmem y (fun h ↦ hx (h ▸ hy.2.2.2)) hy

open scoped Classical in
/-- **The read of trial `c` moves the weight of a later trial** by at most `2F/N`, and only when
the cell of trial `c` then holds a codeword truncation. -/
theorem termW_move (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) {c c' : ℕ}
    (hxx : cell e P t (M, e.shift r0 c') ≠ cell e P t (M, e.shift r0 c))
    (s s' : HwReg HashOutput HashDomain Mem) (hw : s'.2.1 = s.2.1)
    (hd : ∀ y, y ≠ cell e P t (M, e.shift r0 c) → s'.1.1 y = s.1.1 y)
    (hrec : s'.2.2.recs = s.2.2.recs) :
    termW e F P t M r0 (c + 1) c' s' ≤ termW e F P t M r0 c c' s +
      2 * F / Fintype.card HashOutput *
        (if CodeAt e s' (cell e P t (M, e.shift r0 c)) then 1 else 0) := by
  have hN : (0 : ℝ) ≤ Fintype.card HashOutput := Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have h1 := hd _ hxx
  have hrl : Recordless e.hash G s'.2.2 (cell e P t (M, e.shift r0 c')) ↔
      Recordless e.hash G s.2.2 (cell e P t (M, e.shift r0 c')) := by
    unfold Tcr.Recordless
    rw [hrec]
  have hcp := codeP_move (c := c) (c' := c') P t M r0 s s' hw hd
  have hind : (0 : ℝ) ≤ if CodeAt e s' (cell e P t (M, e.shift r0 c)) then 1 else 0 := by
    split_ifs <;> norm_num
  have hcp0 : (0 : ℝ) ≤ codeP e (cell e P t (M, e.shift r0 c')) (Eset e P t M r0 c c') s :=
    Nat.cast_nonneg _
  have hR : (if Recordless e.hash G s'.2.2 (cell e P t (M, e.shift r0 c')) then
      2 * (F : ℝ) * codeP e (cell e P t (M, e.shift r0 c')) (Eset e P t M r0 (c + 1) c') s'
        else 0) ≤
      (if Recordless e.hash G s.2.2 (cell e P t (M, e.shift r0 c')) then
        2 * (F : ℝ) * codeP e (cell e P t (M, e.shift r0 c')) (Eset e P t M r0 c c') s
          else 0) + 2 * F * (if CodeAt e s' (cell e P t (M, e.shift r0 c)) then 1 else 0) := by
    by_cases ha : Recordless e.hash G s'.2.2 (cell e P t (M, e.shift r0 c'))
    · rw [ite_eq_left ha, ite_eq_left (hrl.1 ha)]
      nlinarith
    · rw [ite_eq_right ha]
      positivity
  have hdiv := div_le_div_of_nonneg_right (add_le_add (add_le_add hR (le_refl (2 * (F : ℝ))))
    (le_refl 2)) hN
  unfold termW gW
  rw [hw, h1]
  have he : ((if Recordless e.hash G s.2.2 (cell e P t (M, e.shift r0 c')) then
        2 * (F : ℝ) * codeP e (cell e P t (M, e.shift r0 c')) (Eset e P t M r0 c c') s
          else 0) + 2 * F * (if CodeAt e s' (cell e P t (M, e.shift r0 c)) then 1 else 0) +
        2 * F + 2) / Fintype.card HashOutput =
      ((if Recordless e.hash G s.2.2 (cell e P t (M, e.shift r0 c')) then
        2 * (F : ℝ) * codeP e (cell e P t (M, e.shift r0 c')) (Eset e P t M r0 c c') s
          else 0) + 2 * F + 2) / Fintype.card HashOutput +
      2 * F / Fintype.card HashOutput *
        (if CodeAt e s' (cell e P t (M, e.shift r0 c)) then 1 else 0) := by ring
  linarith

/-- The cells of two trials of a base differ. -/
theorem cell_ne (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    (P : Par) (t : Tw) (M : Msg) (r0 : Salt) {c c' : ℕ} (hc : c < e.limit)
    (hc' : c' < e.limit) (hcc : c ≠ c') :
    cell e P t (M, e.shift r0 c') ≠ cell e P t (M, e.shift r0 c) := fun h ↦
  hcc (hdist r0 c c' hc hc' (congrArg Prod.snd (cell_inj hinj hlen h)).symm)

/-- The answers' policy keeps the records on a non-codeword outcome. -/
theorem uSel_recs_of_not_code {x : HashDomain} (m : Mem) {o : Option HashOutput}
    (ho : e.isCode (e.hash.trunc (o.getD 0)) = false) : (uSel e x m o).recs = m.recs := by
  rw [uSel_recs, ite_eq_right]
  rintro ⟨-, -, v, rfl, hv⟩
  simp only [Option.getD_some] at ho
  rw [ho] at hv
  exact Bool.false_ne_true hv

open scoped Classical in
/-- **The next stage after the read of trial `c`**, at a content `a` of its cell and a
non-codeword outcome `o`: at most the rest of the stage, plus `κc c` when `a` is neither empty nor
`o`. -/
theorem Pt_succ_le (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) {c : ℕ} (hc : c < e.limit)
    (s : HwReg HashOutput HashDomain Mem) (hs : s.2.1.1 (cell e P t (M, e.shift r0 c)) = none)
    (a o : Option HashOutput) (ho : e.isCode (e.hash.trunc (o.getD 0)) = false) :
    Pt e F P t M r0 (c + 1) ((Function.update s.1.1 (cell e P t (M, e.shift r0 c)) a, s.1.2),
      s.2.1, upd e .answer (cell e P t (M, e.shift r0 c)) s.2.2 o) ≤
      Hc e F P t M r0 c s + if a = none ∨ a = o then 0 else κc e F c := by
  set s' : HwReg HashOutput HashDomain Mem :=
    ((Function.update s.1.1 (cell e P t (M, e.shift r0 c)) a, s.1.2), s.2.1,
      upd e .answer (cell e P t (M, e.shift r0 c)) s.2.2 o) with hs'
  have hrec : s'.2.2.recs = s.2.2.recs := uSel_recs_of_not_code s.2.2 ho
  have hd : ∀ y, y ≠ cell e P t (M, e.shift r0 c) → s'.1.1 y = s.1.1 y := fun y hy ↦
    Function.update_of_ne hy _ _
  have hind : (if CodeAt e s' (cell e P t (M, e.shift r0 c)) then (1 : ℝ) else 0) ≤
      if a = none ∨ a = o then 0 else 1 := by
    by_cases ha : a = none ∨ a = o
    · rw [ite_eq_left ha, ite_eq_right]
      rintro ⟨w, hw, hcw⟩
      have hu : unionH s' (cell e P t (M, e.shift r0 c)) = a := by
        change (s.2.1.1 _).or (Function.update s.1.1 _ a _) = a
        rw [hs, Function.update_self, Option.none_or]
      rw [hu] at hw
      rcases ha with rfl | rfl
      · cases hw
      · subst hw
        simp only [Option.getD_some] at ho
        rw [ho] at hcw
        exact Bool.false_ne_true hcw
    · rw [ite_eq_right ha]
      split_ifs <;> norm_num
  have hterm : ∀ c' ∈ Finset.Ico (c + 1) e.limit, termW e F P t M r0 (c + 1) c' s' ≤
      termW e F P t M r0 c c' s + 2 * F / Fintype.card HashOutput *
        (if CodeAt e s' (cell e P t (M, e.shift r0 c)) then 1 else 0) := fun c' hc' ↦ by
    rw [Finset.mem_Ico] at hc'
    exact termW_move F P t M r0 (cell_ne hinj hlen hdist P t M r0 hc hc'.2 (by omega)) s s' rfl
      hd hrec
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  refine add_le_add le_rfl ?_
  have hk : (0 : ℝ) ≤ 2 * F / Fintype.card HashOutput * (Finset.Ico (c + 1) e.limit).card := by
    positivity
  calc ((Finset.Ico (c + 1) e.limit).card : ℝ) * (2 * F / Fintype.card HashOutput *
        (if CodeAt e s' (cell e P t (M, e.shift r0 c)) then 1 else 0))
      = 2 * F / Fintype.card HashOutput * (Finset.Ico (c + 1) e.limit).card *
        (if CodeAt e s' (cell e P t (M, e.shift r0 c)) then 1 else 0) := by ring
    _ ≤ 2 * F / Fintype.card HashOutput * (Finset.Ico (c + 1) e.limit).card *
        (if a = none ∨ a = o then 0 else 1) := mul_le_mul_of_nonneg_left hind hk
    _ = if a = none ∨ a = o then 0 else κc e F c := by
        unfold κc
        split_ifs
        · ring
        · ring

open scoped Classical in
/-- **The next stage after the read of a hardwired trial cell** with a non-codeword value: at
most the rest of the stage. -/
theorem Pt_succ_le_hw (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) {c : ℕ} (hc : c < e.limit)
    (s : HwReg HashOutput HashDomain Mem) (hs : s.2.1.1 (cell e P t (M, e.shift r0 c)) ≠ none)
    (ho : e.isCode (e.hash.trunc ((s.2.1.1 (cell e P t (M, e.shift r0 c))).getD 0)) = false) :
    Pt e F P t M r0 (c + 1) (s.1, s.2.1, upd e .answer (cell e P t (M, e.shift r0 c)) s.2.2
      (s.2.1.1 (cell e P t (M, e.shift r0 c)))) ≤ Hc e F P t M r0 c s := by
  set s' : HwReg HashOutput HashDomain Mem := (s.1, s.2.1, upd e .answer
    (cell e P t (M, e.shift r0 c)) s.2.2 (s.2.1.1 (cell e P t (M, e.shift r0 c)))) with hs'
  have hrec : s'.2.2.recs = s.2.2.recs := uSel_recs_of_not_code s.2.2 ho
  have hnc : ¬ CodeAt e s' (cell e P t (M, e.shift r0 c)) := by
    rintro ⟨w, hw, hcw⟩
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hs
    have hu : unionH s' (cell e P t (M, e.shift r0 c)) = some v := by
      change (s.2.1.1 _).or (s.1.1 _) = some v
      rw [hv, Option.some_or]
    rw [hu] at hw
    cases hw
    rw [hv] at ho
    simp only [Option.getD_some] at ho
    rw [ho] at hcw
    exact Bool.false_ne_true hcw
  have hterm : ∀ c' ∈ Finset.Ico (c + 1) e.limit, termW e F P t M r0 (c + 1) c' s' ≤
      termW e F P t M r0 c c' s := fun c' hc' ↦ by
    rw [Finset.mem_Ico] at hc'
    have h := termW_move F P t M r0 (cell_ne hinj hlen hdist P t M r0 hc hc'.2 (by omega)) s s'
      rfl (fun _ _ ↦ rfl) hrec
    rw [ite_eq_right hnc, mul_zero, add_zero] at h
    exact h
  exact Finset.sum_le_sum hterm

end stages

/-! ## The cost of an answer -/

section final

open Quantum.Qrom HashSig Props OracleComp OracleSpec
open Quantum.Xmss.Hybrid (runtime2)
open Tcr (Mem Recordless SameCls GSep GCell gCell_unique)

variable {Par Tw Msg Salt Dig : Type} {e : SaltEnc Par Tw Msg Salt Dig}

open scoped Classical in
/-- **An answer, as a step bound with stage potentials**: the grind from every base, averaged
over the base. -/
theorem step₂_answer_code [SampleableType Salt] (hs : GSep e.hash G)
    (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    [Fintype Salt] (m₀ : Mem) (B : QReg) (P : Par) (q : Tw × Msg) :
    Step₂ (runtime2 HashOutput HashDomain m₀) .instruments
      (fun i σ ↦ ENNReal.ofReal (dSΦ e i σ).trace.re)
      (readProgOf (upd e) ((sample romWorld Salt >>= fun r0 ↦
        e.grind romWorld P q.1 q.2 r0 0 e.limit).toQuantumAt (mixImpl .answer B)))
      (fun _ ↦ wPot fun _ ↦ 0)
      (wPot fun s ↦ ∑ r0, (Pr{let z ← $ᵗ Salt}[z = r0]).toReal *
        Pt e F P q.1 q.2 r0 0 s) := by
  rw [toQuantumAt_bind', sample, toQuantumAt_liftComp, readProgOf_bind₂]
  exact step₂_bind (isCP_dSΦ e) _ _ _
    (step₂_sampler m₀ (isCP_dSΦ e) (upd e) B ($ᵗ Salt)
      (fun r0 ↦ Pt e F P q.1 q.2 r0 0) fun r0 s ↦ Pt_nonneg F P q.1 q.2 r0 0 s)
    fun r0 ↦ step₂_grind_slack m₀ (isCP_dSΦ e) hlen B P q.1 q.2 r0
      (fun c ↦ gW e F P q.1 q.2 r0 c c) (Hc e F P q.1 q.2 r0) (Pt e F P q.1 q.2 r0) (κc e F)
      (fun c s ↦ gW_nonneg F P q.1 q.2 r0 c c s) (Hc_nonneg F P q.1 q.2 r0)
      (κc_nonneg F) (Pt_nonneg F P q.1 q.2 r0) e.limit
      (fun c _ σ hσ ↦ dSΦ_trial_le_code hs hF P q.1 q.2 r0 c σ hσ)
      (fun c hc s ↦ Pt_split F P q.1 q.2 r0 hc s)
      (fun c hc s hs' a o ho ↦ Pt_succ_le hinj hlen hdist F P q.1 q.2 r0 hc s hs' a o ho)
      (fun c hc s hs' ho ↦ Pt_succ_le_hw hinj hlen hdist F P q.1 q.2 r0 hc s hs' ho)
      e.limit 0 (zero_add _)

/-- A filter and the image of an injective family outside it, inside a second filter: their
cards add up to at most the second filter's. -/
theorem card_filter_add_le {α β : Type} [Fintype α] [DecidableEq α] (A R : α → Prop)
    [DecidablePred A] [DecidablePred R] (C : Finset β) (f : β → α)
    (hf : ∀ b ∈ C, ∀ b' ∈ C, f b = f b' → b = b') (hA : ∀ y, A y → R y)
    (hC : ∀ b ∈ C, R (f b) ∧ ¬ A (f b)) :
    (Finset.univ.filter A).card + C.card ≤ (Finset.univ.filter R).card := by
  have hcard : (C.image f).card = C.card :=
    Finset.card_image_of_injOn fun b hb b' hb' h ↦ hf b hb b' hb' h
  have hdisj : Finset.univ.filter A ∩ C.image f = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun y hy ↦ ?_
    obtain ⟨hyA, hyC⟩ := Finset.mem_inter.1 hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hyC
    exact (hC b hb).2 (Finset.mem_filter.1 hyA).2
  have hsub : Finset.univ.filter A ∪ C.image f ⊆ Finset.univ.filter R := by
    refine Finset.union_subset (fun y hy ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
      hA y (Finset.mem_filter.1 hy).2⟩) fun y hy ↦ ?_
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hC b hb).1⟩
  have h := Finset.card_union_add_card_inter (Finset.univ.filter A) (C.image f)
  rw [hdisj, Finset.card_empty, add_zero, hcard] at h
  rw [← h]
  exact Finset.card_le_card hsub

open scoped Classical in
/-- The partners of trial `c` off the earlier trials and the recorded earlier trial cells are
distinct recorded cells of the class, on a state without hardwired cells. -/
theorem codeP_add_le (hs : GSep e.hash G) (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    (P : Par) (t : Tw) (M : Msg) (r0 : Salt) {c : ℕ} (hc : c < e.limit)
    (s : HwReg HashOutput HashDomain Mem) (hw : ∀ y, s.2.1.1 y = none) :
    (codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s : ℝ) +
        ((Finset.range c).filter fun c'' ↦ s.1.1 (cell e P t (M, e.shift r0 c'')) ≠ none).card ≤
      (Finset.univ.filter fun y ↦ GCell e.hash G y P t ∧ s.1.1 y ≠ none).card := by
  have key : codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s +
      ((Finset.range c).filter fun c'' ↦ s.1.1 (cell e P t (M, e.shift r0 c'')) ≠ none).card ≤
      (Finset.univ.filter fun y ↦ GCell e.hash G y P t ∧ s.1.1 y ≠ none).card := by
    unfold codeP
    refine card_filter_add_le _ _ _ (fun c'' ↦ cell e P t (M, e.shift r0 c''))
      (fun b hb b' hb' h ↦ ?_) (fun y hy ↦ ?_) fun b hb ↦ ?_
    · have h₁ := Finset.mem_range.1 (Finset.mem_filter.1 hb).1
      have h₂ := Finset.mem_range.1 (Finset.mem_filter.1 hb').1
      exact hdist r0 b b' (by omega) (by omega) (congrArg Prod.snd (cell_inj hinj hlen h))
    · obtain ⟨hyx, -, -, w, hu, -⟩ := hy
      refine ⟨?_, ?_⟩
      · obtain ⟨P', t', h1, h2⟩ := hyx
        obtain ⟨rfl, rfl⟩ := gCell_unique hs (gCell_cell hlen P t _) h2
        exact h1
      · change (s.2.1.1 y).or (s.1.1 y) = some w at hu
        rw [hw, Option.none_or] at hu
        rw [hu]
        exact Option.some_ne_none w
    · have hlt := Finset.mem_range.1 (Finset.mem_filter.1 hb).1
      refine ⟨⟨gCell_cell hlen P t _, (Finset.mem_filter.1 hb).2⟩, fun h ↦ h.2.2.1 ?_⟩
      rw [Eset, Finset.mem_image]
      exact ⟨b, Finset.mem_Ico.2 ⟨Nat.zero_le _, hlt⟩, rfl⟩
  exact_mod_cast key

/-- **The slack of the reads of the recorded trial cells**, swapped: each later trial counts the
recorded earlier trial cells. -/
theorem sum_card_Ico_mul (L : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ∑ c ∈ Finset.range L, ((Finset.Ico (c + 1) L).card : ℝ) * (if p c then 1 else 0) =
      ∑ c' ∈ Finset.range L, (((Finset.range c').filter p).card : ℝ) := by
  have h1 : ∀ c, ((Finset.Ico (c + 1) L).card : ℝ) * (if p c then 1 else 0) =
      ∑ _c' ∈ Finset.Ico (c + 1) L, (if p c then (1 : ℝ) else 0) := fun c ↦ by
    rw [Finset.sum_const, nsmul_eq_mul]
  simp only [h1]
  rw [Finset.sum_comm' (s := Finset.range L) (t := fun c ↦ Finset.Ico (c + 1) L)
    (t' := Finset.range L) (s' := fun c' ↦ Finset.range c') fun c c' ↦ by
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega]
  refine Finset.sum_congr rfl fun c' _ ↦ ?_
  rw [Finset.sum_boole]

open scoped Classical in
/-- **A trial's weight at stage `0`** on a state without hardwired cells. -/
theorem termW_le_hw (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c : ℕ)
    (s : HwReg HashOutput HashDomain Mem) (hw : ∀ y, s.2.1.1 y = none) :
    termW e F P t M r0 0 c s ≤ (2 + 2 / (Fintype.card HashOutput : ℝ)) *
        (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0) +
      ((2 * F + 2) / Fintype.card HashOutput +
        2 * F * e.limit / Fintype.card HashOutput / Fintype.card HashOutput) +
      2 * F / Fintype.card HashOutput *
        (codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s +
          ((Finset.Ico (c + 1) e.limit).card : ℝ) *
            (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0)) := by
  have hN : (0 : ℝ) ≤ Fintype.card HashOutput := Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have h1 : (if s.2.1.1 (cell e P t (M, e.shift r0 c)) = none ∧
      s.1.1 (cell e P t (M, e.shift r0 c)) = none then (0 : ℝ) else 1) =
      if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0 := by
    rw [hw]
    by_cases h : s.1.1 (cell e P t (M, e.shift r0 c)) = none <;> simp [h]
  have h3 : (if s.1.1 (cell e P t (M, e.shift r0 c)) = none then 0 else κc e F c) =
      κc e F c * (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0) := by
    by_cases h : s.1.1 (cell e P t (M, e.shift r0 c)) = none <;> simp [h]
  have h2 : (if Recordless e.hash G s.2.2 (cell e P t (M, e.shift r0 c)) then
      2 * (F : ℝ) * codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s else 0) ≤
      2 * (F : ℝ) * codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s := by
    split_ifs
    · exact le_rfl
    · positivity
  have h4 : κc e F c ≤ 2 * F * e.limit / Fintype.card HashOutput := by
    unfold κc
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hN
    have hk : (Finset.Ico (c + 1) e.limit).card ≤ e.limit := by simp
    exact_mod_cast hk
  have h5 := div_le_div_of_nonneg_right (add_le_add (add_le_add h2 (le_refl (2 * (F : ℝ))))
    (le_refl 2)) hN
  have h6 := div_le_div_of_nonneg_right h4 hN
  have h7 : κc e F c * (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0) =
      2 * F / Fintype.card HashOutput * (((Finset.Ico (c + 1) e.limit).card : ℝ) *
        (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0)) := by
    unfold κc
    ring
  have h8 : (2 * (F : ℝ) * codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s +
      2 * F + 2) / Fintype.card HashOutput = (2 * F + 2) / Fintype.card HashOutput +
      2 * F / Fintype.card HashOutput *
        codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s := by ring
  unfold termW gW
  rw [h1, h3, h7]
  linarith

open scoped Classical in
/-- **Stage `0` of a grind on a state without hardwired cells**: per trial, `2 + 2/N` on a
recorded cell, and `(2F · #{recorded cells of the class} + 2F + 2 + 2F · limit/N)/N`. -/
theorem Pt_zero_le (hs : GSep e.hash G) (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (s : HwReg HashOutput HashDomain Mem)
    (hw : ∀ y, s.2.1.1 y = none) :
    Pt e F P t M r0 0 s ≤ ∑ c ∈ Finset.range e.limit,
      ((2 + 2 / (Fintype.card HashOutput : ℝ)) *
          (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0) +
        (2 * F * (Finset.univ.filter fun y ↦ GCell e.hash G y P t ∧ s.1.1 y ≠ none).card +
          (2 * F + 2 + 2 * F * e.limit / Fintype.card HashOutput)) /
            Fintype.card HashOutput) := by
  have hsum : ∑ c ∈ Finset.range e.limit,
      ((codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s : ℝ) +
        ((Finset.Ico (c + 1) e.limit).card : ℝ) *
          (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0)) ≤
      ∑ _c ∈ Finset.range e.limit,
        ((Finset.univ.filter fun y ↦ GCell e.hash G y P t ∧ s.1.1 y ≠ none).card : ℝ) := by
    have h1 := Finset.sum_le_sum fun c (hc : c ∈ Finset.range e.limit) ↦
      codeP_add_le hs hinj hlen hdist P t M r0 (Finset.mem_range.1 hc) s hw
    have h2 : ∑ c ∈ Finset.range e.limit, ((Finset.Ico (c + 1) e.limit).card : ℝ) *
          (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0) =
        ∑ c ∈ Finset.range e.limit, ((((Finset.range c).filter fun c'' ↦
          s.1.1 (cell e P t (M, e.shift r0 c'')) ≠ none).card : ℕ) : ℝ) :=
      sum_card_Ico_mul _ _
    rw [Finset.sum_add_distrib] at h1 ⊢
    linarith
  have hF : (0 : ℝ) ≤ 2 * F / Fintype.card HashOutput := by positivity
  unfold Pt
  rw [← Finset.range_eq_Ico]
  calc ∑ c ∈ Finset.range e.limit, termW e F P t M r0 0 c s
      ≤ ∑ c ∈ Finset.range e.limit, ((2 + 2 / (Fintype.card HashOutput : ℝ)) *
          (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0) +
        ((2 * F + 2) / Fintype.card HashOutput +
          2 * F * e.limit / Fintype.card HashOutput / Fintype.card HashOutput) +
        2 * F / Fintype.card HashOutput *
          (codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s +
            ((Finset.Ico (c + 1) e.limit).card : ℝ) *
              (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0))) :=
        Finset.sum_le_sum fun c _ ↦ termW_le_hw F P t M r0 c s hw
    _ = ∑ c ∈ Finset.range e.limit, ((2 + 2 / (Fintype.card HashOutput : ℝ)) *
          (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0) +
        ((2 * F + 2) / Fintype.card HashOutput +
          2 * F * e.limit / Fintype.card HashOutput / Fintype.card HashOutput)) +
        2 * F / Fintype.card HashOutput * ∑ c ∈ Finset.range e.limit,
          ((codeP e (cell e P t (M, e.shift r0 c)) (Eset e P t M r0 0 c) s : ℝ) +
            ((Finset.Ico (c + 1) e.limit).card : ℝ) *
              (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ c ∈ Finset.range e.limit, ((2 + 2 / (Fintype.card HashOutput : ℝ)) *
          (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0) +
        ((2 * F + 2) / Fintype.card HashOutput +
          2 * F * e.limit / Fintype.card HashOutput / Fintype.card HashOutput)) +
        2 * F / Fintype.card HashOutput * ∑ _c ∈ Finset.range e.limit,
          ((Finset.univ.filter fun y ↦ GCell e.hash G y P t ∧ s.1.1 y ≠ none).card : ℝ) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hF)
    _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun _ _ ↦ ?_
        ring

variable (e) in
open scoped Classical in
/-- **The cost of an answer to `(t, M)` at `P` with codeword partners**, on the database of the
state `s`: per trial, `(2 + 2/N)` times the share of the salts whose cell is recorded, and
`(2F · #{recorded cells of the class} + 2F + 2 + 2F · limit/N)/N`. -/
noncomputable def ansCode [Fintype Salt] (F : ℕ) (P : Par) (q : Tw × Msg)
    (s : HwReg HashOutput HashDomain Mem) : ℝ :=
  e.limit * ((2 + 2 / (Fintype.card HashOutput : ℝ)) *
      (Finset.univ.filter fun r : Salt ↦ s.1.1 (cell e P q.1 (q.2, r)) ≠ none).card /
        Fintype.card Salt +
    (2 * F * (Finset.univ.filter fun y ↦ GCell e.hash G y P q.1 ∧ s.1.1 y ≠ none).card +
      (2 * F + 2 + 2 * F * e.limit / Fintype.card HashOutput)) / Fintype.card HashOutput)

open scoped Classical in
/-- **The averaged stage-`0` potential is the answer's cost** on a state without hardwired
cells. -/
theorem avg_Pt_le [SampleableType Salt] [Fintype Salt] (hs : GSep e.hash G)
    (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen)
    (hbase : ∀ c, Function.Injective fun r0 ↦ e.shift r0 c)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    (F : ℕ) (P : Par) (q : Tw × Msg) (s : HwReg HashOutput HashDomain Mem)
    (hW : s.2.1 = hwEmpty HashOutput HashDomain) :
    ∑ r0, (Pr{let z ← $ᵗ Salt}[z = r0]).toReal * Pt e F P q.1 q.2 r0 0 s ≤
      ansCode e F P q s := by
  have hw : ∀ y, s.2.1.1 y = none := fun y ↦ by
    rw [hW]
    exact hwEmpty_fst_apply y
  have hPr : ∀ r0, (Pr{let z ← $ᵗ Salt}[z = r0]).toReal = (Fintype.card Salt : ℝ)⁻¹ :=
    fun r0 ↦ by
      rw [SampleableType.prEvent_uniformSample_eq_singleton, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
  simp only [hPr]
  have hS : (0 : ℝ) ≤ (Fintype.card Salt : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum fun r0 _ ↦ mul_le_mul_of_nonneg_left
    (Pt_zero_le hs hinj hlen hdist F P q.1 q.2 r0 s hw) hS).trans ?_
  refine (avg_sum_le e.limit
    (fun r0 c ↦ (2 + 2 / (Fintype.card HashOutput : ℝ)) *
      (if s.1.1 (cell e P q.1 (q.2, e.shift r0 c)) ≠ none then 1 else 0) +
      (2 * F * (Finset.univ.filter fun y ↦ GCell e.hash G y P q.1 ∧ s.1.1 y ≠ none).card +
        (2 * F + 2 + 2 * F * e.limit / Fintype.card HashOutput)) / Fintype.card HashOutput)
    (fun r0 c ↦ if s.1.1 (cell e P q.1 (q.2, e.shift r0 c)) ≠ none then 1 else 0)
    (2 + 2 / (Fintype.card HashOutput : ℝ))
    ((2 * F * (Finset.univ.filter fun y ↦ GCell e.hash G y P q.1 ∧ s.1.1 y ≠ none).card +
        (2 * F + 2 + 2 * F * e.limit / Fintype.card HashOutput)) / Fintype.card HashOutput)
    ((Finset.univ.filter fun r : Salt ↦ s.1.1 (cell e P q.1 (q.2, r)) ≠ none).card)
    (by positivity) (fun _ _ ↦ le_rfl) fun c ↦ ?_).trans (le_of_eq ?_)
  · rw [Finset.sum_boole]
    exact_mod_cast Finset.card_le_card_of_injOn (fun r0 ↦ e.shift r0 c)
      (fun r0 hr0 ↦ by simpa using hr0)
      (hbase c).injOn
  · unfold ansCode
    rfl

open scoped Classical in
/-- **The cost of an answer with codeword partners** (`AnsBound`): from a positive semidefinite
state without hardwired cells, the trial reads of an answer to `(t, M)` at `P` add at most the
weight of `ansCode`. -/
theorem totalWeight_answer_le_code [SampleableType Salt] [Fintype Salt] (hs : GSep e.hash G)
    (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (hbase : ∀ c, Function.Injective fun r0 ↦ e.shift r0 c)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    [SampleableType Par] (m₀ : Mem) (P : Par) (q : Tw × Msg) (B : QReg)
    (ρ : Matrix (B × RomReg HashDomain HashOutput Mem) (B × RomReg HashDomain HashOutput Mem) ℂ)
    (hρ : ρ.PosSemidef)
    (hW : QuerySupportedOn (fun x ↦ x.2) {s | s.2.1 = hwEmpty HashOutput HashDomain} ρ) :
    (runtime2 HashOutput HashDomain m₀).totalWeight .instruments (dS e)
        (readProgOf (upd e) (((encTcrSalt romWorld e).answer P q).toQuantumAt
          (mixImpl .answer B))) ρ ≤
      ENNReal.ofReal (∑ s, ansCode e F P q s.2 * (ρ s s).re) := by
  rw [dS_eq_dSΦ]
  have h := step₂_answer_code hs hinj hlen hF hdist m₀ B P q ρ hρ
  refine (le_self_add.trans h).trans ?_
  have hV : ∀ s : HwReg HashOutput HashDomain Mem, 0 ≤ ∑ r0, (Pr{let z ← $ᵗ Salt}[z = r0]).toReal *
      Pt e F P q.1 q.2 r0 0 s := fun s ↦ Finset.sum_nonneg fun r0 _ ↦
    mul_nonneg ENNReal.toReal_nonneg (Pt_nonneg F P q.1 q.2 r0 0 s)
  rw [potential_wPot hV]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun s _ ↦ ?_)
  by_cases h0 : ρ s s = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (avg_Pt_le hs hinj hlen hbase hdist F P q s.2 (hW s s h0).1)
      (Complex.nonneg_iff.1 hρ.diag_nonneg).1

open scoped Classical in
/-- **Every answer costs at most `ansCode`.** -/
theorem ansBound_ansCode [SampleableType Par] [SampleableType Salt] [Fintype Salt]
    (hs : GSep e.hash G) (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (hbase : ∀ c, Function.Injective fun r0 ↦ e.shift r0 c)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c') :
    AnsBound e (ansCode e F) := fun P q B ρ hρ hW ↦
  totalWeight_answer_le_code hs hinj hlen hF hbase hdist mem0 P q B ρ hρ hW

variable (e) in
/-- **The constant of an answer's cost with codeword partners**:
`limit · (2F + 2 + ε)/N` with `ε = 2F · limit/N`. -/
noncomputable def c0C (F : ℕ) : ℝ :=
  e.limit * ((2 * F + 2 + 2 * F * e.limit / Fintype.card HashOutput) / Fintype.card HashOutput)

theorem c0C_nonneg (F : ℕ) : 0 ≤ c0C e F := by
  unfold c0C
  positivity

/-- The arithmetic of an answer's cost with codeword partners. -/
theorem ansCode_arith {L A a S N F c g C : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hA : 0 ≤ A) (hF : 0 ≤ F) (ha : a ≤ c) (hg : g ≤ c) :
    L * (A * a / S + (2 * F * g + C) / N) ≤ L * (A / S + 2 * F / N) * c + L * (C / N) := by
  have h1 : A * a / S ≤ A / S * c := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left ha (div_nonneg hA hS)
  have h2 : (2 * F * g + C) / N ≤ 2 * F / N * c + C / N := by
    rw [div_mul_eq_mul_div, ← add_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hN
  calc L * (A * a / S + (2 * F * g + C) / N) ≤ L * (A / S * c + (2 * F / N * c + C / N)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hL
    _ = L * (A / S + 2 * F / N) * c + L * (C / N) := by ring

open scoped Classical in
/-- **The cost of an answer with codeword partners is linear in the recorded cells of its
class**: `ansCode ≤ lamS · cntY + c0C`. -/
theorem ansCode_le_cntY [Fintype Salt] (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen) (F : ℕ) (P : Par) (q : Tw × Msg)
    (s : HwReg HashOutput HashDomain Mem) :
    ansCode e F P q s ≤ lamS e F * cntY (Kset e P q.1) s + c0C e F := by
  have ha : ((Finset.univ.filter fun r : Salt ↦ s.1.1 (cell e P q.1 (q.2, r)) ≠ none).card : ℝ)
      ≤ cntY (Kset e P q.1) s :=
    Nat.cast_le.mpr (card_filter_le_of_inj _ _ (fun r ↦ cell e P q.1 (q.2, r))
      (cell_injective hinj hlen P q.1 q.2) fun r hr ↦ ⟨gCell_cell hlen P q.1 (q.2, r), hr⟩)
  have hg : ((Finset.univ.filter fun y ↦ GCell e.hash G y P q.1 ∧ s.1.1 y ≠ none).card : ℝ)
      ≤ cntY (Kset e P q.1) s :=
    Nat.cast_le.mpr (card_filter_le_of_inj _ _ id Function.injective_id fun _ hy ↦ hy)
  unfold ansCode lamS c0C
  exact ansCode_arith (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) (Nat.cast_nonneg _) ha hg

end final

end Quantum.StdModel.Qrom.EncSalt.Code

end
