import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.UniformTableConditioning
namespace SphincsSecurity.Concrete.FirstSuccessTable

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Answer Value : Type}

def select (decode : Answer → Option Value) : {n : Nat} → (Fin n → Answer) → Option (Fin n × Value)
  | 0, _ => none
  | n + 1, table =>
      match decode (table 0) with
      | some value => some (0, value)
      | none => (select decode (fun i : Fin n => table i.succ)).map (fun result => (result.1.succ, result.2))

theorem select_none_iff (decode : Answer → Option Value) {n : Nat} (table : Fin n → Answer) :
    select decode table = none ↔ ∀ i, decode (table i) = none := by
  induction n with
  | zero => simp [select]
  | succ n ih =>
      rw [select, Fin.forall_fin_succ]
      cases hzero : decode (table 0) <;> simp [ih]

theorem select_some_iff (decode : Answer → Option Value) {n : Nat} (table : Fin n → Answer)
    (index : Fin n) (value : Value) :
    select decode table = some (index, value) ↔
      decode (table index) = some value ∧ ∀ i, i < index → decode (table i) = none := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · rw [select]
        cases hzero : decode (table 0) with
        | none =>
            simp only [Option.map_eq_some_iff, Prod.mk.injEq]
            constructor
            · rintro ⟨⟨i, result⟩, _, hi, _⟩
              exact (Fin.succ_ne_zero i hi).elim
            · simp
        | some result => simp
      · rw [select]
        cases hzero : decode (table 0) with
        | none =>
            simp only [Option.map_eq_some_iff, Prod.mk.injEq, Fin.succ_inj]
            constructor
            · rintro ⟨⟨i, result⟩, hselected, hi, hv⟩
              dsimp only at hi hv
              subst i
              subst result
              obtain ⟨hvalue, hbefore⟩ := (ih _ _).mp hselected
              refine ⟨hvalue, ?_⟩
              intro i
              refine Fin.cases (fun _ => hzero) (fun i hi => hbefore i (by simpa using hi)) i
            · rintro ⟨hvalue, hbefore⟩
              refine ⟨(index, value), (ih _ _).mpr ⟨hvalue, ?_⟩, rfl, rfl⟩
              intro i hi
              exact hbefore i.succ (by simpa using hi)
        | some result =>
            constructor
            · intro h
              have hindex := congrArg (fun result => result.map (fun pair => pair.1.val)) h
              simp at hindex
            · rintro ⟨_, hbefore⟩
              have h := hbefore 0 (by simp)
              simp [hzero] at h

variable [Fintype Answer] [DecidableEq Answer]

noncomputable def invalid (decode : Answer → Option Value) : Finset Answer :=
  Finset.univ.filter (fun answer => decode answer = none)

noncomputable def fiber (decode : Answer → Option Value) (value : Value) : Finset Answer :=
  Finset.univ.filter (fun answer => decode answer = some value)

omit [DecidableEq Answer] in
@[simp] theorem mem_invalid (decode : Answer → Option Value) (answer : Answer) :
    answer ∈ invalid decode ↔ decode answer = none := by simp [invalid]

omit [DecidableEq Answer] in
@[simp] theorem mem_fiber (decode : Answer → Option Value) (value : Value) (answer : Answer) :
    answer ∈ fiber decode value ↔ decode answer = some value := by simp [fiber]

noncomputable def allowed (decode : Answer → Option Value) {n : Nat} (index : Fin n) (value : Value)
    (coordinate : Fin n) : Finset Answer :=
  if coordinate < index then invalid decode else if coordinate = index then fiber decode value else Finset.univ

omit [DecidableEq Answer] in
theorem allowed_nonempty (decode : Answer → Option Value) {n : Nat} (index : Fin n) (value : Value)
    (hinvalid : (invalid decode).Nonempty) (hvalue : (fiber decode value).Nonempty) :
    ∀ coordinate, (allowed decode index value coordinate).Nonempty := by
  intro coordinate
  unfold allowed
  split_ifs
  · exact hinvalid
  · exact hvalue
  · exact Finset.univ_nonempty_iff.mpr ⟨hinvalid.choose⟩

omit [DecidableEq Answer] in
theorem select_some_iff_allowed (decode : Answer → Option Value) {n : Nat} (table : Fin n → Answer)
    (index : Fin n) (value : Value) :
    select decode table = some (index, value) ↔
      ∀ coordinate, table coordinate ∈ allowed decode index value coordinate := by
  rw [select_some_iff]
  constructor
  · rintro ⟨hvalue, hbefore⟩ coordinate
    unfold allowed
    split_ifs with hlt heq
    · exact (mem_invalid _ _).mpr (hbefore coordinate hlt)
    · subst coordinate
      exact (mem_fiber _ _ _).mpr hvalue
    · exact Finset.mem_univ _
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [allowed] using h index
    · intro coordinate hlt
      simpa [allowed, hlt] using h coordinate

noncomputable def full (n : Nat) [Nonempty Answer] : PMF (Fin n → Answer) :=
  uniformTable (fun _ => Finset.univ) (fun _ => Finset.univ_nonempty)

omit [DecidableEq Answer] in
theorem full_eq_uniform (n : Nat) [Nonempty Answer] :
    full (Answer := Answer) n = PMF.uniformOfFintype (Fin n → Answer) := by
  unfold full uniformTable PMF.uniformOfFintype
  congr 1

noncomputable def conditional (decode : Answer → Option Value) {n : Nat} (index : Fin n) (value : Value)
    (hinvalid : (invalid decode).Nonempty) (hvalue : (fiber decode value).Nonempty) : PMF (Fin n → Answer) :=
  uniformTable (allowed decode index value) (allowed_nonempty decode index value hinvalid hvalue)

noncomputable def successMass (decode : Answer → Option Value) {n : Nat} (index : Fin n) (value : Value) : ENNReal :=
  ((∏ coordinate, (allowed decode index value coordinate).card : Nat) : ENNReal) /
    ((∏ _coordinate : Fin n, Fintype.card Answer : Nat) : ENNReal)

theorem full_success_mass [Nonempty Answer] (decode : Answer → Option Value) {n : Nat}
    (index : Fin n) (value : Value) (hinvalid : (invalid decode).Nonempty)
    (hvalue : (fiber decode value).Nonempty) (table : Fin n → Answer) :
    (if select decode table = some (index, value) then full n table else 0) =
      successMass decode index value * conditional decode index value hinvalid hvalue table := by
  simp only [select_some_iff_allowed]
  have h := uniformTable_restrict (fun _ : Fin n => Finset.univ) (allowed decode index value)
      (fun _ => Finset.univ_nonempty) (allowed_nonempty decode index value hinvalid hvalue)
      (fun _ => Finset.subset_univ _) table
  by_cases ht : ∀ coordinate, table coordinate ∈ allowed decode index value coordinate <;>
    simpa only [full, successMass, conditional, Finset.card_univ, ht, if_true, if_false] using h

theorem probEvent_full_success [Nonempty Answer] (decode : Answer → Option Value) {n : Nat}
    (index : Fin n) (value : Value) (hinvalid : (invalid decode).Nonempty)
    (hvalue : (fiber decode value).Nonempty) :
    Pr[fun table => select decode table = some (index, value) | full (Answer := Answer) n] =
      successMass decode index value := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    full_success_mass decode index value hinvalid hvalue, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

noncomputable def exhausted (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (invalid decode).Nonempty) : PMF (Fin n → Answer) :=
  uniformTable (fun _ => invalid decode) (fun _ => hinvalid)

theorem full_exhaustion_mass [Nonempty Answer] (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (invalid decode).Nonempty) (table : Fin n → Answer) :
    (if select decode table = none then full n table else 0) =
      ((invalid decode).card / (Fintype.card Answer : ENNReal)) ^ n * exhausted decode n hinvalid table := by
  have h := uniformTable_restrict (fun _ : Fin n => Finset.univ) (fun _ => invalid decode)
    (fun _ => Finset.univ_nonempty) (fun _ => hinvalid) (fun _ => Finset.subset_univ _) table
  have hmass :
      (((∏ _coordinate : Fin n, (invalid decode).card : Nat) : ENNReal) /
        ((∏ _coordinate : Fin n, (Finset.univ : Finset Answer).card : Nat) : ENNReal)) =
          ((invalid decode).card / (Fintype.card Answer : ENNReal)) ^ n := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
      div_eq_mul_inv, ENNReal.inv_pow, mul_pow]
  rw [hmass] at h
  simp only [mem_invalid] at h
  simp only [select_none_iff]
  by_cases ht : ∀ coordinate, decode (table coordinate) = none <;>
    simpa only [full, exhausted, ht, if_true, if_false] using h

theorem probEvent_full_exhaustion [Nonempty Answer] (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (invalid decode).Nonempty) :
    Pr[fun table => select decode table = none | full (Answer := Answer) n] =
      ((invalid decode).card / (Fintype.card Answer : ENNReal)) ^ n := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    full_exhaustion_mass decode n hinvalid, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

noncomputable def selected [Nonempty Answer] (decode : Answer → Option Value) (n : Nat) :
    PMF (Option (Fin n × Value)) := (full n).map (select decode)

noncomputable def afterSelect [Nonempty Answer] (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (invalid decode).Nonempty) : Option (Fin n × Value) → PMF (Fin n → Answer)
  | none => exhausted decode n hinvalid
  | some (index, value) =>
      if hvalue : (fiber decode value).Nonempty then conditional decode index value hinvalid hvalue else full n

omit [DecidableEq Answer] in
theorem selected_apply [Nonempty Answer] (decode : Answer → Option Value) (n : Nat)
    (result : Option (Fin n × Value)) :
    selected decode n result = Pr[fun table => select decode table = result | full (Answer := Answer) n] := by
  simp only [selected, PMF.map_apply, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  apply tsum_congr
  intro table
  by_cases h : select decode table = result
  · subst result
    simp
  · simp only [h, Ne.symm h, if_false]

theorem selected_mul_afterSelect [Nonempty Answer] (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (invalid decode).Nonempty) (result : Option (Fin n × Value)) (table : Fin n → Answer) :
    selected decode n result * afterSelect decode n hinvalid result table =
      if select decode table = result then full n table else 0 := by
  cases result with
  | none =>
      rw [selected_apply, probEvent_full_exhaustion decode n hinvalid, afterSelect]
      exact (full_exhaustion_mass decode n hinvalid table).symm
  | some result =>
      obtain ⟨index, value⟩ := result
      by_cases hvalue : (fiber decode value).Nonempty
      · rw [selected_apply, probEvent_full_success decode index value hinvalid hvalue,
          afterSelect, dif_pos hvalue]
        exact (full_success_mass decode index value hinvalid hvalue table).symm
      · have hselected : ∀ table : Fin n → Answer, select decode table ≠ some (index, value) := by
          intro table h
          exact hvalue ⟨table index, (mem_fiber _ _ _).mpr ((select_some_iff _ _ _ _).mp h).1⟩
        simp only [selected_apply, probEvent_eq_tsum_ite, hselected, if_false, tsum_zero, zero_mul]

end SphincsSecurity.Concrete.FirstSuccessTable
