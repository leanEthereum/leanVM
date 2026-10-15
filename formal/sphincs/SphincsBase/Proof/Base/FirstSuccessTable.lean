import SphincsBase.Proof.Base.Prelude
import SphincsBase.Proof.Base.UniformTableConditioning
namespace SphincsBase.Concrete.FirstSuccessTable

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

/-- The uniform table over `rows`, or the full table if a row is empty. An empty row has probability zero, so the fallback only makes the definition total. -/
noncomputable def constrained [Nonempty Answer] {n : Nat} (rows : Fin n → Finset Answer) : PMF (Fin n → Answer) :=
  if hrows : ∀ coordinate, (rows coordinate).Nonempty then uniformTable rows hrows else full n

theorem full_restrict_mass [Nonempty Answer] {n : Nat} (rows : Fin n → Finset Answer) (table : Fin n → Answer) :
    (if ∀ coordinate, table coordinate ∈ rows coordinate then full n table else 0) =
      ((∏ coordinate, (rows coordinate).card : Nat) : ENNReal) /
        ((∏ _coordinate : Fin n, Fintype.card Answer : Nat) : ENNReal) * constrained rows table := by
  by_cases hrows : ∀ coordinate, (rows coordinate).Nonempty
  · have h := uniformTable_restrict (fun _ : Fin n => Finset.univ) rows
      (fun _ => Finset.univ_nonempty) hrows (fun _ => Finset.subset_univ _) table
    by_cases ht : ∀ coordinate, table coordinate ∈ rows coordinate <;>
      simpa only [full, constrained, dif_pos hrows, Finset.card_univ, ht, if_true, if_false] using h
  · push Not at hrows
    obtain ⟨coordinate, hempty⟩ := hrows
    have hzero : (∏ coordinate, (rows coordinate).card : Nat) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ coordinate) (by rw [hempty, Finset.card_empty])
    have ht : ¬∀ coordinate, table coordinate ∈ rows coordinate := fun h => by
      simpa only [hempty, Finset.notMem_empty] using h coordinate
    simp only [ht, if_false, hzero, Nat.cast_zero, ENNReal.zero_div, zero_mul]

noncomputable def successMass (decode : Answer → Option Value) {n : Nat} (index : Fin n) (value : Value) : ENNReal :=
  ((∏ coordinate, (allowed decode index value coordinate).card : Nat) : ENNReal) /
    ((∏ _coordinate : Fin n, Fintype.card Answer : Nat) : ENNReal)

theorem full_success_mass [Nonempty Answer] (decode : Answer → Option Value) {n : Nat}
    (index : Fin n) (value : Value) (table : Fin n → Answer) :
    (if select decode table = some (index, value) then full n table else 0) =
      successMass decode index value * constrained (allowed decode index value) table := by
  simp only [select_some_iff_allowed]
  exact full_restrict_mass _ table

theorem probEvent_full_success [Nonempty Answer] (decode : Answer → Option Value) {n : Nat}
    (index : Fin n) (value : Value) :
    Pr[fun table => select decode table = some (index, value) | full (Answer := Answer) n] =
      successMass decode index value := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    full_success_mass decode index value, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem full_exhaustion_mass [Nonempty Answer] (decode : Answer → Option Value) (n : Nat)
    (table : Fin n → Answer) :
    (if select decode table = none then full n table else 0) =
      ((invalid decode).card / (Fintype.card Answer : ENNReal)) ^ n *
        constrained (fun _ : Fin n => invalid decode) table := by
  have h := full_restrict_mass (fun _ : Fin n => invalid decode) table
  have hmass :
      (((∏ _coordinate : Fin n, (invalid decode).card : Nat) : ENNReal) /
        ((∏ _coordinate : Fin n, Fintype.card Answer : Nat) : ENNReal)) =
          ((invalid decode).card / (Fintype.card Answer : ENNReal)) ^ n := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
      div_eq_mul_inv, ENNReal.inv_pow, mul_pow]
  rw [hmass] at h
  simp only [mem_invalid] at h
  simpa only [select_none_iff] using h

theorem probEvent_full_exhaustion [Nonempty Answer] (decode : Answer → Option Value) (n : Nat) :
    Pr[fun table => select decode table = none | full (Answer := Answer) n] =
      ((invalid decode).card / (Fintype.card Answer : ENNReal)) ^ n := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    full_exhaustion_mass decode n, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

noncomputable def selected [Nonempty Answer] (decode : Answer → Option Value) (n : Nat) :
    PMF (Option (Fin n × Value)) := (full n).map (select decode)

noncomputable def afterSelect [Nonempty Answer] (decode : Answer → Option Value) (n : Nat) :
    Option (Fin n × Value) → PMF (Fin n → Answer)
  | none => constrained (fun _ => invalid decode)
  | some (index, value) => constrained (allowed decode index value)

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
    (result : Option (Fin n × Value)) (table : Fin n → Answer) :
    selected decode n result * afterSelect decode n result table =
      if select decode table = result then full n table else 0 := by
  cases result with
  | none =>
      rw [selected_apply, probEvent_full_exhaustion decode n, afterSelect]
      exact (full_exhaustion_mass decode n table).symm
  | some result =>
      obtain ⟨index, value⟩ := result
      rw [selected_apply, probEvent_full_success decode index value, afterSelect]
      exact (full_success_mass decode index value table).symm

end SphincsBase.Concrete.FirstSuccessTable
