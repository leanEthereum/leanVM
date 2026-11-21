module

public import Quantum.Sponge.Oracle.Hardwired.Classical

@[expose] public section

/-!
# The decompressed table is uniform off the hardwired cells

In the decompressed basis (conjugation by `compressReg`), every port of the hardwired runtime is
controlled on the database triple `D` except a program call, which resets its cell: a sponge port
is the table oracle of `D` (it keeps `D`), a read is diagonal in `D`, a program call changes `D`
only at its cell (the cell becomes the uniform superposition), and a port acting as the identity on
the databases (a record port) keeps `D`. The run starts from the uniform superposition over the
total tables. So an event `F` on `D` that does not look at the cells hardwired in a static `W`,
along a run whose program calls only program cells of `W`, has weight at most its uniform
probability times the trace.

* **Runs commuting with a projector** (`eventWeight_le_of_commute`): if every port a run calls
  commutes with `Q` (as `conj Q` on the runtime register), the weight of `1 ⊗ Q` at the end is at
  most that at the start. The ports that are never called are replaced by failing ones
  (`run_branch_apply_eq_of_forallQueries`), and the run then commutes with `conj Q`
  (`simulation`).
* **The decompressed event projector** `hwDecProj E = C diag(1_E) C`, `C = compressReg`.
* **The ports commute with it** (`hwPort_commute_hwDecProj`, `hwReadKraus_commute_hwDecProj`,
  `hwProgKraus_commute_hwDecProj`, `clsKraus_commute_hwDecProj`): for `E = {s | F s.1}`, any `F`
  for sponge and read ports and for classical ports acting as the identity on the databases
  (`clsKraus_one_commute_hwDecProj`), and `F` determined off `W` (`OffHw W F`) for a program port
  of a cell hardwired in `W` (`HwProg.CellIn`).
* **The initial weight** (`trace_conj_hwDecProj_basis`): from the empty databases, the weight of
  `{s | F s.1}` is `#{t | F (ofFunDbs t)} / #tables` times the trace.
* **The invariant** (`eventWeight_hwDecProj_le`): along any run of the hardwired runtime extended
  by ports commuting with the projector (record ports), whose calls are all `HwPortIn W`, the
  weight of `{s | F s.1}` is at most `tr ρ · #{t | F (ofFunDbs t)} / #tables`.
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Sponge

open Quantum QuantumRuntime

/-! ## Runs commuting with a projector -/

section commute

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **The weight of `1 ⊗ Q` does not grow along a run whose called ports commute with `Q`.** If
every port `i` with `good i` commutes with `conj Q` on the runtime register, and every call of
the run of `x` from `ρ` is of such a port (`ForallQueries` of a condition implying `good`), then
the weight of `1 ⊗ Q` over the leaves of the run is at most that of `ρ`. -/
theorem eventWeight_le_of_commute (R : QuantumRuntime spec) (Q : Matrix R.D R.D ℂ)
    (good : spec.Port → Prop)
    (hc : ∀ i, good i → ∀ r, (R.step i).branch r ∘ₗ (MatrixMap.conj Q).amplifyLeft (spec.In i) =
      (MatrixMap.conj Q).amplifyLeft (spec.Out i) ∘ₗ (R.step i).branch r)
    {P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    (hP : ∀ i E σ, P i E σ → good i) (x : QuantumComp L spec Ω A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (hx : R.ForallQueries I P x ρ) :
    R.eventWeight I Q x ρ ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ).trace.re := by
  classical
  let s' : ∀ i, SubInstrument (spec.In i × R.D) (spec.Out i × R.D) (spec.Result i) :=
    fun i ↦ if good i then R.step i else SubInstrument.fail
  have hs' : ∀ i, good i → s' i = R.step i := fun i hi ↦ ite_eq_left hi
  have hsn : ∀ i, ¬good i → s' i = SubInstrument.fail := fun i hi ↦ ite_eq_right hi
  let R' : QuantumRuntime spec := ⟨R.D, R.init, s'⟩
  have hrun : ∀ p, (R.run I x).branch p ρ = (R'.run I x).branch p ρ := fun p ↦
    run_branch_apply_eq_of_forallQueries (D := R.D) (σ₁ := R.init) (σ₂ := R.init)
      (s₁ := R.step) (s₂ := s') I (fun i E σ hσ r ↦ by rw [hs' i (hP i E σ hσ)]) hx p
  have hcomm : ∀ i r, (R'.step i).branch r ∘ₗ (MatrixMap.conj Q).amplifyLeft (spec.In i) =
      (MatrixMap.conj Q).amplifyLeft (spec.Out i) ∘ₗ (R'.step i).branch r := by
    intro i r
    change (s' i).branch r ∘ₗ _ = _ ∘ₗ (s' i).branch r
    by_cases hi : good i
    · rw [hs' i hi]
      exact hc i hi r
    · rw [hsn i hi]
      change (0 : MatrixMap _ _) ∘ₗ _ = _ ∘ₗ (0 : MatrixMap _ _)
      rw [LinearMap.zero_comp, LinearMap.comp_zero]
  have hρQ : (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ).PosSemidef := by
    rw [MatrixMap.conj_apply]
    exact hρ.mul_mul_conjTranspose_same _
  unfold QuantumRuntime.eventWeight
  calc ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ Q)
        ((R.run I x).branch p ρ)).trace.re
      = ∑' p, ENNReal.ofReal ((R'.run I x).branch p
          (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ)).trace.re := by
        refine tsum_congr fun p ↦ ?_
        have h := LinearMap.congr_fun
          (simulation (R₁ := R') (R₂ := R') (V := MatrixMap.conj Q) I hcomm x p) ρ
        rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_conj,
          MatrixMap.amplifyLeft_conj] at h
        rw [h, ← hrun p]
    _ ≤ _ := (R'.run I x).isCPTNIFamily.tsum_ofReal_trace_re_le hρQ

/-- A step branch given by a Kraus operator commuting with `1 ⊗ Q` commutes with `conj Q`. -/
theorem branch_comm_of_commute {O J S : Type} [Fintype O] [DecidableEq O] [Fintype J]
    [DecidableEq J] [Fintype S] [DecidableEq S] {Φ : MatrixMap (J × S) (O × S)}
    {K : Matrix (O × S) (J × S) ℂ} (hΦ : Φ = MatrixMap.conj K) {Q : Matrix S S ℂ}
    (hK : ((1 : Matrix O O ℂ) ⊗ₖ Q) * K = K * ((1 : Matrix J J ℂ) ⊗ₖ Q)) :
    Φ ∘ₗ (MatrixMap.conj Q).amplifyLeft J = (MatrixMap.conj Q).amplifyLeft O ∘ₗ Φ := by
  rw [hΦ, MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
    ← MatrixMap.conj_mul, hK]

end commute

/-! ## The decompressed event projector -/

section proj

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] {M : Type} [Fintype M] [DecidableEq M]

/-- **The projector on a decompressed event** `E`, in the compressed basis: `C diag(1_E) C` with
`C = compressReg`. -/
noncomputable def hwDecProj (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)] :
    Matrix (HwReg X Z M) (HwReg X Z M) ℂ :=
  compressReg X Z M * diagonal (fun s ↦ if s ∈ E then 1 else 0) * compressReg X Z M

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] in
theorem one_kronecker_diagonal_ind {n : Type} [Fintype n] [DecidableEq n]
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)] :
    (1 : Matrix n n ℂ) ⊗ₖ diagonal (fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0) =
      diagonal fun a : n × HwReg X Z M ↦ if a.2 ∈ E then (1 : ℂ) else 0 := by
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  simp only [one_mul]

/-- **Commuting with the decompressed projector.** An operator whose decompressed form has
nonzero entries only between registers both in `E` or both out of `E` commutes with
`1 ⊗ hwDecProj E`. -/
theorem commute_hwDecProj {O J : Type} [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    (K : Matrix (O × HwReg X Z M) (J × HwReg X Z M) ℂ)
    (h : ∀ a b, (((1 : Matrix O O ℂ) ⊗ₖ compressReg X Z M) * K *
      ((1 : Matrix J J ℂ) ⊗ₖ compressReg X Z M)) a b ≠ 0 → (a.2 ∈ E ↔ b.2 ∈ E)) :
    ((1 : Matrix O O ℂ) ⊗ₖ hwDecProj E) * K = K * ((1 : Matrix J J ℂ) ⊗ₖ hwDecProj E) := by
  set CO := (1 : Matrix O O ℂ) ⊗ₖ compressReg X Z M
  set CJ := (1 : Matrix J J ℂ) ⊗ₖ compressReg X Z M
  set PO := (1 : Matrix O O ℂ) ⊗ₖ
    diagonal (fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0)
  set PJ := (1 : Matrix J J ℂ) ⊗ₖ
    diagonal (fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0)
  have hO : CO * CO = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  have hJ : CJ * CJ = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  have hQO : (1 : Matrix O O ℂ) ⊗ₖ hwDecProj E = CO * PO * CO := by
    rw [hwDecProj, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  have hQJ : (1 : Matrix J J ℂ) ⊗ₖ hwDecProj E = CJ * PJ * CJ := by
    rw [hwDecProj, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  have hP : PO * (CO * K * CJ) = (CO * K * CJ) * PJ := by
    simp only [PO, PJ, one_kronecker_diagonal_ind]
    ext a b
    rw [diagonal_mul, mul_diagonal]
    by_cases hab : (CO * K * CJ) a b = 0
    · rw [hab, mul_zero, zero_mul]
    · have hiff := h a b hab
      by_cases ha : a.2 ∈ E
      · simp [ha, hiff.mp ha]
      · have hb : b.2 ∉ E := fun hb ↦ ha (hiff.mpr hb)
        simp [ha, hb]
  rw [hQO, hQJ]
  calc CO * PO * CO * K = CO * (PO * (CO * K * CJ)) * CJ := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = CO * ((CO * K * CJ) * PJ) * CJ := by rw [hP]
    _ = K * (CJ * PJ * CJ) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc CO CO, hO, Matrix.one_mul]

/-! ### Sponge ports -/

theorem one_kronecker_compressReg_hwPort {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y]
    (read : HwReg X Z M → A → Y) :
    ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) * hwPort read *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) = tableOracle read := by
  have hCC : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  rw [hwPort, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hCC, Matrix.one_mul, Matrix.mul_assoc,
    hCC, Matrix.mul_one]

/-- **A sponge port commutes with every decompressed event projector**: in the decompressed basis
it is the table oracle, which keeps the register. -/
theorem hwPort_commute_hwDecProj {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    (read : HwReg X Z M → A → Y) :
    ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ hwDecProj E) * hwPort read =
      hwPort read * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ hwDecProj E) := by
  refine commute_hwDecProj E _ fun a b hab ↦ ?_
  rw [one_kronecker_compressReg_hwPort, tableOracle_apply] at hab
  split_ifs at hab with he
  · rw [he]
    rfl
  · exact absurd rfl hab

/-! ### Classical ports -/

omit [Fintype X] [Fintype Z] [AddCommGroup X] [AddCommGroup Z] [DecidableEq M] in
theorem kron_one_mul_clsKraus_dec {T B : Type} [Fintype T] [Fintype B] [DecidableEq B]
    (V : Matrix T T ℂ) (p : B → Prop) [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ) :
    (V ⊗ₖ (1 : Matrix B B ℂ)) * clsKraus p φ R = clsKraus p φ fun b ↦ V * R b := by
  ext ⟨s', b'⟩ ⟨s, b⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kroneckerMap_apply, Matrix.one_apply, clsKraus_apply]
  have key : ∀ t, ∑ c, V s' t * (if b' = c then (1 : ℂ) else 0) *
      (if p b ∧ c = φ b then R b t s else 0) = if p b ∧ b' = φ b then V s' t * R b t s else 0 := by
    intro t
    rw [Finset.sum_eq_single b' (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp)]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl fun t _ ↦ key t]
  split_ifs <;> simp [Matrix.mul_apply]

omit [Fintype X] [Fintype Z] [AddCommGroup X] [AddCommGroup Z] [DecidableEq M] in
theorem clsKraus_mul_kron_one_dec {T B : Type} [Fintype T] [Fintype B] [DecidableEq B]
    (V : Matrix T T ℂ) (p : B → Prop) [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ) :
    clsKraus p φ R * (V ⊗ₖ (1 : Matrix B B ℂ)) = clsKraus p φ fun b ↦ R b * V := by
  ext ⟨s', b'⟩ ⟨s, b⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kroneckerMap_apply, Matrix.one_apply, clsKraus_apply]
  have key : ∀ t, ∑ c, (if p c ∧ b' = φ c then R c s' t else 0) * (V t s *
      (if c = b then (1 : ℂ) else 0)) = if p b ∧ b' = φ b then R b s' t * V t s else 0 := by
    intro t
    rw [Finset.sum_eq_single b (fun c _ hc ↦ by simp [hc]) (by simp)]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl fun t _ ↦ key t]
  split_ifs <;> simp [Matrix.mul_apply]

/-- **A classical Kraus operator commutes with the projector of an event on the databases** when
its decompressed database operators keep the event. -/
theorem clsKraus_commute_hwDecProj {n : Type} [Fintype n] [DecidableEq n]
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)] (F : DbReg X Z → Prop)
    (hE : ∀ s, s ∈ E ↔ F s.1) (p : Hw X Z × M → Prop) [DecidablePred p]
    (φ : Hw X Z × M → Hw X Z × M) (R : Hw X Z × M → Matrix (DbReg X Z) (DbReg X Z) ℂ)
    (hR : ∀ b D' D, (compressDbs X Z * R b * compressDbs X Z) D' D ≠ 0 → (F D' ↔ F D)) :
    ((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E) * ((1 : Matrix n n ℂ) ⊗ₖ clsKraus p φ R) =
      ((1 : Matrix n n ℂ) ⊗ₖ clsKraus p φ R) * ((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E) := by
  refine commute_hwDecProj E _ fun a b hab ↦ ?_
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, compressReg,
    kron_one_mul_clsKraus_dec, clsKraus_mul_kron_one_dec] at hab
  have h := (one_kronecker_ne_zero hab).2
  rw [clsKraus_apply] at h
  split_ifs at h with hc
  · rw [hE, hE]
    exact hR _ _ _ h
  · exact absurd rfl h

/-- A classical Kraus operator acting as the identity on the databases (a record port) commutes
with the projector of every event on the databases. -/
theorem clsKraus_one_commute_hwDecProj {n : Type} [Fintype n] [DecidableEq n]
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)] (F : DbReg X Z → Prop)
    (hE : ∀ s, s ∈ E ↔ F s.1) (p : Hw X Z × M → Prop) [DecidablePred p]
    (φ : Hw X Z × M → Hw X Z × M) :
    ((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E) *
        ((1 : Matrix n n ℂ) ⊗ₖ clsKraus p φ fun _ ↦ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) =
      ((1 : Matrix n n ℂ) ⊗ₖ clsKraus p φ fun _ ↦ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) *
        ((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E) := by
  refine clsKraus_commute_hwDecProj E F hE p φ _ fun _ D' D h ↦ ?_
  rw [Matrix.mul_one, compressDbs_mul_self] at h
  by_cases he : D' = D
  · rw [he]
  · exact absurd (Matrix.one_apply_ne he) h

end proj

/-! ## Database operators in the decompressed basis -/

section cells

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]

/-- The nonzero entries of `N` keep every cell outside `S`. -/
def CellsKeep (S : A → Prop) (N : Matrix (Database A Y) (Database A Y) ℂ) : Prop :=
  ∀ D' D, N D' D ≠ 0 → ∀ a, ¬S a → D' a = D a

omit [Fintype Y] in
/-- The compressed discard of cell `a` as a pi-tensor product: `|⊥⟩⟨o|` at `a`. -/
theorem cellDiscard_eq_piKron_dec (a : A) (o : Option Y) :
    cellDiscard (Y := Y) a o =
      piKron (Function.update (fun _ ↦ (1 : Matrix (Option Y) (Option Y) ℂ)) a
        (Matrix.of fun u u' ↦ if u = none ∧ u' = o then 1 else 0)) := by
  ext D' D
  rw [piKron_apply, Fintype.prod_eq_mul_prod_compl a, Function.update_self]
  have hrest : ∏ x ∈ ({a}ᶜ : Finset A), Function.update
      (fun _ ↦ (1 : Matrix (Option Y) (Option Y) ℂ)) a
        (Matrix.of fun u u' ↦ if u = none ∧ u' = o then 1 else 0) x (D' x) (D x) =
      if ∀ x ∈ ({a}ᶜ : Finset A), D' x = D x then 1 else 0 := by
    by_cases h : ∀ x ∈ ({a}ᶜ : Finset A), D' x = D x
    · simp only [eq_true h, ↓reduceIte]
      refine Finset.prod_eq_one fun x hx ↦ ?_
      rw [Function.update_of_ne (by simpa using hx), h x hx, Matrix.one_apply_eq]
    · simp only [eq_false h, ↓reduceIte]
      simp only [not_forall] at h
      obtain ⟨x, hx, hne⟩ := h
      exact Finset.prod_eq_zero hx (by
        rw [Function.update_of_ne (by simpa using hx), Matrix.one_apply_ne hne])
  rw [hrest, cellDiscard, of_apply, of_apply]
  by_cases h : D a = o ∧ D' = Function.update D a none
  · obtain ⟨h1, rfl⟩ := h
    simp [h1]
    exact fun x hx ↦ Function.update_of_ne hx _ _
  · simp only [h, ↓reduceIte]
    by_cases h1 : D' a = none ∧ D a = o
    · have h2 : ¬ ∀ x ∈ ({a}ᶜ : Finset A), D' x = D x := fun h2 ↦ h ⟨h1.2, funext fun x ↦ by
        by_cases hx : x = a
        · subst hx
          rw [Function.update_self, h1.1]
        · rw [Function.update_of_ne hx, h2 x (by simpa using hx)]⟩
      simp only [eq_false h2, ↓reduceIte, mul_zero]
    · simp only [h1, ↓reduceIte, zero_mul]

variable [Nonempty Y]

/-- Every cell is kept by the identity. -/
theorem cellsKeep_one (S : A → Prop) :
    CellsKeep S (compressAll A Y * (1 : Matrix (Database A Y) (Database A Y) ℂ) *
      compressAll A Y) := by
  intro D' D h a _
  rw [Matrix.mul_one, compressAll_mul_self] at h
  by_cases he : D' = D
  · rw [he]
  · exact absurd (Matrix.one_apply_ne he) h

/-- **A read in the decompressed basis is diagonal**: the projector on the databases whose cell
`a`, overwritten by the hardwired value, is `o`. -/
theorem compressAll_mul_cellRead_mul_compressAll_dec (w : Database A Y) (a : A) (o : Option Y) :
    compressAll A Y * cellRead w a o * compressAll A Y =
      diagonal fun D : Database A Y ↦ if (w a).or (D a) = o then (1 : ℂ) else 0 := by
  rcases hw : w a with _ | v
  · have hr : cellRead w a o = compressAll A Y *
        (diagonal fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0) * compressAll A Y := by
      rw [← compressAt_mul_diagonal_cell_mul_compressAt]
      simp [cellRead, hw]
    rw [hr, ← Matrix.mul_assoc, ← Matrix.mul_assoc, compressAll_mul_self, Matrix.one_mul,
      Matrix.mul_assoc, compressAll_mul_self, Matrix.mul_one]
    congr 1
  · have hr : cellRead w a o = if o = some v then 1 else 0 := by simp [cellRead, hw]
    rw [hr]
    by_cases ho : o = some v
    · subst ho
      simp [compressAll_mul_self]
    · have ho' : ¬ some v = o := fun h ↦ ho h.symm
      simp [ho, ho']

/-- Every cell is kept by a read. -/
theorem cellsKeep_cellRead (S : A → Prop) (w : Database A Y) (a : A) (o : Option Y) :
    CellsKeep S (compressAll A Y * cellRead w a o * compressAll A Y) := by
  intro D' D h b _
  rw [compressAll_mul_cellRead_mul_compressAll_dec] at h
  by_cases he : D' = D
  · rw [he]
  · exact absurd (diagonal_apply_ne _ he) h

/-- A discard of cell `a` keeps every other cell. -/
theorem cellsKeep_cellDiscard {S : A → Prop} {a : A} (ha : S a) (o : Option Y) :
    CellsKeep S (compressAll A Y * cellDiscard a o * compressAll A Y) := by
  intro D' D h b hb
  have hba : b ≠ a := fun e ↦ hb (e ▸ ha)
  rw [cellDiscard_eq_piKron_dec, compressAll, piKron_mul, piKron_mul, piKron_apply] at h
  have hb' := Finset.prod_ne_zero_iff.mp h b (Finset.mem_univ b)
  rw [Function.update_of_ne hba, Matrix.mul_one, cellCompress_mul_self] at hb'
  by_contra hne
  exact hb' (Matrix.one_apply_ne hne)

end cells

section dbs

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

omit [Fintype X] [Fintype Z] in
/-- A nonzero entry of the decompressed product operator on the three databases is nonzero on
each factor. -/
theorem cellsKeep_dbs [Fintype X] [Fintype Z] {N₁ : Matrix (Database Z X) (Database Z X) ℂ}
    {N₂ N₃ : Matrix (Database X Z) (Database X Z) ℂ} {S₁ : Z → Prop} {S₂ S₃ : X → Prop}
    (h₁ : CellsKeep S₁ (compressAll Z X * N₁ * compressAll Z X))
    (h₂ : CellsKeep S₂ (compressAll X Z * N₂ * compressAll X Z))
    (h₃ : CellsKeep S₃ (compressAll X Z * N₃ * compressAll X Z)) {D' D : DbReg X Z}
    (h : (compressDbs X Z * (N₁ ⊗ₖ (N₂ ⊗ₖ N₃)) * compressDbs X Z) D' D ≠ 0) :
    (∀ z, ¬S₁ z → D'.1 z = D.1 z) ∧ (∀ x, ¬S₂ x → D'.2.1 x = D.2.1 x) ∧
      ∀ x, ¬S₃ x → D'.2.2 x = D.2.2 x := by
  simp only [compressDbs, ← mul_kronecker_mul] at h
  rw [kroneckerMap_apply, kroneckerMap_apply] at h
  exact ⟨h₁ _ _ (left_ne_zero_of_mul h),
    h₂ _ _ (left_ne_zero_of_mul (right_ne_zero_of_mul h)),
    h₃ _ _ (right_ne_zero_of_mul (right_ne_zero_of_mul h))⟩

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- A database triple agreeing with `D` at every cell is `D`. -/
theorem dbReg_eq_of_cells {D' D : DbReg X Z}
    (h : (∀ z, ¬False → D'.1 z = D.1 z) ∧ (∀ x, ¬False → D'.2.1 x = D.2.1 x) ∧
      ∀ x, ¬False → D'.2.2 x = D.2.2 x) : D' = D :=
  Prod.ext (funext fun z ↦ h.1 z not_false) (Prod.ext (funext fun x ↦ h.2.1 x not_false)
    (funext fun x ↦ h.2.2 x not_false))

/-- **An event determined off the hardwired cells of `W`**: two database triples that agree at
every cell not hardwired in `W` are both in `F` or both out. -/
def OffHw (W : Hw X Z) (F : DbReg X Z → Prop) : Prop :=
  ∀ D D' : DbReg X Z, (∀ z, W.1 z = none → D.1 z = D'.1 z) →
    (∀ x, W.2.1 x = none → D.2.1 x = D'.2.1 x) → (∀ x, W.2.2 x = none → D.2.2 x = D'.2.2 x) →
    (F D ↔ F D')

/-- The cell of a program port is hardwired in `W`. -/
def HwProg.CellIn (W : Hw X Z) : HwProg X Z → Prop
  | .programH z _ => W.1 z ≠ none
  | .programK x _ => W.2.1 x ≠ none
  | .programK' x _ => W.2.2 x ≠ none

variable {M : Type} [Fintype M] [DecidableEq M]

variable (M) in
/-- The ports of the hardwired runtime extended by `t` whose program ports program a cell
hardwired in `W`. -/
def HwPortIn {t : QuantumOracleSpec.{0, 0}} (W : Hw X Z) : ((hwSpec X Z M).sum t).Port → Prop
  | .inl (.inr c) => c.CellIn W
  | _ => True

variable [AddCommGroup X] [AddCommGroup Z]

/-- **A read commutes with the projector of every event on the databases**: in the decompressed
basis it is diagonal. -/
theorem hwReadKraus_commute_hwDecProj (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    (F : DbReg X Z → Prop) (hE : ∀ s, s ∈ E ↔ F s.1) (c : HwRead X Z M) (r : c.Result) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj E) * hwReadKraus c r =
      hwReadKraus c r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj E) := by
  cases c with
  | readH z upd =>
    refine clsKraus_commute_hwDecProj E F hE _ _ _ fun b D' D h ↦ ?_
    rw [← one_kronecker_one] at h
    rw [dbReg_eq_of_cells (cellsKeep_dbs (cellsKeep_cellRead _ _ _ _) (cellsKeep_one _)
      (cellsKeep_one _) h)]
  | readK x upd =>
    refine clsKraus_commute_hwDecProj E F hE _ _ _ fun b D' D h ↦ ?_
    rw [dbReg_eq_of_cells (cellsKeep_dbs (cellsKeep_one _) (cellsKeep_cellRead _ _ _ _)
      (cellsKeep_one _) h)]
  | readK' x upd =>
    refine clsKraus_commute_hwDecProj E F hE _ _ _ fun b D' D h ↦ ?_
    rw [dbReg_eq_of_cells (cellsKeep_dbs (cellsKeep_one _) (cellsKeep_one _)
      (cellsKeep_cellRead _ _ _ _) h)]

/-- **A program call of a cell hardwired in `W` commutes with the projector of an event
determined off `W`**: in the decompressed basis it changes the databases only at its cell. -/
theorem hwProgKraus_commute_hwDecProj (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    {W : Hw X Z} {F : DbReg X Z → Prop} (hF : OffHw W F) (hE : ∀ s, s ∈ E ↔ F s.1)
    {c : HwProg X Z} (hc : c.CellIn W) (r : c.Result) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj E) * hwProgKraus c r =
      hwProgKraus c r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj E) := by
  have hoff : ∀ {D' D : DbReg X Z},
      ((∀ z, ¬W.1 z ≠ none → D'.1 z = D.1 z) ∧ (∀ x, ¬W.2.1 x ≠ none → D'.2.1 x = D.2.1 x) ∧
        ∀ x, ¬W.2.2 x ≠ none → D'.2.2 x = D.2.2 x) → (F D' ↔ F D) := fun h ↦
    hF _ _ (fun z hz ↦ h.1 z (not_not.mpr hz)) (fun x hx ↦ h.2.1 x (not_not.mpr hx))
      (fun x hx ↦ h.2.2 x (not_not.mpr hx))
  cases c with
  | programH z v =>
    refine clsKraus_commute_hwDecProj E F hE _ _ _ fun b D' D h ↦ ?_
    rw [← one_kronecker_one] at h
    exact hoff (cellsKeep_dbs (cellsKeep_cellDiscard (S := fun z ↦ W.1 z ≠ none) hc _)
      (cellsKeep_one _) (cellsKeep_one _) h)
  | programK x v =>
    refine clsKraus_commute_hwDecProj E F hE _ _ _ fun b D' D h ↦ ?_
    exact hoff (cellsKeep_dbs (cellsKeep_one _)
      (cellsKeep_cellDiscard (S := fun x ↦ W.2.1 x ≠ none) hc _) (cellsKeep_one _) h)
  | programK' x v =>
    refine clsKraus_commute_hwDecProj E F hE _ _ _ fun b D' D h ↦ ?_
    exact hoff (cellsKeep_dbs (cellsKeep_one _) (cellsKeep_one _)
      (cellsKeep_cellDiscard (S := fun x ↦ W.2.2 x ≠ none) hc _) h)

/-! ## The initial weight -/

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] in
/-- The amplitude of a total table in the uniform superposition, squared, is one over the number
of tables. -/
theorem star_amp_mul_amp :
    star (cellAmp X ^ Fintype.card Z * (cellAmp Z ^ Fintype.card X * cellAmp Z ^ Fintype.card X)) *
        (cellAmp X ^ Fintype.card Z * (cellAmp Z ^ Fintype.card X * cellAmp Z ^ Fintype.card X)) =
      ((Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℂ))⁻¹ := by
  simp only [star_mul', star_pow, star_cellAmp]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun]
  push_cast
  rw [show cellAmp X ^ Fintype.card Z * (cellAmp Z ^ Fintype.card X * cellAmp Z ^ Fintype.card X) *
      (cellAmp X ^ Fintype.card Z * (cellAmp Z ^ Fintype.card X * cellAmp Z ^ Fintype.card X)) =
      (cellAmp X * cellAmp X) ^ Fintype.card Z * ((cellAmp Z * cellAmp Z) ^ Fintype.card X *
        (cellAmp Z * cellAmp Z) ^ Fintype.card X) by ring, cellAmp_mul_self, cellAmp_mul_self]
  rw [inv_pow, inv_pow, ← mul_inv, ← mul_inv]

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] in
open scoped Classical in
/-- The column of the decompressed empty databases, squared and summed over an event. -/
theorem sum_star_compressDbs_empty (F : DbReg X Z → Prop) :
    ∑ D : DbReg X Z, star (compressDbs X Z D (Database.empty, Database.empty, Database.empty)) *
        (if F D then 1 else 0) * compressDbs X Z D (Database.empty, Database.empty, Database.empty) =
      ((Finset.univ.filter fun t ↦ F (ofFunDbs t)).card : ℂ) *
        ((Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℂ))⁻¹ := by
  have hent : ∀ D : DbReg X Z, compressDbs X Z D (Database.empty, Database.empty, Database.empty) =
      compressAll Z X D.1 Database.empty *
        (compressAll X Z D.2.1 Database.empty * compressAll X Z D.2.2 Database.empty) := fun D ↦ by
    rw [compressDbs, kroneckerMap_apply, kroneckerMap_apply]
  rw [← Finset.sum_boole, Finset.sum_mul]
  symm
  refine Fintype.sum_of_injective ofFunDbs ofFunDbs_injective _ _ (fun D hD ↦ ?_) fun t ↦ ?_
  · rw [hent]
    by_contra hne
    have h₁ := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
    have h₀ := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have h₂ := left_ne_zero_of_mul (right_ne_zero_of_mul (right_ne_zero_of_mul hne))
    have h₃ := right_ne_zero_of_mul (right_ne_zero_of_mul (right_ne_zero_of_mul hne))
    rw [compressAll_apply_empty] at h₁ h₂ h₃
    split_ifs at h₁ with c₁
    split_ifs at h₂ with c₂
    split_ifs at h₃ with c₃
    · refine hD ⟨(fun z ↦ (D.1 z).get (Option.isSome_iff_ne_none.mpr (c₁ z)),
        fun x ↦ (D.2.1 x).get (Option.isSome_iff_ne_none.mpr (c₂ x)),
        fun x ↦ (D.2.2 x).get (Option.isSome_iff_ne_none.mpr (c₃ x))), ?_⟩
      refine Prod.ext (funext fun z ↦ ?_) (Prod.ext (funext fun x ↦ ?_) (funext fun x ↦ ?_)) <;>
        simp [ofFunDbs, Database.ofFun]
    · exact h₃ rfl
    · exact h₂ rfl
    · exact h₁ rfl
  · rw [hent]
    simp only [ofFunDbs, compressAll_ofFun_empty]
    rw [← star_amp_mul_amp (X := X) (Z := Z)]
    split_ifs <;> ring

open scoped Classical in
/-- **The initial weight of a database event**: from the empty databases, in the decompressed
basis, the weight of `{s | F s.1}` is the uniform probability of `F` over the total tables times
the trace. -/
theorem trace_conj_hwDecProj_basis (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    (F : DbReg X Z → Prop) (hE : ∀ s, s ∈ E ↔ F s.1) (b : Hw X Z × M) {A : Type} [Fintype A]
    [DecidableEq A] (ρ : Matrix A A ℂ) :
    (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ hwDecProj E)
      (ρ ⊗ₖ Matrix.single (((Database.empty, Database.empty, Database.empty), b) : HwReg X Z M)
        ((Database.empty, Database.empty, Database.empty), b) 1)).trace.re =
      ρ.trace.re * (((Finset.univ.filter fun t ↦ F (ofFunDbs t)).card : ℝ) /
        Fintype.card ((Z → X) × (X → Z) × (X → Z))) := by
  classical
  set s₀ : HwReg X Z M := ((Database.empty, Database.empty, Database.empty), b)
  have hPi : (diagonal fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0)ᴴ =
      diagonal fun s ↦ if s ∈ E then 1 else 0 := by
    rw [diagonal_conjTranspose]
    congr 1
    funext s
    simp only [Pi.star_apply]
    split_ifs <;> simp
  have hPP : (diagonal fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0) *
      (diagonal fun s ↦ if s ∈ E then 1 else 0) = diagonal fun s ↦ if s ∈ E then 1 else 0 := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext s
    split_ifs <;> simp
  have hQ : (hwDecProj E)ᴴ = hwDecProj E := by
    rw [hwDecProj, conjTranspose_mul, conjTranspose_mul, conjTranspose_compressReg, hPi,
      Matrix.mul_assoc]
  have hQQ : hwDecProj E * hwDecProj E = hwDecProj E := by
    have hCC := compressReg_mul_self (X := X) (Z := Z) (M := M)
    unfold hwDecProj
    generalize compressReg X Z M = C at hCC ⊢
    generalize (diagonal fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0) = P at hPP ⊢
    rw [show C * P * C * (C * P * C) = C * P * (C * C) * P * C by
      simp only [Matrix.mul_assoc], hCC, Matrix.mul_one, Matrix.mul_assoc C P P, hPP]
  have hdiag : hwDecProj E s₀ s₀ = ((((Finset.univ.filter fun t ↦ F (ofFunDbs t)).card : ℝ) /
      Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ) : ℂ) := by
    rw [hwDecProj, Matrix.mul_apply]
    simp only [mul_diagonal]
    rw [Fintype.sum_prod_type]
    have hrow : ∀ D : DbReg X Z, ∑ b' : Hw X Z × M, compressReg X Z M s₀ (D, b') *
        (if (D, b') ∈ E then (1 : ℂ) else 0) * compressReg X Z M (D, b') s₀ =
        star (compressDbs X Z D (Database.empty, Database.empty, Database.empty)) *
          (if F D then 1 else 0) * compressDbs X Z D (Database.empty, Database.empty,
            Database.empty) := fun D ↦ by
      rw [Finset.sum_eq_single b (fun b' _ hb' ↦ by
        simp [s₀, compressReg, kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hb')])
        (fun h ↦ absurd (Finset.mem_univ b) h)]
      have hstar : compressReg X Z M s₀ (D, b) = star (compressReg X Z M (D, b) s₀) := by
        rw [← conjTranspose_apply, conjTranspose_compressReg]
      rw [hstar]
      simp only [compressReg, kroneckerMap_apply, Matrix.one_apply_eq, mul_one, s₀]
      rw [if_congr (hE (D, b)) rfl rfl]
    rw [Finset.sum_congr rfl fun D _ ↦ hrow D, sum_star_compressDbs_empty]
    push_cast
    rw [div_eq_mul_inv]
  rw [MatrixMap.conj_apply, conjTranspose_kronecker, conjTranspose_one, hQ,
    ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, trace_kronecker]
  have htr : (hwDecProj E * Matrix.single s₀ s₀ 1 * hwDecProj E).trace = hwDecProj E s₀ s₀ := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQQ]
    simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]
  rw [htr, hdiag, Complex.re_mul_ofReal]

/-! ## The invariant -/

variable {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

open scoped Classical in
/-- **The decompressed table is uniform off the hardwired cells.** Run the hardwired runtime
started at `(∅, W₀, m₀)`, extended by ports `step` commuting with the projector (record ports:
`clsKraus_one_commute_hwDecProj`), from `ρ ⊗ init`, along a program whose every call is
`HwPortIn W` (program calls only program cells hardwired in `W`). For an event `F` on the
database triples determined off `W`, the weight of the decompressed event `{s | F s.1}` at the end
is at most `tr ρ` times the uniform probability of `F` over the total tables. -/
theorem eventWeight_hwDecProj_le {t : QuantumOracleSpec.{0, 0}} (W₀ : Hw X Z) (m₀ : M)
    (step : ∀ j : t.Port, SubInstrument (t.In j × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (t.Out j × (spongeHardwiredRuntime X Z W₀ m₀).D) (t.Result j))
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    (hstep : ∀ j r, (step j).branch r ∘ₗ
        (MatrixMap.conj (hwDecProj E)).amplifyLeft (t.In j) =
      (MatrixMap.conj (hwDecProj E)).amplifyLeft (t.Out j) ∘ₗ (step j).branch r)
    {W : Hw X Z} {F : DbReg X Z → Prop} (hF : OffHw W F) (hE : ∀ s, s ∈ E ↔ F s.1)
    {P : ∀ (i : ((hwSpec X Z M).sum t).Port) (E' : QReg),
      Matrix ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E')
        ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E') ℂ → Prop}
    (hP : ∀ i E' σ, P i E' σ → HwPortIn M W i) (x : QuantumComp L ((hwSpec X Z M).sum t) Ω A)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef)
    (hx : ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I P x
      (ρ ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix)) :
    ((spongeHardwiredRuntime X Z W₀ m₀).extend step).eventWeight I (hwDecProj E) x
        (ρ ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix) ≤
      ENNReal.ofReal ρ.trace.re *
        (((Finset.univ.filter fun t ↦ F (ofFunDbs t)).card : ℝ≥0∞) /
          Fintype.card ((Z → X) × (X → Z) × (X → Z))) := by
  classical
  have hρ₀ : (ρ ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).PosSemidef :=
    hρ.kronecker (spongeHardwiredRuntime X Z W₀ m₀).init.posSemidef
  refine (eventWeight_le_of_commute I ((spongeHardwiredRuntime X Z W₀ m₀).extend step)
    (hwDecProj E) (HwPortIn M W) (fun i hi r ↦ ?_) hP x hρ₀ hx).trans (le_of_eq ?_)
  · rcases i with ((i | c) | c) | j
    · cases i <;> exact branch_comm_of_commute
        (spongeHardwiredRuntime_step_sponge W₀ m₀ _ r) (hwPort_commute_hwDecProj E _)
    · exact branch_comm_of_commute (spongeHardwiredRuntime_step_read W₀ m₀ c r)
        (hwReadKraus_commute_hwDecProj E F hE c r)
    · exact branch_comm_of_commute (spongeHardwiredRuntime_step_prog W₀ m₀ c r)
        (hwProgKraus_commute_hwDecProj E hF hE hi r)
    · exact hstep j r
  · change ENNReal.ofReal (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ hwDecProj E)
      (ρ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
        HwReg X Z M)).matrix)).trace.re = _
    rw [SubState.matrix_basis, trace_conj_hwDecProj_basis E F hE (W₀, m₀) ρ,
      ENNReal.ofReal_mul (hρ.trace_re_nonneg), ENNReal.ofReal_div_of_pos
        (Nat.cast_pos.mpr Fintype.card_pos), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

end dbs

end Quantum.Sponge

end
