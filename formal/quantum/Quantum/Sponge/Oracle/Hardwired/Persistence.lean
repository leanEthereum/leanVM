module

public import Quantum.Sponge.Oracle.Hardwired.DecUniform

@[expose] public section

/-!
# Persistence of a decompressed cell value, and recorded weight against decompressed weight

In the decompressed basis (conjugation by `compressReg`), every port of the hardwired runtime
extended by record ports leaves the decompressed database triple `D` unchanged, except a program
call, which resets its own cell (DecUniform). So the projector `Q` on "cell `c` of `D` satisfies
`F`" commutes with every port except a program at `c`, and a branch on which `Q` has weight zero
keeps weight zero until a program at `c`.

* **Zero weight persists** (`forallQueries_conj_eq_zero`, `eventWeight_eq_zero_of_commute`):
  along a run whose calls all commute with `Q`, an operator annihilated by `1 ⊗ Q` presents
  annihilated operators to every later call and ends annihilated.
* **The hardwired ports** (`extend_step_commute_hwDecProj`, `forallQueries_hwDecProj_eq_zero`,
  `eventWeight_hwDecProj_eq_zero`): every port other than a program at `c` (`NotProgAt`)
  commutes with `hwDecProj E` for `E = {s | F s.1}` and `F` looking only at `c` (`OnCell`).
* **A read outside the event starts it** (`hwDecProj_mul_hwReadKraus_mul_eq_zero`,
  `conj_queryStep_read_eq_zero`): after a read of `c` whose outcome is outside the event, from
  an operator whose cell `c` is not hardwired, `1 ⊗ Q` has weight zero.
* **Recorded weight against decompressed weight** (`re_trace_cellInd_le`, `re_trace_recH_le`,
  `re_trace_recK_le`, `re_trace_recK'_le`). Let `G` be the compressed projector "cell `c` is
  recorded with a value `y` with `g (some y)`" and `Q = C G C` the decompressed one. On an
  operator with no decompressed `⊥` at `c` (`CellNoBot`-type support, from `noBot_runtimeR`):
  `tr(G σ) ≤ (√tr(Q σ) + √(κ tr σ))²` with `κ = cellFrac g = #{y | g (some y)} / |Y|`.
  With `Π` the projector on the recorded values of the cell and `U` the projector on their
  uniform superposition, `Π C G C Π = (Π - U) G (Π - U)` (`cellSomeProj_mul_cellCompress_mul`)
  and `U G U = κ U`: the conversion error is the weight `κ tr(U σ) ≤ κ tr σ` of the
  uniform-vector component, entering through `√`.
* **The consequence along runs** (`forallQueries_recH_le`, `forallQueries_recK_le`,
  `forallQueries_recK'_le`): from a branch with decompressed weight zero, every later call before
  a program at `c` is presented an operator whose recorded weight is at most `κ` times its trace.
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Sponge

open Quantum QuantumRuntime

/-! ## Zero weight of a commuting projector persists -/

section persist

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **Zero weight persists along a run of commuting ports.** If every port `i` with `good i`
commutes with `conj Q` on the runtime register, every call of the run of `x` from `ρ` is of such
a port, and `1 ⊗ Q` annihilates `ρ`, then every call is presented an operator annihilated by
`1 ⊗ Q` (on the runtime register, framed by the remainder). -/
theorem forallQueries_conj_eq_zero (R : QuantumRuntime spec) (Q : Matrix R.D R.D ℂ)
    (good : spec.Port → Prop)
    (hc : ∀ i, good i → ∀ r, (R.step i).branch r ∘ₗ (MatrixMap.conj Q).amplifyLeft (spec.In i) =
      (MatrixMap.conj Q).amplifyLeft (spec.Out i) ∘ₗ (R.step i).branch r)
    {P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    (hP : ∀ i E σ, P i E σ → good i) {x : QuantumComp L spec Ω A}
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hx : R.ForallQueries I P x ρ)
    (h0 : (MatrixMap.conj Q).amplifyLeft A ρ = 0) :
    R.ForallQueries I (fun i E σ ↦ P i E σ ∧
      ((MatrixMap.conj Q).amplifyLeft (spec.In i)).amplify E σ = 0) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => trivial
  | primBind B o k ih =>
    intro b
    refine ih b (hx b) ?_
    have e : ((I o).frame R.D).branch b ((MatrixMap.conj Q).amplifyLeft B ρ) =
        (MatrixMap.conj Q).amplifyLeft _ (((I o).frame R.D).branch b ρ) :=
      LinearMap.congr_fun
        (MatrixMap.amplify_comp_amplifyLeft ((I o).branch b) (MatrixMap.conj Q)) ρ
    rw [← e, h0, map_zero]
  | queryBind B i E ℓ k ih =>
    refine ⟨⟨hx.1, ?_⟩, fun r ↦ ih r (hx.2 r) ?_⟩
    · have e : (SubInstrument.relabel (queryEquivIn ℓ R.D)).branch ()
            ((MatrixMap.conj Q).amplifyLeft B ρ) =
          ((MatrixMap.conj Q).amplifyLeft (spec.In i)).amplify E
            ((SubInstrument.relabel (queryEquivIn ℓ R.D)).branch () ρ) :=
        LinearMap.congr_fun (intertwines_relabel_queryEquivIn (MatrixMap.conj Q) ℓ ()) ρ
      rw [← e, h0, map_zero]
    · have e : (R.queryStep i E ℓ).branch r ((MatrixMap.conj Q).amplifyLeft B ρ) =
          (MatrixMap.conj Q).amplifyLeft _ ((R.queryStep i E ℓ).branch r ρ) :=
        LinearMap.congr_fun (intertwines_queryStep (fun r ↦ hc i (hP _ _ _ hx.1) r) E ℓ r) ρ
      rw [← e, h0, map_zero]

/-- **Zero weight at the end.** Under the hypotheses of `forallQueries_conj_eq_zero`, from a
positive semidefinite `ρ` annihilated by `1 ⊗ Q`, the weight of `1 ⊗ Q` over the leaves is zero. -/
theorem eventWeight_eq_zero_of_commute (R : QuantumRuntime spec) (Q : Matrix R.D R.D ℂ)
    (good : spec.Port → Prop)
    (hc : ∀ i, good i → ∀ r, (R.step i).branch r ∘ₗ (MatrixMap.conj Q).amplifyLeft (spec.In i) =
      (MatrixMap.conj Q).amplifyLeft (spec.Out i) ∘ₗ (R.step i).branch r)
    {P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    (hP : ∀ i E σ, P i E σ → good i) (x : QuantumComp L spec Ω A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (hx : R.ForallQueries I P x ρ)
    (h0 : (MatrixMap.conj Q).amplifyLeft A ρ = 0) :
    R.eventWeight I Q x ρ = 0 := by
  refine le_antisymm ((eventWeight_le_of_commute I R Q good hc hP x hρ hx).trans ?_) zero_le
  rw [← MatrixMap.amplifyLeft_conj, h0, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]

end persist

/-! ## Cells, and the ports that keep them -/

/-- A cell of the three databases: cell `z` of `h`, cell `x` of `k`, cell `x` of `k'`. -/
inductive DbCell (X Z : Type) where
  | h (z : Z)
  | k (x : X)
  | k' (x : X)

section cellDefs

variable {X Z : Type}

/-- The cell a program port hardwires. -/
def HwProg.cell : HwProg X Z → DbCell X Z
  | .programH z _ => .h z
  | .programK x _ => .k x
  | .programK' x _ => .k' x

/-- Two database triples agree at a cell. -/
def DbCell.Agree : DbCell X Z → DbReg X Z → DbReg X Z → Prop
  | .h z, D, D' => D.1 z = D'.1 z
  | .k x, D, D' => D.2.1 x = D'.2.1 x
  | .k' x, D, D' => D.2.2 x = D'.2.2 x

/-- An event on the database triples that looks only at cell `c`. -/
def OnCell (c : DbCell X Z) (F : DbReg X Z → Prop) : Prop :=
  ∀ D D', c.Agree D D' → (F D ↔ F D')

variable [DecidableEq X] [DecidableEq Z]

/-- The hardwired data holding only the cell of a program port, at its value. -/
def HwProg.single : HwProg X Z → Hw X Z
  | .programH z v => (Function.update (fun _ ↦ none) z (some v), fun _ ↦ none, fun _ ↦ none)
  | .programK x v => (fun _ ↦ none, Function.update (fun _ ↦ none) x (some v), fun _ ↦ none)
  | .programK' x v => (fun _ ↦ none, fun _ ↦ none, Function.update (fun _ ↦ none) x (some v))

end cellDefs

section ports

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

variable (M : Type) in
/-- The ports of the hardwired runtime extended by `t` other than a program call at cell `c`. -/
def NotProgAt {t : QuantumOracleSpec.{0, 0}} (c : DbCell X Z) :
    ((hwSpec X Z M).sum t).Port → Prop
  | .inl (.inr p) => p.cell ≠ c
  | _ => True

omit [Fintype X] [Fintype Z] in
/-- A program port's cell is hardwired in its single-cell data. -/
theorem HwProg.cellIn_single (p : HwProg X Z) : p.CellIn p.single := by
  cases p <;> simp [HwProg.CellIn, HwProg.single]

omit [Fintype X] [Fintype Z] in
/-- An event looking only at cell `c` is determined off the single-cell data of a program port
at another cell. -/
theorem offHw_single {c : DbCell X Z} {F : DbReg X Z → Prop} (hF : OnCell c F) {p : HwProg X Z}
    (hp : p.cell ≠ c) : OffHw p.single F := by
  intro D D' h₁ h₂ h₃
  refine hF D D' ?_
  cases p with
  | programH z v =>
    cases c with
    | h z' =>
      have hz : z' ≠ z := fun e ↦ hp (by subst e; rfl)
      exact h₁ z' (by simp [HwProg.single, hz])
    | k x => exact h₂ x rfl
    | k' x => exact h₃ x rfl
  | programK x v =>
    cases c with
    | h z => exact h₁ z rfl
    | k x' =>
      have hx : x' ≠ x := fun e ↦ hp (by subst e; rfl)
      exact h₂ x' (by simp [HwProg.single, hx])
    | k' x' => exact h₃ x' rfl
  | programK' x v =>
    cases c with
    | h z => exact h₁ z rfl
    | k x' => exact h₂ x' rfl
    | k' x' =>
      have hx : x' ≠ x := fun e ↦ hp (by subst e; rfl)
      exact h₃ x' (by simp [HwProg.single, hx])

variable [AddCommGroup X] [AddCommGroup Z] {M : Type} [Fintype M] [DecidableEq M]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The decompressed projector is Hermitian. -/
theorem conjTranspose_hwDecProj (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)] :
    (hwDecProj E)ᴴ = hwDecProj E := by
  have hPi : (diagonal fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0)ᴴ =
      diagonal fun s ↦ if s ∈ E then 1 else 0 := by
    rw [diagonal_conjTranspose]
    congr 1
    funext s
    simp only [Pi.star_apply]
    split_ifs <;> simp
  rw [hwDecProj, conjTranspose_mul, conjTranspose_mul, conjTranspose_compressReg, hPi,
    Matrix.mul_assoc]

/-- The decompressed projector is idempotent. -/
theorem hwDecProj_mul_self (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)] :
    hwDecProj E * hwDecProj E = hwDecProj E := by
  have hPP : (diagonal fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0) *
      (diagonal fun s ↦ if s ∈ E then 1 else 0) = diagonal fun s ↦ if s ∈ E then 1 else 0 := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext s
    split_ifs <;> simp
  have hCC := compressReg_mul_self (X := X) (Z := Z) (M := M)
  unfold hwDecProj
  generalize compressReg X Z M = C at hCC ⊢
  generalize (diagonal fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0) = P at hPP ⊢
  rw [show C * P * C * (C * P * C) = C * P * (C * C) * P * C by
    simp only [Matrix.mul_assoc], hCC, Matrix.mul_one, Matrix.mul_assoc C P P, hPP]

/-- **Every port other than a program at `c` commutes with the projector of an event looking
only at `c`**: sponge ports and reads keep the decompressed databases, a program at another cell
changes only its own cell, and the extension ports commute by hypothesis (record ports:
`clsKraus_one_commute_hwDecProj`). -/
theorem extend_step_commute_hwDecProj {t : QuantumOracleSpec.{0, 0}} (W₀ : Hw X Z) (m₀ : M)
    (step : ∀ j : t.Port, SubInstrument (t.In j × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (t.Out j × (spongeHardwiredRuntime X Z W₀ m₀).D) (t.Result j))
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    (hstep : ∀ j r, (step j).branch r ∘ₗ
        (MatrixMap.conj (hwDecProj E)).amplifyLeft (t.In j) =
      (MatrixMap.conj (hwDecProj E)).amplifyLeft (t.Out j) ∘ₗ (step j).branch r)
    {c : DbCell X Z} {F : DbReg X Z → Prop} (hF : OnCell c F) (hE : ∀ s, s ∈ E ↔ F s.1)
    (i : ((hwSpec X Z M).sum t).Port) (hi : NotProgAt M c i)
    (r : ((hwSpec X Z M).sum t).Result i) :
    (((spongeHardwiredRuntime X Z W₀ m₀).extend step).step i).branch r ∘ₗ
        (MatrixMap.conj (hwDecProj E)).amplifyLeft (((hwSpec X Z M).sum t).In i) =
      (MatrixMap.conj (hwDecProj E)).amplifyLeft (((hwSpec X Z M).sum t).Out i) ∘ₗ
        (((spongeHardwiredRuntime X Z W₀ m₀).extend step).step i).branch r := by
  rcases i with ((i | p) | p) | j
  · cases i <;> exact branch_comm_of_commute
      (spongeHardwiredRuntime_step_sponge W₀ m₀ _ r) (hwPort_commute_hwDecProj E _)
  · exact branch_comm_of_commute (spongeHardwiredRuntime_step_read W₀ m₀ p r)
      (hwReadKraus_commute_hwDecProj E F hE p r)
  · exact branch_comm_of_commute (spongeHardwiredRuntime_step_prog W₀ m₀ p r)
      (hwProgKraus_commute_hwDecProj E (offHw_single hF hi) hE p.cellIn_single r)
  · exact hstep j r

variable {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **Persistence of a decompressed cell event (Consequence 1).** Run the hardwired runtime
extended by ports commuting with the projector (record ports) from an operator `ρ` on which
the decompressed event `E = {s | F s.1}`, `F` looking only at cell `c`, has weight zero (the
branch after a read of `c` with an outcome outside the event:
`conj_queryStep_read_eq_zero`). If no call of the run is a program at `c`, every call is
presented an operator on which the event still has weight zero: its decompressed form is
supported off `E`. -/
theorem forallQueries_hwDecProj_eq_zero {t : QuantumOracleSpec.{0, 0}} (W₀ : Hw X Z) (m₀ : M)
    (step : ∀ j : t.Port, SubInstrument (t.In j × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (t.Out j × (spongeHardwiredRuntime X Z W₀ m₀).D) (t.Result j))
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    (hstep : ∀ j r, (step j).branch r ∘ₗ
        (MatrixMap.conj (hwDecProj E)).amplifyLeft (t.In j) =
      (MatrixMap.conj (hwDecProj E)).amplifyLeft (t.Out j) ∘ₗ (step j).branch r)
    {c : DbCell X Z} {F : DbReg X Z → Prop} (hF : OnCell c F) (hE : ∀ s, s ∈ E ↔ F s.1)
    {P : ∀ (i : ((hwSpec X Z M).sum t).Port) (E' : QReg),
      Matrix ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E')
        ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E') ℂ → Prop}
    (hP : ∀ i E' σ, P i E' σ → NotProgAt M c i) {x : QuantumComp L ((hwSpec X Z M).sum t) Ω A}
    {ρ : Matrix (A × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (A × (spongeHardwiredRuntime X Z W₀ m₀).D) ℂ}
    (hx : ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I P x ρ)
    (h0 : (MatrixMap.conj (hwDecProj E)).amplifyLeft A ρ = 0) :
    ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I (fun i E' σ ↦ P i E' σ ∧
      ((MatrixMap.conj (hwDecProj E)).amplifyLeft (((hwSpec X Z M).sum t).In i)).amplify E' σ =
        0) x ρ :=
  forallQueries_conj_eq_zero I ((spongeHardwiredRuntime X Z W₀ m₀).extend step) (hwDecProj E)
    (NotProgAt M c)
    (fun i hi r ↦ extend_step_commute_hwDecProj W₀ m₀ step E hstep hF hE i hi r) hP hx h0

/-- **Persistence at the end of the run**: under the hypotheses of
`forallQueries_hwDecProj_eq_zero`, from a positive semidefinite operator, the decompressed event
has weight zero over the leaves. -/
theorem eventWeight_hwDecProj_eq_zero {t : QuantumOracleSpec.{0, 0}} (W₀ : Hw X Z) (m₀ : M)
    (step : ∀ j : t.Port, SubInstrument (t.In j × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (t.Out j × (spongeHardwiredRuntime X Z W₀ m₀).D) (t.Result j))
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    (hstep : ∀ j r, (step j).branch r ∘ₗ
        (MatrixMap.conj (hwDecProj E)).amplifyLeft (t.In j) =
      (MatrixMap.conj (hwDecProj E)).amplifyLeft (t.Out j) ∘ₗ (step j).branch r)
    {c : DbCell X Z} {F : DbReg X Z → Prop} (hF : OnCell c F) (hE : ∀ s, s ∈ E ↔ F s.1)
    {P : ∀ (i : ((hwSpec X Z M).sum t).Port) (E' : QReg),
      Matrix ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E')
        ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E') ℂ → Prop}
    (hP : ∀ i E' σ, P i E' σ → NotProgAt M c i) (x : QuantumComp L ((hwSpec X Z M).sum t) Ω A)
    {ρ : Matrix (A × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (A × (spongeHardwiredRuntime X Z W₀ m₀).D) ℂ} (hρ : ρ.PosSemidef)
    (hx : ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I P x ρ)
    (h0 : (MatrixMap.conj (hwDecProj E)).amplifyLeft A ρ = 0) :
    ((spongeHardwiredRuntime X Z W₀ m₀).extend step).eventWeight I (hwDecProj E) x ρ = 0 :=
  eventWeight_eq_zero_of_commute I ((spongeHardwiredRuntime X Z W₀ m₀).extend step)
    (hwDecProj E) (NotProgAt M c)
    (fun i hi r ↦ extend_step_commute_hwDecProj W₀ m₀ step E hstep hF hE i hi r) hP x hρ hx h0

/-! ### A read outside the event starts the persistence -/

/-- The read cell of a read port is not hardwired in the classical data. -/
def HwRead.Free : HwRead X Z M → Hw X Z × M → Prop
  | .readH z _, b => b.1.1 z = none
  | .readK x _, b => b.1.2.1 x = none
  | .readK' x _, b => b.1.2.2 x = none

/-- Freedom of the read cell, decided cell by cell. -/
instance HwRead.instDecidablePredFree (c : HwRead X Z M) : DecidablePred c.Free := fun b ↦
  match c with
  | .readH z _ => inferInstanceAs (Decidable (b.1.1 z = none))
  | .readK x _ => inferInstanceAs (Decidable (b.1.2.1 x = none))
  | .readK' x _ => inferInstanceAs (Decidable (b.1.2.2 x = none))

/-- The decompressed content of the read cell is the outcome of the read. -/
def HwRead.Hit : (c : HwRead X Z M) → c.Result → DbReg X Z → Prop
  | .readH z _, r, D => D.1 z = r.1
  | .readK x _, r, D => D.2.1 x = r.1
  | .readK' x _, r, D => D.2.2 x = r.1

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
theorem diagonal_ne_zero {T : Type} [DecidableEq T] {f : T → Prop} [DecidablePred f]
    {D' D : T} (h : (diagonal fun D ↦ if f D then (1 : ℂ) else 0) D' D ≠ 0) : D' = D ∧ f D := by
  by_cases hDD : D' = D
  · subst hDD
    rw [diagonal_apply_eq] at h
    exact ⟨rfl, by_contra fun hc ↦ h (by simp [hc])⟩
  · exact absurd (diagonal_apply_ne _ hDD) h

omit [Fintype M] [DecidableEq M] in
theorem compressDbs_readH_ne_zero {w : Database Z X} {z : Z} {o : Option X} {D' D : DbReg X Z}
    (h : (compressDbs X Z * (cellRead w z o ⊗ₖ
      (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ)) *
        compressDbs X Z) D' D ≠ 0) : D' = D ∧ (w z).or (D.1 z) = o := by
  have hd : compressDbs X Z * (cellRead w z o ⊗ₖ
      (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ)) *
        compressDbs X Z = diagonal fun D : DbReg X Z ↦ if (w z).or (D.1 z) = o then 1 else 0 := by
    rw [← one_kronecker_one, compressDbs]
    simp only [← mul_kronecker_mul, Matrix.mul_one, compressAll_mul_self,
      compressAll_mul_cellRead_mul_compressAll_dec]
    simp only [← diagonal_one, diagonal_kronecker_diagonal, mul_one]
  rw [hd] at h
  exact diagonal_ne_zero h

omit [Fintype M] [DecidableEq M] in
theorem compressDbs_readK_ne_zero {w : Database X Z} {x : X} {o : Option Z} {D' D : DbReg X Z}
    (h : (compressDbs X Z * ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (cellRead w x o ⊗ₖ
      (1 : Matrix (Database X Z) (Database X Z) ℂ))) * compressDbs X Z) D' D ≠ 0) :
    D' = D ∧ (w x).or (D.2.1 x) = o := by
  have hd : compressDbs X Z * ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (cellRead w x o ⊗ₖ
      (1 : Matrix (Database X Z) (Database X Z) ℂ))) * compressDbs X Z =
        diagonal fun D : DbReg X Z ↦ if (w x).or (D.2.1 x) = o then 1 else 0 := by
    rw [compressDbs]
    simp only [← mul_kronecker_mul, Matrix.mul_one, compressAll_mul_self,
      compressAll_mul_cellRead_mul_compressAll_dec]
    simp only [← diagonal_one, diagonal_kronecker_diagonal, one_mul, mul_one]
  rw [hd] at h
  exact diagonal_ne_zero h

omit [Fintype M] [DecidableEq M] in
theorem compressDbs_readK'_ne_zero {w : Database X Z} {x : X} {o : Option Z} {D' D : DbReg X Z}
    (h : (compressDbs X Z * ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead w x o)) * compressDbs X Z) D' D ≠
        0) : D' = D ∧ (w x).or (D.2.2 x) = o := by
  have hd : compressDbs X Z * ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead w x o)) * compressDbs X Z =
        diagonal fun D : DbReg X Z ↦ if (w x).or (D.2.2 x) = o then 1 else 0 := by
    rw [compressDbs]
    simp only [← mul_kronecker_mul, Matrix.mul_one, compressAll_mul_self,
      compressAll_mul_cellRead_mul_compressAll_dec]
    simp only [← diagonal_one, diagonal_kronecker_diagonal, one_mul]
  rw [hd] at h
  exact diagonal_ne_zero h

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
theorem one_kron_diagonal_snd {n T : Type} [DecidableEq n] [DecidableEq T] [DecidableEq (n × T)]
    (f : T → ℂ) :
    (1 : Matrix n n ℂ) ⊗ₖ diagonal f = diagonal fun a : n × T ↦ f a.2 := by
  ext a b
  rw [kroneckerMap_apply, diagonal_apply, Matrix.one_apply, diagonal_apply]
  by_cases h₁ : a.1 = b.1 <;> by_cases h₂ : a.2 = b.2 <;> simp [h₁, h₂, Prod.ext_iff]

/-- **A classical port whose decompressed database operators fix the databases and, where the
cell is free, leave them outside `F`, maps a free operator outside the decompressed event.** -/
theorem one_kron_hwDecProj_mul_clsKraus_mul_eq_zero (E : Set (HwReg X Z M))
    [DecidablePred (· ∈ E)] (F : DbReg X Z → Prop) (hE : ∀ s, s ∈ E ↔ F s.1)
    (p : Hw X Z × M → Prop) [DecidablePred p] (φ : Hw X Z × M → Hw X Z × M)
    (R : Hw X Z × M → Matrix (DbReg X Z) (DbReg X Z) ℂ) (free : Hw X Z × M → Prop)
    [DecidablePred free]
    (hR : ∀ b D' D, (compressDbs X Z * R b * compressDbs X Z) D' D ≠ 0 → free b →
      D' = D ∧ ¬ F D) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj E) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus p φ R) *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ diagonal fun s : HwReg X Z M ↦ if free s.2 then 1 else 0) =
        0 := by
  set C1 := (1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M with hC1
  set P1 := (1 : Matrix Unit Unit ℂ) ⊗ₖ
    diagonal (fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0) with hP1
  set W1 := (1 : Matrix Unit Unit ℂ) ⊗ₖ
    diagonal (fun s : HwReg X Z M ↦ if free s.2 then (1 : ℂ) else 0) with hW1
  set K := (1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus p φ R with hK
  have hCC : C1 * C1 = 1 := by
    rw [hC1, ← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  have hQ : (1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj E = C1 * P1 * C1 := by
    rw [hC1, hP1, hwDecProj, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.one_mul]
  have hW : C1 * W1 = W1 * C1 := by
    have hdiag : (diagonal fun s : HwReg X Z M ↦ if free s.2 then (1 : ℂ) else 0) =
        (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ) ⊗ₖ
          diagonal fun b : Hw X Z × M ↦ if free b then 1 else 0 :=
      (one_kron_diagonal_snd (fun b : Hw X Z × M ↦ if free b then (1 : ℂ) else 0)).symm
    rw [hC1, hW1, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, hdiag, compressReg,
      ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
  have hK' : C1 * K * C1 = (1 : Matrix Unit Unit ℂ) ⊗ₖ
      clsKraus p φ fun b ↦ compressDbs X Z * R b * compressDbs X Z := by
    rw [hC1, hK, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
      compressReg, kron_one_mul_clsKraus_dec, clsKraus_mul_kron_one_dec]
  have h0 : P1 * (C1 * K * C1) * W1 = 0 := by
    rw [hK', hP1, hW1, one_kron_diagonal_snd, one_kron_diagonal_snd]
    ext a b
    rw [mul_diagonal, diagonal_mul, Matrix.zero_apply]
    by_cases hab : ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        clsKraus p φ fun b ↦ compressDbs X Z * R b * compressDbs X Z) a b = 0
    · rw [hab, mul_zero, zero_mul]
    · by_cases hb : free b.2.2
      · have h1 := (one_kronecker_ne_zero (a := b.1) (a' := a.1) (b := b.2) (b' := a.2) hab).2
        rw [clsKraus_apply] at h1
        split_ifs at h1 with hc
        · obtain ⟨hD, hF⟩ := hR _ _ _ h1 hb
          have ha : a.2 ∉ E := by
            rw [hE, hD]
            exact hF
          simp [ha]
        · exact absurd rfl h1
      · simp [hb]
  rw [hQ]
  have e : C1 * P1 * C1 * K * W1 = C1 * (P1 * (C1 * K * C1) * W1) * C1 := by
    rw [show C1 * (P1 * (C1 * K * C1) * W1) * C1 = C1 * P1 * C1 * K * (C1 * (W1 * C1)) by
      simp only [Matrix.mul_assoc], ← hW, ← Matrix.mul_assoc C1 C1 W1, hCC, Matrix.one_mul]
  rw [e, h0, Matrix.mul_zero, Matrix.zero_mul]

/-- **A read outside the event, on a free cell, leaves the decompressed event empty**: the read
of cell `c` with outcome `r`, from a register whose cell `c` is not hardwired, projects the
decompressed cell on the outcome; if no database with that content is in `F`, the decompressed
event `E = {s | F s.1}` is annihilated. -/
theorem hwDecProj_mul_hwReadKraus_mul_eq_zero (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    (F : DbReg X Z → Prop) (hE : ∀ s, s ∈ E ↔ F s.1) (c : HwRead X Z M) (r : c.Result)
    (hout : ∀ D, c.Hit r D → ¬ F D) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj E) * hwReadKraus c r *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ diagonal fun s : HwReg X Z M ↦ if c.Free s.2 then 1 else 0) =
        0 := by
  cases c with
  | readH z upd =>
    refine one_kron_hwDecProj_mul_clsKraus_mul_eq_zero E F hE (fun b ↦ b.2 = r.2)
      (fun b ↦ (b.1, upd r.2 r.1)) (fun b ↦ cellRead b.1.1 z r.1 ⊗ₖ 1)
      (HwRead.Free (.readH z upd)) fun b D' D h hb ↦ ?_
    obtain ⟨rfl, hD⟩ := compressDbs_readH_ne_zero h
    refine ⟨rfl, hout D' ?_⟩
    change b.1.1 z = none at hb
    rw [hb, Option.none_or] at hD
    exact hD
  | readK x upd =>
    refine one_kron_hwDecProj_mul_clsKraus_mul_eq_zero E F hE (fun b ↦ b.2 = r.2)
      (fun b ↦ (b.1, upd r.2 r.1)) (fun b ↦ 1 ⊗ₖ (cellRead b.1.2.1 x r.1 ⊗ₖ 1))
      (HwRead.Free (.readK x upd)) fun b D' D h hb ↦ ?_
    obtain ⟨rfl, hD⟩ := compressDbs_readK_ne_zero h
    refine ⟨rfl, hout D' ?_⟩
    change b.1.2.1 x = none at hb
    rw [hb, Option.none_or] at hD
    exact hD
  | readK' x upd =>
    refine one_kron_hwDecProj_mul_clsKraus_mul_eq_zero E F hE (fun b ↦ b.2 = r.2)
      (fun b ↦ (b.1, upd r.2 r.1)) (fun b ↦ 1 ⊗ₖ (1 ⊗ₖ cellRead b.1.2.2 x r.1))
      (HwRead.Free (.readK' x upd)) fun b D' D h hb ↦ ?_
    obtain ⟨rfl, hD⟩ := compressDbs_readK'_ne_zero h
    refine ⟨rfl, hout D' ?_⟩
    change b.1.2.2 x = none at hb
    rw [hb, Option.none_or] at hD
    exact hD

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] [DecidableEq M] in
/-- A framed Kraus step after a support projection: if `Q K W = 0` and `σ` is supported by `W`
(on the left factor), the framed step leaves an operator annihilated by `Q`. -/
theorem amplify_conj_conj_eq_zero {α β E : Type} [Fintype α] [Fintype β] [Fintype E]
    [DecidableEq E] {K : Matrix β α ℂ} {Q : Matrix β β ℂ} {W : Matrix α α ℂ} (h : Q * K * W = 0)
    {σ : Matrix (α × E) (α × E) ℂ} (hσ : (MatrixMap.conj W).amplify E σ = σ) :
    (MatrixMap.conj Q).amplify E ((MatrixMap.conj K).amplify E σ) = 0 := by
  rw [← hσ, ← LinearMap.comp_apply ((MatrixMap.conj Q).amplify E), ← MatrixMap.amplify_comp,
    ← LinearMap.comp_apply (MatrixMap.amplify (MatrixMap.conj Q ∘ₗ MatrixMap.conj K) E),
    ← MatrixMap.amplify_comp, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul, h]
  ext a b
  rw [MatrixMap.amplify_apply, MatrixMap.conj_apply]
  simp

/-- **The start of the persistence, at a read call.** In the hardwired runtime extended by `step`,
a read of cell `c` presented an operator supported where `c` is not hardwired (`hσ`), with an
outcome `r` outside `F` (`hout`), leaves on branch `r` an operator on which the decompressed event
`E = {s | F s.1}` has weight zero: the premise `h0` of `forallQueries_hwDecProj_eq_zero` for the
continuation of the call. -/
theorem conj_queryStep_read_eq_zero {t : QuantumOracleSpec.{0, 0}} (W₀ : Hw X Z) (m₀ : M)
    (step : ∀ j : t.Port, SubInstrument (t.In j × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (t.Out j × (spongeHardwiredRuntime X Z W₀ m₀).D) (t.Result j))
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)] (F : DbReg X Z → Prop)
    (hE : ∀ s, s ∈ E ↔ F s.1) (c : HwRead X Z M)
    (r : ((hwSpec X Z M).sum t).Result (.inl (.inl (.inr c))))
    (hout : ∀ D, c.Hit r D → ¬ F D) {B : QReg} (E' : QReg)
    (ℓ : B ≃ ((hwSpec X Z M).sum t).In (.inl (.inl (.inr c))) × E')
    (ρ : Matrix (B × ((spongeHardwiredRuntime X Z W₀ m₀).extend step).D)
      (B × ((spongeHardwiredRuntime X Z W₀ m₀).extend step).D) ℂ)
    (hσ : (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        diagonal fun s : HwReg X Z M ↦ if c.Free s.2 then 1 else 0)).amplify E'
          ((SubInstrument.relabel (queryEquivIn ℓ
            ((spongeHardwiredRuntime X Z W₀ m₀).extend step).D)).branch () ρ) =
        (SubInstrument.relabel (queryEquivIn ℓ
          ((spongeHardwiredRuntime X Z W₀ m₀).extend step).D)).branch () ρ) :
    (MatrixMap.conj (hwDecProj E)).amplifyLeft _
      ((((spongeHardwiredRuntime X Z W₀ m₀).extend step).queryStep (.inl (.inl (.inr c))) E'
        ℓ).branch r ρ) = 0 := by
  have hb : (((spongeHardwiredRuntime X Z W₀ m₀).extend step).step
      (.inl (.inl (.inr c)))).branch r = MatrixMap.conj (hwReadKraus c r) :=
    spongeHardwiredRuntime_step_read W₀ m₀ c r
  have h0 : ((MatrixMap.conj (hwDecProj E)).amplifyLeft Unit).amplify E'
      ((MatrixMap.conj (hwReadKraus c r)).amplify E'
        ((SubInstrument.relabel (queryEquivIn ℓ
          ((spongeHardwiredRuntime X Z W₀ m₀).extend step).D)).branch () ρ)) = 0 := by
    rw [MatrixMap.amplifyLeft_conj]
    exact amplify_conj_conj_eq_zero (hwDecProj_mul_hwReadKraus_mul_eq_zero E F hE c r hout) hσ
  rw [queryStep_branch_apply]
  calc _ = (SubInstrument.relabel (queryEquivOut Unit
        ((spongeHardwiredRuntime X Z W₀ m₀).extend step).D E')).branch ()
          (((MatrixMap.conj (hwDecProj E)).amplifyLeft Unit).amplify E'
            ((MatrixMap.conj (hwReadKraus c r)).amplify E'
              ((SubInstrument.relabel (queryEquivIn ℓ
                ((spongeHardwiredRuntime X Z W₀ m₀).extend step).D)).branch () ρ))) := by
        rw [← hb]
        exact (LinearMap.congr_fun (intertwines_relabel_queryEquivOut
          (MatrixMap.conj (hwDecProj E)) Unit E' ()) _).symm
    _ = 0 := by
      rw [h0]
      exact map_zero _

end ports

/-! ## One cell: the recorded values, the uniform superposition, an event -/

section oneCell

variable (Y : Type) [Fintype Y] [DecidableEq Y]

/-- The projector on the recorded values of one cell. -/
noncomputable def cellSomeProj : Matrix (Option Y) (Option Y) ℂ :=
  diagonal fun o ↦ if o.isSome then 1 else 0

/-- The projector on the uniform superposition of the values of one cell. -/
noncomputable def cellUnifProj : Matrix (Option Y) (Option Y) ℂ :=
  Matrix.of fun a b ↦ cellUniform Y a * cellUniform Y b

variable {Y}

/-- The projector on the cell contents satisfying `g`. -/
noncomputable def cellIndProj (g : Option Y → Prop) [DecidablePred g] :
    Matrix (Option Y) (Option Y) ℂ :=
  diagonal fun o ↦ if g o then 1 else 0

/-- **The conversion constant**: the fraction of the values `y` with `g (some y)`. -/
noncomputable def cellFrac (g : Option Y → Prop) [DecidablePred g] : ℝ :=
  ((Finset.univ.filter fun y ↦ g (some y)).card : ℝ) / Fintype.card Y

omit [DecidableEq Y] in
theorem cellFrac_nonneg (g : Option Y → Prop) [DecidablePred g] : 0 ≤ cellFrac g :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **The compression on the recorded values**: `Π C Π = Π - U`. -/
theorem cellSomeProj_mul_cellCompress_mul :
    cellSomeProj Y * cellCompress Y * cellSomeProj Y = cellSomeProj Y - cellUnifProj Y := by
  ext a b
  simp only [cellSomeProj, cellUnifProj, mul_diagonal, diagonal_mul, Matrix.sub_apply, of_apply]
  rcases a with _ | y <;> rcases b with _ | y' <;>
    simp [diagonal_apply, cellAmp_mul_self]

omit [Fintype Y] in
theorem conjTranspose_cellIndProj (g : Option Y → Prop) [DecidablePred g] :
    (cellIndProj g)ᴴ = cellIndProj g := by
  rw [cellIndProj, diagonal_conjTranspose]
  congr 1
  funext o
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem cellIndProj_mul_self (g : Option Y → Prop) [DecidablePred g] :
    cellIndProj g * cellIndProj g = cellIndProj g := by
  rw [cellIndProj, diagonal_mul_diagonal]
  congr 1
  funext o
  split_ifs <;> simp

theorem cellSomeProj_mul_cellIndProj {g : Option Y → Prop} [DecidablePred g] (hg : ¬ g none) :
    cellSomeProj Y * cellIndProj g = cellIndProj g := by
  rw [cellSomeProj, cellIndProj, diagonal_mul_diagonal]
  congr 1
  funext o
  rcases o with _ | y
  · simp [hg]
  · simp

theorem cellIndProj_mul_cellSomeProj {g : Option Y → Prop} [DecidablePred g] (hg : ¬ g none) :
    cellIndProj g * cellSomeProj Y = cellIndProj g := by
  rw [cellSomeProj, cellIndProj, diagonal_mul_diagonal]
  congr 1
  funext o
  rcases o with _ | y
  · simp [hg]
  · simp

omit [DecidableEq Y] in
theorem conjTranspose_cellUnifProj : (cellUnifProj Y)ᴴ = cellUnifProj Y := by
  ext a b
  rcases a with _ | y <;> rcases b with _ | y' <;>
    simp [cellUnifProj, conjTranspose_apply]

omit [DecidableEq Y] in
theorem sum_cellUniform_mul_ind (g : Option Y → Prop) [DecidablePred g] :
    ∑ c, cellUniform Y c * (if g c then (1 : ℂ) else 0) * cellUniform Y c = cellFrac g := by
  rw [Fintype.sum_option]
  simp only [cellUniform_none, zero_mul, zero_add, cellUniform_some]
  have h : ∀ y : Y, cellAmp Y * (if g (some y) then (1 : ℂ) else 0) * cellAmp Y =
      (if g (some y) then (1 : ℂ) else 0) * (Fintype.card Y : ℂ)⁻¹ := fun y ↦ by
    rw [← cellAmp_mul_self]
    ring
  rw [Finset.sum_congr rfl fun y _ ↦ h y, ← Finset.sum_mul, Finset.sum_boole, cellFrac]
  push_cast
  rw [div_eq_mul_inv]

/-- **The uniform superposition sees the fraction of the event**: `U G U = κ U`. -/
theorem cellUnifProj_mul_cellIndProj_mul (g : Option Y → Prop) [DecidablePred g] :
    cellUnifProj Y * cellIndProj g * cellUnifProj Y = (cellFrac g : ℂ) • cellUnifProj Y := by
  ext a b
  rw [cellIndProj, Matrix.mul_apply]
  simp only [mul_diagonal, cellUnifProj, of_apply, Matrix.smul_apply, smul_eq_mul]
  have h : ∀ c, cellUniform Y a * cellUniform Y c * (if g c then (1 : ℂ) else 0) *
      (cellUniform Y c * cellUniform Y b) = cellUniform Y c * (if g c then (1 : ℂ) else 0) *
        cellUniform Y c * (cellUniform Y a * cellUniform Y b) := fun c ↦ by ring
  rw [Finset.sum_congr rfl fun c _ ↦ h c, ← Finset.sum_mul, sum_cellUniform_mul_ind]

variable [Nonempty Y]

omit [DecidableEq Y] in
theorem cellUnifProj_mul_self : cellUnifProj Y * cellUnifProj Y = cellUnifProj Y := by
  have hs : ∑ c, cellUniform Y c * cellUniform Y c = 1 := by
    rw [Fintype.sum_option]
    simp only [cellUniform_none, mul_zero, zero_add, cellUniform_some, cellAmp_mul_self,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  ext a b
  simp only [cellUnifProj, Matrix.mul_apply, of_apply]
  have h : ∀ c, cellUniform Y a * cellUniform Y c * (cellUniform Y c * cellUniform Y b) =
      cellUniform Y c * cellUniform Y c * (cellUniform Y a * cellUniform Y b) := fun c ↦ by ring
  rw [Finset.sum_congr rfl fun c _ ↦ h c, ← Finset.sum_mul, hs, one_mul]

end oneCell

/-! ## Operators on one cell of a register -/

section lift

variable {N Y R : Type}

open scoped Classical in
/-- An operator on the cell split off a register by `e`, the identity on the rest. -/
noncomputable def liftCell (e : N ≃ Option Y × R) (A : Matrix (Option Y) (Option Y) ℂ) :
    Matrix N N ℂ :=
  (A ⊗ₖ (1 : Matrix R R ℂ)).submatrix e e

open scoped Classical in
theorem liftCell_apply (e : N ≃ Option Y × R) (A : Matrix (Option Y) (Option Y) ℂ) (a b : N) :
    liftCell e A a b = A (e a).1 (e b).1 * (1 : Matrix R R ℂ) (e a).2 (e b).2 := by
  rw [liftCell, submatrix_apply, kroneckerMap_apply]

theorem liftCell_mul [Fintype N] [Fintype Y] (e : N ≃ Option Y × R)
    (A B : Matrix (Option Y) (Option Y) ℂ) :
    liftCell e A * liftCell e B = liftCell e (A * B) := by
  classical
  let _ : Fintype R := Fintype.ofSurjective (fun a : N ↦ (e a).2) fun r ↦
    ⟨e.symm (none, r), by simp⟩
  rw [liftCell, liftCell, liftCell, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.mul_one]

open scoped Classical in
theorem conjTranspose_liftCell (e : N ≃ Option Y × R) (A : Matrix (Option Y) (Option Y) ℂ) :
    (liftCell e A)ᴴ = liftCell e Aᴴ := by
  rw [liftCell, liftCell, conjTranspose_submatrix, conjTranspose_kronecker, conjTranspose_one]

theorem liftCell_sub (e : N ≃ Option Y × R) (A B : Matrix (Option Y) (Option Y) ℂ) :
    liftCell e (A - B) = liftCell e A - liftCell e B := by
  ext a b
  simp only [liftCell_apply, Matrix.sub_apply, sub_mul]

theorem liftCell_smul (e : N ≃ Option Y × R) (z : ℂ) (A : Matrix (Option Y) (Option Y) ℂ) :
    liftCell e (z • A) = z • liftCell e A := by
  ext a b
  simp only [liftCell_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

open scoped Classical in
/-- A diagonal operator on the cell is the diagonal operator of the cell content. -/
theorem liftCell_diagonal [DecidableEq N] [DecidableEq Y] (e : N ≃ Option Y × R)
    (d : Option Y → ℂ) : liftCell e (diagonal d) = diagonal fun a ↦ d (e a).1 := by
  ext a b
  rw [liftCell_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [diagonal_apply_ne _ hab]
    by_cases h₁ : (e a).1 = (e b).1
    · have h₂ : (e a).2 ≠ (e b).2 := fun h₂ ↦ hab (e.injective (Prod.ext h₁ h₂))
      rw [Matrix.one_apply_ne h₂, mul_zero]
    · rw [diagonal_apply_ne _ h₁, zero_mul]

/-- The cell split off the left factor of `N × Q`. -/
def lensR (Q : Type) (e : N ≃ Option Y × R) : N × Q ≃ Option Y × (R × Q) where
  toFun a := ((e a.1).1, (e a.1).2, a.2)
  invFun b := (e.symm (b.1, b.2.1), b.2.2)
  left_inv a := by simp
  right_inv b := by simp

/-- The cell split off the right factor of `P × N`. -/
def lensL (P : Type) (e : N ≃ Option Y × R) : P × N ≃ Option Y × (P × R) where
  toFun a := ((e a.2).1, a.1, (e a.2).2)
  invFun b := (b.2.1, e.symm (b.1, b.2.2))
  left_inv a := by simp
  right_inv b := by simp

theorem lensR_apply (Q : Type) (e : N ≃ Option Y × R) (a : N) (q : Q) :
    lensR Q e (a, q) = ((e a).1, (e a).2, q) :=
  rfl

theorem lensL_apply (P : Type) (e : N ≃ Option Y × R) (p : P) (a : N) :
    lensL P e (p, a) = ((e a).1, p, (e a).2) :=
  rfl

open scoped Classical in
theorem liftCell_kron_one {Q : Type} [DecidableEq Q] (e : N ≃ Option Y × R)
    (A : Matrix (Option Y) (Option Y) ℂ) :
    liftCell e A ⊗ₖ (1 : Matrix Q Q ℂ) = liftCell (lensR Q e) A := by
  ext ⟨a, q⟩ ⟨b, q'⟩
  rw [kroneckerMap_apply, liftCell_apply, liftCell_apply, lensR_apply, lensR_apply]
  by_cases h₁ : (e a).2 = (e b).2 <;> by_cases h₂ : q = q' <;> simp [Matrix.one_apply, h₁, h₂]

open scoped Classical in
theorem one_kron_liftCell {P : Type} [DecidableEq P] (e : N ≃ Option Y × R)
    (A : Matrix (Option Y) (Option Y) ℂ) :
    (1 : Matrix P P ℂ) ⊗ₖ liftCell e A = liftCell (lensL P e) A := by
  ext ⟨p, a⟩ ⟨p', b⟩
  rw [kroneckerMap_apply, liftCell_apply, liftCell_apply, lensL_apply, lensL_apply]
  by_cases h₁ : p = p' <;> by_cases h₂ : (e a).2 = (e b).2 <;> simp [Matrix.one_apply, h₁, h₂]

end lift

/-! ## One cell of a database -/

section db

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]

omit [Fintype Y] in
/-- An event on one cell of a database, as an operator on the cell. -/
theorem diagonal_cell_eq_liftCell (a : A) (d : Option Y → ℂ) :
    (diagonal fun D : Database A Y ↦ d (D a)) =
      liftCell (Equiv.funSplitAt a (Option Y)) (diagonal d) := by
  rw [liftCell_diagonal]
  rfl

/-- Compressing every cell is compressing the split cell and the others. -/
theorem compressAll_eq_liftCell (a : A) :
    compressAll A Y = (cellCompress Y ⊗ₖ piKron fun _ : {j // j ≠ a} ↦ cellCompress Y).submatrix
      (Equiv.funSplitAt a (Option Y)) (Equiv.funSplitAt a (Option Y)) := by
  ext D D'
  rw [compressAll, submatrix_apply, kroneckerMap_apply, piKron_apply, piKron_apply,
    Fintype.prod_eq_mul_prod_subtype_ne _ a]
  rfl

/-- The identity matrix does not depend on the decidable equality used to build it. -/
theorem matrix_one_inst {T : Type} (d₁ d₂ : DecidableEq T) :
    @OfNat.ofNat (Matrix T T ℂ) 1 (@One.toOfNat1 _ (@Matrix.one T ℂ d₁ _ _)) =
      @OfNat.ofNat (Matrix T T ℂ) 1 (@One.toOfNat1 _ (@Matrix.one T ℂ d₂ _ _)) := by
  obtain rfl := Subsingleton.elim d₁ d₂
  rfl

variable [Nonempty Y]

/-- **Compressing every cell around an operator on one cell** compresses that cell only. -/
theorem compressAll_mul_liftCell_mul (a : A) (B : Matrix (Option Y) (Option Y) ℂ) :
    compressAll A Y * liftCell (Equiv.funSplitAt a (Option Y)) B * compressAll A Y =
      liftCell (Equiv.funSplitAt a (Option Y)) (cellCompress Y * B * cellCompress Y) := by
  rw [compressAll_eq_liftCell a, liftCell, liftCell, submatrix_mul_equiv, submatrix_mul_equiv,
    ← mul_kronecker_mul, ← mul_kronecker_mul,
    matrix_one_inst (T := {j // j ≠ a} → Option Y) _ inferInstance, Matrix.mul_one, piKron_mul]
  simp only [cellCompress_mul_self, piKron_one]

end db

/-! ## Recorded weight against decompressed weight -/

section convert

/-- **The conversion inequality, abstractly.** With `Π` (recorded values), `U` (uniform
superposition), `G` (event, inside the recorded values) projectors and `U G U = κ U`, an operator
`M` with `Π M Π = (Π - U) G (Π - U)` has weight at most `(√tr(G σ) + √(κ tr σ))²` on a positive
semidefinite `σ` supported in `Π`. -/
theorem re_trace_le_of_cellRel {N : Type} [Fintype N] [DecidableEq N]
    {Pi U G M σ : Matrix N N ℂ} {k : ℝ} (hk : 0 ≤ k) (hG : Gᴴ = G) (hGG : G * G = G)
    (hPiG : Pi * G = G) (hGPi : G * Pi = G) (hU : Uᴴ = U) (hUU : U * U = U)
    (hUGU : U * G * U = (k : ℂ) • U) (hM : Pi * M * Pi = (Pi - U) * G * (Pi - U))
    (hσ : σ.PosSemidef) (hsupp : Pi * σ * Pi = σ) :
    (M * σ).trace.re ≤ (√(G * σ).trace.re + √(k * σ.trace.re)) ^ 2 := by
  set t : Matrix N N ℂ → ℝ := fun B ↦ (B * σ).trace.re with ht
  have tadd : ∀ B B', t (B + B') = t B + t B' := fun B B' ↦ by
    simp only [ht, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  have tsub : ∀ B B', t (B - B') = t B - t B' := fun B B' ↦ by
    simp only [ht, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  have tsmul : ∀ (r : ℝ) B, t ((r : ℂ) • B) = r * t B := fun r B ↦ by
    simp only [ht, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have tpos : ∀ B : Matrix N N ℂ, 0 ≤ t (B * Bᴴ) := fun B ↦
    (posSemidef_self_mul_conjTranspose B).trace_mul_re_nonneg hσ
  have hx : t M = t ((Pi - U) * G * (Pi - U)) := by
    rw [← hM]
    simp only [ht]
    conv_lhs => rw [← hsupp]
    rw [show M * (Pi * σ * Pi) = M * Pi * σ * Pi by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show Pi * (M * Pi * σ) = Pi * M * Pi * σ by
        simp only [Matrix.mul_assoc]]
  have hexp : (Pi - U) * G * (Pi - U) = G - G * U - U * G + U * G * U := by
    rw [Matrix.sub_mul Pi U G, hPiG, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hGPi,
      Matrix.mul_assoc U G Pi, hGPi]
    abel
  have ha : 0 ≤ t G := by
    have h := tpos G
    rwa [hG, hGG] at h
  have h1U : (1 - U) * (1 - U)ᴴ = 1 - U := by
    rw [conjTranspose_sub, conjTranspose_one, hU, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hUU]
    abel
  have htr : t 1 = σ.trace.re := by simp only [ht, Matrix.one_mul]
  have hUle : t U ≤ σ.trace.re := by
    have h := tpos (1 - U)
    rw [h1U, tsub, htr] at h
    linarith
  have hU0 : 0 ≤ t U := by
    have h := tpos U
    rwa [hU, hUU] at h
  have hσ0 : 0 ≤ σ.trace.re := hσ.trace_re_nonneg
  have hUGUt : t (U * G * U) = k * t U := by rw [hUGU, tsmul]
  have hUGG : U * G * G = U * G := by rw [Matrix.mul_assoc, hGG]
  refine Real.le_sq_sqrt_add_sqrt_of_forall ha (mul_nonneg hk hσ0) fun s hs ↦ ?_
  show t M ≤ (1 + s) * t G + (1 + s⁻¹) * (k * σ.trace.re)
  set c : ℂ := ((s⁻¹ : ℝ) : ℂ) with hc
  have hTh : (G + c • (U * G))ᴴ = G + c • (G * U) := by
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_mul, hG, hU, hc, Complex.star_def,
      Complex.conj_ofReal]
  have hTT : (G + c • (U * G)) * (G + c • (U * G))ᴴ =
      G + c • (G * U) + (c • (U * G) + ((s⁻¹ * s⁻¹ : ℝ) : ℂ) • (U * G * U)) := by
    rw [hTh, Complex.ofReal_mul, ← hc]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.mul_assoc, hGG, hUGG]
    rw [smul_add, smul_smul]
    abel
  have h0 := tpos (G + c • (U * G))
  rw [hTT, tadd, tadd, tadd, hc, tsmul, tsmul, tsmul, hUGUt] at h0
  rw [hx, hexp, tadd, tsub, tsub, hUGUt]
  have hs' : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have h0' := mul_nonneg hs.le h0
  have e1 : s * (t G + (s⁻¹ * t (G * U) + (s⁻¹ * t (U * G) + s⁻¹ * s⁻¹ * (k * t U)))) =
      s * t G + (s * s⁻¹) * t (G * U) + (s * s⁻¹) * t (U * G) +
        (s * s⁻¹) * (s⁻¹ * (k * t U)) := by ring
  rw [hs'] at e1
  have hkU : k * t U ≤ k * σ.trace.re := mul_le_mul_of_nonneg_left hUle hk
  have hkU' : s⁻¹ * (k * t U) ≤ s⁻¹ * (k * σ.trace.re) :=
    mul_le_mul_of_nonneg_left hkU (inv_nonneg.mpr hs.le)
  nlinarith [h0', e1, hkU, hkU']

/-- **The conversion inequality on a register.** Let `e` split a cell off the register, `C` an
involution (the compression), `G` the compressed projector "the cell is recorded with a content
in `g`" and `C G C` the decompressed one, both acting on the cell through `e`
(`hG`, `hCGC`). On a positive semidefinite `σ` whose decompressed form `C σ C` has no `⊥` at the
cell, the recorded weight is at most `(√(decompressed weight) + √(κ tr σ))²`,
`κ = cellFrac g`. -/
theorem re_trace_cellInd_le {N Y R : Type} [Fintype N] [DecidableEq N] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] (e : N ≃ Option Y × R)
    {C G : Matrix N N ℂ} (hCC : C * C = 1) (hCh : Cᴴ = C) (g : Option Y → Prop) [DecidablePred g]
    (hg : ¬ g none) (hG : G = liftCell e (cellIndProj g))
    (hCGC : C * G * C = liftCell e (cellCompress Y * cellIndProj g * cellCompress Y))
    {σ : Matrix N N ℂ} (hσ : σ.PosSemidef)
    (hnb : ∀ a b, (C * σ * C) a b ≠ 0 → ((e a).1).isSome ∧ ((e b).1).isSome) :
    (G * σ).trace.re ≤ (√((C * G * C) * σ).trace.re + √(cellFrac g * σ.trace.re)) ^ 2 := by
  set σ' := C * σ * C with hσ'
  have hσ'psd : σ'.PosSemidef := by
    have h := hσ.mul_mul_conjTranspose_same C
    rwa [hCh] at h
  have hcomp : (G * σ).trace = (C * G * C * σ').trace := by
    have h : C * G * C * (C * σ * C) = C * (G * σ) * C := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc C C (σ * C), hCC, Matrix.one_mul]
    rw [hσ', h, Matrix.trace_mul_comm (C * (G * σ)) C, ← Matrix.mul_assoc C C (G * σ), hCC,
      Matrix.one_mul]
  have hdec : (C * G * C * σ).trace = (G * σ').trace := by
    rw [hσ', show C * G * C * σ = C * (G * C * σ) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm C (G * C * σ)]
    simp only [Matrix.mul_assoc]
  have htr : σ.trace = σ'.trace := by
    rw [hσ', Matrix.trace_mul_comm (C * σ) C, ← Matrix.mul_assoc C C σ, hCC, Matrix.one_mul]
  have hsupp : liftCell e (cellSomeProj Y) * σ' * liftCell e (cellSomeProj Y) = σ' := by
    rw [cellSomeProj, liftCell_diagonal]
    ext a b
    rw [mul_diagonal, diagonal_mul]
    by_cases h : σ' a b = 0
    · rw [h, mul_zero, zero_mul]
    · obtain ⟨ha, hb⟩ := hnb a b h
      simp [ha, hb]
  have hM0 : cellSomeProj Y * (cellCompress Y * cellIndProj g * cellCompress Y) *
      cellSomeProj Y = (cellSomeProj Y - cellUnifProj Y) * cellIndProj g *
        (cellSomeProj Y - cellUnifProj Y) := by
    have hG' : cellIndProj g = cellSomeProj Y * cellIndProj g * cellSomeProj Y := by
      rw [cellSomeProj_mul_cellIndProj hg, cellIndProj_mul_cellSomeProj hg]
    have h : cellSomeProj Y * (cellCompress Y * cellIndProj g * cellCompress Y) *
        cellSomeProj Y = (cellSomeProj Y * cellCompress Y * cellSomeProj Y) * cellIndProj g *
          (cellSomeProj Y * cellCompress Y * cellSomeProj Y) := by
      conv_lhs => rw [hG']
      simp only [Matrix.mul_assoc]
    rw [h, cellSomeProj_mul_cellCompress_mul]
  have core := re_trace_le_of_cellRel (Pi := liftCell e (cellSomeProj Y))
    (U := liftCell e (cellUnifProj Y)) (G := liftCell e (cellIndProj g))
    (M := liftCell e (cellCompress Y * cellIndProj g * cellCompress Y)) (cellFrac_nonneg g)
    (by rw [conjTranspose_liftCell, conjTranspose_cellIndProj])
    (by rw [liftCell_mul, cellIndProj_mul_self])
    (by rw [liftCell_mul, cellSomeProj_mul_cellIndProj hg])
    (by rw [liftCell_mul, cellIndProj_mul_cellSomeProj hg])
    (by rw [conjTranspose_liftCell, conjTranspose_cellUnifProj])
    (by rw [liftCell_mul, cellUnifProj_mul_self])
    (by rw [liftCell_mul, liftCell_mul, cellUnifProj_mul_cellIndProj_mul, liftCell_smul])
    (by rw [liftCell_mul, liftCell_mul, ← liftCell_sub, liftCell_mul, liftCell_mul, hM0])
    hσ'psd hsupp
  rw [hcomp, hdec, htr, hCGC, hG]
  exact core

end convert

/-! ## The three kinds of cells of the hardwired register -/

section kinds

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {n : Type} [Fintype n] [DecidableEq n] {M : Type} [Fintype M] [DecidableEq M]

variable (n M) in
/-- Cell `z` of `h` split off `n × HwReg X Z M`. -/
def lensH (z : Z) :=
  lensL n (lensR (Hw X Z × M) (lensR (Database X Z × Database X Z)
    (Equiv.funSplitAt z (Option X))))

variable (n M) in
/-- Cell `x` of `k` split off `n × HwReg X Z M`. -/
def lensK (x : X) :=
  lensL n (lensR (Hw X Z × M) (lensL (Database Z X) (lensR (Database X Z)
    (Equiv.funSplitAt x (Option Z)))))

variable (n M) in
/-- Cell `x` of `k'` split off `n × HwReg X Z M`. -/
def lensK' (x : X) :=
  lensL n (lensR (Hw X Z × M) (lensL (Database Z X) (lensL (Database X Z)
    (Equiv.funSplitAt x (Option Z)))))

omit [Fintype n] [Fintype M] in
theorem one_kron_diagonal_eq_liftCell {Y R : Type} [DecidableEq Y]
    (e : n × HwReg X Z M ≃ Option Y × R) (cell : HwReg X Z M → Option Y)
    (he : ∀ a, (e a).1 = cell a.2) (d : Option Y → ℂ) :
    (1 : Matrix n n ℂ) ⊗ₖ diagonal (fun s : HwReg X Z M ↦ d (cell s)) =
      liftCell e (diagonal d) := by
  rw [liftCell_diagonal, ← diagonal_one, diagonal_kronecker_diagonal]
  congr 1
  funext a
  rw [one_mul, he]

variable [AddCommGroup X] [AddCommGroup Z]

theorem one_kron_compressReg_mul_self :
    ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) * ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) = 1 := by
  rw [← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]

omit [Fintype n] [AddCommGroup X] [AddCommGroup Z] in
theorem conjTranspose_one_kron_compressReg :
    ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M)ᴴ = (1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M := by
  rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressReg]

omit [AddCommGroup X] [AddCommGroup Z] in
theorem one_kron_hwDecProj_eq {Y : Type} (cell : HwReg X Z M → Option Y) (g : Option Y → Prop)
    [DecidablePred g] :
    (1 : Matrix n n ℂ) ⊗ₖ hwDecProj {s : HwReg X Z M | g (cell s)} =
      ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) *
        ((1 : Matrix n n ℂ) ⊗ₖ diagonal fun s : HwReg X Z M ↦ if g (cell s) then 1 else 0) *
          ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) := by
  rw [hwDecProj, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  rfl

theorem conj_lensH (z : Z) (B : Matrix (Option X) (Option X) ℂ) :
    ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) * liftCell (lensH n M z) B *
        ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) =
      liftCell (lensH n M z) (cellCompress X * B * cellCompress X) := by
  have hL : ∀ B' : Matrix (Option X) (Option X) ℂ, liftCell (lensH n M z) B' =
      (1 : Matrix n n ℂ) ⊗ₖ ((liftCell (Equiv.funSplitAt z (Option X)) B' ⊗ₖ
        (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ)) ⊗ₖ
          (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ)) := fun B' ↦ by
    rw [liftCell_kron_one, liftCell_kron_one, one_kron_liftCell]
    rfl
  rw [hL, hL, compressReg, compressDbs]
  simp only [← mul_kronecker_mul, Matrix.mul_one, compressAll_mul_self, one_kronecker_one,
    compressAll_mul_liftCell_mul]

theorem conj_lensK (x : X) (B : Matrix (Option Z) (Option Z) ℂ) :
    ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) * liftCell (lensK n M x) B *
        ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) =
      liftCell (lensK n M x) (cellCompress Z * B * cellCompress Z) := by
  have hL : ∀ B' : Matrix (Option Z) (Option Z) ℂ, liftCell (lensK n M x) B' =
      (1 : Matrix n n ℂ) ⊗ₖ (((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        (liftCell (Equiv.funSplitAt x (Option Z)) B' ⊗ₖ
          (1 : Matrix (Database X Z) (Database X Z) ℂ))) ⊗ₖ
            (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ)) := fun B' ↦ by
    rw [liftCell_kron_one, one_kron_liftCell, liftCell_kron_one, one_kron_liftCell]
    rfl
  rw [hL, hL, compressReg, compressDbs]
  simp only [← mul_kronecker_mul, Matrix.mul_one, compressAll_mul_self,
    compressAll_mul_liftCell_mul]

theorem conj_lensK' (x : X) (B : Matrix (Option Z) (Option Z) ℂ) :
    ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) * liftCell (lensK' n M x) B *
        ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) =
      liftCell (lensK' n M x) (cellCompress Z * B * cellCompress Z) := by
  have hL : ∀ B' : Matrix (Option Z) (Option Z) ℂ, liftCell (lensK' n M x) B' =
      (1 : Matrix n n ℂ) ⊗ₖ (((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ
          liftCell (Equiv.funSplitAt x (Option Z)) B')) ⊗ₖ
            (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ)) := fun B' ↦ by
    rw [one_kron_liftCell, one_kron_liftCell, liftCell_kron_one, one_kron_liftCell]
    rfl
  rw [hL, hL, compressReg, compressDbs]
  simp only [← mul_kronecker_mul, Matrix.mul_one, compressAll_mul_self,
    compressAll_mul_liftCell_mul]

/-- **Recorded weight at cell `z` of `h` (Consequence 2, one operator).** For an operator `σ` on
`n × HwReg X Z M` whose decompressed form has no `⊥` at `z` (from `noBot_runtimeR`), the weight
of "cell `z` of `h` is recorded with a content in `g`" is at most
`(√(decompressed weight) + √(κ tr σ))²`, `κ = cellFrac g`. -/
theorem re_trace_recH_le (z : Z) (g : Option X → Prop) [DecidablePred g] (hg : ¬ g none)
    {σ : Matrix (n × HwReg X Z M) (n × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : QuerySupportedOn (fun m : n × HwReg X Z M ↦ m.2) {s | (s.1.1 z).isSome}
      (MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) σ)) :
    (((1 : Matrix n n ℂ) ⊗ₖ diagonal fun s : HwReg X Z M ↦ if g (s.1.1 z) then 1 else 0) *
        σ).trace.re ≤
      (√(((1 : Matrix n n ℂ) ⊗ₖ hwDecProj {s : HwReg X Z M | g (s.1.1 z)}) * σ).trace.re +
        √(cellFrac g * σ.trace.re)) ^ 2 := by
  have hG := one_kron_diagonal_eq_liftCell (n := n) (lensH n M z) (fun s ↦ s.1.1 z)
    (fun _ ↦ rfl) fun o ↦ if g o then 1 else 0
  rw [one_kron_hwDecProj_eq (fun s ↦ s.1.1 z) g]
  refine re_trace_cellInd_le (lensH n M z) one_kron_compressReg_mul_self
    conjTranspose_one_kron_compressReg g hg hG ?_ hσ fun a b h ↦ ?_
  · rw [hG, conj_lensH]
    rfl
  · rw [MatrixMap.conj_apply, conjTranspose_one_kron_compressReg] at hnb
    exact hnb a b h

/-- **Recorded weight at cell `x` of `k`**: as `re_trace_recH_le`. -/
theorem re_trace_recK_le (x : X) (g : Option Z → Prop) [DecidablePred g] (hg : ¬ g none)
    {σ : Matrix (n × HwReg X Z M) (n × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : QuerySupportedOn (fun m : n × HwReg X Z M ↦ m.2) {s | (s.1.2.1 x).isSome}
      (MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) σ)) :
    (((1 : Matrix n n ℂ) ⊗ₖ diagonal fun s : HwReg X Z M ↦ if g (s.1.2.1 x) then 1 else 0) *
        σ).trace.re ≤
      (√(((1 : Matrix n n ℂ) ⊗ₖ hwDecProj {s : HwReg X Z M | g (s.1.2.1 x)}) * σ).trace.re +
        √(cellFrac g * σ.trace.re)) ^ 2 := by
  have hG := one_kron_diagonal_eq_liftCell (n := n) (lensK n M x) (fun s ↦ s.1.2.1 x)
    (fun _ ↦ rfl) fun o ↦ if g o then 1 else 0
  rw [one_kron_hwDecProj_eq (fun s ↦ s.1.2.1 x) g]
  refine re_trace_cellInd_le (lensK n M x) one_kron_compressReg_mul_self
    conjTranspose_one_kron_compressReg g hg hG ?_ hσ fun a b h ↦ ?_
  · rw [hG, conj_lensK]
    rfl
  · rw [MatrixMap.conj_apply, conjTranspose_one_kron_compressReg] at hnb
    exact hnb a b h

/-- **Recorded weight at cell `x` of `k'`**: as `re_trace_recH_le`. -/
theorem re_trace_recK'_le (x : X) (g : Option Z → Prop) [DecidablePred g] (hg : ¬ g none)
    {σ : Matrix (n × HwReg X Z M) (n × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : QuerySupportedOn (fun m : n × HwReg X Z M ↦ m.2) {s | (s.1.2.2 x).isSome}
      (MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) σ)) :
    (((1 : Matrix n n ℂ) ⊗ₖ diagonal fun s : HwReg X Z M ↦ if g (s.1.2.2 x) then 1 else 0) *
        σ).trace.re ≤
      (√(((1 : Matrix n n ℂ) ⊗ₖ hwDecProj {s : HwReg X Z M | g (s.1.2.2 x)}) * σ).trace.re +
        √(cellFrac g * σ.trace.re)) ^ 2 := by
  have hG := one_kron_diagonal_eq_liftCell (n := n) (lensK' n M x) (fun s ↦ s.1.2.2 x)
    (fun _ ↦ rfl) fun o ↦ if g o then 1 else 0
  rw [one_kron_hwDecProj_eq (fun s ↦ s.1.2.2 x) g]
  refine re_trace_cellInd_le (lensK' n M x) one_kron_compressReg_mul_self
    conjTranspose_one_kron_compressReg g hg hG ?_ hσ fun a b h ↦ ?_
  · rw [hG, conj_lensK']
    rfl
  · rw [MatrixMap.conj_apply, conjTranspose_one_kron_compressReg] at hnb
    exact hnb a b h

end kinds

/-! ## Recorded weight along runs -/

section runs

/-- An operator annihilated by `1 ⊗ Q` (framed), `Q` a projector, has zero `Q` weight after
tracing out the frame. -/
theorem re_trace_one_kron_mul_traceRight_eq_zero {I D E : Type} [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D] [Fintype E] {Q : Matrix D D ℂ} (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    {σ : Matrix ((I × D) × E) ((I × D) × E) ℂ}
    (h : ((MatrixMap.conj Q).amplifyLeft I).amplify E σ = 0) :
    (((1 : Matrix I I ℂ) ⊗ₖ Q) * MatrixMap.traceRight (I × D) E σ).trace.re = 0 := by
  have h1 : (MatrixMap.conj Q).amplifyLeft I (MatrixMap.traceRight (I × D) E σ) = 0 := by
    have h2 := congrArg (MatrixMap.traceRight (I × D) E) h
    rwa [← LinearMap.comp_apply (MatrixMap.traceRight (I × D) E),
      MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply, map_zero] at h2
  have hK : ((1 : Matrix I I ℂ) ⊗ₖ Q)ᴴ = (1 : Matrix I I ℂ) ⊗ₖ Q := by
    rw [conjTranspose_kronecker, conjTranspose_one, hQ]
  have hKK : ((1 : Matrix I I ℂ) ⊗ₖ Q) * ((1 : Matrix I I ℂ) ⊗ₖ Q) =
      (1 : Matrix I I ℂ) ⊗ₖ Q := by
    rw [← mul_kronecker_mul, Matrix.one_mul, hQQ]
  rw [MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply, hK] at h1
  set K := (1 : Matrix I I ℂ) ⊗ₖ Q
  set τ := MatrixMap.traceRight (I × D) E σ
  rw [← hKK, Matrix.mul_assoc, Matrix.trace_mul_comm K (K * τ), h1, Matrix.trace_zero,
    Complex.zero_re]

theorem le_of_le_sq_sqrt_add {W a b : ℝ} (h : W ≤ (√a + √b) ^ 2) (ha : a = 0) (hb : 0 ≤ b) :
    W ≤ b := by
  rwa [ha, Real.sqrt_zero, zero_add, Real.sq_sqrt hb] at h

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {M : Type} [Fintype M] [DecidableEq M]
  {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **Recorded weight along runs, at a cell `z` of `h` (Consequence 2).** In the hardwired
runtime extended by ports commuting with the projector (record ports), from an operator on which
the decompressed event "cell `z` of `h` holds a content in `g`" has weight zero (after a read of
`z` outside `g`: `conj_queryStep_read_eq_zero`), along a run with no program at `z` and no
decompressed `⊥` at `z` at the calls (`noBot_runtimeR`), every call is presented an operator
whose recorded weight "cell `z` is recorded with a content in `g`" is at most `cellFrac g` times
its trace. -/
theorem forallQueries_recH_le {t : QuantumOracleSpec.{0, 0}} (W₀ : Hw X Z) (m₀ : M)
    (step : ∀ j : t.Port, SubInstrument (t.In j × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (t.Out j × (spongeHardwiredRuntime X Z W₀ m₀).D) (t.Result j))
    (z : Z) (g : Option X → Prop) [DecidablePred g] (hg : ¬ g none)
    (hstep : ∀ j r, (step j).branch r ∘ₗ
        (MatrixMap.conj (hwDecProj {s : HwReg X Z M | g (s.1.1 z)})).amplifyLeft (t.In j) =
      (MatrixMap.conj (hwDecProj {s : HwReg X Z M | g (s.1.1 z)})).amplifyLeft (t.Out j) ∘ₗ
        (step j).branch r)
    {P : ∀ (i : ((hwSpec X Z M).sum t).Port) (E' : QReg),
      Matrix ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E')
        ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E') ℂ → Prop}
    (hP : ∀ i E' σ, P i E' σ → NotProgAt M (.h z) i)
    (hnb : ∀ i E' σ, P i E' σ →
      QuerySupportedOn (fun m : ((hwSpec X Z M).sum t).In i × HwReg X Z M ↦ m.2)
        {s | (s.1.1 z).isSome} (MatrixMap.conj ((1 : Matrix (((hwSpec X Z M).sum t).In i)
          (((hwSpec X Z M).sum t).In i) ℂ) ⊗ₖ compressReg X Z M) (MatrixMap.traceRight _ E' σ)))
    {x : QuantumComp L ((hwSpec X Z M).sum t) Ω A}
    {ρ : Matrix (A × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (A × (spongeHardwiredRuntime X Z W₀ m₀).D) ℂ}
    (hx : ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I P x ρ)
    (h0 : (MatrixMap.conj (hwDecProj {s : HwReg X Z M | g (s.1.1 z)})).amplifyLeft A ρ = 0) :
    ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I (fun i E' σ ↦ P i E' σ ∧
      (σ.PosSemidef →
        (((1 : Matrix (((hwSpec X Z M).sum t).In i) (((hwSpec X Z M).sum t).In i) ℂ) ⊗ₖ
          diagonal fun s : HwReg X Z M ↦ if g (s.1.1 z) then 1 else 0) *
            MatrixMap.traceRight (((hwSpec X Z M).sum t).In i × HwReg X Z M) E' σ).trace.re ≤
          cellFrac g * (MatrixMap.traceRight (((hwSpec X Z M).sum t).In i × HwReg X Z M) E'
            σ).trace.re)) x ρ := by
  refine ForallQueries.mono I (fun i E' σ h ↦ ⟨h.1, fun hσ ↦ ?_⟩)
    (forallQueries_hwDecProj_eq_zero I W₀ m₀ step _ hstep (c := .h z)
      (F := fun D ↦ g (D.1 z)) (fun D D' h ↦ Iff.of_eq (congrArg g h)) (fun _ ↦ Iff.rfl) hP hx h0)
  have hτ : (MatrixMap.traceRight (((hwSpec X Z M).sum t).In i × HwReg X Z M) E' σ).PosSemidef :=
    hσ.traceRight
  exact le_of_le_sq_sqrt_add (re_trace_recH_le z g hg hτ (hnb i E' σ h.1))
    (re_trace_one_kron_mul_traceRight_eq_zero (conjTranspose_hwDecProj _) (hwDecProj_mul_self _)
      h.2) (mul_nonneg (cellFrac_nonneg g) hτ.trace_re_nonneg)

/-- **Recorded weight along runs, at a cell `x` of `k`**: as `forallQueries_recH_le`. -/
theorem forallQueries_recK_le {t : QuantumOracleSpec.{0, 0}} (W₀ : Hw X Z) (m₀ : M)
    (step : ∀ j : t.Port, SubInstrument (t.In j × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (t.Out j × (spongeHardwiredRuntime X Z W₀ m₀).D) (t.Result j))
    (x : X) (g : Option Z → Prop) [DecidablePred g] (hg : ¬ g none)
    (hstep : ∀ j r, (step j).branch r ∘ₗ
        (MatrixMap.conj (hwDecProj {s : HwReg X Z M | g (s.1.2.1 x)})).amplifyLeft (t.In j) =
      (MatrixMap.conj (hwDecProj {s : HwReg X Z M | g (s.1.2.1 x)})).amplifyLeft (t.Out j) ∘ₗ
        (step j).branch r)
    {P : ∀ (i : ((hwSpec X Z M).sum t).Port) (E' : QReg),
      Matrix ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E')
        ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E') ℂ → Prop}
    (hP : ∀ i E' σ, P i E' σ → NotProgAt M (.k x) i)
    (hnb : ∀ i E' σ, P i E' σ →
      QuerySupportedOn (fun m : ((hwSpec X Z M).sum t).In i × HwReg X Z M ↦ m.2)
        {s | (s.1.2.1 x).isSome} (MatrixMap.conj ((1 : Matrix (((hwSpec X Z M).sum t).In i)
          (((hwSpec X Z M).sum t).In i) ℂ) ⊗ₖ compressReg X Z M) (MatrixMap.traceRight _ E' σ)))
    {y : QuantumComp L ((hwSpec X Z M).sum t) Ω A}
    {ρ : Matrix (A × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (A × (spongeHardwiredRuntime X Z W₀ m₀).D) ℂ}
    (hx : ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I P y ρ)
    (h0 : (MatrixMap.conj (hwDecProj {s : HwReg X Z M | g (s.1.2.1 x)})).amplifyLeft A ρ = 0) :
    ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I (fun i E' σ ↦ P i E' σ ∧
      (σ.PosSemidef →
        (((1 : Matrix (((hwSpec X Z M).sum t).In i) (((hwSpec X Z M).sum t).In i) ℂ) ⊗ₖ
          diagonal fun s : HwReg X Z M ↦ if g (s.1.2.1 x) then 1 else 0) *
            MatrixMap.traceRight (((hwSpec X Z M).sum t).In i × HwReg X Z M) E' σ).trace.re ≤
          cellFrac g * (MatrixMap.traceRight (((hwSpec X Z M).sum t).In i × HwReg X Z M) E'
            σ).trace.re)) y ρ := by
  refine ForallQueries.mono I (fun i E' σ h ↦ ⟨h.1, fun hσ ↦ ?_⟩)
    (forallQueries_hwDecProj_eq_zero I W₀ m₀ step _ hstep (c := .k x)
      (F := fun D ↦ g (D.2.1 x)) (fun D D' h ↦ Iff.of_eq (congrArg g h)) (fun _ ↦ Iff.rfl) hP hx
      h0)
  have hτ : (MatrixMap.traceRight (((hwSpec X Z M).sum t).In i × HwReg X Z M) E' σ).PosSemidef :=
    hσ.traceRight
  exact le_of_le_sq_sqrt_add (re_trace_recK_le x g hg hτ (hnb i E' σ h.1))
    (re_trace_one_kron_mul_traceRight_eq_zero (conjTranspose_hwDecProj _) (hwDecProj_mul_self _)
      h.2) (mul_nonneg (cellFrac_nonneg g) hτ.trace_re_nonneg)

/-- **Recorded weight along runs, at a cell `x` of `k'`**: as `forallQueries_recH_le`. -/
theorem forallQueries_recK'_le {t : QuantumOracleSpec.{0, 0}} (W₀ : Hw X Z) (m₀ : M)
    (step : ∀ j : t.Port, SubInstrument (t.In j × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (t.Out j × (spongeHardwiredRuntime X Z W₀ m₀).D) (t.Result j))
    (x : X) (g : Option Z → Prop) [DecidablePred g] (hg : ¬ g none)
    (hstep : ∀ j r, (step j).branch r ∘ₗ
        (MatrixMap.conj (hwDecProj {s : HwReg X Z M | g (s.1.2.2 x)})).amplifyLeft (t.In j) =
      (MatrixMap.conj (hwDecProj {s : HwReg X Z M | g (s.1.2.2 x)})).amplifyLeft (t.Out j) ∘ₗ
        (step j).branch r)
    {P : ∀ (i : ((hwSpec X Z M).sum t).Port) (E' : QReg),
      Matrix ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E')
        ((((hwSpec X Z M).sum t).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) × E') ℂ → Prop}
    (hP : ∀ i E' σ, P i E' σ → NotProgAt M (.k' x) i)
    (hnb : ∀ i E' σ, P i E' σ →
      QuerySupportedOn (fun m : ((hwSpec X Z M).sum t).In i × HwReg X Z M ↦ m.2)
        {s | (s.1.2.2 x).isSome} (MatrixMap.conj ((1 : Matrix (((hwSpec X Z M).sum t).In i)
          (((hwSpec X Z M).sum t).In i) ℂ) ⊗ₖ compressReg X Z M) (MatrixMap.traceRight _ E' σ)))
    {y : QuantumComp L ((hwSpec X Z M).sum t) Ω A}
    {ρ : Matrix (A × (spongeHardwiredRuntime X Z W₀ m₀).D)
      (A × (spongeHardwiredRuntime X Z W₀ m₀).D) ℂ}
    (hx : ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I P y ρ)
    (h0 : (MatrixMap.conj (hwDecProj {s : HwReg X Z M | g (s.1.2.2 x)})).amplifyLeft A ρ = 0) :
    ((spongeHardwiredRuntime X Z W₀ m₀).extend step).ForallQueries I (fun i E' σ ↦ P i E' σ ∧
      (σ.PosSemidef →
        (((1 : Matrix (((hwSpec X Z M).sum t).In i) (((hwSpec X Z M).sum t).In i) ℂ) ⊗ₖ
          diagonal fun s : HwReg X Z M ↦ if g (s.1.2.2 x) then 1 else 0) *
            MatrixMap.traceRight (((hwSpec X Z M).sum t).In i × HwReg X Z M) E' σ).trace.re ≤
          cellFrac g * (MatrixMap.traceRight (((hwSpec X Z M).sum t).In i × HwReg X Z M) E'
            σ).trace.re)) y ρ := by
  refine ForallQueries.mono I (fun i E' σ h ↦ ⟨h.1, fun hσ ↦ ?_⟩)
    (forallQueries_hwDecProj_eq_zero I W₀ m₀ step _ hstep (c := .k' x)
      (F := fun D ↦ g (D.2.2 x)) (fun D D' h ↦ Iff.of_eq (congrArg g h)) (fun _ ↦ Iff.rfl) hP hx
      h0)
  have hτ : (MatrixMap.traceRight (((hwSpec X Z M).sum t).In i × HwReg X Z M) E' σ).PosSemidef :=
    hσ.traceRight
  exact le_of_le_sq_sqrt_add (re_trace_recK'_le x g hg hτ (hnb i E' σ h.1))
    (re_trace_one_kron_mul_traceRight_eq_zero (conjTranspose_hwDecProj _) (hwDecProj_mul_self _)
      h.2) (mul_nonneg (cellFrac_nonneg g) hτ.trace_re_nonneg)

end runs

end Quantum.Sponge

end
