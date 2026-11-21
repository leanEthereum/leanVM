module

public import Quantum.Xmss.TableLaw
public import VCVio.Quantum.Comp.Hybrid

@[expose] public section

/-!
# The hidden-cell hybrid: runtime 1 against runtime 2

Both runtimes act on the register `HwReg X Z M` of the hardwired runtime, started at
`(∅, ∅, m₀)`, and have its signature `hwSpec X Z M`. A table `L : Hw X Z` holds the keygen-table
cells of the honest table with their values.

* **Runtime 2** (`runtime2`) is `spongeHardwiredRuntime` with no hardwired cell at the start: the
  program ports hardwire cells as they become public.
* **Runtime 1** (`runtime1 L`) hardwires every cell of `L` from the start: its sponge and read
  ports use the view `hwView W L` (the hardwired cells `W` of the register over `L`) where runtime 2
  uses `W`. Its program ports are those of runtime 2. On the states runtime 1 reaches, the
  database is empty on the cells of `L` (they are hardwired from the start), so programming a cell
  of `L` with its value is the identity on the view.

The two runtimes differ only at the *hidden* cells, those of `L` that are not hardwired in `W`.
The Kraus weight of the difference of an adversary call (`krausWeight_le_hidden`) is at most `4`
times the hidden mass of its query input (`hiddenMass`); the program ports are equal, so their
difference has weight `0` (`krausWeight_program_eq_zero`). VCVio's square-root hybrid then gives
`√P₁ ≤ √P₂ + ∑ⱼ √(4 μⱼ)` when the hidden mass of the `j`-th call of the run against runtime 2 is at
most `μⱼ` (`sqrt_win_runtime1_le`).
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

namespace Quantum.Xmss.Hybrid

open Quantum Quantum.Sponge

/-! ## Diagonal masses and Kraus differences supported on a set -/

section operator

/-- The diagonal mass of a set of basis states. -/
noncomputable def diagMass {α : Type} [Fintype α] (S : Set α) (σ : Matrix α α ℂ) : ℝ≥0∞ :=
  ∑ a, S.indicator (fun a ↦ ENNReal.ofReal (σ a a).re) a

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]

/-- The projector on a set of basis states. -/
noncomputable def setProj (S : Set n) : Matrix n n ℂ :=
  diagonal (S.indicator 1)

omit [Fintype n] in
theorem conjTranspose_setProj (S : Set n) : (setProj S)ᴴ = setProj S := by
  rw [setProj, diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : a ∈ S <;> simp [h]

theorem setProj_mul_self (S : Set n) : setProj S * setProj S = setProj S := by
  rw [setProj, diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases h : a ∈ S <;> simp [h]

/-- The weight of the projector on `S` is the diagonal mass of `S`. -/
theorem ofReal_trace_setProj_mul (S : Set n) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    ENNReal.ofReal (setProj S * σ).trace.re = diagMass S σ := by
  have hd : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have ht : (setProj S * σ).trace.re = ∑ a, (S.indicator 1 a * σ a a).re := by
    simp only [setProj, Matrix.trace, Matrix.diag, diagonal_mul, Complex.re_sum]
  have hnn : ∀ a ∈ Finset.univ, 0 ≤ (S.indicator (1 : n → ℂ) a * σ a a).re := fun a _ ↦ by
    by_cases h : a ∈ S <;> simp [h, hd a]
  rw [ht, ENNReal.ofReal_sum_of_nonneg hnn, diagMass]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases h : a ∈ S <;> simp [h]

omit [Fintype m] in
/-- A difference of two operators that agree on the columns outside `S` is supported on `S`. -/
theorem sub_eq_sub_mul_setProj (K K' : Matrix m n ℂ) (S : Set n)
    (h : ∀ i j, j ∉ S → K i j = K' i j) : K - K' = (K - K') * setProj S := by
  ext i j
  rw [setProj, mul_diagonal]
  by_cases hj : j ∈ S
  · simp [hj]
  · simp [hj, h i j hj]

/-- **The Kraus weight of a difference supported on a set.** For two complete Kraus families
whose differences are supported on `S`, the summed weights of the differences on a positive
semidefinite `σ` are at most `4` times the diagonal mass of `S`: with `G = K - K'`,
`∑ Gᴴ G + ∑ (K + K')ᴴ (K + K') = 4`, so `∑ Gᴴ G = P (∑ Gᴴ G) P ≤ 4 P`. -/
theorem tsum_ofReal_trace_conj_sub_le {ι : Type} [Fintype ι] (K K' : ι → Matrix m n ℂ)
    (hK : ∑ r, (K r)ᴴ * K r = 1) (hK' : ∑ r, (K' r)ᴴ * K' r = 1) (S : Set n)
    (hS : ∀ r, K r - K' r = (K r - K' r) * setProj S) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    ∑' r, ENNReal.ofReal (MatrixMap.conj (K r - K' r) σ).trace.re ≤ 4 * diagMass S σ := by
  set P := setProj S
  have hP : Pᴴ = P := conjTranspose_setProj S
  have hPP : P * P = P := setProj_mul_self S
  set H := ∑ r, (K r - K' r)ᴴ * (K r - K' r)
  have hPHP : P * H * P = H := by
    simp only [H, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hr : (K r - K' r)ᴴ = P * (K r - K' r)ᴴ := by
      conv_lhs => rw [hS r]
      rw [conjTranspose_mul, hP]
    calc P * ((K r - K' r)ᴴ * (K r - K' r)) * P
        = (P * (K r - K' r)ᴴ) * ((K r - K' r) * P) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hr, ← hS r]
  have hsum : (4 : ℂ) • (1 : Matrix n n ℂ) - H = ∑ r, (K r + K' r)ᴴ * (K r + K' r) := by
    have hr : ∀ r, (K r - K' r)ᴴ * (K r - K' r) + (K r + K' r)ᴴ * (K r + K' r) =
        (2 : ℂ) • ((K r)ᴴ * K r) + (2 : ℂ) • ((K' r)ᴴ * K' r) := fun r ↦ by
      simp only [conjTranspose_sub, conjTranspose_add, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.add_mul, Matrix.mul_add, two_smul]
      abel
    have htot : H + ∑ r, (K r + K' r)ᴴ * (K r + K' r) = (4 : ℂ) • (1 : Matrix n n ℂ) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun r _ ↦ hr r, Finset.sum_add_distrib,
        ← Finset.smul_sum, ← Finset.smul_sum, hK, hK', ← add_smul]
      norm_num
    rw [← htot]
    abel
  have hpos : ((4 : ℂ) • P - H).PosSemidef := by
    have h := (posSemidef_sum Finset.univ fun r _ ↦
      posSemidef_conjTranspose_mul_self (K r + K' r)).conjTranspose_mul_mul_same P
    rw [← hsum, hP, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hPP, hPHP] at h
    exact h
  have hle : (H * σ).trace.re ≤ 4 * (P * σ).trace.re := by
    have h := hpos.trace_mul_re_nonneg hσ
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul, Complex.mul_re] at h
    norm_num at h
    linarith
  have hnn : ∀ r ∈ Finset.univ, 0 ≤ (MatrixMap.conj (K r - K' r) σ).trace.re := fun r _ ↦
    (hσ.mul_mul_conjTranspose_same _).trace_re_nonneg
  have htr : ∑ r, (MatrixMap.conj (K r - K' r) σ).trace.re = (H * σ).trace.re := by
    simp only [MatrixMap.trace_conj_apply, H, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg hnn, htr, ← ofReal_trace_setProj_mul S hσ,
    ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hle

end operator

/-! ## The two runtimes -/

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-- A read of a cell depends on the hardwired cells only through that cell. -/
theorem cellRead_congr {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    {w w' : Database A Y} {a : A} (h : w a = w' a) (o : Option Y) :
    cellRead w a o = cellRead w' a o := by
  unfold cellRead
  rw [h]

/-- The Kraus operator of a read of cell `z` of `h` in runtime 1: the read of `hwView W L`. -/
noncomputable def readKraus1H (L : Hw X Z) (z : Z) (upd : M → Option X → M) (r : Option X × M) :
    Matrix (HwReg X Z M) (HwReg X Z M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.2 = r.2) (fun b ↦ (b.1, upd r.2 r.1))
    fun b ↦ cellRead (hwView b.1 L).1 z r.1 ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ)

/-- The Kraus operator of a read of cell `x` of `k` in runtime 1. -/
noncomputable def readKraus1K (L : Hw X Z) (x : X) (upd : M → Option Z → M) (r : Option Z × M) :
    Matrix (HwReg X Z M) (HwReg X Z M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.2 = r.2) (fun b ↦ (b.1, upd r.2 r.1))
    fun b ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      (cellRead (hwView b.1 L).2.1 x r.1 ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))

/-- The Kraus operator of a read of cell `x` of `k'` in runtime 1. -/
noncomputable def readKraus1K' (L : Hw X Z) (x : X) (upd : M → Option Z → M)
    (r : Option Z × M) : Matrix (HwReg X Z M) (HwReg X Z M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.2 = r.2) (fun b ↦ (b.1, upd r.2 r.1))
    fun b ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead (hwView b.1 L).2.2 x r.1)

/-- The Kraus operators of the read ports of runtime 1, with their trivial public register. -/
noncomputable def hwReadKraus1 (L : Hw X Z) : (c : HwRead X Z M) → c.Result →
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ
  | .readH z upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1H L z upd r
  | .readK x upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K L x upd r
  | .readK' x upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K' L x upd r

theorem sum_hwReadKraus1 [Nonempty X] [Nonempty Z] (L : Hw X Z) (c : HwRead X Z M) :
    ∑ r, (hwReadKraus1 L c r)ᴴ * hwReadKraus1 L c r = 1 := by
  cases c with
  | readH z upd =>
    refine sum_conjTranspose_clsKraus_mul_self _ _ _
      (fun r b b' hb hb' he ↦ Prod.ext (Prod.mk.inj he).1 (hb.trans hb'.symm)) fun b ↦ ?_
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [sum_kronecker_left, sum_conjTranspose_cellRead_mul_self, one_kronecker_one]
  | readK x upd =>
    refine sum_conjTranspose_clsKraus_mul_self _ _ _
      (fun r b b' hb hb' he ↦ Prod.ext (Prod.mk.inj he).1 (hb.trans hb'.symm)) fun b ↦ ?_
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [sum_kronecker_right, sum_kronecker_left, sum_conjTranspose_cellRead_mul_self,
      one_kronecker_one, one_kronecker_one]
  | readK' x upd =>
    refine sum_conjTranspose_clsKraus_mul_self _ _ _
      (fun r b b' hb hb' he ↦ Prod.ext (Prod.mk.inj he).1 (hb.trans hb'.symm)) fun b ↦ ?_
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [sum_kronecker_right, sum_kronecker_right, sum_conjTranspose_cellRead_mul_self,
      one_kronecker_one, one_kronecker_one]

/-- The read ports of runtime 1 as subinstruments. -/
noncomputable def hwReadStep1 [Nonempty X] [Nonempty Z] (L : Hw X Z) (c : HwRead X Z M) :
    SubInstrument (Unit × HwReg X Z M) (Unit × HwReg X Z M) c.Result :=
  SubInstrument.ofKraus (hwReadKraus1 L c) (sum_hwReadKraus1 L c)

variable [AddCommGroup X] [AddCommGroup Z]

variable (X Z) in
/-- The initial state of both runtimes: empty databases, no hardwired cell, memory `m₀`. -/
noncomputable def initHw (m₀ : M) : SubState (QReg.of (HwReg X Z M)) :=
  SubState.basis ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀)

variable (X Z) in
/-- The sponge ports of runtime 1: the oracle of the view `hwView W L` on hardwired cells, the
compressed oracle on the others, on the register started at `(∅, ∅, m₀)`. -/
@[reducible]
noncomputable def spongeHardwired1 (L : Hw X Z) (m₀ : M) :
    EmulatedOracle SpongePort (spongeIn X Z) where
  S := QReg.of (HwReg X Z M)
  init := initHw X Z m₀
  U
    | .h => hwPort fun s : HwReg X Z M ↦ fun z ↦
        ((hwView s.2.1 L).1 z).getD (s.1.1.lookup z)
    | .k => hwPort fun s : HwReg X Z M ↦ fun x ↦
        ((hwView s.2.1 L).2.1 x).getD (s.1.2.1.lookup x)
    | .k' => hwPort fun s : HwReg X Z M ↦ fun x ↦
        ((hwView s.2.1 L).2.2 x).getD (s.1.2.2.lookup x)
  unitary
    | .h => hwPort_mem_unitaryGroup _
    | .k => hwPort_mem_unitaryGroup _
    | .k' => hwPort_mem_unitaryGroup _

variable (X Z) in
/-- **Runtime 2.** The hardwired runtime with no hardwired cell at the start
(`runtime2_eq_spongeHardwiredRuntime`), with its register and initial state written out. -/
@[reducible]
noncomputable def runtime2 [Nonempty X] [Nonempty Z] (m₀ : M) : QuantumRuntime (hwSpec X Z M) where
  D := QReg.of (HwReg X Z M)
  init := initHw X Z m₀
  step := (spongeHardwiredRuntime X Z (hwEmpty X Z) m₀).step

theorem runtime2_eq_spongeHardwiredRuntime [Nonempty X] [Nonempty Z] (m₀ : M) :
    runtime2 X Z m₀ = spongeHardwiredRuntime X Z (hwEmpty X Z) m₀ :=
  rfl

variable (X Z) in
/-- **Runtime 1.** Every cell of `L` hardwired from the start: the sponge and read ports use the
view `hwView W L`; the program ports are those of runtime 2. -/
@[reducible]
noncomputable def runtime1 [Nonempty X] [Nonempty Z] (L : Hw X Z) (m₀ : M) :
    QuantumRuntime (hwSpec X Z M) where
  D := QReg.of (HwReg X Z M)
  init := initHw X Z m₀
  step := ((((spongeHardwired1 X Z L m₀).toRuntime : QuantumRuntime (spongeSpec X Z)).extend
    (t := hwReadCmdSpec X Z M) (hwReadStep1 L)).extend (t := hwProgSpec X Z) hwProgStep).step

variable (X Z) in
/-- The Kraus operators of runtime 2. -/
noncomputable def kraus2 (m₀ : M) : ∀ i : (hwSpec X Z M).Port, (hwSpec X Z M).Result i →
    Matrix ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ
  | .inl (.inl i), _ => (spongeHardwired X Z (hwEmpty X Z) m₀).U i
  | .inl (.inr c), r => hwReadKraus c r
  | .inr c, r => hwProgKraus c r

variable (X Z) in
/-- The Kraus operators of runtime 1. -/
noncomputable def kraus1 (L : Hw X Z) (m₀ : M) : ∀ i : (hwSpec X Z M).Port,
    (hwSpec X Z M).Result i →
      Matrix ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M))
        ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ
  | .inl (.inl i), _ => (spongeHardwired1 X Z L m₀).U i
  | .inl (.inr c), r => hwReadKraus1 L c r
  | .inr c, r => hwProgKraus c r

variable (X Z) in
/-- The difference of the Kraus operators of the two runtimes. -/
noncomputable def krausDiff (L : Hw X Z) (m₀ : M) (i : (hwSpec X Z M).Port)
    (r : (hwSpec X Z M).Result i) :
    Matrix ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ :=
  kraus2 X Z m₀ i r - kraus1 X Z L m₀ i r

theorem runtime2_branch [Nonempty X] [Nonempty Z] (m₀ : M) (i : (hwSpec X Z M).Port)
    (r : (hwSpec X Z M).Result i) :
    ((runtime2 X Z m₀).step i).branch r = MatrixMap.conj (kraus2 X Z m₀ i r) := by
  rcases i with (i | c) | c
  · exact spongeHardwiredRuntime_step_sponge _ m₀ i r
  · exact spongeHardwiredRuntime_step_read _ m₀ c r
  · exact spongeHardwiredRuntime_step_prog _ m₀ c r

theorem runtime1_branch [Nonempty X] [Nonempty Z] (L : Hw X Z) (m₀ : M)
    (i : (hwSpec X Z M).Port) (r : (hwSpec X Z M).Result i) :
    ((runtime1 X Z L m₀).step i).branch r = MatrixMap.conj (kraus1 X Z L m₀ i r) := by
  rcases i with (i | c) | c
  · exact (spongeHardwired1 X Z L m₀).toRuntime_step_branch i r
  · rfl
  · exact hwProgStep_branch c r

/-! ## Hidden masses -/

/-- The cells of `L` lie in the hidden sets `Hh`, `Hk`, `Hk'`. -/
def Covers (L : Hw X Z) (Hh : Set Z) (Hk Hk' : Set X) : Prop :=
  (∀ z, L.1 z ≠ none → z ∈ Hh) ∧ (∀ x, L.2.1 x ≠ none → x ∈ Hk) ∧
    (∀ x, L.2.2 x ≠ none → x ∈ Hk')

/-- **The hidden mass** of the input of a call. For a sponge port, the mass of the query inputs at
a cell of the hidden set that is not hardwired; for a read port, the mass of the states in which
the read cell is in the hidden set and not hardwired; for a program port, `0` (the two runtimes
program alike). -/
noncomputable def hiddenMass (Hh : Set Z) (Hk Hk' : Set X) :
    ∀ i : (hwSpec X Z M).Port, Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞
  | .inl (.inl .h) => diagMass {p : (Z × X) × HwReg X Z M | p.1.1 ∈ Hh ∧ p.2.2.1.1 p.1.1 = none}
  | .inl (.inl .k) =>
      diagMass {p : (X × Z) × HwReg X Z M | p.1.1 ∈ Hk ∧ p.2.2.1.2.1 p.1.1 = none}
  | .inl (.inl .k') =>
      diagMass {p : (X × Z) × HwReg X Z M | p.1.1 ∈ Hk' ∧ p.2.2.1.2.2 p.1.1 = none}
  | .inl (.inr (.readH z _)) => diagMass {p : Unit × HwReg X Z M | z ∈ Hh ∧ p.2.2.1.1 z = none}
  | .inl (.inr (.readK x _)) =>
      diagMass {p : Unit × HwReg X Z M | x ∈ Hk ∧ p.2.2.1.2.1 x = none}
  | .inl (.inr (.readK' x _)) =>
      diagMass {p : Unit × HwReg X Z M | x ∈ Hk' ∧ p.2.2.1.2.2 x = none}
  | .inr _ => fun _ ↦ 0

/-! ## The Kraus weights of the differences -/

/-- The view over `L` agrees with `W` outside the hidden cells. -/
theorem hwView_or_eq {A Y : Type} {w l : A → Option Y} {H : Set A} (hl : ∀ a, l a ≠ none → a ∈ H)
    {a : A} (ha : ¬ (a ∈ H ∧ w a = none)) : (w a).or (l a) = w a := by
  rcases hw : w a with _ | v
  · have hlN : l a = none := by
      by_contra hne
      exact ha ⟨hl a hne, hw⟩
    simp [hlN]
  · rfl

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The difference of two ports of the hardwired runtime is supported on a set of query inputs
and classical data outside which the two reads agree. -/
theorem hwPort_sub_eq {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] (read read' : HwReg X Z M → A → Y) (S : Set ((A × Y) × HwReg X Z M))
    (hS : ∀ q q' : (A × Y) × HwReg X Z M, q.1 = q'.1 → q.2.2 = q'.2.2 → (q ∈ S ↔ q' ∈ S))
    (hr : ∀ q ∉ S, read q.2 q.1.1 = read' q.2 q.1.1) :
    hwPort read - hwPort read' = (hwPort read - hwPort read') * setProj S := by
  set C := (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M
  have hT : tableOracle read - tableOracle read' =
      (tableOracle read - tableOracle read') * setProj S := by
    refine sub_eq_sub_mul_setProj _ _ S fun p q hq ↦ ?_
    obtain ⟨m', t⟩ := q
    simp only [tableOracle_apply, tableOracleEquiv_apply, oracleEquiv_apply, hr (m', t) hq]
    split_ifs <;> simp_all
  have hC : setProj S * C = C * setProj S := by
    ext p q
    rw [setProj, diagonal_mul, mul_diagonal]
    by_cases h1 : p.1 = q.1
    · by_cases h2 : p.2.2 = q.2.2
      · have hpq := hS p q h1 h2
        by_cases hp : p ∈ S
        · simp [hp, hpq.1 hp]
        · simp [hp, mt hpq.2 hp]
      · have h0 : C p q = 0 := by
          simp only [C, compressReg, kroneckerMap_apply]
          rw [Matrix.one_apply_ne h2]
          simp
        simp [h0]
    · have h0 : C p q = 0 := by
        simp only [C, kroneckerMap_apply]
        rw [Matrix.one_apply_ne h1]
        simp
      simp [h0]
  calc hwPort read - hwPort read' = C * (tableOracle read - tableOracle read') * C := by
        simp only [hwPort, C, Matrix.mul_sub, Matrix.sub_mul]
    _ = C * (tableOracle read - tableOracle read') * (setProj S * C) := by
        conv_lhs => rw [hT]
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hC]
        simp only [hwPort, C, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- **A program call.** The two runtimes program alike, so the difference has weight `0`. -/
theorem krausWeight_program_eq_zero (L : Hw X Z) (m₀ : M) (c : HwProg X Z)
    (σ : Matrix ((hwSpec X Z M).In (.inr c) × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In (.inr c) × QReg.of (HwReg X Z M)) ℂ) :
    QuantumRuntime.krausWeight (krausDiff X Z L m₀) (.inr c) σ = 0 := by
  rw [QuantumRuntime.krausWeight]
  refine ENNReal.tsum_eq_zero.2 fun r ↦ ?_
  rw [MatrixMap.conj_apply, show krausDiff X Z L m₀ (.inr c) r = 0 from sub_self _]
  have h0 : ∀ {a b : Type} [Fintype a] [Fintype b] (τ : Matrix a a ℂ),
      ((0 : Matrix b a ℂ) * τ * (0 : Matrix b a ℂ)ᴴ).trace.re ≤ 0 := fun _ ↦ by simp
  exact ENNReal.ofReal_eq_zero.2
    (h0 (b := (hwSpec X Z M).Out (.inr c) × QReg.of (HwReg X Z M)) σ)

variable {Hh : Set Z} {Hk Hk' : Set X}

/-- **An adversary or read call.** The Kraus weight of the difference of the two runtimes at any
call is at most `4` times the hidden mass of its input. -/
theorem krausWeight_le_hidden [Nonempty X] [Nonempty Z] (L : Hw X Z) (m₀ : M)
    (hL : Covers L Hh Hk Hk') (i : (hwSpec X Z M).Port)
    {σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ} (hσ : σ.PosSemidef) :
    QuantumRuntime.krausWeight (krausDiff X Z L m₀) i σ ≤ 4 * hiddenMass Hh Hk Hk' i σ := by
  obtain ⟨hLh, hLk, hLk'⟩ := hL
  rcases i with (i | c) | c
  · have hU : ∀ (A Y : Type) [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
        [AddCommGroup Y] (read read' : HwReg X Z M → A → Y)
        (S : Set ((A × Y) × HwReg X Z M))
        (hS : ∀ q q' : (A × Y) × HwReg X Z M, q.1 = q'.1 → q.2.2 = q'.2.2 → (q ∈ S ↔ q' ∈ S))
        (hr : ∀ q ∉ S, read q.2 q.1.1 = read' q.2 q.1.1)
        {σ : Matrix ((A × Y) × HwReg X Z M) ((A × Y) × HwReg X Z M) ℂ}, σ.PosSemidef →
        ∑' _ : Unit, ENNReal.ofReal (MatrixMap.conj (hwPort read - hwPort read') σ).trace.re ≤
          4 * diagMass S σ := by
      intro A Y _ _ _ _ _ read read' S hS hr σ hσ
      have hu : ∀ read : HwReg X Z M → A → Y,
          ∑ _ : Unit, (hwPort read)ᴴ * hwPort read = 1 := fun read ↦ by
        have h := Matrix.mem_unitaryGroup_iff'.mp (hwPort_mem_unitaryGroup read)
        rw [star_eq_conjTranspose] at h
        simpa using h
      exact tsum_ofReal_trace_conj_sub_le (fun _ ↦ hwPort read) (fun _ ↦ hwPort read')
        (hu read) (hu read') S (fun _ ↦ hwPort_sub_eq read read' S hS hr) hσ
    cases i with
    | h =>
      exact hU (Z) (X) _ _ _ (fun q q' h1 h2 ↦ by simp [h1, h2])
        (fun q hq ↦ by simp only [hwView, hwView_or_eq (w := q.2.2.1.1) (a := q.1.1) hLh hq])
        hσ
    | k =>
      exact hU (X) (Z) _ _ _ (fun q q' h1 h2 ↦ by simp [h1, h2])
        (fun q hq ↦ by
          simp only [hwView, hwView_or_eq (w := q.2.2.1.2.1) (a := q.1.1) hLk hq])
        hσ
    | k' =>
      exact hU (X) (Z) _ _ _ (fun q q' h1 h2 ↦ by simp [h1, h2])
        (fun q hq ↦ by
          simp only [hwView, hwView_or_eq (w := q.2.2.1.2.2) (a := q.1.1) hLk' hq])
        hσ
  · cases c with
    | readH z upd =>
      refine tsum_ofReal_trace_conj_sub_le (hwReadKraus (.readH z upd))
        (hwReadKraus1 L (.readH z upd)) (sum_hwReadKraus _) (sum_hwReadKraus1 L _)
        {p : Unit × HwReg X Z M | z ∈ Hh ∧ p.2.2.1.1 z = none}
        (fun r ↦ sub_eq_sub_mul_setProj _ _ _ fun p q hq ↦ ?_) hσ
      simp only [hwReadKraus, hwReadKraus1, readKrausH, readKraus1H, kroneckerMap_apply,
        clsKraus_apply]
      rw [cellRead_congr (w := q.2.2.1.1) (w' := (hwView q.2.2.1 L).1)
        (by simp only [hwView, hwView_or_eq (w := q.2.2.1.1) (a := z) hLh hq])]
    | readK x upd =>
      refine tsum_ofReal_trace_conj_sub_le (hwReadKraus (.readK x upd))
        (hwReadKraus1 L (.readK x upd)) (sum_hwReadKraus _) (sum_hwReadKraus1 L _)
        {p : Unit × HwReg X Z M | x ∈ Hk ∧ p.2.2.1.2.1 x = none}
        (fun r ↦ sub_eq_sub_mul_setProj _ _ _ fun p q hq ↦ ?_) hσ
      simp only [hwReadKraus, hwReadKraus1, readKrausK, readKraus1K, kroneckerMap_apply,
        clsKraus_apply]
      rw [cellRead_congr (w := q.2.2.1.2.1) (w' := (hwView q.2.2.1 L).2.1)
        (by simp only [hwView, hwView_or_eq (w := q.2.2.1.2.1) (a := x) hLk hq])]
    | readK' x upd =>
      refine tsum_ofReal_trace_conj_sub_le (hwReadKraus (.readK' x upd))
        (hwReadKraus1 L (.readK' x upd)) (sum_hwReadKraus _) (sum_hwReadKraus1 L _)
        {p : Unit × HwReg X Z M | x ∈ Hk' ∧ p.2.2.1.2.2 x = none}
        (fun r ↦ sub_eq_sub_mul_setProj _ _ _ fun p q hq ↦ ?_) hσ
      simp only [hwReadKraus, hwReadKraus1, readKrausK', readKraus1K', kroneckerMap_apply,
        clsKraus_apply]
      rw [cellRead_congr (w := q.2.2.1.2.2) (w' := (hwView q.2.2.1 L).2.2)
        (by simp only [hwView, hwView_or_eq (w := q.2.2.1.2.2) (a := x) hLk' hq])]
  · rw [krausWeight_program_eq_zero]
    exact zero_le

/-! ## The hybrid -/

section hybrid

universe u v w

variable [Nonempty X] [Nonempty Z] {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w}
  {A : QReg} {γ : Type*} [MeasurableSpace γ]

/-- **The square-root hybrid**, with the Kraus weights of the differences on the inputs of the
calls of the run against runtime 2. -/
theorem sqrt_win_runtime1_le_krausWeight (L : Hw X Z) (m₀ : M)
    (x : QuantumComp Λ (hwSpec X Z M) Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    (runtime1 X Z L m₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (runtime2 X Z m₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (runtime2 X Z m₀).queryWeight I
          (QuantumRuntime.krausWeight (krausDiff X Z L m₀)) x
          (ρ.matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j ^ (2⁻¹ : ℝ) :=
  QuantumRuntime.rpow_inv_two_outcomeLawWith_le' I (initHw X Z m₀)
    (runtime2_branch m₀) (runtime1_branch L m₀) x ρ f hs

/-- **Runtime 1 against runtime 2.** If the hidden mass of the `j`-th call of the run against
runtime 2 is at most `μ j`, then `√P₁ ≤ √P₂ + ∑ⱼ √(4 μ j)`. -/
theorem sqrt_win_runtime1_le (L : Hw X Z) (m₀ : M) (hL : Covers L Hh Hk Hk')
    (x : QuantumComp Λ (hwSpec X Z M) Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ) {s : Set γ}
    (hs : MeasurableSet s) {μ : ℕ → ℝ≥0∞}
    (hHidden : ∀ j, (runtime2 X Z m₀).queryWeight I (hiddenMass Hh Hk Hk') x
      (ρ.matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j ≤ μ j) :
    (runtime1 X Z L m₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (runtime2 X Z m₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) + ∑' j, (4 * μ j) ^ (2⁻¹ : ℝ) := by
  refine (sqrt_win_runtime1_le_krausWeight I L m₀ x ρ f hs).trans (add_le_add le_rfl ?_)
  refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
  calc (runtime2 X Z m₀).queryWeight I (QuantumRuntime.krausWeight (krausDiff X Z L m₀)) x
        (ρ.matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j
      ≤ (runtime2 X Z m₀).queryWeight I (fun i σ ↦ 4 * hiddenMass Hh Hk Hk' i σ) x
          (ρ.matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j :=
        (runtime2 X Z m₀).queryWeight_mono I
          (fun i _ hσ ↦ krausWeight_le_hidden L m₀ hL i hσ) x
          (ρ.prod (runtime2 X Z m₀).init).posSemidef j
    _ = 4 * (runtime2 X Z m₀).queryWeight I (hiddenMass Hh Hk Hk') x
          (ρ.matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j :=
        (runtime2 X Z m₀).queryWeight_const_mul I 4 x _ j
    _ ≤ 4 * μ j := by gcongr; exact hHidden j
end hybrid

end Quantum.Xmss.Hybrid

end
