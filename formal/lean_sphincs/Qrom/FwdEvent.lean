module

public import Qrom.FwdGame
public import Qrom.Fwd

@[expose] public section

/-!
# The search event of a game with overrides, by the one-directional hybrid

A program with at most `n` calls in all, to the hash and to the side ports of a game with overrides
(`Qrom.OvGame`), leaves weight at most `λ (2 + 4 λ) n² tr ρ` on the search event of the compressed
database, when every input has at most `s` good values and `λ = s / |Y|`
(`Qrom.OvGame.tsum_eventWeight_compressed_le_fwd`), against `6 λ n² tr ρ` by the commutators
(`Qrom.OvGame.tsum_eventWeight_compressed_le`).

The proof is the one-directional hybrid (`Qrom.rpow_inv_two_fwd_run_le`): each call adds to the
square root of the weight on the event at most the square root of the weight its forward block
moves in. The compressed run is the purified run carried by `1_S ⊗ K`, `K` tabulating a function
and compressing every cell (`Quantum.QuantumRuntime.queryWeight_simulation`), and every column of
`K` is reachable (`Qrom.OvGame.reachS_mul_tab`), so the forward block of each call acts as its
restriction to reachable databases, of squared norm at most `λ (2 + 4 λ)`
(`Qrom.OvGame.norm_fwd_compOracle_sq_le`). Side ports keep the database, so they move nothing.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w

namespace Qrom

open Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

theorem tabCompress_apply (D : Database X Y) (H : X → Y) :
    tabCompress X Y D H = ∏ j, cellCompress Y (D j) (some (H j)) := by
  rw [tabCompress, mul_basisMatrix_apply, compressAll, piKron_apply]
  rfl

omit [DecidableEq Y] in
theorem cellReach_mul_cellCompress [Nonempty Y] [DecidableEq Y] (c : Option Y) (y : Y) :
    ∑ a, cellReach Y c a * cellCompress Y a (some y) = cellCompress Y c (some y) := by
  have hv := congrFun (cellCompress_mulVec_cellUniform (Y := Y)) (some y)
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, reduceCtorEq, ↓reduceIte] at hv
  have h : ∑ a, cellUniform Y c * cellUniform Y a * cellCompress Y a (some y) = 0 := by
    rw [show ∑ a, cellUniform Y c * cellUniform Y a * cellCompress Y a (some y) =
        cellUniform Y c * ∑ a, cellCompress Y (some y) a * cellUniform Y a by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ ↦ by rw [cellCompress_apply_comm]; ring, hv, mul_zero]
  simp only [cellReach_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, h, sub_zero]

namespace OvGame

variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable (g : OvGame X Y S P Res)

/-- **Every tabulated and compressed database is reachable.** -/
theorem reachS_mul_tab [Nonempty Y] :
    reachS (X := X) (Y := Y) (S := S) * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)) =
      (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y) := by
  ext ⟨m', s', D'⟩ ⟨m, s, H⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single m]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · simp only [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, reachS, of_apply]
      by_cases hs : s' = s
      · subst hs
        simp only [↓reduceIte, reachQ, of_apply, Matrix.one_apply]
        by_cases hm : m' = m
        · subst hm
          simp only [true_and, ↓reduceIte, one_mul, ite_mul, zero_mul]
          set x := m'.1
          set r := Function.update D' x none
          have hr : r x = none := by simp [r]
          have hcond : ∀ D'' : Database X Y, (∀ j ≠ x, D' j = D'' j) ↔
              Function.update D'' x none = r := by
            intro D''
            constructor
            · intro h
              exact (update_none_eq_of_agree fun j hj ↦ (h j hj).symm)
            · intro h j hj
              have := congrFun h j
              rw [Function.update_of_ne hj] at this
              rw [this]
              simp [r, Function.update_of_ne hj]
          simp only [hcond]
          rw [Database.sum_ite_update_none_eq hr (fun D'' ↦ cellReach Y (D' x) (D'' x) *
            tabCompress X Y D'' H)]
          simp only [tabCompress_apply, Function.update_self]
          have hprod : ∀ a : Option Y, ∏ j, cellCompress Y (Function.update r x a j) (some (H j)) =
              cellCompress Y a (some (H x)) *
                ∏ j ∈ Finset.univ \ {x}, cellCompress Y (D' j) (some (H j)) := by
            intro a
            have he : (fun j ↦ cellCompress Y (Function.update r x a j) (some (H j))) =
                Function.update (fun j ↦ cellCompress Y (D' j) (some (H j))) x
                  (cellCompress Y a (some (H x))) := by
              funext j
              by_cases hj : j = x
              · subst hj
                simp
              · simp [Function.update_of_ne hj, r]
            rw [he, Finset.prod_update_of_mem (Finset.mem_univ x)]
          simp only [hprod, ← mul_assoc, ← Finset.sum_mul, cellReach_mul_cellCompress]
          rw [← Finset.prod_update_of_mem (Finset.mem_univ x)]
          refine Finset.prod_congr rfl fun j _ ↦ ?_
          by_cases hj : j = x
          · subst hj
            simp
          · simp [Function.update_of_ne hj]
        · simp [hm]
      · simp [hs]
    · intro b _ hb
      refine Finset.sum_eq_zero fun D₁ _ ↦ ?_
      simp [kroneckerMap_apply, hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun p _ ↦ ?_
    simp [kroneckerMap_apply, Matrix.one_apply, hb]
  · simp

/-! ## The event bound -/

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
variable [AddCommGroup Y] [Nonempty Y]

omit [Fintype S] [DecidableEq X] [Fintype Y] [AddCommGroup Y] [Nonempty Y] in
theorem one_kronecker_one_sub_eq (E : Matrix (Database X Y) (Database X Y) ℂ) {B : Type}
    [Fintype B] [DecidableEq B] :
    (1 : Matrix B B ℂ) ⊗ₖ (1 - (1 : Matrix S S ℂ) ⊗ₖ E) =
      (1 : Matrix B B ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ (1 - E)) := by
  congr 1
  have := kronecker_add (1 : Matrix S S ℂ) (1 - E) E
  rw [sub_add_cancel, one_kronecker_one] at this
  rw [this, add_sub_cancel_right]

/-- The compressed initial state is the purified one carried by `1_S ⊗ K`. -/
theorem conj_tab_purified_init :
    MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y) g.purified.init.matrix =
      g.compressed.init.matrix := by
  change MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)
      ((SubState.basis g.init).prod (uniformFunctionState X Y)).matrix =
    (SubState.basis (g.init, Database.empty)).matrix
  rw [SubState.matrix_prod, MatrixMap.conj_apply, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    ← MatrixMap.conj_apply, conj_compressAll_mul_basisMatrix_uniformFunctionState,
    SubState.matrix_basis, SubState.matrix_basis, SubState.matrix_basis]
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [kroneckerMap_apply, Matrix.single_apply, Prod.mk.injEq]
  rcases eq_or_ne g.init a with rfl | ha
  · rcases eq_or_ne g.init c with rfl | hc
    · rcases eq_or_ne Database.empty b with rfl | hb
      · rcases eq_or_ne Database.empty d with rfl | hd
        · simp
        · simp [hd]
      · simp [hb]
    · simp [hc]
  · simp [ha]

/-- The compressed game simulates the purified one through `1_S ⊗ K`. -/
theorem compressed_simulation (i : (ovSpec X Y S P Res).Port) (r : (ovSpec X Y S P Res).Result i) :
    (g.compressed.step i).branch r ∘ₗ
        (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft
          ((ovSpec X Y S P Res).In i) =
      (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft
          ((ovSpec X Y S P Res).Out i) ∘ₗ (g.purified.step i).branch r := by
  rcases i with ⟨⟩ | j
  · change MatrixMap.conj g.compOracle ∘ₗ
        (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft (X × Y) =
      (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft (X × Y) ∘ₗ
        MatrixMap.conj (tableOracle (fun t : S × (X → Y) ↦ g.answer t.1 t.2))
    rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
      compOracle_mul_one_kronecker]
  · change MatrixMap.conj (g.sideKraus (Database X Y) j r) ∘ₗ
        (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft Unit =
      (MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft Unit ∘ₗ
        MatrixMap.conj (g.sideKraus (X → Y) j r)
    rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
    exact congrArg MatrixMap.conj (g.sideKraus_mul_one_kronecker (X → Y) (tabCompress X Y) j r)

variable (good : X → Y → Prop) [∀ z, DecidablePred (good z)]

/-- The search event on the register of the compressed game. -/
noncomputable abbrev evQ : Matrix (S × Database X Y) (S × Database X Y) ℂ :=
  (1 : Matrix S S ℂ) ⊗ₖ eventProj (searchEvent good)

theorem fwdKraus_side (j : P) (r : (ovSpec X Y S P Res).Result (Sum.inr j)) :
    fwdKraus (spec := ovSpec X Y S P Res) (D := g.compressed.D) g.compKraus (evQ good)
      (Sum.inr j) r = 0 := by
  have hQQ : evQ (S := S) good * evQ good = evQ good := by
    rw [evQ, ← mul_kronecker_mul, Matrix.one_mul, eventProj_mul_self]
  have key : ((1 : Matrix Unit Unit ℂ) ⊗ₖ evQ good) * g.sideKraus (Database X Y) j r *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ (1 - evQ good)) = 0 := by
    rw [evQ, ← g.sideKraus_mul_one_kronecker (Database X Y) (eventProj (searchEvent good)) j r,
      Matrix.mul_assoc, ← evQ, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      hQQ, sub_self, kronecker_zero, Matrix.mul_zero]
  rw [fwdKraus]
  exact key

/-- **The forward block of a hash call, on the purified input.** -/
theorem norm_fwd_hash_mul_tab_sq_le (s : ℕ) (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s) :
    ‖((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ evQ good) * g.compOracle *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ (1 - evQ good)) *
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y))‖ ^ 2 ≤
      (s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y)) := by
  have hM : ‖(1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)‖ ≤ 1 :=
    l2_opNorm_le_one_of_conjTranspose_mul_self (by
      rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_kronecker, conjTranspose_one,
        ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
        conjTranspose_compressAll_mul_basisMatrix_mul_self, one_kronecker_one, one_kronecker_one])
  rw [evQ, one_kronecker_one_sub_eq, ← reachS_mul_tab, ← Matrix.mul_assoc]
  refine (pow_le_pow_left₀ (norm_nonneg _) ((l2_opNorm_mul _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hM)) 2).trans ?_
  exact g.norm_fwd_compOracle_sq_le good s hs

/-- **The forward weight of a call**, against the purified input, is at most `λ (2 + 4 λ)` times its
trace. -/
theorem krausWeight_fwd_le (s : ℕ) (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s)
    (i : (ovSpec X Y S P Res).Port)
    (σ : Matrix ((ovSpec X Y S P Res).In i × g.purified.D) ((ovSpec X Y S P Res).In i ×
      g.purified.D) ℂ) (hσ : σ.PosSemidef) :
    QuantumRuntime.krausWeight (spec := ovSpec X Y S P Res) (D := g.compressed.D)
        (fwdKraus g.compKraus (evQ good)) i
        ((MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)).amplifyLeft
          ((ovSpec X Y S P Res).In i) σ) ≤
      ENNReal.ofReal ((s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y))) *
        ENNReal.ofReal σ.trace.re := by
  rcases i with ⟨⟩ | j
  · let _ : Fintype ((ovSpec X Y S P Res).Result (Sum.inl ())) := inferInstanceAs (Fintype Unit)
    let _ : Unique ((ovSpec X Y S P Res).Result (Sum.inl ())) := inferInstanceAs (Unique Unit)
    rw [QuantumRuntime.krausWeight, tsum_fintype, Fintype.sum_unique, MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.conj _), ← MatrixMap.conj_mul,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((MatrixMap.re_trace_conj_le _ hσ).trans
      (mul_le_mul_of_nonneg_right ?_ hσ.trace_re_nonneg))
    exact g.norm_fwd_hash_mul_tab_sq_le good s hs
  · rw [QuantumRuntime.krausWeight]
    refine (ENNReal.tsum_eq_zero.mpr fun r ↦ ?_).le.trans zero_le
    rw [fwdKraus_side, MatrixMap.conj_apply, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero,
      Complex.zero_re, ENNReal.ofReal_zero]

/-- **The search event of a game with overrides, by the one-directional hybrid.** From `ρ`, a
program with at most `n` calls in all leaves weight at most `λ (2 + 4 λ) n² tr ρ` on the search
event of the compressed database, with `λ = s / |Y|`. -/
theorem tsum_eventWeight_compressed_le_fwd (I : L.Interp) (s : ℕ)
    (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s) (n : ℕ)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (hx : x.IsTotalQueryBound n) (ρ : SubState A) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ
        ((1 : Matrix S S ℂ) ⊗ₖ eventProj (searchEvent good)))
          (g.compressed.jointPost I x ρ p).matrix).trace.re ≤
      ENNReal.ofReal ((s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y))) *
        (n : ℝ≥0∞) ^ 2 * ENNReal.ofReal ρ.matrix.trace.re := by
  set R := g.compressed
  set Q : Matrix (S × Database X Y) (S × Database X Y) ℂ := evQ good with hQdef
  set κ : ℝ := (s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y))
  set c : ℝ≥0∞ := ENNReal.ofReal κ
  set V := MatrixMap.conj ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)
  have hU : ∀ i r, (R.step i).branch r = MatrixMap.conj (g.compKraus i r) := by
    rintro (⟨⟩ | j) r
    · exact SubInstrument.branch_ofIsometry_apply g.compOracle g.conjTranspose_compOracle_mul_self r
    · exact g.sideStep_branch (Database X Y) j r
  have hQ : Qᴴ = Q := by
    rw [hQdef, evQ, conjTranspose_kronecker, conjTranspose_one, eventProj_conjTranspose]
  have hQQ : Q * Q = Q := by
    rw [hQdef, evQ, ← mul_kronecker_mul, Matrix.one_mul, eventProj_mul_self]
  have hρ : (ρ.matrix ⊗ₖ R.init.matrix).PosSemidef := (ρ.prod R.init).posSemidef
  have hρQ : evW Q (ρ.matrix ⊗ₖ R.init.matrix) = 0 := by
    have h : Q * (SubState.basis (g.init, Database.empty)).matrix = 0 := by
      rw [SubState.matrix_basis]
      ext ⟨s₀, D⟩ ⟨s₀', D'⟩
      simp only [hQdef, evQ, Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
        Matrix.one_apply, Matrix.single_apply, eventProj, labelProjector, diagonal_apply,
        Matrix.zero_apply]
      refine Finset.sum_eq_zero fun s₁ _ ↦ Finset.sum_eq_zero fun D₁ _ ↦ ?_
      by_cases h1 : D = D₁
      · subst h1
        by_cases h2 : D = Database.empty
        · subst h2
          simp [searchEvent_empty]
        · simp [Ne.symm h2]
      · simp [h1]
    rw [evW, MatrixMap.conj_apply, ← mul_kronecker_mul, Matrix.one_mul]
    change ENNReal.ofReal (ρ.matrix ⊗ₖ (Q * (SubState.basis (g.init, Database.empty)).matrix) *
      _).trace.re = 0
    rw [h, kronecker_zero, Matrix.zero_mul]
    simp
  have h := rpow_inv_two_fwd_run_le I R hU hQ hQQ x hρ
  rw [hρQ, ENNReal.zero_rpow_of_pos (by norm_num), zero_add] at h
  -- the compressed run is the purified run carried by `1_S ⊗ K`
  have hΓ : ρ.matrix ⊗ₖ R.init.matrix = V.amplifyLeft A (ρ.matrix ⊗ₖ g.purified.init.matrix) := by
    rw [MatrixMap.amplifyLeft_kronecker, conj_tab_purified_init]
  have hρp : (ρ.matrix ⊗ₖ g.purified.init.matrix).PosSemidef := (ρ.prod g.purified.init).posSemidef
  have hj : ∀ j, R.queryWeight I (QuantumRuntime.krausWeight (fwdKraus g.compKraus Q)) x
      (ρ.matrix ⊗ₖ R.init.matrix) j ≤ c * ENNReal.ofReal ρ.matrix.trace.re := by
    intro j
    rw [hΓ, QuantumRuntime.queryWeight_simulation I (R₁ := g.purified) (R₂ := R)
      g.compressed_simulation]
    refine (g.purified.queryWeight_mono I (w' := fun _ σ ↦ c * ENNReal.ofReal σ.trace.re)
      (fun i σ hσ ↦ g.krausWeight_fwd_le good s hs i σ hσ) x hρp j).trans ?_
    rw [QuantumRuntime.queryWeight_const_mul]
    have htr : (ρ.matrix ⊗ₖ g.purified.init.matrix).trace = ρ.matrix.trace := by
      have hiso : ((1 : Matrix A A ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y))ᴴ *
          ((1 : Matrix A A ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ tabCompress X Y)) = 1 := by
        rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_kronecker, conjTranspose_one,
          ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
          conjTranspose_compressAll_mul_basisMatrix_mul_self, one_kronecker_one, one_kronecker_one]
      have h1 : (V.amplifyLeft A (ρ.matrix ⊗ₖ g.purified.init.matrix)).trace =
          (ρ.matrix ⊗ₖ g.purified.init.matrix).trace := by
        rw [MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply, Matrix.trace_mul_cycle, hiso,
          Matrix.one_mul]
      rw [← h1, ← hΓ]
      simp [R, Matrix.trace_kronecker, SubState.matrix_basis]
    gcongr
    rw [← htr]
    exact g.purified.queryWeight_le_ofReal_trace I (fun _ _ _ ↦ le_rfl) x hρp j
  have hzero : ∀ j ∉ Finset.range n, R.queryWeight I (QuantumRuntime.krausWeight
      (fwdKraus g.compKraus Q)) x (ρ.matrix ⊗ₖ R.init.matrix) j ^ (2⁻¹ : ℝ) = 0 := by
    intro j hj'
    rw [R.queryWeight_eq_zero_of_isTotalQueryBound I hx (by simpa using hj') _,
      ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hzero] at h
  have hsum : ∑ j ∈ Finset.range n, R.queryWeight I (QuantumRuntime.krausWeight
      (fwdKraus g.compKraus Q)) x (ρ.matrix ⊗ₖ R.init.matrix) j ^ (2⁻¹ : ℝ) ≤
      (n : ℝ≥0∞) * (c * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) := by
    calc _ ≤ ∑ _j ∈ Finset.range n, (c * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ ENNReal.rpow_le_rpow (hj j) (by norm_num)
      _ = _ := by simp
  have h2 := ENNReal.rpow_le_rpow (h.trans hsum) (z := 2) (by norm_num)
  rw [← ENNReal.rpow_mul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2
  calc _ = ∑' p, evW Q ((R.run I x).branch p (ρ.matrix ⊗ₖ R.init.matrix)) := rfl
    _ ≤ _ := h2
    _ = _ := by
      rw [show ((n : ℝ≥0∞) ^ (2 : ℝ)) = (n : ℝ≥0∞) ^ 2 by norm_cast]
      ring

end OvGame

end Qrom
